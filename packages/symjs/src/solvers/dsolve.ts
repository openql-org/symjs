// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Single ODE solvers (port of SymPy solvers/ode/single.py and
 * nonhomogeneous.py): the hints are tried in SymPy's order and the raw
 * general solution is post-processed by odesimp.
 */

import { isReal } from '../core/assumptions';
import type { ExprLike } from '../core/nodes';
import { Add, Derivative, Dummy, Expr, Fn, Integral, Mul, Pow, Rational, Rel, S, Special, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, some, subs, xreplace } from '../core/traverse';
import { derivative } from '../core/undef';
import { diff } from '../calculus/diff';
import { abs, cos, fn, im, log, re, sin, tan } from '../functions/elementary';
import '../functions/bessel';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients, roots } from '../polys/poly';
import { factor } from '../polys/sympoly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand, expandMul } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { collect } from '../simplify/radsimp';
import { cancel, fraction, together } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { simplify } from '../simplify/simplify';
import { trigsimp } from '../simplify/trigsimp';
import { odesimp } from './odesimp';
import { linsolve, solve } from './solve';
import { homogeneousOrder } from './homogeneous';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;

const isZero = (e: Expr) => e instanceof Rational && e.isZero;
const C = (i: number) => new Sym(`C${i}`);

export interface OdeProblem {
  eq: Expr;
  fx: UndefFn;
  x: Sym;
  order: number;
}

/** d^k f/dx^k (f itself for k = 0). */
const D = (p: OdeProblem, k: number): Expr => (k === 0 ? p.fx : derivative(p.fx, [[p.x, k]], true));

function orderOf(e: Expr, fx: UndefFn): number {
  let n = 0;
  const go = (t: Expr) => {
    if (t instanceof Derivative && t.expr.key === fx.key) n = Math.max(n, t.variableCount.reduce((s, [, k]) => s + k, 0));
    t.args.forEach(go);
  };
  go(e);
  return n;
}

/** e = A + B*f' with A, B free of f' (B != 0), or undefined. */
function firstOrderParts(e: Expr, p: OdeProblem): [Expr, Expr] | undefined {
  const df = D(p, 1);
  const terms = e instanceof Add ? e.args : [e];
  const A: Expr[] = [];
  const B: Expr[] = [];
  for (const t of terms) {
    if (!t.has(df)) {
      A.push(t);
      continue;
    }
    const fs = t instanceof Mul ? t.args : [t];
    const i = fs.findIndex((g) => g.key === df.key);
    if (i < 0) return undefined;
    const c = mul(...fs.filter((_, j) => j !== i));
    if (c.has(df)) return undefined;
    B.push(c);
  }
  if (!B.length) return undefined;
  return [add(...A), add(...B)];
}

/** Coefficients of f^(k) (k = 0..order) and the remaining term (key -1), or undefined if not linear. */
function linearCoefficients(e: Expr, p: OdeProblem): Map<number, Expr> | undefined {
  const ex = expand(e);
  const out = new Map<number, Expr[]>();
  for (let k = -1; k <= p.order; k++) out.set(k, []);
  const ds = Array.from({ length: p.order + 1 }, (_, k) => D(p, k));
  for (const t of ex instanceof Add ? ex.args : [ex]) {
    const fs = t instanceof Mul ? t.args : [t];
    const hits = fs.map((g, i) => [g, i] as const).filter(([g]) => ds.some((d) => g.has(d) || g.key === d.key));
    if (!hits.length) {
      getOrThrow(out, -1).push(t);
      continue;
    }
    if (hits.length !== 1) return undefined;
    const [g, i] = first(hits);
    const k = ds.findIndex((d) => d.key === g.key);
    if (k < 0) return undefined;
    getOrThrow(out, k).push(mul(...fs.filter((_, j) => j !== i)));
  }
  const r = new Map<number, Expr>();
  for (const [k, v] of out) r.set(k, add(...v));
  return r;
}

type Solver = (p: OdeProblem) => Expr[] | undefined;

/** separatevars without dict: always an expression. */
const separateExpr = (e: Expr): Expr => cast(separatevars(e), Expr, 'separatevars result');

/** x of f(x). */
const independentVariable = (fx: UndefFn): Sym => cast(first(fx.args), Sym, 'independent variable');

// ---------------------------------------------------------------------------
// first order
// ---------------------------------------------------------------------------

function sepDict(e: Expr, x: Sym, y: Sym): Map<Sym | 'coeff', Expr> | undefined {
  const sv = separateExpr(e);
  const m = separatevars(sv, { dict: true, symbols: [x, y] });
  return m instanceof Map ? m : undefined;
}

const separable: Solver = (p) => {
  if (p.order !== 1) return undefined;
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const [d, e] = parts;
  const y = new Dummy('y');
  const m1 = sepDict(xreplace(d, [[p.fx, y]]), p.x, y);
  const m2 = sepDict(xreplace(e, [[p.fx, y]]), p.x, y);
  if (!m1 || !m2) return undefined;
  const g = (m: Map<Sym | 'coeff', Expr>, k: Sym | 'coeff') => m.get(k) ?? S.One;
  const lhs = xreplace(integrate(mul(g(m2, 'coeff'), g(m2, y), pow(g(m1, y), -1)), y), [[y, p.fx]]);
  const rhs = add(integrate(mul(-1, g(m1, 'coeff'), g(m1, p.x), pow(g(m2, p.x), -1)), p.x), C(1));
  return [Eq(lhs, rhs)];
};

const firstExact: Solver = (p) => {
  if (p.order !== 1) return undefined;
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  let [m, n] = parts;
  const y = new Dummy('y');
  m = xreplace(m, [[p.fx, y]]);
  n = xreplace(n, [[p.fx, y]]);
  const num = cancel(add(diff(m, y), mul(-1, diff(n, p.x))));
  if (!isZero(num)) {
    const fn_ = cancel(mul(num, pow(n, -1)));
    const fm = cancel(mul(-1, num, pow(m, -1)));
    let factorE: Expr;
    if (!fn_.has(y)) factorE = exp(integrate(fn_, p.x));
    else if (!fm.has(p.x)) factorE = exp(integrate(fm, y));
    else return undefined;
    m = mul(m, factorE);
    n = mul(n, factorE);
  }
  const Fx = integrate(m, p.x);
  const F = add(Fx, integrate(add(n, mul(-1, diff(Fx, y))), y));
  return [Eq(xreplace(F, [[y, p.fx]]), C(1))];
};

/** f' + P f = Q normalized from the expanded equation. */
function linearFirst(p: OdeProblem): [Expr, Expr] | undefined {
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const [A, B] = parts;
  if (B.has(p.fx)) return undefined;
  const a = expand(mul(A, pow(B, -1)));
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- polyCoefficients only compares its generator by key and has(), so f(x) works as one (its parameter is typed Sym)
  const pc = polyCoefficients(a, p.fx as unknown as Sym);
  if (!pc || Math.max(...pc.keys()) > 1) return undefined;
  const P = cancel(pc.get(1) ?? S.Zero);
  const Q = cancel(mul(-1, pc.get(0) ?? S.Zero));
  if (P.has(p.fx) || Q.has(p.fx)) return undefined;
  return [P, Q];
}

const firstLinear: Solver = (p) => {
  if (p.order !== 1) return undefined;
  const pq = linearFirst(p);
  if (!pq) return undefined;
  const [P, Q] = pq;
  const IP = integrate(P, p.x);
  return [Eq(p.fx, mul(add(C(1), integrate(mul(Q, exp(IP)), p.x)), exp(mul(-1, IP))))];
};

const bernoulli: Solver = (p) => {
  if (p.order !== 1) return undefined;
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const [A, B] = parts;
  if (B.has(p.fx)) return undefined;
  const a = expand(mul(A, pow(B, -1)));
  // P*f - Q*f**n
  let P: Expr = S.Zero;
  let Q: Expr = S.Zero;
  let n: Expr | undefined;
  for (const t of a instanceof Add ? a.args : [a]) {
    const fs = t instanceof Mul ? t.args : [t];
    const i = fs.findIndex((g) => g.key === p.fx.key || (g instanceof Pow && g.base.key === p.fx.key));
    if (i < 0) return undefined;
    const g = at(fs, i);
    const k = g instanceof Pow ? g.exp : S.One;
    const c = mul(...fs.filter((_, j) => j !== i));
    if (c.has(p.fx) || k.has(p.x)) return undefined;
    if (k instanceof Rational && k.isOne) P = add(P, c);
    else if (n === undefined || n.key === k.key) {
      n = k;
      Q = add(Q, mul(-1, c));
    } else return undefined;
  }
  if (n === undefined || isZero(n)) return undefined;
  const IP = integrate(P, p.x);
  return [
    Eq(
      pow(p.fx, add(1, mul(-1, n))),
      mul(add(C(1), mul(-1, add(n, -1), integrate(mul(Q, exp(mul(-1, n, IP)), exp(IP)), p.x))), exp(mul(-1, add(1, mul(-1, n)), IP))),
    ),
  ];
};

const riccatiSpecial: Solver = (p) => {
  if (p.order !== 1) return undefined;
  // a*f' + b*f**2 + c*f/x + d/x**2 with constant a, b != 0
  const e = expand(p.eq);
  let a: Expr = S.Zero;
  let b: Expr = S.Zero;
  let c: Expr = S.Zero;
  let d: Expr = S.Zero;
  const df = D(p, 1);
  const x = p.x;
  for (const t of e instanceof Add ? e.args : [e]) {
    if (t.has(df)) {
      const k = cancel(mul(t, pow(df, -1)));
      if (k.has(x) || k.has(p.fx) || k.has(df)) return undefined;
      a = add(a, k);
    } else if (t.has(p.fx)) {
      const k2 = cancel(mul(t, pow(p.fx, -2)));
      if (!k2.has(x) && !k2.has(p.fx)) {
        b = add(b, k2);
        continue;
      }
      const k1 = cancel(mul(t, x, pow(p.fx, -1)));
      if (!k1.has(x) && !k1.has(p.fx)) {
        c = add(c, k1);
        continue;
      }
      return undefined;
    } else {
      const k0 = cancel(mul(t, pow(x, 2)));
      if (k0.has(x)) return undefined;
      d = add(d, k0);
    }
  }
  if (isZero(a) || isZero(b)) return undefined;
  const mu = sqrt(add(mul(4, d, b), mul(-1, pow(add(a, mul(-1, c)), 2))));
  return [Eq(p.fx, mul(add(a, mul(-1, c), mul(-1, mu, tan(add(mul(mu, pow(mul(2, a), -1), log(x)), C(1))))), pow(mul(2, b, x), -1)))];
};

const nthAlgebraic: Solver = (p) => {
  // the equation involves only derivatives of a single order n and x: f = n-fold integral of the roots
  const n = p.order;
  if (n < 1) return undefined;
  const dn = D(p, n);
  const t = new Dummy('t');
  const e = xreplace(p.eq, [[dn, t]]);
  if (e.has(p.fx) || [...Array(n).keys()].some((k) => k > 0 && e.has(D(p, k)))) return undefined;
  let rs: Expr[];
  try {
    rs = solve(e, t);
  } catch {
    return undefined;
  }
  if (!rs.length) return undefined;
  return rs.map((r) => {
    let g = r;
    for (let i = 0; i < n; i++) g = add(integrate(g, p.x), C(n - i));
    return Eq(p.fx, g);
  });
};

// ---------------------------------------------------------------------------
// linear equations with constant coefficients
// ---------------------------------------------------------------------------

type Term = [number, Expr, Expr];

/** SymPy _get_const_characteristic_eq_sols: homogeneous solutions and collect terms. */
function constCharacteristicSols(r: Map<number, Expr>, p: OdeProblem): [Expr[], Term[]] {
  const s = new Dummy('x');
  const chareq = add(...[...r.entries()].filter(([k]) => k >= 0).map(([k, c]) => mul(c, pow(s, k))));
  const rs = roots(chareq, s);
  const x = p.x;
  const counts = new Map<string, [Expr, number]>();
  for (const v of rs) counts.set(v.key, [v, (counts.get(v.key)?.[1] ?? 0) + 1]);
  const gensols: Expr[] = [];
  let collectterms: Term[] = [];
  const conj: string[] = [];
  const done = new Set<string>();
  // complex (or not known real) coefficients: plain exponentials
  const isComplex = [...r.entries()].some(([k, c]) => k >= 0 && isReal(c) !== true);
  for (const root of rs) {
    if (done.has(root.key)) continue;
    done.add(root.key);
    const mult = getOrThrow(counts, root.key)[1];
    for (let i = 0; i < mult; i++) {
      if (isComplex) {
        gensols.push(mul(pow(x, i), exp(mul(root, x))));
        collectterms = [[i, root, S.Zero], ...collectterms];
        continue;
      }
      const reroot = re(root);
      const imroot = im(root);
      if (conj.includes(root.key)) {
        collectterms = [[i, reroot, imroot], ...collectterms];
        continue;
      }
      if (isZero(imroot)) {
        gensols.push(mul(pow(x, i), exp(mul(reroot, x))));
        collectterms = [[i, reroot, S.Zero], ...collectterms];
        continue;
      }
      conj.push(expand(add(reroot, mul(-1, S.I, imroot))).key);
      gensols.push(mul(pow(x, i), exp(mul(reroot, x)), sin(mul(abs(imroot), x))));
      gensols.push(mul(pow(x, i), exp(mul(reroot, x)), cos(mul(imroot, x))));
      collectterms = [[i, reroot, imroot], ...collectterms];
    }
  }
  return [gensols, collectterms];
}

/** SymPy _get_simplified_sol: collect the homogeneous parts and powsimp. */
function simplifiedSol(sol: Expr, p: OdeProblem, terms: Term[]): Expr {
  const x = p.x;
  // sorted like SymPy's default_sort_key of the tuples (i, re, im), then reversed
  const cmpT = (a: Term, b: Term) => a[0] - b[0] || compareKeys(sortKey(a[1]), sortKey(b[1])) || compareKeys(sortKey(a[2]), sortKey(b[2]));
  const ts = [...terms].sort(cmpT).reverse();
  let e = expandMul(sol);
  for (const [i, rr, ii] of ts) {
    e = collect(e, mul(pow(x, i), exp(mul(rr, x)), sin(mul(abs(ii), x))));
    e = collect(e, mul(pow(x, i), exp(mul(rr, x)), cos(mul(ii, x))));
  }
  for (const [i, rr] of ts) e = collect(e, mul(pow(x, i), exp(mul(rr, x))));
  return powsimp(e);
}

function constantCoeffMatch(p: OdeProblem): Map<number, Expr> | undefined {
  if (p.order < 1) return undefined;
  const r = linearCoefficients(p.eq, p);
  if (!r) return undefined;
  for (const [k, c] of r) if (k >= 0 && (c.has(p.x) || c.has(p.fx))) return undefined;
  if (getOrThrow(r, -1).has(p.fx)) return undefined;
  return r;
}

const nthLinearConstHomogeneous: Solver = (p) => {
  const r = constantCoeffMatch(p);
  if (!r || !isZero(getOrThrow(r, -1))) return undefined;
  const [gensols, terms] = constCharacteristicSols(r, p);
  const sol = add(...gensols.map((g, i) => mul(C(i + 1), g)));
  return [Eq(p.fx, simplifiedSol(sol, p, terms))];
};

/** SymPy _undetermined_coefficients_match: the trial set, or undefined. */
function trialSet(expr0: Expr, x: Sym, homogeneous?: (t: Expr) => boolean): Expr[] | undefined {
  const expr = powsimp(expr0, { combine: 'exp' });
  const linear = (u: Expr) => {
    const pc = polyCoefficients(u, x);
    return !!pc && Math.max(...pc.keys()) <= 1;
  };
  const test = (e: Expr): boolean => {
    if (!e.has(x)) return true;
    if (e instanceof Add) return e.args.every(test);
    if (e instanceof Mul) {
      const trig = e.args.filter((i) => i.has(x) && someFn(i, ['sin', 'cos']));
      if (trig.length > 1) return false;
      return e.args.every(test);
    }
    if (e instanceof Fn) return ['sin', 'cos', 'sinh', 'cosh'].includes(e.name) && linear(first(e.args));
    if (e instanceof Pow && e.base.key === x.key && e.exp instanceof Rational && e.exp.isInteger && !e.exp.isNegative) return true;
    if (e instanceof Pow && freeSymbols(e.base).size === 0) return linear(e.exp);
    return e instanceof Sym || freeSymbols(e).size === 0;
  };
  if (!test(expr)) return undefined;
  const removeCoeff = (e: Expr): Expr => {
    if (e instanceof Mul) return mul(...e.args.filter((i) => i.has(x)));
    return e.has(x) ? e : S.One;
  };
  const getTrial = (e0: Expr, acc: Map<string, Expr>): Map<string, Expr> => {
    const e1 = expandMul(e0);
    if (e1 instanceof Add) {
      for (const term of e1.args) {
        const rc = removeCoeff(term);
        if (!acc.has(rc.key)) {
          acc.set(rc.key, rc);
          getTrial(term, acc);
        }
      }
      return acc;
    }
    let e = e1;
    const tmp = new Map(acc);
    const t0 = removeCoeff(e);
    tmp.set(t0.key, t0);
    for (let guard = 0; guard < 20; guard++) {
      const before = tmp.size;
      e = diff(e, x);
      const term = removeCoeff(e);
      if (term instanceof Add) getTrial(term, tmp);
      else tmp.set(term.key, term);
      if (tmp.size === before) break;
    }
    for (const [k, v] of tmp) acc.set(k, v);
    return acc;
  };
  const out = new Map<string, Expr>();
  for (const i of expr instanceof Add ? expr.args : [expr]) {
    let act = [...getTrial(i, new Map()).values()];
    if (homogeneous) {
      for (let guard = 0; guard < 10 && act.some(homogeneous); guard++) act = act.map((t) => mul(x, t));
    }
    for (const a of act) out.set(a.key, a);
  }
  return [...out.values()];
}

function someFn(e: Expr, names: string[]): boolean {
  return (e instanceof Fn && names.includes(e.name)) || e.args.some((a) => someFn(a, names));
}

/** Substitute g for f(x) in e and evaluate the derivatives. */
function subFuncDoit(e: Expr, p: OdeProblem, g: Expr): Expr {
  let r = e;
  for (let k = p.order; k >= 1; k--) r = xreplace(r, [[D(p, k), diff(g, p.x, k)]]);
  return xreplace(r, [[p.fx, g]]);
}

const undeterminedCoefficients: Solver = (p) => {
  const r = constantCoeffMatch(p);
  if (!r || isZero(getOrThrow(r, -1))) return undefined;
  const homog = add(p.eq, mul(-1, getOrThrow(r, -1)));
  const trial = trialSet(getOrThrow(r, -1), p.x, (t) => isZero(expand(subFuncDoit(homog, p, t))));
  if (!trial) return undefined;
  const [gensols, terms] = constCharacteristicSols(r, p);
  if (gensols.length !== p.order) return undefined;
  const cs = trial.map((_, i) => new Dummy(`a${i}`));
  const trialfunc = add(...trial.map((t, i) => mul(at(cs, i), t)));
  const eqs = expand(subFuncDoit(p.eq, p, trialfunc));
  const byTerm = new Map<string, Expr[]>();
  for (const t of eqs instanceof Add ? eqs.args : [eqs]) {
    const m = separatevars(t, { dict: true, symbols: [p.x] });
    if (!(m instanceof Map)) return undefined;
    const k = (m.get(p.x) ?? S.One).key;
    byTerm.set(k, [...(byTerm.get(k) ?? []), m.get('coeff') ?? S.One]);
  }
  const sol = linsolve([...byTerm.values()].map((v) => add(...v)), cs);
  if (!sol) return undefined;
  const psol = xreplace(trialfunc, cs.map((c, i): [Expr, Expr] => [c, at(sol, i)]));
  const gsol = add(...gensols.map((g, i) => mul(C(i + 1), g)), psol);
  return [Eq(p.fx, simplifiedSol(gsol, p, terms))];
};

function wronskian(fs: Expr[], x: Sym): Expr {
  const n = fs.length;
  if (n === 0) return S.One;
  return Matrix.of(Array.from({ length: n }, (_, i) => fs.map((f) => diff(f, x, i)))).det();
}

const variationOfParameters: Solver = (p) => {
  const r = constantCoeffMatch(p);
  if (!r || isZero(getOrThrow(r, -1))) return undefined;
  const [gensols, terms] = constCharacteristicSols(r, p);
  if (gensols.length !== p.order) return undefined;
  let wr = trigsimp(simplify(wronskian(gensols, p.x)));
  if (isZero(wr)) return undefined;
  let psol: Expr = S.Zero;
  let sign = p.order % 2 === 0 ? 1 : -1;
  for (const g of gensols) {
    const others = gensols.filter((h) => h !== g);
    psol = add(psol, mul(sign, integrate(mul(wronskian(others, p.x), getOrThrow(r, -1), pow(wr, -1)), p.x), g, pow(getOrThrow(r, p.order), -1)));
    sign = -sign;
  }
  psol = trigsimp(simplify(psol));
  wr = S.One;
  const gsol = add(...gensols.map((g, i) => mul(C(i + 1), g)), psol);
  return [Eq(p.fx, simplifiedSol(gsol, p, terms))];
};

// ---------------------------------------------------------------------------
// Euler equations
// ---------------------------------------------------------------------------

function eulerMatch(p: OdeProblem): Map<number, Expr> | undefined {
  if (p.order < 1) return undefined;
  const m = linearCoefficients(p.eq, p);
  if (!m) return undefined;
  const lead = getOrThrow(m, p.order);
  if (isZero(lead)) return undefined;
  const r = new Map<number, Expr>();
  for (const [k, c] of m) r.set(k, cancel(mul(pow(p.x, p.order), pow(lead, -1), c)));
  for (const [k, c] of r) {
    if (k < 0) continue;
    if (isZero(c)) continue;
    const q = cancel(mul(c, pow(p.x, -k)));
    if (q.has(p.x) || q.has(p.fx)) return undefined;
  }
  return r;
}

function eulerCharacteristicSols(p: OdeProblem, r: Map<number, Expr>): [Expr, Expr[]] {
  const s = new Dummy('x');
  const x = p.x;
  const rs = sortRoots(roots(eulerChareq(r, x, s), s));
  const cs = Array.from({ length: rs.length * 2 }, (_, i) => C(i + 1)).reverse();
  const counts = new Map<string, [Expr, number]>();
  for (const v of rs) counts.set(v.key, [v, (counts.get(v.key)?.[1] ?? 0) + 1]);
  let gsol: Expr = S.Zero;
  const gens: Expr[] = [];
  for (const [root, mult] of counts.values()) {
    for (let i = 0; i < mult; i++) {
      if (isReal(root) === true) {
        gsol = add(gsol, mul(pow(log(x), i), pow(x, root), defined(cs.pop(), 'constant')));
        gens.push(mul(pow(log(x), i), pow(x, root)));
      } else {
        const rr = re(root);
        const ii = im(root);
        gsol = add(gsol, mul(pow(log(x), i), pow(x, rr), add(mul(defined(cs.pop(), 'constant'), sin(mul(abs(ii), log(x)))), mul(defined(cs.pop(), 'constant'), cos(mul(ii, log(x)))))));
        gens.push(mul(pow(log(x), i), pow(x, rr), sin(mul(abs(ii), log(x)))));
      }
    }
  }
  return [Eq(p.fx, gsol), gens];
}

/** sum_k (r_k/x**k)*s*(s - 1)*...*(s - k + 1): x**(-s)*L[x**s] for the Euler operator. */
function eulerChareq(r: Map<number, Expr>, x: Sym, s: Sym): Expr {
  let chareq: Expr = S.Zero;
  for (const [k, c] of r) {
    if (k < 0) continue;
    let ff: Expr = S.One;
    for (let j = 0; j < k; j++) ff = mul(ff, add(s, -j));
    chareq = add(chareq, mul(cancel(mul(c, pow(x, -k))), ff));
  }
  return expand(chareq);
}

/** Real roots first in increasing order (like rootof indexing), then complex ones. */
function sortRoots(rs: Expr[]): Expr[] {
  const real = rs.filter((r) => isReal(r) === true);
  const other = rs.filter((r) => isReal(r) !== true);
  real.sort((a, b) => a.toNumber() - b.toNumber());
  return [...real, ...other];
}

const eulerHomogeneous: Solver = (p) => {
  const r = eulerMatch(p);
  if (!r || !isZero(getOrThrow(r, -1))) return undefined;
  return [eulerCharacteristicSols(p, r)[0]];
};

const eulerUndetermined: Solver = (p) => {
  const r = eulerMatch(p);
  if (!r || isZero(getOrThrow(r, -1))) return undefined;
  // substitute x = exp(t): a linear equation with constant coefficients in t
  const s = new Dummy('x');
  const x = p.x;
  const pc = polyCoefficients(eulerChareq(r, x, s), s);
  if (!pc) return undefined;
  const rhs = simplify(xreplace(getOrThrow(r, -1), [[x, exp(x)]]));
  if (!trialSet(rhs, x)) return undefined;
  let eq: Expr = S.Zero;
  for (const [k, c] of pc) eq = add(eq, mul(c, D(p, k)));
  eq = add(eq, rhs);
  const sub: OdeProblem = { eq, fx: p.fx, x, order: p.order };
  const sols = undeterminedCoefficients(sub);
  if (!sols) return undefined;
  const s0 = cast(first(sols), Rel, 'solution');
  return [Eq(p.fx, expand(xreplace(s0.rhs, [[x, log(x)]])))];
};

// ---------------------------------------------------------------------------
// second order and reducible equations
// ---------------------------------------------------------------------------

const liouville: Solver = (p) => {
  if (p.order !== 2) return undefined;
  // d*f'' + e*f'**2 + k*f' = 0
  const e0 = expand(p.eq);
  const d2 = D(p, 2);
  const d1 = D(p, 1);
  let dd: Expr = S.Zero;
  let ee: Expr = S.Zero;
  let kk: Expr = S.Zero;
  for (const t of e0 instanceof Add ? e0.args : [e0]) {
    if (t.has(d2)) {
      const c = cancel(mul(t, pow(d2, -1)));
      if (c.has(d2) || c.has(d1)) return undefined;
      dd = add(dd, c);
    } else if (t.has(d1)) {
      const c2 = cancel(mul(t, pow(d1, -2)));
      if (!c2.has(d1)) {
        ee = add(ee, c2);
        continue;
      }
      const c1 = cancel(mul(t, pow(d1, -1)));
      if (c1.has(d1)) return undefined;
      kk = add(kk, c1);
    } else return undefined;
  }
  if (isZero(dd) || isZero(ee)) return undefined;
  const y = new Dummy('y');
  const g = xreplace(simplify(mul(ee, pow(dd, -1))), [[p.fx, y]]);
  const h = xreplace(simplify(mul(kk, pow(dd, -1))), [[p.fx, y]]);
  if (h.has(y) || g.has(p.x)) return undefined;
  const inner = xreplace(integrate(exp(integrate(g, y)), y), [[y, p.fx]]);
  return [Eq(add(inner, mul(C(1), integrate(exp(mul(-1, integrate(h, p.x))), p.x)), C(2)), S.Zero)];
};

const nthOrderReducible: Solver = (p) => {
  const ords = new Set<number>();
  const walk = (e: Expr) => {
    if (e instanceof Derivative && e.expr.key === p.fx.key) ords.add(e.variableCount.reduce((s, [, k]) => s + k, 0));
    e.args.forEach(walk);
  };
  walk(p.eq);
  if (ords.size < 2) return undefined;
  const n = Math.min(...ords);
  const t = new Dummy('t');
  if (subs(p.eq, [[D(p, n), t]]).has(p.fx)) return undefined;
  const g = new UndefFn('_g', [p.x]);
  let geq = p.eq;
  for (const k of [...ords].sort((a, b) => b - a)) geq = xreplace(geq, [[D(p, k), k === n ? g : derivative(g, [[p.x, k - n]], true)]]);
  const gsol = dsolveRaw(geq, g);
  if (!gsol) return undefined;
  const out: Expr[] = [];
  for (const gs of gsol) {
    const gr = cast(gs, Rel, 'solution');
    if (gr.lhs.key !== g.key) return undefined;
    let f = gr.rhs;
    // integrate n times with new constants
    const used = [...freeSymbols(f)].filter((s) => /^C\d+$/.test(s.name)).length;
    for (let i = 0; i < n; i++) f = add(integrate(f, p.x), C(used + i + 1));
    out.push(Eq(p.fx, f));
  }
  return out;
};

const factorable: Solver = (p) => {
  const eq0 = p.eq;
  let eq: Expr;
  try {
    eq = fraction(factor(eq0))[0];
  } catch {
    return undefined;
  }
  const fs = eq instanceof Mul ? eq.args : [eq];
  // oxlint-disable-next-line typescript/no-unnecessary-type-assertion -- the tuple type is needed by tsc
  const bases = fs.map((f) => (f instanceof Pow ? [f.base, f.exp] : [f, S.One]) as [Expr, Expr]).filter(([b]) => b.args.length !== 0);
  let eqs: Expr[] = [];
  if (bases.length > 1 || (bases[0] && !(bases[0][1] instanceof Rational && bases[0][1].isOne))) {
    eqs = bases.filter(([b]) => b.has(p.fx)).map(([b]) => b);
  }
  if (eqs.length < 2) {
    if (p.order !== 1) return undefined;
    const df = D(p, 1);
    let rs: Expr[] = [];
    try {
      rs = solve(eq0, df);
    } catch {
      rs = [];
    }
    if (rs.length < 2) return undefined;
    eqs = rs.map((r) => add(df, mul(-1, r)));
  }
  // SymPy iterates the factors in Mul argument order
  const argCmp = (a: Expr, b: Expr): number => {
    // like Basic.compare for sums: compare the (sorted) terms one by one
    const ta = [...(a instanceof Add ? a.args : [a])].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
    const tb = [...(b instanceof Add ? b.args : [b])].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
    for (let i = 0; i < Math.min(ta.length, tb.length); i++) {
      const c = compareKeys(sortKey(at(ta, i)), sortKey(at(tb, i)));
      if (c) return c;
    }
    return ta.length - tb.length;
  };
  eqs = [...eqs].sort(argCmp);
  const sols: Expr[] = [];
  for (const e of eqs) {
    const s = dsolveRaw(e, p.fx);
    if (s) sols.push(...s);
  }
  return sols.length ? sols : undefined;
};

// ---------------------------------------------------------------------------
// Airy and Bessel equations
// ---------------------------------------------------------------------------

const airy: Solver = (p) => {
  if (p.order !== 2) return undefined;
  const r = linearCoefficients(p.eq, p);
  if (!r || !isZero(getOrThrow(r, -1)) || !isZero(getOrThrow(r, 1)) || isZero(getOrThrow(r, 2))) return undefined;
  const q = cancel(mul(getOrThrow(r, 0), pow(getOrThrow(r, 2), -1)));
  const pc = polyCoefficients(q, p.x);
  if (!pc || Math.max(...pc.keys()) !== 1) return undefined;
  const b = pc.get(0) ?? S.Zero;
  const m = getOrThrow(pc, 1);
  if (m.has(p.x)) return undefined;
  const cbrt = (e: Expr) => pow(e, Rational.of(1, 3));
  const arg =
    m instanceof Rational && m.isPositive
      ? add(mul(-1, b, pow(cbrt(m), -2)), mul(-1, cbrt(m), p.x))
      : add(mul(-1, b, pow(cbrt(mul(-1, m)), -2)), mul(cbrt(mul(-1, m)), p.x));
  return [Eq(p.fx, add(mul(C(1), fn('airyai', [arg])), mul(C(2), fn('airybi', [arg]))))];
};

const bessel: Solver = (p) => {
  if (p.order !== 2) return undefined;
  const r = linearCoefficients(p.eq, p);
  if (!r || !isZero(getOrThrow(r, -1))) return undefined;
  const x = p.x;
  const a3 = getOrThrow(r, 2);
  // a3 = A*x**k
  const pa = polyCoefficients(expand(a3), x);
  if (pa?.size !== 1) return undefined;
  const [k, A] = first([...pa.entries()]);
  if (k === 0 || A.has(x)) return undefined;
  const norm = (e: Expr) => cancel(mul(e, pow(mul(A, pow(x, k - 2)), -1)));
  const b3 = norm(getOrThrow(r, 1));
  const c3 = expand(norm(getOrThrow(r, 0)));
  // b3 = c4*x
  const c4 = cancel(mul(b3, pow(x, -1)));
  if (c4.has(x)) return undefined;
  // c3 = alpha**2*x**(2*d) - n**2
  const terms = c3 instanceof Add ? c3.args : [c3];
  const dep = terms.filter((t) => t.has(x));
  const ind = add(...terms.filter((t) => !t.has(x)));
  if (dep.length !== 1) return undefined;
  const pd = polyCoefficients(first(dep), x);
  if (pd?.size !== 1) return undefined;
  const [e2, alpha2] = first([...pd.entries()]);
  if (e2 % 2 !== 0) return undefined;
  const d = e2 / 2;
  const alpha = sqrt(alpha2);
  const nsq = mul(-1, ind);
  const n = sqrt(add(nsq, mul(Rational.of(1, 4), pow(add(c4, -1), 2))));
  const argB = mul(alpha, pow(x, d), Rational.of(1, d));
  const nu = mul(n, Rational.of(1, d));
  const pre = pow(x, mul(Rational.of(1, 2), add(1, mul(-1, c4))));
  return [Eq(p.fx, mul(pre, add(mul(C(1), fn('besselj', [nu, argB])), mul(C(2), fn('bessely', [nu, argB])))))];
};

// ---------------------------------------------------------------------------
// homogeneous coefficients and linear coefficients (SymPy single.py)
// ---------------------------------------------------------------------------

/** d + e*f' of a first-order equation with f(x) replaced by y (SymPy's wilds match, collected with cancel). */
function deMatch(p: OdeProblem): { d: Expr; e: Expr; y: Dummy } | undefined {
  if (p.order !== 1) return undefined;
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const y = new Dummy('y');
  const d = cancel(xreplace(parts[0], [[p.fx, y]]));
  const e = cancel(xreplace(parts[1], [[p.fx, y]]));
  if (d.has(D(p, 1)) || e.has(D(p, 1))) return undefined;
  return { d, e, y };
}

/** d and e are homogeneous of the same order in x and y (SymPy HomogeneousCoeff _verify). */
function sameHomogeneousOrder(d: Expr, e: Expr, x: Sym, y: Dummy): boolean {
  const od = homogeneousOrder(separateExpr(d), x, y);
  const oe = homogeneousOrder(separateExpr(e), x, y);
  return od !== undefined && oe !== undefined && od.key === oe.key;
}

/**
 * SymPy 1st_homogeneous_coeff_subs_dep_div_indep (u = y/x) or
 * _subs_indep_div_dep (u = x/y) before odesimp; the solution is shifted
 * back by (xarg, yarg) for linear coefficients.
 */
function homogeneousSolution(p: OdeProblem, m: { d: Expr; e: Expr; y: Dummy }, dep: boolean, xarg: Expr = S.Zero, yarg: Expr = S.Zero): Expr | undefined {
  const { d, e, y } = m;
  const x = p.x;
  const u1 = new Dummy('u1');
  const integrand = dep ? cancel(subs(mul(-1, e, pow(add(d, mul(u1, e)), -1)), [[x, 1], [y, u1]])) : simplify(subs(mul(-1, d, pow(add(e, mul(u1, d)), -1)), [[x, u1], [y, 1]]));
  if (integrand instanceof Special) return undefined;
  const I = integrate(integrand, u1);
  if (some(I, (t) => t instanceof Integral)) return undefined;
  const lhs = dep ? log(x) : log(p.fx);
  const arg = dep ? mul(p.fx, pow(x, -1)) : mul(x, pow(p.fx, -1));
  // SymPy combines the logs while the integral is still unevaluated, so log(C1) stays apart (constantsimp then makes it C1)
  let sol = Eq(lhs, add(subs(I, [[u1, arg]]), C(1)));
  if (!isZero(xarg) || !isZero(yarg)) {
    const u = new Dummy('u');
    sol = xreplace(sol, [[p.fx, u]]);
    sol = subs(sol, [[u, add(u, mul(-1, yarg))]]);
    sol = subs(sol, [[x, add(x, mul(-1, xarg))]]);
    sol = xreplace(sol, [[u, p.fx]]);
  }
  return sol;
}

/** SymPy ode_sol_simplicity: solved for f(x) first, then without Integrals, then shortest. */
function solSimplicity(sols: Expr[], fx: Expr): number {
  if (sols.some((s) => some(s, (t) => t instanceof Integral))) return Infinity;
  if (sols.every((s) => s instanceof Rel && s.lhs.key === fx.key && !s.rhs.has(fx))) return -2;
  return sols.map(String).join(', ').length;
}

/** SymPy HomogeneousCoeffBest: both substitutions, the simpler result (after odesimp). */
function homogeneousBest(p: OdeProblem, m: { d: Expr; e: Expr; y: Dummy }, xarg?: Expr, yarg?: Expr): Expr[] | undefined {
  const cands: Expr[][] = [];
  for (const [dep, hint] of [[false, '1st_homogeneous_coeff_subs_indep_div_dep'], [true, '1st_homogeneous_coeff_subs_dep_div_indep']] as const) {
    try {
      const raw = homogeneousSolution(p, m, dep, xarg, yarg);
      if (raw) cands.push(odesimp(p.eq, raw, p.fx, hint));
    } catch {
      // this substitution fails; the other one may work
    }
  }
  if (!cands.length) return undefined;
  return cands.reduce((a, b) => (solSimplicity(b, p.fx) < solSimplicity(a, p.fx) ? b : a));
}

const homogeneousCoeffBest: Solver = (p) => {
  const m = deMatch(p);
  if (!m || !sameHomogeneousOrder(m.d, m.e, p.x, m.y)) return undefined;
  if (isZero(simplify(subs(add(m.d, mul(new Dummy('u'), m.e)), [[p.x, 1]])))) return undefined;
  return homogeneousBest(p, m);
};

/** a*x + b*y + c with rational a, b, c (SymPy _linear_coeff_match abc). */
function linearABC(e: Expr, x: Sym, y: Expr): [Rational, Rational, Rational] | undefined {
  const pe = expand(e);
  const c = subs(pe, [[x, 0], [y, 0]]);
  const a = subs(diff(pe, x), [[y, 0]]);
  const b = subs(diff(pe, y), [[x, 0]]);
  if (!(a instanceof Rational && b instanceof Rational && c instanceof Rational)) return undefined;
  return isZero(expand(add(pe, mul(-1, add(mul(a, x), mul(b, y), c))))) ? [a, b, c] : undefined;
}

const linearCoefficientsSolver: Solver = (p) => {
  const m = deMatch(p);
  if (!m) return undefined;
  const x = p.x;
  const F = cancel(mul(m.d, pow(m.e, -1)));
  const [num, den] = fraction(F);
  const n1 = linearABC(num, x, m.y);
  const n2 = linearABC(den, x, m.y);
  if (!n1 || !n2) return undefined;
  const [a1, b1, c1] = n1;
  const [a2, b2, c2] = n2;
  const det = add(mul(a2, b1), mul(-1, a1, b2));
  if (isZero(det) || (isZero(c1) && isZero(c2))) return undefined;
  const xarg = mul(add(mul(b2, c1), mul(-1, b1, c2)), pow(det, -1));
  const yarg = mul(add(mul(a1, c2), mul(-1, a2, c1)), pow(det, -1));
  // d and e after x -> x + xarg, y -> y + yarg are homogeneous
  const shift = (t: Expr) => cancel(subs(t, [[x, add(x, xarg)], [m.y, add(m.y, yarg)]]));
  const sm = { d: shift(m.d), e: shift(m.e), y: m.y };
  if (!sameHomogeneousOrder(sm.d, sm.e, x, sm.y)) return undefined;
  return homogeneousBest(p, sm, xarg, yarg);
};

/** Hints whose solvers return solutions already simplified by odesimp. */
const PRESIMPLIFIED = new Set(['1st_homogeneous_coeff_best', 'linear_coefficients']);

// ---------------------------------------------------------------------------
// driver
// ---------------------------------------------------------------------------

// SymPy's dsolve takes the first matching solver in solver_map order (not allhints order)
const HINTS: [string, Solver][] = [
  ['factorable', factorable],
  ['nth_linear_constant_coeff_homogeneous', nthLinearConstHomogeneous],
  ['nth_linear_euler_eq_homogeneous', eulerHomogeneous],
  ['nth_linear_constant_coeff_undetermined_coefficients', undeterminedCoefficients],
  ['nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients', eulerUndetermined],
  ['separable', separable],
  ['1st_exact', firstExact],
  ['1st_linear', firstLinear],
  ['Bernoulli', bernoulli],
  ['Riccati_special_minus2', riccatiSpecial],
  ['1st_homogeneous_coeff_best', homogeneousCoeffBest],
  ['linear_coefficients', linearCoefficientsSolver],
  ['nth_linear_constant_coeff_variation_of_parameters', variationOfParameters],
  // SymPy reaches f'' + f'**2 = 0 through factorable/nth_order_reducible before Liouville
  ['nth_order_reducible', nthOrderReducible],
  ['Liouville', liouville],
  ['2nd_linear_airy', airy],
  ['2nd_linear_bessel', bessel],
  ['nth_algebraic', nthAlgebraic],
];

/** The hints with a solver here that match the equation (solver order). */
function solverHints(eqIn: ExprLike, fx: UndefFn): string[] {
  const eq = toZeroForm(sympify(eqIn));
  const p: OdeProblem = { eq, fx, x: independentVariable(fx), order: orderOf(eq, fx) };
  return HINTS.filter(([, s]) => {
    try {
      return s(p) !== undefined;
    } catch {
      return false;
    }
  }).map(([h]) => h);
}

function toZeroForm(e: Expr): Expr {
  return e instanceof Rel && e.op === 'Eq' ? add(e.lhs, mul(-1, e.rhs)) : e;
}

/** Solve with the first matching hint; the solutions are post-processed with odesimp. */
export function dsolveRaw(eqIn: Expr, fx: UndefFn, hint?: string): Expr[] | undefined {
  const eq = toZeroForm(eqIn);
  const p: OdeProblem = { eq, fx, x: independentVariable(fx), order: orderOf(eq, fx) };
  if (p.order === 0) return undefined;
  for (const [h, s] of HINTS) {
    if (hint && hint !== 'default' && h !== hint) continue;
    let raw: Expr[] | undefined;
    try {
      raw = s(p);
    } catch {
      raw = undefined;
    }
    if (!raw) continue;
    try {
      const out: Expr[] = [];
      if (PRESIMPLIFIED.has(h)) out.push(...raw);
      else for (const r of raw) out.push(...odesimp(eq, r, fx, h));
      return out;
    } catch {
      continue;
    }
  }
  return undefined;
}


// ---- SymPy classify_ode -------------------------------------------------------------

/** SymPy allhints, the order in which classify_ode reports the matching hints. */
const ALL_HINTS = [
  'factorable', 'nth_algebraic', 'separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_rational_riccati', 'Riccati_special_minus2',
  '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'almost_linear',
  'linear_coefficients', 'separable_reduced', '1st_power_series', 'lie_group', 'nth_linear_constant_coeff_homogeneous',
  'nth_linear_euler_eq_homogeneous', 'nth_linear_constant_coeff_undetermined_coefficients',
  'nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters',
  'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', 'Liouville', '2nd_linear_airy', '2nd_linear_bessel', '2nd_hypergeometric',
  '2nd_hypergeometric_Integral', 'nth_order_reducible', '2nd_power_series_ordinary', '2nd_power_series_regular', 'nth_algebraic_Integral',
  'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral',
  '1st_homogeneous_coeff_subs_dep_div_indep_Integral', 'almost_linear_Integral', 'linear_coefficients_Integral', 'separable_reduced_Integral',
  'nth_linear_constant_coeff_variation_of_parameters_Integral', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters_Integral',
  'Liouville_Integral', '2nd_nonlinear_autonomous_conserved', '2nd_nonlinear_autonomous_conserved_Integral',
];

/** d + e*f'(x) = eq (first order): [d, e] with f(x) replaced by y, or undefined. */
function firstOrderDE(p: OdeProblem, y: Sym): [Expr, Expr] | undefined {
  if (p.order !== 1) return undefined;
  const df = new Derivative([p.fx, p.x, S.One]);
  const ex = expandMul(p.eq);
  const terms = ex instanceof Add ? ex.args : [ex];
  const e: Expr[] = [];
  const d: Expr[] = [];
  for (const t of terms) {
    if (!t.has(df)) d.push(t);
    else {
      const c = mul(t, pow(df, -1));
      if (c.has(df)) return undefined;
      e.push(c);
    }
  }
  const rep = (u: Expr) => xreplace(u, [[p.fx, y]]);
  return [rep(add(...d)), rep(add(...e))];
}

/** Extra matchers for the hints classify_ode reports without a solver here. */
function classifyExtra(p: OdeProblem): Set<string> {
  const out = new Set<string>();
  const x = p.x;
  const y = new Sym('y_cls');
  const df = new Derivative([p.fx, x, S.One]);
  // factorable (SymPy Factorable._matches): several factors, or solvable for f' with a different equation
  try {
    const [n] = fraction(together(p.eq));
    const fac = factor(n);
    const factors = fac instanceof Mul ? fac.args : [fac];
    const withF = factors.filter((u) => u.has(p.fx));
    // oxlint-disable-next-line typescript/no-unnecessary-type-assertion -- the tuple type is needed by tsc
    const bases = factors.filter((u) => u.args.length).map((u) => (u instanceof Pow && u.exp instanceof Rational ? [u.base, Number(u.exp.p)] : [u, 1]) as [Expr, number]);
    if ((bases.length > 1 || (bases[0] && bases[0][1] > 1)) && withF.length) out.add('factorable');
    else {
      const t = new Dummy('df');
      const roots = solve(xreplace(n, [[df, t]]), t);
      if (roots.length && !(roots.length === 1 && add(df, mul(-1, first(roots))).key === p.eq.key)) out.add('factorable');
    }
  } catch {
    // not decided
  }
  const de = firstOrderDE(p, y);
  if (de) {
    const [d, e] = de;
    // Bernoulli: f' + P*f - Q*f**n (linear equations included)
    const rest = expandMul(mul(d, pow(e, -1)));
    const exps = new Set<string>();
    let bern = !isZeroE(e);
    for (const t of rest instanceof Add ? rest.args : [rest]) {
      const fs = t instanceof Mul ? t.args : [t];
      const yf = fs.filter((u) => u.has(y));
      if (yf.length > 1) bern = false;
      else if (yf.length === 1) {
        const u = first(yf);
        if (u.key === y.key) exps.add('1');
        else if (u instanceof Pow && u.base.key === y.key && !u.exp.has(x) && !u.exp.has(y)) exps.add(u.exp.key);
        else bern = false;
      } else exps.add('0');
    }
    if (bern && [...exps].filter((k) => k !== '1').length <= 1) out.add('Bernoulli');
    // homogeneous coefficients: d and e homogeneous of the same order
    try {
      const sep = (u: Expr): Expr => {
        const r = separatevars(u);
        return r instanceof Expr ? r : u;
      };
      const od = homogeneousOrder(sep(d), x, y);
      const oe = homogeneousOrder(sep(e), x, y);
      if (od !== undefined && oe !== undefined && od.key === oe.key) {
        const u = new Sym('u_cls');
        const indep = !isZeroE(simplify(xreplace(add(e, mul(u, d)), [[x, u], [y, S.One]])));
        const dep = !isZeroE(simplify(xreplace(add(d, mul(u, e)), [[x, S.One], [y, u]])));
        if (indep) out.add('1st_homogeneous_coeff_subs_indep_div_dep');
        if (dep) out.add('1st_homogeneous_coeff_subs_dep_div_indep');
        if (indep && dep) out.add('1st_homogeneous_coeff_best');
      }
    } catch {
      // not homogeneous
    }
    // 1st_power_series: d/e and its x-derivative finite at x = 0, f(0) = C1
    try {
      const C1 = new Sym('C1');
      const check = cancel(mul(d, pow(e, -1)));
      const bad = (v: Expr): boolean => v instanceof Special || v.args.some(bad);
      const c1 = xreplace(check, [[x, S.Zero], [y, C1]]);
      const c2 = xreplace(diff(c1, x), [[x, S.Zero], [y, C1]]);
      if (!bad(c1) && !bad(c2)) out.add('1st_power_series');
    } catch {
      // not decided
    }
    out.add('lie_group');
  }
  return out;
}

/** SymPy classify_ode(eq, f(x)): the names of the matching hints in SymPy's order, with their _Integral variants. */
export function classifyOde(eqIn: ExprLike, fx: UndefFn): string[] {
  const eq = toZeroForm(sympify(eqIn));
  const p: OdeProblem = { eq, fx, x: independentVariable(fx), order: orderOf(eq, fx) };
  const matched = new Set(solverHints(eq, fx).filter((h) => h !== 'factorable'));
  for (const h of classifyExtra(p)) matched.add(h);
  for (const h of [...matched]) if (ALL_HINTS.includes(`${h}_Integral`)) matched.add(`${h}_Integral`);
  return ALL_HINTS.filter((h) => matched.has(h));
}
