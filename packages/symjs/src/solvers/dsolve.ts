// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Single ODE solvers (port of SymPy solvers/ode/single.py and
 * nonhomogeneous.py): the hints are tried in SymPy's order and the raw
 * general solution is post-processed by odesimp.
 */

import { isReal } from '../core/assumptions';
import { Add, Derivative, Dummy, Expr, ExprLike, Fn, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { derivative } from '../core/undef';
import { diff } from '../calculus/diff';
import { abs, cos, im, log, re, sin, tan } from '../functions/elementary';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients, roots } from '../polys/poly';
import { factor } from '../polys/sympoly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand, expandMul } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { collect } from '../simplify/radsimp';
import { cancel, fraction } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { simplify } from '../simplify/simplify';
import { trigsimp } from '../simplify/trigsimp';
import { odesimp } from './odesimp';
import { linsolve, solve } from './solve';

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
      out.get(-1)!.push(t);
      continue;
    }
    if (hits.length !== 1) return undefined;
    const [g, i] = hits[0]!;
    const k = ds.findIndex((d) => d.key === g.key);
    if (k < 0) return undefined;
    out.get(k)!.push(mul(...fs.filter((_, j) => j !== i)));
  }
  const r = new Map<number, Expr>();
  for (const [k, v] of out) r.set(k, add(...v));
  return r;
}

type Solver = (p: OdeProblem) => Expr[] | undefined;

// ---------------------------------------------------------------------------
// first order
// ---------------------------------------------------------------------------

function sepDict(e: Expr, x: Sym, y: Sym): Map<Sym | 'coeff', Expr> | undefined {
  const sv = separatevars(e) as Expr;
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
    const g = fs[i]!;
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
    const mult = counts.get(root.key)![1];
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
  if (r.get(-1)!.has(p.fx)) return undefined;
  return r;
}

const nthLinearConstHomogeneous: Solver = (p) => {
  const r = constantCoeffMatch(p);
  if (!r || !isZero(r.get(-1)!)) return undefined;
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
    if (e instanceof Fn) return ['sin', 'cos', 'sinh', 'cosh'].includes(e.name) && linear(e.args[0]!);
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
  if (!r || isZero(r.get(-1)!)) return undefined;
  const homog = add(p.eq, mul(-1, r.get(-1)!));
  const trial = trialSet(r.get(-1)!, p.x, (t) => isZero(expand(subFuncDoit(homog, p, t))));
  if (!trial) return undefined;
  const [gensols, terms] = constCharacteristicSols(r, p);
  if (gensols.length !== p.order) return undefined;
  const cs = trial.map((_, i) => new Dummy(`a${i}`));
  const trialfunc = add(...trial.map((t, i) => mul(cs[i]!, t)));
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
  const psol = xreplace(trialfunc, cs.map((c, i) => [c, sol[i]!] as [Expr, Expr]));
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
  if (!r || isZero(r.get(-1)!)) return undefined;
  const [gensols, terms] = constCharacteristicSols(r, p);
  if (gensols.length !== p.order) return undefined;
  let wr = trigsimp(simplify(wronskian(gensols, p.x)));
  if (isZero(wr)) return undefined;
  let psol: Expr = S.Zero;
  let sign = p.order % 2 === 0 ? 1 : -1;
  for (const g of gensols) {
    const others = gensols.filter((h) => h !== g);
    psol = add(psol, mul(sign, integrate(mul(wronskian(others, p.x), r.get(-1)!, pow(wr, -1)), p.x), g, pow(r.get(p.order)!, -1)));
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
  const lead = m.get(p.order)!;
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
        gsol = add(gsol, mul(pow(log(x), i), pow(x, root), cs.pop()!));
        gens.push(mul(pow(log(x), i), pow(x, root)));
      } else {
        const rr = re(root);
        const ii = im(root);
        gsol = add(gsol, mul(pow(log(x), i), pow(x, rr), add(mul(cs.pop()!, sin(mul(abs(ii), log(x)))), mul(cs.pop()!, cos(mul(ii, log(x)))))));
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
  if (!r || !isZero(r.get(-1)!)) return undefined;
  return [eulerCharacteristicSols(p, r)[0]];
};

const eulerUndetermined: Solver = (p) => {
  const r = eulerMatch(p);
  if (!r || isZero(r.get(-1)!)) return undefined;
  // substitute x = exp(t): a linear equation with constant coefficients in t
  const s = new Dummy('x');
  const x = p.x;
  const pc = polyCoefficients(eulerChareq(r, x, s), s);
  if (!pc) return undefined;
  const rhs = simplify(xreplace(r.get(-1)!, [[x, exp(x)]]));
  if (!trialSet(rhs, x)) return undefined;
  let eq: Expr = S.Zero;
  for (const [k, c] of pc) eq = add(eq, mul(c, D(p, k)));
  eq = add(eq, rhs);
  const sub: OdeProblem = { eq, fx: p.fx, x, order: p.order };
  const sols = undeterminedCoefficients(sub);
  if (!sols) return undefined;
  const s0 = sols[0] as Rel;
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
  if (xreplace(p.eq, [[D(p, n), t]]).has(p.fx)) return undefined;
  const g = new UndefFn('_g', [p.x]);
  let geq = p.eq;
  for (const k of [...ords].sort((a, b) => b - a)) geq = xreplace(geq, [[D(p, k), k === n ? g : derivative(g, [[p.x, k - n]], true)]]);
  const gsol = dsolveRaw(geq, g as UndefFn);
  if (!gsol) return undefined;
  const out: Expr[] = [];
  for (const gs of gsol) {
    const gr = gs as Rel;
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
  const sols: Expr[] = [];
  for (const e of eqs) {
    const s = dsolveRaw(e, p.fx);
    if (s) sols.push(...s);
  }
  return sols.length ? sols : undefined;
};

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
  ['nth_linear_constant_coeff_variation_of_parameters', variationOfParameters],
  ['Liouville', liouville],
  ['nth_order_reducible', nthOrderReducible],
  ['nth_algebraic', nthAlgebraic],
];

/** The hints (SymPy classify_ode names) that match the equation, in SymPy's order. */
export function classifyOde(eqIn: ExprLike, fx: UndefFn): string[] {
  const eq = toZeroForm(sympify(eqIn));
  const p: OdeProblem = { eq, fx, x: fx.args[0] as Sym, order: orderOf(eq, fx) };
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
  const p: OdeProblem = { eq, fx, x: fx.args[0] as Sym, order: orderOf(eq, fx) };
  if (p.order === 0) return undefined;
  for (const [h, s] of HINTS) {
    if (hint && hint !== 'default' && h !== hint) continue;
    let raw: Expr[] | undefined;
    try {
      raw = s(p);
    } catch (err) {
      if (process.env['SYMJS_DEBUG_ODE']) console.error(h, err);
      raw = undefined;
    }
    if (!raw) continue;
    try {
      const out: Expr[] = [];
      for (const r of raw) out.push(...odesimp(eq, r, fx, h));
      return out;
    } catch (err) {
      if (process.env['SYMJS_DEBUG_ODE']) console.error(h, 'odesimp', err);
      continue;
    }
  }
  return undefined;
}

export const __debug = { eulerMatch, linearCoefficients, eulerHomogeneous, nthOrderReducible, orderOf };
