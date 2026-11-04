// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Single ODE solvers (port of SymPy solvers/ode/single.py and
 * nonhomogeneous.py): the hints are tried in SymPy's order and the raw
 * general solution is post-processed by odesimp.
 */

import { isReal } from '../core/assumptions';
import type { ExprLike } from '../core/nodes';
import { Add, Derivative, Dummy, Expr, Fn, Integral, Mul, Order, Pow, Rational, Rel, S, Special, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { at, cast, defined, expectType, first, getOrThrow } from '../core/guard';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, some, subs, xreplace } from '../core/traverse';
import { derivative } from '../core/undef';
import { diff } from '../calculus/diff';
import { evalf } from '../numeric/evalf';
import { abs, cos, fn, im, log, re, sin, tan } from '../functions/elementary/elementary';
import '../functions/special/bessel';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients, roots } from '../polys/poly';
import { factor, Poly } from '../polys/sympoly';
import { nroots } from '../polys/nroots';
import { CRootOf } from '../polys/rootof';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand, expandMul } from '../simplify/expand';
import { factorTerms } from '../simplify/exprtools';
import { powsimp } from '../simplify/powsimp';
import { collect } from '../simplify/radsimp';
import { cancel, fraction, together } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { simplify } from '../simplify/simplify';
import { trigsimp } from '../simplify/trigsimp';
import { odesimp } from './odesimp';
import { linsolve, solve } from './solve';
import { homogeneousOrder } from './homogeneous';
import { odeLieGroup } from './liegroup';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;

const isZero = (e: Expr) => e instanceof Rational && e.isZero;
/** The terms of a sum (an expression that is not a sum is one term). */
const addTerms = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
/** The factors of a product (an expression that is not a product is one factor). */
const mulFactors = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const C = (i: number) => new Sym(`C${i}`);

/** Numerical values of the roots of each polynomial with indexed roots (one nroots per polynomial). */
const indexedRootValues = new Map<string, { re: number; im: number }[]>();
/** The value of an indexed root (CRootOf), computed once for all the roots of its polynomial. */
function indexedRootValue(root: CRootOf): { re: number; im: number } {
  const key = root.poly.key;
  let vs = indexedRootValues.get(key);
  if (!vs) {
    vs = nroots(Poly.from(root.poly, [root.gen]), 15).map((v) => evalf(v, 15).toComplex());
    indexedRootValues.set(key, vs);
  }
  return at(vs, root.index);
}

export interface OdeProblem {
  eq: Expr;
  fx: UndefFn;
  x: Sym;
  order: number;
  /** User-given infinitesimals for the lie_group hint (dsolve's xi and eta). */
  infs?: { xi: ExprLike; eta: ExprLike };
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
  const terms = addTerms(e);
  const A: Expr[] = [];
  const B: Expr[] = [];
  for (const t of terms) {
    if (!t.has(df)) {
      A.push(t);
      continue;
    }
    const fs = mulFactors(t);
    const i = fs.findIndex((g) => g.key === df.key);
    if (i < 0) return undefined;
    const c = mul(...fs.filter((_, j) => j !== i));
    if (c.has(df)) return undefined;
    B.push(c);
  }
  // the equations are of first order, so some term has f'
  return [add(...A), add(...B)];
}

/** Coefficients of f^(k) (k = 0..order) and the remaining term (key -1), or undefined if not linear. */
function linearCoefficients(e: Expr, p: OdeProblem): Map<number, Expr> | undefined {
  const ex = expand(e);
  const out = new Map<number, Expr[]>();
  for (let k = -1; k <= p.order; k++) out.set(k, []);
  const ds = Array.from({ length: p.order + 1 }, (_, k) => D(p, k));
  for (const t of addTerms(ex)) {
    const fs = mulFactors(t);
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

const isSepDict = (v: unknown): v is Map<Sym | 'coeff', Expr> => v instanceof Map;

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

/** classify_ode is running the solvers (the Lie group method is not tried). */
let matching = false;

/**
 * e with f(x) for y; an integral in y left unevaluated gets f(x) as its upper
 * limit (SymPy's Integral(g(_y), (_y, f(x)))).
 */
const atFunction = (e: Expr, y: Sym, fx: UndefFn): Expr => (some(e, (u) => u instanceof Integral && u.variable.key === y.key) ? subs(e, [[y, fx]]) : xreplace(e, [[y, fx]]));

const separable: Solver = (p) => {
  if (p.order !== 1) return undefined;
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const [d, e] = parts;
  const y = new Dummy('y');
  const m1 = sepDict(xreplace(d, [[p.fx, y]]), p.x, y);
  const m2 = sepDict(xreplace(e, [[p.fx, y]]), p.x, y);
  if (!m1 || !m2) return undefined;
  // the dict form has an entry for each symbol and the coefficient
  const g = (m: Map<Sym | 'coeff', Expr>, k: Sym | 'coeff') => getOrThrow(m, k);
  const ly = integrate(mul(g(m2, 'coeff'), g(m2, y), pow(g(m1, y), -1)), y);
  const lhs = atFunction(ly, y, p.fx);
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
  return [Eq(atFunction(F, y, p.fx), C(1))];
};

/** f' + P f = Q normalized from the expanded equation. */
function linearFirst(p: OdeProblem): [Expr, Expr] | undefined {
  const parts = firstOrderParts(expand(p.eq), p);
  if (!parts) return undefined;
  const [A, B] = parts;
  if (B.has(p.fx)) return undefined;
  const a = expand(mul(A, pow(B, -1)));
  const pc = polyCoefficients(a, p.fx);
  if (!pc || Math.max(...pc.keys()) > 1) return undefined;
  const P = cancel(pc.get(1) ?? S.Zero);
  const Q = cancel(mul(-1, pc.get(0) ?? S.Zero));
  // polynomial coefficients in f(x) are free of f(x)
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
  for (const t of addTerms(a)) {
    const fs = mulFactors(t);
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
  for (const t of addTerms(e)) {
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
  // (order 0, an algebraic equation, as in SymPy's classify_ode)
  const n = p.order;
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
  // an irreducible factor without a formula: its roots as CRootOf (SymPy Poly.all_roots)
  let rs: Expr[];
  try {
    rs = roots(chareq, s);
  } catch {
    rs = Poly.from(chareq, [s]).allRoots();
  }
  const x = p.x;
  const counts = new Map<string, [Expr, number]>();
  for (const v of rs) counts.set(v.key, [v, (counts.get(v.key)?.[1] ?? 0) + 1]);
  const gensols: Expr[] = [];
  let collectterms: Term[] = [];
  const conj: string[] = [];
  const conjNum: { re: number; im: number }[] = [];
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
      let reroot = re(root);
      let imroot = im(root);
      let absIm = abs(imroot);
      // an indexed root (CRootOf): real or not, the sign of its imaginary part and its conjugate
      // (another index) are found numerically
      if (root instanceof CRootOf) {
        const c = indexedRootValue(root);
        if (Math.abs(c.im) < 1e-12) [reroot, imroot] = [root, S.Zero];
        absIm = c.im < 0 ? mul(-1, imroot) : imroot;
        if (conjNum.some((d) => Math.abs(d.re - c.re) + Math.abs(d.im + c.im) < 1e-9)) {
          collectterms = [[i, reroot, imroot], ...collectterms];
          continue;
        }
        conjNum.push(c);
      }
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
      gensols.push(mul(pow(x, i), exp(mul(reroot, x)), sin(mul(absIm, x))));
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
  // the remaining term (key -1) is free of f and its derivatives by construction
  for (const [k, c] of r) if (k >= 0 && (c.has(p.x) || c.has(p.fx))) return undefined;
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
  for (const i of addTerms(expr)) {
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
  // roots() finds all the roots of the characteristic polynomial or throws, so there are p.order solutions
  const [gensols, terms] = constCharacteristicSols(r, p);
  const cs = trial.map((_, i) => new Dummy(`a${i}`));
  const trialfunc = add(...trial.map((t, i) => mul(at(cs, i), t)));
  const eqs = expand(subFuncDoit(p.eq, p, trialfunc));
  const byTerm = new Map<string, Expr[]>();
  for (const t of addTerms(eqs)) {
    // with the single symbol x the dict form exists and has the entries x and coeff
    const m = expectType(separatevars(t, { dict: true, symbols: [p.x] }), isSepDict, 'separatevars dict');
    const k = getOrThrow(m, p.x).key;
    byTerm.set(k, [...(byTerm.get(k) ?? []), getOrThrow(m, 'coeff')]);
  }
  // the trial set holds every derivative of the right-hand side terms (times x while homogeneous), so the
  // coefficients exist
  const sol = defined(linsolve([...byTerm.values()].map((v) => add(...v)), cs), 'undetermined coefficients');
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
  // the fundamental solutions are linearly independent: the Wronskian is not zero
  let wr = trigsimp(simplify(wronskian(gensols, p.x)));
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
  // f^(n) occurs (n is the order), so its coefficient is not zero
  const lead = getOrThrow(m, p.order);
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

/**
 * SymPy _get_euler_characteristic_eq_sols: the homogeneous solution. A pair
 * of conjugate roots gives one sin and one cos term (SymPy writes both and
 * constantsimp removes the repeated ones).
 */
function eulerCharacteristicSols(p: OdeProblem, r: Map<number, Expr>): Expr {
  const s = new Dummy('x');
  const x = p.x;
  const chareq = eulerChareq(r, x, s);
  // an irreducible factor without a formula: its roots as CRootOf (SymPy rootof(chareq, k))
  let rs: Expr[];
  try {
    rs = sortRoots(roots(chareq, s));
  } catch {
    rs = Poly.from(chareq, [s]).allRoots();
  }
  const cs = Array.from({ length: rs.length }, (_, i) => C(i + 1)).reverse();
  const counts = new Map<string, [Expr, number]>();
  for (const v of rs) counts.set(v.key, [v, (counts.get(v.key)?.[1] ?? 0) + 1]);
  const conj = new Set<string>();
  let gsol: Expr = S.Zero;
  for (const [root, mult] of counts.values()) {
    if (conj.has(root.key)) continue;
    for (let i = 0; i < mult; i++) {
      // SymPy keeps x**CRootOf(...) for every indexed root, real or not
      if (root.kind === 'Extension' || isReal(root) === true) {
        gsol = add(gsol, mul(pow(log(x), i), pow(x, root), defined(cs.pop(), 'constant')));
      } else {
        const rr = re(root);
        const ii = im(root);
        conj.add(expand(add(rr, mul(-1, S.I, ii))).key);
        gsol = add(gsol, mul(pow(log(x), i), pow(x, rr), add(mul(defined(cs.pop(), 'constant'), sin(mul(abs(ii), log(x)))), mul(defined(cs.pop(), 'constant'), cos(mul(ii, log(x)))))));
      }
    }
  }
  return Eq(p.fx, gsol);
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
  return [eulerCharacteristicSols(p, r)];
};

const eulerUndetermined: Solver = (p) => {
  const r = eulerMatch(p);
  if (!r || isZero(getOrThrow(r, -1))) return undefined;
  // substitute x = exp(t): a linear equation with constant coefficients in t
  const s = new Dummy('x');
  const x = p.x;
  // the characteristic polynomial of an Euler equation
  const pc = defined(polyCoefficients(eulerChareq(r, x, s), s), 'characteristic polynomial');
  // x -> exp(x) with x positive (SymPy posify), so that log(exp(x)) = x
  const xp = new Dummy('x', { positive: true });
  const rhs = xreplace(simplify(xreplace(getOrThrow(r, -1), [[x, exp(xp)]])), [[xp, x]]);
  if (!trialSet(rhs, x)) return undefined;
  let eq: Expr = S.Zero;
  for (const [k, c] of pc) eq = add(eq, mul(c, D(p, k)));
  eq = add(eq, rhs);
  const sub: OdeProblem = { eq, fx: p.fx, x, order: p.order };
  // the transformed equation has constant coefficients and the right-hand side passed the trial test
  const sols = defined(undeterminedCoefficients(sub), 'undetermined coefficients solution');
  const s0 = cast(first(sols), Rel, 'solution');
  // exp(r*log(x)) -> x**r for a real indexed root r or its real part (SymPy's exp.eval: r is comparable)
  const lx = log(x);
  const realRootPow = (e: Expr): Expr => {
    if (!(e instanceof Pow) || e.base.key !== S.E.key || !(e.exp instanceof Mul) || e.exp.args.length !== 2 || !e.exp.args.some((u) => u.key === lx.key)) return e;
    // a CRootOf in an exponential is a real root (complex ones come as re(...) and im(...))
    const r0 = at(e.exp.args.filter((u) => u.key !== lx.key), 0);
    return r0 instanceof CRootOf || (r0 instanceof Fn && r0.name === 're') ? pow(x, r0) : e;
  };
  return [Eq(p.fx, expand(mapBottomUp(xreplace(s0.rhs, [[x, lx]]), realRootPow)))];
};

/**
 * SymPy nth_linear_euler_eq_nonhomogeneous_variation_of_parameters: the
 * homogeneous solutions of the Euler equation and a particular solution by
 * variation of parameters (SymPy _solve_variation_of_parameters).
 */
const eulerVariation: Solver = (p) => {
  const r = eulerMatch(p);
  if (!r || isZero(getOrThrow(r, -1))) return undefined;
  const hom = eulerCharacteristicSols(p, r).args[1];
  const gensols = Array.from({ length: p.order }, (_, i) => diff(defined(hom, 'homogeneous solution'), C(i + 1)));
  const wr = simplify(wronskian(gensols, p.x));
  // r is scaled so that f^(n) has the coefficient x**n
  const lead = pow(p.x, p.order);
  let psol: Expr = S.Zero;
  let sign = p.order % 2 === 0 ? 1 : -1;
  for (const g of gensols) {
    const others = gensols.filter((h) => h !== g);
    psol = add(psol, mul(sign, g, integrate(simplify(mul(wronskian(others, p.x), getOrThrow(r, -1), pow(mul(wr, lead), -1))), p.x)));
    sign = -sign;
  }
  return [Eq(p.fx, add(defined(hom, 'homogeneous solution'), simplify(psol)))];
};

/**
 * SymPy's classify_ode match of the power series hints: a homogeneous linear
 * second-order equation a3*f'' + b3*f' + c3*f = 0, with x = 0 an ordinary point
 * (b3/a3 and c3/a3 finite there) or a regular singular point (x*b3/a3 and
 * x**2*c3/a3 finite there). The coefficients come from the numerator when they
 * are not polynomials.
 */
function powerSeriesMatch(p: OdeProblem): { kind: 'ordinary' | 'regular'; r: Map<number, Expr> } | undefined {
  if (p.order !== 2) return undefined;
  let r = linearCoefficients(p.eq, p);
  if (r && [...r.values()].some((c) => !polyCoefficients(c, p.x))) r = linearCoefficients(expand(fraction(together(p.eq))[0]), p);
  if (!r || !isZero(getOrThrow(r, -1)) || [0, 1, 2].some((k) => getOrThrow(r, k).has(p.fx))) return undefined;
  const a3 = getOrThrow(r, 2);
  const finite = (e: Expr): boolean => {
    const v = xreplace(e, [[p.x, S.Zero]]);
    const bad = (u: Expr): boolean => u instanceof Special || u.args.some(bad);
    return !bad(v);
  };
  const P = cancel(mul(getOrThrow(r, 1), pow(a3, -1)));
  const Q = cancel(mul(getOrThrow(r, 0), pow(a3, -1)));
  if (finite(P) && finite(Q)) return { kind: 'ordinary', r };
  if (finite(cancel(mul(p.x, P))) && finite(cancel(mul(pow(p.x, 2), Q)))) return { kind: 'regular', r };
  return undefined;
}

/**
 * SymPy almost_linear: a(x)*l(y)' + b(x)*l(y) + c(x) = 0 with y = f(x), a linear
 * equation in l(f(x)): l(f) = (C1 + Integral(cx/ax*exp(Integral(bx/ax)))) * exp(-Integral(bx/ax)).
 */
const almostLinear: Solver = (p) => {
  const y = new Dummy('y');
  const de = firstOrderDE(p, y);
  if (!de) return undefined;
  // f' occurs (the order is 1), so its coefficient a is not zero
  const [d, a] = de;
  const terms = addTerms(d);
  const c = add(...terms.filter((t) => !t.has(y)));
  const b = add(...terms.filter((t) => t.has(y)));
  const db = diff(b, y);
  if (isZero(db) || simplify(mul(db, pow(a, -1))).has(y)) return undefined;
  const fb = factorTerms(b);
  const ly = mul(...mulFactors(fb).filter((u) => u.has(y)));
  const x = p.x;
  const ax = mul(a, pow(diff(ly, y), -1));
  const bx = mul(fb, pow(ly, -1));
  const cx = mul(-1, c);
  const ib = integrate(mul(bx, pow(ax, -1)), x);
  const rhs = mul(add(C(1), integrate(mul(cx, pow(ax, -1), exp(ib)), x)), exp(mul(-1, ib)));
  return [Eq(xreplace(ly, [[y, p.fx]]), rhs)];
};

/** The number of terms of the power series solutions (SymPy's default n = 6). */
const SERIES_TERMS = 6;

/**
 * SymPy ode_1st_power_series: f' = h(x, f) expanded at x = 0 with f(0) = C1,
 * the Taylor coefficients from the total derivatives of h; oo when h or a
 * derivative is not finite there.
 */
const firstPowerSeries: Solver = (p) => {
  const y = new Dummy('y');
  const de = firstOrderDE(p, y);
  if (!de || isZero(de[1])) return undefined;
  const x = p.x;
  const h = cancel(mul(-1, de[0], pow(de[1], -1)));
  const C1 = C(1);
  if (isZero(h)) return [Eq(p.fx, C1)];
  const at0 = (e: Expr): Expr => xreplace(e, [[x, S.Zero], [y, C1]]);
  const bad = (u: Expr): boolean => u instanceof Special || u.args.some(bad);
  let series: Expr = C1;
  let F = h;
  let fact = 1n;
  for (let k = 1; k < SERIES_TERMS; k++) {
    if (k > 1) F = add(diff(F, x), mul(diff(F, y), h));
    fact *= BigInt(k);
    const c = at0(F);
    // h or its first derivative not finite at x = 0: the hint does not match (SymPy classify_ode)
    if (bad(c)) return k <= 2 ? undefined : [Eq(p.fx, S.Infinity)];
    series = add(series, mul(c, pow(x, k), Rational.of(1n, fact)));
  }
  return [Eq(p.fx, add(series, new Order([pow(x, SERIES_TERMS)])))];
};

/**
 * SymPy ode_2nd_power_series_ordinary: f = C0 + C1*x + a2*x**2 + ... with the
 * coefficients a2, ..., a(terms - 2) from the recurrence, collected in C0, C1,
 * plus O(x**terms).
 */
const secondPowerSeriesOrdinary: Solver = (p) => {
  const m = powerSeriesMatch(p);
  if (m?.kind !== 'ordinary') return undefined;
  const x = p.x;
  const [C0, C1] = [C(1), C(2)];
  const coeffs: Expr[] = [C0, C1];
  for (let k = 2; k < SERIES_TERMS - 1; k++) {
    // the coefficient of x**(k - 2) in a3*f'' + b3*f' + c3*f with f = sum a_j*x**j, a_k unknown
    const a = new Dummy('a');
    const f = add(...[...coeffs, a].map((c, j) => mul(c, pow(x, j))));
    const lhs = expand(add(...[0, 1, 2].map((d) => mul(getOrThrow(m.r, d), diff(f, x, d)))));
    const pc = defined(polyCoefficients(lhs, x), 'polynomial in x');
    // a_k occurs in this coefficient
    const eq = getOrThrow(pc, k - 2);
    const ca = diff(eq, a);
    // x = 0 is an ordinary point, so a_k occurs
    coeffs.push(expand(mul(-1, xreplace(eq, [[a, S.Zero]]), pow(ca, -1))));
  }
  const series = add(...coeffs.map((c, j) => mul(c, pow(x, j))));
  return [Eq(p.fx, add(collect(expandMul(series), [C0, C1]), new Order([pow(x, SERIES_TERMS)])))];
};

/** The Taylor coefficients c_0, ..., c_n of e at x = 0. */
function taylorCoeffs(e: Expr, x: Sym, n: number): Expr[] {
  const out: Expr[] = [];
  let d = e;
  let fact = 1n;
  for (let i = 0; i <= n; i++) {
    if (i > 1) fact *= BigInt(i);
    out.push(cancel(mul(xreplace(d, [[x, S.Zero]]), Rational.of(1n, fact))));
    d = cancel(diff(d, x));
  }
  return out;
}

/**
 * SymPy _frobenius: the coefficients c_1, ..., c_n of the series
 * x**m*(c + c_1*x + ...), or undefined when (for the smaller root m of an
 * integer-spaced pair, at index check - m) no second series exists.
 */
function frobenius(n: number, m: Expr, ps: Expr[], qs: Expr[], c: Expr, check?: Expr): Expr[] | undefined {
  const [p0, q0] = [at(ps, 0), at(qs, 0)];
  const indicial = (d: Expr): Expr => add(mul(d, add(d, -1)), mul(d, p0), q0);
  const out: Expr[] = [];
  for (let i = 1; i <= n; i++) {
    let num = mul(c, add(mul(m, at(ps, i)), at(qs, i)));
    for (let j = 1; j < i; j++) num = add(num, mul(at(out, j - 1), add(mul(add(m, j), at(ps, i - j)), at(qs, i - j))));
    num = expand(num);
    if (check !== undefined && add(check, mul(-1, m)).key === Rational.of(i).key) {
      if (!isZero(num)) return undefined;
      out.push(S.Zero);
    } else out.push(mul(-1, num, pow(expand(indicial(add(m, i))), -1)));
  }
  return out;
}

/** SymPy ode_2nd_power_series_regular: Frobenius series at the regular singular point x = 0. */
const secondPowerSeriesRegular: Solver = (p) => {
  const mt = powerSeriesMatch(p);
  if (mt?.kind !== 'regular') return undefined;
  const x = p.x;
  const a3 = getOrThrow(mt.r, 2);
  const P = cancel(mul(x, getOrThrow(mt.r, 1), pow(a3, -1)));
  const Q = cancel(mul(pow(x, 2), getOrThrow(mt.r, 0), pow(a3, -1)));
  const [C0, C1] = [C(1), C(2)];
  const terms = SERIES_TERMS;
  const P0 = xreplace(P, [[x, S.Zero]]);
  const Q0 = xreplace(Q, [[x, S.Zero]]);
  const mm = new Dummy('m');
  const ms = solve(add(mul(mm, add(mm, -1)), mul(mm, P0), Q0), mm);
  // real rational exponents only (the number of terms depends on them)
  if (!ms.length || !ms.every((v) => v instanceof Rational)) return undefined;
  const rs = ms.filter((v): v is Rational => v instanceof Rational).sort((a, b) => b.value - a.value);
  const m1 = first(rs);
  const nTerms = (m: Rational) => Math.trunc(terms - m.value - 1);
  const ser = (m: Rational, c: Expr, cs: Expr[]) => mul(pow(x, m), add(c, ...cs.map((v, i) => mul(v, pow(x, i + 1)))));
  // SymPy: Eq(f(x), Order(terms)), which is O(1)
  if (nTerms(m1) <= 0) return [Eq(p.fx, new Order([S.One]))];
  const N = Math.max(...rs.map(nTerms));
  const ps = taylorCoeffs(P, x, N);
  const qs = taylorCoeffs(Q, x, N);
  const s1 = ser(m1, C0, defined(frobenius(nTerms(m1), m1, ps, qs, C0), 'first Frobenius series'));
  let s2: Expr = S.Zero;
  if (rs.length === 2) {
    const m2 = at(rs, 1);
    const integer = (m1.p * m2.q - m2.p * m1.q) % (m1.q * m2.q) === 0n;
    const c2 = frobenius(nTerms(m2), m2, ps, qs, C1, integer ? m1 : undefined);
    if (c2) s2 = ser(m2, C1, c2);
  }
  return [Eq(p.fx, add(collect(add(s1, s2), [C0, C1]), new Order([pow(x, terms)])))];
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
  for (const t of addTerms(e0)) {
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
  if (!gsol.length) return undefined;
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

/**
 * Basic.compare of two numbers: the singletons One and NegativeOne are classes
 * of their own, ordered before Integer (ordering_of_classes); numbers of one
 * class compare by value.
 */
function numberCompare(a: Rational, b: Rational): number {
  // a term of a sum is never zero, and factor gives integer coefficients: One, NegativeOne or Integer
  const rank = (r: Rational): number => (r.p === 1n ? 1 : r.p === -1n ? 5 : 7);
  const d = rank(a) - rank(b);
  if (d) return d;
  const v = a.p * b.q - b.p * a.q;
  return Number(v > 0n) - Number(v < 0n);
}

const factorable: Solver = (p) => {
  const eq0 = p.eq;
  // (a failure of factor is caught by the driver like any failing solver)
  const eq = fraction(factor(eq0))[0];
  const fs = mulFactors(eq);
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
    // like Basic.compare for sums: the number of terms first, then the (sorted) terms one by one
    const ta = [...addTerms(a)].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
    const tb = [...addTerms(b)].sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
    if (ta.length !== tb.length) return ta.length - tb.length;
    const cmpTerm = (u: Expr, v: Expr): number => (u instanceof Rational && v instanceof Rational ? numberCompare(u, v) : compareKeys(sortKey(u), sortKey(v)));
    // distinct factors differ in some term
    for (let i = 0; i < ta.length - 1; i++) {
      const c = cmpTerm(at(ta, i), at(tb, i));
      if (c) return c;
    }
    return cmpTerm(at(ta, -1), at(tb, -1));
  };
  eqs = [...eqs].sort(argCmp);
  const sols: Expr[] = [];
  for (const e of eqs) {
    sols.push(...dsolveRaw(e, p.fx));
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
  // polynomial coefficients are free of x
  const m = getOrThrow(pc, 1);
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
  const terms = addTerms(c3);
  const dep = terms.filter((t) => t.has(x));
  const ind = add(...terms.filter((t) => !t.has(x)));
  if (dep.length !== 1) return undefined;
  const pd = polyCoefficients(first(dep), x);
  if (pd?.size !== 1) return undefined;
  const [e2, alpha2] = first([...pd.entries()]);
  // d may be a half integer (x**2*f'' + x*f' + (x - 4)*f: besselj(4, 2*sqrt(x)))
  const d = Rational.of(e2, 2);
  const alpha = sqrt(alpha2);
  const nsq = mul(-1, ind);
  const n = sqrt(add(nsq, mul(Rational.of(1, 4), pow(add(c4, -1), 2))));
  const argB = mul(alpha, pow(x, d), pow(d, -1));
  const nu = mul(n, pow(d, -1));
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
  // both parts are free of f' (firstOrderParts)
  const e = cancel(xreplace(parts[1], [[p.fx, y]]));
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

/**
 * SymPy ode_sol_simplicity: solved for f(x) first, then shortest (the candidates are free of
 * Integrals: homogeneousSolution gives up on an unevaluated integral).
 */
function solSimplicity(sols: Expr[], fx: Expr): number {
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
  // SymPy HomogeneousCoeffBest._verify: d + u*e at (1, u) and e + u*d at (u, 1) are not zero; d/e is
  // homogeneous of order 0, so both vanish exactly when d/e = -y/x and the first test decides
  const u = new Dummy('u');
  if (isZero(simplify(subs(add(m.d, mul(u, m.e)), [[p.x, 1], [m.y, u]])))) return undefined;
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

/** SymPy LieGroup: the Lie group method for first-order equations (solvers/liegroup.ts). */
const lieGroup: Solver = (p) => {
  // classify_ode decides the other hints without the (slow) Lie group method, which matches every first-order equation
  if (p.order !== 1 || matching) return undefined;
  return odeLieGroup(p.eq, p.fx, (eq, fx) => dsolveRaw(eq, fx), p.infs);
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
  ['almost_linear', almostLinear],
  ['linear_coefficients', linearCoefficientsSolver],
  ['nth_linear_constant_coeff_variation_of_parameters', variationOfParameters],
  ['nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', eulerVariation],
  // SymPy reaches f'' + f'**2 = 0 through factorable/nth_order_reducible before Liouville
  ['nth_order_reducible', nthOrderReducible],
  ['Liouville', liouville],
  ['2nd_linear_airy', airy],
  ['2nd_linear_bessel', bessel],
  ['nth_algebraic', nthAlgebraic],
  ['2nd_power_series_ordinary', secondPowerSeriesOrdinary],
  ['2nd_power_series_regular', secondPowerSeriesRegular],
  // SymPy's solver_map ends with lie_group, which matches every first-order equation
  ['lie_group', lieGroup],
  // SymPy's default for a first-order equation is lie_group, which matches before: this one is used on request
  ['1st_power_series', firstPowerSeries],
];

/**
 * Hints whose match is decided without solving (variation of parameters needs
 * Wronskians and integrals, which can be expensive, e.g. with CRootOf roots).
 */
const MATCHERS = new Map<string, (p: OdeProblem) => boolean>([
  ['lie_group', (p) => p.order === 1],
  ['nth_linear_constant_coeff_variation_of_parameters', (p) => {
    const r = constantCoeffMatch(p);
    return r !== undefined && !isZero(getOrThrow(r, -1));
  }],
  ['nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', (p) => {
    const r = eulerMatch(p);
    return r !== undefined && !isZero(getOrThrow(r, -1));
  }],
]);

/** The hints with a solver here that match the equation (solver order). */
function solverHints(eqIn: ExprLike, fx: UndefFn): string[] {
  const eq = toZeroForm(sympify(eqIn));
  const p: OdeProblem = { eq, fx, x: independentVariable(fx), order: orderOf(eq, fx) };
  matching = true;
  try {
    return HINTS.filter(([h, s]) => {
      try {
        const m = MATCHERS.get(h);
        if (m) return m(p);
        return s(p) !== undefined;
      } catch {
        return false;
      }
    }).map(([h]) => h);
  } finally {
    matching = false;
  }
}

function toZeroForm(e: Expr): Expr {
  return e instanceof Rel && e.op === 'Eq' ? add(e.lhs, mul(-1, e.rhs)) : e;
}

/** Solve with the first matching hint (no solution: []); the solutions are post-processed with odesimp. */
export function dsolveRaw(eqIn: Expr, fx: UndefFn, hint?: string, infs?: { xi: ExprLike; eta: ExprLike }): Expr[] {
  const eq = toZeroForm(eqIn);
  const p: OdeProblem = { eq, fx, x: independentVariable(fx), order: orderOf(eq, fx), ...(infs ? { infs } : {}) };
  if (p.order === 0) return [];
  for (const [h, s] of HINTS) {
    if (hint && hint !== 'default' && h !== hint) continue;
    if ((!hint || hint === 'default') && h === '1st_power_series') continue;
    let raw: Expr[] | undefined;
    try {
      raw = s(p);
    } catch {
      raw = undefined;
    }
    if (!raw) continue;
    // like SymPy, a failure of odesimp is not caught
    const out: Expr[] = [];
    if (PRESIMPLIFIED.has(h)) out.push(...raw);
    else for (const r of raw) out.push(...odesimp(eq, r, fx, h));
    return out;
  }
  return [];
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
  const terms = addTerms(ex);
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
    const factors = mulFactors(fac);
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
  const ps = powerSeriesMatch(p);
  if (ps) out.add(`2nd_power_series_${ps.kind}`);
  const de = firstOrderDE(p, y);
  if (de) {
    const [d, e] = de;
    // Bernoulli: f' + P*f - Q*f**n (linear equations included)
    const rest = expandMul(mul(d, pow(e, -1)));
    const exps = new Set<string>();
    let bern = !isZeroE(e);
    for (const t of addTerms(rest)) {
      const fs = mulFactors(t);
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
      const od = homogeneousOrder(separateExpr(d), x, y);
      const oe = homogeneousOrder(separateExpr(e), x, y);
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
