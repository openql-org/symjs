// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sums and products (SymPy Sum/Product/summation/product).
 */

import { Expr, ExprLike, Mul, Pow, Rational, S, Special, Sym, impl } from '../core/nodes';
import { Lt, piecewise } from '../core/logic';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { abs, log, sin, tan } from '../functions/elementary';
import { bernoulliNumber, factorial, rf } from '../functions/special';
import { polyCoefficients, roots } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { Concrete } from './node';

export { Concrete };

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';

/** Unevaluated Sum(f, (k, a, b), ...). */
export function Sum(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Sum', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** Unevaluated Product(f, (k, a, b), ...). */
export function Product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Product', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** S_p(n) = sum_{k=1}^{n} k^p (Faulhaber, with B_1 = +1/2). */
function powerSum(p: number, n: Expr): Expr {
  const terms: Expr[] = [];
  for (let j = 0; j <= p; j++) {
    const binom = choose(p + 1, j);
    terms.push(mul(binom, bernoulliNumber(j), pow(n, p + 1 - j)));
  }
  return expand(mul(Rational.of(1, p + 1), add(...terms)));
}

function choose(n: number, k: number): Rational {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return Rational.of(r);
}

/** Closed form of sum_{k=a}^{b} f, or undefined. */
function sumOne(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if (!f.has(k)) {
    if (isOo(b) || (a instanceof Special && a.name === '-oo')) return undefined;
    return expand(mul(f, add(b, mul(-1, a), 1)));
  }
  // Karr convention for reversed limits
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) {
    const r = sumOne(f, k, add(b, 1), add(a, -1));
    return r === undefined ? undefined : mul(-1, r);
  }
  // explicit evaluation for short finite ranges
  if (isInt(diff_) && diff_.p >= -1n && diff_.p <= 1000n) {
    const terms: Expr[] = [];
    for (let i = 0n; i <= diff_.p; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
    return add(...terms);
  }
  if (isOo(b) || isNegOo(a)) {
    const r = evalSumResidue(f, k, a, b);
    if (r) return r;
  }
  const ef = expand(f);
  const pc = polyCoefficients(ef, k);
  if (pc && !isOo(b)) {
    const parts: Expr[] = [];
    for (const [p, c] of pc) {
      parts.push(mul(c, add(powerSum(p, b), mul(-1, powerSum(p, add(a, -1))))));
    }
    return expand(add(...parts));
  }
  // c * r**k (geometric)
  const factors = ef instanceof Mul ? ef.args : [ef];
  const dep = factors.filter((g) => g.has(k));
  const c = mul(...factors.filter((g) => !g.has(k)));
  if (dep.length === 1 && dep[0] instanceof Pow && !dep[0].base.has(k)) {
    const P = dep[0];
    const ePc = polyCoefficients(P.exp, k);
    if (ePc && Math.max(...ePc.keys()) === 1) {
      const r = pow(P.base, ePc.get(1)!);
      const first = xreplace(ef, [[k, a]]);
      if (isOo(b)) {
        const closed = mul(first, pow(add(1, mul(-1, r)), -1));
        const rv = numeric(r);
        if (rv !== undefined) return Math.abs(rv) < 1 ? closed : undefined;
        return piecewise([closed, Lt(abs(r), 1)], [Sum(f, [k, a, b]), true]);
      }
      return mul(c, add(pow(r, a), mul(-1, pow(r, add(b, 1)))), pow(add(1, mul(-1, r)), -1));
    }
  }
  // exponential series: x**k / k! from 0 to oo
  if (isOo(b) && a instanceof Rational && a.isZero) {
    const num = factors.find((g) => g instanceof Pow && g.exp.key === k.key);
    const den = factors.find((g) => g instanceof Pow && g.exp instanceof Rational && g.exp.p === -1n && g.base.key === factorial(k).key);
    if (num && den && factors.length === 2) return exp((num as Pow).base);
  }
  return undefined;
}

/**
 * Port of SymPy eval_sum_residue: sums of rational functions (optionally
 * times (-1)**k) over infinite ranges via residues of f*cot(pi*z) (or
 * f*csc(pi*z)). Only simple poles are handled.
 */
function evalSumResidue(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if ([...freeSymbols(f)].some((s) => s.key !== k.key)) return undefined;
  if (!(isInt(a) || isOo(a) || isNegOo(a)) || !(isInt(b) || isOo(b) || isNegOo(b))) return undefined;
  const ratCoeffs = (e: Expr): [Map<number, Expr>, Map<number, Expr>] | undefined => {
    const [n, d] = fractionOf(e);
    const pn = polyCoefficients(expand(n), k);
    const pd = polyCoefficients(expand(d), k);
    return pn && pd ? [pn, pd] : undefined;
  };
  let alternating = false;
  let m = ratCoeffs(f);
  if (!m) {
    m = ratCoeffs(mul(f, pow(-1, mul(-1, k))));
    if (!m) return undefined;
    alternating = true;
  }
  let [pn, pd] = m;
  const deg = (p: Map<number, Expr>) => Math.max(-Infinity, ...[...p].filter(([, c]) => !(c instanceof Rational && c.isZero)).map(([i]) => i));
  const toExpr = (p: Map<number, Expr>) => add(...[...p].map(([i, c]) => mul(c, pow(k, i))));
  if (deg(pd) - deg(pn) < 2) return undefined;
  const isEven = () => {
    const ms = (p: Map<number, Expr>) => [...p].filter(([, c]) => !(c instanceof Rational && c.isZero)).map(([i]) => i);
    const all = (p: Map<number, Expr>, r: number) => ms(p).every((i) => i % 2 === r);
    return (all(pn, 0) && all(pd, 0)) || (all(pn, 1) && all(pd, 1));
  };
  // poles: all roots of the denominator, which must be simple
  const poles = (): [Rational[], Expr[]] | undefined => {
    const D = toExpr(pd);
    let rs: Expr[] | undefined;
    try {
      rs = roots(D, k);
    } catch {
      return undefined;
    }
    if (!rs || rs.length !== deg(pd) || new Set(rs.map((r) => r.key)).size !== rs.length) return undefined;
    return [rs.filter(isInt), rs.filter((r) => !isInt(r))];
  };
  const residues = (rs: Expr[]): Expr => {
    const N = toExpr(pn);
    const dD = add(...[...pd].map(([i, c]) => mul(i, c, pow(k, i - 1))));
    return add(
      ...rs.map((r) => {
        const res = mul(xreplace(N, [[k, r]]), pow(xreplace(dD, [[k, r]]), -1));
        const piR = mul(S.Pi, r);
        if (isInt(r)) return alternating ? mul(res, pow(-1, r)) : res;
        return mul(res, pow(alternating ? sin(piR) : tan(piR), -1));
      }),
    );
  };
  if (isNegOo(a) && isOo(b)) {
    const ps = poles();
    if (!ps || ps[0].length) return undefined;
    return mul(-1, S.Pi, residues(ps[1]));
  }
  if (!(isInt(a) && isOo(b))) return undefined;
  if (!isEven()) {
    const n = deg(pd);
    const lead = pd.get(n)!;
    const sub = pd.get(n - 1) ?? S.Zero;
    const shift = mul(-1, sub, pow(lead, -1), Rational.of(1, n));
    if (!isInt(shift) || shift.isZero) return undefined;
    const sh = (p: Map<number, Expr>) => expand(xreplace(toExpr(p), [[k, add(k, shift)]]));
    const nn = sh(pn);
    const dd = sh(pd);
    pn = polyCoefficients(nn, k)!;
    pd = polyCoefficients(dd, k)!;
    if (!isEven()) return undefined;
    const g = alternating ? mul(pow(-1, k), pow(-1, shift), nn, pow(dd, -1)) : mul(nn, pow(dd, -1));
    return evalSumResidue(g, k, add(a, mul(-1, shift)), b);
  }
  const ps = poles();
  if (!ps) return undefined;
  const [intRoots, nonInt] = ps;
  const ints = intRoots.map((r) => Number(r.p));
  if (ints.length) {
    const mx = Math.max(...ints);
    if (ints.length !== mx - Math.min(...ints) + 1) return undefined;
    if (Number(a.p) <= mx) return undefined;
  }
  const full = mul(-1, S.Pi, residues([...intRoots, ...nonInt]));
  const at = (i: number) => xreplace(f, [[k, Rational.of(i)]]);
  const ai = Number(a.p);
  if (!ints.length) {
    const half = mul(add(full, at(0)), Rational.of(1, 2));
    const neg: Expr[] = [];
    const pos: Expr[] = [];
    for (let i = ai; i < 0; i++) neg.push(at(i));
    for (let i = 0; i < ai; i++) pos.push(at(i));
    return add(half, ...neg, mul(-1, add(...pos)));
  }
  const extra: Expr[] = [];
  for (let i = Math.max(...ints) + 1; i < ai; i++) extra.push(at(i));
  return add(mul(full, Rational.of(1, 2)), mul(-1, add(...extra)));
}

function numeric(e: Expr): number | undefined {
  if (freeSymbols(e).size) return undefined;
  try {
    const v = e.toComplex();
    return Math.abs(v.im) < 1e-14 ? v.re : undefined;
  } catch {
    return undefined;
  }
}

function productOne(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) {
    const r = productOne(f, k, add(b, 1), add(a, -1));
    return r === undefined ? undefined : pow(r, -1);
  }
  if (isInt(diff_) && diff_.p >= -1n && diff_.p <= 1000n) {
    const terms: Expr[] = [];
    for (let i = 0n; i <= diff_.p; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
    return mul(...terms);
  }
  return evalProduct(f, k, a, b);
}

/** Port of SymPy Product._eval_product for the indefinite cases. */
function evalProduct(term: Expr, k: Sym, a: Expr, n: Expr): Expr | undefined {
  const count = add(n, mul(-1, a), 1);
  if (!term.has(k)) return term instanceof Rational && term.isOne ? S.One : pow(term, count);
  if (a.key === n.key) return xreplace(term, [[k, a]]);
  const pc = polyCoefficients(expand(term), k);
  if (pc) {
    const deg = Math.max(...pc.keys());
    let rs: Expr[];
    try {
      rs = roots(expand(term), k);
    } catch {
      rs = [];
    }
    const mult = new Map<string, [Expr, number]>();
    for (const r of rs) {
      const cur = mult.get(r.key);
      mult.set(r.key, [r, (cur ? cur[1] : 0) + 1]);
    }
    let A: Expr = S.One;
    let M = 0;
    for (const [r, m] of mult.values()) {
      M += m;
      A = mul(A, pow(rf(add(a, mul(-1, r)), count), m));
    }
    if (M < deg) return undefined;
    return mul(pow(pc.get(deg)!, count), A);
  }
  if (term instanceof Mul) {
    const without = term.args.filter((t) => !t.has(k));
    const withK = term.args.filter((t) => t.has(k));
    const parts: Expr[] = [];
    for (const t of withK) {
      const p = evalProduct(t, k, a, n);
      if (p === undefined) return undefined;
      parts.push(p);
    }
    return mul(pow(mul(...without), count), ...parts);
  }
  if (term instanceof Pow) {
    if (!term.base.has(k)) return pow(term.base, summation(term.exp, [k, a, n]));
    if (!term.exp.has(k)) {
      const p = evalProduct(term.base, k, a, n);
      if (p !== undefined) return pow(p, term.exp);
    }
  }
  return undefined;
}

/** Evaluate sums and products (SymPy summation / doit). */
export function summation(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  let e = sympify(f);
  for (const [k, a, b] of limits) {
    const r = sumOne(e, k, sympify(a), sympify(b));
    if (r === undefined) return Sum(e, [k, a, b]);
    e = r;
  }
  return e;
}

export function product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  let e = sympify(f);
  for (const [k, a, b] of limits) {
    const r = productOne(e, k, sympify(a), sympify(b));
    if (r === undefined || r.key === S.NaN.key) return Product(e, [k, a, b]);
    e = r;
  }
  return e;
}

/** doit() for a Concrete node. */
export function doitConcrete(c: Concrete): Expr {
  const lims = c.limits.map(([k, a, b]) => [k as Sym, a, b] as [Sym, Expr, Expr]);
  return c.kind2 === 'Sum' ? summation(c.function, ...lims) : product(c.function, ...lims);
}

/** Reverse the order of the given limits (by index or variable), SymPy reverse_order. */
export function reverseOrder(c: Concrete, ...which: (number | Sym)[]): Expr {
  const lims = c.limits.map((l) => [...l] as [Expr, Expr, Expr]);
  let f = c.function;
  for (const w of which) {
    const i = typeof w === 'number' ? w : lims.findIndex(([k]) => k.key === w.key);
    const [k, a, b] = lims[i]!;
    lims[i] = [k, add(b, 1), add(a, -1)];
    f = c.kind2 === 'Sum' ? mul(-1, f) : pow(f, -1);
  }
  return new Concrete(c.kind2, [f, ...lims.flat()]);
}


const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isFiniteBound = (e: Expr) => !(e instanceof Special);

/** Limit of f(k) as k -> oo, or undefined. */
function limOo(f: Expr, k: Sym): Expr | undefined {
  try {
    return impl.limit(f, k, S.Infinity);
  } catch {
    return undefined;
  }
}

/** Decay order p of a rational function f(k) ~ C*k**(-p) (or k**(-p) with rational p). */
function pSeriesOrder(f: Expr, k: Sym): number | undefined {
  if (f instanceof Pow && f.base.key === k.key && f.exp instanceof Rational) return -f.exp.value;
  const [n, d] = fractionOf(f);
  const pn = polyCoefficients(expand(n), k);
  const pd = polyCoefficients(expand(d), k);
  if (!pn || !pd) return undefined;
  return Math.max(...pd.keys()) - Math.max(...pn.keys());
}

function fractionOf(f: Expr): [Expr, Expr] {
  const fs = f instanceof Mul ? f.args : [f];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const t of fs) {
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative) den.push(pow(t.base, mul(-1, t.exp)));
    else if (t instanceof Rational && !t.isInteger) {
      num.push(Rational.of(t.p));
      den.push(Rational.of(t.q));
    } else num.push(t);
  }
  return [mul(...num), mul(...den)];
}

/** SymPy Sum.is_convergent for common series tests (divergence, p-series, ratio, alternating). */
export function sumIsConvergent(c: Concrete): boolean | undefined {
  const [kE, a, b] = c.limits[0]!;
  const k = kE as Sym;
  const f = c.function;
  if (isFiniteBound(a) && isFiniteBound(b)) return true;
  if (isNegOo(a) || isNegOo(b)) return undefined;
  if (c.kind2 === 'Product') {
    const l = limOo(f, k);
    if (!(l instanceof Rational && l.isOne)) return false;
    return sumIsConvergent(new Concrete('Sum', [log(f), ...c.args.slice(1)]));
  }
  const l = limOo(f, k);
  if (l !== undefined && !(l instanceof Rational && l.isZero)) return false;
  // p-series: f ~ C*k**(-p) for rational functions
  const r = pSeriesOrder(f, k);
  if (r !== undefined) return r > 1;
  // limit comparison with a p-series: f ~ c*k**(-p) as k -> oo with real c != 0
  try {
    const t = new Sym('_t', { positive: true });
    const [c0, e0] = impl.leadterm!(xreplace(f, [[k, pow(t, -1)]]), t);
    if (e0 instanceof Rational && c0.freeSymbols().size === 0 && !(c0 instanceof Rational && c0.isZero)) {
      const cv = c0.toComplex();
      if (Math.abs(cv.im) < 1e-300 && cv.re !== 0) return e0.value > 1;
    }
  } catch {
    // no asymptotic expansion
  }
  // ratio test
  const ratio = limOo(impl.abs(mul(xreplace(f, [[k, add(k, 1)]]), pow(f, -1))), k);
  if (ratio !== undefined && ratio.freeSymbols().size === 0 && !(ratio instanceof Special)) {
    const v = ratio.toNumber();
    if (v < 1) return true;
    if (v > 1) return false;
  }
  if (ratio instanceof Special && ratio.name === 'oo') return false;
  // alternating series (-1)**k * g(k) with g -> 0 monotonically
  const fs = f instanceof Mul ? f.args : [f];
  const alt = fs.find((t) => t instanceof Pow && t.base instanceof Rational && t.base.p === -1n && t.base.q === 1n && t.exp.key === k.key);
  if (alt) {
    const g = mul(...fs.filter((t) => t !== alt));
    const lg = limOo(g, k);
    if (lg instanceof Rational && lg.isZero) return true;
  }
  return undefined;
}

/** Sum(|f|) converges. */
export function sumIsAbsolutelyConvergent(c: Concrete): boolean | undefined {
  return sumIsConvergent(new Concrete(c.kind2, [abs(c.function), ...c.args.slice(1)]));
}
