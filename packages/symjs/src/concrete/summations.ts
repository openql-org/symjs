// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sums and products (SymPy Sum/Product/summation/product).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { Add, Dummy, ExtensionExpr, Fn, Integral, Limit, Mul, Piecewise, Pow, Rational, Rel, S, Special, Sym, Wild, asRational, impl, isNum, registerRewrite } from '../core/nodes';
import { asIndependent, asNumerDenom } from '../core/methods';
import { apart } from '../polys/partfrac';
import { cancel, fraction, together } from '../simplify/rational';
import { factor } from '../polys/sympoly';
import { hyperexpand } from '../simplify/hyperexpand';
import { Hyper, hyper } from '../functions/special/hyper';
import { BoolOp, and, not } from '../core/boolalg';
import { isIntegerQ, isNegative, isNonNegative, isPositive, isZero as isZeroQ } from '../core/assumptions';
import { Eq, Gt, Le, Lt, piecewise } from '../core/logic';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, some, subs, xreplace } from '../core/traverse';
import { abs, fn, log, re, sin, tan } from '../functions/elementary/elementary';
import { bernoulliNumber, factorial, harmonic, zeta } from '../functions/special/special';
import { contains, Naturals0 } from '../sets/sets';
import { fact } from '../core/exprfacts';
import { rf } from '../functions/combinatorial/factorials';
import { polyCoefficients, roots } from '../polys/poly';
import { expand as expandFull, expandMul, withFactoredDenominators } from '../simplify/expand';

/** Distribution over sums with the denominators left factored: the summation rules match the factors of a term. */
const expand = (e: ExprLike): Expr => withFactoredDenominators(() => expandMul(e));
import { combsimp, hypersimp } from '../simplify/gammasimp';
import { powsimp } from '../simplify/powsimp';
import { factorTerms } from '../simplify/exprtools';
import { match } from '../core/match';
import { residue } from '../series/residues';
import { Concrete } from './node';

export { Concrete };

/** Gosper summation is registered by the calculus entry alongside its solver dependencies. @internal */
export const summationHooks: { gosperSum?: (f: Expr, limits: [Sym, Expr, Expr]) => Expr | NoMatchResult } = {};

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';

export { Sum, Product } from '../core/concrete';
import { Sum, Product } from '../core/concrete';
import { at, cast, defined, first, getOrThrow, pair } from '../core/guard';
import { NoMatch, isNoMatch, orNoMatch } from '../core/truth';
import type { NoMatchResult } from '../core/truth';

registerRewrite('Concrete', 'Sum', (args, self) => self instanceof Concrete && self.kind2 === 'Product'
  ? exp(new Concrete('Sum', [log(first(args)), ...args.slice(1)])) : undefined);
registerRewrite('Concrete', 'Product', (args, self) => self instanceof Concrete && self.kind2 === 'Sum' && fact(first(args), 'extended_real') === true
  ? log(new Concrete('Product', [exp(first(args)), ...args.slice(1)])) : undefined);

/**
 * Evaluate an infinite rational sum by residues, or return NoMatch.
 *
 * @param f - The summand.
 * @param limits - The triple `[k, a, b]` giving the index and inclusive endpoints.
 * @returns The value of the infinite sum, or `NoMatch` when the residue method does not apply.
 * @see SymPy `sympy.concrete.summations.eval_sum_residue`
 * @example
 * ```ts
 * import { evalSumResidue, ex, oo, symbols } from '@symjs/symjs';
 *
 * evalSumResidue(ex`1/k**2`, [symbols('k')[0], 1, oo]); // => pi**2/6
 * ```
 */
export function evalSumResidue(f: ExprLike, [k, a, b]: readonly [Sym, ExprLike, ExprLike]): Expr | NoMatchResult {
  const upper = sympify(b);
  if (!isOo(upper)) return NoMatch;
  return orNoMatch(evalSumResidueImpl(sympify(f), k, sympify(a), upper));
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
function sumOne(fIn: Expr, k: Sym, a: Expr, b: Expr, mirrored = false): Expr | undefined {
  const simplified = powsimp(fIn);
  const f = simplified.has(k) ? fIn : simplified;
  if (isOo(a) && !isOo(b)) {
    const r = sumOne(f, k, add(b, 1), S.Infinity);
    return r === undefined ? undefined : xreplace(r, [[new Concrete('Sum', [f, k, add(b, 1), S.Infinity]), new Concrete('Sum', [f, k, a, b])]]);
  }
  if (!f.has(k)) {
    if (isOo(b) || isNegOo(a)) return f instanceof Rational && f.isZero ? S.Zero : mul(f, S.Infinity);
    return expand(mul(f, add(b, mul(-1, a), 1)));
  }
  // Karr convention for reversed limits (a range with a known length always has a sum)
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) return mul(-1, defined(sumOne(f, k, add(b, 1), add(a, -1)), 'sum over a finite range'));
  // a Kronecker delta in k picks one term (SymPy deltasummation)
  if (hasDelta(f, k)) {
    const d = deltaSum(f, k, a, b);
    if (d !== undefined) return d;
  }
  // a Piecewise whose conditions do not contain k: the Piecewise of the sums (SymPy eval_sum)
  if (f instanceof Piecewise && !f.pairs.some(([, c]) => c.has(k))) {
    const sums = f.pairs.map(([e, c]) => [sumOne(e, k, a, b), c] as const);
    if (sums.every(([e]) => e !== undefined)) return piecewise(...sums.map(([e, c]) => [defined(e), c] as const));
  }
  // a Piecewise term whose condition bounds k: the sum over the range where it holds
  const pw = piecewiseRange(f, k, a, b);
  if (pw !== undefined) return pw;
  // Pull constant matrix factors off the ends without commuting them across the summand.
  if (f instanceof ExtensionExpr && f.name === 'MatMul') {
    if (!isInt(diff_)) return undefined;
    const dependent = f.args.filter(t => t.has(k));
    if (dependent.length === 1) {
      const body = first(dependent);
      const term = directSum(body, k, a, diff_.p);
      return f.withArgs(f.args.map(t => t === body ? term : t));
    }
  }
  // explicit evaluation for short finite ranges (SymPy: fewer than 100 terms)
  if (isInt(diff_) && diff_.p < 100n) return directSum(f, k, a, diff_.p);
  // Karr convention: sum_{k=a}^{-oo} f = -sum_{k=-oo}^{a-1} f
  if (isNegOo(b) && !isNegOo(a)) {
    const r = sumOne(f, k, b, add(a, -1));
    return r === undefined ? undefined : mul(-1, r);
  }
  // k -> -k turns sum_{k=-oo}^{b} into a sum ending at oo. SymPy's summation by residues takes only
  // sums from a finite a to oo and over all integers, so it leaves Sum(1/(k**2 + 1), (k, -oo, 0)) unevaluated
  if (isNegOo(a) && !isOo(b)) return sumOne(xreplace(f, [[k, mul(-1, k)]]), k, mul(-1, b), S.Infinity, true);
  if (isOo(b) && !mirrored) {
    const r = evalSumResidueImpl(f, k, a, b);
    if (r) return r;
  }
  // Binomial(n, k) vanishes at every negative integer k.
  const binomialTerm = (f instanceof Mul ? f.args : [f]).find(t => t instanceof Fn && t.name === 'binomial' && at(t.args, 1).equals(k));
  if (isNegOo(a) && isOo(b) && binomialTerm) {
    const negativeIndex = new Dummy('j', { negative: true, integer: true });
    const rest = mul(f, pow(binomialTerm, -1));
    if (fact(xreplace(rest, [[k, negativeIndex]]), 'finite') === true) return sumOne(f, k, S.Zero, b);
  }
  if (f instanceof Pow && f.base instanceof Add && isInt(f.exp) && f.exp.isNegative) {
    const factored = factorTerms(f);
    if (factored instanceof Mul) {
      const [coefficient, dependent] = splitFactors(factored, k);
      const value = sumOne(mul(...dependent), k, a, b);
      if (value !== undefined) return mul(coefficient, value);
    }
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
  // c * k**(-m) from a positive integer: generalized harmonic numbers (SymPy; harmonic(oo, m) = zeta(m))
  const [d0] = dep;
  if (dep.length === 1 && d0 instanceof Pow && d0.base.key === k.key && isInt(d0.exp) && d0.exp.isNegative && isInt(a) && a.isPositive) {
    const m = -d0.exp.p;
    const H = (u: Expr) => (m === 1n ? harmonic(u) : harmonic(u, Rational.of(m)));
    return mul(c, add(H(b), mul(-1, H(add(a, -1)))));
  }
  if (!isNegOo(a) && dep.length === 1 && d0 instanceof Pow && !d0.base.has(k)) {
    const P = d0;
    const ePc = polyCoefficients(P.exp, k);
    if (ePc && Math.max(...ePc.keys()) === 1) {
      const r = pow(P.base, getOrThrow(ePc, 1));
      const first = xreplace(ef, [[k, a]]);
      if (isOo(b)) {
        const closed = mul(first, pow(add(1, mul(-1, r)), -1));
        const rv = numeric(r);
        const fv = numeric(first);
        if (rv !== undefined) {
          if (Math.abs(rv) < 1) return closed;
          // a real geometric series with ratio >= 1 diverges to oo or -oo
          if (rv < 1 || fv === undefined || fv === 0) return undefined;
          return fv > 0 ? S.Infinity : S.NegativeInfinity;
        }
        return piecewise([closed, Lt(abs(r), 1)], [Sum(f, [k, a, b]), true]);
      }
      // c*base**(q + p*k) = c*base**q * r**k with r = base**p
      const c0 = mul(c, pow(P.base, ePc.get(0) ?? S.Zero));
      const closed = mul(add(pow(r, a), mul(-1, pow(r, add(b, 1)))), pow(add(1, mul(-1, r)), -1));
      // the closed form needs r != 1 (SymPy's Piecewise for a symbolic ratio)
      if (freeSymbols(r).size === 0) return mul(c0, closed);
      return mul(c0, piecewise([add(b, mul(-1, a), 1), Eq(r, 1)], [closed, true]));
    }
  }
  // exponential series: x**k / k! from 0 to oo
  if (isOo(b) && a instanceof Rational && a.isZero) {
    const num = factors.find((g): g is Pow => g instanceof Pow && g.exp.key === k.key);
    const den = factors.find((g) => g instanceof Pow && g.exp instanceof Rational && g.exp.p === -1n && g.base.key === factorial(k).key);
    if (num && den && factors.length === 2) return exp(num.base);
  }
  // two terms that cancel after a shift, also after a partial fraction decomposition (SymPy telescopic)
  if (!isOo(b)) {
    const t = telescopicAdd(f, k, a, b) ?? (isRationalIn(f, k) ? telescopicAdd(apart(f, k), k, a, b) : undefined);
    if (t !== undefined) return t;
  }
  // Gosper antidifferences for a binomial term, or an index times a geometric term.
  if (!isOo(b) && !isNegOo(a)) {
    const geometric = dep.find(t => t instanceof Pow && t.exp.equals(k) && !t.base.has(k));
    const weighted = dep.length === 2 && dep.some(t => t.equals(k)) && geometric instanceof Pow;
    if (weighted || binomialTerm && [...freeSymbols(f)].every(v => v.equals(k))) {
      const result = summationHooks.gosperSum?.(f, [k, a, b]) ?? NoMatch;
      if (!isNoMatch(result)) {
        if (!weighted) return result;
        const base = geometric.base;
        const [num] = fraction(together(add(base, -1)));
        let condition = Eq(base, 1);
        for (const variable of [...freeSymbols(base)].filter(v => v instanceof Sym).sort((x, y) => x.name.localeCompare(y.name))) {
          const root = linearRoot(num, variable);
          if (root !== undefined) { condition = Eq(variable, factor(root)); break; }
        }
        const atOne = mul(c, S.Half, add(a, b), add(b, mul(-1, a), 1));
        return piecewise([base instanceof Sym ? expand(atOne) : atOne, condition], [result, true]);
      }
    }
  }
  // a hypergeometric term: the hypergeometric series, expanded (SymPy eval_sum_hyper)
  if (isOo(b) && !isNegOo(a) && !isOo(a) && f instanceof Pow && !f.exp.has(k)) {
    const base = polyCoefficients(expand(f.base), k);
    const slope = base?.get(1);
    if (base && [...base.keys()].every((power) => power <= 1) && slope !== undefined && isPositive(slope) === true) {
      const s = mul(-1, f.exp);
      const q = add(mul(base.get(0) ?? S.Zero, pow(slope, -1)), a);
      const negativeQ = mul(-1, q);
      const noPole = fact(negativeQ, 'integer') === false ? S.true : not(contains(Naturals0, negativeQ));
      const condition = and(noPole, Gt(re(s), 1));
      return piecewise([mul(pow(slope, mul(-1, s)), zeta(s, q)), condition], [Sum(f, [k, a, b]), true]);
    }
  }
  if (!isInt(diff_) && !isNegOo(a)) {
    // term by term (SymPy eval_sum_symbolic of an Add)
    if (ef instanceof Add) {
      const parts = ef.args.map((term) => sumOne(term, k, a, b));
      if (parts.every((x) => x !== undefined)) return add(...parts);
    }
    const h = evalSumHyper(f, k, a, b);
    if (h !== undefined) return h;
  }
  // no closed form: a range with a known length is summed term by term (SymPy eval_sum_direct)
  return isInt(diff_) ? directSum(f, k, a, diff_.p) : undefined;
}

/** The expression contains KroneckerDelta(i, j) with k in i - j. */
const hasDelta = (e: Expr, k: Sym): boolean => (e instanceof Fn && e.name === 'KroneckerDelta' && e.has(k)) || e.args.some((a) => hasDelta(a, k));

/** The value of k where the linear expression d vanishes, or undefined when d is not linear in k. */
function linearRoot(d: Expr, k: Sym): Expr | undefined {
  const pc = polyCoefficients(d, k);
  if (pc === undefined || Math.max(...pc.keys()) !== 1) return undefined;
  return mul(-1, pc.get(0) ?? S.Zero, pow(getOrThrow(pc, 1), -1));
}

/**
 * SymPy deltasummation: the sum of f*KroneckerDelta(i, j), with i - j
 * linear in k, is f at the root k0 when a <= k0 <= b (a Piecewise of that
 * condition); sums are taken term by term. Undefined for other deltas.
 */
function deltaSum(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  const additive = f instanceof Mul && f.args.find(t => t instanceof Add && hasDelta(t, k));
  const g = additive instanceof Add ? add(...additive.args.map(t => mul(...f.args.map(v => v === additive ? t : v)))) : f;
  if (g instanceof Add) {
    const parts = g.args.map((t) => {
      if (hasDelta(t, k)) return deltaSum(t, k, a, b);
      const result = sumOne(t, k, a, b);
      if (result !== undefined) return result;
      // Pull a delta in another index outside this sum so its own limit can contract it.
      const [constant, dependent] = asIndependent(t, [k], { asAdd: false });
      return some(constant, v => v instanceof Fn && v.name === 'KroneckerDelta')
        ? mul(constant, Sum(dependent, [k, a, b])) : Sum(t, [k, a, b]);
    });
    return parts.every((x) => x !== undefined) ? add(...parts) : undefined;
  }
  const factors = g instanceof Mul ? g.args : [g];
  const delta = factors.find((t): t is Fn => t instanceof Fn && t.name === 'KroneckerDelta' && t.has(k));
  if (delta === undefined) return undefined;
  const value = linearRoot(add(at(delta.args, 0), mul(-1, at(delta.args, 1))), k);
  if (value === undefined) return undefined;
  const rest = mul(...factors.filter((t) => t !== delta));
  const range = delta.args[2];
  if (range && isNonNegative(add(at(range.args, 0), mul(-1, a))) === true && isNonNegative(add(b, mul(-1, at(range.args, 1)))) === true) {
    return xreplace(rest, [[k, value]]);
  }
  // (SymPy's value < oo for an infinite range holds: the value is finite)
  const cond = isOo(b) ? Le(a, value) : and(Le(a, value), Le(value, b));
  return piecewise([powsimp(xreplace(rest, [[k, value]])), cond], [S.Zero, true]);
}

/**
 * The sum of c*Piecewise((g, cond), (0, True)) where cond is a conjunction
 * of relations linear in k: the sum of c*g over the part of [a, b] where
 * cond holds; undefined for other terms.
 */
function piecewiseRange(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  const factors = f instanceof Mul ? f.args : [f];
  const pw = factors.find((t): t is Piecewise => t instanceof Piecewise);
  const zero = (e: Expr): boolean => e instanceof Rational && e.isZero;
  if (pw?.args.length !== 4 || at(pw.args, 3) !== S.true || !zero(at(pw.args, 2))) return undefined;
  const cond = at(pw.args, 1);
  const rels = cond instanceof BoolOp && cond.op === 'And' ? cond.args : [cond];
  let lo = a;
  let hi = b;
  for (const r of rels) {
    if (!(r instanceof Rel) || r.op === 'Eq' || r.op === 'Ne') return undefined;
    const d = add(r.lhs, mul(-1, r.rhs));
    const pc = polyCoefficients(d, k);
    if (pc === undefined || Math.max(...pc.keys()) !== 1) return undefined;
    const c1 = getOrThrow(pc, 1);
    if (!(c1 instanceof Rational)) return undefined;
    const root = mul(-1, pc.get(0) ?? S.Zero, pow(c1, -1));
    // k < oo and k > -oo hold for a finite k
    if (root instanceof Special) continue;
    // (a bound with parameters may give an empty range, which SymPy's formulas would not see)
    if (freeSymbols(root).size > 0) return undefined;
    // k < root (or k > root for a negative coefficient), as a bound on the integer k
    const upper = (r.op === 'Lt' || r.op === 'Le') === c1.isPositive;
    const strict = r.op === 'Lt' || r.op === 'Gt';
    if (upper) {
      const bound = strict ? add(fn('ceiling', [root]), -1) : fn('floor', [root]);
      hi = isOo(hi) ? bound : fn('Min', [hi, bound]);
    } else {
      const bound = strict ? add(fn('floor', [root]), 1) : fn('ceiling', [root]);
      lo = fn('Max', [lo, bound]);
    }
  }
  const rest = mul(...factors.filter((t) => t !== pw), at(pw.args, 0));
  const len = add(hi, mul(-1, lo));
  // an empty range
  if (len instanceof Rational && len.isNegative) return S.Zero;
  // (a sum that is not evaluated keeps its Piecewise, as in SymPy)
  return sumOne(rest, k, lo, hi);
}

/** The term ratio f(k + 1)/f(k) as a rational function of k (SymPy hypersimp), or undefined. */
function termRatio(f: Expr, k: Sym): Expr | undefined {
  // b**(k + 1) is written b*b**k first, so that the powers of b cancel
  const shifted = expandFull(xreplace(f, [[k, add(k, 1)]]), { mul: false, multinomial: false, power_base: false, log: false });
  const r = factor(cancel(powsimp(combsimp(mul(shifted, pow(f, -1))))));
  const [n, d] = fraction(r);
  return polyCoefficients(expand(n), k) !== undefined && polyCoefficients(expand(d), k) !== undefined ? r : undefined;
}

/** The factors of a product that contain k and the product of the others (SymPy as_coeff_mul(k)). */
function splitFactors(e: Expr, k: Sym): [Expr, Expr[]] {
  const fs = e instanceof Mul ? e.args : [e];
  return [mul(...fs.filter((t) => !t.has(k))), fs.filter((t) => t.has(k))];
}

/**
 * SymPy _eval_sum_hyper: the sum of f from a to oo as [value, condition
 * of convergence], f a hypergeometric term whose term ratio has linear
 * factors; undefined otherwise.
 */
function sumHyperFrom(fIn: Expr, k: Sym, a: Expr, zeros = 0): [Expr, Expr] | undefined {
  if (!(a instanceof Rational && a.isZero)) return sumHyperFrom(xreplace(fIn, [[k, add(k, a)]]), k, S.Zero);
  const f = fIn;
  const f0 = xreplace(f, [[k, S.Zero]]);
  // a pole of the term at the start (SymPy leaves such sums to the other methods)
  if (hasNonFinite(f0)) return undefined;
  if (f0 instanceof Rational && f0.isZero) {
    const d = new Dummy('i', { integer: true, positive: true });
    // (SymPy simplifies the term at a positive integer; the automatic evaluation suffices for the terms met here)
    const z = xreplace(f, [[k, d]]);
    if (z instanceof Rational && z.isZero) {
      // A trigonometric factor vanishing at all integer samples has no term ratio there.
      if (some(f, (t) => t instanceof Fn && ['sin', 'cos'].includes(t.name) && t.has(k))) return undefined;
      return [S.Zero, S.true];
    }
    // terms that vanish for every k from some point on (binomial(x, -k - 1)) would be skipped forever
    if (zeros >= 6) return undefined;
    return sumHyperFrom(xreplace(f, [[k, add(k, 1)]]), k, S.Zero, zeros + 1);
  }
  const hs = termRatio(f, k) ?? hypersimp(f, k);
  if (hs === undefined) return undefined;
  const [numer, denom] = fraction(hs);
  const ab: Expr[] = [];
  const params: Expr[][] = [[], []];
  for (const [i, part] of [numer, denom].entries()) {
    const [c, deps] = splitFactors(part, k);
    let coeff = c;
    for (const fac0 of deps) {
      let fac = fac0;
      let m = 1;
      // (the factors of a polynomial have positive integer powers)
      if (fac instanceof Pow) {
        m = Number(asRational(fac.exp, 'power of a factor').p);
        fac = fac.base;
      }
      const pc = polyCoefficients(expand(fac), k);
      if (pc === undefined || Math.max(...pc.keys()) !== 1) return undefined;
      const lead = getOrThrow(pc, 1);
      coeff = mul(coeff, pow(lead, m));
      for (let j = 0; j < m; j++) at(params, i).push(mul(pc.get(0) ?? S.Zero, pow(lead, -1)));
    }
    ab.push(coeff);
  }
  // 1 among the numerator parameters accounts for the implicit k! of the hypergeometric series
  const h = cast(hyper([...at(params, 0), 1], at(params, 1), mul(at(ab, 0), pow(at(ab, 1), -1))), Hyper);
  // series beyond 2F1 with symbolic parameters are not expanded here (hyperexpand takes seconds and seldom closes)
  if (h.ap.length > 2 && h.freeSymbols().size > 0) return undefined;
  const value = mul(xreplace(combsimp(f), [[k, S.Zero]]), hyperexpand(h));
  // an expansion at a branch point that does not reduce (SymPy divides by 105 - 105*exp_polar(0) = 0)
  if (hasNonFinite(value) || value.has(expPolarZero)) return undefined;
  return [value, h.convergenceStatement];
}

/** exp_polar(0), left by expansions at a branch point. */
const expPolarZero = /* @__PURE__ */ fn('exp_polar', [S.Zero]);

/** The expression contains oo, -oo, zoo or nan. */
const hasNonFinite = (e: Expr): boolean => e instanceof Special || e.args.some(hasNonFinite);

/** SymPy eval_sum_hyper: sum_{k=a}^{b} f of a hypergeometric term f over an infinite or symbolic range, or undefined. */
function evalSumHyper(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  const oldSum = Sum(f, [k, a, b]);
  if (!isOo(b)) {
    const tails: [Expr, Expr][] = [];
    for (const start of [a, add(b, 1)]) {
      const tail = sumHyperFrom(f, k, start);
      if (tail === undefined) return undefined;
      tails.push(tail);
    }
    const [res1, res2] = pair(tails);
    const cond = and(res1[1], res2[1]);
    if (cond === S.false) return undefined;
    return piecewise([add(res1[0], mul(-1, res2[0])), cond], [oldSum, true]);
  }
  const res = sumHyperFrom(f, k, a);
  if (res === undefined) return undefined;
  const [r, c] = res;
  if (c === S.false) {
    // a divergent series of terms of one sign
    if (freeSymbols(r).size !== 0) return undefined;
    const t = xreplace(f, [[k, add(new Dummy('i', { integer: true, positive: true }), a)]]);
    if (isPositive(t) === true || isZeroQ(t) === true) return S.Infinity;
    return isNegative(t) === true ? S.NegativeInfinity : undefined;
  }
  return piecewise([r, c], [oldSum, true]);
}

/** A rational function of k that is not a polynomial. */
function isRationalIn(f: Expr, k: Sym): boolean {
  const [n, d] = fraction(f);
  return d.has(k) && polyCoefficients(expand(n), k) !== undefined && polyCoefficients(expand(d), k) !== undefined;
}

/**
 * sum_{k=a}^{b} (L + R) for R = -L(k + s) with an integer shift s (SymPy telescopic): the first
 * |s| terms of L (of R) and the last ones of R (of L) remain.
 */
function telescopicAdd(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if (!(f instanceof Add && f.args.length === 2)) return undefined;
  const result = telescopic(first(f.args), at(f.args, 1), [k, a, b]);
  return isNoMatch(result) ? undefined : result;
}

/**
 * Sum two terms whose translates cancel, or return NoMatch.
 *
 * @param left - The first term of the telescoping pair.
 * @param right - The second term of the telescoping pair.
 * @param limits - The index and its inclusive lower and upper bounds.
 * @returns The matching result, or `NoMatch` when the required form is absent.
 * @see SymPy `sympy.concrete.summations.telescopic`
 */
export function telescopic(left: ExprLike, right: ExprLike, limits: readonly [Sym, ExprLike, ExprLike]): Expr | NoMatchResult {
  const L = sympify(left), R = sympify(right), [k] = limits;
  if (L instanceof Add || R instanceof Add) return NoMatch;
  const shift = new Wild('shift', { exclude: [k] });
  const shifted = xreplace(L, [[k, add(k, shift)]]);
  const matched = match(mul(-1, R), shifted)?.get(shift);
  const valid = (s: Expr): s is Rational => isInt(s) && !s.isZero && isZeroExpanded(fraction(together(add(xreplace(L, [[k, add(k, s)]]), R)))[0]);
  let distance = matched;
  if (distance === undefined || !valid(distance)) {
    const numerator = expand(fraction(together(add(shifted, R)))[0]);
    const candidates = polyCoefficients(numerator, shift) === undefined ? [] : roots(numerator, shift).filter(valid);
    const distinct = [...new Map(candidates.map(s => [s.key, s])).values()];
    if (distinct.length !== 1) return NoMatch;
    distance = first(distinct);
  }
  return isNegative(distance) === true ? telescopicDirect(R, L, mul(-1, distance), limits) : telescopicDirect(L, R, distance, limits);
}

/**
 * Boundary terms left after cancelling a telescoping sum with a positive integer shift.
 *
 * @param L - The first term of the telescoping pair.
 * @param R - The second term of the telescoping pair.
 * @param nIn - The positive index shift between the two terms.
 * @param limits - The index and its inclusive lower and upper bounds.
 * @returns The sum of the surviving boundary terms.
 * @throws RangeError when the shift is not a nonnegative integer.
 * @see SymPy `sympy.concrete.summations.telescopic_direct`
 * @example
 * ```ts
 * import { ex, symbols, telescopicDirect } from '@symjs/symjs';
 *
 * telescopicDirect(ex`1/k`, ex`-1/(k + 1)`, 1, [symbols('k')[0], 1, 3]); // => 3/4
 * ```
 */
export function telescopicDirect(L: ExprLike, R: ExprLike, nIn: ExprLike, limits: readonly [Sym, ExprLike, ExprLike]): Expr {
  const shift = sympify(nIn);
  if (!(shift instanceof Rational && shift.isInteger) || shift.isNegative || shift.p > BigInt(Number.MAX_SAFE_INTEGER)) throw new RangeError('telescopicDirect requires a nonnegative integer shift');
  const n = shift.toNumber();
  const [k, a, b] = limits;
  const terms: Expr[] = [];
  for (let m = 0; m < n; m++) terms.push(xreplace(sympify(L), [[k, add(a, m)]]), xreplace(sympify(R), [[k, add(b, -m)]]));
  return add(...terms);
}

const isZeroExpanded = (e: Expr): boolean => {
  const x = expand(e);
  return x instanceof Rational && x.isZero;
};

/** sum_{i=0}^{len} f(a + i). */
function directSum(f: Expr, k: Sym, a: Expr, len: bigint): Expr {
  const terms: Expr[] = [];
  for (let i = 0n; i <= len; i++) {
    const term = xreplace(f, [[k, add(a, Rational.of(i))]]);
    terms.push(mapBottomUp(term, (node) => node instanceof Concrete ? doitConcrete(node) : node));
  }
  return add(...terms);
}

/**
 * Port of SymPy eval_sum_residue: sums of rational functions (optionally
 * times (-1)**k) over infinite ranges via residues of f*cot(pi*z) (or
 * f*csc(pi*z)). Repeated poles use the Laurent coefficient of the kernel.
 */
function evalSumResidueImpl(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if ([...freeSymbols(f)].some((s) => s.key !== k.key)) return undefined;
  // the callers pass b = oo (a sum from -oo to b is mirrored first)
  if (!(isInt(a) || isNegOo(a))) return undefined;
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
  // Poles of the rational function, including their multiplicities.
  const repeated = new Set<string>();
  const poles = (): [Rational[], Expr[]] | undefined => {
    const D = toExpr(pd);
    let rs: Expr[];
    try {
      rs = roots(D, k);
    } catch {
      return undefined;
    }
    const unique = new Map<string, Expr>();
    for (const r of rs) {
      if (unique.has(r.key)) repeated.add(r.key);
      unique.set(r.key, r);
    }
    const uniqueRoots = [...unique.values()];
    return [uniqueRoots.filter(isInt), uniqueRoots.filter((r) => !isInt(r))];
  };
  const residues = (rs: Expr[]): Expr => {
    const N = toExpr(pn);
    const dPoly = (p: Map<number, Expr>) => new Map([...p].filter(([i]) => i > 0).map(([i, c]): [number, Expr] => [i - 1, mul(i, c)]));
    const dN = toExpr(dPoly(pn));
    const dD = toExpr(dPoly(pd));
    const d2D = toExpr(dPoly(dPoly(pd)));
    return add(
      ...rs.map((r) => {
        if (repeated.has(r.key)) {
          // The contour variable is complex even when the discrete index is an integer.
          const z = new Dummy('z');
          const kernel = alternating ? sin(mul(S.Pi, z)) : tan(mul(S.Pi, z));
          const rational = xreplace(mul(N, pow(toExpr(pd), -1)), [[k, z]]);
          return residue(mul(rational, pow(kernel, -1)), z, r);
        }
        const at = (e: Expr) => xreplace(e, [[k, r]]);
        const piR = mul(S.Pi, r);
        if (isInt(r)) {
          // f = g/(z - r) has a double pole in f*cot(pi*z) (or f*csc(pi*z)) at the integer r:
          // the residue is g'(r)/pi (times (-1)**r), g'(r) = (N'(r)*D'(r) - N(r)*D''(r)/2)/D'(r)**2
          const g1 = mul(add(mul(at(dN), at(dD)), mul(Rational.of(-1, 2), at(N), at(d2D))), pow(at(dD), -2));
          const res = mul(g1, pow(S.Pi, -1));
          return alternating ? mul(res, pow(-1, r)) : res;
        }
        const res = mul(at(N), pow(at(dD), -1));
        return mul(res, pow(alternating ? sin(piR) : tan(piR), -1));
      }),
    );
  };
  if (!isInt(a)) {
    // a = -oo, b = oo: the sum over all integers
    const ps = poles();
    if (!ps || ps[0].length) return undefined;
    return mul(-1, S.Pi, residues(ps[1]));
  }
  if (!isEven()) {
    const n = deg(pd);
    const lead = getOrThrow(pd, n);
    const sub = pd.get(n - 1) ?? S.Zero;
    const shift = mul(-1, sub, pow(lead, -1), Rational.of(1, n));
    if (!isInt(shift) || shift.isZero) return undefined;
    const sh = (p: Map<number, Expr>) => expand(xreplace(toExpr(p), [[k, add(k, shift)]]));
    const nn = sh(pn);
    const dd = sh(pd);
    pn = defined(polyCoefficients(nn, k), 'shifted numerator coefficients');
    pd = defined(polyCoefficients(dd, k), 'shifted denominator coefficients');
    if (!isEven()) return undefined;
    const g = alternating ? mul(pow(-1, k), pow(-1, shift), nn, pow(dd, -1)) : mul(nn, pow(dd, -1));
    return evalSumResidueImpl(g, k, add(a, mul(-1, shift)), b);
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
  if (!f.has(k)) {
    if (f instanceof Mul && !f.isCommutative) {
      const count = add(diff_, 1);
      return mul(pow(mul(...f.args.filter((t) => t.isCommutative)), count), pow(mul(...f.args.filter((t) => !t.isCommutative)), count));
    }
    return evalProduct(f, k, a, b);
  }
  // Karr convention for reversed limits (a range with a known length always has a product)
  if (isInt(diff_) && diff_.p < -1n) return pow(defined(productOne(f, k, add(b, 1), add(a, -1)), 'product over a finite range'), -1);
  // explicit evaluation for short finite ranges (SymPy: fewer than 100 factors)
  if (isInt(diff_) && diff_.p < 100n) return directProduct(f, k, a, diff_.p);
  // no closed form: a range with a known length is multiplied out (SymPy _eval_product_direct)
  return evalProduct(f, k, a, b) ?? (isInt(diff_) ? directProduct(f, k, a, diff_.p) : undefined);
}

/** prod_{i=0}^{len} f(a + i). */
function directProduct(f: Expr, k: Sym, a: Expr, len: bigint): Expr {
  const terms: Expr[] = [];
  for (let i = 0n; i <= len; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
  return mul(...terms);
}

/** Port of SymPy Product._eval_product for the indefinite cases. */
function evalProduct(term: Expr, k: Sym, a: Expr, n: Expr): Expr | undefined {
  const count = add(n, mul(-1, a), 1);
  if (!term.has(k)) return term instanceof Rational && term.isOne ? S.One : pow(term, count);
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
    return mul(pow(getOrThrow(pc, deg), count), A);
  }
  if (term instanceof Add) {
    const [num, den] = asNumerDenom(term);
    if (den.has(k)) {
      const numerator = evalProduct(num, k, a, n);
      const denominator = evalProduct(den, k, a, n);
      if (numerator !== undefined && denominator !== undefined) return mul(numerator, pow(denominator, -1));
    }
  }
  if (term instanceof Mul) {
    // the factors with a product, times the Product of the others (SymPy: of several factors with k
    // at least one must have a product; a single one stays a Product times the constant factors)
    const without = term.args.filter((t) => !t.has(k));
    const withK = term.args.filter((t) => t.has(k));
    const done: Expr[] = [];
    const left: Expr[] = [];
    for (const t of withK) {
      const p = evalProduct(t, k, a, n);
      if (p === undefined) left.push(t);
      else done.push(p);
    }
    if (!done.length && withK.length > 1) return undefined;
    const rest = left.length ? Product(mul(...left), [k, a, n]) : S.One;
    return mul(pow(mul(...without), count), ...done, rest);
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

/**
 * Computes the sum of `f` over each `[k, a, b]` of `limits`, from the
 * innermost (first) to the outermost. A sum that cannot be computed is
 * returned unevaluated as a `Sum`.
 *
 * @param f - The summand.
 * @param limits - The index and its lower and upper bounds, which may be
 *   infinite.
 * @returns The sum.
 * @see SymPy `sympy.concrete.summations.summation`
 * @example
 * ```ts
 * import { ex, factorial, oo, summation, symbols } from '@symjs/symjs';
 *
 * const [i, n, m] = symbols('i n m', { integer: true });
 * const [x] = symbols('x');
 * summation(ex`2*${i} - 1`, [i, 1, n]); // => n**2
 * summation(ex`1/2**${i}`, [i, 0, oo]); // => 2
 * summation(i, [i, 0, n], [n, 0, m]); // => m**3/6 + m**2/2 + m/3
 * summation(x.pow(n).div(factorial(n)), [n, 0, oo]); // => exp(x)
 * ```
 */
export function summation(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  if (limits.length === 0) throw new RangeError('summation requires a definite limit');
  let e = sympify(f);
  if (new Concrete('Sum', [e, ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]).hasEmptySequence === true) return S.Zero;
  for (const [i, [k, a0, b0]] of limits.entries()) {
    const [a, b] = [sympify(a0), sympify(b0)];
    // the summation variable has the signs of its limits (SymPy _dummy_with_inherited_properties_concrete)
    const d = inheritedDummy(k, a, b);
    // (substituted with evaluation: a condition such as d >= 0 is decided by the inherited sign)
    const withDummy = d === undefined ? e : subs(e, [[k, d]]);
    const r = d === undefined ? sumOne(e, k, a, b) : sumOne(withDummy, d, a, b);
    // SymPy returns the sum of the function as evaluated with those assumptions; here that form is taken when
    // the assumptions decide every condition, and the given function is kept otherwise
    if (r === undefined) {
      const decided = d !== undefined && !some(withDummy, (t) => t instanceof Piecewise);
      return Sum(decided ? xreplace(withDummy, [[d, k]]) : e, [k, a, b], ...limits.slice(i + 1));
    }
    e = d === undefined ? r : xreplace(r, [[d, k]]);
  }
  return e;
}

/**
 * A dummy for the summation variable with the signs that both limits have
 * (oo counts as positive, -oo as negative) and integer when both are
 * integers; undefined when it would add nothing.
 */
function inheritedDummy(k: Sym, a: Expr, b: Expr): Dummy | undefined {
  const have = k.assumptions;
  const add_: Record<string, boolean> = {};
  const both = (test: (e: Expr) => boolean | undefined, inf: Expr): boolean => [a, b].every((e) => e === inf || test(e) === true);
  if (!have.positive && both(isPositive, S.Infinity)) add_['positive'] = true;
  else if (!have.nonnegative && both(isNonNegative, S.Infinity)) add_['nonnegative'] = true;
  if (!have.negative && both(isNegative, S.NegativeInfinity)) add_['negative'] = true;
  else if (!have.nonpositive && both((e) => isNonNegative(mul(-1, e)), S.NegativeInfinity)) add_['nonpositive'] = true;
  if (!have.integer && [a, b].every((e) => isIntegerQ(e) === true)) add_['integer'] = true;
  if (Object.keys(add_).length === 0) return undefined;
  return new Dummy('d', { ...have, ...add_ });
}

/**
 * Computes the product of `f` over each `[k, a, b]` of `limits`, from the
 * innermost (first) to the outermost. A product that cannot be computed is
 * returned unevaluated as a `Product`.
 *
 * @param f - The factor.
 * @param limits - The index and its lower and upper bounds.
 * @returns The product.
 * @see SymPy `sympy.concrete.products.product`
 * @example
 * ```ts
 * import { product, symbols } from '@symjs/symjs';
 *
 * const [i, n, m, k] = symbols('i n m k', { integer: true });
 * product(i, [i, 1, k]); // => factorial(k)
 * product(m, [i, 1, k]); // => m**k
 * product(i, [i, 1, k], [k, 1, n]); // => Product(factorial(k), (k, 1, n))
 * ```
 */
export function product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  // SymPy product() is Product.doit(deep=False), which powsimps the result (2**(n*(n + 1)/2))
  // (a number times a sum is distributed, as SymPy's Mul does: 2**(-a**2/2 + a/2 + n**2/2 + n/2))
  const distribute = (e: Expr): Expr => (e instanceof Mul && e.args.length === 2 && isNum(at(e.args, 0)) && at(e.args, 1) instanceof Add ? expand(e) : e);
  return mapBottomUp(powsimp(productDeep(sympify(f), limits)), distribute);
}

/** Product(...).doit(): the product without the final powsimp. */
function productDeep(f: Expr, limits: readonly [Sym, ExprLike, ExprLike][]): Expr {
  let e = f;
  for (const [k, a, b] of limits) {
    const r = productOne(e, k, sympify(a), sympify(b));
    if (r === undefined || r.key === S.NaN.key) return Product(e, [k, a, b]);
    e = r;
  }
  return e;
}

/**
 * Evaluates a symbolic sum or product over its limits.
 *
 * @see SymPy `sympy.concrete.summations.Sum.doit`
 * @see SymPy `sympy.concrete.products.Product.doit`
 */
export function doitConcrete(c: Concrete): Expr {
  if (c.hasEmptySequence === true) return c.kind2 === 'Sum' ? S.Zero : S.One;
  const lims = c.limits.map(([k, a, b]): [Sym, Expr, Expr] => [cast(k, Sym, 'limit variable'), a, b]);
  return c.kind2 === 'Sum' ? summation(c.function, ...lims) : productDeep(c.function, lims);
}

/**
 * Reverse the order of the given limits (by index or variable), SymPy reverse_order.
 *
 * @param c - The unevaluated sum or product.
 * @param which - The indices or variables of the limits to reverse.
 * @returns The equivalent sum or product with the selected bounds reversed.
 * @see SymPy `sympy.concrete.summations.Sum.reverse_order`
 * @example
 * ```ts
 * import { Concrete, ex, reverseOrder } from '@symjs/symjs';
 *
 * reverseOrder(new Concrete('Sum', [ex`k`, ex`k`, ex`1`, ex`3`]), 0); // => Sum(-k, (k, 4, 0))
 * ```
 */
export function reverseOrder(c: Concrete, ...which: (number | Sym)[]): Expr {
  // as in SymPy, each selected limit is reversed once however often it is named
  const sel = new Set(which.map((w) => (typeof w === 'number' ? w : c.limits.findIndex(([k]) => k.key === w.key))));
  const lims = c.limits.map(([k, a, b], i): [Expr, Expr, Expr] => (sel.has(i) ? [k, add(b, 1), add(a, -1)] : [k, a, b]));
  const odd = c.limits.filter((_, i) => sel.has(i)).length % 2 === 1;
  const f = !odd ? c.function : c.kind2 === 'Sum' ? mul(-1, c.function) : pow(c.function, -1);
  return new Concrete(c.kind2, [f, ...lims.flat()]);
}


const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isFiniteBound = (e: Expr) => !(e instanceof Special);

/** Limit of f(k) as k -> oo, or undefined. */
function limOo(f: Expr, k: Sym): Expr | undefined {
  // an undetermined limit is an unevaluated Limit, or NotImplementedError (SymPy limit_seq catches it)
  let l: Expr;
  try {
    l = impl.limit(f, k, S.Infinity);
  } catch (err) {
    if (err instanceof NotImplementedError) return undefined;
    throw err;
  }
  return l instanceof Limit ? undefined : l;
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

/**
 * Tests a sum for convergence using the divergence, p-series, ratio, root and alternating series tests.
 * For an infinite product, it checks whether the factors approach one and tests the sum of their
 * logarithms for convergence.
 *
 * @see SymPy `sympy.concrete.summations.Sum.is_convergent`
 * @see SymPy `sympy.concrete.products.Product.is_convergent`
 */
export function sumIsConvergent(c: Concrete): boolean | undefined {
  const [kE, a, b] = first(c.limits);
  const k0 = cast(kE, Sym, 'limit variable');
  if (freeSymbols(c.function).size > 1) throw new NotImplementedError('convergence checking for more than one symbol containing series is not handled');
  if (isFiniteBound(a) && isFiniteBound(b)) return true;
  // as in SymPy, the summation variable is a positive integer
  const k = new Sym(k0.name, { integer: true, positive: true });
  const f0 = c.function;
  if (isNegOo(a)) {
    // k -> -k turns the range into one ending at oo
    const g = xreplace(f0, [[k0, mul(-1, k0)]]);
    if (!isOo(b)) return sumIsConvergent(new Concrete(c.kind2, [g, k0, mul(-1, b), S.Infinity]));
    const left = sumIsConvergent(new Concrete(c.kind2, [g, k0, S.Zero, S.Infinity]));
    const right = sumIsConvergent(new Concrete(c.kind2, [f0, k0, S.Zero, S.Infinity]));
    return left === false || right === false ? false : left === true && right === true ? true : undefined;
  }
  // Karr convention: Sum(f, (k, a, -oo)) = -Sum(f, (k, -oo, a - 1)) and Sum(f, (k, oo, b)) = -Sum(f, (k, b + 1, oo))
  if (isNegOo(b)) return sumIsConvergent(new Concrete(c.kind2, [f0, k0, b, add(a, -1)]));
  if (isOo(a) && !isOo(b)) return sumIsConvergent(new Concrete(c.kind2, [f0, k0, add(b, 1), S.Infinity]));
  // a complex infinity as a limit (SymPy ValueError); SymPy gives True for a nan limit, which is no sum
  if (b instanceof Special && b.name === 'zoo') throw new RangeError('Non-real intervals are not supported');
  if (!isOo(b)) return undefined;
  // other symbols (Sum(x**k, ...)): the answer depends on them (SymPy raises NotImplementedError)
  if ([...freeSymbols(f0)].some((v) => v.key !== k0.key)) throw new NotImplementedError('convergence checking for more than one symbol containing series is not handled');
  const f = xreplace(f0, [[k0, k]]);
  // a product converges with the sum of the logarithms of its factors (SymPy), which needs factors -> 1
  if (c.kind2 === 'Product') {
    const l = limOo(f, k);
    if (l !== undefined && !(l instanceof Rational && l.isOne)) return false;
    return sumIsConvergent(new Concrete('Sum', [log(f0), ...c.args.slice(1)]));
  }
  // divergence test: the terms (or their moduli) do not tend to 0
  const l = limOo(f, k);
  if (l !== undefined && !(l instanceof Rational && l.isZero)) return false;
  const la = limOo(impl.abs(f), k);
  if (la !== undefined && !(la instanceof Rational && la.isZero)) return false;
  // p-series: f ~ C*k**(-p) for rational functions
  const r = pSeriesOrder(f, k);
  if (r !== undefined) return r > 1;
  // limit comparison with a p-series: f ~ c*k**(-p) as k -> oo with a constant c != 0 (for a
  // complex c the real or the imaginary part compares, and |f| ~ |c|*k**(-p))
  try {
    const t = new Sym('_t', { positive: true });
    const [c0, e0] = defined(impl.leadterm?.(xreplace(f, [[k, pow(t, -1)]]), t), 'impl.leadterm');
    // f ~ C*k**(-p)*log(k)**(-q) (log(t) = -log(k) in the coefficient of t**p): it converges for p > 1,
    // or p = 1 and q > 1 (SymPy's comparison with 1/(n**p*log(n)**q))
    const logT = log(t);
    let q = 0;
    const rest: Expr[] = [];
    for (const g of c0 instanceof Mul ? c0.args : [c0]) {
      if (g.key === logT.key) q -= 1;
      else if (g instanceof Pow && g.base.key === logT.key && g.exp instanceof Rational) q -= g.exp.value;
      else rest.push(g);
    }
    const C = mul(...rest);
    if (e0 instanceof Rational && C.freeSymbols().size === 0 && !(C instanceof Rational && C.isZero)) return e0.value > 1 || (e0.value === 1 && q > 1);
  } catch {
    // no asymptotic expansion
  }
  // ratio test
  // SymPy simplifies the ratio with combsimp(powsimp(...)) first
  const ratio = limOo(impl.abs(combsimp(powsimp(mul(xreplace(f, [[k, add(k, 1)]]), pow(f, -1))))), k);
  // (an accumulation interval is not a number: SymPy requires lim_ratio.is_number)
  if (ratio?.freeSymbols().size === 0 && !(ratio instanceof Special) && !defined(impl.accumBounds, 'accumBounds').is(ratio)) {
    const v = ratio.toNumber();
    if (v < 1) return true;
    if (v > 1) return false;
  }
  if (ratio instanceof Special && ratio.name === 'oo') return false;
  // root test: lim |f|**(1/k) < 1 (a limit above 1 makes the terms grow, which the divergence test decides)
  const root = limOo(pow(impl.abs(f), pow(k, -1)), k);
  if (root?.freeSymbols().size === 0 && !(root instanceof Special) && !defined(impl.accumBounds, 'accumBounds').is(root) && root.toNumber() < 1) return true;
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

/**
 * [approximation, error estimate] by the
 * Euler-Maclaurin formula with m explicit leading terms and n correction terms.
 *
 * @param sum - The unevaluated sum to approximate.
 * @param mIn - The number of leading terms to sum explicitly.
 * @param n - The number of correction terms.
 * @param eps - The requested error threshold.
 * @returns The approximation and estimated absolute error.
 * @throws TypeError when the expression is not a sum with one limit.
 * @remarks SymPy returns the tuple `(6, 0)` for the example below.
 * @see SymPy `sympy.concrete.summations.Sum.euler_maclaurin`
 * @example
 * ```ts
 * import { Concrete, eulerMaclaurin, ex } from '@symjs/symjs';
 *
 * eulerMaclaurin(new Concrete('Sum', [ex`k`, ex`k`, ex`1`, ex`3`])); // => [6, 0]
 * ```
 */
export function eulerMaclaurin(sum: Concrete, mIn = 0, n = 0, eps = 0): [Expr, Expr] {
  let m = mIn;
  if (!(sum instanceof Concrete) || sum.limits.length !== 1) throw new TypeError('euler_maclaurin: a Sum with one limit expected');
  let f = sum.function;
  const [i0, a0, b0] = first(sum.limits);
  const i = cast(i0, Sym, 'limit variable');
  let a = a0;
  let b = b0;
  const bmaNum = add(b, mul(-1, a));
  if (bmaNum instanceof Rational && bmaNum.isNegative) {
    if (add(a, mul(-1, b)).key === S.One.key) return [S.Zero, S.Zero];
    [a, b] = [add(b, 1), add(a, -1)];
    f = mul(-1, f);
  }
  const at = (e: Expr, p: Expr) => xreplace(e, [[i, p]]);
  let s: Expr = S.Zero;
  if (m) {
    if (a instanceof Rational && b instanceof Rational) m = Math.min(m, Number((b).p - (a).p) + 1);
    const checkTerms = eps > 0 && polyCoefficients(expand(f), i) === undefined;
    for (let k = 0; k < m; k++) {
      const term = at(f, add(a, k));
      if (checkTerms && term !== S.Zero) {
        const value = numeric(term);
        if (value === undefined && k === 0) return [term, S.Zero];
        if (value !== undefined && Math.abs(value) < eps) return [s, abs(term)];
      }
      s = add(s, term);
    }
    if (add(b, mul(-1, a), 1).key === Rational.of(m).key) return [s, S.Zero];
    a = add(a, m);
  }
  let integral = impl.integrate(f, i, [a, b]);
  if (integral instanceof Integral) {
    // Euler-Maclaurin assumes a smooth summand on the interval. Its formal
    // endpoint expression remains useful when symbolic bounds prevent the
    // definite integrator from deciding whether the interval crosses a pole.
    const primitive = impl.integrate(f, i);
    if (!(primitive instanceof Integral)) integral = add(at(primitive, b), mul(-1, at(primitive, a)));
  }
  s = add(s, integral);
  const fpoint = (e: Expr): [Expr, Expr] => (b instanceof Special && b.name === 'oo' ? [at(e, a), S.Zero] : [at(e, a), at(e, b)]);
  const [fa, fb] = fpoint(f);
  const iterm = mul(add(fa, fb), S.Half);
  let g = impl.diff(f, i, 1);
  let term: Expr = S.Zero;
  for (let k = 1; k <= n + 1; k++) {
    const [ga, gb] = fpoint(g);
    term = mul(bernoulliNumber(2 * k), pow(factorial(2 * k), -1), add(gb, mul(-1, ga)));
    if (k > n) break;
    if (eps > 0 && term !== S.Zero) {
      const value = numeric(term);
      if (value !== undefined && Number.isNaN(value)) return [S.NaN, S.NaN];
      if (value !== undefined && Math.abs(value) < eps) break;
    }
    s = add(s, term);
    g = impl.diff(g, i, 2);
  }
  return [add(s, iterm), abs(term)];
}
