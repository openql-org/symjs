// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/ring_series.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/** Truncated arithmetic in a specified series variable; all other generators remain parameters. */
import { NotImplementedError } from '../core/errors';
import { at, first } from '../core/guard';
import { removeO } from '../core/methods';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Float, Mul, Pow, Rational } from '../core/nodes';
import { lcm } from '../core/numbers';
import { exp, pow, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { fn } from '../functions/elementary/elementary';
import { series } from '../series/series';
import { expand } from '../simplify/expand';
import type { IntLike } from '../ntheory/intutil';
import { groundIsZero, intArg } from './compatibility';
import { QQ } from './domains';
import type { PolyElement } from './rings';
import { PolyRing } from './rings';
import type { PuiseuxTerm } from './puiseux';
import { PuiseuxPoly, PuiseuxRing, addExponents as plus, multiplyExponents as times, compareExponents as cmp, rationalExponent as rat } from './puiseux';

export type SeriesPoly = PolyElement | PuiseuxPoly;
export type SeriesFunction = (p: SeriesPoly, x: SeriesPoly, prec: ExprLike) => SeriesPoly;
const zero = Rational.of(0), one = Rational.of(1), minusOne = Rational.of(-1);
const minus = (a: Rational, b: Rational): Rational => plus(a, times(minusOne, b));

function lift(p: SeriesPoly): PuiseuxPoly {
  return p instanceof PuiseuxPoly ? p : new PuiseuxRing(p.ring.symbols, p.ring.domain).fromPoly(p);
}
function index(p: SeriesPoly, x: SeriesPoly): number {
  return lift(p).ring.index(lift(x));
}
function restore(p: SeriesPoly, q: PuiseuxPoly): SeriesPoly {
  // Fractional exponents are promoted instead of being rounded to JS numbers.
  if (p instanceof PuiseuxPoly || q.monoms().some((m) => m.some((e) => !e.isInteger))) return q;
  return p.ring.fromTerms(q.terms().map(([m, c]) => [m.map((e) => {
    const n = Number(e.p);
    if (!Number.isSafeInteger(n)) throw new RangeError('polynomial exponent exceeds the safe integer range');
    return n;
  }), c]));
}
function trunc(p: PuiseuxPoly, i: number, prec: Rational): PuiseuxPoly {
  return p.ring.fromDict(p.terms().filter(([m]) => cmp(at(m, i), prec) < 0));
}
function valuation(p: PuiseuxPoly, i: number): Rational {
  if (p.isZero) throw new RangeError('the zero series has no finite valuation');
  return p.monoms().map((m) => at(m, i)).reduce((a, b) => cmp(a, b) < 0 ? a : b);
}
function shift(p: PuiseuxPoly, i: number, amount: Rational): PuiseuxPoly {
  return p.ring.fromDict(p.terms().map(([m, c]) => [m.map((e, j) => j === i ? plus(e, amount) : e), c]));
}
function product(p: PuiseuxPoly, q: PuiseuxPoly, i: number, prec: Rational): PuiseuxPoly {
  p.ring.ringNew(q); // Require the same generators and coefficient domain.
  const terms: PuiseuxTerm[] = [];
  for (const [m, c] of p.terms()) for (const [n, d] of q.terms()) {
    if (cmp(plus(at(m, i), at(n, i)), prec) < 0) terms.push([m.map((e, j) => plus(e, at(n, j))), p.ring.domain.mul(c, d)]);
  }
  return p.ring.fromDict(terms);
}
function integral(p: PuiseuxPoly, i: number): PuiseuxPoly {
  return p.ring.fromDict(p.terms().map(([m, c]) => {
    const e = plus(at(m, i), one);
    if (e.isZero) throw new NotImplementedError('the integral contains a logarithm');
    return [m.map((a, j) => j === i ? e : a), p.ring.domainNew(c.div(e))];
  }));
}
function factorial(n: number): bigint {
  let r = 1n;
  for (let k = 2; k <= n; k++) r *= BigInt(k);
  return r;
}

/** Remove all terms of degree at least prec in x (SymPy rs_trunc). */
export function rsTrunc(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return restore(p, trunc(lift(p), index(p, x), rat(prec))); }
/** Multiply with truncation before accumulating terms (SymPy rs_mul). */
export function rsMul(p: SeriesPoly, q: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return restore(p, product(lift(p), lift(q), index(p, x), rat(prec))); }
/** Square modulo O(x**prec) (SymPy rs_square). */
export function rsSquare(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsMul(p, p, x, prec); }
/** Differentiate a finite series (SymPy rs_diff). */
export function rsDiff(p: SeriesPoly, x: SeriesPoly): SeriesPoly { const q = lift(p); return restore(p, q.diff(at(q.ring.gens, index(p, x)))); }
/** Integrate a finite series when no logarithmic term is needed (SymPy rs_integrate). */
export function rsIntegrate(p: SeriesPoly, x: SeriesPoly): SeriesPoly { return restore(p, integral(lift(p), index(p, x))); }

/** Substitute x_i -> x_i**n in the exponent lattice (SymPy pow_xin). */
export function powXin(p: SeriesPoly, iIn: IntLike, n: ExprLike): SeriesPoly {
  const i = intArg(iIn);
  if (!Number.isInteger(i) || i < 0 || i >= p.ring.ngens) throw new RangeError('invalid generator index');
  const q = lift(p), exponent = rat(n);
  return restore(p, q.ring.fromDict(q.terms().map(([m, c]) => [m.map((e, j) => j === i ? times(e, exponent) : e), c])));
}
/** A nonintegral exponent in x; negative integer powers are not regular (SymPy rs_is_puiseux). */
export function rsIsPuiseux(p: SeriesPoly, x: SeriesPoly): boolean {
  const i = index(p, x);
  for (const m of lift(p).monoms()) {
    const e = at(m, i);
    if (!e.isInteger) return true;
    if (e.isNegative) throw new RangeError('the series is not regular');
  }
  return false;
}

/** Compose coefficients with a series of positive valuation. */
function composePositive(p: PuiseuxPoly, i: number, prec: Rational, coefficient: (n: number) => ExprLike): PuiseuxPoly {
  const constant = p.ring.groundNew(coefficient(0));
  if (p.isZero) return trunc(constant, i, prec);
  const v = valuation(p, i);
  if (cmp(v, zero) <= 0) throw new NotImplementedError('a positive series valuation is required');
  let result = trunc(constant, i, prec), power = p.ring.one;
  for (let k = 1; cmp(times(v, Rational.of(k)), prec) < 0; k++) {
    power = product(power, p, i, prec);
    result = result.add(power.mul(coefficient(k)));
  }
  return result;
}
/** Factor c*x**v from p, with a scalar nonzero leading coefficient. */
function normalize(p: PuiseuxPoly, i: number): [Rational, Expr, PuiseuxPoly] {
  const v = valuation(p, i), q = shift(p, i, times(minusOne, v));
  const c = q.get(q.ring.zeroMonom);
  if (groundIsZero(q.ring.domain, c) || q.terms().some(([m]) => at(m, i).isZero && m.some((e) => !e.isZero))) {
    throw new NotImplementedError('the leading coefficient must be a ground-domain unit');
  }
  return [v, c, q.truediv(c).sub(1)];
}
function rationalPower(p: PuiseuxPoly, exponent: Rational, i: number, prec: Rational): PuiseuxPoly {
  if (p.isZero) {
    if (exponent.isNegative) throw new RangeError('division by the zero series');
    // Zero exponents are handled by integerPower before this function is called.
    return p;
  }
  const [v, c, tail] = normalize(p, i);
  const offset = times(v, exponent);
  let binomial = one;
  const result = composePositive(tail, i, minus(prec, offset), (k) => {
    if (k) binomial = times(binomial, times(plus(exponent, Rational.of(1 - k)), Rational.of(1, k)));
    return binomial;
  });
  return shift(result.mul(p.ring.domainNew(pow(c, exponent))), i, offset);
}
function integerPower(p: PuiseuxPoly, n: bigint, i: number, prec: Rational): PuiseuxPoly {
  if (!n) return trunc(p.ring.one, i, prec);
  if (p.isZero) return p;
  const v = valuation(p, i), offset = times(v, Rational.of(n));
  const work = minus(prec, offset);
  let factor = trunc(shift(p, i, times(minusOne, v)), i, work), result = p.ring.one, k = n;
  while (k) {
    if (k & 1n) result = product(result, factor, i, work);
    k >>= 1n;
    if (k) factor = product(factor, factor, i, work);
  }
  return shift(result, i, offset);
}
/** Integer or rational power, retaining the requested final precision (SymPy rs_pow). */
export function rsPow(p: SeriesPoly, n: ExprLike, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const e = rat(n), q = lift(p), i = index(p, x), order = rat(prec);
  return restore(p, e.isInteger && !e.isNegative ? integerPower(q, e.p, i, order) : rationalPower(q, e, i, order));
}
/** Laurent/Puiseux reciprocal with a scalar leading coefficient (SymPy rs_series_inversion). */
export function rsSeriesInversion(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsPow(p, -1, x, prec); }
/** Expand the nth root, or its reciprocal for negative n (SymPy rs_nth_root). */
export function rsNthRoot(p: SeriesPoly, nIn: IntLike, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const n = intArg(nIn);
  if (!Number.isSafeInteger(n)) throw new RangeError('root order must be an integer');
  if (!n) {
    if (lift(p).isZero) throw new RangeError('0**0 expression');
    return p.ring.one;
  }
  return rsPow(p, Rational.of(1, n), x, prec);
}

type AnalyticName = 'exp' | 'sin' | 'cos' | 'sinh' | 'cosh' | 'atan' | 'atanh' | 'asin' | 'asinh' | 'LambertW';
function analyticCoefficient(name: AnalyticName, n: number): Rational {
  if (name === 'exp') return Rational.of(1, factorial(n));
  if (name === 'sin' || name === 'sinh') return n % 2 ? Rational.of(name === 'sin' && n % 4 === 3 ? -1 : 1, factorial(n)) : zero;
  if (name === 'cos' || name === 'cosh') return n % 2 ? zero : Rational.of(name === 'cos' && n % 4 === 2 ? -1 : 1, factorial(n));
  if (name === 'LambertW') return n ? Rational.of((-BigInt(n)) ** BigInt(n - 1), factorial(n)) : zero;
  if (n % 2 === 0) return zero;
  if (name === 'atan' || name === 'atanh') return Rational.of(name === 'atan' && n % 4 === 3 ? -1 : 1, n);
  const k = (n - 1) / 2;
  return Rational.of((name === 'asinh' && k % 2 ? -1n : 1n) * factorial(2 * k), 4n ** BigInt(k) * factorial(k) ** 2n * BigInt(n));
}
function analytic(p: SeriesPoly, x: SeriesPoly, prec: ExprLike, name: AnalyticName): SeriesPoly {
  // SymPy's exp/cos algorithms require a positive truncation order.
  if ((name === 'exp' || name === 'cos') && !rat(prec).isPositive) throw new RangeError('the series order must be positive');
  const q = lift(p), i = index(p, x), c = q.get(q.ring.zeroMonom), tail = q.sub(c);
  if (groundIsZero(q.ring.domain, c)) return restore(p, composePositive(tail, i, rat(prec), (k) => analyticCoefficient(name, k)));
  // Taylor coefficients at a nonzero ground constant, kept in the original domain.
  const t = new Dummy('t');
  let derivative = name === 'exp' ? exp(t) : fn(name, [t]);
  return restore(p, composePositive(tail, i, rat(prec), (k) => {
    if (k) derivative = diff(derivative, t);
    return q.ring.domainNew(derivative.subs([[t, q.ring.domain.toSympy(c)]]).div(Rational.of(factorial(k))));
  }));
}
/** Exponential series (SymPy rs_exp). */
export function rsExp(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'exp'); }
/** Sine series (SymPy rs_sin). */
export function rsSin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'sin'); }
/** Cosine series (SymPy rs_cos). */
export function rsCos(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'cos'); }
/** Hyperbolic sine series (SymPy rs_sinh). */
export function rsSinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'sinh'); }
/** Hyperbolic cosine series (SymPy rs_cosh). */
export function rsCosh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'cosh'); }
/** Arcsine series (SymPy rs_asin). */
export function rsAsin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'asin'); }
/** Inverse hyperbolic sine series (SymPy rs_asinh). */
export function rsAsinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'asinh'); }
/** Arctangent series (SymPy rs_atan). */
export function rsAtan(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'atan'); }
/** Inverse hyperbolic tangent series (SymPy rs_atanh). */
export function rsAtanh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'atanh'); }
/** Principal Lambert W series at zero (SymPy rs_LambertW). */
export function rsLambertW(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'LambertW'); }
/** Tangent series (SymPy rs_tan). */
export function rsTan(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsMul(rsSin(p, x, prec), rsSeriesInversion(rsCos(p, x, prec), x, prec), x, prec); }
/** Hyperbolic tangent series (SymPy rs_tanh). */
export function rsTanh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsMul(rsSinh(p, x, prec), rsSeriesInversion(rsCosh(p, x, prec), x, prec), x, prec); }
/** Cotangent Laurent series, computing enough terms before inversion (SymPy rs_cot). */
export function rsCot(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const v = valuation(lift(p), index(p, x));
  const order = plus(rat(prec), times(Rational.of(2), v));
  return rsSeriesInversion(rsTan(p, x, order), x, prec);
}
/** Logarithmic series for a nonzero ground constant (SymPy rs_log). */
export function rsLog(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), [v, c, tail] = normalize(q, i);
  if (!v.isZero) throw new NotImplementedError('the logarithm contains log(x)');
  const result = composePositive(tail, i, rat(prec), (k) => k ? Rational.of(k % 2 ? 1 : -1, k) : q.ring.domainNew(fn('log', [q.ring.domain.toSympy(c)])));
  return restore(p, result);
}

/** Finite composition sum(c[k]*p**k) with truncation (SymPy rs_series_from_list). */
export function rsSeriesFromList(p: SeriesPoly, c: readonly ExprLike[], x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), order = rat(prec);
  let result = q.ring.zero;
  c.forEach((coefficient, k) => { result = result.add(integerPower(q, BigInt(k), i, order).mul(coefficient)); });
  return restore(p, result);
}
/** Simultaneous substitution; replacements are not substituted into one another (SymPy rs_subs). */
export function rsSubs(p: SeriesPoly, rules: ReadonlyMap<SeriesPoly, SeriesPoly>, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), order = rat(prec), replacements = new Map<number, PuiseuxPoly>();
  for (const [a, b] of rules) replacements.set(index(p, a), q.ring.ringNew(lift(b)));
  let result = q.ring.zero;
  for (const [m, c] of q.terms()) {
    const factors = m.map((exponent, j) => ({ exponent, base: replacements.get(j) ?? at(q.ring.gens, j) })).filter(({ exponent }) => !exponent.isZero);
    if (factors.some(({ base, exponent }) => base.isZero && exponent.isNegative)) throw new RangeError('substitution divides by the zero series');
    if (factors.some(({ base, exponent }) => base.isZero && exponent.isPositive)) continue;
    const valuations = factors.map(({ base, exponent }) => times(valuation(base, i), exponent));
    let remaining = valuations.reduce(plus, zero), term = q.ring.groundNew(c);
    factors.forEach(({ base, exponent }, j) => {
      const precision = plus(minus(order, valuations.reduce(plus, zero)), at(valuations, j));
      let power: PuiseuxPoly;
      if (base.isTerm) {
        // Unchanged parameter generators can carry fractional powers too;
        // they do not need inversion in the selected series variable.
        const [monom, coefficient] = first(base.terms());
        power = q.ring.fromDict([[monom.map((e) => times(e, exponent)), q.ring.domainNew(pow(coefficient, exponent))]]);
      } else power = exponent.isInteger && exponent.isPositive ? integerPower(base, exponent.p, i, precision) : rationalPower(base, exponent, i, precision);
      remaining = minus(remaining, at(valuations, j));
      term = product(term, power, i, minus(order, remaining));
    });
    result = result.add(trunc(term, i, order));
  }
  return restore(p, result);
}
/** Revert p(x)=y with a scalar nonzero coefficient of x (SymPy rs_series_reversion). */
export function rsSeriesReversion(p: SeriesPoly, x: SeriesPoly, nIn: IntLike, y: SeriesPoly): SeriesPoly {
  const n = intArg(nIn);
  const q = lift(p), i = index(p, x), j = index(p, y);
  if (!Number.isSafeInteger(n) || n < 1) throw new RangeError('the series order must be positive');
  if (rsIsPuiseux(p, x)) throw new NotImplementedError('reversion requires integer exponents');
  if (q.terms().some(([m]) => at(m, i).isZero)) throw new RangeError('the series must have no constant term');
  const leading = q.ring.fromDict(q.terms().filter(([m]) => at(m, i).isOne));
  const a = leading.get(q.ring.zeroMonom.map((e, k) => k === i ? one : e));
  if (leading.length !== 1 || groundIsZero(q.ring.domain, a)) throw new NotImplementedError('reversion requires a nonzero scalar linear coefficient');
  let result = lift(y).truediv(a);
  for (let k = 2; k < n; k++) {
    const composed = lift(rsSubs(q, new Map([[lift(x), result]]), lift(y), k + 1));
    result = result.sub(q.ring.fromDict(composed.terms().filter(([m]) => at(m, j).key === Rational.of(k).key)).truediv(a));
  }
  return restore(p, trunc(result, j, Rational.of(n)));
}
/** Transfer an ordinary-series algorithm to a fractional exponent lattice (SymPy rs_puiseux). */
export function rsPuiseux(f: SeriesFunction, p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const i = index(p, x), denominator = lift(p).monoms().reduce((n, m) => lcm(n, at(m, i).q), 1n);
  const scaled = powXin(p, i, Rational.of(denominator));
  return powXin(f(scaled, x, times(rat(prec), Rational.of(denominator))), i, Rational.of(1, denominator));
}
/** Compose a univariate series algorithm with a multivariate input (SymPy rs_fun). */
export function rsFun(p: SeriesPoly, f: SeriesFunction, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), constant = q.get(q.ring.zeroMonom), tail = q.sub(constant);
  const r = new PuiseuxRing([new Dummy('t')], q.ring.domain), t = first(r.gens);
  const order = rat(prec);
  const v = tail.isZero ? one : valuation(tail, i);
  if (!v.isPositive) throw new NotImplementedError('composition requires positive valuation');
  const count = Number((order.p * v.q + order.q * v.p - 1n) / (order.q * v.p));
  const expansion = lift(f(t.add(constant), t, Math.max(1, count)));
  return restore(p, lift(rsSeriesFromList(tail, Array.from({ length: Math.max(1, count) }, (_, k) => expansion.get([k])), at(q.ring.gens, i), prec)));
}
/** Coefficientwise division/multiplication by factorials (SymPy rs_hadamard_exp). */
export function rsHadamardExp(p: SeriesPoly, inverse = false): SeriesPoly {
  const q = lift(p);
  if (q.ring.domain !== QQ) throw new NotImplementedError('Hadamard exponential requires QQ');
  return restore(p, q.ring.fromDict(q.terms().map(([m, c]) => {
    const e = first(m);
    if (!e.isInteger || e.isNegative) throw new RangeError('factorial weights require nonnegative integer exponents');
    const f = factorial(Number(e.p));
    return [m, inverse ? c.mul(Rational.of(f)) : c.div(Rational.of(f))];
  })));
}
/** Newton power-sum generating series of a univariate polynomial (SymPy rs_newton). */
export function rsNewton(p: PolyElement, x: PolyElement, prec: ExprLike): SeriesPoly {
  if (p.ring.ngens !== 1 || p.isZero) throw new RangeError('Newton sums require a nonzero univariate polynomial');
  const degree = p.degree(), reversed = p.ring.fromTerms(p.listterms().map(([m, c]) => [[degree - first(m)], c]));
  const q = lift(p);
  return restore(p, q.ring.groundNew(degree).sub(lift(rsMul(rsDiff(reversed, x), rsSeriesInversion(reversed, x, prec), x, prec)).mul(lift(x))));
}
/** Polynomial whose roots are all pairwise sums of roots (SymPy rs_compose_add). */
export function rsComposeAdd(p: PolyElement, q: PolyElement): PolyElement {
  if (!p.ring.equals(q.ring) || p.ring.ngens !== 1 || p.isZero || q.isZero) throw new RangeError('expected nonzero polynomials in the same univariate ring');
  const x = first(p.ring.gens), degree = p.degree() * q.degree(), prec = degree + 1;
  const sums = lift(rsHadamardExp(rsMul(rsHadamardExp(rsNewton(p, x, prec)), rsHadamardExp(rsNewton(q, x, prec)), x, prec), true));
  const integrand = shift(sums.ring.groundNew(sums.get([0])).sub(sums), 0, minusOne);
  const exponential = lift(rsExp(restore(p, integral(integrand, 0)), x, prec));
  return p.ring.fromTerms(exponential.terms().map(([m, c]) => [[degree - Number(first(m).p)], c])).primitive()[1];
}
/** Expand an expression at zero and return its finite polynomial/Puiseux part (SymPy rs_series). */
export function rsSeries(expr: ExprLike, x: Sym, prec: IntLike): SeriesPoly {
  const expanded = expand(removeO(series(sympify(expr), x, 0, intArg(prec))));
  const generators = new Map<string, Expr>([[x.key, x]]);
  const collect = (e: Expr): void => {
    if (e instanceof Rational || e instanceof Float || e.key === x.key) return;
    if (e instanceof Add || e instanceof Mul) { e.args.forEach(collect); return; }
    if (e instanceof Pow && e.exp instanceof Rational && (e.has(x) || e.exp.isInteger)) { collect(e.base); return; }
    if (e.has(x)) throw new NotImplementedError('the expression did not expand into a finite Puiseux series');
    generators.set(e.key, e);
  };
  collect(expanded);
  const symbols = [...generators.values()], p = new PuiseuxRing(symbols, QQ).fromExpr(expanded);
  return restore(new PolyRing(symbols, QQ).zero, p);
}

/** Cosine and sine series to the same precision (SymPy rs_cos_sin). */
export function rsCosSin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): [SeriesPoly, SeriesPoly] {
  return [rsCos(p, x, prec), rsSin(p, x, prec)];
}
/** Hyperbolic cosine and sine series (SymPy rs_cosh_sinh). */
export function rsCoshSinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): [SeriesPoly, SeriesPoly] {
  return [rsCosh(p, x, prec), rsSinh(p, x, prec)];
}
