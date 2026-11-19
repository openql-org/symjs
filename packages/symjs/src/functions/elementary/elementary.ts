// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Elementary functions with automatic evaluation of special values.
 */

import { accumBoundsFunction } from './accumbounds';
import { AccumBounds } from '../../core/accumbounds';
import { piecewise } from '../../core/logic';
import { expectType, first } from '../../core/guard';
import { precToDps } from '../../numeric/mpf';
import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPositive, isReal } from '../../core/assumptions';
import type { ExprLike, FnName } from '../../core/nodes';
import {
  Add,
  Constant,
  Expr,
  Fn,
  Mul,
  Piecewise,
  Pow,
  Float,
  Rational,
  S,
  Special,
  impl,
  isNum,
  ExtensionExpr,
  Sym, registerFunctionHeads,
  UndefFn,
} from '../../core/nodes';
import { numAbs, numNeg, ratFloor, ratMod } from '../../core/num';
import { add, couldExtractMinusSign, exp, mul, neg, pow, splitCoeff, sqrt, sympify } from '../../core/ops';

export type Evaluator = (x: Expr, ...rest: Expr[]) => Expr | undefined;

/** Calls f for every entry of a registration table keyed by function name. */
export function forEachEntry<K extends string, V>(table: Partial<Record<K, V>>, f: (name: K, value: V) => void): void {
  for (const name in table) {
    const v = table[name];
    if (v !== undefined) f(name, v);
  }
}

const isI = (e: Expr) => e instanceof Constant && e.name === 'I';
const isPi = (e: Expr) => e instanceof Constant && e.name === 'pi';

/** If x = c*pi with rational c, return c. */
function piCoeff(x: Expr): Rational | undefined {
  if (isPi(x)) return S.One;
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [c, rest] = splitCoeff(x);
  if (c instanceof Rational && isPi(rest)) return c;
  return undefined;
}

/**
 * SymPy _pi_coeff for a product c*x*pi with an integer x: the coefficient of pi reduced modulo 2
 * (a Float c that is an exact binary fraction counts as that rational). Undefined for other arguments.
 * Integer results are all that tan needs, so even multiples give 0 rather than SymPy's parity marker 2.
 */
function integerPiCoeff(arg: Expr): Expr | undefined {
  if (!(arg instanceof Mul) || !arg.args.some(isPi)) return undefined;
  const cx = mul(...arg.args.filter((a) => !isPi(a)));
  const [c0, x] = splitCoeff(cx);
  if (isNum(x) || isIntegerQ(x) !== true) return undefined;
  let c: Rational | undefined = c0 instanceof Rational ? c0 : undefined;
  if (c0 instanceof Float) {
    const v = Number(c0.value);
    const f = Math.abs(v) % 1;
    if (f === 0) c = Rational.of(BigInt(Math.trunc(v)));
    else {
      const m = 2 ** -Math.round(Math.log2(f));
      if (Number.isInteger(v * m)) c = Rational.of(BigInt(v * m), BigInt(m));
    }
  }
  if (c === undefined) return undefined;
  // the coefficient modulo 2 (an even multiple gives 0, an odd one x itself)
  return mul(ratMod(c, S.Two), x);
}

/** Split x = a + c*pi where c is rational (c may be zero). */
export function splitPiTerm(x: Expr): [Expr, Rational] {
  const c = piCoeff(x);
  if (c) return [S.Zero, c];
  if (x instanceof Add) {
    for (const [i, xi] of x.args.entries()) {
      const ci = piCoeff(xi);
      if (ci) return [add(...x.args.filter((_, j) => j !== i)), ci];
    }
  }
  return [x, S.Zero];
}

const r = (p: number, q = 1) => Rational.of(p, q);

/** sin(k*pi/12 ... ) table for multiples of pi in [0, 2): key = c.key */
function sinOfPiMultiple(c: Rational): Expr | undefined {
  // reduce to [0, 2)
  const m = ratMod(c, S.Two);
  // use symmetry: sin(pi + t) = -sin(t)
  if (m.p * 1n >= m.q) {
    const v = sinOfPiMultiple(Rational.of(m.p - m.q, m.q));
    return v === undefined ? undefined : neg(v);
  }
  // m in [0, 1): sin(pi - t) = sin(t)
  const t = m.p * 2n > m.q ? Rational.of(m.q - m.p, m.q) : m; // t in [0, 1/2]
  const table: Record<string, () => Expr> = {
    '0': () => S.Zero,
    '1/2': () => S.One,
    '1/6': () => S.Half,
    '1/4': () => mul(S.Half, sqrt(2)),
    '1/3': () => mul(S.Half, sqrt(3)),
    '1/12': () => mul(r(1, 4), add(sqrt(6), neg(sqrt(2)))),
    '5/12': () => mul(r(1, 4), add(sqrt(6), sqrt(2))),
    '1/10': () => add(r(-1, 4), mul(r(1, 4), sqrt(5))),
    '3/10': () => add(r(1, 4), mul(r(1, 4), sqrt(5))),
    '1/5': () => sqrt(add(r(5, 8), mul(r(-1, 8), sqrt(5)))),
    '2/5': () => sqrt(add(r(5, 8), mul(r(1, 8), sqrt(5)))),
    '1/8': () => sqrt(add(r(1, 2), mul(r(-1, 4), sqrt(2)))),
    '3/8': () => sqrt(add(r(1, 2), mul(r(1, 4), sqrt(2)))),
  };
  return table[t.key]?.();
}

function cosOfPiMultiple(c: Rational): Expr | undefined {
  // cos(x) = sin(x + pi/2)
  return sinOfPiMultiple(Rational.of(c.p * 2n + c.q, c.q * 2n));
}

// ---------------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------------

/** SymPy _peeloff_pi: the multiple of pi/2 in c*pi, c - (c mod 1/2). */
function peelHalfPi(c: Rational): Rational {
  const twice = Rational.of(c.p * 2n, c.q);
  return Rational.of(ratFloor(twice), 2n);
}

/** sin(c*pi) for rational c (SymPy sin.eval of a rational multiple of pi). */
function sinPi(c: Rational): Expr | undefined {
  const v = sinOfPiMultiple(c);
  if (v !== undefined) return v;
  const m = ratMod(c, S.Two);
  if (m.p > m.q) return neg(sin(mul(Rational.of(m.p - m.q, m.q), S.Pi)));
  if (2n * m.p > m.q) return sin(mul(Rational.of(m.q - m.p, m.q), S.Pi));
  return m.equals(c) ? undefined : sin(mul(m, S.Pi));
}

/** cos(c*pi) for rational c (SymPy cos.eval of a rational multiple of pi). */
function cosPi(c: Rational): Expr | undefined {
  const v = cosOfPiMultiple(c);
  if (v !== undefined) return v;
  if (c.isNegative) return cos(mul(numNeg(c), S.Pi));
  // the coefficient reduced into [0, 2); SymPy keeps cos(15*pi/7) as it is
  const m = ratMod(c, S.Two);
  if (m.p > m.q) return neg(cos(mul(Rational.of(m.p - m.q, m.q), S.Pi)));
  if (2n * m.p > m.q) return neg(cos(mul(Rational.of(m.q - m.p, m.q), S.Pi)));
  return undefined;
}

/**
 * SymPy sin/cos/tan.eval at an infinity: nan for nan and zoo, AccumBounds(-1, 1) for sin and
 * cos at oo and -oo, AccumBounds(-oo, oo) for tan. Undefined for other arguments.
 */
function trigAtInfinity(x: Expr, bound: Expr): Expr | undefined {
  if (!(x instanceof Special)) return undefined;
  if (x.name === 'nan' || x.name === 'zoo') return S.NaN;
  return AccumBounds(neg(bound), bound);
}

const evalSin: Evaluator = (x) => {
  const inf = trigAtInfinity(x, S.One);
  if (inf) return inf;
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) return sinPi(c);
  if (couldExtractMinusSign(x)) return neg(sin(neg(x)));
  const m = peelHalfPi(c);
  if (!m.isZero) {
    // SymPy: sin(m*pi)*cos(x) + cos(m*pi)*sin(x) with x = arg - m*pi
    const mp = mul(m, S.Pi);
    const xr = add(rest, mul(add(c, numNeg(m)), S.Pi));
    return add(mul(sin(mp), cos(xr)), mul(cos(mp), sin(xr)));
  }
  if (x instanceof Fn && x.name === 'asin') return x.args[0];
  return undefined;
};

const evalCos: Evaluator = (x) => {
  const inf = trigAtInfinity(x, S.One);
  if (inf) return inf;
  if (x instanceof Rational && x.isZero) return S.One;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) return cosPi(c);
  if (couldExtractMinusSign(x)) return cos(neg(x));
  const m = peelHalfPi(c);
  if (!m.isZero) {
    // SymPy: cos(m*pi)*cos(x) - sin(m*pi)*sin(x) with x = arg - m*pi
    const mp = mul(m, S.Pi);
    const xr = add(rest, mul(add(c, numNeg(m)), S.Pi));
    return add(mul(cos(mp), cos(xr)), neg(mul(sin(mp), sin(xr))));
  }
  if (x instanceof Fn && x.name === 'acos') return x.args[0];
  return undefined;
};

const evalTan: Evaluator = (x) => {
  const inf = trigAtInfinity(x, S.Infinity);
  if (inf) return inf;
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) {
    const s = sinOfPiMultiple(c);
    const co = cosOfPiMultiple(c);
    // tan(pi/2 + k*pi) = 1/0 = zoo
    if (s && co) return mul(s, pow(co, -1));
    // SymPy: the coefficient reduced into [-1/2, 1/2)
    const r1 = ratMod(Rational.of(2n * c.p + c.q, 2n * c.q), S.One);
    const n = Rational.of(2n * r1.p - r1.q, 2n * r1.q);
    if (!n.equals(c)) return tan(mul(n, S.Pi));
    return c.isNegative ? neg(tan(mul(numNeg(c), S.Pi))) : undefined;
  }
  if (!c.isZero) {
    const m = ratMod(c, S.One);
    if (m.isZero) return tan(rest);
    if (!m.equals(c)) return tan(add(rest, mul(m, S.Pi)));
  }
  const ic = integerPiCoeff(x);
  if (ic !== undefined) {
    if (isIntegerQ(ic) === true) return S.Zero;
    const narg = mul(ic, S.Pi);
    if (narg.key !== x.key) return tan(narg);
  }
  if (couldExtractMinusSign(x)) return neg(tan(neg(x)));
  if (x instanceof Fn && x.name === 'atan') return x.args[0];
  return undefined;
};

const evalAsin: Evaluator = (x) => {
  if (x instanceof Special && x.name === 'oo') return mul(-1, S.I, S.Infinity);
  if (x instanceof Special && x.name === '-oo') return mul(S.I, S.Infinity);
  const table: Record<string, Expr> = {
    '0': S.Zero,
    '1': mul(S.Half, S.Pi),
    '1/2': mul(r(1, 6), S.Pi),
  };
  if (x.key in table) return table[x.key];
  if (x.equals(mul(S.Half, sqrt(2)))) return mul(r(1, 4), S.Pi);
  if (x.equals(mul(S.Half, sqrt(3)))) return mul(r(1, 3), S.Pi);
  if (couldExtractMinusSign(x)) return neg(asin(neg(x)));
  return undefined;
};

const evalAcos: Evaluator = (x) => {
  if (x instanceof Special && x.name === 'oo') return mul(S.I, S.Infinity);
  if (x instanceof Special && x.name === '-oo') return mul(-1, S.I, S.Infinity);
  const v = evalAsin(x);
  // only exact values; acos(-u) stays (SymPy does not rewrite it through asin)
  const hasAsin = (t: Expr): boolean => (t instanceof Fn && t.name === 'asin') || t.args.some(hasAsin);
  if (v === undefined || hasAsin(v)) return undefined;
  return add(mul(S.Half, S.Pi), neg(v));
};

const evalAtan: Evaluator = (x) => {
  if (x === S.ComplexInfinity) return AccumBounds(mul(S.NegHalf, S.Pi), mul(S.Half, S.Pi));
  if (x instanceof Special && x.name === 'oo') return mul(S.Half, S.Pi);
  if (x instanceof Special && x.name === '-oo') return mul(S.NegHalf, S.Pi);
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (x instanceof Rational && x.isOne) return mul(r(1, 4), S.Pi);
  if (x.equals(sqrt(3))) return mul(r(1, 3), S.Pi);
  if (x.equals(mul(r(1, 3), sqrt(3)))) return mul(r(1, 6), S.Pi);
  if (couldExtractMinusSign(x)) return neg(atan(neg(x)));
  return undefined;
};

const evalSinh: Evaluator = (x) => {
  if (x instanceof Special && (x.name === 'oo' || x.name === '-oo')) return x;
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(sinh(neg(x)));
  return undefined;
};
const evalCosh: Evaluator = (x) => {
  if (x instanceof Special && (x.name === 'oo' || x.name === '-oo')) return S.Infinity;
  if (x instanceof Rational && x.isZero) return S.One;
  if (couldExtractMinusSign(x)) return cosh(neg(x));
  return undefined;
};
const evalTanh: Evaluator = (x) => {
  if (x instanceof Special && x.name === 'oo') return S.One;
  if (x instanceof Special && x.name === '-oo') return S.NegOne;
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(tanh(neg(x)));
  return undefined;
};

/** Does e contain a function call (an angle that did not evaluate to a multiple of pi)? */
const hasFn = (e: Expr): boolean => e instanceof Fn || e.args.some(hasFn);

const evalLog: Evaluator = (x, ...more) => {
  // log(x, base) written as a call with two arguments (parsed SymPy source)
  const base = more[0];
  if (base !== undefined) return log(x, base);
  if (x instanceof Special) return x.name === 'nan' ? S.NaN : x.name === 'zoo' ? S.ComplexInfinity : S.Infinity;
  if (x instanceof Rational) {
    if (x.isOne) return S.Zero;
    if (x.isZero) return S.ComplexInfinity;
    if (x.isNegative) return add(log(numNeg(x)), mul(S.I, S.Pi));
    if (x.p === 1n && x.q !== 1n) return neg(log(Rational.of(x.q, 1n)));
  }
  if (x instanceof Constant && x.name === 'E') return S.One;
  if (x instanceof Mul && x.freeSymbols().size === 0) {
    const reciprocal = x.args.find((term): term is Pow => term instanceof Pow && term.exp.equals(S.NegOne)
      && term.base instanceof Fn && term.base.name === 'abs');
    if (reciprocal) {
      const value = first(reciprocal.base.args);
      if (mul(...x.args.filter((term) => term !== reciprocal)).equals(value) && isNonZero(value) === true) {
        // Dividing by the modulus puts a nonzero number on the unit circle.
        return mul(S.I, arg(value));
      }
    }
  }
  // SymPy log.eval splits the principal argument of negative numeric
  // expressions, including sums of radicals. Symbolic signs stay unevaluated.
  if (x.freeSymbols().size === 0 && isNegative(x) === true) return add(log(neg(x)), mul(S.I, S.Pi));
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E' && isReal(x.exp)) return x.exp;
  // log(+-I*oo) = oo; log(c*I) = log(|c|) +- I*pi/2 for a rational c (SymPy log.eval)
  if (x.key === mul(S.I, S.Infinity).key || x.key === mul(-1, S.I, S.Infinity).key) return S.Infinity;
  const [c, rest] = splitCoeff(x);
  if (isI(rest) && c instanceof Rational) {
    return c.isNegative ? add(mul(S.NegHalf, S.I, S.Pi), log(numNeg(c))) : add(mul(S.Half, S.I, S.Pi), log(c));
  }
  if (x instanceof Mul && x.args.some(isI)) {
    const coefficient = mul(...x.args.filter((a) => !isI(a)));
    if (isPositive(coefficient) === true) return add(log(coefficient), mul(S.Half, S.I, S.Pi));
    if (isNegative(coefficient) === true) return add(log(neg(coefficient)), mul(S.NegHalf, S.I, S.Pi));
  }
  // a + b*I whose argument is a rational multiple of pi
  if (x instanceof Add && x.freeSymbols().size === 0 && !isReal(x) && !x.args.some((a) => a instanceof Float)) {
    const t = arg(x);
    if (!hasFn(t)) return add(log(abs(x)), mul(S.I, t));
  }
  return undefined;
};

/** Sign of a real constant expression decided numerically (SymPy evaluates is_positive by evalf). */
function numericSign(x: Expr): 1 | -1 | undefined {
  if (x.freeSymbols().size || x instanceof Rational || x.has(S.I)) return undefined;
  if (!(x instanceof Fn || x instanceof Mul || x instanceof Pow || x instanceof Add)) return undefined;
  try {
    const v = x.toComplex();
    if (Math.abs(v.im) > 1e-14 * Math.max(1, Math.abs(v.re)) || !Number.isFinite(v.re) || Math.abs(v.re) < 1e-12) return undefined;
    return v.re > 0 ? 1 : -1;
  } catch {
    return undefined;
  }
}

/** Is e known to be an even integer (an even integer times an integer)? */
function isEven(e: Expr): boolean {
  const [c, r] = splitCoeff(e);
  return c instanceof Rational && c.isInteger && c.p % 2n === 0n && isIntegerQ(r) === true;
}

const evalAbs: Evaluator = (x) => {
  if (x.kind === 'Set') throw new TypeError('Abs requires an expression');
  if (isNum(x)) return numAbs(x);
  if (!isNonNegative(x) && !isNegative(x)) {
    const sg = numericSign(x);
    if (sg === 1) return x;
    if (sg === -1) return neg(x);
  }
  if (x instanceof Special) return x.name === 'nan' ? S.NaN : S.Infinity;
  if (isI(x)) return S.One;
  if (isNonNegative(x)) return x;
  if (isNegative(x)) return neg(x);
  // SymPy Abs.eval: signsimp(arg) takes the minus sign out of a sum (Abs(1 - x) = Abs(x - 1))
  if (x instanceof Add && couldExtractMinusSign(x)) return abs(neg(x));
  if (x instanceof Mul) {
    // SymPy Abs.eval: factors whose Abs evaluates to something other than an Abs come out, the rest
    // stay inside a single Abs (each factor by the registered Abs rules, such as those of polar
    // numbers: |exp_polar(z)| = exp(re(z)) comes out, |polar_lift(z)| = Abs(z) stays inside)
    const known: Expr[] = [];
    const unknown: Expr[] = [];
    for (const t of x.args) {
      if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && isReal(t.base) !== true) {
        unknown.push(t);
        continue;
      }
      const v = abs(t);
      if (v instanceof Fn && v.name === 'abs') unknown.push(t);
      else known.push(v);
    }
    if (known.length === 0) return undefined;
    return mul(...known, ...(unknown.length ? [new Fn('abs', [mul(...unknown)])] : []));
  }
  if (x instanceof Pow) {
    // SymPy Abs.eval of a power
    const [b, e] = x.args;
    if (b instanceof Constant && b.name === 'E') return pow(b, re(e));
    if (isReal(b) === true) {
      if (isIntegerQ(e) === true) {
        if (isEven(e)) return x;
        if (b instanceof Rational && b.p === -1n && b.q === 1n) return S.One;
        // SymPy Abs._eval_power: Abs(b)**n = b**(n - 1)*Abs(b) for an odd integer n other than -1
        if (e instanceof Rational && e.p > 1n) return mul(pow(b, Rational.of(e.p - 1n)), abs(b));
        if (e instanceof Rational && e.p < -1n) return mul(pow(b, Rational.of(e.p + 1n)), pow(abs(b), -1));
        return pow(abs(b), e);
      }
      if (isNonNegative(b) === true) return pow(b, re(e));
      if (isNegative(b) === true) return mul(pow(neg(b), re(e)), exp(mul(-1, S.Pi, im(e))));
    }
    // a complex base: SymPy keeps Abs(x**2); symjs gives Abs(x)**2 (relied on by the transforms code)
    if (isReal(e) === true) return pow(abs(b), e);
  }
  if (x instanceof Fn && (x.name === 'abs' || x.name === 'conjugate')) return abs(first(x.args));
  // SymPy Abs.eval keeps Abs of an imaginary symbol (its assumptions never fix the sign of -I*x)
  if (x instanceof Sym && x.assumptions.imaginary === true) return undefined;
  // a + b*I with real a, b
  const [a, b] = reIm(x);
  if (!(b instanceof Rational && b.isZero) && !hasReIm(a) && !hasReIm(b)) {
    return sqrt(add(pow(a, 2), pow(b, 2)));
  }
  return undefined;
};

const hasReIm = (e: Expr): boolean =>
  (e instanceof Fn && (e.name === 're' || e.name === 'im')) || e.args.some(hasReIm);

/** Decompose into real and imaginary parts when possible (fallback: re()/im() nodes). */
function reIm(x: Expr): [Expr, Expr] {
  return [re(x), im(x)];
}

/**
 * b**r for rational r and b = I or a negative rational: [|b|**r*cos(pi r), |b|**r*sin(pi r)]
 * ((-2)**(1/3) = 2**(1/3)*(-1)**(1/3), I**r = (-1)**(r/2)).
 */
function unitRoot(x: Expr): [Expr, Expr] | undefined {
  if (!(x instanceof Pow && x.exp instanceof Rational)) return undefined;
  const b = x.base;
  const negative = b instanceof Rational && b.isNegative;
  if (!negative && !isI(b)) return undefined;
  const ang = mul(negative ? x.exp : mul(x.exp, S.Half), S.Pi);
  const scale = negative ? pow(neg(b), x.exp) : S.One;
  return [mul(scale, cos(ang)), mul(scale, sin(ang))];
}

/** SymPy re/im: an imaginary argument (or one whose product with I is real) is I times a real. */
const isImaginaryArg = (x: Expr): boolean => (x instanceof Sym && x.assumptions.imaginary === true) || isReal(mul(S.I, x)) === true;

/** log of a nonnegative argument: an extended real number (-oo at 0), as SymPy's re and im take it. */
const isExtendedRealLog = (x: Expr): boolean => x instanceof Fn && x.name === 'log' && isNonNegative(first(x.args)) === true;

/** For a product of real factors and z, take the component of z after extracting a factor I. */
function productComponent(x: Mul, imaginary: boolean): Expr | undefined {
  const component = imaginary ? im : re;
  const rotated = (z: Expr): Expr => imaginary ? re(z) : neg(im(z));
  const real: Expr[] = [];
  const other: Expr[] = [];
  for (const factor of x.args) (isReal(factor) === true ? real : other).push(factor);
  if (real.length) {
    const rest = mul(...other);
    if (isI(rest)) return imaginary ? mul(...real) : S.Zero;
    if (rest instanceof Mul && rest.args.filter(isI).length === 1) {
      return mul(...real, rotated(mul(...rest.args.filter((a) => !isI(a)))));
    }
    return mul(...real, component(rest));
  }
  if (x.args.some(isI)) return rotated(mul(...x.args.filter((a) => !isI(a))));
  return undefined;
}

const evalRe: Evaluator = (x) => {
  if (x instanceof ExtensionExpr) {
    const parts = x.asRealImagSelf();
    if (parts !== undefined) return parts[0];
  }
  if (isReal(x) || isExtendedRealLog(x)) return x;
  if (isI(x)) return S.Zero;
  const ur = unitRoot(x);
  if (ur) return ur[0];
  if (x instanceof Add) return add(...x.args.map(re));
  if (x instanceof Mul) {
    const part = productComponent(x, false);
    if (part !== undefined) return part;
  }
  if (x instanceof Fn && x.name === 'conjugate') return re(first(x.args));
  if (isImaginaryArg(x)) return S.Zero;
  return undefined;
};

const evalIm: Evaluator = (x) => {
  if (x instanceof ExtensionExpr) {
    const parts = x.asRealImagSelf();
    if (parts !== undefined) return parts[1];
  }
  const ur = unitRoot(x);
  if (ur) return ur[1];
  if (isReal(x) || isExtendedRealLog(x)) return S.Zero;
  if (isI(x)) return S.One;
  if (x instanceof Add) return add(...x.args.map(im));
  if (x instanceof Mul) {
    const part = productComponent(x, true);
    if (part !== undefined) return part;
  }
  if (x instanceof Fn && x.name === 'conjugate') return neg(im(first(x.args)));
  if (isImaginaryArg(x)) return mul(-1, S.I, x);
  return undefined;
};

const evalArg: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.NaN;
  // SymPy: arg(arg(arg(...))) is nan, and so is arg(arg(r)) for real r
  {
    let a = x;
    let depth = 0;
    while (depth < 3 && a instanceof Fn && a.name === 'arg') {
      a = first(a.args);
      depth++;
    }
    if (depth === 3 || (depth === 2 && isReal(a) === true)) return S.NaN;
  }
  // the sign of a factor (SymPy sign(a) of 1 or -1: positive or negative, an infinite value included for a
  // function declared extended_positive or extended_negative)
  const knownSign = (t: Expr): 1 | -1 | undefined =>
    isPositive(t) === true ? 1 : isNegative(t) === true ? -1
      : t instanceof UndefFn ? (t.givenFacts.get('extended_positive') === true ? 1 : t.givenFacts.get('extended_negative') === true ? -1 : undefined) : undefined;
  const sign = knownSign(x) ?? numericSign(x);
  if (sign !== undefined) return sign === 1 ? S.Zero : S.Pi;
  // SymPy arg.eval: a factor of known sign counts by that sign only (arg((3 + I)*p) = arg(3 + I) for positive p)
  if (x instanceof Mul) {
    const reduced = mul(...x.args.map((t) => knownSign(t) ?? t));
    if (reduced.key !== x.key) return arg(reduced);
  }
  // a + b*I with real numeric a, b
  if (x.freeSymbols().size === 0 && !isReal(x)) {
    const a = re(x);
    const b = im(x);
    if (isNum(a) && isNum(b) && (a instanceof Float || b instanceof Float)) {
      return new Float(Math.atan2(b.value, a.value));
    }
    if (!(a instanceof Fn) && !(b instanceof Fn) && a.freeSymbols().size === 0) {
      // signs decided by the assumptions, else numerically (SymPy evaluates is_positive by evalf)
      const sign = (e: Expr): 1 | -1 | undefined => (isPositive(e) ? 1 : isNegative(e) ? -1 : numericSign(e));
      if (a instanceof Rational && a.isZero) {
        const sb = sign(b);
        return sb === undefined ? undefined : mul(Rational.of(sb, 2), S.Pi);
      }
      const sa = sign(a);
      if (sa !== undefined) {
        const t = atan(mul(b, pow(a, -1)));
        return sa === 1 ? t : sign(b) === -1 ? add(t, neg(S.Pi)) : add(t, S.Pi);
      }
    }
  }
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') {
    const t = im(x.exp);
    // a rational angle reduced into (-pi, pi]
    if (t instanceof Rational) {
      const n = Math.round(t.value / (2 * Math.PI));
      return n === 0 ? t : add(t, mul(-2 * n, S.Pi));
    }
  }
  return undefined;
};

/** Functions with f(conjugate(z)) = conjugate(f(z)) (real on the real axis); filled by special.ts. */
export const conjugateCommutes = new Set<string>();

/** Functions with their own conjugate (SymPy _eval_conjugate), by name; filled by the modules that define them. */
export const conjugateRules: Partial<Record<string, (args: readonly Expr[]) => Expr>> = {};

/** Complex conjugate, pushed through the expression tree. */
export function conjugate(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof Piecewise) return piecewise(...x.pairs.map(([value, condition]) => [conjugate(value), condition] as const));
  if (x instanceof ExtensionExpr) {
    const r = x.conjugateSelf();
    if (r !== undefined) return r;
  }
  if (isReal(x)) return x;
  if (isI(x)) return neg(S.I);
  // SymPy Symbol._eval_conjugate: an imaginary symbol is its negated conjugate
  if (x instanceof Sym && x.assumptions.imaginary === true) return neg(x);
  if (x instanceof Add) return add(...x.args.map(conjugate));
  if (x instanceof Mul) return mul(...x.args.map(conjugate));
  if (x instanceof Pow) {
    // SymPy Pow._eval_conjugate
    const [b, e] = x.args;
    if (isIntegerQ(e) === true) return pow(conjugate(b), e);
    if (isPositive(b) === true) return pow(b, conjugate(e));
  }
  if (x instanceof Fn) {
    switch (x.name) {
      case 'conjugate':
        return first(x.args);
      // conjugate(transpose(A)) = adjoint(A) and conjugate(adjoint(A)) = transpose(A)
      case 'transpose':
        return adjoint(first(x.args));
      case 'adjoint':
        return transpose(first(x.args));
      case 'sin':
      case 'cos':
      case 'tan':
      case 'sinh':
      case 'cosh':
      case 'tanh':
        return fn(x.name, [conjugate(first(x.args))]);
      default: {
        if (conjugateCommutes.has(x.name)) return fn(x.name, x.args.map(conjugate));
        const rule = conjugateRules[x.name];
        if (rule) return rule(x.args);
        break;
      }
    }
  }
  return new Fn('conjugate', [x]);
}

/**
 * Hermitian adjoint (SymPy adjoint): conjugate of commutative factors,
 * reversed product order for non-commutative ones.
 */
export function adjoint(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof Piecewise) return piecewise(...x.pairs.map(([value, condition]) => [adjoint(value), condition] as const));
  if (x instanceof ExtensionExpr) {
    const r = x.adjointSelf();
    if (r !== undefined) return r;
  }
  // SymPy Expr._eval_adjoint: a hermitian symbol is its own adjoint, an antihermitian one its negative
  if (x instanceof Sym && x.assumptions.hermitian === true) return x;
  if (x instanceof Sym && x.assumptions.antihermitian === true) return neg(x);
  if (x.isCommutative && !(x instanceof Add) && !(x instanceof Mul)) return conjugate(x);
  if (x instanceof Add) return add(...x.args.map(adjoint));
  if (x instanceof Mul) return mul(...[...x.args].reverse().map(adjoint));
  if (x instanceof Pow && x.exp.isCommutative && isReal(x.exp)) return pow(adjoint(x.base), x.exp);
  if (x instanceof Fn) {
    if (x.name === 'adjoint') return first(x.args);
    if (x.name === 'conjugate') return transpose(first(x.args));
    if (x.name === 'transpose') return conjugate(first(x.args));
    // SymPy Expr._eval_adjoint: transpose(conjugate(f)) when the conjugate evaluates
    const c = conjugate(x);
    if (!(c instanceof Fn && c.name === 'conjugate')) return transpose(c);
  }
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') return pow(x.base, adjoint(x.exp));
  return new Fn('adjoint', [x]);
}

/** Transpose (SymPy transpose): commutative scalars are unchanged, products reverse. */
export function transpose(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof Piecewise) return piecewise(...x.pairs.map(([value, condition]) => [transpose(value), condition] as const));
  if (x instanceof ExtensionExpr) {
    const r = x.transposeSelf();
    if (r !== undefined) return r;
  }
  if (x.isCommutative) return x;
  if (x instanceof Sym && x.assumptions.hermitian === true) return conjugate(x);
  if (x instanceof Sym && x.assumptions.antihermitian === true) return neg(conjugate(x));
  if (x instanceof Add) return add(...x.args.map(transpose));
  if (x instanceof Mul) return mul(...[...x.args].reverse().map(transpose));
  if (x instanceof Pow && x.exp.isCommutative && isReal(x.exp)) return pow(transpose(x.base), x.exp);
  if (x instanceof Fn) {
    if (x.name === 'transpose') return first(x.args);
    if (x.name === 'conjugate') return adjoint(first(x.args));
    if (x.name === 'adjoint') return conjugate(first(x.args));
  }
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') return pow(x.base, transpose(x.exp));
  return new Fn('transpose', [x]);
}

/** A symbolic involution that returns its own unevaluated call leaves evaluation to fn. */
function involutionEvaluator(name: FnName, apply: (x: Expr) => Expr): Evaluator {
  return (x) => {
    const result = apply(x);
    return result instanceof Fn && result.name === name && result.args[0] === x ? undefined : result;
  };
}

export const evaluators: Partial<Record<FnName, Evaluator>> = {
  adjoint: involutionEvaluator('adjoint', adjoint),
  transpose: involutionEvaluator('transpose', transpose),
  sin: evalSin,
  cos: evalCos,
  tan: evalTan,
  asin: evalAsin,
  acos: evalAcos,
  atan: evalAtan,
  sinh: evalSinh,
  cosh: evalCosh,
  tanh: evalTanh,
  log: evalLog,
  abs: evalAbs,
  re: evalRe,
  im: evalIm,
  arg: evalArg,
  conjugate: involutionEvaluator('conjugate', conjugate),
};

/** The sign of a finite part, undefined when it is not decided. */
type Sign = -1 | 0 | 1 | undefined;

/**
 * A number with an infinite part, as the signs of its parts: R is s*oo plus a finite imaginary part
 * of sign c (oo + I), I a finite real part of sign a plus t*oo*I (1 - oo*I), D both infinite
 * (oo - oo*I), zoo the complex infinity.
 */
export type InfiniteForm =
  | { readonly kind: 'R'; readonly s: 1 | -1; readonly c: Sign }
  | { readonly kind: 'I'; readonly a: Sign; readonly t: 1 | -1 }
  | { readonly kind: 'D'; readonly s: 1 | -1; readonly t: 1 | -1 }
  | { readonly kind: 'zoo' };

/** The sign of a real number without free symbols, or undefined. */
function signOfReal(e: Expr): -1 | 0 | 1 | undefined {
  if (isNum(e)) return e.isZero ? 0 : e.isPositive ? 1 : -1;
  if (isPositive(e) === true) return 1;
  if (isNegative(e) === true) return -1;
  return numericSign(e);
}

/** The real coefficient of I in t (I, 2*I, I*pi), or undefined. */
function imagCoeff(t: Expr): Expr | undefined {
  if (isI(t)) return S.One;
  if (!(t instanceof Mul) || t.args.filter(isI).length !== 1) return undefined;
  const r = mul(...t.args.filter((a) => !isI(a)));
  return isReal(r) === true ? r : undefined;
}

/** The form of a number with an infinite part (oo + I, 1 - oo*I, oo + oo*I, zoo, oo), else undefined. */
export function infiniteForm(z: Expr): InfiniteForm | undefined {
  if (z instanceof Special) {
    if (z.name === 'zoo') return { kind: 'zoo' };
    return z.name === 'nan' ? undefined : { kind: 'R', s: z.name === 'oo' ? 1 : -1, c: 0 };
  }
  if (!(z instanceof Add || z instanceof Mul) || z.freeSymbols().size > 0) return undefined;
  let s: -1 | 0 | 1 = 0;
  let t: -1 | 0 | 1 = 0;
  const re: Expr[] = [];
  const im: Expr[] = [];
  for (const u of z instanceof Add ? z.args : [z]) {
    if (u instanceof Special) {
      // (zoo and nan absorb finite terms, and oo - oo is nan: an Add has at most one of oo, -oo)
      s = u.name === 'oo' ? 1 : -1;
      continue;
    }
    // (the coefficient of oo*I is oo or -oo: c*oo is oo or -oo for a real number c)
    const w = imagCoeff(u);
    if (w instanceof Special) t = w.name === 'oo' ? 1 : -1;
    else if (w !== undefined) im.push(w);
    else if (isReal(u) === true) re.push(u);
    else return undefined;
  }
  if (s !== 0 && t !== 0) return { kind: 'D', s, t };
  if (s !== 0) return { kind: 'R', s, c: signOfReal(add(...im)) };
  return t === 0 ? undefined : { kind: 'I', a: signOfReal(add(...re)), t };
}

const halfPi = (k: number): Expr => mul(Rational.of(k, 2), S.Pi);
const iHalfPi = (k: number): Expr => mul(Rational.of(k, 2), S.I, S.Pi);
const ooI = (k: number): Expr => mul(k, S.I, S.Infinity);
const signedOo = (k: number): Expr => (k > 0 ? S.Infinity : S.NegativeInfinity);
/** zoo where the modulus grows without bound (the limit on the Riemann sphere). */
const zooUnless = (f: InfiniteForm, kinds: readonly string[]): Expr | undefined => (kinds.includes(f.kind) ? S.ComplexInfinity : undefined);

/** Reciprocal functions vanish at a directed infinity. The evaluator handles a pure real infinity. */
const reciprocalLimit = (f: InfiniteForm): Expr | undefined =>
  f.kind === 'zoo' || (f.kind === 'R' && f.c === 0) ? undefined : S.Zero;

/**
 * The values of functions at a number with an infinite part, where SymPy leaves them
 * unevaluated: the limit when it exists (zoo when the modulus grows without bound in no fixed
 * direction), with SymPy's own values (asin(oo) = -oo*I, asinh(oo*I) = oo, atanh(oo) = -I*pi/2)
 * left to the evaluators. A case that depends on the sign of a finite part needs it decided
 * (erf(oo + I*c) = 1 whatever c is, asin(oo + I*c) depends on it).
 */
const INFINITE_LIMITS: Partial<Record<FnName, (f: InfiniteForm) => Expr | undefined>> = {
  // gamma(-x + I*c), gamma(a + I*y), gamma(-x + I*y) -> 0; |gamma(x + I*c)| grows with a turning phase
  gamma: (f) => (f.kind === 'R' ? (!f.c ? undefined : f.s > 0 ? S.ComplexInfinity : S.Zero) : f.kind === 'I' || (f.kind === 'D' && f.s < 0) ? S.Zero : undefined),
  loggamma: (f) => (f.kind === 'R' && !f.c ? undefined : S.ComplexInfinity),
  erf: (f) => (f.kind === 'R' && f.c !== 0 ? Rational.of(f.s) : f.kind === 'I' && f.a ? S.ComplexInfinity : undefined),
  erfc: (f) => (f.kind === 'R' && f.c !== 0 ? (f.s > 0 ? S.Zero : S.Two) : f.kind === 'I' && f.a ? S.ComplexInfinity : undefined),
  erfi: (f) => (f.kind === 'R' && f.c ? S.ComplexInfinity : f.kind === 'I' && f.a !== 0 ? mul(f.t, S.I) : undefined),
  // Ei(z) = -E1(-z) + I*pi*sign(im(z)) and E1(w) -> 0 for re(w) -> oo or |im(w)| -> oo
  Ei: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : f.s > 0 ? S.ComplexInfinity : mul(f.c, S.I, S.Pi);
    if (f.kind === 'I' || (f.kind === 'D' && f.s < 0)) return mul(f.t, S.I, S.Pi);
    return undefined;
  },
  // |li(z)| ~ |z/log(z)| grows in every direction
  li: (f) => (f.kind === 'R' && !f.c && f.s > 0 ? undefined : S.ComplexInfinity),
  asin: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : add(halfPi(f.s), ooI(f.c));
    return f.kind === 'I' ? ooI(f.t) : S.ComplexInfinity;
  },
  acos: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : f.s > 0 ? ooI(-f.c) : add(S.Pi, ooI(-f.c));
    return f.kind === 'I' ? add(halfPi(1), ooI(-f.t)) : S.ComplexInfinity;
  },
  asinh: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : signedOo(f.s);
    if (f.kind === 'I') return !f.a ? undefined : add(signedOo(f.a), iHalfPi(f.t));
    return zooUnless(f, ['D']);
  },
  acosh: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : f.s > 0 ? S.Infinity : add(S.Infinity, mul(f.c, S.I, S.Pi));
    if (f.kind === 'I') return add(S.Infinity, iHalfPi(f.t));
    return zooUnless(f, ['D']);
  },
  atanh: (f) => (f.kind === 'R' ? (!f.c ? undefined : iHalfPi(f.c)) : f.kind === 'zoo' ? undefined : iHalfPi(f.t)),
  acoth: reciprocalLimit,
  // asech(z) = acosh(1/z) with 1/z -> 0 from the side opposite to z
  asech: (f) => (f.kind === 'R' ? (!f.c ? undefined : iHalfPi(-f.c)) : f.kind === 'zoo' ? undefined : iHalfPi(-f.t)),
  acsch: reciprocalLimit,
  atan: (f) => {
    if (f.kind === 'R') return !f.c ? undefined : halfPi(f.s);
    if (f.kind === 'I') return !f.a ? undefined : halfPi(f.a);
    return f.kind === 'D' ? halfPi(f.s) : undefined;
  },
  acot: reciprocalLimit,
  asec: (f) => (f.kind === 'zoo' ? undefined : halfPi(1)),
  acsc: reciprocalLimit,
  // arg and sign of a direction; arg of a D form has no limit: SymPy's values, arg(oo + oo*I) = pi/4,
  // arg(oo - oo*I) = -pi/4, arg(-oo + oo*I) = pi, arg(-oo - oo*I) = -3*pi/4 (SymPy arg(-1 + oo*I) = nan,
  // its limit pi/2 here)
  arg: (f) => {
    if (f.kind === 'zoo') return S.NaN;
    if (f.kind === 'D') return f.s > 0 ? mul(Rational.of(f.t, 4), S.Pi) : f.t > 0 ? S.Pi : mul(Rational.of(-3, 4), S.Pi);
    return f.kind === 'I' ? halfPi(f.t) : undefined;
  },
  sign: (f) => (f.kind === 'R' && f.c !== 0 ? Rational.of(f.s) : f.kind === 'I' ? mul(f.t, S.I) : undefined),
  // log(oo + oo*I): the modulus grows, the argument has no limit (SymPy keeps it, evalf gives nan)
  log: (f) => (f.kind === 'D' ? S.ComplexInfinity : undefined),
  re: (f) => (f.kind === 'zoo' ? S.NaN : undefined),
  im: (f) => (f.kind === 'zoo' ? S.NaN : undefined),
};

/**
 * Apply a named function with automatic evaluation; `{ evaluate: false }`
 * keeps the call as written (SymPy cos(pi/2 - x, evaluate=False)).
 *
 * @experimental May change in a minor release.
 */
export function fn(name: FnName, args: readonly ExprLike[], opts: { evaluate?: boolean } = {}): Expr {
  const xs = args.map(sympify);
  if (opts.evaluate === false) return new Fn(name, xs);
  const [x0, ...rest] = xs;
  if (x0 instanceof ExtensionExpr && x0.name === 'SetExpr' && rest.length === 0
    && ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(name)
    && 'applyfunc' in x0 && typeof x0.applyfunc === 'function') {
    const mapped: unknown = x0.applyfunc((value: Expr) => fn(name, [value]));
    return expectType(mapped, (value): value is Expr => value instanceof Expr, 'mapped set expression');
  }
  if (x0 !== undefined && rest.length === 0 && impl.accumBounds?.is(x0)) {
    const r = accumBoundsFunction(name, x0, (n, x) => fn(n, [x]));
    if (r !== undefined) return r;
  }
  // a number with an infinite part: the limit (or SymPy's value) before the evaluator, which may
  // rewrite it into a form without one (arg(oo + oo*I) = atan(nan))
  const lim = x0 !== undefined && rest.length === 0 ? INFINITE_LIMITS[name] : undefined;
  const form = lim && x0 !== undefined ? infiniteForm(x0) : undefined;
  const l = lim && form ? lim(form) : undefined;
  if (l !== undefined) return l;
  const ev = evaluators[name];
  const v = ev && x0 !== undefined ? ev(x0, ...rest) : undefined;
  if (v !== undefined) return v;
  const f = new Fn(name, xs);
  // SymPy Function.__new__: evaluate numerically when every argument is a Float
  // (a call without arguments has max(-1) = -1)
  const precs = xs.map(shouldEvalf);
  const maxPrec = Math.max(-1, ...precs);
  // (evalf does not throw: a function it cannot evaluate is returned unchanged)
  if (maxPrec > 0 && Math.min(...precs) > 0) return impl.evalf(f, precToDps(maxPrec));
  return f;
}

/** SymPy Function._should_evalf: the precision of a Float (or pure complex Float) argument, else -1. */
function shouldEvalf(a: Expr): number {
  if (a instanceof Float) return a.prec;
  if (!(a instanceof Add) || a.args.length !== 2) return -1;
  const [r, t] = a.args;
  // (pure_complex(1.0 + I) is (1.0, 1))
  const im = t === S.I ? S.One : t instanceof Mul && t.args.length === 2 && t.args[1] === S.I ? t.args[0] : undefined;
  if (r === undefined || !isNum(r) || im === undefined || !isNum(im)) return -1;
  return Math.max(r instanceof Float ? r.prec : -1, im instanceof Float ? im.prec : -1);
}

export const sin = (x: ExprLike): Expr => fn('sin', [x]);
export const cos = (x: ExprLike): Expr => fn('cos', [x]);
export const tan = (x: ExprLike): Expr => fn('tan', [x]);
export const asin = (x: ExprLike): Expr => fn('asin', [x]);
export const acos = (x: ExprLike): Expr => fn('acos', [x]);
export const atan = (x: ExprLike): Expr => fn('atan', [x]);
export const sinh = (x: ExprLike): Expr => fn('sinh', [x]);
export const cosh = (x: ExprLike): Expr => fn('cosh', [x]);
export const tanh = (x: ExprLike): Expr => fn('tanh', [x]);
/**
 * Natural logarithm, or log(x, base) = log(x)/log(base) like SymPy
 * (pulling out integer powers of a rational base first).
 */
export function log(x: ExprLike, base?: ExprLike): Expr {
  if (base === undefined) return fn('log', [x]);
  const b = sympify(base);
  const a = sympify(x);
  if (b instanceof Constant && b.name === 'E') return fn('log', [a]);
  if (b instanceof Rational && b.isOne) return a instanceof Rational && a.isOne ? S.NaN : S.ComplexInfinity;
  if (b instanceof Rational && b.isInteger && b.p > 1n && a instanceof Rational && !a.isZero) {
    const count = (v: bigint) => {
      let m = 0;
      let w = v < 0n ? -v : v;
      while (w % b.p === 0n) { w /= b.p; m++; }
      return m;
    };
    let m = count(a.p);
    if (m === 0) m = -count(a.q);
    if (m !== 0) return add(m, mul(fn('log', [mul(a, pow(b, -m))]), pow(fn('log', [b]), -1)));
  }
  return mul(fn('log', [a]), pow(fn('log', [b]), -1));
}
export const abs = (x: ExprLike): Expr => fn('abs', [x]);
export const re = (x: ExprLike): Expr => fn('re', [x]);
export const im = (x: ExprLike): Expr => fn('im', [x]);
export const arg = (x: ExprLike): Expr => fn('arg', [x]);

/**
 * Hermitian adjoint of a scalar is its conjugate.
 *
 * @experimental May change in a minor release.
 */
export const dagger = conjugate;

impl.conjugate = conjugate;
impl.fn = (name, args) => fn(name, args);
impl.abs = abs;
impl.cos = (e) => cos(e);
impl.sin = (e) => sin(e);

registerFunctionHeads([
  ['sin', sin],
  ['cos', cos],
  ['tan', tan],
  ['asin', asin],
  ['acos', acos],
  ['atan', atan],
  ['sinh', sinh],
  ['cosh', cosh],
  ['tanh', tanh],
  ['abs', abs],
  ['re', re],
  ['im', im],
  ['arg', arg],
  ['conjugate', conjugate],
  ['log', log],
]);
