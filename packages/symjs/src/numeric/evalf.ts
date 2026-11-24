// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Numeric evaluation: evalf, toComplex and lambdify (compile to a closure).
 */

import { DeferredVector } from '../core/classes';
import { isReal, isZero } from '../core/assumptions';
import type {
  ComplexValue as C,
  ConstantName,
  EvalfOptions,
  ExprLike,
  NumericValues } from '../core/nodes';
import {
  Add,
  BoolAtom,
  Constant,
  Expr,
  ExtensionExpr,
  Float,
  Fn,
  Integral,
  Mul,
  Piecewise,
  Pow,
  Rational,
  Rel,
  S,
  Special,
  Sym,
  UndefFn,
  impl,
} from '../core/nodes';
import { at } from '../core/guard';
import { Concrete } from '../core/concrete';
import { PrecisionExhausted, EvalfValueError } from '../core/errors';
import { add, mul, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';

import {
  c,
  cabs,
  cacos,
  cadd,
  carg,
  casin,
  catan,
  cconj,
  ccos,
  ccosh,
  cexp,
  clog,
  cmul,
  cpow,
  csin,
  csinh,
  ctan,
  ctanh,
} from './complex';
import * as F from './mpf';
import { dpsToPrec } from './mpf';
import { type Mpc, type MpPart, MpSpecialValue, evalAdaptive, evalMp, fromMpc } from './mpeval';
import { asRealImag } from '../core/methods';
import { fn } from '../functions/elementary/elementary';
import { fromInt } from './mpf';
import type { Mpf } from './mpf';

/** SymPy is_comparable: a real numerical value whose evalf(2) has precision. */
export function isComparable(ex: ExprLike): boolean {
  const e = sympify(ex);
  if (!e.isNumber) return false;
  // SymPy uses precision 1 for a Float with no significant bits; evaluating
  // that stored approximation at more digits cannot restore its accuracy.
  if (e instanceof Float) return e.prec > 1;
  if (e instanceof Special) return e.name === 'oo' || e.name === '-oo';
  const accuracy = { re: 1, im: 1 };
  try {
    const hasLimits = (x: Expr): boolean => x instanceof Integral || x instanceof Concrete || x.args.some(hasLimits);
    const numerical = hasLimits(e) ? impl.doit?.(e) ?? e : e;
    const [, im] = evalAdaptive(numerical, dpsToPrec(2), undefined, accuracy);
    return F.isZero(im) && accuracy.re > 1 && (isReal(e) === true || accuracy.im > 1);
  } catch {
    return false;
  }
}

/** SymPy pure_complex: a + I*b with numeric atoms a and b, or NoMatch. */
export function pureComplex(v: ExprLike, orReal = false): [Expr, Expr] | NoMatchResult {
  const e = sympify(v);
  const terms = e instanceof Add ? e.args : [e];
  let real: Expr = S.Zero, imaginary: Expr = S.Zero;
  for (const term of terms) {
    if (term instanceof Rational || term instanceof Float) real = add(real, term);
    else if (term.equals(S.I)) imaginary = add(imaginary, S.One);
    else if (term instanceof Mul && term.args.length === 2) {
      const coefficient = at(term.args, 0);
      if (!(coefficient instanceof Rational || coefficient instanceof Float) || !at(term.args, 1).equals(S.I)) return NoMatch;
      imaginary = add(imaginary, coefficient);
    } else return NoMatch;
  }
  return !imaginary.equals(S.Zero) || orReal ? [real, imaginary] : NoMatch;
}

/** SymPy's raw mpf representation: sign, mantissa, exponent, bit count. */
export type RawMpfTuple = readonly [number, number, number, number];
/** A scaled zero wraps the sign to distinguish it from an ordinary mpf value. */
export type ScaledZero = readonly [readonly [number], number, number, number];

/** SymPy scaled_zero: encode a magnitude with unknown precision, or unwrap its sign. */
export function scaledZero(mag: number, sign?: number): [ScaledZero, -1];
export function scaledZero(mag: ScaledZero): RawMpfTuple;
export function scaledZero(mag: number | ScaledZero, sign = 1): RawMpfTuple | [ScaledZero, -1] {
  if (typeof mag !== 'number') return [mag[0][0], mag[1], mag[2], mag[3]];
  if (!Number.isSafeInteger(mag)) throw new RangeError('scaledZero expects an integer magnitude');
  if (sign !== 1 && sign !== -1) throw new RangeError('scaledZero sign must be +/-1');
  return [[[sign === 1 ? 0 : 1], 1, mag, 1], -1];
}

type Compiled = (env: readonly C[]) => C;

type Value = number | C | Expr;

const toC = (v: Value): C => (typeof v === 'number' ? c(v) : v instanceof Expr ? toComplex(v) : v);

const isValueMap = (v: NumericValues): v is ReadonlyMap<Expr | string, Value> => v instanceof Map;

/** Look up the raw value given for a symbol. Matches by name. */
function makeRawLookup(values: NumericValues | undefined): (s: Sym) => Value | undefined {
  if (!values) return () => undefined;
  if (isValueMap(values)) {
    const byKey = new Map<string, Value>();
    for (const [k, v] of values) {
      if (typeof k !== 'string') byKey.set(k.key, v);
    }
    return (s) => byKey.get(s.key) ?? values.get(s.name);
  }
  return (s) => (Object.prototype.hasOwnProperty.call(values, s.name) ? values[s.name] : undefined);
}

/** Look up a numeric value for a symbol. Matches by name. */
function makeLookup(values: NumericValues | undefined): (s: Sym) => C | undefined {
  const raw = makeRawLookup(values);
  return (s) => {
    const v = raw(s);
    return v === undefined ? undefined : toC(v);
  };
}

const FN_NUMERIC1: Partial<Record<Fn['name'], (a: C) => C>> = {
  sin: csin,
  cos: ccos,
  tan: ctan,
  asin: casin,
  acos: cacos,
  atan: catan,
  sinh: csinh,
  cosh: ccosh,
  tanh: ctanh,
  log: clog,
  abs: (a) => c(cabs(a)),
  re: (a) => c(a.re),
  im: (a) => c(a.im),
  arg: (a) => c(carg(a)),
  conjugate: cconj,
};

/** Numeric implementations of functions (multi-argument); functions/special/special.ts registers more. */
export const numericFns: Partial<Record<Fn['name'], (args: C[]) => C>> = Object.fromEntries(
  Object.entries(FN_NUMERIC1).map(([k, f]) => [k, (args: C[]) => f(at(args, 0))]),
);

/** Numeric implementations of extension nodes by node name (the C functions of codegen/cfunctions.ts register theirs). */
export const numericExtensions: Partial<Record<string, (args: C[]) => C>> = {};

const CONSTANT_VALUES: Record<ConstantName, C> = {
  pi: c(Math.PI),
  E: c(Math.E),
  I: c(0, 1),
  EulerGamma: c(0.5772156649015329),
  Catalan: c(0.915965594177219),
  GoldenRatio: c((1 + Math.sqrt(5)) / 2),
  TribonacciConstant: c(1.8392867552141612),
};

function compile(e: Expr, resolve: (s: Sym) => Compiled): Compiled {
  if (e instanceof Rational) {
    const v = c(e.value);
    return () => v;
  }
  if (e instanceof Float) {
    const v = c(e.value);
    return () => v;
  }
  if (e instanceof Constant) {
    const v = CONSTANT_VALUES[e.name];
    return () => v;
  }
  if (e instanceof Special) {
    const v = { oo: c(Infinity), '-oo': c(-Infinity), zoo: c(Infinity, Infinity), nan: c(NaN) }[e.name];
    return () => v;
  }
  if (e instanceof Concrete) {
    const value = impl.evalConcrete?.(e);
    if (value !== undefined) return compile(value, resolve);
  }
  if (e instanceof Sym) return resolve(e);
  if (e instanceof Add) {
    const fs = e.args.map((a) => compile(a, resolve));
    return (env) => fs.reduce((acc, f) => cadd(acc, f(env)), c(0));
  }
  if (e instanceof Mul) {
    const fs = e.args.map((a) => compile(a, resolve));
    return (env) => fs.reduce((acc, f) => cmul(acc, f(env)), c(1));
  }
  if (e instanceof Pow) {
    const fx = compile(e.exp, resolve);
    if (e.base instanceof Constant && e.base.name === 'E') return (env) => cexp(fx(env));
    const fb = compile(e.base, resolve);
    return (env) => cpow(fb(env), fx(env));
  }
  if (e instanceof Fn) {
    const fas = e.args.map((a) => compile(a, resolve));
    const op = numericFns[e.name];
    if (!op) throw new TypeError(`Cannot evaluate ${e.name} numerically`);
    return (env) => op(fas.map((f) => f(env)));
  }
  const extension = e instanceof ExtensionExpr ? numericExtensions[e.name] : undefined;
  if (extension) {
    const op = extension;
    const fas = e.args.map((a) => compile(a, resolve));
    return (env) => op(fas.map((f) => f(env)));
  }
  if (e instanceof Piecewise) {
    const branches = e.pairs.map(([x, cond]) => [compile(x, resolve), compileCond(cond, resolve)] as const);
    return (env) => {
      for (const [f, c] of branches) if (c(env)) return f(env);
      throw new RangeError('Piecewise: no condition is satisfied');
    };
  }
  throw new TypeError(`Cannot evaluate ${e.toString()}`);
}

function compileCond(e: Expr, resolve: (s: Sym) => Compiled): (env: readonly C[]) => boolean {
  if (e instanceof BoolAtom) return () => e.value;
  if (e instanceof Rel) {
    const a = compile(e.lhs, resolve);
    const b = compile(e.rhs, resolve);
    const tol = 1e-12;
    return (env) => {
      const x = a(env);
      const y = b(env);
      const eq = Math.abs(x.re - y.re) <= tol && Math.abs(x.im - y.im) <= tol;
      switch (e.op) {
        case 'Eq':
          return eq;
        case 'Ne':
          return !eq;
        case 'Lt':
          return x.re < y.re;
        case 'Le':
          return x.re <= y.re;
        case 'Gt':
          return x.re > y.re;
        case 'Ge':
          return x.re >= y.re;
      }
    };
  }
  throw new TypeError(`Cannot evaluate condition ${e.toString()}`);
}

/**
 * Evaluate to a complex number. All free symbols must be given values.
 *
 * @experimental May change in a minor release.
 */
export function toComplex(ex: ExprLike, values?: NumericValues): C {
  const e = sympify(ex);
  const lookup = makeLookup(values);
  const f = compile(e, (s) => {
    const v = lookup(s);
    if (v === undefined) throw new TypeError(`toComplex: no value for symbol '${s.name}'`);
    return () => v;
  });
  return f([]);
}

/** Numerically evaluate. Sub-expressions containing symbols without values stay symbolic. */
export function evalf(ex: ExprLike, n?: number | NumericValues, opts: EvalfOptions = {}): Expr {
  const e = sympify(ex);
  let dps = 15;
  let values = opts.subs;
  if (typeof n === 'number') dps = n;
  else if (n !== undefined) values = n;
  return evalfPrec(e, dpsToPrec(dps), values, opts.chop, opts);
}

/** A function application (exp is a power of E here, a function in SymPy). */
const isFunction = (x: Expr): boolean => x instanceof Fn || x instanceof UndefFn || (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E');

/** A single argument that is the number zero. */
const isZeroNumber = (args: readonly Expr[]): boolean => {
  const a = args[0];
  return args.length === 1 && (a instanceof Rational || a instanceof Float) && a.isZero;
};

/** SymPy Float._new of an mpmath component: finf -> oo, fninf -> -oo, fnan -> nan, zero -> 0. */
function specialPart(p: MpPart, prec: number): Expr {
  if (p === 'inf') return S.Infinity;
  if (p === '-inf') return S.NegativeInfinity;
  if (p === 'nan') return S.NaN;
  return F.isZero(p) ? S.Zero : new Float(p, prec);
}

/** evalf at a binary precision. */
export function evalfPrec(e: Expr, prec: number, values?: NumericValues, chop?: boolean | number, options: Pick<EvalfOptions, 'maxn' | 'strict'> = {}): Expr {
  const maxPrec = options.maxn === undefined ? Infinity : dpsToPrec(options.maxn);
  const raw = makeRawLookup(values);
  // an exact value is evaluated at the working precision, not the target one
  const lookup = (s: Sym, wp: number): Mpc | undefined => {
    const v = raw(s);
    if (v === undefined) return undefined;
    if (typeof v === 'number') return [F.fromNumber(v), F.ZERO];
    if (v instanceof Special) return undefined;
    if (v instanceof Expr) return evalAdaptive(v, wp);
    return [F.fromNumber(v.re), F.fromNumber(v.im)];
  };
  const noValue = (): Mpc | undefined => undefined;
  /** The value of x when it is a number (every symbol having a value), or undefined. */
  const numeric = (x: Expr, look: (s: Sym, wp: number) => Mpc | undefined): Expr | undefined => {
    let ok = true as boolean; // set inside visit
    const visit = (y: Expr) => {
      if (y instanceof ExtensionExpr && y.numericValue(5) !== undefined) return;
      if (y instanceof Sym && look(y, prec) === undefined) ok = false;
      else if ((y instanceof Special && y.name === 'zoo') || y instanceof Rel || y instanceof BoolAtom) ok = false;
      else y.args.forEach(visit);
    };
    visit(x);
    if (!ok) return undefined;
    try {
      const accuracy = options.strict === true ? { re: prec, im: prec } : undefined;
      const parts = evalAdaptive(x, prec, look, accuracy, maxPrec);
      const result = fromMpc(parts, prec, chop);
      if (accuracy !== undefined && chop !== true &&
          (complexAccuracy([...parts, accuracy.re, accuracy.im]) < prec ||
           result === S.Zero && Math.min(accuracy.re, accuracy.im) < prec)) {
        throw new PrecisionExhausted('could not achieve the requested accuracy');
      }
      return result;
    } catch (err) {
      // (SymPy raises the ValueError of mpmath)
      if (err instanceof EvalfValueError || err instanceof PrecisionExhausted) throw err;
      // mpmath's inf and nan (SymPy _from_mpmath: Float._new(re) + Float._new(im)*I)
      if (err instanceof MpSpecialValue) return add(specialPart(err.re, prec), mul(specialPart(err.im, prec), S.I));
      // not numerically evaluable
      return undefined;
    }
  };
  /** SymPy _eval_evalf: the numeric parts evaluated, the others kept. */
  const go = (x: Expr): Expr => {
    if (x instanceof Integral && isZero(x.integrand) === true) return S.Zero;
    const v = numeric(x, noValue);
    if (v !== undefined) return v;
    // SymPy Function._eval_evalf: a function that is not a number keeps its arguments
    // (f(1).evalf() == f(1), sin(x + 1).evalf() == sin(x + 1), exp(x + 1).evalf() == exp(x + 1))
    if (x.args.length === 0 || isFunction(x)) return x;
    if (x instanceof Piecewise) return rebuild(x, x.pairs.flatMap(([value, condition]) => [go(value), condition]));
    // keep integer exponents exact (SymPy: (x**2).evalf() == x**2)
    if (x instanceof Pow && x.exp instanceof Rational && x.exp.isInteger) return rebuild(x, [go(x.base), x.exp]);
    if (x instanceof Mul && x.args[0] instanceof Rational && x.args[0].p === -1n && x.args[0].q === 1n) {
      return mul(-1, go(mul(...x.args.slice(1))));
    }
    if (x instanceof ExtensionExpr) {
      const own = x.evalfSelf(go, F.precToDps(prec));
      if (own !== undefined) return own;
    }
    if (x instanceof Integral && x.limits && (x.limits[0].equals(x.limits[1]) || !x.integrand.has(x.variable))) {
      const [a, b] = x.limits;
      return go(a.equals(b) ? S.Zero : mul(x.integrand, add(b, mul(-1, a))));
    }
    // SymPy Sum._eval_evalf and Product._eval_evalf: a sum with finite limits is evaluated term by term
    if (x instanceof Concrete) {
      const v = impl.evalConcrete?.(x);
      if (v !== undefined) return go(v);
    }
    if (x instanceof Integral && x.args.length === 4 && x.freeSymbols().size === 0) {
      const value = impl.doit?.(x);
      const result = value === undefined ? undefined : numeric(value, noValue);
      if (result !== undefined) return result;
    }
    return rebuild(x, x.args.map(go));
  };
  if (values === undefined) return go(e);
  const v = numeric(e, lookup);
  if (v !== undefined) return v;
  // SymPy evalf(subs=...) when the value is not a number: the expression with the values
  // substituted is evaluated part by part when it is a sum, product or power; otherwise the
  // expression is returned unchanged (yn(0, x).evalf(subs={x: 0}) == yn(0, x))
  let pole = false as boolean; // set inside sub
  const sub = (x: Expr): Expr => {
    if (x instanceof Sym) {
      const r = raw(x);
      return r === undefined ? x : typeof r === 'number' || r instanceof Expr ? sympify(r) : sympify(r.re).add(sympify(r.im).mul(S.I));
    }
    if (x.args.length === 0) return x;
    const args = x.args.map(sub);
    if (args.every((a, i) => a === x.args[i])) return x;
    // the mpmath value of log(0) is -oo (SymPy log(x).evalf(subs={x: 0}) == -oo)
    if (x instanceof Fn && x.name === 'log' && isZeroNumber(args)) return S.NegativeInfinity;
    const r = rebuild(x, args);
    if (x instanceof Fn && r instanceof Special && !args.some((a) => a instanceof Special)) pole = true;
    return r;
  };
  if (e instanceof Concrete) {
    const replacements = [...e.freeSymbols()].filter(s => s instanceof Sym).map(s => [s, sub(s)] as const);
    return go(e.subs(replacements));
  }
  const e2 = sub(e);
  if (e2 instanceof Special) return pole ? e : e2;
  if (e2.kind === 'Set') return go(e2);
  if (e2 instanceof Add || e2 instanceof Mul || (e2 instanceof Pow && !isFunction(e2))) return go(e2);
  // a node that evaluates its parts itself (SymPy _eval_evalf: vectors evaluate their components)
  const own = e2 instanceof ExtensionExpr ? e2.evalfSelf(go, F.precToDps(prec)) : undefined;
  if (own !== undefined) return own;
  return numeric(e2, noValue) ?? e;
}

const isVector = (a: number | C | readonly (number | C)[]): a is readonly (number | C)[] => Array.isArray(a);

/**
 * Compiles an expression into a fast numeric function of the given symbols.
 * The function takes numbers or complex values `{ re, im }` and returns a
 * complex value `{ re, im }` in double precision.
 *
 * @param ex - The expression.
 * @param params - The symbols, in the order of the arguments of the function.
 * @returns The numeric function.
 * @see SymPy `sympy.utilities.lambdify.lambdify`
 * @example
 * ```ts
 * import { ex, lambdify, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * const f = lambdify(ex`sin(x) + y`, [x, y]);
 * f(0, 2).re; // => 2
 * lambdify(ex`exp(I*x)`, [x])(Math.PI).re; // => -1
 * ```
 */
export function lambdify(ex: ExprLike, params: readonly Sym[]): (...args: (number | C | readonly (number | C)[])[]) => C {
  const e = sympify(ex);
  const index = new Map(params.map((p, i) => [p.name, i]));
  // a DeferredVector parameter X takes an array; the symbol X[k] is its k-th entry
  const vectors = new Map(params.flatMap((p, i) => (p instanceof DeferredVector ? [[p.name, i] as const] : [])));
  const slots: [number, number][] = [];
  const f = compile(e, (s) => {
    const m = /^(.*)\[(\d+)\]$/.exec(s.name);
    if (m) {
      const [, base = '', k = ''] = m;
      const vi = vectors.get(base);
      if (vi !== undefined) {
        const slot = params.length + slots.length;
        slots.push([vi, Number(k)]);
        return (env) => at(env, slot);
      }
    }
    const i = index.get(s.name);
    if (i === undefined) throw new TypeError(`lambdify: symbol '${s.name}' is not a parameter`);
    return (env) => at(env, i);
  });
  return (...args) => {
    if (args.length !== params.length) {
      throw new RangeError(`lambdify: expected ${params.length} arguments, got ${args.length}`);
    }
    const env = args.map((a) => (isVector(a) ? toC(0) : toC(a)));
    for (const [i, k] of slots) {
      const v = args[i];
      if (v === undefined || !isVector(v) || k >= v.length) throw new RangeError(`lambdify: ${at(params, i).name}[${k}] is not given`);
      env.push(toC(at(v, k)));
    }
    return f(env);
  };
}

impl.evalf = evalf;
impl.isComparable = isComparable;

impl.toComplex = toComplex;

export type EvalfResult = readonly [Mpf, Mpf, number, number];

type RawPart = Mpf | NoMatchResult;
type RawAccuracy = number | NoMatchResult;
export type RawEvalfResult = readonly [RawPart, RawPart, RawAccuracy, RawAccuracy];

/** Evaluate a closed number at binary precision and preserve its component accuracies. */
export function evalfRaw(expression: ExprLike, precision: number): RawEvalfResult | NoMatchResult {
  const e = sympify(expression);
  if (!Number.isSafeInteger(precision) || precision < 1) throw new RangeError('precision must be a positive integer');
  if (isZero(e) === true || e instanceof Concrete && isZero(e.function) === true) return [NoMatch, NoMatch, precision, NoMatch];
  const accuracy = { re: precision, im: precision };
  try {
    const [real, imaginary] = evalAdaptive(e, precision, undefined, accuracy);
    if (!(e instanceof Add)) return rawParts(real, imaginary, accuracy.re, accuracy.im);
    // As in evalf_add, retain the relative precision before rounding the reported value.
    const working = precision + 10;
    const terms = e.args.map((term) => evalMp(term, working));
    const estimate = (index: 0 | 1, value: Mpf, fallback: number): number => {
      const parts = terms.map((term) => term[index]).filter((term) => !F.isZero(term));
      if (parts.length < 2 || F.isZero(value)) return fallback;
      const sum = parts.reduce((total, term) => F.add(total, term, working), F.ZERO);
      return Math.min(Math.max(F.mag(sum) + working - Math.max(...parts.map(F.mag)), 1), working + 1);
    };
    return rawParts(real, imaginary, estimate(0, real, accuracy.re), estimate(1, imaginary, accuracy.im));
  } catch {
    return NoMatch;
  }
}

function rawParts(real: Mpf, imaginary: Mpf, realAccuracy: number, imaginaryAccuracy: number): RawEvalfResult {
  const r = F.isZero(real);
  const i = F.isZero(imaginary);
  return [r ? NoMatch : real, i ? NoMatch : imaginary, r && !i ? NoMatch : realAccuracy, i ? NoMatch : imaginaryAccuracy];
}

/** Relative accuracy in bits, using SymPy's maximum-norm error estimate. */
export function complexAccuracy(result: EvalfResult | Expr): number {
  if (result === S.ComplexInfinity) return Infinity;
  if (result instanceof Expr) throw new TypeError('expected an evalf result');
  const [re, im, reAccuracy, imAccuracy] = result;
  if (im.man === 0n) return re.man === 0n ? Infinity : reAccuracy;
  if (re.man === 0n) return imAccuracy;
  const size = (x: Mpf): number => Number(x.exp) + (x.man < 0n ? -x.man : x.man).toString(2).length;
  const reSize = size(re), imSize = size(im);
  return Math.max(reSize, imSize) - Math.max(reSize - reAccuracy, imSize - imAccuracy);
}

/** Exact floor/ceiling of the real and imaginary parts; unresolved parts signal failure. */
export function getIntegerPart(expr: Expr, direction: 1 | -1, options: ReadonlyMap<string, unknown> = new Map(), returnInts = false): readonly [bigint, bigint] | readonly [Mpf | NoMatchResult, Mpf | NoMatchResult, number | NoMatchResult, number | NoMatchResult] {
  if (expr === S.ComplexInfinity) throw new RangeError('Cannot get integer part of Complex Infinity');
  if (options.size !== 0) throw new RangeError('unsupported integer-part options');
  const round = (part: Expr): bigint => {
    const value = fn(direction === 1 ? 'ceiling' : 'floor', [part]);
    if (!(value instanceof Rational) || value.q !== 1n) throw new RangeError('Cannot determine exact integer part');
    return value.p;
  };
  const [real, imag] = asRealImag(expr);
  const re = round(real), im = round(imag);
  if (returnInts) return [re, im];
  const mpf = (man: bigint): Mpf | NoMatchResult => man === 0n ? NoMatch : fromInt(man);
  return [mpf(re), mpf(im), re === 0n ? NoMatch : Infinity, im === 0n ? NoMatch : Infinity];
}
