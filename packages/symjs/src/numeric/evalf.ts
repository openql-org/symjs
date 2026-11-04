// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Numeric evaluation: evalf, toComplex and lambdify (compile to a closure).
 */

import { DeferredVector } from '../core/classes';
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
import { EvalfValueError } from '../core/errors';
import { add, mul, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';
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
import { type Mpc, type MpPart, MpSpecialValue, evalAdaptive, fromMpc } from './mpeval';

type Compiled = (env: readonly C[]) => C;

type Value = number | C | Expr;

const toC = (v: Value): C => (typeof v === 'number' ? c(v) : v instanceof Expr ? toComplex(v) : v);

const isValueMap = (v: NumericValues): v is ReadonlyMap<Expr | string, Value> => v instanceof Map;

/** Look up the raw value given for a symbol. Matches by name. */
function makeRawLookup(values: NumericValues | undefined): (s: Sym) => Value | undefined {
  if (!values) return () => undefined;
  if (isValueMap(values)) {
    const byName = new Map<string, Value>();
    for (const [k, v] of values) {
      byName.set(typeof k === 'string' ? k : k instanceof Sym ? k.name : k.key, v);
    }
    return (s) => byName.get(s.name);
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
  return evalfPrec(e, dpsToPrec(dps), values, opts.chop);
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
export function evalfPrec(e: Expr, prec: number, values?: NumericValues, chop?: boolean | number): Expr {
  const raw = makeRawLookup(values);
  // an exact value is evaluated at the working precision, not the target one
  const lookup = (s: Sym, wp: number): Mpc | undefined => {
    const v = raw(s);
    if (v === undefined) return undefined;
    if (typeof v === 'number') return [F.fromNumber(v), F.ZERO];
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
      return fromMpc(evalAdaptive(x, prec, look), prec, chop);
    } catch (err) {
      // (SymPy raises the ValueError of mpmath)
      if (err instanceof EvalfValueError) throw err;
      // mpmath's inf and nan (SymPy _from_mpmath: Float._new(re) + Float._new(im)*I)
      if (err instanceof MpSpecialValue) return add(specialPart(err.re, prec), mul(specialPart(err.im, prec), S.I));
      // not numerically evaluable
      return undefined;
    }
  };
  /** SymPy _eval_evalf: the numeric parts evaluated, the others kept. */
  const go = (x: Expr): Expr => {
    const v = numeric(x, noValue);
    if (v !== undefined) return v;
    // SymPy Function._eval_evalf: a function that is not a number keeps its arguments
    // (f(1).evalf() == f(1), sin(x + 1).evalf() == sin(x + 1), exp(x + 1).evalf() == exp(x + 1))
    if (x.args.length === 0 || isFunction(x)) return x;
    // keep integer exponents exact (SymPy: (x**2).evalf() == x**2)
    if (x instanceof Pow && x.exp instanceof Rational && x.exp.isInteger) return rebuild(x, [go(x.base), x.exp]);
    if (x instanceof Mul && x.args[0] instanceof Rational && x.args[0].p === -1n && x.args[0].q === 1n) {
      return mul(-1, go(mul(...x.args.slice(1))));
    }
    if (x instanceof ExtensionExpr) {
      const own = x.evalfSelf(go, F.precToDps(prec));
      if (own !== undefined) return own;
    }
    // SymPy Sum._eval_evalf and Product._eval_evalf: a sum with finite limits is evaluated term by term
    if (x instanceof Concrete) {
      const v = impl.evalConcrete?.(x);
      if (v !== undefined) return go(v);
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
  const e2 = sub(e);
  if (e2 instanceof Special) return pole ? e : e2;
  if (e2 instanceof Add || e2 instanceof Mul || (e2 instanceof Pow && !isFunction(e2))) return go(e2);
  // a node that evaluates its parts itself (SymPy _eval_evalf: vectors evaluate their components)
  const own = e2 instanceof ExtensionExpr ? e2.evalfSelf(go, F.precToDps(prec)) : undefined;
  if (own !== undefined) return own;
  return numeric(e2, noValue) ?? e;
}

const isVector = (a: number | C | readonly (number | C)[]): a is readonly (number | C)[] => Array.isArray(a);

/**
 * Compile an expression into a fast numeric function of the given symbols.
 *
 * @example
 * const f = lambdify(cos(theta).mul(exp(I.mul(phi))), [theta, phi]);
 * f(0.1, 0.2) // => { re, im }
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

impl.toComplex = toComplex;
