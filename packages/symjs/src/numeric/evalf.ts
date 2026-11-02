// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Numeric evaluation: evalf, toComplex and lambdify (compile to a closure).
 */

import {
  Add,
  BoolAtom,
  ComplexValue as C,
  Constant,
  Expr,
  ExtensionExpr,
  EvalfOptions,
  ExprLike,
  Float,
  Fn,
  Mul,
  NumericValues,
  Piecewise,
  Pow,
  Rational,
  Rel,
  Special,
  Sym,
  impl,
} from '../core/nodes';
import { mul, sympify } from '../core/ops';
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
import { type Mpc, evalAdaptive, fromMpc, setDoubleFallback } from './mpeval';

type Compiled = (env: readonly C[]) => C;

type Value = number | C | Expr;

const toC = (v: Value): C => (typeof v === 'number' ? c(v) : v instanceof Expr ? toComplex(v) : v);

/** Look up the raw value given for a symbol. Matches by name. */
function makeRawLookup(values: NumericValues | undefined): (s: Sym) => Value | undefined {
  if (!values) return () => undefined;
  if (values instanceof Map) {
    const byName = new Map<string, Value>();
    for (const [k, v] of values as ReadonlyMap<Expr | string, Value>) {
      byName.set(typeof k === 'string' ? k : k instanceof Sym ? k.name : k.key, v);
    }
    return (s) => byName.get(s.name);
  }
  const rec = values as Readonly<Record<string, Value>>;
  return (s) => (Object.prototype.hasOwnProperty.call(rec, s.name) ? rec[s.name]! : undefined);
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

/** Numeric implementations of functions (multi-argument); special.ts registers more. */
export const numericFns: Partial<Record<Fn['name'], (args: C[]) => C>> = Object.fromEntries(
  Object.entries(FN_NUMERIC1).map(([k, f]) => [k, (args: C[]) => f!(args[0]!)]),
);

const CONSTANT_VALUES: Record<string, C> = {
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
    const v = CONSTANT_VALUES[e.name]!;
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
    if (!op) throw new Error(`Cannot evaluate ${e.name} numerically`);
    return (env) => op(fas.map((f) => f(env)));
  }
  if (e instanceof Piecewise) {
    const branches = e.pairs.map(([x, cond]) => [compile(x, resolve), compileCond(cond, resolve)] as const);
    return (env) => {
      for (const [f, c] of branches) if (c(env)) return f(env);
      throw new RangeError('Piecewise: no condition is satisfied');
    };
  }
  throw new Error(`Cannot evaluate ${e.toString()}`);
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
  throw new Error(`Cannot evaluate condition ${e.toString()}`);
}

/** Evaluate to a complex number. All free symbols must be given values. */
export function toComplex(ex: ExprLike, values?: NumericValues): C {
  const e = sympify(ex);
  const lookup = makeLookup(values);
  const f = compile(e, (s) => {
    const v = lookup(s);
    if (v === undefined) throw new Error(`toComplex: no value for symbol '${s.name}'`);
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

/** evalf at a binary precision. */
export function evalfPrec(e: Expr, prec: number, values?: NumericValues, chop?: boolean | number): Expr {
  const raw = makeRawLookup(values);
  const lookup = (s: Sym): Mpc | undefined => {
    const v = raw(s);
    if (v === undefined) return undefined;
    if (typeof v === 'number') return [F.fromNumber(v), F.ZERO];
    if (v instanceof Expr) return evalAdaptive(v, prec, () => undefined);
    return [F.fromNumber(v.re), F.fromNumber(v.im)];
  };
  const go = (x: Expr): Expr => {
    let numeric = true;
    const visit = (y: Expr) => {
      if (y instanceof ExtensionExpr && y.numericValue(5) !== undefined) return;
      if (y instanceof Sym && lookup(y) === undefined) numeric = false;
      else if (y instanceof Special || y instanceof Rel || y instanceof BoolAtom) numeric = false;
      else y.args.forEach(visit);
    };
    visit(x);
    if (numeric) {
      try {
        return fromMpc(evalAdaptive(x, prec, lookup), prec, chop);
      } catch {
        // not numerically evaluable: fall through to the arguments
      }
    }
    if (x.args.length === 0) return x;
    // keep integer exponents exact (SymPy: (x**2).evalf() == x**2)
    if (x instanceof Pow && x.exp instanceof Rational && x.exp.isInteger) return rebuild(x, [go(x.base), x.exp]);
    if (x instanceof Mul && x.args[0] instanceof Rational && x.args[0].p === -1n && x.args[0].q === 1n) {
      return mul(-1, go(mul(...x.args.slice(1))));
    }
    return rebuild(x, x.args.map(go));
  };
  return go(e);
}

/**
 * Compile an expression into a fast numeric function of the given symbols.
 *
 * @example
 * const f = lambdify(cos(theta).mul(exp(I.mul(phi))), [theta, phi]);
 * f(0.1, 0.2) // => { re, im }
 */
export function lambdify(ex: ExprLike, params: readonly Sym[]): (...args: (number | C)[]) => C {
  const e = sympify(ex);
  const index = new Map(params.map((p, i) => [p.name, i]));
  const f = compile(e, (s) => {
    const i = index.get(s.name);
    if (i === undefined) throw new Error(`lambdify: symbol '${s.name}' is not a parameter`);
    return (env) => env[i]!;
  });
  return (...args) => {
    if (args.length !== params.length) {
      throw new RangeError(`lambdify: expected ${params.length} arguments, got ${args.length}`);
    }
    return f(args.map(toC));
  };
}

impl.evalf = evalf;

setDoubleFallback((name, args) => {
  const f = numericFns[name as Fn['name']];
  if (!f) return undefined;
  const r = f(args.map((a) => c(F.toNumber(a[0]), F.toNumber(a[1]))));
  if (!Number.isFinite(r.re) || !Number.isFinite(r.im)) throw new RangeError('non-finite');
  return [F.fromNumber(r.re), F.fromNumber(r.im)];
});

impl.toComplex = toComplex;
