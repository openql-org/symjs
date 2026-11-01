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
  ExprLike,
  Float,
  Fn,
  Mul,
  NumericValues,
  Piecewise,
  Pow,
  Rational,
  Rel,
  S,
  Special,
  Sym,
  impl,
} from '../core/nodes';
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

type Compiled = (env: readonly C[]) => C;

const toC = (v: number | C): C => (typeof v === 'number' ? c(v) : v);

/** Look up a numeric value for a symbol. Matches by name. */
function makeLookup(values: NumericValues | undefined): (s: Sym) => C | undefined {
  if (!values) return () => undefined;
  if (values instanceof Map) {
    const byName = new Map<string, C>();
    for (const [k, v] of values as ReadonlyMap<Expr | string, number | C>) {
      byName.set(typeof k === 'string' ? k : k instanceof Sym ? k.name : k.key, toC(v));
    }
    return (s) => byName.get(s.name);
  }
  const rec = values as Readonly<Record<string, number | C>>;
  return (s) => (Object.prototype.hasOwnProperty.call(rec, s.name) ? toC(rec[s.name]!) : undefined);
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

function fromComplex(v: C): Expr {
  if (Number.isNaN(v.re) || Number.isNaN(v.im)) return S.NaN;
  if (!Number.isFinite(v.im)) return S.ComplexInfinity;
  if (!Number.isFinite(v.re)) {
    if (v.im !== 0) return S.ComplexInfinity;
    return v.re > 0 ? S.Infinity : S.NegativeInfinity;
  }
  if (v.im === 0) return new Float(v.re);
  if (v.re === 0) return mul(new Float(v.im), S.I);
  return add(new Float(v.re), mul(new Float(v.im), S.I));
}

/** Numerically evaluate. Sub-expressions containing symbols without values stay symbolic. */
export function evalf(ex: ExprLike, values?: NumericValues): Expr {
  const e = sympify(ex);
  const lookup = makeLookup(values);
  const go = (x: Expr): Expr => {
    if (x instanceof Sym) {
      const v = lookup(x);
      return v === undefined ? x : fromComplex(v);
    }
    let numeric = true;
    const visit = (y: Expr) => {
      if (y instanceof Sym && lookup(y) === undefined) numeric = false;
      else y.args.forEach(visit);
    };
    visit(x);
    if (numeric) {
      return fromComplex(
        compile(x, (s) => {
          const v = lookup(s)!;
          return () => v;
        })([]),
      );
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
impl.toComplex = toComplex;
