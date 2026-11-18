// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Parts ported from SymPy (sympy/functions/combinatorial/factorials.py),
// Copyright (c) SymPy Development Team, BSD-3-Clause.

/** Rising and falling factorials of expressions and univariate polynomials. */
import type { ExprLike } from '../../core/nodes';
import { Expr, Rational, S, functionFactHandlers, registerFunctionHeads } from '../../core/nodes';
import { first, pair } from '../../core/guard';
import { Eq, Ge, Gt, piecewise } from '../../core/logic';
import { add, mul, pow, sqrt, sympify } from '../../core/ops';
import { isIntegerQ } from '../../core/assumptions';
import type { Poly } from '../../polys/sympoly';
import { fn } from '../elementary/elementary';
import { fnPartials } from '../../calculus/diff';

function factorialProduct(x: ExprLike | Poly, kIn: ExprLike, direction: 1 | -1): Expr | Poly {
  if (typeof x !== 'object' || x instanceof Expr) return fn(direction === 1 ? 'rf' : 'ff', [x, kIn]);
  const k = sympify(kIn);
  if (!(k instanceof Rational && k.isInteger)) throw new TypeError('polynomial factorial requires an integer order');
  if (k.isZero) return S.One;
  if (x.gens.length !== 1) throw new RangeError('polynomial factorial requires one generator');
  let product = x.mul(0).add(1);
  const count = k.isNegative ? -k.p : k.p;
  for (let i = 0n; i < count; i++) product = product.mul(x.shift(k.isNegative ? -BigInt(direction) * (i + 1n) : BigInt(direction) * i));
  return k.isNegative ? pow(product.asExpr(), -1) : product;
}

/** Falling factorial x*(x-1)*...; polynomial factors shift the generator. */
export function ff(x: ExprLike, k: ExprLike): Expr;
export function ff(x: ExprLike | Poly, k: ExprLike): Expr | Poly;
export function ff(x: ExprLike | Poly, k: ExprLike): Expr | Poly {
  return factorialProduct(x, k, -1);
}

/** Rising factorial x*(x+1)*...; polynomial factors shift the generator. */
export function rf(x: ExprLike, k: ExprLike): Expr;
export function rf(x: ExprLike | Poly, k: ExprLike): Expr | Poly;
export function rf(x: ExprLike | Poly, k: ExprLike): Expr | Poly {
  return factorialProduct(x, k, 1);
}

registerFunctionHeads([['ff', ff], ['rf', rf]]);

const factorial = (n: Expr): Expr => fn('factorial', [n]);
const gamma = (n: Expr): Expr => fn('gamma', [n]);
const neg = (n: Expr): Expr => mul(-1, n);
const div = (n: Expr, d: Expr): Expr => mul(n, pow(d, -1));

/** Rewrite a rising factorial using a quotient of factorials. */
function risingFactorials(args: readonly Expr[]): Expr | undefined {
  const [x, k] = pair(args);
  if (isIntegerQ(x) !== true || isIntegerQ(k) !== true) return undefined;
  return piecewise(
    [div(factorial(add(k, x, -1)), factorial(add(x, -1))), Gt(x, 0)],
    [mul(pow(-1, k), div(factorial(neg(x)), factorial(neg(add(k, x))))), true],
  );
}

/** Rewrite a falling factorial using gamma or factorial quotients. */
function fallingQuotient(
  args: readonly Expr[],
  useGamma: boolean,
): Expr | undefined {
  const [x, k] = pair(args);
  if (!useGamma && (isIntegerQ(x) !== true || isIntegerQ(k) !== true)) return undefined;
  const f = useGamma ? gamma : factorial;
  const shift = useGamma ? 1 : 0;
  return piecewise(
    [div(f(add(x, shift)), f(add(x, neg(k), shift))), Ge(x, 0)],
    [mul(pow(-1, k), div(f(add(k, neg(x), shift - 1)), f(add(neg(x), shift - 1)))), true],
  );
}

/** Combinatorial rewrites of the factorial family. */
export const factorialRewrites = {
  RisingFactorial: {
    FallingFactorial: (args: readonly Expr[]): Expr => {
      const [x, k] = pair(args);
      return ff(add(x, k, -1), k);
    },
    factorial: risingFactorials,
    binomial: (args: readonly Expr[]): Expr | undefined => {
      const [x, k] = pair(args);
      return isIntegerQ(k) === true ? mul(factorial(k), fn('binomial', [add(x, k, -1), k])) : undefined;
    },
  },
  FallingFactorial: {
    RisingFactorial: (args: readonly Expr[]): Expr => {
      const [x, k] = pair(args);
      return rf(add(x, neg(k), 1), k);
    },
    gamma: (args: readonly Expr[]): Expr | undefined => fallingQuotient(args, true),
    factorial: (args: readonly Expr[]): Expr | undefined => fallingQuotient(args, false),
    binomial: (args: readonly Expr[]): Expr | undefined => {
      const [x, k] = pair(args);
      return isIntegerQ(k) === true ? mul(factorial(k), fn('binomial', [x, k])) : undefined;
    },
  },
  subfactorial: {
    uppergamma: (args: readonly Expr[]): Expr => div(fn('uppergamma', [add(first(args), 1), -1]), S.E),
  },
};

/** Rewrite a double factorial using gamma and the parity of its argument. */
export function factorial2Gamma(n: Expr, parity: Expr): Expr {
  const half = mul(n, S.Half);
  return mul(pow(2, half), gamma(add(half, 1)), piecewise(
    [S.One, Eq(parity, 0)], [div(sqrt(2), sqrt(S.Pi)), Eq(parity, 1)],
  ));
}

fnPartials['binomial'] = (args, i) => {
  const [n, k] = pair(args);
  const psi = (z: Expr): Expr => fn('polygamma', [0, add(z, 1)]);
  const gap = psi(add(n, neg(k)));
  const difference = i === 0 ? add(psi(n), neg(gap)) : add(gap, neg(psi(k)));
  return mul(fn('binomial', [n, k]), difference);
};

for (const name of ['factorial', 'factorial2', 'rf', 'ff', 'binomial', 'subfactorial'] as const) {
  functionFactHandlers[name] = (fact, args, query) => {
    const n = first(args);
    const q = (p: string, a = n) => query(p, a);
    const integer = q('integer');
    const nonnegative = q('nonnegative');
    if (name === 'rf' || name === 'ff' || name === 'binomial') {
      if (fact !== 'integer' && fact !== 'nonnegative') return undefined;
      const [, k] = pair(args);
      const orderInteger = q('integer', k);
      if (name === 'binomial') {
        if (fact === 'integer') {
          if (q('zero', k) === true || (integer === true && orderInteger === true)) return true;
          return integer === true && nonnegative === false && orderInteger === false ? false : undefined;
        }
        if (integer !== true || orderInteger !== true) return undefined;
        if (nonnegative === true || q('negative', k) === true || q('even', k) === true) return true;
        return nonnegative === false && q('positive', k) === true && q('odd', k) === true ? false : undefined;
      }
      if (fact !== 'integer') return undefined;
      if (q('zero', k) === true) return true;
      if (orderInteger === false && (name === 'ff' || nonnegative === true)) return false;
      return integer === true && orderInteger === true && q('nonnegative', k) === true ? true : undefined;
    }
    if (name === 'factorial2') {
      if (integer !== true) return undefined;
      if ((fact === 'integer' || fact === 'positive') && q('nonnegative', add(n, 1)) === true) return true;
      if (q('odd') === true) {
        if (fact === 'even') return false;
        if (fact === 'integer' || fact === 'odd') return q('nonnegative', add(n, 3));
        if (fact === 'positive') {
          if (q('nonnegative', add(n, 2)) === true) return true;
          return q('even', mul(S.Half, add(n, 1)));
        }
      }
      if ((fact === 'even' || fact === 'odd') && q('even') === true) {
        if (q('positive') === true) return fact === 'even';
        if (q('zero') === true) return fact === 'odd';
      }
      return undefined;
    }
    if (name === 'factorial' && fact === 'real') {
      if (nonnegative === true || q('noninteger') === true) return true;
    }
    if (integer !== true || nonnegative !== true) return undefined;
    if (fact === 'integer') return true;
    if (name === 'subfactorial') {
      if (fact === 'nonnegative') return true;
      if (fact === 'even' && q('odd') === true) return true;
      if (fact === 'odd' && q('even') === true) return true;
    } else {
      if (fact === 'positive') return true;
      if (fact === 'even') return q('nonnegative', add(n, -2));
      if (fact === 'composite') return q('nonnegative', add(n, -3));
    }
    return undefined;
  };
}
