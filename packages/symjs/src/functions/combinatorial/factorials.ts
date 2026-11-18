// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Rising and falling factorials of expressions and univariate polynomials. */
import type { ExprLike } from '../../core/nodes';
import { Expr, Rational, S, registerFunctionHeads } from '../../core/nodes';
import { pow, sympify } from '../../core/ops';
import type { Poly } from '../../polys/sympoly';
import { fn } from '../elementary/elementary';

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
