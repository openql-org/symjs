// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy poly_from_expr / parallel_poly_from_expr (polynomials with
 * the options they were built with) and gff.
 */

import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Dummy } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { Poly, PolificationFailed, inferDomain } from './sympoly';

/** The options SymPy returns with a polynomial: generators and domain. */
export interface PolyOptions {
  /** The ordered generators. */
  gens: Expr[];
  /** The coefficient domain. */
  domain: string;
}

/**
 * Converts an expression to a polynomial and determines its generators and coefficient domain.
 *
 * @param expr - Expression to convert.
 * @param gens - Polynomial generators in the desired order.
 * @param opts - Controls `domain` (the coefficient domain).
 * @returns The polynomial and resolved options.
 * @see SymPy `sympy.polys.polytools.poly_from_expr`
 */
export function polyFromExpr(expr: ExprLike, gens: readonly Expr[] = [], opts: { domain?: string } = {}): [Poly, PolyOptions] {
  const p = Poly.from(expr, gens.length ? gens : undefined, opts);
  return [p, { gens: [...p.gens], domain: p.domain }];
}

/**
 * Converts several expressions using shared generators and a single coefficient domain.
 *
 * @param exprs - Expressions to convert, with a common generator order.
 * @param gens - Polynomial generators in the desired order.
 * @param opts - Controls `domain` (the coefficient domain).
 * @returns The polynomial list and resolved options.
 * @throws PolificationFailed when the input cannot be converted to polynomial form.
 * @see SymPy `sympy.polys.polytools.parallel_poly_from_expr`
 */
export function parallelPolyFromExpr(exprs: readonly ExprLike[], gens: readonly Expr[] = [], opts: { domain?: string } = {}): [Poly[], PolyOptions] {
  const es = exprs.map((e) => sympify(e));
  // common generators: those of the polynomial of all expressions together
  const g = gens.length ? [...gens] : [...Poly.from(add(...es.map((e, i) => mul(e, new Dummy(`w${i}`)))), undefined).gens.filter((v) => !(v instanceof Dummy))];
  if (!g.length) throw new PolificationFailed('polynomial generators are required');
  const first = es.map((e) => Poly.from(e, g, opts));
  const domain = opts.domain ?? inferDomain(first.flatMap((p) => p.coeffs()));
  const polys = first.map((p, i) => (p.domain === domain ? p : Poly.from(at(es, i), g, { domain })));
  return [polys, { gens: g, domain }];
}

/**
 * The symbolic greatest factorial factorization is not
 * implemented in SymPy either (use Poly.gffList).
 *
 * @param _f - Polynomial to operate on.
 * @throws NotImplementedError when the falling factorial cannot be evaluated symbolically.
 * @see SymPy `sympy.polys.polytools.gff`
 */
export function gff(_f: ExprLike): never {
  throw new NotImplementedError('symbolic falling factorial');
}
