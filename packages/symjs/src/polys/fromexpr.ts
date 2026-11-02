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
import { Poly, inferDomain } from './sympoly';

/** The options SymPy returns with a polynomial: generators and domain. */
export interface PolyOptions {
  gens: Expr[];
  domain: string;
}

/** SymPy poly_from_expr(expr, *gens): [Poly, { gens, domain }]. */
export function polyFromExpr(expr: ExprLike, gens: readonly Expr[] = [], opts: { domain?: string } = {}): [Poly, PolyOptions] {
  const p = Poly.from(expr, gens.length ? gens : undefined, opts);
  return [p, { gens: [...p.gens], domain: p.domain }];
}

/**
 * SymPy parallel_poly_from_expr(exprs, *gens): polynomials over common
 * generators and a common domain.
 */
export function parallelPolyFromExpr(exprs: readonly ExprLike[], gens: readonly Expr[] = [], opts: { domain?: string } = {}): [Poly[], PolyOptions] {
  const es = exprs.map((e) => sympify(e));
  // common generators: those of the polynomial of all expressions together
  const g = gens.length ? [...gens] : [...Poly.from(add(...es.map((e, i) => mul(e, new Dummy(`w${i}`)))), undefined).gens.filter((v) => !(v instanceof Dummy))];
  const first = es.map((e) => Poly.from(e, g, opts));
  const domain = opts.domain ?? inferDomain(first.flatMap((p) => p.coeffs()));
  const polys = first.map((p, i) => (p.domain === domain ? p : Poly.from(at(es, i), g, { domain })));
  return [polys, { gens: g, domain }];
}

/**
 * SymPy gff(f): the symbolic greatest factorial factorization is not
 * implemented in SymPy either (use Poly.gffList).
 */
export function gff(_f: ExprLike): never {
  throw new NotImplementedError('symbolic falling factorial');
}
