// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/integrals.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.integrals: ParametricIntegral, the integral of a
 * scalar or vector field over a parametric region (line, surface and volume
 * integrals), and vector_integrate, the integral over a region (parametric,
 * implicit or geometric) or with respect to base scalars.
 */

import { Expr, ExtensionExpr, Integral, S, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { atoms } from '../core/methods';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import { Matrix } from '../matrices/matrix';
import { jacobian } from '../matrices/linalg';
import { topologicalSort } from '../utilities/iterables';
import { GeometryEntity } from '../geometry/entity';
import type { ExprMap } from '../core/exprmap';
import { Vector, coordSystems } from './vector';
import { CoordSys3DNode } from './coordsysrect';
import { ImplicitRegionNode } from './implicitregion';
import { ParametricRegionNode, parametricRegionList } from './parametricregion';

/**
 * SymPy ParametricIntegral._bounds_case: the parameters in the order of
 * integration, the parameters whose bounds depend on another one first.
 */
function boundsCase(parameters: readonly Expr[], limits: ExprMap<[Expr, Expr]>): Expr[] {
  const V = [...limits.keys()];
  const E: [Expr, Expr][] = [];
  for (const p of V) {
    const [lo, hi] = defined(limits.get(p), 'limits');
    const inBounds = new Set([...atoms(lo), ...atoms(hi)].map((a) => a.key));
    for (const q of V) if (p.key !== q.key && inBounds.has(q.key)) E.push([p, q]);
  }
  if (E.length === 0) return [...parameters];
  return topologicalSort<Expr>([V, E]);
}

/** The integral of f over the parameters with their limits, innermost first. */
function integrateOver(f: Expr, variables: readonly Expr[], limits: ExprMap<[Expr, Expr]>): Expr {
  let r = f;
  for (const v of variables) {
    r = integrate(r, cast(v, Sym, 'parameter'), defined(limits.get(v), 'limits'));
  }
  return r;
}

/**
 * The integral of a field over a parametric region (unevaluated when the integral cannot be
 * computed).
 *
 * @see SymPy `sympy.vector.integrals.ParametricIntegral`
 * @example
 * ```ts
 * import { ParametricIntegral, ParametricRegion, ex } from '@symjs/symjs';
 *
 * const curve = ParametricRegion([ex`3*t - 2`, ex`t + 1`], [ex`t`, 1, 2]);
 * ParametricIntegral(1, curve); // => sqrt(10)
 * ```
 */
export class ParametricIntegralNode extends ExtensionExpr {
  /**
   * Constructs an instance of `ParametricIntegralNode`.
   *
   * @param field - Field to evaluate or differentiate.
   * @param region - Region or integration limits.
   */
  constructor(field: Expr, region: ParametricRegionNode) {
    super('ParametricIntegral', [field, region]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return parametricIntegral(at(args, 0), cast(at(args, 1), ParametricRegionNode, 'ParametricRegion'));
  }
  /**
   * Field to evaluate or differentiate.
   *
   * @returns Field to evaluate or differentiate.
   * @see SymPy `sympy.vector.integrals.ParametricIntegral.field`
   */
  get field(): Expr {
    return at(this.args, 0);
  }
  /**
   * The parametric region of integration.
   *
   * @returns The parametric region of integration.
   * @see SymPy `sympy.vector.integrals.ParametricIntegral.parametricregion`
   */
  get parametricregion(): ParametricRegionNode {
    return cast(at(this.args, 1), ParametricRegionNode, 'ParametricRegion');
  }
}

/** SymPy ParametricIntegral.__new__: the evaluated integral, or the unevaluated node. */
function parametricIntegral(fieldIn: ExprLike, region: ParametricRegionNode): Expr {
  const field = sympify(fieldIn);
  const systems = coordSystems(field);
  if (systems.length > 1) throw new RangeError('the field is defined in several coordinate systems');
  const cs = systems[0] ?? new CoordSys3DNode('C');
  if (region.dimensions === 0) return S.Zero;
  const baseVectors = cs.baseVectors();
  const baseScalars = cs.baseScalars();
  const definition = region.definition;
  let r: Expr = Vector.zero;
  definition.forEach((d, i) => {
    r = add(r, mul(at(baseVectors, i), d));
  });
  let pf = field;
  if (systems.length !== 0) definition.forEach((d, i) => (pf = subs(pf, [[at(baseScalars, i), d]])));
  const limits = region.limits;
  const asVector = (e: Expr): Vector => cast(e, Vector, 'vector');
  let result: Expr;
  if (region.dimensions === 1) {
    const parameter = at(region.parameters, 0);
    const rDiff = asVector(diff(r, parameter));
    const integrand = simplify(pf instanceof Vector ? rDiff.dot(pf) : mul(rDiff.magnitude(), pf));
    result = integrateOver(integrand, [parameter], limits);
  } else if (region.dimensions === 2) {
    const [u, v] = boundsCase(region.parameters, limits);
    const ru = asVector(diff(r, defined(u, 'u')));
    const rv = asVector(diff(r, defined(v, 'v')));
    const normal = asVector(simplify(ru.cross(rv)));
    const integrand = simplify(pf instanceof Vector ? pf.dot(normal) : mul(pf, normal.magnitude()));
    result = integrateOver(integrand, [defined(u, 'u'), defined(v, 'v')], limits);
  } else {
    const variables = boundsCase(region.parameters, limits);
    const coeff = jacobian(Matrix.col(...definition), variables).det();
    result = integrateOver(simplify(mul(pf, coeff)), variables, limits);
  }
  return result instanceof Integral ? new ParametricIntegralNode(field, region) : result;
}

/**
 * The integral of a scalar or vector field over a parametrized region.
 *
 * @param field - Field to evaluate or differentiate.
 * @param region - Region or integration limits.
 * @returns The value of the integral, or a parametric integral if it cannot be evaluated.
 * @see SymPy `sympy.vector.integrals.ParametricIntegral`
 * @example
 * ```ts
 * import { ParametricIntegral, ParametricRegion, ex } from '@symjs/symjs';
 *
 * const curve = ParametricRegion([ex`3*t - 2`, ex`t + 1`], [ex`t`, 1, 2]);
 * ParametricIntegral(1, curve); // => sqrt(10)
 * ```
 */
export const ParametricIntegral = /* @__PURE__ */ callableClass(ParametricIntegralNode, (field: ExprLike, region: ParametricRegionNode): Expr => parametricIntegral(field, region));
export type ParametricIntegral = ParametricIntegralNode;

/** A region of vector_integrate: a parameter or base scalar, or [variable, lower, upper]. */
export type IntegrationLimit = Sym | readonly [Sym, ExprLike, ExprLike] | TupleNode;

/**
 * The integral of a field over a parametric, implicit or geometric region, or with respect to
 * variables (with their limits).
 *
 * @param fieldIn - Scalar or vector field on the region.
 * @param region - Region or integration limits.
 * @returns The integral of a field over a parametric, implicit or geometric region, or with respect to variables (with their limits).
 * @throws TypeError when a limit does not specify a variable and bounds.
 * @see SymPy `sympy.vector.integrals.vector_integrate`
 * @example
 * ```ts
 * import { CoordSys3D, vectorIntegrate } from '@symjs/symjs';
 *
 * const C = CoordSys3D('C');
 * vectorIntegrate(C.y.pow(3).mul(12), [C.y, 1, 3]); // => 240
 * ```
 */
export function vectorIntegrate(fieldIn: ExprLike, ...region: (Expr | IntegrationLimit)[]): Expr {
  const field = sympify(fieldIn);
  if (region.length === 1) {
    const reg = at(region, 0);
    if (reg instanceof ParametricRegionNode) return parametricIntegral(field, reg);
    if (reg instanceof ImplicitRegionNode) return vectorIntegrate(field, at(parametricRegionList(reg), 0));
    if (reg instanceof GeometryEntity) return add(...parametricRegionList(reg).map((r) => vectorIntegrate(field, r)));
  }
  let r = field;
  for (const lim of region) {
    if (lim instanceof Sym) r = integrate(r, lim);
    else {
      const items: readonly ExprLike[] = lim instanceof TupleNode ? lim.args : lim instanceof Expr ? [lim] : lim;
      const [x, a, b] = items.map((i) => sympify(i));
      if (!(x instanceof Sym) || a === undefined || b === undefined) throw new TypeError(`${String(lim)} is not a variable with limits`);
      r = integrate(r, x, [a, b]);
    }
  }
  return r;
}
