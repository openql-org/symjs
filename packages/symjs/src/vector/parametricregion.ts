// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/parametricregion.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.parametricregion: ParametricRegion, a region
 * of space given by the base scalars as functions of parameters, and
 * parametric_region_list, the parametric regions of the entities of
 * `@symjs/symjs/geometry` and of implicit regions.
 */

import { Expr, ExtensionExpr, S, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { ExprMap } from '../core/exprmap';
import { subs } from '../core/traverse';
import { tan } from '../functions/elementary/elementary';
import { trigsimp } from '../simplify/trigsimp';
import { solve } from '../solvers/solve';
import { realSymbol } from '../geometry/entity';
import { PointNode } from '../geometry/point';
import { SegmentNode } from '../geometry/line';
import { CurveNode } from '../geometry/curve';
import { EllipseNode } from '../geometry/ellipse';
import { PolygonNode } from '../geometry/polygon';
import { ImplicitRegionNode } from './implicitregion';

/** A bound of a parametric region: a parameter, or [parameter, lower, upper]. */
export type ParametricBound = Expr | readonly [ExprLike, ExprLike, ExprLike];

/**
 * The base scalars as functions of parameters.
 *
 * @see SymPy `sympy.vector.parametricregion.ParametricRegion`
 * @remarks SymPy prints the coordinate tuple as `(t, t**2)`. The coordinates here form an ordered array.
 * @example
 * ```ts
 * import { ParametricRegion, ex } from '@symjs/symjs';
 *
 * const region = ParametricRegion([ex`t`, ex`t**2`], [ex`t`, -1, 2]);
 * region.definition; // => [t, t**2]
 * ```
 */
export class ParametricRegionNode extends ExtensionExpr {
  /**
   * Constructs an instance of `ParametricRegionNode`.
   *
   * @param definition - Coordinate expressions in the region parameters.
   * @param bounds - Parameters or triples of parameter, lower bound and upper bound.
   * @throws RangeError when a parameter bound is not a triple.
   */
  constructor(definition: ExprLike | readonly ExprLike[] | TupleNode, ...bounds: (ParametricBound | TupleNode)[]) {
    const def = definition instanceof TupleNode ? definition : new TupleNode((Array.isArray(definition) ? definition : [definition]).map((d: ExprLike) => sympify(d)));
    const bs = bounds.map((b) => {
      if (b instanceof Expr && !(b instanceof TupleNode)) return b;
      const items: readonly ExprLike[] = b instanceof TupleNode ? b.args : b;
      if (items.length !== 3) throw new RangeError('Tuple should be in the form (parameter, lowerbound, upperbound)');
      return new TupleNode(items.map((i) => sympify(i)));
    });
    super('ParametricRegion', [def, ...bs]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new ParametricRegionNode(at(args, 0), ...args.slice(1));
  }
  /**
   * Expresses the region's coordinates in terms of its parameters.
   *
   * @returns The parametric coordinate expressions.
   * @see SymPy `sympy.vector.parametricregion.ParametricRegion.definition`
   */
  get definition(): Expr[] {
    return [...at(this.args, 0).args];
  }
  /**
   * Lists the symbols or names used to parametrize the region.
   *
   * @returns The independent parameters in definition order.
   * @see SymPy `sympy.vector.parametricregion.ParametricRegion.parameters`
   */
  get parameters(): Expr[] {
    return this.args.slice(1).map((b) => (b instanceof TupleNode ? at(b.args, 0) : b));
  }
  /**
   * Identifies the endpoints of each bounded parameter.
   *
   * @returns The parameter bounds.
   * @see SymPy `sympy.vector.parametricregion.ParametricRegion.limits`
   */
  get limits(): ExprMap<[Expr, Expr]> {
    const m = new ExprMap<[Expr, Expr]>();
    for (const b of this.args.slice(1)) if (b instanceof TupleNode) m.set(at(b.args, 0), [at(b.args, 1), at(b.args, 2)]);
    return m;
  }
  /**
   * Counts bounded parameters, giving one for a curve, two for a surface, and three for a volume.
   *
   * @returns The region dimension.
   * @see SymPy `sympy.vector.parametricregion.ParametricRegion.dimensions`
   */
  get dimensions(): number {
    return this.limits.size;
  }
}

/**
 * Constructs a region described by coordinate functions of one or more parameters, optionally with
 * bounds.
 *
 * @param definition - Coordinate expressions in the region parameters.
 * @param bounds - Parameters or triples of parameter, lower bound and upper bound.
 * @returns The resulting `ParametricRegion` expression.
 * @throws RangeError when a parameter bound is not a triple.
 * @see SymPy `sympy.vector.parametricregion.ParametricRegion`
 * @remarks SymPy prints the coordinate tuple as `(t, t**2)`. The coordinates here form an ordered array.
 * @example
 * ```ts
 * import { ParametricRegion, ex } from '@symjs/symjs';
 *
 * const region = ParametricRegion([ex`t`, ex`t**2`], [ex`t`, -1, 2]);
 * region.definition; // => [t, t**2]
 * ```
 */
export const ParametricRegion = /* @__PURE__ */ callableClass(
  ParametricRegionNode,
  (definition: ExprLike | readonly ExprLike[] | TupleNode, ...bounds: (ParametricBound | TupleNode)[]): ParametricRegionNode => new ParametricRegionNode(definition, ...bounds),
);
export type ParametricRegion = ParametricRegionNode;

/**
 * Parametrizes a geometric or implicit region, using the rational parametrization for an implicit
 * region.
 *
 * @param reg - Geometric or implicit region to parametrize.
 * @param parameter - Symbol or name used for the parametrization.
 * @returns The parametrizations covering the supplied region.
 * @throws RangeError when no parametrization can be found for the region.
 * @see SymPy `sympy.vector.parametricregion.parametric_region_list`
 * @example
 * ```ts
 * import { Point, parametricRegionList } from '@symjs/symjs';
 *
 * parametricRegionList(Point(2, 5)); // => [ParametricRegion((2, 5))]
 * ```
 */
export function parametricRegionList(reg: Expr, parameter?: string | Sym | readonly (string | Sym)[]): ParametricRegionNode[] {
  if (reg instanceof PointNode) return [new ParametricRegionNode(reg.args)];
  if (reg instanceof CurveNode) return [new ParametricRegionNode(reg.arbitraryPoint(reg.parameter).args, reg.limits)];
  const p = typeof parameter === 'string' || parameter instanceof Sym ? parameter : 't';
  if (reg instanceof EllipseNode) return [new ParametricRegionNode(reg.arbitraryPoint(p).args, [realSymbol(p), 0, mul(2, S.Pi)])];
  if (reg instanceof SegmentNode) {
    const t = realSymbol(p);
    const definition = reg.arbitraryPoint(t).args;
    const [p0, p1] = reg.points;
    let bounds: [Expr, Expr, Expr] | undefined;
    for (let i = 0; i < definition.length && bounds === undefined; i++) {
      const lower = solve(at(definition, i).sub(at(p0.args, i)), t);
      const upper = solve(at(definition, i).sub(at(p1.args, i)), t);
      if (lower.length === 1 && upper.length === 1) bounds = [t, at(lower, 0), at(upper, 0)];
    }
    // (the coordinates of distinct points differ in one of the axes)
    return [new ParametricRegionNode(reg.arbitraryPoint(p).args, defined(bounds, 'bounds'))];
  }
  if (reg instanceof PolygonNode) return reg.sides.map((side) => at(parametricRegionList(side, p), 0));
  if (reg instanceof ImplicitRegionNode) {
    const parameters = parameter === undefined ? ['t', 's'] : typeof parameter === 'string' || parameter instanceof Sym ? [parameter] : parameter;
    let definition = reg.rationalParametrization(parameters);
    const bounds: [Expr, Expr, Expr][] = [];
    for (let i = 0; i < reg.variables.length - 1; i++) {
      // each parameter is replaced by its tangent to simplify integration
      const par = realSymbol(at(parameters, i));
      definition = definition.map((e) => trigsimp(subs(e, [[par, tan(mul(par, S.Half))]])));
      bounds.push([par, S.Zero, mul(2, S.Pi)]);
    }
    return [new ParametricRegionNode(new TupleNode(definition), ...bounds)];
  }
  throw new RangeError('SymPy cannot determine parametric representation of the region.');
}
