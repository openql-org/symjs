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

/** SymPy ParametricRegion(definition, *bounds): the base scalars as functions of parameters. */
export class ParametricRegionNode extends ExtensionExpr {
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
  withArgs(args: readonly Expr[]): Expr {
    return new ParametricRegionNode(at(args, 0), ...args.slice(1));
  }
  /** SymPy definition: the base scalars in terms of the parameters. */
  get definition(): Expr[] {
    return [...at(this.args, 0).args];
  }
  /** SymPy parameters. */
  get parameters(): Expr[] {
    return this.args.slice(1).map((b) => (b instanceof TupleNode ? at(b.args, 0) : b));
  }
  /** SymPy limits: the lower and upper bounds of the bounded parameters. */
  get limits(): ExprMap<[Expr, Expr]> {
    const m = new ExprMap<[Expr, Expr]>();
    for (const b of this.args.slice(1)) if (b instanceof TupleNode) m.set(at(b.args, 0), [at(b.args, 1), at(b.args, 2)]);
    return m;
  }
  /** SymPy dimensions: the number of bounded parameters (1 for a curve, 2 for a surface, 3 for a volume). */
  get dimensions(): number {
    return this.limits.size;
  }
}

/** SymPy ParametricRegion(definition, *bounds). */
export const ParametricRegion = /* @__PURE__ */ callableClass(
  ParametricRegionNode,
  (definition: ExprLike | readonly ExprLike[] | TupleNode, ...bounds: (ParametricBound | TupleNode)[]): ParametricRegionNode => new ParametricRegionNode(definition, ...bounds),
);
export type ParametricRegion = ParametricRegionNode;

/**
 * SymPy parametric_region_list(reg, parameter): the parametric regions of a
 * geometric entity (point, curve, ellipse, segment, polygon) or an
 * implicit region (with the parameters of its rational parametrization).
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
