// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/parabola.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.parabola: parabolas in the plane, given by a
 * focus and a directrix.
 */

import type { Expr} from '../core/nodes';
import { S, Sym } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { subs } from '../core/traverse';
import { ordered } from '../core/match';
import { callableClass } from '../core/callable';
import { at, cast } from '../core/guard';
import { sign } from '../functions/special/special';
import { simplify } from '../simplify/simplify';
import { GeometrySet, realSymbol } from './entity';
import type { PointInput , GeometryEntity} from './entity';
import { Point2DNode, PointNode, toInput, toPoint } from './point';
import { Line, Line2D, Line2DNode, LinearEntity, Ray2DNode, Segment2DNode } from './line';
import { EllipseNode } from './ellipse';
import { solveEquations } from './solvehelp';

const as2D = (e: Expr): Point2DNode => cast(e, Point2DNode, 'Point2DNode');
const asLine = (e: Expr): Line2DNode => cast(e, Line2DNode, 'Line2DNode');

/**
 * The points at equal distance from a focus and a directrix.
 *
 * @see SymPy `sympy.geometry.parabola.Parabola`
 * @example
 * ```ts
 * import { Line, Parabola } from '@symjs/symjs';
 *
 * const p = Parabola([0, 0], Line([5, 8], [7, 8]));
 * p.focus; // => Point2D(0, 0)
 * p.directrix; // => Line2D(Point2D(5, 8), Point2D(7, 8))
 * ```
 */
export class ParabolaNode extends GeometrySet {
  /**
   * Constructs an instance of `ParabolaNode`.
   *
   * @param focus - Focus of the parabola.
   * @param directrix - Line equidistant from each point of the parabola and its focus.
   */
  constructor(focus: Point2DNode, directrix: Line2DNode) {
    super('Parabola', [focus, directrix]);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return newParabola(at(args, 0), at(args, 1));
  }

  /**
   * The number of coordinates in the surrounding space.
   *
   * @returns The number of coordinates in the surrounding space.
   * @see SymPy `sympy.geometry.parabola.Parabola.ambient_dimension`
   */
  get ambientDimension(): number {
    return 2;
  }

  /**
   * The focus.
   *
   * @returns The focus.
   * @see SymPy `sympy.geometry.parabola.Parabola.focus`
   */
  get focus(): Point2DNode {
    return as2D(at(this.args, 0));
  }

  /**
   * The directrix.
   *
   * @returns The directrix.
   * @see SymPy `sympy.geometry.parabola.Parabola.directrix`
   */
  get directrix(): Line2DNode {
    return asLine(at(this.args, 1));
  }

  /**
   * The line through the focus perpendicular to the directrix.
   *
   * @returns The line through the focus perpendicular to the directrix.
   * @see SymPy `sympy.geometry.parabola.Parabola.axis_of_symmetry`
   */
  get axisOfSymmetry(): Line2DNode {
    return this.directrix.perpendicularLine(this.focus);
  }

  /**
   * The eccentricity: 1.
   *
   * @returns The eccentricity: 1.
   * @see SymPy `sympy.geometry.parabola.Parabola.eccentricity`
   */
  get eccentricity(): Expr {
    return S.One;
  }

  /**
   * The equation of the parabola in real symbols x and y.
   *
   * @param x - Symbol for the x coordinate.
   * @param y - Symbol for the y coordinate.
   * @returns The equation of the parabola in real symbols x and y.
   * @see SymPy `sympy.geometry.parabola.Parabola.equation`
   */
  equation(x: string | Sym = 'x', y: string | Sym = 'y'): Expr {
    const [X, Y] = [realSymbol(x), realSymbol(y)];
    const m = this.directrix.slope;
    let t1: Expr, t2: Expr;
    if (m.key === S.Infinity.key) {
      t1 = mul(4, this.pParameter, add(X, mul(-1, this.vertex.x)));
      t2 = pow(add(Y, mul(-1, this.vertex.y)), 2);
    } else if (m.key === S.Zero.key) {
      t1 = mul(4, this.pParameter, add(Y, mul(-1, this.vertex.y)));
      t2 = pow(add(X, mul(-1, this.vertex.x)), 2);
    } else {
      const { x: a, y: b } = this.focus;
      const [c, d] = this.directrix.coefficients;
      t1 = add(pow(add(X, mul(-1, a)), 2), pow(add(Y, mul(-1, b)), 2));
      t2 = mul(pow(this.directrix.equation(X, Y), 2), pow(add(pow(c, 2), pow(d, 2)), -1));
    }
    return add(t1, mul(-1, t2));
  }

  /**
   * Half the distance from the focus to the directrix.
   *
   * @returns The distance between the focus and the vertex.
   * @see SymPy `sympy.geometry.parabola.Parabola.focal_length`
   */
  get focalLength(): Expr {
    return mul(this.directrix.distance(this.focus), S.Half);
  }

  /**
   * The signed focal length: positive when the parabola opens right or up.
   *
   * @returns The signed focal length: positive when the parabola opens right or up.
   * @see SymPy `sympy.geometry.parabola.Parabola.p_parameter`
   */
  get pParameter(): Expr {
    const m = this.directrix.slope;
    let p: Expr;
    if (m.key === S.Infinity.key) p = sign(add(this.focus.x, this.directrix.coefficients[2]));
    else if (m.key === S.Zero.key) p = sign(add(this.focus.y, this.directrix.coefficients[2]));
    else {
      const d = cast(this.directrix.projection(this.focus), PointNode, 'Point');
      p = sign(add(this.focus.x, mul(-1, d.coordinate(0))));
    }
    return mul(p, this.focalLength);
  }

  /**
   * The vertex.
   *
   * @returns The vertex.
   * @see SymPy `sympy.geometry.parabola.Parabola.vertex`
   */
  get vertex(): Point2DNode {
    const f = this.focus;
    const m = this.directrix.slope;
    if (m.key === S.Infinity.key) return as2D(toPoint([add(f.x, mul(-1, this.pParameter)), f.y]));
    if (m.key === S.Zero.key) return as2D(toPoint([f.x, add(f.y, mul(-1, this.pParameter))]));
    return as2D(at(this.axisOfSymmetry.intersection(this), 0));
  }

  /**
   * The points or entities common to the parabola and o.
   *
   * @param o - Entity to intersect with this one.
   * @returns The points or entities common to the parabola and o.
   * @throws TypeError when a three-dimensional entity is supplied to a planar operation or the operand is not a supported geometric entity.
   * @see SymPy `sympy.geometry.parabola.Parabola.intersection`
   */
  override intersection(o: unknown): GeometryEntity[] {
    const [x, y] = [new Sym('x', { real: true }), new Sym('y', { real: true })];
    const peq = this.equation();
    const points = (sols: Expr[][]): PointNode[] => ordered(sols.map((s) => toPoint(s))).filter((p): p is PointNode => p instanceof PointNode);
    if (o instanceof ParabolaNode) {
      if (this.contains(o)) return [o];
      return points(solveEquations([peq, o.equation()], [x, y]));
    }
    if (o instanceof Point2DNode) {
      if (simplify(subs(peq, [[x, o.x], [y, o.y]])).key === S.Zero.key) return [o];
      return [];
    }
    if (o instanceof Segment2DNode || o instanceof Ray2DNode) {
      const sols = solveEquations([peq, Line2D(o.p1, o.p2).equation()], [x, y]);
      return points(sols).filter((p) => o.contains(p));
    }
    if (o instanceof Line2DNode || o instanceof EllipseNode) return points(solveEquations([peq, o.equation()], [x, y]));
    if (o instanceof LinearEntity && o.ambientDimension === 3) throw new TypeError('Entity must be two dimensional, not three dimensional');
    throw new TypeError('Wrong type of argument were put');
  }
}

/** SymPy Parabola.__new__(focus=None, directrix=None). */
function newParabola(focusIn: PointInput | undefined, directrixIn: unknown): ParabolaNode {
  const focus = as2D(focusIn === undefined ? toPoint([0, 0]) : toPoint(focusIn, { dim: 2 }));
  if (!(directrixIn instanceof LinearEntity)) throw new TypeError('The directrix must be a line');
  const directrix = asLine(Line(directrixIn));
  if (directrix.contains(focus)) throw new RangeError('The focus must not be a point of directrix');
  return new ParabolaNode(focus, directrix);
}

/**
 * The points in a plane equidistant from a focus and a directrix line.
 *
 * @param focus - Focus of the parabola.
 * @param directrix - Line equidistant from each point of the parabola and its focus.
 * @returns The resulting `Parabola` expression.
 * @throws RangeError when the focus lies on the directrix.
 * @throws TypeError when the directrix is not a linear entity.
 * @see SymPy `sympy.geometry.parabola.Parabola`
 * @example
 * ```ts
 * import { Line, Parabola } from '@symjs/symjs';
 *
 * const p = Parabola([0, 0], Line([5, 8], [7, 8]));
 * p.focus; // => Point2D(0, 0)
 * p.directrix; // => Line2D(Point2D(5, 8), Point2D(7, 8))
 * ```
 */
export const Parabola = /* @__PURE__ */ callableClass(ParabolaNode, (focus: PointInput | undefined, directrix: LinearEntity): ParabolaNode => newParabola(focus === undefined ? undefined : toInput(focus), directrix));
export type Parabola = ParabolaNode;
