// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/orienters.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.orienters: the orientations of a new coordinate
 * system with respect to another (AxisOrienter, BodyOrienter,
 * SpaceOrienter, QuaternionOrienter), as rotation matrices.
 */

import { ExtensionExpr } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, cast } from '../core/guard';
import { cos, sin } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { rotAxis1, rotAxis2, rotAxis3 } from '../matrices/linalg';
import { CoordSysBase, expressHook, matMul } from './basisdependent';
import { Vector } from './vector';

/**
 * The super class of the orienters.
 *
 * @see SymPy `sympy.vector.orienters.Orienter`
 */
export abstract class Orienter extends ExtensionExpr {
  /**
   * The rotation matrix of this orientation (SymPy rotation_matrix); an AxisOrienter needs the
   * system the axis is expressed in.
   *
   * @param system - Coordinate system in which to express components.
   * @returns The rotation matrix of this orientation (SymPy rotation_matrix); an AxisOrienter needs the system the axis is expressed in.
   * @see SymPy `sympy.vector.orienters.Orienter.rotation_matrix`
   */
  abstract rotationMatrix(system?: CoordSysBase): Matrix;
}

/**
 * A rotation about an axis (a vector) by an angle.
 *
 * @see SymPy `sympy.vector.orienters.AxisOrienter`
 */
export class AxisOrienterNode extends Orienter {
  /**
   * Constructs an instance of `AxisOrienterNode`.
   *
   * @param angleIn - Rotation angle in radians.
   * @param axis - Vector defining the rotation axis.
   * @throws TypeError when the axis is not a vector.
   */
  constructor(angleIn: ExprLike, axis: Expr) {
    if (!(axis instanceof Vector)) throw new TypeError('axis should be a Vector');
    super('AxisOrienter', [sympify(angleIn), axis]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new AxisOrienterNode(at(args, 0), at(args, 1));
  }
  /**
   * Rotation angle in radians.
   *
   * @returns Rotation angle in radians.
   * @see SymPy `sympy.vector.orienters.AxisOrienter.angle`
   */
  get angle(): Expr {
    return at(this.args, 0);
  }
  /**
   * Vector defining the rotation axis.
   *
   * @returns Vector defining the rotation axis.
   * @see SymPy `sympy.vector.orienters.AxisOrienter.axis`
   */
  get axis(): Vector {
    return cast(at(this.args, 1), Vector, 'axis');
  }
  /**
   * The rotation with the axis expressed in system.
   *
   * @param system - Coordinate system in which to express components.
   * @returns The rotation with the axis expressed in system.
   * @throws TypeError when the coordinate system of the rotation axis is missing.
   * @see SymPy `sympy.vector.orienters.AxisOrienter.rotation_matrix`
   */
  rotationMatrix(system?: CoordSysBase): Matrix {
    if (!(system instanceof CoordSysBase)) throw new TypeError('AxisOrienter.rotationMatrix needs the coordinate system of the axis');
    const a = cast(cast(expressHook(this.axis, system), Vector, 'axis').normalize(), Vector, 'axis').toMatrix(system);
    const theta = this.angle;
    const aat = matMul(a, a.T);
    const skew = Matrix.of([
      [0, mul(-1, a.get(2, 0)), a.get(1, 0)],
      [a.get(2, 0), 0, mul(-1, a.get(0, 0))],
      [mul(-1, a.get(1, 0)), a.get(0, 0), 0],
    ]);
    const m = Matrix.eye(3).sub(aat).scale(cos(theta)).add(skew.scale(sin(theta))).add(aat);
    return m.T;
  }
}

/** The approved rotation orders of SymPy ThreeAngleOrienter. */
const APPROVED_ORDERS = new Set(['123', '231', '312', '132', '213', '321', '121', '131', '212', '232', '313', '323', '']);

/** SymPy _rot(axis, angle): the DCM of a simple rotation about axis 1, 2 or 3. */
function rot(axis: number, angle: Expr): Matrix {
  return (axis === 1 ? rotAxis1(angle) : axis === 2 ? rotAxis2(angle) : rotAxis3(angle)).T;
}

/**
 * The super class of the body and space orienters.
 *
 * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter`
 */
export abstract class ThreeAngleOrienter extends Orienter {
  readonly #parentOrient: Matrix;
  /**
   * The rotation order as given.
   *
   * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter.rot_order`
   */
  readonly rotOrder: string;
  /** The rotation order as digits (SymPy's Str argument). */
  readonly order: string;

  /**
   * Constructs an instance of `ThreeAngleOrienter`.
   *
   * @param name - Symbolic name.
   * @param angle1In - First rotation angle in radians.
   * @param angle2In - Second rotation angle in radians.
   * @param angle3In - Third rotation angle in radians.
   * @param rotOrder - Order of the rotation axes.
   * @param inOrder - Use the body-fixed order when composing rotations.
   * @throws TypeError when the sequence of rotation axes is invalid or the axis order is not a three-character string.
   */
  constructor(name: string, angle1In: ExprLike, angle2In: ExprLike, angle3In: ExprLike, rotOrder: string, inOrder: boolean) {
    const upper = String(rotOrder).toUpperCase();
    if (upper.length !== 3) throw new TypeError('rot_order should be a str of length 3');
    const order = upper.replace(/X/g, '1').replace(/Y/g, '2').replace(/Z/g, '3');
    if (!APPROVED_ORDERS.has(order)) throw new TypeError('Invalid rot_type parameter');
    const digits = order.split('').map(Number);
    const angles = [sympify(angle1In), sympify(angle2In), sympify(angle3In)];
    super(name, angles);
    const r = (i: number): Matrix => rot(at(digits, i), at(angles, i));
    const m = inOrder ? matMul(matMul(r(0), r(1)), r(2)) : matMul(matMul(r(2), r(1)), r(0));
    this.#parentOrient = m.T;
    this.rotOrder = rotOrder;
    this.order = order;
  }
  /**
   * First rotation angle in radians.
   *
   * @returns First rotation angle in radians.
   * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter.angle1`
   */
  get angle1(): Expr {
    return at(this.args, 0);
  }
  /**
   * Second rotation angle in radians.
   *
   * @returns Second rotation angle in radians.
   * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter.angle2`
   */
  get angle2(): Expr {
    return at(this.args, 1);
  }
  /**
   * Third rotation angle in radians.
   *
   * @returns Third rotation angle in radians.
   * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter.angle3`
   */
  get angle3(): Expr {
    return at(this.args, 2);
  }
  /**
   * The rotation matrix corresponding to this orienter instance.
   *
   * @returns The rotation matrix corresponding to this orienter instance.
   * @see SymPy `sympy.vector.orienters.ThreeAngleOrienter.rotation_matrix`
   */
  rotationMatrix(): Matrix {
    return this.#parentOrient;
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(print).join(', ')}, ${this.order})`;
  }
  protected override computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')};${this.order})`;
  }
}

/**
 * Three successive rotations about the body-fixed axes.
 *
 * @see SymPy `sympy.vector.orienters.BodyOrienter`
 */
export class BodyOrienterNode extends ThreeAngleOrienter {
  /**
   * Constructs an instance of `BodyOrienterNode`.
   *
   * @param angle1 - First rotation angle in radians.
   * @param angle2 - Second rotation angle in radians.
   * @param angle3 - Third rotation angle in radians.
   * @param rotOrder - Order of the rotation axes.
   */
  constructor(angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string) {
    super('BodyOrienter', angle1, angle2, angle3, rotOrder, true);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new BodyOrienterNode(at(args, 0), at(args, 1), at(args, 2), this.rotOrder);
  }
}

/**
 * Three successive rotations about the space-fixed axes.
 *
 * @see SymPy `sympy.vector.orienters.SpaceOrienter`
 */
export class SpaceOrienterNode extends ThreeAngleOrienter {
  /**
   * Constructs an instance of `SpaceOrienterNode`.
   *
   * @param angle1 - First rotation angle in radians.
   * @param angle2 - Second rotation angle in radians.
   * @param angle3 - Third rotation angle in radians.
   * @param rotOrder - Order of the rotation axes.
   */
  constructor(angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string) {
    super('SpaceOrienter', angle1, angle2, angle3, rotOrder, false);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new SpaceOrienterNode(at(args, 0), at(args, 1), at(args, 2), this.rotOrder);
  }
}

/**
 * The rotation of a quaternion.
 *
 * @see SymPy `sympy.vector.orienters.QuaternionOrienter`
 */
export class QuaternionOrienterNode extends Orienter {
  readonly #parentOrient: Matrix;
  /**
   * Constructs an instance of `QuaternionOrienterNode`.
   *
   * @param q0In - Scalar quaternion component.
   * @param q1In - First vector quaternion component.
   * @param q2In - Second vector quaternion component.
   * @param q3In - Third vector quaternion component.
   */
  constructor(q0In: ExprLike, q1In: ExprLike, q2In: ExprLike, q3In: ExprLike) {
    const qs = [sympify(q0In), sympify(q1In), sympify(q2In), sympify(q3In)];
    super('QuaternionOrienter', qs);
    const [q0, q1, q2, q3] = [at(qs, 0), at(qs, 1), at(qs, 2), at(qs, 3)];
    const sq = (e: Expr): Expr => e.pow(2);
    const m = Matrix.of([
      [add(sq(q0), sq(q1), mul(-1, sq(q2)), mul(-1, sq(q3))), mul(2, add(mul(q1, q2), mul(-1, q0, q3))), mul(2, add(mul(q0, q2), mul(q1, q3)))],
      [mul(2, add(mul(q1, q2), mul(q0, q3))), add(sq(q0), mul(-1, sq(q1)), sq(q2), mul(-1, sq(q3))), mul(2, add(mul(q2, q3), mul(-1, q0, q1)))],
      [mul(2, add(mul(q1, q3), mul(-1, q0, q2))), mul(2, add(mul(q0, q1), mul(q2, q3))), add(sq(q0), mul(-1, sq(q1)), mul(-1, sq(q2)), sq(q3))],
    ]);
    this.#parentOrient = m.T;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new QuaternionOrienterNode(at(args, 0), at(args, 1), at(args, 2), at(args, 3));
  }
  /**
   * Scalar component of the rotation quaternion.
   *
   * @returns Scalar component of the rotation quaternion.
   * @see SymPy `sympy.vector.orienters.QuaternionOrienter.q0`
   */
  get q0(): Expr {
    return at(this.args, 0);
  }
  /**
   * First vector component of the rotation quaternion.
   *
   * @returns First vector component of the rotation quaternion.
   * @see SymPy `sympy.vector.orienters.QuaternionOrienter.q1`
   */
  get q1(): Expr {
    return at(this.args, 1);
  }
  /**
   * Second vector component of the rotation quaternion.
   *
   * @returns Second vector component of the rotation quaternion.
   * @see SymPy `sympy.vector.orienters.QuaternionOrienter.q2`
   */
  get q2(): Expr {
    return at(this.args, 2);
  }
  /**
   * Third vector component of the rotation quaternion.
   *
   * @returns Third vector component of the rotation quaternion.
   * @see SymPy `sympy.vector.orienters.QuaternionOrienter.q3`
   */
  get q3(): Expr {
    return at(this.args, 3);
  }
  /**
   * The rotation matrix corresponding to this orienter instance.
   *
   * @returns The rotation matrix corresponding to this orienter instance.
   * @see SymPy `sympy.vector.orienters.QuaternionOrienter.rotation_matrix`
   */
  rotationMatrix(): Matrix {
    return this.#parentOrient;
  }
}

/**
 * Rotation about a specified vector axis through a given angle.
 *
 * @param angle - Rotation angle in radians.
 * @param axis - Vector defining the rotation axis.
 * @returns The resulting `AxisOrienter` expression.
 * @throws TypeError when the axis is not a vector.
 * @see SymPy `sympy.vector.orienters.AxisOrienter`
 */
export const AxisOrienter = /* @__PURE__ */ callableClass(AxisOrienterNode, (angle: ExprLike, axis: Expr): AxisOrienterNode => new AxisOrienterNode(angle, axis));
export type AxisOrienter = AxisOrienterNode;

/**
 * Three successive rotations about body-fixed axes in the specified order.
 *
 * @param angle1 - First rotation angle in radians.
 * @param angle2 - Second rotation angle in radians.
 * @param angle3 - Third rotation angle in radians.
 * @param rotOrder - Order of the rotation axes.
 * @returns The resulting `BodyOrienter` expression.
 * @see SymPy `sympy.vector.orienters.BodyOrienter`
 */
export const BodyOrienter = /* @__PURE__ */ callableClass(
  BodyOrienterNode,
  (angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string): BodyOrienterNode => new BodyOrienterNode(angle1, angle2, angle3, rotOrder),
);
export type BodyOrienter = BodyOrienterNode;

/**
 * Three successive rotations about space-fixed axes in the specified order.
 *
 * @param angle1 - First rotation angle in radians.
 * @param angle2 - Second rotation angle in radians.
 * @param angle3 - Third rotation angle in radians.
 * @param rotOrder - Order of the rotation axes.
 * @returns The resulting `SpaceOrienter` expression.
 * @see SymPy `sympy.vector.orienters.SpaceOrienter`
 */
export const SpaceOrienter = /* @__PURE__ */ callableClass(
  SpaceOrienterNode,
  (angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string): SpaceOrienterNode => new SpaceOrienterNode(angle1, angle2, angle3, rotOrder),
);
export type SpaceOrienter = SpaceOrienterNode;

/**
 * Orientation specified by a quaternion with scalar component first.
 *
 * @param q0 - Scalar quaternion component.
 * @param q1 - First vector quaternion component.
 * @param q2 - Second vector quaternion component.
 * @param q3 - Third vector quaternion component.
 * @returns The resulting `QuaternionOrienter` expression.
 * @see SymPy `sympy.vector.orienters.QuaternionOrienter`
 */
export const QuaternionOrienter = /* @__PURE__ */ callableClass(
  QuaternionOrienterNode,
  (q0: ExprLike, q1: ExprLike, q2: ExprLike, q3: ExprLike): QuaternionOrienterNode => new QuaternionOrienterNode(q0, q1, q2, q3),
);
export type QuaternionOrienter = QuaternionOrienterNode;
