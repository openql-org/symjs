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

/** SymPy Orienter: the super class of the orienters. */
export abstract class Orienter extends ExtensionExpr {
  /**
   * The rotation matrix of this orientation (SymPy rotation_matrix); an
   * AxisOrienter needs the system the axis is expressed in.
   */
  abstract rotationMatrix(system?: CoordSysBase): Matrix;
}

/** SymPy AxisOrienter(angle, axis): a rotation about an axis (a vector) by an angle. */
export class AxisOrienterNode extends Orienter {
  constructor(angleIn: ExprLike, axis: Expr) {
    if (!(axis instanceof Vector)) throw new TypeError('axis should be a Vector');
    super('AxisOrienter', [sympify(angleIn), axis]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new AxisOrienterNode(at(args, 0), at(args, 1));
  }
  /** SymPy angle. */
  get angle(): Expr {
    return at(this.args, 0);
  }
  /** SymPy axis. */
  get axis(): Vector {
    return cast(at(this.args, 1), Vector, 'axis');
  }
  /** SymPy AxisOrienter.rotation_matrix(system): the rotation with the axis expressed in system. */
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

/** SymPy ThreeAngleOrienter: the super class of the body and space orienters. */
export abstract class ThreeAngleOrienter extends Orienter {
  readonly #parentOrient: Matrix;
  /** The rotation order as given (SymPy rot_order). */
  readonly rotOrder: string;
  /** The rotation order as digits (SymPy's Str argument). */
  readonly order: string;

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
  /** SymPy angle1, angle2, angle3. */
  get angle1(): Expr {
    return at(this.args, 0);
  }
  get angle2(): Expr {
    return at(this.args, 1);
  }
  get angle3(): Expr {
    return at(this.args, 2);
  }
  /** SymPy rotation_matrix(). */
  rotationMatrix(): Matrix {
    return this.#parentOrient;
  }
  override printStr(print: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(print).join(', ')}, ${this.order})`;
  }
  protected override computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')};${this.order})`;
  }
}

/** SymPy BodyOrienter(angle1, angle2, angle3, rot_order): three successive rotations about the body-fixed axes. */
export class BodyOrienterNode extends ThreeAngleOrienter {
  constructor(angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string) {
    super('BodyOrienter', angle1, angle2, angle3, rotOrder, true);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new BodyOrienterNode(at(args, 0), at(args, 1), at(args, 2), this.rotOrder);
  }
}

/** SymPy SpaceOrienter(angle1, angle2, angle3, rot_order): three successive rotations about the space-fixed axes. */
export class SpaceOrienterNode extends ThreeAngleOrienter {
  constructor(angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string) {
    super('SpaceOrienter', angle1, angle2, angle3, rotOrder, false);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new SpaceOrienterNode(at(args, 0), at(args, 1), at(args, 2), this.rotOrder);
  }
}

/** SymPy QuaternionOrienter(q0, q1, q2, q3): the rotation of a quaternion. */
export class QuaternionOrienterNode extends Orienter {
  readonly #parentOrient: Matrix;
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
  withArgs(args: readonly Expr[]): Expr {
    return new QuaternionOrienterNode(at(args, 0), at(args, 1), at(args, 2), at(args, 3));
  }
  /** SymPy q0, q1, q2, q3. */
  get q0(): Expr {
    return at(this.args, 0);
  }
  get q1(): Expr {
    return at(this.args, 1);
  }
  get q2(): Expr {
    return at(this.args, 2);
  }
  get q3(): Expr {
    return at(this.args, 3);
  }
  /** SymPy rotation_matrix(). */
  rotationMatrix(): Matrix {
    return this.#parentOrient;
  }
}

/** SymPy AxisOrienter(angle, axis). */
export const AxisOrienter = /* @__PURE__ */ callableClass(AxisOrienterNode, (angle: ExprLike, axis: Expr): AxisOrienterNode => new AxisOrienterNode(angle, axis));
export type AxisOrienter = AxisOrienterNode;

/** SymPy BodyOrienter(angle1, angle2, angle3, rot_order). */
export const BodyOrienter = /* @__PURE__ */ callableClass(
  BodyOrienterNode,
  (angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string): BodyOrienterNode => new BodyOrienterNode(angle1, angle2, angle3, rotOrder),
);
export type BodyOrienter = BodyOrienterNode;

/** SymPy SpaceOrienter(angle1, angle2, angle3, rot_order). */
export const SpaceOrienter = /* @__PURE__ */ callableClass(
  SpaceOrienterNode,
  (angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotOrder: string): SpaceOrienterNode => new SpaceOrienterNode(angle1, angle2, angle3, rotOrder),
);
export type SpaceOrienter = SpaceOrienterNode;

/** SymPy QuaternionOrienter(q0, q1, q2, q3). */
export const QuaternionOrienter = /* @__PURE__ */ callableClass(
  QuaternionOrienterNode,
  (q0: ExprLike, q1: ExprLike, q2: ExprLike, q3: ExprLike): QuaternionOrienterNode => new QuaternionOrienterNode(q0, q1, q2, q3),
);
export type QuaternionOrienter = QuaternionOrienterNode;
