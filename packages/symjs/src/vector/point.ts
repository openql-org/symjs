// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/point.py, and _path of
// sympy/vector/functions.py), Copyright (c) 2006-2023 SymPy Development
// Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.point: Point, a point in 3-D space located by
 * its position vector with respect to a parent point (the origins of the
 * coordinate systems are such points).
 *
 * Exported as `VectorPoint`: SymPy's top-level `Point` is the geometric
 * point of `@symjs/symjs/geometry`.
 */

import type { Expr} from '../core/nodes';
import { ExtensionExpr } from '../core/nodes';
import { mul } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { CoordSysBase } from './basisdependent';
import { Vector } from './vector';

/**
 * SymPy _path(from_object, to_object): the path from one node of a tree of
 * points (or coordinate systems) to another through their first common
 * ancestor, and the index of that ancestor in the path.
 */
export function treePath<T extends Expr>(from: T, to: T, parent: (t: T) => T | undefined, root: (t: T) => T): [number, T[]] {
  if (root(from).key !== root(to).key) throw new RangeError(`No connecting path found between ${String(from)} and ${String(to)}`);
  const otherPath: T[] = [];
  let obj: T = to;
  let p = parent(obj);
  while (p !== undefined) {
    otherPath.push(obj);
    obj = p;
    p = parent(obj);
  }
  otherPath.push(obj);
  const keys = otherPath.map((o) => o.key);
  const fromPath: T[] = [];
  let cur: T = from;
  while (!keys.includes(cur.key)) {
    fromPath.push(cur);
    cur = defined(parent(cur), 'parent');
  }
  const index = fromPath.length;
  const k = keys.indexOf(cur.key);
  fromPath.push(...otherPath.slice(0, k + 1).reverse());
  return [index, fromPath];
}

/**
 * A point in 3-D space.
 *
 * @see SymPy `sympy.vector.point.Point`
 */
export class VectorPointNode extends ExtensionExpr {
  /** The name of the point. */
  readonly pointName: string;
  readonly #root: VectorPointNode;

  /**
   * Constructs an instance of `VectorPointNode`.
   *
   * @param name - Symbolic name.
   * @param position - Displacement from the reference point.
   * @param parentPoint - Reference point from which the displacement is measured.
   * @throws TypeError when the reference point is not a vector-package point or the displacement is not a vector.
   */
  constructor(name: string, position: Expr = Vector.zero, parentPoint?: VectorPointNode) {
    if (!(position instanceof Vector)) throw new TypeError(`position should be an instance of Vector, not ${String(position)}`);
    if (parentPoint !== undefined && !(parentPoint instanceof VectorPointNode)) {
      throw new TypeError(`parent_point should be an instance of Point, not ${String(parentPoint)}`);
    }
    super('VectorPoint', parentPoint === undefined ? [position] : [position, parentPoint]);
    this.pointName = String(name);
    this.#root = parentPoint === undefined ? this : parentPoint.root;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const parent = args[1];
    return new VectorPointNode(this.pointName, at(args, 0), parent instanceof VectorPointNode ? parent : undefined);
  }
  /**
   * The position vector with respect to the parent point.
   *
   * @returns The position vector with respect to the parent point.
   */
  get position(): Vector {
    return cast(at(this.args, 0), Vector, 'position');
  }
  /**
   * The reference point for a displacement. A root point has no parent.
   *
   * @returns The reference point, when one is defined.
   */
  get parent(): VectorPointNode | undefined {
    const p = this.args[1];
    return p instanceof VectorPointNode ? p : undefined;
  }
  /**
   * The root of the tree of points.
   *
   * @returns The root of the tree of points.
   */
  get root(): VectorPointNode {
    return this.#root;
  }

  /**
   * The position vector of this point with respect to another point, or to the origin of a
   * coordinate system.
   *
   * @param otherIn - Reference point or coordinate system origin.
   * @returns The position vector of this point with respect to another point, or to the origin of a coordinate system.
   * @throws TypeError when the reference is neither a vector point nor a coordinate system.
   * @see SymPy `sympy.vector.point.Point.position_wrt`
   */
  positionWrt(otherIn: VectorPointNode | CoordSysBase): Expr {
    if (!(otherIn instanceof VectorPointNode) && !(otherIn instanceof CoordSysBase)) throw new TypeError(`${String(otherIn)}is not a Point or CoordSys3D`);
    const o = cast(otherIn instanceof CoordSysBase ? otherIn.originPoint : otherIn, VectorPointNode, 'Point');
    if (o.key === this.key) return Vector.zero;
    if (this.parent !== undefined && o.key === this.parent.key) return this.position;
    if (o.parent !== undefined && o.parent.key === this.key) return mul(-1, o.position);
    const [rootIndex, path] = treePath<VectorPointNode>(
      this,
      o,
      (p) => p.parent,
      (p) => p.root,
    );
    let result: Expr = Vector.zero;
    for (let i = 0; i < rootIndex; i++) result = result.add(at(path, i).position);
    for (let i = rootIndex + 1; i < path.length; i++) result = result.sub(at(path, i).position);
    return result;
  }

  /**
   * A new point at the given position with respect to this one.
   *
   * @param name - Symbolic name.
   * @param position - Displacement from the reference point.
   * @returns A new point at the given position with respect to this one.
   * @see SymPy `sympy.vector.point.Point.locate_new`
   */
  locateNew(name: string, position: Expr): VectorPointNode {
    return new VectorPointNode(name, position, this);
  }

  /**
   * The coordinates of this point with respect to the origin of system.
   *
   * @param system - Coordinate system in which to express components.
   * @returns The coordinates of this point with respect to the origin of system.
   * @see SymPy `sympy.vector.point.Point.express_coordinates`
   */
  expressCoordinates(system: CoordSysBase): [Expr, Expr, Expr] {
    const m = cast(this.positionWrt(system), Vector, 'position').toMatrix(system);
    return [m.get(0, 0), m.get(1, 0), m.get(2, 0)];
  }

  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.pointName;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    return this.pointName;
  }
  protected override computeKey(): string {
    return `VectorPoint(${JSON.stringify(this.pointName)};${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * A named point with a vector displacement from its parent point.
 *
 * @param name - Symbolic name.
 * @param position - Displacement from the reference point.
 * @param parentPoint - Reference point from which the displacement is measured.
 * @returns The resulting `VectorPoint` expression.
 * @throws TypeError when the reference point is not a vector-package point or the displacement is not a vector.
 * @see SymPy `sympy.vector.point.Point`
 */
export const VectorPoint = /* @__PURE__ */ callableClass(
  VectorPointNode,
  (name: string, position?: Expr, parentPoint?: VectorPointNode): VectorPointNode => new VectorPointNode(name, position, parentPoint),
);
export type VectorPoint = VectorPointNode;
