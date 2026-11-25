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
 * Finds the path between two points or coordinate systems through their nearest common ancestor.
 * Returns the ancestor's index followed by the full path.
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

/** The parent of a point, or undefined for a root. */
function parentPoint(p: VectorPointNode): VectorPointNode | undefined {
  const q = p.args[1];
  return q instanceof VectorPointNode ? q : undefined;
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
   * Measures the offset from the parent point.
   *
   * @returns The relative position vector.
   */
  get position(): Vector {
    return cast(at(this.args, 0), Vector, 'position');
  }
  /**
   * Tells whether the point was created without a parent, so that it is the root of its tree.
   *
   * @returns `true` when the point has no parent.
   */
  get isRoot(): boolean {
    return parentPoint(this) === undefined;
  }
  /**
   * Identifies the point relative to which the displacement is measured.
   *
   * @returns The reference point.
   * @throws RangeError when the point is a root (see `isRoot`).
   * @see SymPy `sympy.vector.point.Point._parent`
   */
  get parent(): VectorPointNode {
    const p = parentPoint(this);
    if (p === undefined) throw new RangeError(`${String(this)} is a root point and has no parent`);
    return p;
  }
  /**
   * Follows parent points to the top of the hierarchy.
   *
   * @returns The root point.
   */
  get root(): VectorPointNode {
    return this.#root;
  }

  /**
   * Measures the displacement from another point or coordinate-system origin to this point.
   *
   * @param otherIn - Reference point or coordinate system origin.
   * @returns The relative position vector.
   * @throws TypeError when the reference is neither a vector point nor a coordinate system.
   * @see SymPy `sympy.vector.point.Point.position_wrt`
   */
  positionWrt(otherIn: VectorPointNode | CoordSysBase): Expr {
    if (!(otherIn instanceof VectorPointNode) && !(otherIn instanceof CoordSysBase)) throw new TypeError(`${String(otherIn)}is not a Point or CoordSys3D`);
    const o = cast(otherIn instanceof CoordSysBase ? otherIn.originPoint : otherIn, VectorPointNode, 'Point');
    if (o.key === this.key) return Vector.zero;
    if (parentPoint(this)?.key === o.key) return this.position;
    if (parentPoint(o)?.key === this.key) return mul(-1, o.position);
    const [rootIndex, path] = treePath<VectorPointNode>(
      this,
      o,
      parentPoint,
      (p) => p.root,
    );
    let result: Expr = Vector.zero;
    for (let i = 0; i < rootIndex; i++) result = result.add(at(path, i).position);
    for (let i = rootIndex + 1; i < path.length; i++) result = result.sub(at(path, i).position);
    return result;
  }

  /**
   * Creates a point displaced from this one by the supplied vector.
   *
   * @param name - Symbolic name.
   * @param position - Displacement from the reference point.
   * @returns The new point.
   * @see SymPy `sympy.vector.point.Point.locate_new`
   */
  locateNew(name: string, position: Expr): VectorPointNode {
    return new VectorPointNode(name, position, this);
  }

  /**
   * Resolves the displacement from the system origin along its coordinate axes.
   *
   * @param system - Coordinate system in which to express components.
   * @returns The point coordinates.
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
 * Constructs a named point with a vector displacement from its parent point.
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
