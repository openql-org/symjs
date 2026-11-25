// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/coordsysrect.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.coordsysrect: CoordSys3D, a coordinate system in
 * 3-D space with its base vectors and base scalars, located and oriented
 * with respect to a parent system, or connected to it by transformation
 * equations (spherical, cylindrical, or given equations).
 *
 * The base vectors and scalars are `C.i`, `C.j`, `C.k` and `C.x`, `C.y`,
 * `C.z` (`C.attr(name)` for custom names, SymPy getattr).
 */

import { Dummy, ExtensionExpr, S, Sym } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sqrt, sympify } from '../core/ops';
import { ExprMap } from '../core/exprmap';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { LambdaNode } from '../core/lambda';
import { freeSymbols } from '../core/traverse';
import { acos, cos, sin } from '../functions/elementary/elementary';
import { atan2 } from '../functions/special/special';
import { diff } from '../calculus/diff';
import { Matrix } from '../matrices/matrix';
import { simplify } from '../simplify/simplify';
import { trigsimp } from '../simplify/trigsimp';
import { solveEquations } from '../geometry/solvehelp';
import { CoordSysBase, matMul } from './basisdependent';
import { BaseScalarNode } from './scalar';
import { BaseVectorNode, Vector, projections } from './vector';
import { AxisOrienterNode, BodyOrienterNode, Orienter, QuaternionOrienterNode, SpaceOrienterNode } from './orienters';
import { VectorPointNode, treePath } from './point';

/** Transformation equations: a function of the three coordinates giving the parent's coordinates. */
type Equations = (x: Expr, y: Expr, z: Expr) => [Expr, Expr, Expr];

/**
 * A transformation as SymPy accepts it: the name of a predefined system ('cartesian',
 * 'spherical', 'cylindrical'), a Lambda or a function of the three coordinates, `[variables,
 * equations]`, or `[rotationMatrix, location]`.
 */
export type Transformation =
  | string
  | LambdaNode
  | ((x1: Expr, x2: Expr, x3: Expr) => readonly ExprLike[])
  | readonly [Matrix, Expr]
  | readonly [readonly Expr[] | TupleNode, readonly ExprLike[] | TupleNode];

/** The names of the base vectors and base scalars. */
export interface NamesOptions {
  /** Names of the three basis vectors in axis order. */
  readonly vectorNames?: readonly string[];
  /** Names of the three coordinate scalars in axis order. */
  readonly variableNames?: readonly string[];
}

/** The options of CoordSys3D. */
export interface CoordSysOptions extends NamesOptions {
  /** Coordinate transformation to the parent system. */
  readonly transformation?: Transformation;
  /** Parent coordinate system relative to which this system is defined. */
  readonly parent?: CoordSys3DNode;
  /** Position of the new origin relative to the parent origin. */
  readonly location?: Expr;
  /** Rotation matrix relative to the parent basis. */
  readonly rotationMatrix?: Matrix;
}

/** The form of a transformation: rotation and translation, a predefined system, or equations. */
type TransformationForm = { kind: 'rect'; rotation: Matrix; location: Expr } | { kind: 'name'; name: string } | { kind: 'lambda'; lambda: LambdaNode };

const isMatrixPair = (t: Transformation): t is readonly [Matrix, Expr] => Array.isArray(t) && t[0] instanceof Matrix;

const tupleItems = (t: readonly ExprLike[] | readonly Expr[] | TupleNode): Expr[] => (t instanceof TupleNode ? t.toArray() : t.map(sympify));

function checkStrings(argName: string, arg: readonly unknown[]): void {
  const msg = `${argName} must be an iterable of 3 string-types`;
  if (arg.length !== 3) throw new RangeError(msg);
  for (const s of arg) if (typeof s !== 'string') throw new TypeError(msg);
}

/** SymPy _get_lame_coeff: the Lame coefficients of a predefined system. */
function lameOf(name: string): Equations {
  if (name === 'cartesian') return () => [S.One, S.One, S.One];
  if (name === 'spherical') return (r, theta) => [S.One, r, mul(r, sin(theta))];
  // cylindrical (transformationOf has rejected the other names)
  return (r) => [S.One, r, S.One];
}

/** SymPy _get_transformation_lambdas: the transformation equations of a predefined system. */
function transformationOf(name: string): Equations {
  if (name === 'cartesian') return (x, y, z) => [x, y, z];
  if (name === 'spherical') return (r, theta, phi) => [mul(r, sin(theta), cos(phi)), mul(r, sin(theta), sin(phi)), mul(r, cos(theta))];
  if (name === 'cylindrical') return (r, theta, h) => [mul(r, cos(theta)), mul(r, sin(theta)), h];
  throw new RangeError('Wrong set of parameters.Type of coordinate system is defined');
}

/** SymPy _set_inv_trans_equations: the inverse transformation equations of a predefined system. */
function inverseOf(name: string): Equations {
  if (name === 'spherical') {
    return (x, y, z) => {
      const r = sqrt(add(x.pow(2), y.pow(2), z.pow(2)));
      return [r, acos(mul(z, r.pow(-1))), atan2(y, x)];
    };
  }
  if (name === 'cylindrical') return (x, y, z) => [sqrt(add(x.pow(2), y.pow(2))), atan2(y, x), z];
  return (x, y, z) => [x, y, z];
}

/** The three expressions of a Lambda applied to three arguments. */
function applyLambda(l: LambdaNode, x: Expr, y: Expr, z: Expr): [Expr, Expr, Expr] {
  const items = cast(l.call(x, y, z), TupleNode, 'transformation equations').toArray();
  return [at(items, 0), at(items, 1), at(items, 2)];
}

/** SymPy _calculate_lame_coeff: the Lame coefficients of transformation equations. */
function lameOfLambda(l: LambdaNode): Equations {
  return (x1, x2, x3) => {
    const eqs = applyLambda(l, x1, x2, x3);
    const h = (v: Expr): Expr => sqrt(add(...eqs.map((e) => diff(e, v).pow(2))));
    return [h(x1), h(x2), h(x3)];
  };
}

/** Tests whether the coordinate transformation defines an orthogonal system. */
export function checkOrthogonality(equations: LambdaNode): boolean {
  const xs = [new Dummy('x1'), new Dummy('x2'), new Dummy('x3')];
  const eqs = applyLambda(equations, at(xs, 0), at(xs, 1), at(xs, 2));
  const [v1, v2, v3] = xs.map((x) => eqs.map((e) => diff(e, x)));
  const isZero = (e: Expr): boolean => simplify(e).key === S.Zero.key;
  const dotv = (a: Expr[], b: Expr[]): Expr => add(...a.map((ai, i) => mul(ai, at(b, i))));
  const vs = [defined(v1, 'v1'), defined(v2, 'v2'), defined(v3, 'v3')];
  if (vs.some((v) => isZero(add(...v)))) return false;
  const [a, b, c] = vs;
  return isZero(dotv(defined(a, 'a'), defined(b, 'b'))) && isZero(dotv(defined(b, 'b'), defined(c, 'c'))) && isZero(dotv(defined(c, 'c'), defined(a, 'a')));
}

/** Rotates the transformation equations by multiplying their coordinate column by the given matrix. */
export function rotationTransEquations(matrix: Matrix, equations: readonly ExprLike[]): Expr[] {
  return [...matMul(matrix, Matrix.col(...equations)).data];
}

/**
 * A coordinate system in 3-D space.
 *
 * @see SymPy `sympy.vector.coordsysrect.CoordSys3D`
 */
export class CoordSys3DNode extends CoordSysBase {
  readonly #name: string;
  readonly #form: TransformationForm;
  readonly #vectorNames: readonly string[];
  readonly #variableNames: readonly string[];
  readonly #baseVectors: readonly [BaseVectorNode, BaseVectorNode, BaseVectorNode];
  readonly #baseScalars: readonly [BaseScalarNode, BaseScalarNode, BaseScalarNode];
  readonly #transformationLambda: Equations;
  readonly #lame: readonly [Expr, Expr, Expr];
  #inverse: Equations | undefined;
  readonly #parent: CoordSys3DNode | undefined;
  readonly #root: CoordSys3DNode;
  readonly #rotation: Matrix;
  readonly #origin: VectorPointNode;

  /**
   * Constructs an instance of `CoordSys3DNode`.
   *
   * @param nameIn - Symbolic name.
   * @param opts - Settings described by {@link CoordSysOptions}.
   * @throws RangeError when a predefined transformation has a non-Cartesian parent or the transformation does not define orthogonal coordinates or the displacement depends on base scalars or a coordinate transformation is combined with a location or rotation matrix.
   * @throws TypeError when the displacement is not a vector or the parent is not a three-dimensional coordinate system or the rotation matrix has an unsupported type or the transformation has an unsupported type.
   */
  constructor(nameIn: string, opts: CoordSysOptions = {}) {
    const name = String(nameIn);
    let rotation = opts.rotationMatrix;
    let location = opts.location;
    let form: TransformationForm | undefined;
    const t = opts.transformation;
    if (t !== undefined) {
      if (location !== undefined || rotation !== undefined) throw new RangeError('specify either `transformation` or `location`/`rotation_matrix`');
      if (typeof t === 'string') form = { kind: 'name', name: t };
      else if (t instanceof LambdaNode) form = { kind: 'lambda', lambda: t };
      else if (typeof t === 'function') {
        const xs = [new Dummy('x1'), new Dummy('x2'), new Dummy('x3')];
        form = { kind: 'lambda', lambda: new LambdaNode([...xs, new TupleNode(t(at(xs, 0), at(xs, 1), at(xs, 2)).map(sympify))]) };
      } else if (isMatrixPair(t)) {
        rotation = t[0];
        location = t[1];
      } else if (Array.isArray(t)) {
        const [vars, eqs] = t;
        form = { kind: 'lambda', lambda: new LambdaNode([...tupleItems(vars), new TupleNode(tupleItems(eqs))]) };
      } else throw new TypeError(`transformation: wrong type ${typeof t}`);
    }
    if (rotation !== undefined && !(rotation instanceof Matrix)) throw new TypeError('rotation_matrix should be an ImmutableMatrix instance');
    const rot = rotation ?? Matrix.eye(3);
    const parent = opts.parent;
    if (parent !== undefined) {
      if (!(parent instanceof CoordSys3DNode)) throw new TypeError('parent should be a CoordSys3D/None');
      if (location === undefined) location = Vector.zero;
      else {
        if (!(location instanceof Vector)) throw new TypeError('location should be a Vector');
        if ([...freeSymbols(location)].some((x) => x instanceof BaseScalarNode)) throw new RangeError('location should not contain BaseScalars');
      }
    } else location = Vector.zero;
    const loc = location;
    form ??= { kind: 'rect', rotation: rot, location: loc };
    const parentArgs = parent === undefined ? [] : [parent];
    const args = form.kind === 'rect' ? [new TupleNode(form.rotation.data), form.location, ...parentArgs] : form.kind === 'lambda' ? [form.lambda, ...parentArgs] : parentArgs;
    super('CoordSys3D', args);
    this.#name = name;
    this.#form = form;
    this.#parent = parent;
    this.#root = parent === undefined ? this : parent.#root;
    this.#rotation = rot;
    this.#origin = parent === undefined ? new VectorPointNode(`${name}.origin`) : parent.origin.locateNew(`${name}.origin`, loc);

    let lame: Equations;
    switch (form.kind) {
      case 'rect': {
        const r = form.rotation;
        this.#transformationLambda = composeRotationAndTranslation(r, form.location, parent);
        const l = projections(form.location);
        lame = lameOf('cartesian');
        this.#inverse = (x, y, z) => {
          const v = matMul(r.inv(), Matrix.col(add(x, mul(-1, l[0])), add(y, mul(-1, l[1])), add(z, mul(-1, l[2]))));
          return [v.get(0, 0), v.get(1, 0), v.get(2, 0)];
        };
        break;
      }
      case 'name': {
        this.#transformationLambda = transformationOf(form.name);
        if (parent !== undefined && !parent.lameCoefficients().every((h) => h.key === S.One.key)) {
          throw new RangeError('Parent for pre-defined coordinate system should be Cartesian.');
        }
        lame = lameOf(form.name);
        this.#inverse = inverseOf(form.name);
        break;
      }
      case 'lambda': {
        if (!checkOrthogonality(form.lambda)) throw new RangeError('The transformation equation does not create orthogonal coordinate system');
        const l = form.lambda;
        this.#transformationLambda = (x, y, z) => applyLambda(l, x, y, z);
        lame = lameOfLambda(l);
        this.#inverse = undefined;
        break;
      }
    }

    let variableNames = opts.variableNames;
    if (variableNames === undefined) {
      if (form.kind === 'lambda') variableNames = ['x1', 'x2', 'x3'];
      else if (form.kind === 'name' && form.name === 'spherical') variableNames = ['r', 'theta', 'phi'];
      else if (form.kind === 'name' && form.name === 'cylindrical') variableNames = ['r', 'theta', 'z'];
      else variableNames = ['x', 'y', 'z'];
    }
    const vectorNames = opts.vectorNames ?? ['i', 'j', 'k'];
    checkStrings('vector_names', vectorNames);
    checkStrings('variable_names', variableNames);
    this.#vectorNames = [...vectorNames];
    this.#variableNames = [...variableNames];
    const vec = (i: number): BaseVectorNode => {
      const n = at(vectorNames, i);
      return new BaseVectorNode(i, this, `${n}_${name}`, `\\mathbf{\\hat{${n}}_{${name}}}`);
    };
    const sc = (i: number): BaseScalarNode => {
      const n = at(variableNames, i);
      return new BaseScalarNode(i, this, `${n}_${name}`, `\\mathbf{{${n}}_{${name}}}`);
    };
    this.#baseVectors = [vec(0), vec(1), vec(2)];
    this.#baseScalars = [sc(0), sc(1), sc(2)];
    this.#lame = lame(...this.#baseScalars);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const last = args[args.length - 1];
    const parent = last instanceof CoordSys3DNode ? last : undefined;
    const names = { vectorNames: this.#vectorNames, variableNames: this.#variableNames, parent };
    const f = this.#form;
    if (f.kind === 'rect') {
      const rows = at(args, 0).args;
      const rotation = Matrix.fromFunction(3, 3, (r, c) => at(rows, 3 * r + c));
      return new CoordSys3DNode(this.#name, { ...names, rotationMatrix: rotation, location: parent === undefined ? undefined : at(args, 1) });
    }
    if (f.kind === 'lambda') return new CoordSys3DNode(this.#name, { ...names, transformation: cast(at(args, 0), LambdaNode, 'Lambda') });
    return new CoordSys3DNode(this.#name, { ...names, transformation: f.name });
  }

  /**
   * Formats the system's name, coordinate transformation, and parent in constructor form.
   *
   * @param repr - Formatter for expression arguments.
   * @returns The constructor representation.
   */
  printRepr(repr: (e: Expr) => string): string {
    const f = this.#form;
    const rows = (m: Matrix): string => [0, 1, 2].map((r) => `[${[0, 1, 2].map((c) => repr(at(m.data, 3 * r + c))).join(', ')}]`).join(', ');
    const transformation = f.kind === 'rect' ? `Tuple(ImmutableDenseMatrix([${rows(f.rotation)}]), ${repr(f.location)})` : f.kind === 'name' ? `Str('${f.name}')` : repr(f.lambda);
    return `CoordSys3D(Str('${this.#name}'), ${transformation}${this.#parent === undefined ? '' : `, ${repr(this.#parent)}`})`;
  }

  /**
   * Identifies the coordinate system by name.
   *
   * @returns The system name.
   */
  override get sysName(): string {
    return this.#name;
  }
  /**
   * Lists the names of the basis vectors in axis order.
   *
   * @returns The three vector names.
   */
  override get vectorNames(): readonly string[] {
    return this.#vectorNames;
  }
  /**
   * Lists the coordinate scalar names in axis order.
   *
   * @returns The three scalar names.
   */
  override get variableNames(): readonly string[] {
    return this.#variableNames;
  }
  /**
   * Describes how the system is related to its parent.
   *
   * @returns A rotation and location, predefined transformation name, or coordinate lambda.
   */
  get transformation(): Expr | string {
    const f = this.#form;
    return f.kind === 'rect' ? new TupleNode([new TupleNode(f.rotation.data), f.location]) : f.kind === 'name' ? f.name : f.lambda;
  }
  /**
   * Tells whether the system was created without a parent, so that it is the root of its tree.
   *
   * @returns `true` when the system has no parent.
   * @example
   * ```ts
   * import { CoordSys3D } from '@symjs/symjs';
   *
   * const A = CoordSys3D('A');
   * A.isRoot; // => True
   * A.locateNew('B', A.i).isRoot; // => False
   * ```
   */
  override get isRoot(): boolean {
    return this.#parent === undefined;
  }
  /**
   * Identifies the coordinate system from which this one was constructed.
   *
   * @returns The parent coordinate system.
   * @throws RangeError when the system is a root (see `isRoot`).
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D._parent`
   */
  override get parentSystem(): CoordSys3DNode {
    if (this.#parent === undefined) throw new RangeError(`${this.#name} is a root coordinate system and has no parent`);
    return this.#parent;
  }
  /**
   * Follows the parent chain to the top-level coordinate system.
   *
   * @returns The root system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D._root`
   */
  override get rootSystem(): CoordSys3DNode {
    return this.#root;
  }
  /**
   * Describes the orientation of the axes relative to the parent system.
   *
   * @returns The parent-relative rotation matrix.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D._parent_rotation_matrix`
   */
  get parentRotationMatrix(): Matrix {
    return this.#rotation;
  }
  /**
   * Locates the coordinate system's zero point.
   *
   * @returns The system origin.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.origin`
   */
  get origin(): VectorPointNode {
    return this.#origin;
  }
  /**
   * Identifies the point from which positions in this system are measured.
   *
   * @returns The origin point.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.origin`
   */
  override get originPoint(): VectorPointNode {
    return this.#origin;
  }

  /**
   * Looks up a coordinate basis object by its assigned name.
   *
   * @param name - Symbolic name.
   * @returns The named base vector or scalar.
   * @throws TypeError when the coordinate system has no basis element of that name.
   */
  attr(name: string): BaseVectorNode | BaseScalarNode {
    const v = this.#vectorNames.indexOf(name);
    if (v >= 0) return at(this.#baseVectors, v);
    const s = this.#variableNames.indexOf(name);
    if (s >= 0) return at(this.#baseScalars, s);
    throw new TypeError(`'CoordSys3D' object has no attribute '${name}'`);
  }
  #vector(name: string): BaseVectorNode {
    const v = this.attr(name);
    if (!(v instanceof BaseVectorNode)) throw new TypeError(`${name} of ${this.#name} is a base scalar`);
    return v;
  }
  #scalar(name: string): BaseScalarNode {
    const v = this.attr(name);
    if (!(v instanceof BaseScalarNode)) throw new TypeError(`${name} of ${this.#name} is a base vector`);
    return v;
  }
  /**
   * Looks up the basis vector named `i`, normally the first axis.
   *
   * @returns The named base vector.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.i`
   */
  get i(): BaseVectorNode {
    return this.#vector('i');
  }
  /**
   * Looks up the basis vector named `j`, normally the second axis.
   *
   * @returns The named base vector.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.j`
   */
  get j(): BaseVectorNode {
    return this.#vector('j');
  }
  /**
   * Looks up the basis vector named `k`, normally the third axis.
   *
   * @returns The named base vector.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.k`
   */
  get k(): BaseVectorNode {
    return this.#vector('k');
  }
  /**
   * Looks up the coordinate scalar named `x`, normally the first coordinate.
   *
   * @returns The named base scalar.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.x`
   */
  get x(): BaseScalarNode {
    return this.#scalar('x');
  }
  /**
   * Looks up the coordinate scalar named `y`, normally the second coordinate.
   *
   * @returns The named base scalar.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.y`
   */
  get y(): BaseScalarNode {
    return this.#scalar('y');
  }
  /**
   * Looks up the coordinate scalar named `z`, normally the third coordinate.
   *
   * @returns The named base scalar.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.z`
   */
  get z(): BaseScalarNode {
    return this.#scalar('z');
  }

  /**
   * Iterates over the basis vectors of the coordinate system.
   *
   * @returns An iterator over the basis vectors.
   */
  [Symbol.iterator](): Iterator<BaseVectorNode> {
    return this.#baseVectors[Symbol.iterator]();
  }

  /**
   * Lists the coordinate basis vectors in axis order.
   *
   * @returns The vector fields.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.base_vectors`
   */
  override baseVectors(): readonly [BaseVectorNode, BaseVectorNode, BaseVectorNode] {
    return this.#baseVectors;
  }
  /**
   * Lists the basis scalar fields in chart order.
   *
   * @returns The coordinate fields.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.base_scalars`
   */
  override baseScalars(): readonly [BaseScalarNode, BaseScalarNode, BaseScalarNode] {
    return this.#baseScalars;
  }
  /**
   * Computes the Lamé scale factors along the three coordinate axes.
   *
   * @returns The three scale factors.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.lame_coefficients`
   */
  override lameCoefficients(): readonly [Expr, Expr, Expr] {
    return this.#lame;
  }
  /**
   * Expresses the parent coordinates in the base scalars of this system.
   *
   * @returns The parent coordinate triple.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.transformation_to_parent`
   */
  transformationToParent(): [Expr, Expr, Expr] {
    return this.#transformationLambda(...this.#baseScalars);
  }
  /**
   * Expresses this system's base scalars in the coordinates of its parent.
   *
   * @returns The transformed coordinate triple.
   * @throws RangeError when the coordinate system has no parent to transform from.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.transformation_from_parent`
   */
  transformationFromParent(): [Expr, Expr, Expr] {
    if (this.#parent === undefined) throw new RangeError('no parent coordinate system, use `transformation_from_parent_function()`');
    return this.transformationFromParentFunction()(...this.#parent.#baseScalars);
  }
  /**
   * Constructs the inverse coordinate map, solving the defining equations when necessary.
   *
   * @returns A function of the parent coordinates.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.transformation_from_parent_function`
   */
  transformationFromParentFunction(): Equations {
    return (this.#inverse ??= this.#calculateInverse());
  }
  /** SymPy _calculate_inv_trans_equations: the inverse of the transformation equations, by solve. */
  #calculateInverse(): Equations {
    const xs = [new Dummy('x1', { real: true }), new Dummy('x2', { real: true }), new Dummy('x3', { real: true })];
    const ys = [new Dummy('x'), new Dummy('y'), new Dummy('z')];
    const eqs = this.#transformationLambda(at(xs, 0), at(xs, 1), at(xs, 2));
    const sols = solveEquations(
      eqs.map((e, i) => add(e, mul(-1, at(ys, i)))),
      xs,
    );
    const sol = defined(sols[0], 'inverse transformation');
    return (a, b, c) => {
      const vals = [a, b, c];
      const r = sol.map((s) => s.subs(ys.map((y, i): [Expr, Expr] => [y, at(vals, i)])));
      return [at(r, 0), at(r, 1), at(r, 2)];
    };
  }
  /**
   * Inverts and simplifies the rotation relative to the parent system.
   *
   * @returns The inverse rotation matrix.
   */
  inverseRotationMatrix(): Matrix {
    return this.#rotation.inv().map((e) => simplify(e));
  }

  /**
   * Computes the direction cosine matrix mapping components in the other system to components in this
   * one.
   *
   * @param other - Coordinate system in whose basis to express the rotation.
   * @returns The relative rotation matrix.
   * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.rotation_matrix`
   */
  override rotationMatrix(other: CoordSysBase): Matrix {
    if (!(other instanceof CoordSys3DNode)) throw new TypeError(`${String(other)} is not a CoordSys3D`);
    if (other.key === this.key) return Matrix.eye(3);
    if (this.#parent !== undefined && other.key === this.#parent.key) return this.#rotation;
    if (other.#parent !== undefined && other.#parent.key === this.key) return other.#rotation.T;
    const [rootIndex, path] = treePath<CoordSys3DNode>(
      this,
      other,
      (s) => s.#parent,
      (s) => s.#root,
    );
    let result = Matrix.eye(3);
    for (let i = 0; i < rootIndex; i++) result = matMul(result, at(path, i).#rotation);
    for (let i = rootIndex + 1; i < path.length; i++) result = matMul(result, at(path, i).#rotation.T);
    return result;
  }

  /**
   * Measures the displacement from the reference point or system origin to this origin.
   *
   * @param other - Reference point or coordinate system origin.
   * @returns The relative position vector.
   * @throws TypeError when the reference is neither a vector point nor a coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.position_wrt`
   */
  override positionWrt(other: Expr): Expr {
    if (!(other instanceof VectorPointNode) && !(other instanceof CoordSysBase)) throw new TypeError(`${String(other)}is not a Point or CoordSys3D`);
    return this.#origin.positionWrt(other);
  }

  /**
   * Expresses this system's coordinate scalars in those of the other system.
   *
   * @param other - Coordinate system whose base scalars will appear in the expressions.
   * @returns A map of scalar substitutions.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.scalar_map`
   */
  override scalarMap(other: CoordSysBase): ExprMap<Expr> {
    const originCoords = cast(this.positionWrt(other), Vector, 'position').toMatrix(other).data;
    const relocated = other.baseScalars().map((x, i) => add(x, mul(-1, at(originCoords, i))));
    const vars = matMul(this.rotationMatrix(other), Matrix.col(...relocated));
    return new ExprMap<Expr>(this.#baseScalars.map((x, i) => [x, trigsimp(at(vars.data, i))]));
  }

  /**
   * Creates a child system with its origin displaced by the supplied position vector.
   *
   * @param name - Symbolic name.
   * @param position - Displacement from the reference point.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The translated coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.locate_new`
   */
  locateNew(name: string, position: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    return new CoordSys3DNode(name, { location: position, vectorNames: opts.vectorNames ?? this.#vectorNames, variableNames: opts.variableNames ?? this.#variableNames, parent: this });
  }

  /**
   * Creates a child system by applying one or more orienters in order.
   *
   * @param name - Symbolic name.
   * @param orienters - Rotations to apply in order.
   * @param location - Position of the new origin relative to the parent origin.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The oriented coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.orient_new`
   */
  orientNew(name: string, orienters: Orienter | readonly Orienter[], location?: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    const mat = (o: Orienter): Matrix => (o instanceof AxisOrienterNode ? o.rotationMatrix(this) : o.rotationMatrix());
    let final: Matrix;
    if (orienters instanceof Orienter) {
      // (SymPy: trigsimp makes the matrix canonical, so that equal orientations give equal systems)
      final = mat(orienters).map((e) => trigsimp(e));
    } else {
      final = Matrix.eye(3);
      for (const o of orienters) final = matMul(final, mat(o));
    }
    return new CoordSys3DNode(name, {
      rotationMatrix: final,
      vectorNames: opts.vectorNames ?? this.#vectorNames,
      variableNames: opts.variableNames ?? this.#variableNames,
      location,
      parent: this,
    });
  }

  /**
   * Rotates a child system through the given angle about the specified axis.
   *
   * @param name - Symbolic name.
   * @param angle - Rotation angle in radians.
   * @param axis - Vector defining the rotation axis.
   * @param location - Position of the new origin relative to the parent origin.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The oriented coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.orient_new_axis`
   * @example
   * ```ts
   * import { CoordSys3D, ex, express } from '@symjs/symjs';
   *
   * const A = CoordSys3D('A');
   * const B = A.orientNewAxis('B', ex`pi/2`, A.k);
   * express(B.i, A); // => A.j
   * ```
   */
  orientNewAxis(name: string, angle: ExprLike, axis: Expr, location?: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    return this.orientNew(name, new AxisOrienterNode(angle, axis), location, opts);
  }

  /**
   * Orients a child system using three successive rotations about body-fixed axes.
   *
   * @param name - Symbolic name.
   * @param angle1 - First rotation angle in radians.
   * @param angle2 - Second rotation angle in radians.
   * @param angle3 - Third rotation angle in radians.
   * @param rotationOrder - Order of the rotation axes.
   * @param location - Position of the new origin relative to the parent origin.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The child coordinate system after the body-fixed rotations.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.orient_new_body`
   */
  orientNewBody(name: string, angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotationOrder: string, location?: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    return this.orientNew(name, BodyOrienterFn(angle1, angle2, angle3, rotationOrder), location, opts);
  }

  /**
   * Orients a child system using three successive rotations about space-fixed axes.
   *
   * @param name - Symbolic name.
   * @param angle1 - First rotation angle in radians.
   * @param angle2 - Second rotation angle in radians.
   * @param angle3 - Third rotation angle in radians.
   * @param rotationOrder - Order of the rotation axes.
   * @param location - Position of the new origin relative to the parent origin.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The child coordinate system after the space-fixed rotations.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.orient_new_space`
   */
  orientNewSpace(name: string, angle1: ExprLike, angle2: ExprLike, angle3: ExprLike, rotationOrder: string, location?: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    return this.orientNew(name, SpaceOrienterFn(angle1, angle2, angle3, rotationOrder), location, opts);
  }

  /**
   * Defines a child coordinate system using the supplied quaternion rotation.
   *
   * @param name - Symbolic name.
   * @param q0 - Scalar quaternion component.
   * @param q1 - First vector quaternion component.
   * @param q2 - Second vector quaternion component.
   * @param q3 - Third vector quaternion component.
   * @param location - Position of the new origin relative to the parent origin.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The oriented coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.orient_new_quaternion`
   */
  orientNewQuaternion(name: string, q0: ExprLike, q1: ExprLike, q2: ExprLike, q3: ExprLike, location?: Expr, opts: NamesOptions = {}): CoordSys3DNode {
    return this.orientNew(name, QuaternionOrienterFn(q0, q1, q2, q3), location, opts);
  }

  /**
   * Creates a child coordinate system related by the specified transformation.
   *
   * @param name - Symbolic name.
   * @param transformation - Coordinate transformation to the parent system.
   * @param opts - Settings described by {@link NamesOptions}.
   * @returns The new coordinate system.
   * @see SymPy `sympy.vector.coordsysrect.CoordSys3D.create_new`
   */
  createNew(name: string, transformation: Transformation, opts: NamesOptions = {}): CoordSys3DNode {
    return new CoordSys3DNode(name, { parent: this, transformation, ...opts });
  }

  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.#name;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    return this.#name;
  }
  protected override computeKey(): string {
    const f = this.#form;
    const kind = f.kind === 'name' ? `name=${f.name}` : f.kind;
    return `CoordSys3D(${JSON.stringify(this.#name)};${kind};${this.#vectorNames.join(',')};${this.#variableNames.join(',')};${this.args.map((a) => a.key).join(',')})`;
  }
}


/** SymPy _compose_rotation_and_translation: the rotation, then the translation by the location in the parent. */
function composeRotationAndTranslation(rot: Matrix, translation: Expr, parent: CoordSys3DNode | undefined): Equations {
  const r: Equations = (x, y, z) => {
    const v = rotationTransEquations(rot, [x, y, z]);
    return [at(v, 0), at(v, 1), at(v, 2)];
  };
  if (parent === undefined) return r;
  const [dx, dy, dz] = parent.baseVectors().map((i) => cast(translation, Vector, 'location').dot(i));
  return (x, y, z) => {
    const [a, b, c] = r(x, y, z);
    return [add(a, defined(dx, 'dx')), add(b, defined(dy, 'dy')), add(c, defined(dz, 'dz'))];
  };
}

const BodyOrienterFn = (a: ExprLike, b: ExprLike, c: ExprLike, order: string): Orienter => new BodyOrienterNode(a, b, c, order);
const SpaceOrienterFn = (a: ExprLike, b: ExprLike, c: ExprLike, order: string): Orienter => new SpaceOrienterNode(a, b, c, order);
const QuaternionOrienterFn = (a: ExprLike, b: ExprLike, c: ExprLike, d: ExprLike): Orienter => new QuaternionOrienterNode(a, b, c, d);

/**
 * Constructs a three-dimensional coordinate system with its origin, basis vectors and coordinate
 * scalars.
 *
 * @param name - Symbolic name.
 * @param transformationOrOpts - Coordinate transformation or coordinate-system construction options.
 * @param opts - Settings described by {@link CoordSysOptions}.
 * @returns The resulting `CoordSys3D` expression.
 * @throws RangeError when a predefined transformation has a non-Cartesian parent or the transformation does not define orthogonal coordinates or the displacement depends on base scalars or a coordinate transformation is combined with a location or rotation matrix.
 * @throws TypeError when the displacement is not a vector or the parent is not a three-dimensional coordinate system or the rotation matrix has an unsupported type or the transformation has an unsupported type.
 * @see SymPy `sympy.vector.coordsysrect.CoordSys3D`
 */
export const CoordSys3D = /* @__PURE__ */ callableClass(CoordSys3DNode, (name: string, transformationOrOpts?: Transformation | CoordSysOptions, opts: CoordSysOptions = {}): CoordSys3DNode => {
  if (transformationOrOpts === undefined) return new CoordSys3DNode(name, opts);
  if (isOptions(transformationOrOpts)) return new CoordSys3DNode(name, { ...transformationOrOpts, ...opts });
  return new CoordSys3DNode(name, { ...opts, transformation: transformationOrOpts });
});
export type CoordSys3D = CoordSys3DNode;

/** A plain options object (not a transformation). */
function isOptions(x: Transformation | CoordSysOptions): x is CoordSysOptions {
  return typeof x === 'object' && !Array.isArray(x) && !(x instanceof ExtensionExpr) && !(x instanceof Sym);
}
