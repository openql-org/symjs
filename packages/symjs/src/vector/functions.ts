// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/functions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.functions: re-expression of vectors, dyadics and
 * scalar fields in another coordinate system (express, matrix_to_vector),
 * the field functions (directional_derivative, laplacian, is_conservative,
 * is_solenoidal, scalar_potential, scalar_potential_difference) and the
 * Gram-Schmidt orthogonalization.
 */

import { Expr, S, isNum } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { at, cast } from '../core/guard';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { doit } from '../calculus/doit';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import type { Matrix } from '../matrices/matrix';
import { CoordSysBase, matMul, vectorHooks } from './basisdependent';
import type { ExpressOptions } from './basisdependent';
import { Vector, VectorZeroNode, coordSystems } from './vector';
import { Dyadic } from './dyadic';
import { curl, divergence, gradient } from './operators';
import { VectorPointNode } from './point';

const isZeroExpr = (e: Expr): boolean => (isNum(e) && e.isZero) || e instanceof VectorZeroNode;

/** The substitution of the base scalars of the systems (other than system) by their expressions in system. */
function scalarSubstitution(e: Expr, system: CoordSysBase): [Expr, Expr][] {
  const pairs: [Expr, Expr][] = [];
  for (const f of coordSystems(e)) {
    if (f.key === system.key) continue;
    for (const [k, v] of f.scalarMap(system)) pairs.push([k, v]);
  }
  return pairs;
}

/**
 * Resolves a vector, dyadic, or scalar in the specified coordinates, optionally transforming base
 * scalars and choosing a second basis for a dyadic.
 *
 * @param exprIn - Expression to transform.
 * @param system - Coordinate system in which to express components.
 * @param system2 - Coordinate system for the second basis vector of a dyadic.
 * @param opts - Settings described by {@link ExpressOptions}.
 * @returns A vector, dyadic or scalar re-expressed in the coordinate system (a dyadic's second vectors in system2).
 * @throws RangeError when a second coordinate system is supplied for a scalar or vector.
 * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
 * @see SymPy `sympy.vector.functions.express`
 * @example
 * ```ts
 * import { CoordSys3D, ex, express } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const B = R.orientNewAxis('B', ex`q`, R.k);
 * express(B.i, R); // => (cos(q))*R.i + (sin(q))*R.j
 * ```
 */
export function express(exprIn: ExprLike, system: CoordSysBase, system2?: CoordSysBase, opts: ExpressOptions = {}): Expr {
  let expr = sympify(exprIn);
  if (isZeroExpr(expr)) return expr;
  if (!(system instanceof CoordSysBase)) throw new TypeError('system should be a CoordSys3D instance');
  const variables = opts.variables === true;
  if (expr instanceof Vector) {
    if (system2 !== undefined) throw new RangeError('system2 should not be provided for Vectors');
    if (variables) expr = subs(expr, scalarSubstitution(expr, system));
    let out: Expr = Vector.zero;
    for (const [x, part] of cast(expr, Vector, 'vector').separate()) {
      if (x.key === system.key) out = add(out, part);
      else {
        const sys = asSystem(x);
        const temp = matMul(system.rotationMatrix(sys), asVector(part).toMatrix(sys));
        out = add(out, matrixToVector(temp, system));
      }
    }
    return out;
  }
  if (expr instanceof Dyadic) {
    const second = system2 ?? system;
    if (!(second instanceof CoordSysBase)) throw new TypeError('system2 should be a CoordSys3D instance');
    let out: Expr = Dyadic.zero;
    for (const [k, v] of expr.components) {
      const a = asVector(express(at(k.args, 0), system, undefined, opts));
      out = add(out, mul(express(v, system, undefined, opts), a.outer(express(at(k.args, 1), second, undefined, opts))));
    }
    return out;
  }
  if (system2 !== undefined) throw new RangeError('system2 should not be provided for Vectors');
  if (variables) return subs(expr, scalarSubstitution(expr, system));
  return expr;
}

const asVector = (e: Expr): Vector => cast(e, Vector, 'vector');
const asSystem = (e: Expr): CoordSysBase => cast(e, CoordSysBase, 'CoordSys3D');

/**
 * Differentiates a scalar or vector field along a direction in the field's coordinates.
 *
 * @param fieldIn - Scalar or vector field on the region.
 * @param directionVector - Vector specifying the differentiation direction.
 * @returns The directional derivative.
 * @see SymPy `sympy.vector.functions.directional_derivative`
 * @example
 * ```ts
 * import { CoordSys3D, directionalDerivative } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const direction = R.i.mul(3).add(R.j.mul(4)).add(R.k);
 * directionalDerivative(R.x.mul(R.y).mul(R.z), direction); // => R.x*R.y + 4*R.x*R.z + 3*R.y*R.z
 * ```
 */
export function directionalDerivative(fieldIn: ExprLike, directionVector: Expr): Expr {
  let field = sympify(fieldIn);
  const systems = coordSystems(field);
  const cs = systems[0];
  if (cs === undefined) return field instanceof Vector ? Vector.zero : S.Zero;
  field = express(field, cs, undefined, { variables: true });
  const [i, j, k] = cs.baseVectors();
  const [x, y, z] = cs.baseScalars();
  const dir = asVector(directionVector);
  let out = mul(dir.dot(i), diff(field, x));
  out = add(out, mul(dir.dot(j), diff(field, y)));
  out = add(out, mul(dir.dot(k), diff(field, z)));
  if (isNum(out) && out.isZero && field instanceof Vector) out = Vector.zero;
  return out;
}

/**
 * Computes the Laplacian in the field's base coordinates.
 *
 * @param exprIn - Expression to transform.
 * @returns The scalar or vector Laplacian.
 * @see SymPy `sympy.vector.functions.laplacian`
 * @example
 * ```ts
 * import { CoordSys3D, laplacian } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * laplacian(R.x.pow(2).mul(R.y.pow(5)).mul(R.z)); // => 20*R.x**2*R.y**3*R.z + 2*R.y**5*R.z
 * ```
 */
export function laplacian(exprIn: ExprLike): Expr {
  const expr = sympify(exprIn);
  if (expr instanceof Vector) return doit(add(gradient(divergence(expr)), mul(-1, curl(curl(expr)))));
  return doit(divergence(gradient(expr, { doit: false }), { doit: false }));
}

/**
 * Tests whether the vector field has vanishing curl.
 *
 * @param field - Field to evaluate or differentiate.
 * @returns Whether the curl vanishes.
 * @throws TypeError when a field or vector operand is not a vector.
 * @see SymPy `sympy.vector.functions.is_conservative`
 * @example
 * ```ts
 * import { CoordSys3D, isConservative } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * isConservative(R.z.mul(R.j)); // => False
 * ```
 */
export function isConservative(field: Expr): boolean {
  if (!(field instanceof Vector)) throw new TypeError('field should be a Vector');
  if (field instanceof VectorZeroNode) return true;
  return simplify(curl(field)) instanceof VectorZeroNode;
}

/**
 * Tests whether the vector field has vanishing divergence.
 *
 * @param field - Field to evaluate or differentiate.
 * @returns Whether the divergence vanishes.
 * @throws TypeError when a field or vector operand is not a vector.
 * @see SymPy `sympy.vector.functions.is_solenoidal`
 * @example
 * ```ts
 * import { CoordSys3D, isSolenoidal } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * isSolenoidal(R.y.mul(R.j)); // => False
 * ```
 */
export function isSolenoidal(field: Expr): boolean {
  if (!(field instanceof Vector)) throw new TypeError('field should be a Vector');
  if (field instanceof VectorZeroNode) return true;
  return simplify(divergence(field)).key === S.Zero.key;
}

/**
 * Recovers a potential for the conservative field in the chosen coordinates, omitting the additive
 * constant.
 *
 * @param field - Field to evaluate or differentiate.
 * @param coordSys - Coordinate system defining the basis.
 * @returns The scalar potential.
 * @throws RangeError when the field is not conservative.
 * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
 * @see SymPy `sympy.vector.functions.scalar_potential`
 * @example
 * ```ts
 * import { CoordSys3D, scalarPotential } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * scalarPotential(R.k, R); // => R.z
 * ```
 */
export function scalarPotential(field: Expr, coordSys: CoordSysBase): Expr {
  if (!isConservative(field)) throw new RangeError('Field is not conservative');
  if (field instanceof VectorZeroNode) return S.Zero;
  if (!(coordSys instanceof CoordSysBase)) throw new TypeError('coord_sys must be a CoordSys3D');
  const f = asVector(express(field, coordSys, undefined, { variables: true }));
  const dims = coordSys.baseVectors();
  const scalars = coordSys.baseScalars();
  let temp = integrate(f.dot(dims[0]), scalars[0]);
  for (let i = 1; i < 3; i++) {
    const s = at(scalars, i);
    const partial = add(f.dot(at(dims, i)), mul(-1, diff(temp, s)));
    temp = add(temp, integrate(partial, s));
  }
  return temp;
}

/**
 * Subtracts the potential at the first point from that at the second, deriving the potential for a
 * conservative vector field.
 *
 * @param fieldIn - Scalar or vector field on the region.
 * @param coordSys - Coordinate system defining the basis.
 * @param point1 - Starting point for the potential difference.
 * @param point2 - Ending point for the potential difference.
 * @returns The potential difference.
 * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
 * @see SymPy `sympy.vector.functions.scalar_potential_difference`
 * @example
 * ```ts
 * import { CoordSys3D, scalarPotentialDifference } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const p = R.origin.locateNew('P', R.i.mul(3).add(R.j).add(R.k.mul(2)));
 * const field = R.i.mul(R.x.mul(R.y).mul(4)).add(R.j.mul(R.x.pow(2).mul(2)));
 * scalarPotentialDifference(field, R, R.origin, p); // => 18
 * ```
 */
export function scalarPotentialDifference(fieldIn: ExprLike, coordSys: CoordSysBase, point1: VectorPointNode, point2: VectorPointNode): Expr {
  if (!(coordSys instanceof CoordSysBase)) throw new TypeError('coord_sys must be a CoordSys3D');
  const field = sympify(fieldIn);
  const fn = field instanceof Vector ? scalarPotential(field, coordSys) : field;
  const origin = cast(coordSys.originPoint, VectorPointNode, 'Point');
  const p1 = asVector(express(point1.positionWrt(origin), coordSys, undefined, { variables: true }));
  const p2 = asVector(express(point2.positionWrt(origin), coordSys, undefined, { variables: true }));
  const scalars = coordSys.baseScalars();
  const vectors = coordSys.baseVectors();
  const at1 = scalars.map((s, i): [Expr, Expr] => [s, asVector(at(vectors, i)).dot(p1)]);
  const at2 = scalars.map((s, i): [Expr, Expr] => [s, asVector(at(vectors, i)).dot(p2)]);
  return add(subs(fn, at2), mul(-1, subs(fn, at1)));
}

/**
 * Uses the matrix entries as components along the system's basis vectors.
 *
 * @param matrix - Column of components in basis order.
 * @param system - Coordinate system in which to express components.
 * @returns The reconstructed vector.
 * @see SymPy `sympy.vector.functions.matrix_to_vector`
 * @example
 * ```ts
 * import { CoordSys3D, Matrix, matrixToVector } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * matrixToVector(Matrix.of([[1], [2], [3]]), R); // => R.i + 2*R.j + 3*R.k
 * ```
 */
export function matrixToVector(matrix: Matrix, system: CoordSysBase): Expr {
  let out: Expr = Vector.zero;
  const vects = system.baseVectors();
  matrix.data.forEach((x, i) => {
    out = add(out, mul(x, at(vects, i)));
  });
  return out;
}

/** The options of orthogonalize. */
export interface OrthogonalizeOptions {
  /** Normalize the vectors. */
  readonly orthonormal?: boolean;
}

/**
 * Applies Gram–Schmidt to independent vectors, optionally normalizing each result.
 *
 * @param args - Linearly independent vectors and optional `orthonormal` flag for unit output vectors.
 * @returns The orthogonal or orthonormal vectors.
 * @throws RangeError when the vectors are linearly dependent.
 * @throws TypeError when a field or vector operand is not a vector.
 * @see SymPy `sympy.vector.functions.orthogonalize`
 * @example
 * ```ts
 * import { CoordSys3D, orthogonalize } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const v = R.i.add(R.j.mul(2)), w = R.i.mul(2).add(R.j.mul(3));
 * orthogonalize(v, w); // => [R.i + 2*R.j, 2/5*R.i + (-1/5)*R.j]
 * ```
 */
export function orthogonalize(...args: (Expr | OrthogonalizeOptions)[]): Expr[] {
  const last = args[args.length - 1];
  const opts: OrthogonalizeOptions = last !== undefined && !(last instanceof Expr) ? last : {};
  const vlist = args.filter((a): a is Expr => a instanceof Expr);
  if (!vlist.every((v) => v instanceof Vector)) throw new TypeError('Each element must be of Type Vector');
  const ortho: Vector[] = [];
  vlist.forEach((v, i) => {
    let term: Expr = v;
    for (let j = 0; j < i; j++) term = term.sub(at(ortho, j).projection(v));
    const t = asVector(term);
    if (t.equals(Vector.zero)) throw new RangeError('Vector set not linearly independent');
    ortho.push(t);
  });
  return opts.orthonormal === true ? ortho.map((v) => v.normalize()) : ortho;
}

vectorHooks.express = express;
vectorHooks.laplacian = laplacian;
vectorHooks.directionalDerivative = directionalDerivative;
