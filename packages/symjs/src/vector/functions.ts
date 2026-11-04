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
 * SymPy express(expr, system, system2=None, variables=False): a vector,
 * dyadic or scalar re-expressed in the coordinate system (a dyadic's
 * second vectors in system2). With `variables`, the base scalars of other
 * systems are also expressed in those of system.
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
 * SymPy directional_derivative(field, direction_vector): the directional
 * derivative of a scalar or vector field along a vector, in the coordinate
 * system of the field.
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
 * SymPy laplacian(expr): the Laplacian of a scalar or vector field in the
 * base scalars of its coordinate system.
 */
export function laplacian(exprIn: ExprLike): Expr {
  const expr = sympify(exprIn);
  if (expr instanceof Vector) return doit(add(gradient(divergence(expr)), mul(-1, curl(curl(expr)))));
  return doit(divergence(gradient(expr, { doit: false }), { doit: false }));
}

/** SymPy is_conservative(field): the curl of the vector field vanishes. */
export function isConservative(field: Expr): boolean {
  if (!(field instanceof Vector)) throw new TypeError('field should be a Vector');
  if (field instanceof VectorZeroNode) return true;
  return simplify(curl(field)) instanceof VectorZeroNode;
}

/** SymPy is_solenoidal(field): the divergence of the vector field vanishes. */
export function isSolenoidal(field: Expr): boolean {
  if (!(field instanceof Vector)) throw new TypeError('field should be a Vector');
  if (field instanceof VectorZeroNode) return true;
  return simplify(divergence(field)).key === S.Zero.key;
}

/**
 * SymPy scalar_potential(field, coord_sys): the scalar potential of a
 * conservative field in the coordinate system (without the constant).
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
 * SymPy scalar_potential_difference(field, coord_sys, point1, point2): the
 * potential at point2 minus the potential at point1, of a scalar field or
 * of the scalar potential of a conservative vector field.
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
 * SymPy matrix_to_vector(matrix, system): the vector whose measure numbers
 * along the base vectors of system are the entries of the matrix.
 */
export function matrixToVector(matrix: Matrix, system: CoordSysBase): Expr {
  let out: Expr = Vector.zero;
  const vects = system.baseVectors();
  matrix.data.forEach((x, i) => {
    out = add(out, mul(x, at(vects, i)));
  });
  return out;
}

/** The options of orthogonalize (SymPy keyword arguments). */
export interface OrthogonalizeOptions {
  /** Normalize the vectors (SymPy orthonormal=True). */
  readonly orthonormal?: boolean;
}

/**
 * SymPy orthogonalize(*vlist, orthonormal=False): the orthogonal (or
 * orthonormal) vectors of independent vectors by the Gram-Schmidt process.
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
