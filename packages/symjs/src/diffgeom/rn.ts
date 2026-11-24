// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Cartesian, polar, cylindrical and spherical charts on Euclidean space. */
import { Sym } from '../core/nodes';
import { sqrt, add, mul } from '../core/ops';
import { atan2 } from '../functions/special/special';
import { acos, sin, cos } from '../functions/elementary/elementary';
import { Manifold, Patch, CoordSystem } from './diffgeom';
import type { CoordinateRelations } from './diffgeom';

const x = new Sym('x', { real: true }),
  y = new Sym('y', { real: true }),
  z = new Sym('z', { real: true });
const rho = new Sym('rho', { nonnegative: true }),
  theta = new Sym('theta', { nonnegative: true });
const r = new Sym('r', { nonnegative: true }),
  psi = new Sym('psi', { nonnegative: true }),
  phi = new Sym('phi', { nonnegative: true });
const plane = new Manifold('R^2', 2);
const origin2 = new Patch('origin', plane);
/**
 * Coordinate changes between the Cartesian and polar charts on the Euclidean plane.
 *
 * @see SymPy `sympy.diffgeom.rn.relations_2d`
 */
export const relations2d: CoordinateRelations = new Map([
  [
    ['rectangular', 'polar'],
    [
      [x, y],
      [sqrt(add(x.pow(2), y.pow(2))), atan2(y, x)],
    ],
  ],
  [
    ['polar', 'rectangular'],
    [
      [rho, theta],
      [mul(rho, cos(theta)), mul(rho, sin(theta))],
    ],
  ],
]);
const rectangular2 = new CoordSystem('rectangular', origin2, [x, y], relations2d);
const polar = new CoordSystem('polar', origin2, [rho, theta], relations2d);
/**
 * The Cartesian chart on the Euclidean plane with its coordinate fields and dual basis.
 *
 * @see SymPy `sympy.diffgeom.rn.R2_r`
 * @remarks SymPy prints the coordinate symbols as `(x, y)`.
 * @example
 * ```ts
 * import { R2R } from '@symjs/symjs/diffgeom';
 *
 * R2R.symbols; // => [x, y]
 * ```
 */
export const R2R = Object.assign(rectangular2, {
  x: rectangular2.baseScalar(0),
  y: rectangular2.baseScalar(1),
  eX: rectangular2.baseVector(0),
  eY: rectangular2.baseVector(1),
  dx: rectangular2.baseOneform(0),
  dy: rectangular2.baseOneform(1),
});
/**
 * The polar chart on the Euclidean plane with its radial and angular fields.
 *
 * @see SymPy `sympy.diffgeom.rn.R2_p`
 * @remarks SymPy prints the coordinate symbols as `(rho, theta)`.
 * @example
 * ```ts
 * import { R2P } from '@symjs/symjs/diffgeom';
 *
 * R2P.symbols; // => [rho, theta]
 * ```
 */
export const R2P = Object.assign(polar, {
  r: polar.baseScalar(0),
  theta: polar.baseScalar(1),
  eR: polar.baseVector(0),
  eTheta: polar.baseVector(1),
  dr: polar.baseOneform(0),
  dtheta: polar.baseOneform(1),
});
const fields2 = {
  x: R2R.x,
  y: R2R.y,
  r: R2P.r,
  theta: R2P.theta,
  eX: R2R.eX,
  eY: R2R.eY,
  eR: R2P.eR,
  eTheta: R2P.eTheta,
  dx: R2R.dx,
  dy: R2R.dy,
  dr: R2P.dr,
  dtheta: R2P.dtheta,
};
/**
 * The Euclidean plane with its Cartesian and polar coordinate fields.
 *
 * @see SymPy `sympy.diffgeom.rn.R2`
 * @example
 * ```ts
 * import { R2 } from '@symjs/symjs/diffgeom';
 *
 * R2.dim; // => 2
 * ```
 */
export const R2 = Object.assign(plane, fields2);
/**
 * The origin patch of the Euclidean plane with Cartesian and polar coordinate fields.
 *
 * @see SymPy `sympy.diffgeom.rn.R2_origin`
 * @example
 * ```ts
 * import { R2Origin } from '@symjs/symjs/diffgeom';
 *
 * R2Origin.dim; // => 2
 * ```
 */
export const R2Origin = Object.assign(origin2, fields2);

/**
 * Three-dimensional Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.R3`
 * @example
 * ```ts
 * import { R3 } from '@symjs/symjs/diffgeom';
 *
 * R3.dim; // => 3
 * ```
 */
export const R3: Manifold = new Manifold('R^3', 3);
/**
 * The patch containing the origin of three-dimensional Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.R3_origin`
 * @example
 * ```ts
 * import { R3Origin } from '@symjs/symjs/diffgeom';
 *
 * R3Origin.dim; // => 3
 * ```
 */
export const R3Origin: Patch = new Patch('origin', R3);
const radius = sqrt(add(x.pow(2), y.pow(2), z.pow(2)));
/**
 * Coordinate changes between the Cartesian, cylindrical and spherical charts of Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.relations_3d`
 */
export const relations3d: CoordinateRelations = new Map([
  [
    ['rectangular', 'cylindrical'],
    [
      [x, y, z],
      [sqrt(add(x.pow(2), y.pow(2))), atan2(y, x), z],
    ],
  ],
  [
    ['cylindrical', 'rectangular'],
    [
      [rho, psi, z],
      [mul(rho, cos(psi)), mul(rho, sin(psi)), z],
    ],
  ],
  [
    ['rectangular', 'spherical'],
    [
      [x, y, z],
      [radius, acos(z.div(radius)), atan2(y, x)],
    ],
  ],
  [
    ['spherical', 'rectangular'],
    [
      [r, theta, phi],
      [mul(r, sin(theta), cos(phi)), mul(r, sin(theta), sin(phi)), mul(r, cos(theta))],
    ],
  ],
  [
    ['cylindrical', 'spherical'],
    [
      [rho, psi, z],
      [sqrt(add(rho.pow(2), z.pow(2))), acos(z.div(sqrt(add(rho.pow(2), z.pow(2))))), psi],
    ],
  ],
  [
    ['spherical', 'cylindrical'],
    [
      [r, theta, phi],
      [mul(r, sin(theta)), phi, mul(r, cos(theta))],
    ],
  ],
]);
const rectangular3 = new CoordSystem('rectangular', R3Origin, [x, y, z], relations3d);
const cylindrical = new CoordSystem('cylindrical', R3Origin, [rho, psi, z], relations3d);
const spherical = new CoordSystem('spherical', R3Origin, [r, theta, phi], relations3d);
/**
 * The Cartesian chart on three-dimensional Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.R3_r`
 * @remarks SymPy prints the coordinate symbols as `(x, y, z)`.
 * @example
 * ```ts
 * import { R3R } from '@symjs/symjs/diffgeom';
 *
 * R3R.symbols; // => [x, y, z]
 * ```
 */
export const R3R = Object.assign(rectangular3, {
  x: rectangular3.baseScalar(0),
  y: rectangular3.baseScalar(1),
  z: rectangular3.baseScalar(2),
  eX: rectangular3.baseVector(0),
  eY: rectangular3.baseVector(1),
  eZ: rectangular3.baseVector(2),
  dx: rectangular3.baseOneform(0),
  dy: rectangular3.baseOneform(1),
  dz: rectangular3.baseOneform(2),
});
/**
 * The cylindrical chart on three-dimensional Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.R3_c`
 * @remarks SymPy prints the coordinate symbols as `(rho, psi, z)`.
 * @example
 * ```ts
 * import { R3C } from '@symjs/symjs/diffgeom';
 *
 * R3C.symbols; // => [rho, psi, z]
 * ```
 */
export const R3C = Object.assign(cylindrical, {
  rho: cylindrical.baseScalar(0),
  psi: cylindrical.baseScalar(1),
  z: cylindrical.baseScalar(2),
  eRho: cylindrical.baseVector(0),
  ePsi: cylindrical.baseVector(1),
  eZ: cylindrical.baseVector(2),
  drho: cylindrical.baseOneform(0),
  dpsi: cylindrical.baseOneform(1),
  dz: cylindrical.baseOneform(2),
});
/**
 * The spherical chart on three-dimensional Euclidean space.
 *
 * @see SymPy `sympy.diffgeom.rn.R3_s`
 * @remarks SymPy prints the coordinate symbols as `(r, theta, phi)`.
 * @example
 * ```ts
 * import { R3S } from '@symjs/symjs/diffgeom';
 *
 * R3S.symbols; // => [r, theta, phi]
 * ```
 */
export const R3S = Object.assign(spherical, {
  r: spherical.baseScalar(0),
  theta: spherical.baseScalar(1),
  phi: spherical.baseScalar(2),
  eR: spherical.baseVector(0),
  eTheta: spherical.baseVector(1),
  ePhi: spherical.baseVector(2),
  dr: spherical.baseOneform(0),
  dtheta: spherical.baseOneform(1),
  dphi: spherical.baseOneform(2),
});
