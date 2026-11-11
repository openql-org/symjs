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
export const R2R = Object.assign(rectangular2, {
  x: rectangular2.baseScalar(0),
  y: rectangular2.baseScalar(1),
  eX: rectangular2.baseVector(0),
  eY: rectangular2.baseVector(1),
  dx: rectangular2.baseOneform(0),
  dy: rectangular2.baseOneform(1),
});
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
export const R2 = Object.assign(plane, fields2);
export const R2Origin = Object.assign(origin2, fields2);

export const R3: Manifold = new Manifold('R^3', 3);
export const R3Origin: Patch = new Patch('origin', R3);
const radius = sqrt(add(x.pow(2), y.pow(2), z.pow(2)));
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
