// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Differential geometry, available only through `@symjs/symjs/diffgeom`. */
import './core';
import './calculus/doit';

export {
  Manifold,
  Patch,
  CoordSystem,
  CoordinateSymbol,
  Point,
  BaseScalarField,
  BaseVectorField,
  contravariantOrder,
  covariantOrder,
  Commutator,
  Differential,
  TensorProduct,
  WedgeProduct,
  LieDerivative,
  vectorsInBasis,
  BaseCovarDerivativeOp,
  CovarDerivativeOp,
  intcurveSeries,
  intcurveDiffequ,
  twoformToMatrix,
  metricToChristoffel1st,
  metricToChristoffel2nd,
  metricToRiemannComponents,
  metricToRicciComponents,
} from './diffgeom/diffgeom';
export { relations2d, R2R, R2P, R2, R2Origin, R3, R3Origin, relations3d, R3R, R3C, R3S } from './diffgeom/rn';
export type { CoordinateRelation, CoordinateRelations } from './diffgeom/diffgeom';
