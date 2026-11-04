// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/vector`: vector calculus in 3-D
 * coordinate systems (SymPy sympy.vector: CoordSys3D with its base vectors
 * and scalars, vectors and dyadics, the Del operator, gradient, divergence
 * and curl, re-expression in other systems, orienters, points, and
 * integrals over parametric and implicit regions).
 */

// every entry point brings the core with its registrations
import './core';

export { BasisDependent } from './vector/basisdependent';
export type { BasisFamily, ExpressOptions } from './vector/basisdependent';
export { VectorKind } from './vector/kind';
export type { VectorKindNode } from './vector/kind';
export { BaseScalar } from './vector/scalar';
export type { BaseScalarNode } from './vector/scalar';
export { Vector, BaseVector, VectorAdd, VectorMul, VectorZero, Cross, Dot } from './vector/vector';
export type { BaseVectorNode, VectorAddNode, VectorMulNode, VectorZeroNode, CrossNode, DotNode, ProjectionOptions } from './vector/vector';
export { cross, dot } from './matrices/linalg';
export { Dyadic, BaseDyadic, DyadicAdd, DyadicMul, DyadicZero } from './vector/dyadic';
export type { BaseDyadicNode, DyadicAddNode, DyadicMulNode, DyadicZeroNode } from './vector/dyadic';
export { Orienter, ThreeAngleOrienter, AxisOrienter, BodyOrienter, SpaceOrienter, QuaternionOrienter } from './vector/orienters';
export type { AxisOrienterNode, BodyOrienterNode, SpaceOrienterNode, QuaternionOrienterNode } from './vector/orienters';
export { VectorPoint } from './vector/point';
export type { VectorPointNode } from './vector/point';
export { CoordSys3D } from './vector/coordsysrect';
export type { CoordSys3DNode, CoordSysOptions, NamesOptions, Transformation } from './vector/coordsysrect';
export { Gradient, Divergence, Curl, Laplacian, gradient, divergence, curl } from './vector/operators';
export type { GradientNode, DivergenceNode, CurlNode, LaplacianNode, OperatorOptions } from './vector/operators';
export { Del } from './vector/deloperator';
export type { DelNode } from './vector/deloperator';
export {
  express,
  directionalDerivative,
  laplacian,
  isConservative,
  isSolenoidal,
  scalarPotential,
  scalarPotentialDifference,
  matrixToVector,
  orthogonalize,
} from './vector/functions';
export type { OrthogonalizeOptions } from './vector/functions';
export { ImplicitRegion } from './vector/implicitregion';
export type { ImplicitRegionNode } from './vector/implicitregion';
export { ParametricRegion, parametricRegionList } from './vector/parametricregion';
export type { ParametricRegionNode, ParametricBound } from './vector/parametricregion';
export { ParametricIntegral, vectorIntegrate } from './vector/integrals';
export type { ParametricIntegralNode, IntegrationLimit } from './vector/integrals';
