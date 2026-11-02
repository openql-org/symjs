// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/calculus`: integration, limits, series,
 * summations and products.
 */

// every entry point brings the core with its registrations
import './core';

export { doit } from './calculus/doit';
export { integrate } from './integrals/integrate';
export { transformIntegral, principalValue } from './integrals/transform';
export { limit } from './series/limits';
export { Sum, Product, summation, product, doitConcrete, reverseOrder, Concrete } from './concrete/summations';
export { series, O } from './series/series';
export { piecewiseIntegrate } from './integrals/integrate';
export { sumIsConvergent, sumIsAbsolutelyConvergent } from './concrete/summations';
export { leadterm, asLeadingTerm, getn, extractLeadingOrder } from './series/series';
export { finiteDiffWeights, asFiniteDifference } from './calculus/finitediff';
