// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Entry point `@symjs/symjs/utilities`: iterable utilities (SymPy sympy.utilities.iterables).
 * @module
 */

// every entry point brings the core with its registrations
import './core';
export { lambdastr } from './utilities/lambdify';
export type { LambdaArgs, LambdaBody } from './utilities/lambdify';

export * from './utilities/index';
