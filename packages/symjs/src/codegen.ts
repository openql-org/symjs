// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/codegen`: the C99 math functions of SymPy
 * sympy.codegen.cfunctions (expm1, log1p, exp2, log2, fma, log10, Sqrt, Cbrt,
 * hypot, isnan, isinf) as symbolic functions. It also exposes symbolic matrix solves.
 */

// every entry point brings the core with its registrations
import './core';

export { expm1, log1p, exp2, log2, fma, log10, Sqrt, Cbrt, hypot, isnan, isinf, CFunction, CBooleanFunction } from './codegen/cfunctions';
export type { CFunctionClass, CBooleanFunctionClass } from './codegen/cfunctions';
export { MatrixSolve } from './codegen/matrixnodes';
