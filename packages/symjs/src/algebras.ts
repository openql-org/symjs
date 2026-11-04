// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/algebras`: quaternions (SymPy sympy.algebras: Quaternion).
 */

// every entry point brings the core with its registrations
import './core';

export { Quaternion } from './algebras/quaternion';
export type { QuaternionNode, QuaternionOptions, ToEulerOptions, ToRotationMatrixOptions } from './algebras/quaternion';
