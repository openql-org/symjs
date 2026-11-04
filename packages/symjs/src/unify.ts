// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/unify`: unification of expressions and rewrite rules (SymPy sympy.unify).
 */

// every entry point brings the core with its registrations
import './core';

export * from './unify/index';
