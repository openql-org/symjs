// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/logic`: propositional logic (SymPy
 * sympy.logic: Implies, Equivalent, normal forms, simplify_logic,
 * satisfiable, ...) and the assumption helpers of SymPy sympy.assumptions
 * that are not part of the core (`allargs`, `anyarg`, `exactlyonearg`,
 * `isInfinite`, `isExtendedReal`, `isExtendedNonnegative`).
 */

// every entry point brings the core with its registrations
import './core';

export * from './logic/index';
export * from './assumptions/index';
