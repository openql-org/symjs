// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Entry point `@symjs/symjs/strategies`: rewrite rules and strategies (SymPy sympy.strategies).
 * @module
 */

// every entry point brings the core with its registrations
import './core';

export * from './strategies/index';
