// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/branch/__init__.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.branch: branching strategies, rules that map
 * a value to a lazy sequence (generator) of values.
 */

export * as traverse from './traverse';
export { chain, condition, debug, doOne, exhaust, identity, multiplex, notempty, onaction, sfilter, yieldify } from './core';
export type { BranchRule } from './core';
export { canon } from './tools';
