// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/unify/__init__.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.unify: unification of expressions and rewrite rules
 * built on it; SymPy's `sympy.unify.rebuild` is `usympy.rebuild` (see http://matthewrocklin.com/blog/work/2012/11/01/Unification/).
 */

export { unify } from './usympy';
export { rewriterule } from './rewrite';
export type { RewriteRule } from './rewrite';
export { Compound, CondVariable, Variable } from './core';
export * as usympy from './usympy';
