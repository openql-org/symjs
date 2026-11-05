// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/tensor`: N-dimensional arrays and array operations (SymPy sympy.tensor.array) and Idx.
 */

// every entry point brings the core with its registrations
import './core';

export * from './tensor/index';

import { arrayHooks } from './tensor/ndimarray';
import { doit as _doit_ } from './calculus/doit';

// array.doit() evaluates the elements with doit, which is a higher layer than the arrays
arrayHooks.doit = _doit_;

import { ImmutableDenseNDimArray as _ImmutableDenseNDimArray_ } from './tensor/index';

/** @deprecated Use `SymArray` (`Array` shadows the JavaScript global); removed in 1.0. */
export const Array = _ImmutableDenseNDimArray_;

/** @deprecated Use `SymArray` (`Array` shadows the JavaScript global); removed in 1.0. */
export type Array = _ImmutableDenseNDimArray_;
