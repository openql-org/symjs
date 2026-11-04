// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The partition function (SymPy sympy.ntheory.partitions_.npartitions,
 * deprecated in SymPy 1.13 in favour of
 * sympy.functions.combinatorial.numbers.partition).
 */

import type { Expr } from '../core/nodes';
import { partition } from '../functions/combinatorial/numbers';
import type { IntLike } from './intutil';
import { asInt } from './intutil';

/**
 * The number of partitions of n (SymPy npartitions, deprecated in SymPy
 * 1.13 in favour of partition), as partition(n).
 */
export function npartitions(n: IntLike): Expr {
  return partition(asInt(n));
}
