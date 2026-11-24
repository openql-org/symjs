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
 * Counts the unrestricted integer partitions of an integer.
 *
 * @param n - Integer to partition.
 * @returns The number of unrestricted integer partitions.
 * @see SymPy `sympy.ntheory.partitions_.npartitions`
 * @example
 * ```ts
 * import { npartitions } from '@symjs/symjs';
 *
 * npartitions(25); // => 1958
 * ```
 */
export function npartitions(n: IntLike): Expr {
  return partition(asInt(n));
}
