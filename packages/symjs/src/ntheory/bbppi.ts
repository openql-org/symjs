// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Hexadecimal digits of pi from any position, by the
 * Bailey-Borwein-Plouffe formula (SymPy sympy.ntheory.bbp_pi).
 *
 * Ported from SymPy 1.14 (sympy/ntheory/bbp_pi.py, BSD-3-Clause, Copyright
 * (c) SymPy Development Team).
 */

import type { IntLike } from './intutil';
import { asInt, bitLength, powmod } from './intutil';

/** The number of hexadecimal digits computed for prec digits from position n (SymPy _dn). */
function dn(n: bigint, prec: bigint): bigint {
  // n + 1 because the caller subtracts 1 for the series
  return BigInt((bitLength(n + 1n + prec) - 1) >> 2) + prec + 3n;
}

/** The fractional part of 16**n * sum(1/(16**k*(8*k + j))), scaled by 16**dn (SymPy _series). */
function series(j: bigint, n: bigint, prec: bigint): bigint {
  // left sum, of the terms with a non-negative power of 16
  const d4 = 4n * dn(n, prec);
  let s = 0n;
  let d = j;
  for (let k = 0n; k <= n; k++) {
    s += (powmod(16n, n - k, d) << d4) / d;
    d += 8n;
  }
  // right sum, up to the first term below the precision
  let t = 0n;
  let e = d4 - 4n;
  d = 8n * (n + 1n) + j;
  for (let dt = (1n << e) / d; dt !== 0n; dt = (1n << e) / d) {
    t += dt;
    e -= 4n;
    d += 8n;
  }
  return s + t;
}

/**
 * The prec (default 14) hexadecimal digits of pi starting at the nth one
 * (SymPy pi_hex_digits): the digit 0 is the integral part 3, the digit 1
 * the first one after the point.
 *
 * Example: piHexDigits(0) is '3243f6a8885a30'; piHexDigits(0, 3) is '324'.
 */
export function piHexDigits(nIn: IntLike, precIn: IntLike = 14): string {
  const n0 = asInt(nIn, 'n');
  const prec = asInt(precIn, 'prec');
  if (n0 < 0n) throw new RangeError('n cannot be negative');
  if (prec < 0n) throw new RangeError('prec cannot be negative');
  if (prec === 0n) return '';
  const n = n0 - 1n;
  const D = dn(n, prec);
  const x = (4n * series(1n, n, prec) - 2n * series(4n, n, prec) - series(5n, n, prec) - series(6n, n, prec)) & (16n ** D - 1n);
  return (x / 16n ** (D - prec)).toString(16).padStart(Number(prec), '0');
}
