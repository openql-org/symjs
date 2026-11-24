// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan types of the simple Lie algebras (SymPy
 * sympy.liealgebras.cartan_type): CartanType('A3') or CartanType(['A', 3]).
 */

import { StandardCartan } from './standard';
import { TypeA } from './typea';
import { TypeB } from './typeb';
import { TypeC } from './typec';
import { TypeD } from './typed';
import { TypeE } from './typee';
import { TypeF } from './typef';
import { TypeG } from './typeg';

export { StandardCartan };

/** A Cartan type: an instance, a string such as 'A3' or a pair such as ['A', 3]. */
export type CartanTypeLike = StandardCartan | string | readonly [string, number | bigint];

/**
 * Selects a Cartan type from its series and rank.
 *
 * @param c - An existing type, a type name or a series and rank.
 * @returns The corresponding Cartan type.
 * @throws TypeError when the rank is not an integer.
 * @throws RangeError when the series is unknown or does not admit the given rank.
 * @see SymPy `sympy.liealgebras.cartan_type.CartanType`
 */
export function CartanType(c: CartanTypeLike): StandardCartan {
  if (c instanceof StandardCartan) return c;
  const [letter, nIn] = typeof c === 'string' ? [c.charAt(0), c.slice(1)] : c;
  const n = Number(nIn);
  if (!Number.isInteger(n)) throw new TypeError("Argument must be a string (e.g. 'A3') or a list (e.g. ['A', 3])");
  if (n < 0) throw new RangeError('Lie algebra rank cannot be negative');
  switch (letter) {
    case 'A':
      return new TypeA(n);
    case 'B':
      return new TypeB(n);
    case 'C':
      return new TypeC(n);
    case 'D':
      return new TypeD(n);
    case 'E':
      return new TypeE(n);
    case 'F':
      return new TypeF(n);
    case 'G':
      return new TypeG(n);
    default:
      throw new RangeError(`unknown Cartan series ${letter}`);
  }
}
