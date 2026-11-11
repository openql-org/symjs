// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/numberfields/resolvent_lookup.py, BSD-3-Clause; see LICENSE.

import { at } from '../../core/guard';
import { Rational } from '../../core/nodes';
import tables from './resolventlookupdata';

/** Evaluate an exact resolvent coefficient table at monic polynomial coefficients. */
export function resolventCoefficients(coefficients: readonly Rational[], number: number): Rational[] {
  const key = `${coefficients.length},${number}`;
  const table = Object.entries(tables).find(([name]) => name === key)?.[1];
  if (table === undefined) throw new RangeError(`no resolvent table ${key}`);
  return [Rational.of(1), ...table.map((terms) => terms.reduce((sum, term) => {
    const { powers: monomial, coefficient } = term;
    let product = Rational.of(BigInt(coefficient));
    monomial.forEach((power, i) => {
      const c = at(coefficients, i);
      product = Rational.of(product.p * c.p ** BigInt(power), product.q * c.q ** BigInt(power));
    });
    return Rational.of(sum.p * product.q + product.p * sum.q, sum.q * product.q);
  }, Rational.of(0)))];
}
