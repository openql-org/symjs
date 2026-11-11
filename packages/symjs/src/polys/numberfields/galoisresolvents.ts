// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/numberfields/galois_resolvents.py, BSD-3-Clause; see LICENSE.

import { expectType } from '../../core/guard';
import { Rational } from '../../core/nodes';
import type { Poly } from '../sympoly';
import { resolventCoefficients } from './resolventlookup';

/** Exact resolvent coefficients, in descending order, for degrees four through six. */
export function getResolventByLookup(polynomial: Poly, number: number): Rational[] {
  if (!polynomial.isMonic) throw new RangeError('resolvents require a monic polynomial');
  return resolventCoefficients(polynomial.allCoeffs().slice(1).map((c) => expectType(c, (e): e is Rational => e instanceof Rational, 'rational coefficient')), number);
}
