// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/densetools.py, BSD-3-Clause; see LICENSE.

import { DomainError } from '../core/errors';
import { dmpFromDict, dmpToDict } from './densebasic';
import type { DensePoly } from './densebasic';
import type { Domain } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { GaussianDomain } from './domains/gaussiandomains';

/** Inject an algebraic coefficient generator as the first polynomial variable. */
export function dmpAlgInject(f: DensePoly, u: number, K: Domain): [unknown[], number, Domain] {
  if (!(K instanceof AlgebraicField || K instanceof GaussianDomain)) throw new DomainError('an algebraic or Gaussian domain is required');
  const terms = new Map<number[], unknown>();
  for (const [powers, c] of dmpToDict(f, u)) {
    if (K instanceof AlgebraicField) {
      const coefficients = K.convert(c).rep;
      coefficients.forEach((coefficient, i) => {
        if (!coefficient.isZero) terms.set([coefficients.length - i - 1, ...powers], coefficient);
      });
    } else {
      const coefficient = K.convert(c);
      if (!coefficient.re.isZero) terms.set([0, ...powers], K.dom.convert(coefficient.re));
      if (!coefficient.im.isZero) terms.set([1, ...powers], K.dom.convert(coefficient.im));
    }
  }
  return [dmpFromDict(terms, u + 1, K.dom), u + 1, K.dom];
}
