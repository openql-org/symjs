// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (matrices/repmatrix.py: RepMatrix.to_DM),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License
// (see LICENSE).

/**
 * @file Matrix.to_DM: a Matrix as a DomainMatrix over the domain of its
 * entries (the DomainMatrix class itself is in polys/matrices).
 */

import { constructDomain, type ConstructDomainOptions } from '../polys/constructor';
import type { Domain } from '../polys/domains';
import { DomainMatrix } from '../polys/matrices/domainmatrix';
import { EXRAW } from '../polys/domains/expressionrawdomain';
import type { Matrix } from './matrix';

export { DomainMatrix } from '../polys/matrices/domainmatrix';

/**
 * Converts an explicit matrix to a sparse domain matrix over an inferred or specified domain.
 * @param m - The input matrix.
 * @param opts - An explicit `domain`, or inference options such as `field`, `extension` and `composite`.
 * @returns The matrix with coefficients in the selected domain.
 * @throws TypeError when an explicit domain is combined with inference options.
 * @see SymPy `sympy.matrices.repmatrix.RepMatrix.to_DM`
 * @example
 * ```ts
 * import { Matrix, toDM } from '@symjs/symjs';
 * String(toDM(Matrix.of([[1, 2], [3, 4]])).domain); // => ZZ
 * ```
 */
export function toDM(m: Matrix, opts: ConstructDomainOptions & { domain?: Domain } = {}): DomainMatrix {
  const { domain, ...options } = opts;
  if (domain && Object.keys(options).length) throw new TypeError('Options cannot be used with a domain');
  const matrix = DomainMatrix.fromMatrix(m, { field: opts.field });
  if (domain) return matrix.convertTo(domain);
  const chosen = options.extension !== undefined || options.composite !== undefined
    ? constructDomain(m.data, options)[0] : matrix.domain;
  return matrix.convertTo(chosen.toString() === 'EX' ? EXRAW : chosen);
}
