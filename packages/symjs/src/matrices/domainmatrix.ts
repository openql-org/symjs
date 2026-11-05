// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (matrices/repmatrix.py: RepMatrix.to_DM),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License
// (see LICENSE).

/**
 * @file Matrix.to_DM: a Matrix as a DomainMatrix over the domain of its
 * entries (the DomainMatrix class itself is in polys/matrices).
 */

import type { Domain } from '../polys/domains';
import { DomainMatrix } from '../polys/matrices/domainmatrix';
import { EXRAW } from '../polys/domains/expressionrawdomain';
import type { Matrix } from './matrix';

export { DomainMatrix } from '../polys/matrices/domainmatrix';

/**
 * SymPy Matrix.to_DM(domain, field): the matrix as a sparse DomainMatrix
 * over the given domain or the one construct_domain chooses (EXRAW instead
 * of EX), optionally its field of fractions.
 */
export function toDM(m: Matrix, opts: { field?: boolean; domain?: Domain } = {}): DomainMatrix {
  const dM = DomainMatrix.fromMatrix(m, { field: opts.field });
  if (opts.domain) return dM.convertTo(opts.domain);
  return dM.domain.toString() === 'EX' ? dM.convertTo(EXRAW) : dM;
}
