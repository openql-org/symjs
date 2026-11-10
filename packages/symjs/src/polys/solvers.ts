// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/solvers.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { Expr } from '../core/nodes';
import { add, mul } from '../core/ops';
import { at } from '../core/guard';
import { InvariantError, NonlinearError } from '../core/errors';
import { NoMatch, type NoMatchResult } from '../core/truth';
import type { Domain } from './domains';
import { DomainMatrix } from './matrices/domainmatrix';
import type { PolyElement, PolyRing } from './rings';

/** Augmented matrix of equations sum(coeff[g]*g)+rhs=0, over the given domain. */
export function eqsToMatrix(coeffs: readonly ReadonlyMap<Expr, unknown>[], rhs: readonly unknown[], gens: readonly Expr[], domain: Domain): DomainMatrix {
  if (coeffs.length !== rhs.length) throw new RangeError('equation coefficients and right-hand sides must have equal lengths');
  const positions = new Map(gens.map((g,i) => [g.key,i]));
  const rows = coeffs.map((coeff,i) => {
    const row = gens.map(() => domain.zero);
    for (const [g,c] of coeff) {
      const j = positions.get(g.key);
      if (j === undefined) throw new RangeError('unknown equation generator');
      row[j] = domain.toSympy(domain.convert(c));
    }
    row.push(domain.fromSympy(mul(-1,domain.toSympy(domain.convert(at(rhs,i))))));
    return row;
  });
  return new DomainMatrix(rows,[rows.length,gens.length+1],domain);
}

/**
 * Solve linear polynomial-ring equations. Keys and values are expressions;
 * only solved generators appear, with free generators left as parameters.
 * An inconsistent system returns NoMatch (SymPy returns None).
 */
export function solveLinSys(eqs: readonly PolyElement[], ring: PolyRing): Map<Expr,Expr> | NoMatchResult {
  if (!ring.domain.isField) throw new InvariantError('solve_lin_sys requires field coefficients');
  const coeffs: Map<Expr,Expr>[] = [], rhs: Expr[] = [];
  for (const eq of eqs) {
    const f = eq.setRing(ring), row = new Map<Expr,Expr>();
    for (const [m,c] of f.toDict()) {
      const degree = m.reduce((a,b) => a+b,0);
      if (degree === 0) continue;
      if (degree !== 1) throw new NonlinearError('Nonlinear term encountered in solve_lin_sys');
      row.set(at(ring.symbols,m.indexOf(1)),c);
    }
    coeffs.push(row); rhs.push(f.get(ring.zeroMonom));
  }
  const [matrix,pivots] = eqsToMatrix(coeffs,rhs,ring.symbols,ring.domain).rref();
  const n = ring.ngens;
  if (pivots.includes(n)) return NoMatch;
  const rows = matrix.toList(), result = new Map<Expr,Expr>();
  pivots.forEach((p,i) => {
    const row = at(rows,i);
    const terms = ring.symbols.flatMap((g,j) => j === p ? [] : [mul(-1,at(row,j),g)]);
    result.set(at(ring.symbols,p),ring.fromExpr(add(at(row,n),...terms)).asExpr());
  });
  return result;
}
