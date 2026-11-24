// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/solvers.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import { Sym } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { add, mul } from '../core/ops';
import { at, cast } from '../core/guard';
import { InvariantError, NonlinearError } from '../core/errors';
import { NoMatch, type NoMatchResult } from '../core/truth';
import type { Domain } from './domains';
import { DomainMatrix } from './matrices/domainmatrix';
import { PolyRing, type PolyElement } from './rings';
import { Poly } from './sympoly';
import { PolynomialRingBase } from './domains/oldpolynomialring';
import { constructDomain } from './constructor';

/**
 * Collects the coefficients and constant terms of linear equations over the given domain.
 *
 * @param coeffs - Coefficients in generator order.
 * @param rhs - Constant terms of the equations.
 * @param gens - Polynomial generators in the desired order.
 * @param domain - Coefficient domain.
 * @returns The augmented matrix.
 * @throws RangeError when the coefficient rows and constant terms have different lengths or an equation contains an unknown generator.
 * @see SymPy `sympy.polys.solvers.eqs_to_matrix`
 * @example
 * ```ts
 * import { ZZ, eqsToMatrix, ex } from '@symjs/symjs';
 *
 * eqsToMatrix([new Map([[ex`x`, 1], [ex`y`, 1]]), new Map([[ex`x`, 1], [ex`y`, -1]])], [0, -1], [ex`x`, ex`y`], ZZ).toMatrix(); // => Matrix([
 * //   [1,  1, 0],
 * //   [1, -1, 1]])
 * ```
 */
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
 * An inconsistent system returns NoMatch.
 *
 * @param eqs - Polynomial equations with right-hand side zero.
 * @param ringIn - Polynomial ring supplying the generators and coefficient domain.
 * @returns A map from generators to their solved values, or `NoMatch` for an inconsistent system.
 * @throws InvariantError when the coefficient domain is not a field.
 * @throws NonlinearError when an equation is nonlinear in the generators.
 * @see SymPy `sympy.polys.solvers.solve_lin_sys`
 * @example
 * ```ts
 * import { QQ, ring, solveLinSys } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * solveLinSys([x.sub(2)], R); // => {x: 2}
 * ```
 */
export function solveLinSys(eqs: readonly PolyElement[], ringIn: PolyRing | PolynomialRingBase): Map<Expr,Expr> | NoMatchResult {
  const ring = ringIn instanceof PolyRing ? ringIn : new PolyRing(ringIn.symbols, ringIn.dom, ringIn.order);
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

/**
 * Convert expression equations to a polynomial ring over a coefficient field.
 *
 * @param eqs - Polynomial equations with right-hand side zero.
 * @param symbols - Symbols naming the generators, in order.
 * @returns The equations as ring elements and their common polynomial ring.
 * @see SymPy `sympy.polys.solvers.sympy_eqs_to_ring`
 * @example
 * ```ts
 * import { ex, sympyEqsToRing } from '@symjs/symjs';
 *
 * sympyEqsToRing([ex`x - y`, ex`a*y + x`], [ex`x`, ex`y`])[0].map(p => p.asExpr()); // => [x - y, a*y + x]
 * ```
 */
export function sympyEqsToRing(eqs: readonly Expr[], symbols: readonly Expr[]): [PolyElement[], PolynomialRingBase] {
  const polys = eqs.map((e) => Poly.from(e, symbols));
  const [domain] = constructDomain(polys.flatMap((p) => p.coeffs()), { field: true, extension: true });
  const ring = new PolyRing(symbols, domain);
  return [eqs.map((e) => ring.fromExpr(e)), new PolynomialRingBase(domain, symbols.map((s) => cast(s, Sym)), 'lex')];
}
