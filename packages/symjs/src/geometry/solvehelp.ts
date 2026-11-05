// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/solvers/solvers.py, the systems solved
// by sympy/geometry), Copyright (c) 2006-2023 SymPy Development Team,
// BSD 3-Clause License.

/**
 * @file The equation systems of the geometry module: SymPy
 * solve([e1, e2, ...], [x, y, ...], dict=True) as the geometry calls it,
 * for systems of coordinate equations. Solutions that violate the
 * assumptions of the unknowns (real dummies) are dropped, like SymPy does.
 */

import type { Expr, Sym } from '../core/nodes';
import { Float, Rational, Special } from '../core/nodes';
import { xreplace } from '../core/traverse';
import { isReal, isZero } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import { asNumerDenom, isPolynomial } from '../core/methods';
import { ordered } from '../core/match';
import { simplify } from '../simplify/simplify';
import { solve, nonlinsolve } from '../solvers/solve';
import { solvePolySystem } from '../solvers/polysys';
import { resultant } from '../polys/sympoly';
import { nroots } from '../polys/nroots';
import { im } from '../functions/elementary/elementary';

const isZeroNumber = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** A number with a nonzero imaginary part (SymPy im(a).is_zero is False), decided numerically when needed. */
export function isNonRealNumber(a: Expr): boolean {
  const z = isZero(im(a));
  if (z !== undefined) return !z;
  try {
    const v = a.toComplex();
    return Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re));
  } catch {
    // not numerically evaluable
    return false;
  }
}

/** A value known not to be real. */
const isNonReal = (v: Expr): boolean => isReal(v) === false || v instanceof Special || (v.freeSymbols().size === 0 && isNonRealNumber(v));

/** The value satisfies the assumptions of the unknown (a real unknown takes no value known to be non-real). */
const admissible = (s: Sym, v: Expr): boolean => s.assumptions.real !== true || !isNonReal(v);

/** The real numbers among numeric roots. */
const realParts = (vs: readonly Expr[]): number[] =>
  vs.map((v) => v.toComplex()).filter((c) => Math.abs(c.im) <= 1e-9 * Math.max(1, Math.abs(c.re))).map((c) => c.re);

/**
 * Two polynomial equations in two real unknowns without a real solution:
 * no real root x of their resultant in y gives a real y that solves both
 * (checked numerically).
 */
function noRealSolution(system: readonly Expr[], syms: readonly Sym[]): boolean {
  if (system.length !== 2 || syms.length !== 2) return false;
  const [x, y] = [at(syms, 0), at(syms, 1)];
  const [f, g] = [at(system, 0), at(system, 1)];
  const r = resultant(f, g, y);
  if (!r.has(x)) return false;
  return realParts(nroots(r, 15, x)).every((xr) => {
    // (the geometry calls this for two conics, whose equations contain y)
    const fx = xreplace(f, [[x, new Float(xr)]]);
    return realParts(nroots(fx, 15, y)).every((yr) => {
      const v = xreplace(g, [[x, new Float(xr)], [y, new Float(yr)]]).toComplex();
      return Math.hypot(v.re, v.im) > 1e-6;
    });
  });
}

/**
 * The solutions of the equations e = 0 for the unknowns, as tuples in the
 * order of the unknowns (SymPy solve(eqs, syms, dict=True)).
 */
export function solveEquations(eqs: readonly Expr[], syms: readonly Sym[]): Expr[][] {
  const system = eqs.filter((e) => !isZeroNumber(e));
  if (system.length === 0) return [syms.slice()];
  let sols: Expr[][];
  if (syms.length === 1) {
    const s = at(syms, 0);
    if (system.some((e) => !e.has(s))) return [];
    // like SymPy _solve_system: the equations in canonical order, the first that solve can handle
    // gives the candidates, which must make the others vanish
    const eqsInOrder = ordered(system);
    let found: Expr[] | undefined;
    let main: Expr | undefined;
    for (const e of eqsInOrder) {
      try {
        found = solve(e, s);
        main = e;
        break;
      } catch {
        // solve raises NotImplementedError for an equation it cannot solve: try the next one
      }
    }
    if (found === undefined) throw new NotImplementedError(`could not solve ${system.map(String).join(', ')} for ${s.name}`);
    sols = found.filter((v) => eqsInOrder.every((e) => e === main || isZeroNumber(simplify(xreplace(e, [[s, v]]))))).map((v) => [v]);
  } else if (system.every((e) => isPolynomial(e, syms))) {
    try {
      sols = solvePolySystem(system, syms);
    } catch {
      // NotImplementedError: an eliminant without supported radical roots: there is nothing to give
      // when the eliminant has no real root; else a system with infinitely many solutions
      if (syms.every((x) => x.assumptions.real === true) && noRealSolution(system, syms)) return [];
      sols = nonlinsolve(system, syms);
    }
  } else {
    sols = nonlinsolve(system, syms);
  }
  // like SymPy's checks: no solution makes a denominator of the equations vanish
  const dens = system.map((e) => asNumerDenom(e)[1]).filter((d) => syms.some((x) => d.has(x)));
  const reps = (t: readonly Expr[]): [Expr, Expr][] => syms.map((x, i) => [x, at(t, i)]);
  return sols.filter((t) => t.every((v, i) => admissible(at(syms, i), v)) && dens.every((d) => !isZeroNumber(simplify(xreplace(d, reps(t))))));
}
