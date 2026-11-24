// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/linsolve.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/** @file Sparse domain arithmetic for linear systems of expressions. */

import { NonlinearError } from '../../core/errors';
import { ExprMap } from '../../core/exprmap';
import { at, defined } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Add, Mul, Rel, S } from '../../core/nodes';
import { add, mul, neg, sympify } from '../../core/ops';
import { EmptySet } from '../../sets/sets';
import { constructDomain } from '../constructor';
import { SDM, sdmIrref, sdmNullspaceFromRref, sdmParticularFromRref } from './sdm';

/**
 * The independent term and coefficients of a linear expression; reject nonlinear terms before
 * cancellation.
 *
 * @remarks SymPy prints the pair as `(3, {x: 1, y: 2})`.
 * @param a - Linear expression.
 * @param symbols - Unknowns of the linear form.
 * @returns The constant term and a map from unknowns to coefficients.
 * @throws NonlinearError when an equation is nonlinear in the unknowns.
 * @see SymPy `sympy.polys.matrices.linsolve._lin_eq2dict`
 * @example
 * ```ts
 * import { _linEq2dict, ex, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * _linEq2dict(ex`x + 2*y + 3`, new Set([x, y])); // => [3, {x: 1, y: 2}]
 * ```
 */
export function _linEq2dict(a: Expr, symbols: ReadonlySet<Expr>): [Expr, ExprMap<Expr>] {
  return linearCoefficients(a, new Map([...symbols].map((s) => [s.key, s])));
}

/** Reuse the symbol lookup across every term and equation of a sparse system. */
function linearCoefficients(a: Expr, symbols: ReadonlyMap<string, Expr>): [Expr, ExprMap<Expr>] {
  const symbol = symbols.get(a.key);
  if (symbol !== undefined) return [S.Zero, new ExprMap([[symbol, S.One]])];
  if (a instanceof Add) {
    const terms = new ExprMap<Expr[]>();
    const constants: Expr[] = [];
    for (const arg of a.args) {
      const [c, d] = linearCoefficients(arg, symbols);
      constants.push(c);
      for (const [s, v] of d) terms.set(s, [...(terms.get(s) ?? []), v]);
    }
    return [add(...constants), new ExprMap([...terms].map(([s, cs]) => [s, add(...cs)]))];
  }
  if (a instanceof Mul) {
    let terms: ExprMap<Expr> | undefined;
    let constant: Expr = S.Zero;
    const factors: Expr[] = [];
    for (const arg of a.args) {
      const [c, d] = linearCoefficients(arg, symbols);
      if (d.size === 0) factors.push(c);
      else if (terms === undefined) [constant, terms] = [c, d];
      else throw new NonlinearError(`nonlinear cross-term: ${String(a)}`);
    }
    const coefficient = mul(...factors);
    return terms === undefined ? [coefficient, new ExprMap()] : [mul(coefficient, constant), new ExprMap([...terms].map(([s, v]) => [s, mul(coefficient, v)]))];
  }
  const containsUnknown = (e: Expr): boolean => symbols.has(e.key) || e.args.some(containsUnknown);
  if (!containsUnknown(a)) return [a, new ExprMap()];
  throw new NonlinearError(`nonlinear term: ${String(a)}`);
}

/**
 * Convert equations into coefficient dictionaries and independent terms.
 *
 * @remarks SymPy prints the pair as `([{x: 2}], [3])`.
 * @param equations - Equations or expressions equated to zero.
 * @param symbols - Unknowns in the system.
 * @returns Coefficient maps and constant terms in equation order.
 * @throws NonlinearError when an equation is nonlinear in the unknowns.
 * @see SymPy `sympy.polys.matrices.linsolve._linear_eq_to_dict`
 * @example
 * ```ts
 * import { _linearEqToDict, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * _linearEqToDict([ex`2*x + 3`], [x]); // => [[{x: 2}], [3]]
 * ```
 */
export function _linearEqToDict(equations: readonly ExprLike[], symbols: Iterable<Expr>): [ExprMap<Expr>[], Expr[]] {
  const syms = new Map([...symbols].map((s) => [s.key, s]));
  const coefficients: ExprMap<Expr>[] = [];
  const constants: Expr[] = [];
  for (const equation of equations) {
    const e = sympify(equation);
    let [c, d] = linearCoefficients(e instanceof Rel && e.op === 'Eq' ? e.lhs : e, syms);
    if (e instanceof Rel && e.op === 'Eq') {
      const [cr, dr] = linearCoefficients(e.rhs, syms);
      c = add(c, neg(cr));
      for (const [s, v] of dr) d.set(s, add(d.get(s) ?? S.Zero, neg(v)));
      d = new ExprMap([...d].filter(([, v]) => !v.equals(S.Zero)));
    }
    coefficients.push(d);
    constants.push(c);
  }
  return [coefficients, constants];
}

/**
 * Convert expression coefficients to a sparse augmented matrix over their common field.
 *
 * @param coefficients - Coefficient map for each row.
 * @param constants - Constant terms of the equations.
 * @param symbols - Unknowns in column order.
 * @returns The sparse augmented coefficient matrix.
 * @see SymPy `sympy.polys.matrices.linsolve.sympy_dict_to_dm`
 */
export function sympyDictToDm(coefficients: readonly ReadonlyMap<Expr, Expr>[], constants: readonly Expr[], symbols: readonly Expr[]): SDM {
  const elements = new Map([...constants, ...coefficients.flatMap((d) => [...d.values()])].map((e) => [e.key, e]));
  const [K] = constructDomain([...elements.values()], { field: true, extension: true });
  const indices = new Map(symbols.map((s, i) => [s.key, i]));
  const rows = new Map<number, Map<number, Expr>>();
  coefficients.forEach((d, i) => {
    const row = new Map([...d].map(([s, v]) => [defined(indices.get(s.key)), K.fromSympy(v)]));
    const c = at(constants, i);
    if (!c.equals(S.Zero)) row.set(symbols.length, K.neg(K.fromSympy(c)));
    if (row.size) rows.set(rows.size, row);
  });
  return new SDM(rows, [coefficients.length, symbols.length + 1], K);
}

/**
 * Solve linear equations using sparse domain arithmetic; an inconsistent system returns EmptySet.
 *
 * @param equations - Equations or expressions equated to zero.
 * @param symbols - Unknowns to solve for.
 * @returns A substitution map, or `EmptySet` for an inconsistent system.
 * @throws NonlinearError when an equation is nonlinear in the unknowns.
 * @see SymPy `sympy.polys.matrices.linsolve._linsolve`
 * @example
 * ```ts
 * import { _linsolve, ex, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * _linsolve([ex`x + y - 1`, ex`x - y - 2`], [x, y]); // => {x: 3/2, y: -1/2}
 * ```
 */
export function _linsolve(equations: readonly ExprLike[], symbols: readonly Expr[]): ExprMap<Expr> | typeof EmptySet {
  const [coefficients, constants] = _linearEqToDict(equations, symbols);
  let matrix = sympyDictToDm(coefficients, constants, symbols);
  const K = matrix.domain;
  if (K.ground === 'RR') matrix = matrix.toDdm().rref()[0].toSdm();
  const [rref, pivots, columns] = sdmIrref(matrix.data, K);
  const n = symbols.length;
  if (pivots.includes(n)) return EmptySet;
  const particular = sdmParticularFromRref(rref, n + 1, pivots, K);
  const [basis, free] = sdmNullspaceFromRref(rref, K.one, n, pivots, columns, K);
  const terms = symbols.map((): Expr[] => []);
  for (const [i, v] of particular) at(terms, i).push(K.toSympy(v));
  basis.forEach((row, j) => {
    for (const [i, v] of row) at(terms, i).push(mul(at(symbols, at(free, j)), K.toSympy(v)));
  });
  return new ExprMap(symbols.map((s, i) => [s, add(...at(terms, i))]));
}
