// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 polys/numberfields/subfield.py, BSD-3-Clause; see LICENSE.
import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { Dummy, Rational, S } from '../../core/nodes';
import { at, expectType } from '../../core/guard';
import { add, mul, pow, sympify } from '../../core/ops';
import { asCoefficientsDict } from '../../core/methods';
import { freeSymbols } from '../../core/traverse';
import { NoMatch, isNoMatch, type NoMatchResult } from '../../core/truth';
import { NotImplementedError, DomainError } from '../../core/errors';
import { expand } from '../../simplify/expand';
import { Matrix } from '../../matrices/matrix';
import { rref } from '../../matrices/linalg';
import { AlgebraicNumber, minimalPolynomial } from '../numberfields';

type AlgebraicInput = ExprLike | AlgebraicNumber;
const value = (a: AlgebraicInput): Expr => a instanceof AlgebraicNumber ? a.asExpr() : sympify(a);

/**
 * Express a in the power basis of b using exact rational linear algebra.
 * Expanded radical monomials supply the equations; every successful result
 * is checked by exact reconstruction. Failure to find this representation is
 * NoMatch, not a proof that two abstract fields are non-isomorphic.
 */
export function fieldIsomorphism(aIn: AlgebraicInput, bIn: AlgebraicInput): Rational[] | NoMatchResult {
  const a = value(aIn), b = value(bIn), t = new Dummy('t');
  if (freeSymbols(a).size || freeSymbols(b).size) throw new DomainError('Number fields must be algebraic over QQ');
  // Validate both inputs, including the rational target case.
  minimalPolynomial(a, t);
  const n = minimalPolynomial(b, t, { polys: true }).degree();
  const basis = Array.from({ length: n }, (_, i) => asCoefficientsDict(expand(pow(b, i))));
  const target = asCoefficientsDict(expand(a));
  const monomials = new Map([...target, ...basis.flatMap((d) => [...d])].map(([m]) => [m.key, m]));
  const rows = [...monomials.values()].map((m) => [...basis.map((d) => d.get(m) ?? S.Zero), target.get(m) ?? S.Zero]);
  const [reduced, pivots] = rref(Matrix.of(rows));
  if (pivots.includes(n) || pivots.length !== n) return NoMatch;
  const coeffs = pivots.map((_, i) => expectType(reduced.get(i, n), (c): c is Rational => c instanceof Rational, 'rational coefficient'));
  // Every expanded monomial is a row of the exact linear system. Consistency
  // already proves reconstruction; a second zero check cannot fail here.
  while (coeffs.length > 1 && at(coeffs, coeffs.length - 1).equals(0)) coeffs.pop();
  return coeffs.reverse();
}

export interface PrimitiveElementOptions { ex?: boolean; maxCandidates?: number; }
export function primitiveElement(extension: readonly AlgebraicInput[], x?: Sym, options?: PrimitiveElementOptions & { ex?: false }): [Expr, number[]];
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym | undefined, options: PrimitiveElementOptions & { ex: true }): [Expr, number[], Rational[][]];
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym | undefined, options: PrimitiveElementOptions): [Expr, number[]] | [Expr, number[], Rational[][]];
/** Primitive elements for extensions whose radical power bases expand exactly. */
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym = new Dummy('x'), options: PrimitiveElementOptions = {}): [Expr, number[]] | [Expr, number[], Rational[][]] {
  if (!extension.length) throw new RangeError('At least one extension is required');
  const maxCandidates = options.maxCandidates ?? 16;
  if (!Number.isInteger(maxCandidates) || maxCandidates < 1) throw new RangeError('maxCandidates must be a positive integer');
  const generators = extension.map(value), coeffs = generators.map(() => 0);
  let theta: Expr = S.Zero;
  let representations: Rational[][] = [];
  for (const [i, generator] of generators.entries()) {
    const existing = fieldIsomorphism(generator, theta);
    if (!isNoMatch(existing)) { representations.push(existing); continue; }
    let found = false;
    // A bounded exact search: unsupported presentations fail explicitly.
    // No numerical root matching is used to assert an embedding.
    for (let k = 1; k <= maxCandidates; k++) {
      const candidate = add(theta, mul(k, generator));
      const reps = generators.slice(0, i + 1).map((g) => fieldIsomorphism(g, candidate));
      if (reps.every((r): r is Rational[] => !isNoMatch(r))) {
        theta = candidate; coeffs[i] = k; representations = reps; found = true; break;
      }
    }
    if (!found) throw new NotImplementedError(`primitiveElement: no exact radical presentation found within ${maxCandidates} candidates`);
  }
  const polynomial = minimalPolynomial(theta, x);
  if (!options.ex) return [polynomial, coeffs];
  return [polynomial, coeffs, representations];
}

/** Embed one or several algebraic values in an explicitly represented number field. */
export function toNumberField(extension: AlgebraicInput | readonly AlgebraicInput[], theta?: AlgebraicInput): AlgebraicNumber {
  const generators = Array.isArray(extension) ? extension : [extension];
  if (!generators.length) throw new RangeError('At least one extension is required');
  const values = generators.map(value);
  const [, coefficients] = primitiveElement(values);
  const root = values.length === 1 ? at(values, 0) : add(...values.map((v, i) => mul(at(coefficients, i), v)));
  if (theta === undefined) return new AlgebraicNumber(root);
  const target = value(theta), embedding = fieldIsomorphism(root, target);
  if (isNoMatch(embedding)) throw new NotImplementedError('toNumberField: exact embedding was not found');
  return new AlgebraicNumber(target, embedding);
}
