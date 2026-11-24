// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/sqfreetools.py, BSD-3-Clause; see LICENSE.

import { DomainError } from '../core/errors';
import { at } from '../core/guard';
import { Dummy } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { xreplace } from '../core/traverse';
import { expand } from '../simplify/expand';
import { dmpFromDict, dmpToDict } from './densebasic';
import type { DensePoly } from './densebasic';
import { dmpAlgInject } from './densetools';
import type { Domain } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { Poly, resultant } from './sympoly';

/**
 * Shift a square-free polynomial over an algebraic field until its norm is square-free.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The generator shifts, the shifted polynomial and its square-free norm over the ground field.
 * @throws DomainError when the coefficient domain is not algebraic.
 * @throws RangeError when the polynomial is not square-free.
 * @see SymPy `sympy.polys.sqfreetools.dmp_sqf_norm`
 * @example
 * ```ts
 * import { QQ, dmpSqfNorm, ex } from '@symjs/symjs';
 *
 * const K = QQ.algebraicField(ex`sqrt(3)`);
 * dmpSqfNorm([1, 0, 1], 0, K)[0]; // => [1]
 * ```
 */
export function dmpSqfNorm(f: DensePoly, u: number, K: Domain): [number[], unknown[], unknown[]] {
  if (!(K instanceof AlgebraicField)) throw new DomainError('ground domain must be algebraic');
  const variables = Array.from({ length: u + 1 }, (_, i) => new Dummy(`x${i}`));
  const terms = [...dmpToDict(f, u)];
  const expression = add(...terms.map(([powers, c]) => mul(K.toSympy(c), ...variables.map((v, i) => pow(v, at(powers, i))))));
  const polynomial = Poly.from(expression, variables, { domain: K.toString() });
  const squarefree = (p: Poly): boolean => {
    let gcd = p;
    for (const v of variables) gcd = gcd.gcd(p.diff(v));
    return !p.isZero && gcd.totalDegree() === 0;
  };
  if (!squarefree(polynomial)) throw new RangeError('a square-free polynomial is required');
  const degrees = polynomial.degreeList();
  const order = variables.map((_, i) => i).filter((i) => at(degrees, i) > 0).sort((a, b) => at(degrees, a) - at(degrees, b) || a - b);
  const theta = new Dummy('a');
  const minimal = add(...K.mod.map((c, i) => mul(K.dom.toSympy(c), pow(theta, K.mod.length - i - 1))));
  const alpha = K.toSympy(K.new([1, 0]));
  for (let trial = 0; ; trial++) {
    const shift = variables.map((_, i) => trial === 0 ? 0 : trial <= order.length ? (at(order, trial - 1) === i ? 1 : 0) : trial - order.length);
    const shifted = Poly.from(expand(xreplace(expression, variables.map((v, i) => [v, add(v, mul(-at(shift, i), alpha))]))), variables, { domain: K.toString() });
    const dense = dmpFromDict(new Map(shifted.terms().map(([m, c]) => [m, K.convert(c)])), u, K);
    const [injected] = dmpAlgInject(dense, u, K);
    const normInput = add(...[...dmpToDict(injected, u + 1)].map(([m, c]) => mul(K.dom.toSympy(c), ...[theta, ...variables].map((v, i) => pow(v, at(m, i))))));
    const norm = Poly.from(resultant(minimal, normInput, theta), variables, { domain: K.dom.toString() });
    if (squarefree(norm)) return [shift, dense, dmpFromDict(new Map(norm.terms().map(([m, c]) => [m, K.dom.convert(c)])), u, K.dom)];
  }
}
