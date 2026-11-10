// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/utilities.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { ExprLike } from '../../core/nodes';
import { Dummy, Float, Rational } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { isReal } from '../../core/assumptions';
import { at, expectType, getOrThrow } from '../../core/guard';
import { NotImplementedError } from '../../core/errors';
import { factorint } from '../../ntheory/factor';
import { asInt, pmod, type IntLike } from '../../ntheory/intutil';
import { mag, toRational } from '../../numeric/mpf';
import { minimalPolynomial } from '../numberfields';

/** Factorizations of d and f with a=d*f**2 and d a fundamental discriminant or 1. */
export function extractFundamentalDiscriminant(aIn: IntLike): [Map<bigint, number>, Map<bigint, number>] {
  const a = asInt(aIn), residue = pmod(a, 4n);
  if (residue !== 0n && residue !== 1n) throw new RangeError('discriminant must be 0 or 1 mod 4');
  const D = new Map<bigint, number>(), F = new Map<bigint, number>();
  if (a === 0n) return [D, new Map([[0n, 1]])];
  let threes = 0;
  for (const [p, e] of factorint(a)) {
    if (e % 2n) {
      D.set(p, 1);
      if (pmod(p, 4n) === 3n) threes++;
      if (e >= 3n) F.set(p, Number((e - 1n) / 2n));
    } else F.set(p, Number(e / 2n));
  }
  const even = D.has(2n);
  if (even || threes % 2) {
    const e = getOrThrow(F, 2n);
    if (e === 1) F.delete(2n);
    else F.set(2n, e - 1);
    D.set(2n, even ? 3 : 2);
  }
  return [D, F];
}

/** Rational isolating interval of a real algebraic number, optionally narrowed to eps. */
export function isolate(algIn: ExprLike, eps?: Rational): [Rational, Rational] {
  const alg = sympify(algIn);
  if (alg instanceof Rational) return [alg, alg];
  if (isReal(alg) !== true) throw new NotImplementedError('complex algebraic numbers are not supported');
  const p = minimalPolynomial(alg, new Dummy('x'), { polys: true });
  const intervals = p.intervals().map(([ab]) => ab);
  let bounds = intervals.length === 1 ? at(intervals, 0) : undefined;
  // Root isolation proves each interval contains exactly one root. Refine
  // the value used to choose that interval until rounding cannot put it on
  // the wrong side of an endpoint; compare rationals without double conversion.
  const le = (a: Rational, b: Rational): boolean => a.p * b.q <= b.p * a.q;
  for (let digits = 15; bounds === undefined; digits *= 2) {
    const v = expectType(alg.evalf(digits), (e): e is Float => e instanceof Float, 'numeric algebraic value');
    const [n, d] = toRational(v.mpf), exponent = mag(v.mpf) - v.prec + 4;
    const error = exponent < 0 ? Rational.of(1n, 2n ** BigInt(-exponent)) : Rational.of(2n ** BigInt(exponent));
    const lo = Rational.of(n * error.q - error.p * d, d * error.q);
    const hi = Rational.of(n * error.q + error.p * d, d * error.q);
    bounds = intervals.find(([a, b]) => le(a, lo) && le(hi, b));
  }
  return eps === undefined ? bounds : p.refineRoot(bounds[0], bounds[1], eps);
}
