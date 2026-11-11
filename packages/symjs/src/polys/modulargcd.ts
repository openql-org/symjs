// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 polys/modulargcd.py, BSD-3-Clause; see LICENSE.

/** Modular polynomial GCDs with certified reconstruction over the integers. */
import { DomainError } from '../core/errors';
import { at, expectType, first } from '../core/guard';
import { gcd as integerGcd } from '../core/numbers';
import { nextprime } from '../ntheory/generate';
import { dmpDiv, dmpExquo, dmpMul, dmpPrem, dmpQuoGround } from './densearith';
import { dmpConvert, dmpFromDict, dmpGroundLC, dmpOneP, dmpToDict, dmpZeroP } from './densebasic';
import type { DensePoly } from './densebasic';
import { ZZ } from './domains';
import type { Domain } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { GF } from './domains/finitefield';
import type { PolyElement } from './rings';

type Cofactors = [PolyElement, PolyElement, PolyElement];

function list(c: unknown): DensePoly {
  return expectType(c, Array.isArray, 'recursive coefficient');
}

function monic(f: DensePoly, u: number, K: Domain): unknown[] {
  return dmpZeroP(f, u) ? [...f] : dmpQuoGround(f, dmpGroundLC(f, u, K), u, K);
}

/** Content and primitive part in x_0 over K[x_1, ..., x_u]. */
function primitive(f: DensePoly, u: number, K: Domain): [unknown[], unknown[]] {
  let c = [...list(first(f))];
  for (const a of f.slice(1)) {
    c = fieldGcd(c, list(a), u - 1, K);
    if (dmpOneP(c, u - 1, K)) break;
  }
  return [c, f.map((a) => dmpExquo(list(a), c, u - 1, K))];
}

/** Primitive PRS over a field, also used to compute the modular images. */
function fieldGcd(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] {
  if (dmpZeroP(f, u)) return monic(g, u, K);
  if (dmpZeroP(g, u)) return monic(f, u, K);
  // Exact divisibility avoids coefficient growth for nested high-degree factors.
  if (dmpZeroP(dmpDiv(f, g, u, K)[1], u)) return monic(g, u, K);
  if (dmpZeroP(dmpDiv(g, f, u, K)[1], u)) return monic(f, u, K);
  if (u === 0) {
    let [a, b] = [[...f], [...g]];
    while (b.length) [a, b] = [b, dmpDiv(a, b, 0, K)[1]];
    return monic(a, 0, K);
  }
  const [cf, pf] = primitive(f, u, K);
  const [cg, pg] = primitive(g, u, K);
  const c = fieldGcd(cf, cg, u - 1, K);
  let [a, b] = [pf, pg];
  while (!dmpZeroP(b, u)) {
    const r = dmpPrem(a, b, u, K);
    a = b;
    b = dmpZeroP(r, u) ? r : primitive(r, u, K)[1];
  }
  return monic(dmpMul(a, [c], u, K), u, K);
}

function checkRing(f: PolyElement, g: PolyElement): void {
  if (!f.ring.equals(g.ring)) throw new DomainError('polynomials must belong to the same ring');
}

function trivial(f: PolyElement, g: PolyElement): Cofactors | false {
  const R = f.ring;
  if (f.isZero && g.isZero) return [R.zero, R.zero, R.zero];
  if (f.isZero) return R.domain.isNegative(g.LC) ? [g.neg(), R.zero, R.one.neg()] : [g, R.zero, R.one];
  if (g.isZero) return R.domain.isNegative(f.LC) ? [f.neg(), R.one.neg(), R.zero] : [f, R.one, R.zero];
  return false;
}

/** Symmetric Chinese remainder reconstruction on the union of term supports. */
function reconstruct(hp: PolyElement, hq: PolyElement, p: bigint, q: bigint): PolyElement {
  const F = GF(p);
  const inverse = F.convert(q).pow(-1).val;
  const modulus = p * q;
  const terms = new Map(hq.listterms().map(([m, c]) => [m.join(','), [m, ZZ.convert(c)] as const]));
  for (const [m] of hp.listterms()) if (!terms.has(m.join(','))) terms.set(m.join(','), [m, 0n]);
  return hp.ring.fromTerms([...terms.values()].map(([m, b]) => {
    const a = ZZ.convert(hp.get(m));
    const t = F.convert((a - b) * inverse).val;
    const c = b + q * t;
    const residue = ((c % modulus) + modulus) % modulus;
    return [m, residue > modulus / 2n ? residue - modulus : residue];
  }));
}

function compare(a: readonly number[], b: readonly number[]): number {
  for (let i = 0; i < a.length; i++) if (at(a, i) !== at(b, i)) return at(a, i) - at(b, i);
  return 0;
}

function integerModgcd(f: PolyElement, g: PolyElement): Cofactors {
  checkRing(f, g);
  const R = f.ring;
  if (!R.domain.equals(ZZ)) throw new DomainError('modular integer GCD requires ZZ');
  const t = trivial(f, g);
  if (t !== false) return t;
  const [cf, fp] = f.primitive();
  const [cg, gp] = g.primitive();
  const content = integerGcd(ZZ.convert(cf), ZZ.convert(cg));
  const u = R.ngens - 1;
  const [fd, gd] = [fp.toDense(), gp.toDense()];
  const gamma = integerGcd(ZZ.convert(dmpGroundLC(fd, u, ZZ)), ZZ.convert(dmpGroundLC(gd, u, ZZ)));
  let p = 65521n;
  let modulus = 1n;
  let previous = R.zero;
  let bound = Array.from({ length: R.ngens }, () => Infinity);
  for (;;) {
    p = nextprime(p);
    if (gamma % p === 0n) continue;
    const F = GF(p);
    const image = fieldGcd(dmpConvert(fd, u, ZZ, F), dmpConvert(gd, u, ZZ, F), u, F);
    const hp = R.fromTerms([...dmpToDict(image, u)].map(([m, c]) => [m, F.toSympy(F.convert(c).mul(gamma))]));
    const degree = first([...dmpToDict(hp.toDense(), u).keys()].sort((a, b) => -compare(a, b)));
    const order = compare(degree, bound);
    if (order > 0) continue;
    if (order < 0) {
      bound = degree;
      modulus = 1n;
    }
    const candidate = modulus === 1n ? hp : reconstruct(hp, previous, p, modulus);
    modulus *= p;
    if (candidate.equals(previous)) {
      const primitiveCandidate = candidate.primitive()[1];
      const h = primitiveCandidate.mulGround(content);
      const [a, ra] = f.div(h);
      const [b, rb] = g.div(h);
      if (ra.isZero && rb.isZero) return [h, a, b];
    }
    previous = candidate;
  }
}

/** GCD and cofactors in ZZ[x] (SymPy modgcd_univariate). */
export function modgcdUnivariate(f: PolyElement, g: PolyElement): Cofactors { return integerModgcd(f, g); }

/** GCD and cofactors in ZZ[x, y] (SymPy modgcd_bivariate). */
export function modgcdBivariate(f: PolyElement, g: PolyElement): Cofactors { return integerModgcd(f, g); }

/** GCD and cofactors in ZZ[x_1, ..., x_n] (SymPy modgcd_multivariate). */
export function modgcdMultivariate(f: PolyElement, g: PolyElement): Cofactors { return integerModgcd(f, g); }

/**
 * Monic GCD and cofactors over an algebraic number field (SymPy func_field_modgcd).
 * Exact arithmetic in the defining number field certifies every PRS step.
 */
export function funcFieldModgcd(f: PolyElement, g: PolyElement): Cofactors {
  checkRing(f, g);
  const R = f.ring;
  const K = R.domain;
  if (!(K instanceof AlgebraicField)) throw new DomainError('an algebraic number field is required');
  const u = R.ngens - 1;
  const h = fieldGcd(dmpFromDict(new Map(f.listterms()), u, K), dmpFromDict(new Map(g.listterms()), u, K), u, K);
  const result = R.fromTerms([...dmpToDict(h, u)].map(([m, c]) => [m, K.toSympy(c)]));
  if (result.isZero) return [result, result, result];
  return [result, f.exquo(result), g.exquo(result)];
}
