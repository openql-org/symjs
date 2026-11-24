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
import { heuGcd } from './euclidtools';
import { gfGcd } from './galoistools';
import type { PolyElement } from './rings';
import { zpoly, type ZPoly } from './wang';

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

/**
 * Computes the GCD of two univariate integer polynomials and divides it out.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @returns The GCD and both cofactors.
 * @see SymPy `sympy.polys.modulargcd.modgcd_univariate`
 * @remarks SymPy returns `(x - 1, x**4 + x**3 + x**2 + x + 1, 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, ex, modgcdUnivariate, ring } from '@symjs/symjs';
 *
 * const [R] = ring('x', ZZ);
 * modgcdUnivariate(R.fromExpr(ex`x**5 - 1`), R.fromExpr(ex`x - 1`)); // => [x - 1, x**4 + x**3 + x**2 + x + 1, 1]
 * ```
 */
export function modgcdUnivariate(f: PolyElement, g: PolyElement): Cofactors { return integerModgcd(f, g); }

/**
 * Computes the GCD of two bivariate integer polynomials and divides it out.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @returns The GCD and both cofactors.
 * @see SymPy `sympy.polys.modulargcd.modgcd_bivariate`
 * @remarks SymPy returns `(x + y, x - y, x + y)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, ex, modgcdBivariate, ring } from '@symjs/symjs';
 *
 * const [R] = ring('x, y', ZZ);
 * modgcdBivariate(R.fromExpr(ex`x**2 - y**2`), R.fromExpr(ex`x**2 + 2*x*y + y**2`)); // => [x + y, x - y, x + y]
 * ```
 */
export function modgcdBivariate(f: PolyElement, g: PolyElement): Cofactors { return integerModgcd(f, g); }

/** A degree-preserving coprime image in every variable excludes a common factor. */
function coprimeImages(f: ZPoly, g: ZPoly, n: number): boolean {
  const prime = 65537n;
  const degrees = (p: ZPoly, j: number) => Math.max(...[...p.values()].map(({ e }) => at(e, j)));
  for (let j = 0; j < n; j++) {
    const df = degrees(f, j), dg = degrees(g, j);
    if (df === 0 || dg === 0) continue;
    const image = (poly: ZPoly, degree: number, point: bigint): bigint[] => {
      const coefficients = Array<bigint>(degree + 1).fill(0n);
      for (const { e, c } of poly.values()) {
        let value = c;
        for (const [i, power] of e.entries()) if (i !== j) value = value * (point + BigInt(i)) ** BigInt(power) % prime;
        const k = degree - at(e, j);
        coefficients[k] = (at(coefficients, k) + value) % prime;
      }
      return coefficients;
    };
    const certified = [1n, 2n, 3n].some((point) => {
      const a = image(f, df, point), b = image(g, dg, point);
      return first(a) !== 0n && first(b) !== 0n && gfGcd(a, b, prime).length === 1;
    });
    if (!certified) return false;
  }
  return true;
}

/**
 * Computes the GCD of multivariate integer polynomials and divides it out.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @returns The GCD and both cofactors.
 * @throws DomainError when the coefficient domain is not the integers.
 * @see SymPy `sympy.polys.modulargcd.modgcd_multivariate`
 * @remarks SymPy returns `(x + y, x - y, x + y)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, ex, modgcdMultivariate, ring } from '@symjs/symjs';
 *
 * const [R] = ring('x, y', ZZ);
 * modgcdMultivariate(R.fromExpr(ex`x**2 - y**2`), R.fromExpr(ex`x**2 + 2*x*y + y**2`)); // => [x + y, x - y, x + y]
 * ```
 */
export function modgcdMultivariate(f: PolyElement, g: PolyElement): Cofactors {
  checkRing(f, g);
  const R = f.ring;
  if (!R.domain.equals(ZZ)) throw new DomainError('modular integer GCD requires ZZ');
  const t = trivial(f, g);
  if (t !== false) return t;
  const encode = (p: PolyElement) => zpoly(p.listterms().map(([e, c]) => [e, ZZ.convert(c)]));
  const candidate = heuGcd(encode(f), encode(g), R.ngens);
  if (candidate && coprimeImages(candidate[1], candidate[2], R.ngens)) {
    const decode = (p: ZPoly) => R.fromTerms([...p.values()].map(({ e, c }) => [e, c]));
    return [decode(candidate[0]), decode(candidate[1]), decode(candidate[2])];
  }
  return integerModgcd(f, g);
}

/**
 * Computes the monic polynomial GCD over the defining number field using exact arithmetic.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @returns The GCD and both cofactors.
 * @throws DomainError when the coefficient domain is not algebraic.
 * @see SymPy `sympy.polys.modulargcd.func_field_modgcd`
 * @example
 * ```ts
 * import { QQ, ex, funcFieldModgcd, ring } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ.algebraicField(ex`sqrt(2)`));
 * funcFieldModgcd(x.pow(2).sub(2), x.sub(ex`sqrt(2)`))[0].asExpr(); // => x - sqrt(2)
 * ```
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
