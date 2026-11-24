// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/numberfields/galoisgroups.py, BSD-3-Clause; see LICENSE.

/**
 * @file Galois groups of polynomials of degree at most six, by the algorithms
 * of Cohen, *A Course in Computational Algebraic Number Theory* (section 6.3),
 * with resolvent coefficients from lookup tables.
 */

import { at, cast, defined, expectType } from '../../core/guard';
import { Dummy, Rational, Sym } from '../../core/nodes';
import type { Expr, ExprLike } from '../../core/nodes';
import { mul, sub } from '../../core/ops';
import { xreplace } from '../../core/traverse';
import { isqrt } from '../../core/numberutils';
import { isSquare } from '../../ntheory/intutil';
import { Permutation } from '../../combinatorics/permutations';
import { S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups } from '../../combinatorics/galois';
import type { TransitiveSubgroup } from '../../combinatorics/galois';
import type { PermutationGroupNode } from '../../combinatorics/permgroups';
import { dupRandom } from '../densebasic';
import { ZZ } from '../domains';
import { numberFieldHooks } from '../domains/algebraicfield';
import { Poly, resultant } from '../sympoly';
import { GaloisGroupException, Resolvent, defineResolvents, getResolventByLookup } from './galoisresolvents';
import { coeffSearch } from './utilities';

/** Controls how the Galois group is computed and represented. */
export interface GaloisGroupOptions {
  /** The choice of a transitive-subgroup name in place of a permutation group. */
  byName?: boolean;
  /** The maximum number of resolvent-search attempts. */
  maxTries?: number;
  /** The choice of random Tschirnhausen transformations. */
  randomize?: boolean
}
/**
 * Pairs the group or its transitive-subgroup name with a flag for containment in the alternating
 * group.
 */
export type GaloisGroupResult = [TransitiveSubgroup | PermutationGroupNode, boolean];
type NamedGroup = [TransitiveSubgroup, boolean];

/**
 * No suitable Tschirnhausen transformation or resolvent was found within the allowed number of
 * tries.
 *
 * @see SymPy `sympy.polys.numberfields.galoisgroups.MaxTriesException`
 */
export class MaxTriesException extends GaloisGroupException {}

/** @internal The key of a polynomial in a Tschirnhausen history: its dense coefficients joined by commas (SymPy Poly.rep). */
export const repKey = (p: Poly): string => p.allCoeffs().map(String).join(',');

/** Options of tschirnhausenTransformation. */
export interface TschirnhausenOptions {
  /** With fixedOrder false, keep the random coefficients between -maxCoeff and maxCoeff (default 10). */
  maxCoeff?: number;
  /** Consider at most this many transformations (default 30). */
  maxTries?: number;
  /**
   * The polynomials that must not be returned as U, as their coefficients
   * from the leading one joined by commas ('1,0,0,0,1' for x**4 + 1); the
   * key of T is added to it before the search.
   */
  history?: Set<string>;
  /**
   * Work through the candidate transformations A(x) in a fixed order from
   * small coefficients to large (default true); otherwise choose them at
   * random, still working upward from small coefficients.
   */
  fixedOrder?: boolean;
  /** The random number generator of the random choices (default Math.random). */
  random?: () => number;
}

/**
 * Another monic irreducible integer polynomial U defining the same number field as the monic
 * irreducible integer polynomial T (Cohen, Alg. 6.3.4): returns [A, U], where the polynomial A maps
 * the roots of T to those of U. Throws MaxTriesException when no square-free U outside the history
 * is found in maxTries attempts.
 *
 * @param T - Monic irreducible integer polynomial.
 * @param options - Coefficient bounds, candidate order, history and trial limit.
 * @returns The transformation polynomial and the transformed defining polynomial.
 * @throws MaxTriesException when no admissible transformation is found within the trial limit.
 * @see SymPy `sympy.polys.numberfields.galoisgroups.tschirnhausen_transformation`
 */
export function tschirnhausenTransformation(T: Poly, options: TschirnhausenOptions = {}): [Poly, Poly] {
  const { maxCoeff = 10, maxTries = 30, history = new Set<string>(), fixedOrder = true, random = Math.random } = options;
  const X = new Dummy('X');
  const n = T.degree();
  history.add(repKey(T));
  const generators = new Map<number, Generator<number[], never>>();
  const coefficientGenerator = (degree: number): Generator<number[], never> => {
    const gen = generators.get(degree) ?? coeffSearch(degree, 1);
    generators.set(degree, gen);
    return gen;
  };
  let degCoeffSum = 3, currentDegree = 2;
  for (let i = 0; i < maxTries; i++) {
    // A linear A(x) multiplies the discriminant by a square only, so it is never used.
    let a: ExprLike[];
    if (fixedOrder) {
      // Move through the (degree, coefficient bound) plane along lines of constant sum.
      let coeffs = coefficientGenerator(currentDegree).next().value;
      if (currentDegree + Math.max(...coeffs.map(Math.abs)) > degCoeffSum) {
        if (currentDegree === 2) {
          degCoeffSum += 1;
          currentDegree = degCoeffSum - 1;
        } else currentDegree -= 1;
        coeffs = coefficientGenerator(currentDegree).next().value;
      }
      a = [1, ...coeffs];
    } else {
      // A progressive coefficient bound, five tries for each.
      const C = Math.min(Math.floor(i / 5) + 1, maxCoeff);
      const d = 2 + Math.floor(random() * (n - 2));
      a = dupRandom(d, -C, C, ZZ, random).map((c) => expectType(c, (v): v is bigint => typeof v === 'bigint', 'integer'));
    }
    const A = Poly.fromList(a, [T.gen]);
    const U = Poly.from(resultant(T.asExpr(), sub(X, A.asExpr()), cast(T.gen, Sym)), [X]);
    if (!history.has(repKey(U)) && U.isSqf) return [A, U];
  }
  throw new MaxTriesException('no Tschirnhausen transformation found');
}

/**
 * Tests whether the discriminant of a polynomial, or of a dense integer polynomial, is a rational
 * square.
 *
 * @param T - Polynomial or its dense integer coefficients.
 * @returns Whether the discriminant is a rational square.
 * @see SymPy `sympy.polys.numberfields.galoisgroups.has_square_disc`
 */
export function hasSquareDisc(T: Poly | readonly (bigint | Rational)[]): boolean {
  const p = T instanceof Poly ? T : dense(T);
  const d = expectType(p.discriminant(), (e): e is Rational => e instanceof Rational, 'rational discriminant');
  return d.p >= 0n && isqrt(d.p) ** 2n === d.p && isqrt(d.q) ** 2n === d.q;
}

const dense = (coefficients: readonly (bigint | Rational)[]): Poly => Poly.fromList(coefficients.map((c) => (typeof c === 'bigint' ? Rational.of(c) : c)), [new Dummy('x')]);

/** The degrees of the irreducible factors, with multiplicity, in increasing order. */
const factorDegrees = (p: Poly): number[] => p.factorList()[1].flatMap(([f, m]) => Array.from({ length: m }, () => f.degree())).sort((a, b) => a - b);

/** A square-free resolvent from the lookup table, after Tschirnhausen transformations of T as needed. */
function lookupResolvent(T0: Poly, number: number, maxTries: number, randomize: boolean): [Poly, Poly] {
  let T = T0;
  const history = new Set<string>();
  for (let i = 0; i < maxTries; i++) {
    const R = dense(getResolventByLookup(T, number));
    if (R.isSqf) return [R, T];
    T = tschirnhausenTransformation(T, { maxTries, history, fixedOrder: !randomize })[1];
  }
  throw new MaxTriesException('no square-free resolvent found');
}

const variables = (n: number): Sym[] => Array.from({ length: n }, (_, i) => new Sym(`X${i}`));

/** @internal The Galois group of a cubic (Cohen, Prop. 6.3.5). */
export function galoisGroupDegree3(T: Poly): NamedGroup {
  return hasSquareDisc(T) ? [S3TransitiveSubgroups.A3, true] : [S3TransitiveSubgroups.S3, false];
}

/** @internal The Galois group of a quartic by root approximation (Cohen, Alg. 6.3.7). */
export function galoisGroupDegree4RootApprox(T0: Poly, maxTries = 30, randomize = false): NamedGroup {
  const X = variables(4);
  const x = (i: number): Expr => cast(X[i], Sym);
  // The form F = X0*X2 + X1*X3 for G = S4: its stabilizer is D4 = <(0123), (02)>.
  const s1 = [new Permutation(3), new Permutation(3).call(0, 1), new Permutation(3).call(0, 3)];
  const R1 = new Resolvent(mul(x(0), x(2)).add(mul(x(1), x(3))), X, s1);
  const F2pre = mul(x(0), x(1), x(1)).add(mul(x(1), x(2), x(2))).add(mul(x(2), x(3), x(3))).add(mul(x(3), x(0), x(0)));
  const s2pre = [new Permutation(3), new Permutation(3).call(0, 2)];
  let T = T0;
  const history = new Set<string>();
  for (let i = 0; i < maxTries; i++) {
    if (i > 0) T = tschirnhausenTransformation(T, { maxTries, history, fixedOrder: !randomize })[1];
    const [R, , i0] = R1.evalForPoly(T, true);
    if (!dense(R).isSqf) continue;
    // Gal(T) is contained in A4 if and only if disc(T) is a square (Cohen, Prop. 6.3.1).
    const sqDisc = hasSquareDisc(T);
    if (typeof i0 !== 'number') return sqDisc ? [S4TransitiveSubgroups.A4, true] : [S4TransitiveSubgroups.S4, false];
    // Gal(T) is conjugate to a subgroup of D4: V, C4 or D4. Neither C4 nor D4 is in A4.
    if (sqDisc) return [S4TransitiveSubgroups.V, true];
    const [, d] = secondResolvent(T, F2pre, s2pre, s1, i0, X);
    if (d === 0n) continue;
    return isSquare(d) ? [S4TransitiveSubgroups.C4, false] : [S4TransitiveSubgroups.D4, false];
  }
  throw new MaxTriesException('no square-free quartic resolvent found');
}

/** The discriminant of the second resolvent, for the conjugate of F2pre selected by the permutation s[i0]. */
function secondResolvent(T: Poly, F2pre: Expr, s2pre: readonly Permutation[], s: readonly Permutation[], i0: number, X: readonly Sym[]): [bigint[], bigint] {
  const sigma = cast(s[i0], Permutation);
  const image = sigma.call([...X]);
  const F2 = xreplace(F2pre, X.map((v, k) => [v, cast(image[k], Sym)]));
  const R2 = new Resolvent(F2, X, s2pre.map((tau) => sigma.mul(tau).mul(sigma)));
  const [R] = R2.evalForPoly(T);
  const d = expectType(dense(R).discriminant(), (e): e is Rational => e instanceof Rational, 'integer discriminant');
  return [R, d.p];
}

/** @internal The Galois group of a quartic (Cohen, Alg. 6.3.6, with the resolvent from the lookup table). */
export function galoisGroupDegree4Lookup(T0: Poly, maxTries = 30, randomize = false): NamedGroup {
  const [R, T] = lookupResolvent(T0, 0, maxTries, randomize);
  const L = factorDegrees(R).join(',');
  if (L === '6') return hasSquareDisc(T) ? [S4TransitiveSubgroups.A4, true] : [S4TransitiveSubgroups.S4, false];
  if (L === '1,1,4') return [S4TransitiveSubgroups.C4, false];
  if (L === '2,2,2') return [S4TransitiveSubgroups.V, true];
  return [S4TransitiveSubgroups.D4, false];
}

/** @internal The Galois group of a quintic (Cohen, Alg. 6.3.9, combining the lookup table with root approximation). */
export function galoisGroupDegree5Hybrid(T0: Poly, maxTries = 30, randomize = false): NamedGroup {
  const X5 = variables(5);
  const [F51, , s51] = defined(defineResolvents().get('5,1'));
  const R51 = new Resolvent(F51.asExpr(...X5), X5, s51);
  const x = (i: number): Expr => cast(X5[i], Sym);
  const F2pre = [0, 1, 2, 3, 4].map((i) => mul(x(i), x((i + 1) % 5), x((i + 1) % 5))).reduce((a, b) => a.add(b));
  const s2pre = [new Permutation(4), new Permutation(4).call(0, 1).call(2, 4)];
  let T = T0;
  const history = new Set<string>();
  let secondStage = false;
  for (let i = 0; i < maxTries; i++) {
    if (i > 0) T = tschirnhausenTransformation(T, { maxTries, history, fixedOrder: !randomize })[1];
    const R51coeffs = getResolventByLookup(T, 1);
    const R51dup = dense(R51coeffs);
    if (!R51dup.isSqf) continue;
    // The group may still be S5, A5 or M20 before the second stage.
    if (!secondStage) {
      const sqDisc = hasSquareDisc(T);
      if (R51dup.isIrreducible) return sqDisc ? [S5TransitiveSubgroups.A5, true] : [S5TransitiveSubgroups.S5, false];
      if (!sqDisc) return [S5TransitiveSubgroups.M20, false];
    }
    secondStage = true;
    // R51 has an integer root; the conjugate of F51 that gives it selects the second resolvent.
    let i0 = 0;
    for (const [index, candidate] of R51.roundRootsToIntegersForPoly(T)) {
      i0 = index;
      if (R51coeffs.reduce((v, c) => v * candidate + c.p, 0n) === 0n) break;
    }
    const [, d] = secondResolvent(T, F2pre, s2pre, s51, i0, X5);
    if (d === 0n) continue;
    return isSquare(d) ? [S5TransitiveSubgroups.C5, true] : [S5TransitiveSubgroups.D5, true];
  }
  throw new MaxTriesException('no square-free quintic resolvent found');
}

/**
 * @internal The Galois group of a quintic (Cohen, Alg. 6.3.9, with the
 * resolvent from the lookup table, and a factorization over the field of a
 * root for the cyclic case).
 */
export function galoisGroupDegree5LookupExtFactor(T0: Poly, maxTries = 30, randomize = false): NamedGroup {
  const [R, T] = lookupResolvent(T0, 1, maxTries, randomize);
  const sqDisc = hasSquareDisc(T);
  if (R.isIrreducible) return sqDisc ? [S5TransitiveSubgroups.A5, true] : [S5TransitiveSubgroups.S5, false];
  if (!sqDisc) return [S5TransitiveSubgroups.M20, false];
  // Gal(T) is D5 or C5; it has order 5 exactly when T splits in the field of one of its roots.
  return splitsInRootField(T0) ? [S5TransitiveSubgroups.C5, true] : [S5TransitiveSubgroups.D5, true];
}

/**
 * Whether T splits into linear factors over Q(a) for a root a of T, from
 * Trager's square-free norm (only finitely many shifts fail to give one).
 */
function splitsInRootField(T: Poly): boolean {
  const x = cast(T.gen, Sym), a = new Dummy('a');
  const modulus = xreplace(T.asExpr(), [[x, a]]);
  for (let shift = 1; ; shift++) {
    const norm = Poly.from(resultant(modulus, xreplace(T.asExpr(), [[x, sub(x, mul(shift, a))]]), a), [x]);
    if (norm.isSqf) return factorDegrees(norm).length === T.degree();
  }
}

/** @internal The Galois group of a sextic (Cohen, Alg. 6.3.10, with resolvents from the lookup table). */
export function galoisGroupDegree6Lookup(T0: Poly, maxTries = 30, randomize = false): NamedGroup {
  const G = S6TransitiveSubgroups;
  const [R, T] = lookupResolvent(T0, 1, maxTries, randomize);
  const factors = R.factorList()[1].map(([f]) => f);
  const L = factors.map((f) => f.degree()).sort((a, b) => a - b).join(',');
  const ofDegree = (n: number): Poly[] => factors.filter((f) => f.degree() === n);
  const square = hasSquareDisc(T);
  if (L === '1,2,3') return hasSquareDisc(at(ofDegree(3), 0)) ? [G.C6, false] : [G.D6, false];
  if (L === '3,3') return ofDegree(3).some((f) => hasSquareDisc(f)) ? [G.G18, false] : [G.G36m, false];
  if (L === '2,4') return square ? [G.S4p, true] : hasSquareDisc(at(ofDegree(4), 0)) ? [G.A4xC2, false] : [G.S4xC2, false];
  if (L === '1,1,4') return square ? [G.A4, true] : [G.S4m, false];
  if (L === '1,5') return square ? [G.PSL2F5, true] : [G.PGL2F5, false];
  if (L === '1,1,1,3') return [G.S3, false];
  const [R2, T2] = lookupResolvent(T, 2, maxTries, randomize);
  const square2 = hasSquareDisc(T2);
  if (R2.isIrreducible) return square2 ? [G.A6, true] : [G.S6, false];
  return square2 ? [G.G36p, true] : [G.G72, false];
}

/**
 * The Galois group of an irreducible polynomial over ZZ or QQ of degree at most six: [G, alt], with
 * G a PermutationGroup, or with byName the member of S1TransitiveSubgroups... S6TransitiveSubgroups
 * naming it, and alt whether G is contained in the alternating group A_n. maxTries bounds the
 * Tschirnhausen transformations tried (MaxTriesException beyond it), and randomize chooses their
 * coefficients at random instead of in a fixed order.
 *
 * @param f - Irreducible univariate polynomial of degree at most six.
 * @param x - Polynomial variable, or the group options.
 * @param options - Group representation and resolvent-search settings.
 * @returns The group or its name and a flag for containment in the alternating group.
 * @throws RangeError when the polynomial is constant, reducible, multivariate, outside the rational
 *   or integer domains, or has degree greater than six.
 * @see SymPy `sympy.polys.numberfields.galoisgroups.galois_group`
 * @example
 * ```ts
 * import { ex, galoisGroup } from '@symjs/symjs';
 *
 * const [, alternating] = galoisGroup(ex`x**4 + 1`);
 * alternating; // => True
 * ```
 */
export function galoisGroup(f: Poly | ExprLike, x?: Sym | GaloisGroupOptions, options: GaloisGroupOptions = {}): GaloisGroupResult {
  const opts = x !== undefined && !(x instanceof Sym) ? x : options;
  const p = f instanceof Poly ? f : Poly.from(f, x instanceof Sym ? [x] : undefined);
  if (p.gens.length !== 1 || !['ZZ', 'QQ'].includes(p.domain) || !p.isIrreducible) throw new RangeError('Polynomial must be irreducible and univariate over ZZ or QQ.');
  const n = p.degree();
  if (n > 6) throw new RangeError('Only polynomials up to degree 6 are supported.');
  if (n < 1) throw new RangeError('Constant polynomial has no Galois group.');
  const { maxTries = 30, randomize = false } = opts;
  let named: NamedGroup;
  if (n === 1) named = [S1TransitiveSubgroups.S1, true];
  else if (n === 2) named = [S2TransitiveSubgroups.S2, false];
  else {
    const [T] = p.makeMonicOverIntegersByScalingRoots();
    named = n === 3 ? galoisGroupDegree3(T) : n === 4 ? galoisGroupDegree4Lookup(T, maxTries, randomize)
      : n === 5 ? galoisGroupDegree5LookupExtFactor(T, maxTries, randomize) : galoisGroupDegree6Lookup(T, maxTries, randomize);
  }
  const [name, alt] = named;
  return [opts.byName === true ? name : name.getPermGroup(), alt];
}

numberFieldHooks.galoisGroup = (K, options) => galoisGroup(K.ext.minpoly(), options);
