// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/polys/groebnertools.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.polys.groebnertools on sparse polynomials (PolyElement):
 * the F5B algorithm with its labeled polynomials (signature, polynomial,
 * number), S-polynomials, the reduction of Groebner bases and the tests for
 * Groebner, minimal and reduced bases, and the lcm and gcd of polynomials by
 * Groebner bases. The public groebner() uses Buchberger's algorithm (a
 * reduced basis is unique).
 */

import { at, defined } from '../core/guard';
import { Dummy } from '../core/nodes';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { groundGcd, groundLcm, groundQuo } from './compatibility';
import { monomialDivides, monomialLcm, monomialLdiv, monomialMul } from './monomial';
import type { MonomialKey } from './orderings';
import { compareMonomialKeys, lex } from './orderings';
import type { Monom, PolyElement } from './rings';
import { PolyRing } from './rings';
import { GF } from './domains/finitefield';
import { constructDomain } from './constructor';
import { Poly } from './sympoly';
import { GroebnerBasis, groebner, type GroebnerOptions, type MonomialOrder } from './groebner';

/** A signature: a monomial and the index of an input polynomial. */
export type Signature = readonly [Monom, number];
/** A labeled polynomial: its signature, the polynomial and its number. */
export type LabeledPolynomial = readonly [Signature, PolyElement, number];
/** A critical pair: (signature, multiplier term, labeled polynomial) for each of the two polynomials. */
export type CriticalPair = readonly [Signature, readonly [Monom, Expr], LabeledPolynomial, Signature, readonly [Monom, Expr], LabeledPolynomial];

const orderKey = (ring: PolyRing, m: Monom): MonomialKey => ring.order.key(m);
const cmpKeys = (a: MonomialKey, b: MonomialKey): number => compareMonomialKeys(a, b);
const sameSig = (u: Signature, v: Signature): boolean => u[1] === v[1] && u[0].length === v[0].length && u[0].every((e, i) => e === v[0][i]);
const sameLbp = (f: LabeledPolynomial, g: LabeledPolynomial): boolean => sameSig(f[0], g[0]) && f[1].equals(g[1]) && f[2] === g[2];

/** The quotient of two terms (the monomial divides). */
function termDiv(a: readonly [Monom, Expr], b: readonly [Monom, Expr], ring: PolyRing): readonly [Monom, Expr] {
  // the callers divide a multiple of b (an lcm or a checked leading monomial)
  return [monomialLdiv(a[0], b[0]), groundQuo(ring.domain, a[1], b[1])];
}

/**
 * Cancels the leading terms of two polynomials using their least common multiple.
 *
 * @param p1 - First polynomial.
 * @param p2 - Second polynomial.
 * @returns The S-polynomial.
 * @see SymPy `sympy.polys.groebnertools.spoly`
 */
export function spoly(p1: PolyElement, p2: PolyElement): PolyElement {
  const lcm = monomialLcm(p1.LM, p2.LM);
  return p1.mulMonom(monomialLdiv(lcm, p1.LM)).sub(p2.mulMonom(monomialLdiv(lcm, p2.LM)));
}

/**
 * Extracts the signature attached to a labeled polynomial.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @returns The monomial and input index.
 * @see SymPy `sympy.polys.groebnertools.Sign`
 */
export const lbpSign = (f: LabeledPolynomial): Signature => f[0];
/**
 * Extracts the polynomial carried by an F5 label.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @returns The polynomial component.
 * @see SymPy `sympy.polys.groebnertools.Polyn`
 */
export const lbpPolyn = (f: LabeledPolynomial): PolyElement => f[1];
/**
 * Reads the sequence number assigned to a labeled polynomial.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @returns The label number.
 * @see SymPy `sympy.polys.groebnertools.Num`
 */
export const lbpNum = (f: LabeledPolynomial): number => f[2];
/**
 * Forms a signature from a monomial and its input polynomial's index.
 *
 * @param monomial - Exponent vector of the monomial.
 * @param index - Zero-based index.
 * @returns A monomial–index pair.
 * @see SymPy `sympy.polys.groebnertools.sig`
 */
export const sig = (monomial: Monom, index: number): Signature => [monomial, index];
/**
 * Construct a labeled polynomial from its signature, polynomial and sequence number.
 *
 * @param signature - Signature of the polynomial.
 * @param polynomial - Polynomial to operate on.
 * @param number - Sequence number of the labeled polynomial.
 * @returns The signature, polynomial and sequence number as a labeled polynomial.
 * @see SymPy `sympy.polys.groebnertools.lbp`
 */
export const lbp = (signature: Signature, polynomial: PolyElement, number: number): LabeledPolynomial => [signature, polynomial, number];

/**
 * Compares signatures by decreasing input index, then by increasing monomial order.
 *
 * @param u - First signature to compare.
 * @param v - Second signature.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns `-1` if the first precedes the second, otherwise `1`.
 * @see SymPy `sympy.polys.groebnertools.sig_cmp`
 */
export function sigCmp(u: Signature, v: Signature, ring: PolyRing): -1 | 1 {
  if (u[1] > v[1]) return -1;
  if (u[1] === v[1] && cmpKeys(orderKey(ring, u[0]), orderKey(ring, v[0])) < 0) return -1;
  return 1;
}

/**
 * Builds the comparison key for a signature in the ring's monomial order.
 *
 * @param s - Signature of the labeled polynomial.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns The signature ordering key.
 * @see SymPy `sympy.polys.groebnertools.sig_key`
 */
export const sigKey = (s: Signature, ring: PolyRing): MonomialKey => [-s[1], orderKey(ring, s[0])];

/**
 * Multiplies the monomial part of a signature by the supplied monomial.
 *
 * @param s - Signature of the labeled polynomial.
 * @param m - Exponent vector multiplying the signature.
 * @returns The updated signature.
 * @see SymPy `sympy.polys.groebnertools.sig_mult`
 */
export const sigMult = (s: Signature, m: Monom): Signature => sig(monomialMul(s[0], m), s[1]);

/**
 * Subtracts two labeled polynomials and retains the larger signature.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @param g - Second polynomial operand.
 * @returns The labeled difference.
 * @see SymPy `sympy.polys.groebnertools.lbp_sub`
 */
export function lbpSub(f: LabeledPolynomial, g: LabeledPolynomial): LabeledPolynomial {
  const maxPoly = sigCmp(lbpSign(f), lbpSign(g), lbpPolyn(f).ring) < 0 ? g : f;
  return lbp(lbpSign(maxPoly), lbpPolyn(f).sub(lbpPolyn(g)), lbpNum(maxPoly));
}

/**
 * Scales a labeled polynomial by a term and multiplies its signature by the term's monomial.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @param cx - Monomial and coefficient of the multiplier.
 * @returns The labeled product.
 * @see SymPy `sympy.polys.groebnertools.lbp_mul_term`
 */
export const lbpMulTerm = (f: LabeledPolynomial, cx: readonly [Monom, Expr]): LabeledPolynomial => lbp(sigMult(lbpSign(f), cx[0]), lbpPolyn(f).mulTerm(cx), lbpNum(f));

/**
 * Orders labeled polynomials by signature, breaking ties by decreasing label number.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @param g - Second polynomial operand.
 * @returns `-1` if the first precedes the second, otherwise `1`.
 * @see SymPy `sympy.polys.groebnertools.lbp_cmp`
 */
export function lbpCmp(f: LabeledPolynomial, g: LabeledPolynomial): -1 | 1 {
  if (sigCmp(lbpSign(f), lbpSign(g), lbpPolyn(f).ring) === -1) return -1;
  if (sameSig(lbpSign(f), lbpSign(g)) && lbpNum(f) > lbpNum(g)) return -1;
  return 1;
}

/**
 * Combines the signature key and label number for ordering.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @returns The labeled polynomial's comparison key.
 * @see SymPy `sympy.polys.groebnertools.lbp_key`
 */
export const lbpKey = (f: LabeledPolynomial): MonomialKey => [sigKey(lbpSign(f), lbpPolyn(f).ring), -lbpNum(f)];

/**
 * Constructs the critical pair with the larger labeled multiple first.
 *
 * @param f - Labeled polynomial with its signature and sequence number.
 * @param g - Second polynomial operand.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns The ordered critical pair.
 * @see SymPy `sympy.polys.groebnertools.critical_pair`
 */
export function criticalPair(f: LabeledPolynomial, g: LabeledPolynomial, ring: PolyRing): CriticalPair {
  const ltf = lbpPolyn(f).LT;
  const ltg = lbpPolyn(g).LT;
  const lt: readonly [Monom, Expr] = [monomialLcm(ltf[0], ltg[0]), ring.domain.one];
  const um = termDiv(lt, ltf, ring);
  const vm = termDiv(lt, ltg, ring);
  const fr = lbpMulTerm(lbp(lbpSign(f), lbpPolyn(f).leadingTerm(), lbpNum(f)), um);
  const gr = lbpMulTerm(lbp(lbpSign(g), lbpPolyn(g).leadingTerm(), lbpNum(g)), vm);
  return lbpCmp(fr, gr) === -1 ? [lbpSign(gr), vm, g, lbpSign(fr), um, f] : [lbpSign(fr), um, f, lbpSign(gr), vm, g];
}

/**
 * Orders critical pairs by their leading labeled signatures.
 *
 * @param c - Critical pair to compare or order.
 * @param d - Critical pair to compare or order.
 * @returns `-1` if the first precedes the second, otherwise `1`.
 * @see SymPy `sympy.polys.groebnertools.cp_cmp`
 */
export function cpCmp(c: CriticalPair, d: CriticalPair): -1 | 1 {
  const zero = lbpPolyn(c[2]).ring.zero;
  if (lbpCmp(lbp(c[0], zero, lbpNum(c[2])), lbp(d[0], zero, lbpNum(d[2]))) === -1) return -1;
  // SymPy then compares the second signatures only when lbp_cmp returned 0, which it never does
  return 1;
}

/**
 * Builds the comparison key for a critical pair.
 *
 * @param c - Critical pair to compare or order.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns The critical-pair ordering key.
 * @see SymPy `sympy.polys.groebnertools.cp_key`
 */
export const cpKey = (c: CriticalPair, ring: PolyRing): MonomialKey => [lbpKey(lbp(c[0], ring.zero, lbpNum(c[2]))), lbpKey(lbp(c[3], ring.zero, lbpNum(c[5])))];

/**
 * Combines the labeled multiples in a critical pair to cancel their leading terms.
 *
 * @param cp - Critical pair.
 * @returns The labeled S-polynomial.
 * @see SymPy `sympy.polys.groebnertools.s_poly`
 */
export const sPoly = (cp: CriticalPair): LabeledPolynomial => lbpSub(lbpMulTerm(cp[2], cp[1]), lbpMulTerm(cp[5], cp[4]));

/**
 * Applies the F5 rewriting and comparability criteria to a signature.
 *
 * @param sign - Signature to test.
 * @param num - Numerator.
 * @param B - Second exponent vector.
 * @returns True if the signature can be discarded.
 * @see SymPy `sympy.polys.groebnertools.is_rewritable_or_comparable`
 */
export function isRewritableOrComparable(sign: Signature, num: number, B: readonly LabeledPolynomial[]): boolean {
  for (const h of B) {
    if (sign[1] < lbpSign(h)[1] && monomialDivides(lbpPolyn(h).LM, sign[0])) return true;
    if (sign[1] === lbpSign(h)[1] && num < lbpNum(h) && monomialDivides(lbpSign(h)[0], sign[0])) return true;
  }
  return false;
}

/**
 * Reduces the labeled polynomial using only basis elements with smaller signatures.
 *
 * @param fIn - Labeled polynomial with its signature and sequence number.
 * @param B - Second exponent vector.
 * @returns The reduced labeled polynomial.
 * @see SymPy `sympy.polys.groebnertools.f5_reduce`
 * @remarks SymPy returns `(((1, 1, 1), 4), x, 3)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { QQ, f5Reduce, ring } from '@symjs/symjs';
 *
 * const [, x] = ring('x, y, z', QQ);
 * f5Reduce([[[1, 1, 1], 4], x, 3], [[[[0, 0, 0], 2], x, 2]]); // => [[[1, 1, 1], 4], x, 3]
 * ```
 */
export function f5Reduce(fIn: LabeledPolynomial, B: readonly LabeledPolynomial[]): LabeledPolynomial {
  let f = fIn;
  const ring = lbpPolyn(f).ring;
  if (lbpPolyn(f).isZero) return f;
  for (;;) {
    const g = f;
    for (const h of B) {
      if (!lbpPolyn(h).isZero && monomialDivides(lbpPolyn(h).LM, lbpPolyn(f).LM)) {
        const t = termDiv(lbpPolyn(f).LT, lbpPolyn(h).LT, ring);
        if (sigCmp(sigMult(lbpSign(h), t[0]), lbpSign(f), ring) < 0) {
          f = lbpSub(f, lbpMulTerm(h, t));
          break;
        }
      }
    }
    if (sameLbp(g, f) || lbpPolyn(f).isZero) return f;
  }
}

const byLM = (ring: PolyRing) => (a: PolyElement, b: PolyElement): number => cmpKeys(orderKey(ring, a.LM), orderKey(ring, b.LM));

type SparsePair = readonly [PolyElement, PolyElement, Monom];

/** SymPy's improved Buchberger algorithm, with pairs ordered by their least common monomial. */
function buchberger(input: readonly PolyElement[], ring: PolyRing): PolyElement[] {
  const order = byLM(ring);
  let initial = [...input];
  for (;;) {
    const reduced = initial.map((g, i) => g.rem(initial.slice(0, i)))
      .filter((g) => !g.isZero).map((g) => g.monic());
    if (initial.length === reduced.length && initial.every((g, i) => g.equals(at(reduced, i)))) break;
    initial = reduced;
  }
  let basis: PolyElement[] = [];
  let pairs: SparsePair[] = [];
  const update = (h: PolyElement): void => {
    const mh = h.LM;
    const pending: SparsePair[] = basis.map((g) => [h, g, monomialLcm(mh, g.LM)]);
    const retained: SparsePair[] = [];
    const relativelyPrime = ([f, g, m]: SparsePair) => monomialMul(f.LM, g.LM).every((e, i) => e === at(m, i));
    while (pending.length) {
      const candidate = defined(pending.pop());
      const dominated = (p: SparsePair) => monomialDivides(p[2], candidate[2]);
      if (relativelyPrime(candidate) || (!pending.some(dominated) && !retained.some(dominated))) retained.push(candidate);
    }
    const sameMonomial = (a: Monom, b: Monom) => a.every((e, i) => e === at(b, i));
    pairs = pairs.filter(([a, b, m]) => !monomialDivides(mh, m)
      || sameMonomial(monomialLcm(a.LM, mh), m) || sameMonomial(monomialLcm(b.LM, mh), m));
    pairs.push(...retained.filter((pair) => !relativelyPrime(pair)));
    basis = basis.filter((g) => !monomialDivides(mh, g.LM));
    basis.push(h);
  };
  initial.sort(order);
  for (const g of initial) update(g);
  while (pairs.length) {
    let index = 0;
    for (let i = 1; i < pairs.length; i++) {
      if (ring.order.compare(at(pairs, i)[2], at(pairs, index)[2]) < 0) index = i;
    }
    const [a, b] = at(pairs.splice(index, 1), 0);
    const remainder = spoly(a, b).rem([...basis].sort(order));
    if (!remainder.isZero) update(remainder.monic());
  }
  return redGroebner(basis).sort((a, b) => order(b, a));
}

/**
 * Computes a reduced Gröbner basis over a field using F5B.
 *
 * @param FIn - Input polynomials.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns The reduced basis polynomials.
 * @see SymPy `sympy.polys.groebnertools._f5b`
 */
export function f5b(FIn: readonly PolyElement[], ring: PolyRing): PolyElement[] {
  // the input interreduced
  let B: PolyElement[] = [...FIn];
  let F: PolyElement[];
  for (;;) {
    F = B;
    B = [];
    for (let i = 0; i < F.length; i++) {
      const r = at(F, i).rem(F.slice(0, i));
      if (!r.isZero) B.push(r);
    }
    if (F.length === B.length && F.every((p, i) => p.equals(at(B, i)))) break;
  }
  const descLM = (a: LabeledPolynomial, b: LabeledPolynomial): number => byLM(ring)(lbpPolyn(b), lbpPolyn(a));
  const L: LabeledPolynomial[] = F.map((p, i) => lbp(sig(ring.zeroMonom, i + 1), p, i + 1)).sort(descLM);
  const descCp = (a: CriticalPair, b: CriticalPair): number => cmpKeys(cpKey(b, ring), cpKey(a, ring));
  let CP: CriticalPair[] = [];
  for (let i = 0; i < L.length; i++) for (let j = i + 1; j < L.length; j++) CP.push(criticalPair(at(L, i), at(L, j), ring));
  CP.sort(descCp);
  let k = L.length;
  while (CP.length) {
    const cp = defined(CP.pop(), 'critical pair');
    if (isRewritableOrComparable(cp[0], lbpNum(cp[2]), L) || isRewritableOrComparable(cp[3], lbpNum(cp[5]), L)) continue;
    const s = sPoly(cp);
    const r = f5Reduce(s, L);
    const p = lbp(lbpSign(r), lbpPolyn(r).monic(), k + 1);
    if (lbpPolyn(p).isZero) continue;
    CP = CP.filter((c) => !(isRewritableOrComparable(c[0], lbpNum(c[2]), [p]) || isRewritableOrComparable(c[3], lbpNum(c[5]), [p])));
    // the labeled polynomials of L are nonzero (SymPy also tests Polyn(g))
    for (const g of L) {
      const c = criticalPair(p, g, ring);
      if (isRewritableOrComparable(c[0], lbpNum(c[2]), [p]) || isRewritableOrComparable(c[3], lbpNum(c[5]), [p])) continue;
      CP.push(c);
    }
    CP.sort(descCp);
    const m = orderKey(ring, lbpPolyn(p).LM);
    if (cmpKeys(m, orderKey(ring, lbpPolyn(at(L, L.length - 1)).LM)) <= 0) L.push(p);
    else L.splice(L.findIndex((q) => cmpKeys(m, orderKey(ring, lbpPolyn(q).LM)) > 0), 0, p);
    k++;
  }
  return redGroebner(L.map((g) => lbpPolyn(g).monic())).sort((a, b) => byLM(ring)(b, a));
}

/**
 * Reduces a Gröbner basis to its canonical reduced basis.
 *
 * @param G - Polynomials of the candidate basis.
 * @returns The reduced basis polynomials.
 * @see SymPy `sympy.polys.groebnertools.red_groebner`
 */
export function redGroebner(G: readonly PolyElement[]): PolyElement[] {
  const F = [...G];
  const H: PolyElement[] = [];
  while (F.length) {
    const f0 = defined(F.pop(), 'polynomial');
    if (![...F, ...H].some((f) => monomialDivides(f.LM, f0.LM))) H.push(f0);
  }
  return H.map((p, i) => p.rem([...H.slice(0, i), ...H.slice(i + 1)]))
    .filter((h) => !h.isZero)
    .map((p) => p.monic());
}

/**
 * Checks the Gröbner basis criterion by reducing every S-polynomial.
 *
 * @param G - Polynomials of the candidate basis.
 * @returns True if all remainders vanish.
 * @see SymPy `sympy.polys.groebnertools.is_groebner`
 */
export function isGroebner(G: readonly PolyElement[]): boolean {
  for (let i = 0; i < G.length; i++) for (let j = i + 1; j < G.length; j++) if (!spoly(at(G, i), at(G, j)).rem([...G]).isZero) return false;
  return true;
}

/**
 * Tests for monicity and pairwise nondivisibility of the leading monomials.
 *
 * @param GIn - Basis polynomials.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns Whether the leading monomials and coefficients form a minimal basis.
 * @see SymPy `sympy.polys.groebnertools.is_minimal`
 */
export function isMinimal(GIn: readonly PolyElement[], ring: PolyRing): boolean {
  const G = [...GIn].sort(byLM(ring));
  return G.every((g, i) => ring.domain.isOne(g.LC) && !G.some((h, j) => j !== i && monomialDivides(h.LM, g.LM)));
}

/**
 * Tests whether a monic basis has no term divisible by another basis element's leading monomial.
 *
 * @param GIn - Basis polynomials.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @returns Whether the basis is monic and every tail is reduced against the other leading monomials.
 * @see SymPy `sympy.polys.groebnertools.is_reduced`
 */
export function isReduced(GIn: readonly PolyElement[], ring: PolyRing): boolean {
  const G = [...GIn].sort(byLM(ring));
  return G.every((g, i) => ring.domain.isOne(g.LC) && g.terms().every(([m]) => !G.some((h, j) => j !== i && monomialDivides(h.LM, m))));
}

/**
 * Finds the LCM by eliminating the auxiliary variable from `t*f` and `(1 - t)*g`.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @returns The polynomial LCM.
 * @throws RangeError when the operands belong to different polynomial rings.
 * @see SymPy `sympy.polys.groebnertools.groebner_lcm`
 */
export function groebnerLcm(f: PolyElement, g: PolyElement): PolyElement {
  if (f.ring !== g.ring) throw new RangeError('Values should be equal');
  const ring = f.ring;
  const domain = ring.domain;
  if (f.isZero || g.isZero) return ring.zero;
  if (f.length <= 1 && g.length <= 1) return ring.termNew(monomialLcm(f.LM, g.LM), groundLcm(domain, f.LC, g.LC));
  const [fc, fp] = f.primitive();
  const [gc, gp] = g.primitive();
  const lcm = groundLcm(domain, fc, gc);
  const t = new Dummy('t');
  const tRing = new PolyRing([t, ...ring.symbols], domain, lex);
  const F = tRing.fromTerms(fp.terms().map(([m, c]) => [[1, ...m], c] as const));
  const G = tRing.fromTerms([...gp.terms().map(([m, c]) => [[0, ...m], c] as const), ...gp.terms().map(([m, c]) => [[1, ...m], c.neg()] as const)]);
  const basis = groebnerOf([F, G], tRing);
  const h = defined(basis.find((b) => b.monoms().every((m) => at(m, 0) === 0)), 'basis element without t');
  return ring.fromTerms(h.terms().map(([m, c]) => [m.slice(1), c.mul(lcm)] as const));
}

/**
 * Obtains the GCD by dividing the product of the inputs by their LCM.
 *
 * @param fIn - Polynomial to operate on.
 * @param gIn - Second polynomial operand.
 * @returns The polynomial GCD.
 * @throws RangeError when the operands belong to different polynomial rings.
 * @see SymPy `sympy.polys.groebnertools.groebner_gcd`
 */
export function groebnerGcd(fIn: PolyElement, gIn: PolyElement): PolyElement {
  if (fIn.ring !== gIn.ring) throw new RangeError('Values should be equal');
  const domain = fIn.ring.domain;
  let f = fIn;
  let g = gIn;
  let gcd: Expr | undefined;
  if (!domain.isField) {
    const [fc, fp] = f.primitive();
    const [gc, gp] = g.primitive();
    f = fp;
    g = gp;
    gcd = groundGcd(domain, fc, gc);
  }
  const q = f.mul(g).div(groebnerLcm(f, g))[0];
  return gcd === undefined ? q.monic() : q.mulGround(gcd);
}

/** SymPy groebnertools.groebner(seq, ring, method) over the field of the ring's domain, with the denominators cleared back. */
function groebnerOf(seq: readonly PolyElement[], ring: PolyRing): PolyElement[] {
  const domain = ring.domain;
  if (domain.isField) return f5b(seq, ring);
  const field = ring.withDomain(domain.getField());
  return f5b(seq.map((s) => s.setRing(field)), field).map((g) => g.clearDenoms()[1].setRing(ring));
}

/**
 * Computes a reduced basis in a sparse polynomial ring, clearing denominators for ring coefficients.
 *
 * @param seq - Sequence of polynomials.
 * @param ring - Polynomial ring supplying the generators and coefficient domain.
 * @param method - Algorithm to use.
 * @returns The basis polynomials.
 * @throws RangeError when the algorithm name is unrecognized.
 * @see SymPy `sympy.polys.groebnertools.groebner`
 */
export function groebnerInRing(seq: readonly PolyElement[], ring: PolyRing, method = 'buchberger'): PolyElement[] {
  if (method !== 'f5b' && method !== 'buchberger') throw new RangeError(`unknown Groebner basis method: ${method}`);
  const field = ring.domain.isField ? ring : ring.withDomain(ring.domain.getField());
  const basis = (method === 'f5b' ? f5b : buchberger)(seq.map((p) => p.setRing(field)), field);
  return field === ring ? basis : basis.map((p) => p.clearDenoms()[1].setRing(ring));
}

/**
 * Computes a reduced Gröbner basis using the supplied coefficient domain when specified.
 *
 * @param F - Input polynomials.
 * @param gens - Polynomial generators in the desired order.
 * @param order - Monomial order used to compare terms.
 * @param opts - Coefficient-domain settings, the basis `method`, and `polys` to yield polynomial objects.
 * @returns The basis polynomials.
 * @see SymPy `sympy.polys.polytools.groebner`
 * @example
 * ```ts
 * import { ex, groebner, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * groebner([ex`x*y - 2*y`, ex`-x**2 + 2*y**2`], [x, y]).exprs; // => [x**2 - 2*y**2, x*y - 2*y, y**3 - 2*y]
 * ```
 */
export function groebnerWithDomain(F: readonly ExprLike[], gens: readonly Sym[], order: MonomialOrder = 'lex', opts: GroebnerOptions = {}): GroebnerBasis {
  return groebner(F, gens, order, opts, (polys, generators, ordering, options) => {
    const extension = options.extension === true ? true : undefined;
    const domain = options.modulus === undefined ? options.domain ?? constructDomain(polys.flatMap((p) => p.coeffs()), { extension, field: options.field })[0]
      : GF(options.modulus, options.symmetric ?? true);
    const ring = new PolyRing(generators, domain, ordering);
    const basis = groebnerInRing(polys.map((p) => ring.fromExpr(p.asExpr())), ring, options.method);
    const exprs = basis.map((g) => ring.domain.isExact ? g.asExpr() : Poly.from(g.asExpr(), generators, { domain: ring.domain }).asExpr());
    return new GroebnerBasis(exprs, generators, String(ring.domain), ordering, options.polys, ring);
  });
}
