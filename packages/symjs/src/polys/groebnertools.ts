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
import type { Expr } from '../core/nodes';
import { groundGcd, groundLcm, groundQuo } from './compatibility';
import { monomialDivides, monomialLcm, monomialLdiv, monomialMul } from './monomial';
import type { MonomialKey } from './orderings';
import { compareMonomialKeys, lex } from './orderings';
import type { Monom, PolyElement } from './rings';
import { PolyRing } from './rings';

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

/** SymPy spoly(p1, p2, ring): the S-polynomial of two polynomials. */
export function spoly(p1: PolyElement, p2: PolyElement): PolyElement {
  const lcm = monomialLcm(p1.LM, p2.LM);
  return p1.mulMonom(monomialLdiv(lcm, p1.LM)).sub(p2.mulMonom(monomialLdiv(lcm, p2.LM)));
}

/** SymPy lbpSign(f): the signature of a labeled polynomial (lbpSign: core exports Num). */
export const lbpSign = (f: LabeledPolynomial): Signature => f[0];
/** SymPy lbpPolyn(f): the polynomial of a labeled polynomial. */
export const lbpPolyn = (f: LabeledPolynomial): PolyElement => f[1];
/** SymPy lbpNum(f): the number of a labeled polynomial. */
export const lbpNum = (f: LabeledPolynomial): number => f[2];
/** SymPy sig(monomial, index). */
export const sig = (monomial: Monom, index: number): Signature => [monomial, index];
/** SymPy lbp(signature, polynomial, number). */
export const lbp = (signature: Signature, polynomial: PolyElement, number: number): LabeledPolynomial => [signature, polynomial, number];

/** SymPy sig_cmp(u, v, order): -1 when u < v (a larger index, or the same index and a smaller monomial), else 1. */
export function sigCmp(u: Signature, v: Signature, ring: PolyRing): -1 | 1 {
  if (u[1] > v[1]) return -1;
  if (u[1] === v[1] && cmpKeys(orderKey(ring, u[0]), orderKey(ring, v[0])) < 0) return -1;
  return 1;
}

/** SymPy sig_key(s, order). */
export const sigKey = (s: Signature, ring: PolyRing): MonomialKey => [-s[1], orderKey(ring, s[0])];

/** SymPy sig_mult(s, m). */
export const sigMult = (s: Signature, m: Monom): Signature => sig(monomialMul(s[0], m), s[1]);

/** SymPy lbp_sub(f, g): the difference, labeled with the larger signature. */
export function lbpSub(f: LabeledPolynomial, g: LabeledPolynomial): LabeledPolynomial {
  const maxPoly = sigCmp(lbpSign(f), lbpSign(g), lbpPolyn(f).ring) < 0 ? g : f;
  return lbp(lbpSign(maxPoly), lbpPolyn(f).sub(lbpPolyn(g)), lbpNum(maxPoly));
}

/** SymPy lbp_mul_term(f, cx). */
export const lbpMulTerm = (f: LabeledPolynomial, cx: readonly [Monom, Expr]): LabeledPolynomial => lbp(sigMult(lbpSign(f), cx[0]), lbpPolyn(f).mulTerm(cx), lbpNum(f));

/** SymPy lbp_cmp(f, g): -1 when f < g (by signature, then by a larger number), else 1. */
export function lbpCmp(f: LabeledPolynomial, g: LabeledPolynomial): -1 | 1 {
  if (sigCmp(lbpSign(f), lbpSign(g), lbpPolyn(f).ring) === -1) return -1;
  if (sameSig(lbpSign(f), lbpSign(g)) && lbpNum(f) > lbpNum(g)) return -1;
  return 1;
}

/** SymPy lbp_key(f). */
export const lbpKey = (f: LabeledPolynomial): MonomialKey => [sigKey(lbpSign(f), lbpPolyn(f).ring), -lbpNum(f)];

/** SymPy critical_pair(f, g, ring): the critical pair of two labeled polynomials, the larger one first. */
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

/** SymPy cp_cmp(c, d). */
export function cpCmp(c: CriticalPair, d: CriticalPair): -1 | 1 {
  const zero = lbpPolyn(c[2]).ring.zero;
  if (lbpCmp(lbp(c[0], zero, lbpNum(c[2])), lbp(d[0], zero, lbpNum(d[2]))) === -1) return -1;
  // SymPy then compares the second signatures only when lbp_cmp returned 0, which it never does
  return 1;
}

/** SymPy cp_key(c, ring). */
export const cpKey = (c: CriticalPair, ring: PolyRing): MonomialKey => [lbpKey(lbp(c[0], ring.zero, lbpNum(c[2]))), lbpKey(lbp(c[3], ring.zero, lbpNum(c[5])))];

/** SymPy s_poly(cp): the S-polynomial of a critical pair. */
export const sPoly = (cp: CriticalPair): LabeledPolynomial => lbpSub(lbpMulTerm(cp[2], cp[1]), lbpMulTerm(cp[5], cp[4]));

/** SymPy is_rewritable_or_comparable(sign, num, B). */
export function isRewritableOrComparable(sign: Signature, num: number, B: readonly LabeledPolynomial[]): boolean {
  for (const h of B) {
    if (sign[1] < lbpSign(h)[1] && monomialDivides(lbpPolyn(h).LM, sign[0])) return true;
    if (sign[1] === lbpSign(h)[1] && num < lbpNum(h) && monomialDivides(lbpSign(h)[0], sign[0])) return true;
  }
  return false;
}

/** SymPy f5_reduce(f, B): f reduced by the labeled polynomials of B with smaller signatures. */
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

/** SymPy _f5b(F, ring): the reduced Groebner basis of F (over a field) by the F5B algorithm. */
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

/** SymPy red_groebner(G, ring): the reduced Groebner basis of a Groebner basis. */
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

/** SymPy is_groebner(G, ring): whether every S-polynomial reduces to zero. */
export function isGroebner(G: readonly PolyElement[]): boolean {
  for (let i = 0; i < G.length; i++) for (let j = i + 1; j < G.length; j++) if (!spoly(at(G, i), at(G, j)).rem([...G]).isZero) return false;
  return true;
}

/** SymPy is_minimal(G, ring): monic leading coefficients and no leading monomial dividing another. */
export function isMinimal(GIn: readonly PolyElement[], ring: PolyRing): boolean {
  const G = [...GIn].sort(byLM(ring));
  return G.every((g, i) => ring.domain.isOne(g.LC) && !G.some((h, j) => j !== i && monomialDivides(h.LM, g.LM)));
}

/** SymPy is_reduced(G, ring): monic and no monomial divisible by another leading monomial. */
export function isReduced(GIn: readonly PolyElement[], ring: PolyRing): boolean {
  const G = [...GIn].sort(byLM(ring));
  return G.every((g, i) => ring.domain.isOne(g.LC) && g.terms().every(([m]) => !G.some((h, j) => j !== i && monomialDivides(h.LM, m))));
}

/** SymPy groebner_lcm(f, g): the lcm of two polynomials by a Groebner basis of t*f, (1 - t)*g. */
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

/** SymPy groebner_gcd(f, g): the gcd of two polynomials as f*g / lcm(f, g). */
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

/** A reduced Groebner basis in a sparse polynomial ring, clearing denominators over rings. */
export function groebnerInRing(seq: readonly PolyElement[], ring: PolyRing): PolyElement[] {
  const field = ring.domain.isField ? ring : ring.withDomain(ring.domain.getField());
  const basis = f5b(seq.map((p) => field.fromExpr(p.asExpr())), field);
  return field === ring ? basis : basis.map((p) => ring.fromExpr(p.clearDenoms()[1].asExpr()));
}
