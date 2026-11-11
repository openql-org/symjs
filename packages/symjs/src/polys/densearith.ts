// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/densearith.py, BSD-3-Clause; see LICENSE.

/** Arithmetic of dense recursive polynomials, with leading coefficients first. */
import { ExactQuotientFailed } from '../core/errors';
import { at, first } from '../core/guard';
import { abs } from '../functions/elementary/elementary';
import { dmpDegree, dmpFromDict, dmpGround, dmpStrip, dmpToDict, dmpZero, dmpZeroP, groundIsZero } from './densebasic';
import type { DensePoly } from './densebasic';
import { domainArith, domainNeg, groundRational, PolynomialRing } from './domains';
import type { Domain } from './domains';
import { PolynomialDivisionFailed } from './polyerrors';

function list(f: unknown): DensePoly {
  if (!Array.isArray(f)) throw new TypeError('a dense polynomial level must be a list');
  return f;
}

function integer(n: number): number {
  const r = groundRational(n);
  if (r === undefined || r[1] !== 1n || !Number.isSafeInteger(Number(r[0]))) throw new RangeError('expected a safe integer');
  return Number(r[0]);
}

function zero(u: number, K: Domain): unknown {
  return u < 0 ? K.zero : dmpZero(u);
}

function isZero(f: unknown, u: number): boolean {
  return u < 0 ? groundIsZero(f) : dmpZeroP(list(f), u);
}

function sum(f: unknown, g: unknown, u: number, K: Domain, subtract = false): unknown {
  if (u < 0) return domainArith(K, subtract ? 'sub' : 'add', f, g);
  const [a, b] = [list(f), list(g)];
  const n = Math.max(a.length, b.length);
  const h = Array.from({ length: n }, (_, i) => sum(
    i < n - a.length ? zero(u - 1, K) : at(a, i - n + a.length),
    i < n - b.length ? zero(u - 1, K) : at(b, i - n + b.length), u - 1, K, subtract));
  return dmpStrip(h, u);
}

function product(f: unknown, g: unknown, u: number, K: Domain): unknown {
  if (u < 0) return domainArith(K, 'mul', f, g);
  if (isZero(f, u) || isZero(g, u)) return dmpZero(u);
  const [a, b] = [list(f), list(g)];
  const h = Array.from({ length: a.length + b.length - 1 }, () => zero(u - 1, K));
  for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) {
    h[i + j] = sum(at(h, i + j), product(at(a, i), at(b, j), u - 1, K), u - 1, K);
  }
  return dmpStrip(h, u);
}

function power(f: unknown, n: number, u: number, K: Domain): unknown {
  if (n < 0) throw new RangeError('Cannot raise polynomial to a negative power');
  let [b, e, h] = [f, n, u < 0 ? K.one : dmpGround(K.one, u)];
  while (e > 0) {
    if (e % 2) h = product(h, b, u, K);
    e = Math.floor(e / 2);
    if (e) b = product(b, b, u, K);
  }
  return h;
}

function term(f: DensePoly, c: unknown, i: number, u: number, K: Domain, subtract = false): unknown[] {
  if (isZero(c, u - 1)) return [...f];
  const h = [c, ...Array.from({ length: i }, () => zero(u - 1, K))];
  return [...list(sum(f, h, u, K, subtract))];
}

function mulTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] {
  if (isZero(f, u) || isZero(c, u - 1)) return dmpZero(u);
  return [...f.map((a) => product(a, c, u - 1, K)), ...Array.from({ length: i }, () => zero(u - 1, K))];
}

function mapGround(f: DensePoly, u: number, fn: (c: unknown) => unknown): unknown[] {
  return f.map((c) => u === 0 ? fn(c) : mapGround(list(c), u - 1, fn));
}

function mulGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] {
  if (u === 0 && groundIsZero(c)) return [];
  return f.map((a) => u === 0 ? domainArith(K, 'mul', a, c) : mulGround(list(a), c, u - 1, K));
}

function quoGround(f: DensePoly, c: unknown, u: number, K: Domain, exact: boolean): unknown[] {
  if (groundIsZero(c)) throw new RangeError('polynomial division by zero');
  return mapGround(f, u, (a) => {
    const [q, r] = groundDivide(a, c, K);
    if (exact && !groundIsZero(r)) throw new ExactQuotientFailed('ground coefficient does not divide exactly');
    return q;
  });
}

function groundDivide(a: unknown, b: unknown, K: Domain): [unknown, unknown] {
  if (K.isField) return [domainArith(K, 'quo', a, b), K.zero];
  if (K instanceof PolynomialRing) {
    const u = K.ngens - 1;
    const [q, r] = divide(dmpFromDict(K.toDict(a), u, K.dom), dmpFromDict(K.toDict(b), u, K.dom), u, K.dom, K.dom.isField);
    return [K.toSympy(dmpToDict(q, u)), K.toSympy(dmpToDict(r, u))];
  }
  return K.div(a, b);
}

/** Long division in the first variable; coefficient division is recursive. */
function divide(f: DensePoly, g: DensePoly, u: number, K: Domain, field: boolean, pseudo = false): [unknown[], unknown[]] {
  const roundoff = field && K.ground === 'RR' && u === 0;
  const dg = dmpDegree(g, u);
  if (dg < 0) throw new RangeError('polynomial division by zero');
  let q = dmpZero(u);
  let r = [...f];
  let dr = dmpDegree(r, u);
  if (dr < dg) return [q, r];
  const lc = first(g);
  let remaining = dr - dg + 1;
  while (dr >= dg) {
    const lead = first(r);
    let c: unknown;
    if (pseudo) {
      c = lead;
      q = mulTerm(q, lc, 0, u, K);
      r = mulTerm(r, lc, 0, u, K);
      remaining--;
    } else if (u > 0) {
      const [cq, cr] = divide(list(lead), list(lc), u - 1, K, field);
      if (!dmpZeroP(cr, u - 1)) break;
      c = cq;
    } else {
      const [cq, cr] = groundDivide(lead, lc, K);
      if (!groundIsZero(cr)) {
        if (field) throw new ExactQuotientFailed('leading coefficient does not divide exactly');
        break;
      }
      c = cq;
    }
    q = term(q, c, dr - dg, u, K);
    r = [...list(sum(r, mulTerm(g, c, dr - dg, u, K), u, K, true))];
    const previous = dr;
    dr = dmpDegree(r, u);
    if (dr >= dg && dr >= previous) {
      // Floating division can leave a rounded leading residue. Its degree
      // must still decrease, as in SymPy's dup_ff_div over inexact fields.
      if (roundoff) {
        r = dmpStrip(r.slice(1), 0);
        dr = dmpDegree(r, 0);
      } else throw new PolynomialDivisionFailed('polynomial division did not decrease the degree');
    }
  }
  if (pseudo) {
    const c = power(lc, remaining, u - 1, K);
    q = mulTerm(q, c, 0, u, K);
    r = mulTerm(r, c, 0, u, K);
  }
  return [q, r];
}

function exactQuotient(result: [unknown[], unknown[]], u: number): unknown[] {
  if (!dmpZeroP(result[1], u)) throw new ExactQuotientFailed('polynomial does not divide exactly');
  return result[0];
}

function absolute(c: unknown, K: Domain): unknown {
  return K.convert(abs(K.toSympy(c)));
}

function norm(f: DensePoly, u: number, K: Domain, kind: 'max' | 'l1' | 'l2'): unknown {
  let h: unknown = K.zero;
  for (const c of f) {
    const a = u > 0 ? norm(list(c), u - 1, K, kind) : kind === 'l2' ? domainArith(K, 'mul', c, c) : absolute(c, K);
    h = kind === 'max' ? K.isPositive(domainArith(K, 'sub', a, h)) ? a : h : domainArith(K, 'add', h, a);
  }
  return h;
}

/** Multiply a sequence of dense polynomials (SymPy dmp_expand). */
export function dmpExpand(polys: readonly DensePoly[], u: number, K: Domain): unknown[] {
  return polys.reduce<unknown[]>((h, f) => [...list(product(h, f, integer(u), K))], [...list(dmpGround(K.one, integer(u)))]);
}

/** Multiply a sequence of univariate polynomials (SymPy dup_expand). */
export function dupExpand(polys: readonly DensePoly[], K: Domain): unknown[] { return dmpExpand(polys, 0, K); }

/** Multiply by x**n (SymPy dup_lshift). */
export function dupLshift(f: DensePoly, n: number, K: Domain): unknown[] {
  return f.length === 0 ? [] : [...f, ...Array.from({ length: integer(n) }, () => K.zero)];
}

/** Remove the n trailing coefficients (SymPy dup_rshift). */
export function dupRshift(f: DensePoly, n: number, _K: Domain): unknown[] {
  const k = integer(n);
  // Dividing by x**0 is the identity. SymPy's f[:-0] incorrectly gives [].
  return k === 0 ? [...f] : f.slice(0, -k);
}

/** SymPy dup_add_term. */
export function dupAddTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return term(f, c, integer(i), 0, K); }

/** SymPy dup_sub_term. */
export function dupSubTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return term(f, c, integer(i), 0, K, true); }

/** SymPy dup_mul_term. */
export function dupMulTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return mulTerm(f, c, integer(i), 0, K); }

/** SymPy dup_add_ground. */
export function dupAddGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return term(f, dmpGround(c, 0 - 1), 0, 0, K); }

/** SymPy dup_sub_ground. */
export function dupSubGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return term(f, dmpGround(c, 0 - 1), 0, 0, K, true); }

/** SymPy dup_mul_ground. */
export function dupMulGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return mulGround(f, c, 0, K); }

/** SymPy dup_quo_ground. */
export function dupQuoGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return quoGround(f, c, 0, K, false); }

/** SymPy dup_exquo_ground. */
export function dupExquoGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return quoGround(f, c, 0, K, true); }

/** SymPy dup_abs. */
export function dupAbs(f: DensePoly, K: Domain): unknown[] { return mapGround(f, 0, (c) => absolute(c, K)); }

/** SymPy dup_neg. */
export function dupNeg(f: DensePoly, K: Domain): unknown[] { return mapGround(f, 0, (c) => domainNeg(K, c)); }

/** SymPy dup_add. */
export function dupAdd(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(sum(f, g, 0, K))]; }

/** SymPy dup_sub. */
export function dupSub(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(sum(f, g, 0, K, true))]; }

/** SymPy dup_mul. */
export function dupMul(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(product(f, g, 0, K))]; }

/** SymPy dup_add_mul. */
export function dupAddMul(f: DensePoly, g: DensePoly, h: DensePoly, K: Domain): unknown[] { return [...list(sum(f, product(g, h, 0, K), 0, K))]; }

/** SymPy dup_sub_mul. */
export function dupSubMul(f: DensePoly, g: DensePoly, h: DensePoly, K: Domain): unknown[] { return [...list(sum(f, product(g, h, 0, K), 0, K, true))]; }

/** SymPy dup_sqr. */
export function dupSqr(f: DensePoly, K: Domain): unknown[] { return [...list(product(f, f, 0, K))]; }

/** SymPy dup_pow. */
export function dupPow(f: DensePoly, n: number, K: Domain): unknown[] { return [...list(power(f, integer(n), 0, K))]; }

/** SymPy dup_pdiv. */
export function dupPdiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, false, true); }

/** SymPy dup_prem. */
export function dupPrem(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, false, true)[1]; }

/** SymPy dup_pquo. */
export function dupPquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, false, true)[0]; }

/** SymPy dup_pexquo. */
export function dupPexquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return exactQuotient(divide(f, g, 0, K, false, true), 0); }

/** SymPy dup_rr_div. */
export function dupRrDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, false); }

/** SymPy dup_ff_div. */
export function dupFfDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, true); }

/** SymPy dup_div. */
export function dupDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, K.isField); }

/** SymPy dup_rem. */
export function dupRem(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, K.isField)[1]; }

/** SymPy dup_quo. */
export function dupQuo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, K.isField)[0]; }

/** SymPy dup_exquo. */
export function dupExquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return exactQuotient(divide(f, g, 0, K, K.isField), 0); }

/** SymPy dup_max_norm. */
export function dupMaxNorm(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'max'); }

/** SymPy dup_l1_norm. */
export function dupL1Norm(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'l1'); }

/** SymPy dup_l2_norm_squared. */
export function dupL2NormSquared(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'l2'); }

/** SymPy dmp_add_term. */
export function dmpAddTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return term(f, c, integer(i), integer(u), K); }

/** SymPy dmp_sub_term. */
export function dmpSubTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return term(f, c, integer(i), integer(u), K, true); }

/** SymPy dmp_mul_term. */
export function dmpMulTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return mulTerm(f, c, integer(i), integer(u), K); }

/** SymPy dmp_add_ground. */
export function dmpAddGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return term(f, dmpGround(c, integer(u) - 1), 0, integer(u), K); }

/** SymPy dmp_sub_ground. */
export function dmpSubGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return term(f, dmpGround(c, integer(u) - 1), 0, integer(u), K, true); }

/** SymPy dmp_mul_ground. */
export function dmpMulGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return mulGround(f, c, integer(u), K); }

/** SymPy dmp_quo_ground. */
export function dmpQuoGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return quoGround(f, c, integer(u), K, false); }

/** SymPy dmp_exquo_ground. */
export function dmpExquoGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return quoGround(f, c, integer(u), K, true); }

/** SymPy dmp_abs. */
export function dmpAbs(f: DensePoly, u: number, K: Domain): unknown[] { return mapGround(f, integer(u), (c) => absolute(c, K)); }

/** SymPy dmp_neg. */
export function dmpNeg(f: DensePoly, u: number, K: Domain): unknown[] { return mapGround(f, integer(u), (c) => domainNeg(K, c)); }

/** SymPy dmp_add. */
export function dmpAdd(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, g, integer(u), K))]; }

/** SymPy dmp_sub. */
export function dmpSub(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, g, integer(u), K, true))]; }

/** SymPy dmp_mul. */
export function dmpMul(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(product(f, g, integer(u), K))]; }

/** SymPy dmp_add_mul. */
export function dmpAddMul(f: DensePoly, g: DensePoly, h: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, product(g, h, integer(u), K), integer(u), K))]; }

/** SymPy dmp_sub_mul. */
export function dmpSubMul(f: DensePoly, g: DensePoly, h: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, product(g, h, integer(u), K), integer(u), K, true))]; }

/** SymPy dmp_sqr. */
export function dmpSqr(f: DensePoly, u: number, K: Domain): unknown[] { return [...list(product(f, f, integer(u), K))]; }

/** SymPy dmp_pow. */
export function dmpPow(f: DensePoly, n: number, u: number, K: Domain): unknown[] { return [...list(power(f, integer(n), integer(u), K))]; }

/** SymPy dmp_pdiv. */
export function dmpPdiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, false, true); }

/** SymPy dmp_prem. */
export function dmpPrem(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, false, true)[1]; }

/** SymPy dmp_pquo. */
export function dmpPquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, false, true)[0]; }

/** SymPy dmp_pexquo. */
export function dmpPexquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return exactQuotient(divide(f, g, integer(u), K, false, true), integer(u)); }

/** SymPy dmp_rr_div. */
export function dmpRrDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, false); }

/** SymPy dmp_ff_div. */
export function dmpFfDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, true); }

/** SymPy dmp_div. */
export function dmpDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, K.isField); }

/** SymPy dmp_rem. */
export function dmpRem(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, K.isField)[1]; }

/** SymPy dmp_quo. */
export function dmpQuo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, K.isField)[0]; }

/** SymPy dmp_exquo. */
export function dmpExquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return exactQuotient(divide(f, g, integer(u), K, K.isField), integer(u)); }

/** SymPy dmp_max_norm. */
export function dmpMaxNorm(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'max'); }

/** SymPy dmp_l1_norm. */
export function dmpL1Norm(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'l1'); }

/** SymPy dmp_l2_norm_squared. */
export function dmpL2NormSquared(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'l2'); }
