// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/densetools.py, BSD-3-Clause; see LICENSE.

/** Advanced tools for dense recursive polynomials in K[x] or K[X], with leading coefficients first. */
import { isNegative as isNegativeExpr } from '../core/assumptions';
import { DomainError } from '../core/errors';
import { at, first } from '../core/guard';
import { asNumerDenom } from '../core/methods';
import { Dummy } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import {
  dmpAdd, dmpAddTerm, dmpExquoGround, dmpMul, dmpMulGround, dmpQuoGround, dmpRem, dmpSub, dupAdd, dupAddTerm,
  dupDiv, dupExquoGround, dupLshift, dupMul, dupMulGround, dupQuoGround, dupRem, dupSqr, dupSub,
} from './densearith';
import {
  dmpConvert, dmpDegree, dmpFromDict, dmpGround, dmpGroundLC, dmpInclude, dmpStrip, dmpToDict, dmpZero, dmpZeroP,
  dmpZeros, dupConvert, dupDegree, dupFromRawDict, dupStrip, groundEquals, groundIsZero, polyLC, polyTC,
} from './densebasic';
import type { DensePoly } from './densebasic';
import { domainArith, domainNeg, ExpressionDomain, FractionField, groundRational, IntegerRing, PolynomialRing, QQ, RationalField, RealField } from './domains';
import type { Domain } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { FiniteField } from './domains/finitefield';
import { GaussianDomain, GaussianRationalField } from './domains/gaussiandomains';
import { MultivariatePolynomialError, NotReversible } from './polyerrors';
import { lcmList, Poly, resultant } from './sympoly';

function list(f: unknown): DensePoly {
  if (!Array.isArray(f)) throw new TypeError('a dense polynomial level must be a list');
  return f;
}

function integer(n: unknown): number {
  const r = groundRational(n);
  if (r === undefined || r[1] !== 1n || !Number.isSafeInteger(Number(r[0]))) throw new RangeError('expected a safe integer');
  return Number(r[0]);
}

const mulInt = (K: Domain, c: unknown, n: number): unknown => domainArith(K, 'mul', BigInt(n), c);

/** The quotient a // b of ground elements of K (SymPy K.quo). */
function groundQuo(a: unknown, b: unknown, K: Domain): unknown {
  return first(dupQuoGround([a], b, K));
}

/** The exact quotient a / b of ground elements of K (SymPy K.exquo). */
function groundExquo(a: unknown, b: unknown, K: Domain): unknown {
  return first(dupExquoGround([a], b, K));
}

/** The falling factorial n*(n-1)*...*(n-m+1). */
function falling(n: number, m: number): number {
  let k = n;
  for (let i = n - 1; i > n - m; i--) k *= i;
  return k;
}

/** The rising product (i+1)*(i+2)*...*(i+m). */
function rising(i: number, m: number): number {
  let n = i + 1;
  for (let j = 1; j < m; j++) n *= i + j + 1;
  return n;
}

/** Computes the indefinite integral of f in x_0 (SymPy dup_integrate). */
export function dupIntegrate(f: DensePoly, m: number, K: Domain): unknown[] {
  const n = integer(m);
  if (n <= 0 || !f.length) return [...f];
  const g: unknown[] = Array.from({ length: n }, () => K.zero);
  [...f].reverse().forEach((c, i) => g.unshift(groundExquo(c, BigInt(rising(i, n)), K)));
  return g;
}

/** Computes the indefinite integral of f in x_0 (SymPy dmp_integrate). */
export function dmpIntegrate(f: DensePoly, m: number, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupIntegrate(f, m, K);
  const n = integer(m);
  if (n <= 0 || dmpZeroP(f, v)) return [...f];
  const g = dmpZeros(n, v - 1, K);
  [...f].reverse().forEach((c, i) => g.unshift(dmpQuoGround(list(c), BigInt(rising(i, n)), v - 1, K)));
  return g;
}

function checkIndex(j: number, u: number): void {
  if (j < 0 || j > u) throw new RangeError(`0 <= j <= ${u} expected, got ${j}`);
}

/** Apply op to the coefficients in x_j through the outer levels; `drop` is 1 when op removes x_j (SymPy _rec_*_in). */
function recIn(g: DensePoly, v: number, i: number, j: number, op: (h: DensePoly, w: number) => unknown, drop = 0): unknown {
  if (i === j) return op(g, v);
  return dmpStrip(g.map((c) => recIn(list(c), v - 1, i + 1, j, op, drop)), v - drop);
}

/** Computes the indefinite integral of f in x_j (SymPy dmp_integrate_in). */
export function dmpIntegrateIn(f: DensePoly, m: number, j: number, u: number, K: Domain): unknown[] {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return [...list(recIn(f, uu, 0, jj, (h, w) => dmpIntegrate(h, m, w, K)))];
}

/** The m-th order derivative of f in x_0 (SymPy dup_diff). */
export function dupDiff(f: DensePoly, m: number, K: Domain): unknown[] {
  const k = integer(m);
  if (k <= 0) return [...f];
  let n = dupDegree(f);
  if (n < k) return [];
  const deriv: unknown[] = [];
  for (const coeff of f.slice(0, -k)) {
    deriv.push(mulInt(K, coeff, falling(n, k)));
    n--;
  }
  return dupStrip(deriv);
}

/** The m-th order derivative of f in x_0 (SymPy dmp_diff). */
export function dmpDiff(f: DensePoly, m: number, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupDiff(f, m, K);
  const k = integer(m);
  if (k <= 0) return [...f];
  let n = dmpDegree(f, v);
  if (n < k) return dmpZero(v);
  const deriv: unknown[] = [];
  for (const coeff of f.slice(0, -k)) {
    deriv.push(dmpMulGround(list(coeff), BigInt(falling(n, k)), v - 1, K));
    n--;
  }
  return dmpStrip(deriv, v);
}

/** The m-th order derivative of f in x_j (SymPy dmp_diff_in). */
export function dmpDiffIn(f: DensePoly, m: number, j: number, u: number, K: Domain): unknown[] {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return [...list(recIn(f, uu, 0, jj, (h, w) => dmpDiff(h, m, w, K)))];
}

/** Evaluate f at x = a with Horner's scheme (SymPy dup_eval). */
export function dupEval(f: DensePoly, a: unknown, K: Domain): unknown {
  if (groundIsZero(a)) return K.convert(polyTC(f, K));
  let result: unknown = K.zero;
  for (const c of f) result = domainArith(K, 'add', domainArith(K, 'mul', result, a), c);
  return result;
}

/** Evaluate f at x_0 = a with Horner's scheme (SymPy dmp_eval). */
export function dmpEval(f: DensePoly, a: unknown, u: number, K: Domain): unknown {
  const v = integer(u);
  if (!v) return dupEval(f, a, K);
  if (groundIsZero(a)) return polyTC(f, K);
  let result = list(polyLC(f, K));
  for (const coeff of f.slice(1)) result = dmpAdd(dmpMulGround(result, a, v - 1, K), list(coeff), v - 1, K);
  return result;
}

/** Evaluate f at x_j = a (SymPy dmp_eval_in). */
export function dmpEvalIn(f: DensePoly, a: unknown, j: number, u: number, K: Domain): unknown {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return recIn(f, uu, 0, jj, (h, w) => dmpEval(h, a, w, K), 1);
}

function recEvalTail(g: DensePoly, i: number, A: readonly unknown[], u: number, K: Domain): unknown {
  if (i === u) return dupEval(g, at(A, A.length - 1), K);
  const h = g.map((c) => recEvalTail(list(c), i + 1, A, u, K));
  return i < u - A.length + 1 ? h : dupEval(h, at(A, A.length - u + i - 1), K);
}

/** Evaluate f at x_k = a_k for the last variables x_k (SymPy dmp_eval_tail). */
export function dmpEvalTail(f: DensePoly, A: readonly unknown[], u: number, K: Domain): unknown {
  const v = integer(u);
  if (!A.length) return [...f];
  if (dmpZeroP(f, v)) return dmpZero(v - A.length);
  const e = recEvalTail(f, 0, A, v, K);
  return v === A.length - 1 ? e : dmpStrip(list(e), v - A.length);
}

/** Differentiate m times in x_j and evaluate at x_j = a (SymPy dmp_diff_eval_in). */
export function dmpDiffEvalIn(f: DensePoly, m: number, a: unknown, j: number, u: number, K: Domain): unknown {
  const [jj, uu] = [integer(j), integer(u)];
  if (jj > uu) throw new RangeError(`-${uu} <= j < ${uu} expected, got ${jj}`);
  if (!jj) return dmpEval(dmpDiff(f, m, uu, K), a, uu, K);
  return recIn(f, uu, 0, jj, (h, w) => dmpEval(dmpDiff(h, m, w, K), a, w, K), 1);
}

/** Reduce the coefficients of f modulo p, symmetrically over ZZ (SymPy dup_trunc). */
export function dupTrunc(f: DensePoly, p: unknown, K: Domain): unknown[] {
  if (K instanceof IntegerRing) {
    const q = K.convert(p);
    return dupStrip(f.map((c) => {
      const r = K.rem(c, q);
      return r > q / 2n ? r - q : r;
    }));
  }
  if (K instanceof FiniteField) {
    const q = K.convert(p).val;
    return dupStrip(f.map((c) => K.convert(K.convert(c).val % q)));
  }
  return dupStrip(f.map((c) => K.rem(c, p)));
}

/** Reduce f modulo a polynomial p in K[Y] (SymPy dmp_trunc). */
export function dmpTrunc(f: DensePoly, p: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  return dmpStrip(f.map((c) => dmpRem(list(c), p, v - 1, K)), v);
}

/** Reduce the ground coefficients of f modulo p (SymPy dmp_ground_trunc). */
export function dmpGroundTrunc(f: DensePoly, p: unknown, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupTrunc(f, p, K);
  return dmpStrip(f.map((c) => dmpGroundTrunc(list(c), p, v - 1, K)), v);
}

/** Divide all coefficients by the leading coefficient (SymPy dup_monic). */
export function dupMonic(f: DensePoly, K: Domain): unknown[] {
  if (!f.length) return [...f];
  const lc = polyLC(f, K);
  return K.isOne(lc) ? [...f] : dupExquoGround(f, lc, K);
}

/** Divide all coefficients by the ground leading coefficient (SymPy dmp_ground_monic). */
export function dmpGroundMonic(f: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupMonic(f, K);
  if (dmpZeroP(f, v)) return [...f];
  const lc = dmpGroundLC(f, v, K);
  return K.isOne(lc) ? [...f] : dmpExquoGround(f, lc, v, K);
}

/** The GCD of the coefficients of f (SymPy dup_content). */
export function dupContent(f: DensePoly, K: Domain): unknown {
  return groundContent(f, 0, K);
}

function groundContent(f: DensePoly, u: number, K: Domain): unknown {
  if (dmpZeroP(f, u)) return K.zero;
  let cont: unknown = K.zero;
  for (const c of f) {
    cont = K.gcd(cont, u ? groundContent(list(c), u - 1, K) : c);
    if (K !== QQ && K.isOne(cont)) break;
  }
  return cont;
}

/** The GCD of the ground coefficients of f (SymPy dmp_ground_content). */
export function dmpGroundContent(f: DensePoly, u: number, K: Domain): unknown {
  return groundContent(f, integer(u), K);
}

/** The content and the primitive part of f (SymPy dup_primitive). */
export function dupPrimitive(f: DensePoly, K: Domain): [unknown, unknown[]] {
  return dmpGroundPrimitive(f, 0, K);
}

/** The content and the primitive part of f in K[X] (SymPy dmp_ground_primitive). */
export function dmpGroundPrimitive(f: DensePoly, u: number, K: Domain): [unknown, unknown[]] {
  const v = integer(u);
  if (dmpZeroP(f, v)) return [K.zero, [...f]];
  const cont = groundContent(f, v, K);
  return K.isOne(cont) ? [cont, [...f]] : [cont, dmpQuoGround(f, cont, v, K)];
}

/** Extract the common content of f and g (SymPy dup_extract). */
export function dupExtract(f: DensePoly, g: DensePoly, K: Domain): [unknown, unknown[], unknown[]] {
  return dmpGroundExtract(f, g, 0, K);
}

/** Extract the common ground content of f and g (SymPy dmp_ground_extract). */
export function dmpGroundExtract(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown, unknown[], unknown[]] {
  const v = integer(u);
  const gcd = K.gcd(groundContent(f, v, K), groundContent(g, v, K));
  if (K.isOne(gcd)) return [gcd, [...f], [...g]];
  return [gcd, dmpQuoGround(f, gcd, v, K), dmpQuoGround(g, gcd, v, K)];
}

/** The real and imaginary parts of f(x + I*y) as polynomials in x and y (SymPy dup_real_imag). */
export function dupRealImag(f: DensePoly, K: Domain): [unknown[], unknown[]] {
  if (!(K instanceof IntegerRing || K instanceof RationalField)) throw new DomainError(`computing real and imaginary parts is not supported over ${K.toString()}`);
  let [f1, f2] = [dmpZero(1), dmpZero(1)];
  if (!f.length) return [f1, f2];
  const g = [[[K.one, K.zero]], [[K.one], []]];
  let h = list(dmpGround(first(f), 2));
  for (const c of f.slice(1)) h = dmpAddTerm(dmpMul(h, g, 2, K), dmpGround(c, 1), 0, 2, K);
  const n = h.length - 1;
  h.forEach((c, i) => {
    const part = list(c);
    const k = (n - i) % 4;
    if (k === 0) f1 = dmpAdd(f1, part, 1, K);
    else if (k === 1) f2 = dmpAdd(f2, part, 1, K);
    else if (k === 2) f1 = dmpSub(f1, part, 1, K);
    else f2 = dmpSub(f2, part, 1, K);
  });
  return [f1, f2];
}

/** f(-x) (SymPy dup_mirror). */
export function dupMirror(f: DensePoly, K: Domain): unknown[] {
  const g = [...f];
  for (let i = g.length - 2; i >= 0; i -= 2) g[i] = domainNeg(K, g[i]);
  return g;
}

/** f(a*x) (SymPy dup_scale). */
export function dupScale(f: DensePoly, a: unknown, K: Domain): unknown[] {
  const g = [...f];
  let b = a;
  for (let i = g.length - 2; i >= 0; i--) {
    g[i] = domainArith(K, 'mul', b, g[i]);
    b = domainArith(K, 'mul', b, a);
  }
  return g;
}

/** f(x + a) (SymPy dup_shift). */
export function dupShift(f: DensePoly, a: unknown, K: Domain): unknown[] {
  const g = [...f];
  for (let i = g.length - 1; i > 0; i--) {
    for (let j = 0; j < i; j++) g[j + 1] = domainArith(K, 'add', g[j + 1], domainArith(K, 'mul', a, g[j]));
  }
  return g;
}

/** f(X + A) (SymPy dmp_shift). */
export function dmpShift(f: DensePoly, a: readonly unknown[], u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupShift(f, first(a), K);
  if (dmpZeroP(f, v)) return [...f];
  const [a0, a1] = [first(a), a.slice(1)];
  const g = a1.some((c) => !groundIsZero(c)) ? f.map((c) => dmpShift(list(c), a1, v - 1, K)) : [...f];
  if (!groundIsZero(a0)) {
    for (let i = g.length - 1; i > 0; i--) {
      for (let j = 0; j < i; j++) g[j + 1] = dmpAdd(list(g[j + 1]), dmpMulGround(list(g[j]), a0, v - 1, K), v - 1, K);
    }
  }
  return dmpStrip(g, v);
}

/** q**n * f(p/q) for n = deg(f) (SymPy dup_transform). */
export function dupTransform(f: DensePoly, p: DensePoly, q: DensePoly, K: Domain): unknown[] {
  if (!f.length) return [];
  const Q: unknown[][] = [[K.one]];
  for (let i = 1; i < f.length; i++) Q.push(dupMul(at(Q, i - 1), q, K));
  let h: unknown[] = [first(f)];
  f.slice(1).forEach((c, i) => {
    h = dupAdd(dupMul(h, p, K), dupMulGround(at(Q, i + 1), c, K), K);
  });
  return h;
}

/** f(g) (SymPy dup_compose). */
export function dupCompose(f: DensePoly, g: DensePoly, K: Domain): unknown[] {
  if (g.length <= 1) return dupStrip([dupEval(f, polyLC(g, K), K)]);
  if (!f.length) return [];
  let h: unknown[] = [first(f)];
  for (const c of f.slice(1)) h = dupAddTerm(dupMul(h, g, K), c, 0, K);
  return h;
}

/** f(g) in K[X] (SymPy dmp_compose). */
export function dmpCompose(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupCompose(f, g, K);
  if (dmpZeroP(f, v)) return [...f];
  let h: unknown[] = [first(f)];
  for (const c of f.slice(1)) h = dmpAddTerm(dmpMul(h, g, v, K), c, 0, v, K);
  return h;
}

function rawDict(f: DensePoly): Map<number, unknown> {
  const n = f.length - 1;
  return new Map(f.flatMap((c, k) => groundIsZero(c) ? [] : [[n - k, c] as [number, unknown]]));
}

function rightDecompose(fIn: DensePoly, s: number, K: Domain): unknown[] {
  const n = fIn.length - 1;
  const lc = polyLC(fIn, K);
  const f = rawDict(fIn);
  const g = new Map<number, unknown>([[s, K.one]]);
  const r = Math.floor(n / s);
  for (let i = 1; i < s; i++) {
    let coeff: unknown = K.zero;
    for (let j = 0; j < i; j++) {
      const [fc, gc] = [f.get(n + j - i), g.get(s - j)];
      if (fc === undefined || gc === undefined) continue;
      coeff = domainArith(K, 'add', coeff, mulInt(K, domainArith(K, 'mul', fc, gc), i - r * j));
    }
    g.set(s - i, groundQuo(coeff, mulInt(K, lc, i * r), K));
  }
  return dupFromRawDict(g, K);
}

function leftDecompose(fIn: DensePoly, h: DensePoly, K: Domain): unknown[] | undefined {
  const g = new Map<number, unknown>();
  let f = [...fIn];
  for (let i = 0; f.length; i++) {
    const [q, r] = dupDiv(f, h, K);
    if (dupDegree(r) > 0) return undefined;
    g.set(i, polyLC(r, K));
    f = q;
  }
  return dupFromRawDict(g, K);
}

function decomposeOnce(f: DensePoly, K: Domain): [unknown[], unknown[]] | undefined {
  const df = f.length - 1;
  for (let s = 2; s < df; s++) {
    if (df % s !== 0) continue;
    const h = rightDecompose(f, s, K);
    const g = leftDecompose(f, h, K);
    if (g !== undefined) return [g, h];
  }
  return undefined;
}

/** The functional decomposition f = f_1(f_2(...f_n)) of a univariate polynomial (SymPy dup_decompose). */
export function dupDecompose(fIn: DensePoly, K: Domain): unknown[][] {
  const F: unknown[][] = [];
  let f = [...fIn];
  for (let result = decomposeOnce(f, K); result !== undefined; result = decomposeOnce(f, K)) {
    [f] = result;
    F.unshift(result[1]);
  }
  return [f, ...F];
}

/** Convert an algebraic coefficient generator into the first polynomial variable (SymPy dmp_alg_inject). */
export function dmpAlgInject(f: DensePoly, u: number, K: Domain): [unknown[], number, Domain] {
  if (!(K instanceof AlgebraicField || K instanceof GaussianDomain)) throw new DomainError('computation can be done only in an algebraic domain');
  const v = integer(u);
  const terms = new Map<number[], unknown>();
  for (const [powers, c] of dmpToDict(f, v)) {
    if (K instanceof AlgebraicField) {
      const coefficients = K.convert(c).rep;
      coefficients.forEach((coefficient, i) => {
        if (!coefficient.isZero) terms.set([coefficients.length - i - 1, ...powers], coefficient);
      });
    } else {
      const coefficient = K.convert(c);
      if (!coefficient.re.isZero) terms.set([0, ...powers], K.dom.convert(coefficient.re));
      if (!coefficient.im.isZero) terms.set([1, ...powers], K.dom.convert(coefficient.im));
    }
  }
  return [dmpFromDict(terms, v + 1, K.dom), v + 1, K.dom];
}

/** The polynomial over K.dom whose roots include those of f over an algebraic field K (SymPy dmp_lift). */
export function dmpLift(f: DensePoly, u: number, K: Domain): unknown[] {
  const [F, v, K2] = dmpAlgInject(f, u, K);
  const mod = K instanceof AlgebraicField ? K.mod : [1n, 0n, 1n];
  const P = dmpInclude(mod, Array.from({ length: v }, (_, i) => i + 1), 0, K2);
  const variables = Array.from({ length: v + 1 }, (_, i) => new Dummy(`x${i}`));
  const expr = (g: DensePoly): Expr => add(...[...dmpToDict(g, v)].map(([m, c]) => mul(K2.toSympy(c), ...variables.map((x, i) => pow(x, at(m, i))))));
  const rest = variables.slice(1);
  const r = Poly.from(resultant(expr(F), expr(P), first(variables)), rest, { domain: K2.toString() });
  return dmpFromDict(new Map(r.terms().map(([m, c]) => [m, K2.convert(c)])), v - 1, K2);
}

/** The number of sign variations of the coefficients of f (SymPy dup_sign_variations). */
export function dupSignVariations(f: DensePoly, K: Domain): number {
  let isNegative: (a: unknown) => boolean;
  if (K instanceof IntegerRing || K instanceof RationalField || K instanceof RealField) isNegative = (a) => K.isNegative(a);
  else if (K instanceof AlgebraicField && K.ext.asExpr().isComparable) {
    isNegative = (a) => !groundIsZero(a) && isNegativeExpr(K.toSympy(a)) === true;
  } else throw new DomainError(`sign variation counting not supported over ${K.toString()}`);
  let [prev, k]: [unknown, number] = [K.zero, 0];
  for (const coeff of f) {
    if (isNegative(domainArith(K, 'mul', coeff, prev))) k++;
    if (!groundIsZero(coeff)) prev = coeff;
  }
  return k;
}

/** Whether the elements of K have denominators other than one (SymPy K.denom). */
function fractional(K: Domain): boolean {
  return K instanceof RationalField || K instanceof GaussianRationalField || K instanceof ExpressionDomain || K instanceof FractionField;
}

function denominator(c: unknown, K: Domain): unknown {
  if (K instanceof RationalField) return K.convert(c).denominator;
  if (K instanceof GaussianRationalField) return K.denom(c);
  return K.convert(asNumerDenom(K.toSympy(c))[1]);
}

function numerator(c: unknown, K: Domain): unknown {
  if (K instanceof RationalField) return K.convert(c).numerator;
  if (K instanceof GaussianRationalField) return K.numer(c);
  return K.convert(asNumerDenom(K.toSympy(c))[0]);
}

function groundLcm(a: unknown, b: unknown, K: Domain): unknown {
  if (K instanceof ExpressionDomain || K instanceof PolynomialRing) return K.convert(lcmList([K.toSympy(a), K.toSympy(b)]));
  return K.lcm(a, b);
}

function commonDenominator(g: DensePoly, v: number, K0: Domain, K1: Domain): unknown {
  let common = K1.convert(K1.one);
  if (!fractional(K0)) return common;
  for (const c of g) common = groundLcm(common, v ? commonDenominator(list(c), v - 1, K0, K1) : K1.convert(denominator(c, K0)), K1);
  return common;
}

/** Clear the denominators: [common, common*f] (SymPy dup_clear_denoms). */
export function dupClearDenoms(f: DensePoly, K0: Domain, K1?: Domain, convert = false): [unknown, unknown[]] {
  const R = K1 ?? K0.getRing();
  const common = commonDenominator(f, 0, K0, R);
  if (groundEquals(common, 1n)) return [common, convert ? dupConvert(f, K0, R) : [...f]];
  const g = f.map((c) => domainArith(R, 'mul', R.convert(numerator(c, K0)), groundQuo(common, R.convert(denominator(c, K0)), R)));
  return [common, convert ? g : dupConvert(g, R, K0)];
}

/** Clear the denominators: [common, common*f] in K[X] (SymPy dmp_clear_denoms). */
export function dmpClearDenoms(f: DensePoly, u: number, K0: Domain, K1?: Domain, convert = false): [unknown, unknown[]] {
  const v = integer(u);
  if (!v) return dupClearDenoms(f, K0, K1, convert);
  const R = K1 ?? K0.getRing();
  const common = commonDenominator(f, v, K0, R);
  const g = groundEquals(common, 1n) ? [...f] : dmpMulGround(f, common, v, K0);
  return [common, convert ? dmpConvert(g, v, K0, R) : g];
}

/** The inverse g of f modulo x**n by Newton iteration: f*g = 1 mod x**n (SymPy dup_revert). */
export function dupRevert(f: DensePoly, n: number, K: Domain): unknown[] {
  const c = polyTC(f, K);
  if (groundIsZero(c) || !(K.isField || K.isOne(c) || K.isOne(domainNeg(K, c)))) throw new NotReversible('only units are reversible in a ring');
  let g: unknown[] = [domainArith(K, 'quo', K.one, c)];
  let h: unknown[] = [K.one, K.zero, K.zero];
  const N = Math.ceil(Math.log2(integer(n)));
  for (let i = 1; i <= N; i++) {
    const a = dupMulGround(g, 2n, K);
    const b = dupMul(f, dupSqr(g, K), K);
    g = dupRem(dupSub(a, b, K), h, K);
    h = dupLshift(h, dupDegree(h), K);
  }
  return g;
}

/** The inverse of f modulo x**n for a univariate f (SymPy dmp_revert). */
export function dmpRevert(f: DensePoly, g: number, u: number, K: Domain): unknown[] {
  if (!integer(u)) return dupRevert(f, g, K);
  throw new MultivariatePolynomialError(`${String(f)}, ${String(g)}`);
}

