// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real and complex root isolation (port of SymPy polys/rootisolation.py):
 * real roots by continued fractions (dup_isolate_real_roots, dup_refine_real_root,
 * dup_isolate_real_roots_list) and complex roots by the Collins-Krandick
 * bisection with winding numbers (dup_count_complex_roots,
 * dup_isolate_complex_roots_sqf, ComplexInterval).
 *
 * Polynomials are dense arrays, highest degree first (SymPy's dup): bigint
 * arrays over ZZ, Rational arrays over QQ.
 */

import { at, defined, first, getOrThrow, last } from '../core/guard';
import { Rational } from '../core/nodes';
import { UPoly } from './poly';
import { RefinementFailed } from './polyerrors';

type P = bigint[];
type M = [bigint, bigint, bigint, bigint];
type Q = Rational;
/** A dense polynomial over QQ, highest degree first. */
type QP = Q[];

const R = (p: bigint, q: bigint = 1n): Q => Rational.of(p, q);
const QZERO = R(0n);
const qadd = (a: Q, b: Q): Q => R(a.p * b.q + b.p * a.q, a.q * b.q);
const qsub = (a: Q, b: Q): Q => R(a.p * b.q - b.p * a.q, a.q * b.q);
const qmul = (a: Q, b: Q): Q => R(a.p * b.p, a.q * b.q);
const qdiv = (a: Q, b: Q): Q => R(a.p * b.q, a.q * b.p);
const qneg = (a: Q): Q => R(-a.p, a.q);
const qabs = (a: Q): Q => (a.p < 0n ? qneg(a) : a);
const qhalf = (a: Q): Q => R(a.p, 2n * a.q);
const cmp = (x: Q, y: Q): number => {
  const v = x.p * y.q - y.p * x.q;
  return v < 0n ? -1 : v > 0n ? 1 : 0;
};
const qeq = (x: Q, y: Q): boolean => x.p === y.p && x.q === y.q;
const qlt = (x: Q, y: Q): boolean => cmp(x, y) < 0;
const qle = (x: Q, y: Q): boolean => cmp(x, y) <= 0;

function strip(f: P): P {
  let i = 0;
  while (i < f.length && f[i] === 0n) i++;
  return f.slice(i);
}
const degree = (f: P) => strip(f).length - 1;
const LC = (f: P) => first(strip(f));
const TC = (f: P) => last(f);

/** floor(log2(a)) for a > 0. */
const ilog2 = (a: bigint) => a.toString(2).length - 1;

/** f(x + a) (Taylor shift, SymPy dup_shift). */
function shift(f0: P, a: bigint): P {
  const f = [...f0];
  const n = f.length - 1;
  for (let i = n; i > 0; i--) {
    // f[j + 1] += a * f[j], with f[j] already updated in this pass
    let prev = at(f, 0);
    for (let j = 1; j <= i; j++) {
      prev = at(f, j) + a * prev;
      f[j] = prev;
    }
  }
  return f;
}
/** f(a*x) (SymPy dup_scale). */
function scale(f: P, a: bigint): P {
  const n = f.length - 1;
  return f.map((c, i) => c * a ** BigInt(n - i));
}
const reverse = (f: P): P => strip([...f].reverse());
/** f(-x). */
const mirror = (f: P): P => {
  const n = f.length - 1;
  return f.map((c, i) => ((n - i) % 2 === 1 ? -c : c));
};
/** f/x**k for f divisible by x**k. */
const rshift = (f: P, k: number): P => f.slice(0, f.length - k);

function signVariations(f: P): number {
  let prev = 0n;
  let k = 0;
  for (const c of f) {
    if (c === 0n) continue;
    if (prev !== 0n && (c < 0n) !== (prev < 0n)) k++;
    prev = c;
  }
  return k;
}

/** SymPy dup_terms_gcd: [j, f/x**j] with x**j the largest power dividing f. */
function termsGcd(f: P): [number, P] {
  if (f.length === 0 || TC(f) !== 0n) return [0, f];
  let j = 0;
  while (at(f, f.length - 1 - j) === 0n) j++;
  return [j, f.slice(0, f.length - j)];
}

/**
 * SymPy dup_root_upper_bound (Kioustelidis/Akritas): a power of two. f has a
 * sign variation (it is only used for polynomials with a positive root), so
 * after making the leading coefficient positive some coefficient is negative,
 * and a positive one (the leading coefficient) follows it: SymPy's empty
 * cases (no candidate, no bound) do not occur.
 */
function rootUpperBound(f0: P): Q {
  let f = f0;
  const n = f.length;
  const t: number[] = Array(n).fill(1);
  if (LC(f) < 0n) f = f.map((c) => -c);
  f = [...f].reverse();
  const P: number[] = [];
  for (let i = 0; i < n; i++) {
    const fi = at(f, i);
    if (fi >= 0n) continue;
    const a = ilog2(-fi);
    const QL: [number, number][] = [];
    for (let j = i + 1; j < n; j++) {
      const fj = at(f, j);
      if (fj <= 0n) continue;
      const q = at(t, j) + a - ilog2(fj);
      QL.push([Math.floor(q / (j - i)), j]);
    }
    const q = QL.reduce((m, v) => (v[0] < m[0] || (v[0] === m[0] && v[1] < m[1]) ? v : m));
    t[q[1]] = at(t, q[1]) + 1;
    P.push(q[0]);
  }
  const e = Math.max(...P) + 1;
  return e >= 0 ? R(2n ** BigInt(e)) : R(1n, 2n ** BigInt(-e));
}

/** int(dup_root_lower_bound(f)): the integer part of 1/(upper bound of the reversed polynomial). */
function rootLowerBound(f: P): bigint {
  const b = rootUpperBound(reverse(f));
  return b.q / b.p;
}

/** SymPy _mobius_to_interval. */
const mobiusToInterval = ([a, b, c, d]: M): [Q, Q] => {
  const s = R(a, c);
  const t = R(b, d);
  return qle(s, t) ? [s, t] : [t, s];
};

/** One step of the continued fraction refinement (SymPy dup_step_refine_real_root). */
function stepRefine(f0: P, M0: M, fast: boolean): [P, M] {
  let [a, b, c, d] = M0;
  if (a === b && c === d) return [f0, M0];
  let f = f0;
  let A = rootLowerBound(f);
  if (fast && A > 16n) {
    f = scale(f, A);
    a *= A;
    c *= A;
    A = 1n;
  }
  // shift by A (when at least 1), then by 1: x -> x + n composed into the Mobius map; a root at the
  // shift point is exact (SymPy checks after each shift; one loop keeps both checks on one path)
  let g = f;
  for (const n of A >= 1n ? [A, 1n] : [1n]) {
    if (n === 1n) g = f;
    f = shift(f, n);
    [b, d] = [n * a + b, n * c + d];
    if (TC(f) === 0n) return [f, [b, b, d, d]];
  }
  // b, d are shifted by 1 here; g and b - a, d - c are before the shift by 1
  [b, d] = [b - a, d - c];
  const [a1, b1, c1, d1] = [a, a + b, c, c + d];
  if (signVariations(f) === 1) return [f, [a1, b1, c1, d1]];
  // the root is in (0, 1) of g: x -> 1/(x + 1). g(1) != 0, so the shifted reverse has no root at 0
  return [shift(reverse(g), 1n), [b, a + b, d, c + d]];
}

interface RefineOptions {
  eps?: Q | undefined;
  steps?: number | undefined;
  disjoint?: Q | undefined;
  fast?: boolean | undefined;
}

const mobiusWidth = ([a, b, c, d]: M): Q => qabs(qsub(R(a, c), R(b, d)));

/** SymPy dup_inner_refine_real_root (mobius=True). */
function innerRefine(f0: P, M0: M, { eps, steps, disjoint, fast = false }: RefineOptions): [P, M] {
  let f = f0;
  let m = M0;
  while (m[2] === 0n) [f, m] = stepRefine(f, m, fast);
  if (eps !== undefined && steps !== undefined) {
    for (let i = 0; i < steps && !qlt(mobiusWidth(m), eps); i++) [f, m] = stepRefine(f, m, fast);
  } else {
    if (eps !== undefined) while (!qlt(mobiusWidth(m), eps)) [f, m] = stepRefine(f, m, fast);
    if (steps !== undefined) for (let i = 0; i < steps; i++) [f, m] = stepRefine(f, m, fast);
  }
  if (disjoint !== undefined) {
    for (;;) {
      const [u, v] = mobiusToInterval(m);
      if (qle(v, disjoint) || qle(disjoint, u)) break;
      [f, m] = stepRefine(f, m, fast);
    }
  }
  return [f, m];
}

/** (c*x + d)**n * f((a*x + b)/(c*x + d)) (SymPy dup_transform with p = a*x + b, q = c*x + d). */
function transform(f: P, [a, b, c, d]: M): P {
  const n = f.length - 1;
  const mulP = (x: P, y: P): P => {
    const r: bigint[] = Array(x.length + y.length - 1).fill(0n);
    x.forEach((xi, i) => {
      let k = i;
      for (const yj of y) {
        r[k] = at(r, k) + xi * yj;
        k++;
      }
    });
    return r;
  };
  const addP = (x: P, y: P): P => {
    const L = Math.max(x.length, y.length);
    const xx = Array(L - x.length).fill(0n).concat(x);
    const yy = Array(L - y.length).fill(0n).concat(y);
    return xx.map((v, i) => v + at(yy, i));
  };
  const p: P = [a, b];
  const q: P = [c, d];
  let res: P = [0n];
  for (const [i, fi] of f.entries()) {
    // coefficient f[i] of x**(n - i): p**(n - i) * q**i
    let term: P = [fi];
    for (let k = 0; k < n - i; k++) term = mulP(term, p);
    for (let k = 0; k < i; k++) term = mulP(term, q);
    res = addP(res, term);
  }
  return strip(res);
}

/** SymPy dup_outer_refine_real_root for 0 <= s < t. */
function outerRefine(f0: P, s: Q, t: Q, opts: RefineOptions): [Q, Q] {
  const m: M = [s.p, t.p, s.q, t.q];
  const f = transform(f0, m);
  if (signVariations(f) !== 1) throw new RefinementFailed(`there should be exactly one root in (${s.toString()}, ${t.toString()}) interval`);
  return mobiusToInterval(innerRefine(f, m, opts)[1]);
}

/** Refine an isolating interval (s, t) of a root of f (SymPy dup_refine_real_root over ZZ). */
export function refineRealRoot(f0: P, s0: Q, t0: Q, opts: RefineOptions = {}): [Q, Q] {
  let f = f0;
  let [s, t] = qle(s0, t0) ? [s0, t0] : [t0, s0];
  if (qeq(s, t)) return [s, t];
  let negative = false;
  let disjoint = opts.disjoint;
  if (s.p < 0n) {
    if (t.p <= 0n) {
      f = mirror(f);
      [s, t] = [qneg(t), qneg(s)];
      negative = true;
    } else throw new RangeError(`Cannot refine a real root in (${s.toString()}, ${t.toString()})`);
  }
  // SymPy drops a nonnegative disjoint point for a negative interval; the bisection only gives points inside the interval
  if (negative && disjoint !== undefined) disjoint = qneg(disjoint);
  const [u, v] = outerRefine(f, s, t, { ...opts, disjoint });
  return negative ? [qneg(v), qneg(u)] : [u, v];
}

/**
 * f(x + n) with b, d of the Mobius map shifted; a root at the shift point is recorded as exact and
 * divided out (one helper for SymPy's two shifts of dup_inner_isolate_real_roots).
 */
function shiftOut(f0: P, n: bigint, [a, b0, c, d0]: M, roots: [P, M][]): [P, bigint, bigint] {
  const f = shift(f0, n);
  const [b, d] = [n * a + b0, n * c + d0];
  if (TC(f) !== 0n) return [f, b, d];
  roots.push([f, [b, b, d, d]]);
  return [rshift(f, 1), b, d];
}

/** Positive roots of f as [transformed polynomial, Mobius map] (SymPy dup_inner_isolate_real_roots). */
function innerIsolate(f0: P, eps: Q | undefined, fast: boolean): [P, M][] {
  const k0 = signVariations(f0);
  if (k0 === 0) return [];
  if (k0 === 1) return [innerRefine(f0, [1n, 0n, 0n, 1n], { eps, fast })];
  const roots: [P, M][] = [];
  const stack: [bigint, bigint, bigint, bigint, P, number][] = [[1n, 0n, 0n, 1n, f0, k0]];
  for (let top = stack.pop(); top !== undefined; top = stack.pop()) {
    let [a, b, c, d, f, k] = top;
    let A = rootLowerBound(f);
    if (fast && A > 16n) {
      f = scale(f, A);
      a *= A;
      c *= A;
      A = 1n;
    }
    if (A >= 1n) {
      [f, b, d] = shiftOut(f, A, [a, b, c, d], roots);
      k = signVariations(f);
      if (k === 0) continue;
      if (k === 1) {
        roots.push(innerRefine(f, [a, b, c, d], { eps, fast }));
        continue;
      }
    }
    const n = roots.length;
    let [f1, b1, d1]: [P | undefined, bigint, bigint] = shiftOut(f, 1n, [a, b, c, d], roots);
    let [a1, c1] = [a, c];
    const r = roots.length - n;
    let k1 = signVariations(f1);
    let k2 = k - k1 - r;
    let [a2, b2, c2, d2] = [b, a + b, d, c + d];
    let f2: P | undefined;
    if (k2 > 1) {
      f2 = shift(reverse(f), 1n);
      if (TC(f2) === 0n) f2 = rshift(f2, 1);
      k2 = signVariations(f2);
    }
    if (k1 < k2) {
      [a1, a2, b1, b2] = [a2, a1, b2, b1];
      [c1, c2, d1, d2] = [c2, c1, d2, d1];
      [f1, f2, k1, k2] = [f2, f1, k2, k1];
    }
    if (!k1) continue;
    // f1 is only missing when k = 2 with the root at 1 taken out (k1 = 0, k2 = 1): f(1) = 0, so
    // SymPy's division by x always happens
    f1 ??= rshift(shift(reverse(f), 1n), 1);
    if (k1 === 1) roots.push(innerRefine(f1, [a1, b1, c1, d1], { eps, fast }));
    else stack.push([a1, b1, c1, d1, f1, k1]);
    if (!k2) continue;
    if (f2 === undefined) {
      f2 = shift(reverse(f), 1n);
      if (TC(f2) === 0n) f2 = rshift(f2, 1);
    }
    if (k2 === 1) roots.push(innerRefine(f2, [a2, b2, c2, d2], { eps, fast }));
    else stack.push([a2, b2, c2, d2, f2, k2]);
  }
  return roots;
}

interface IsolateOptions {
  eps?: Q | undefined;
  inf?: Q | undefined;
  sup?: Q | undefined;
  fast?: boolean | undefined;
}

/** SymPy _discard_if_outside_interval (mobius=True): undefined when the root is outside [inf, sup]. */
function discardIfOutside(f0: P, M0: M, inf: Q | undefined, sup: Q | undefined, negative: boolean, fast: boolean): [P, M] | undefined {
  let [f, m] = [f0, M0];
  for (;;) {
    let [u, v] = mobiusToInterval(m);
    if (negative) [u, v] = [qneg(v), qneg(u)];
    if ((inf === undefined || qle(inf, u)) && (sup === undefined || qle(v, sup))) return [f, m];
    if ((sup !== undefined && qlt(sup, u)) || (inf !== undefined && qlt(v, inf))) return undefined;
    [f, m] = stepRefine(f, m, fast);
  }
}

/** SymPy dup_inner_isolate_positive_roots / dup_inner_isolate_negative_roots (mobius=True). */
function innerIsolateSigned(f: P, negative: boolean, { eps, inf, sup, fast = false }: IsolateOptions): [P, M][] {
  if (negative ? inf !== undefined && inf.p >= 0n : sup !== undefined && sup.p < 0n) return [];
  const roots = innerIsolate(negative ? mirror(f) : f, eps, fast);
  if (inf === undefined && sup === undefined) return roots;
  const out: [P, M][] = [];
  for (const [g, m] of roots) {
    const r = discardIfOutside(g, m, inf, sup, negative, fast);
    if (r !== undefined) out.push(r);
  }
  return out;
}

/** SymPy _disjoint_p. */
function disjointP(M1: M, N1: M, strict: boolean): boolean {
  let [a1, b1, c1, d1] = M1;
  let [a2, b2, c2, d2] = N1;
  const [a1d1, b1c1, a2d2, b2c2] = [a1 * d1, b1 * c1, a2 * d2, b2 * c2];
  if (a1d1 === b1c1 && a2d2 === b2c2) return true;
  if (a1d1 > b1c1) [a1, c1, b1, d1] = [b1, d1, a1, c1];
  if (a2d2 > b2c2) [a2, c2, b2, d2] = [b2, d2, a2, c2];
  return strict ? a2 * d1 > c2 * b1 || b2 * c1 < d2 * a1 : a2 * d1 >= c2 * b1 || b2 * c1 <= d2 * a1;
}

/** An isolating interval with its data (multiplicity or the indices of the polynomials it is a root of) and its factor. */
type Iso<K> = [[Q, Q], K, P];

/** SymPy _real_isolate_and_disjoin with basis=True: [negative roots, positive roots]. */
function realIsolateAndDisjoin<K>(factors: [P, K][], opts: IsolateOptions & { strict?: boolean }): [Iso<K>[], Iso<K>[]] {
  const fast = opts.fast ?? false;
  const strict = opts.strict ?? false;
  type E = [P, M, K, P];
  const pos: E[] = [];
  const neg: E[] = [];
  for (const [f, k] of factors) {
    for (const [g, m] of innerIsolateSigned(f, false, opts)) pos.push([g, m, k, f]);
    for (const [g, m] of innerIsolateSigned(f, true, opts)) neg.push([g, m, k, f]);
  }
  const step = (f: P, m: M) => innerRefine(f, m, { steps: 1, fast });
  for (const list of [pos, neg]) {
    for (let i = 0; i < list.length; i++) {
      let [f, m, k, F] = at(list, i);
      for (let j = i + 1; j < list.length; j++) {
        let [g, n, l, G] = at(list, j);
        while (!disjointP(m, n, strict)) {
          [f, m] = step(f, m);
          [g, n] = step(g, n);
        }
        list[j] = [g, n, l, G];
      }
      list[i] = [f, m, k, F];
    }
  }
  if (strict) {
    // refine the first interval touching 0 on each side until it does not
    for (const list of [neg, pos]) {
      const i = list.findIndex(([, m]) => m[0] === 0n);
      if (i < 0) continue;
      let [f, m, k, F] = at(list, i);
      while (m[0] === 0n) [f, m] = step(f, m);
      list[i] = [f, m, k, F];
    }
  }
  const negOut: Iso<K>[] = neg.map(([, m, k, f]) => {
    const [u, v] = mobiusToInterval(m);
    return [[qneg(v), qneg(u)], k, f];
  });
  const posOut: Iso<K>[] = pos.map(([, m, k, f]) => [mobiusToInterval(m), k, f]);
  return [negOut, posOut];
}

const sortIntervals = <T extends [[Q, Q], ...unknown[]]>(xs: T[]): T[] => xs.sort((x, y) => cmp(x[0][0], y[0][0]) || cmp(x[0][1], y[0][1]));

/** Is 0 in [inf, sup]? */
const zeroInside = (inf: Q | undefined, sup: Q | undefined) => (inf === undefined || inf.p <= 0n) && (sup === undefined || sup.p >= 0n);

/**
 * Isolating intervals of the real roots of an integer polynomial given by
 * its square-free factors [(f, multiplicity)] (SymPy dup_isolate_real_roots).
 * Returns [[s, t], multiplicity] sorted by the intervals.
 */
export function isolateRealRoots(factors: [P, number][], eps?: Q, opts: IsolateOptions = {}): [[Q, Q], number][] {
  let zeroMult = 0;
  const fs: [P, number][] = [];
  for (const [f0, k] of factors) {
    const [j, f] = termsGcd(strip(f0));
    zeroMult += j * k;
    if (degree(f) > 0) fs.push([f, k]);
  }
  const [neg, pos] = realIsolateAndDisjoin(fs, { ...opts, eps });
  const out: [[Q, Q], number][] = [...neg, ...pos].map(([iv, k]) => [iv, k]);
  if (zeroMult && zeroInside(opts.inf, opts.sup)) out.push([[QZERO, QZERO], zeroMult]);
  return sortIntervals(out);
}

/** Isolating intervals of the real roots of a square-free integer polynomial (SymPy dup_isolate_real_roots_sqf). */
export function isolateRealRootsSqf(f0: P, opts: IsolateOptions = {}): [Q, Q][] {
  return isolateRealRoots([[f0, 1]], opts.eps, opts).map(([iv]) => iv);
}

/** Clear the denominators of a polynomial over QQ (SymPy dup_clear_denoms with convert=True). */
function clearDenoms(f: QP): P {
  let common = 1n;
  for (const c of f) {
    let [a, b] = [common, c.q];
    while (b) [a, b] = [b, a % b];
    common = (common / a) * c.q;
  }
  return f.map((c) => c.p * (common / c.q));
}

/** Python list comparison of equally long, distinct integer lists (distinct factors). */
const cmpLists = (f: P, g: P): number => {
  const i = f.findIndex((c, j) => c !== at(g, j));
  return at(f, i) < at(g, i) ? -1 : 1;
};

/**
 * Irreducible factors over ZZ with multiplicities, primitive with positive
 * leading coefficients, in SymPy's dup_factor_list order (by length, then
 * multiplicity, then coefficients); the polynomial has no factor x.
 */
function factorListZZ(f: P): [P, number][] {
  const out: [P, number][] = [];
  for (const [g, k] of new UPoly([...f].reverse().map((c) => R(c))).factor().factors) {
    // a monic factor times the lcm of its denominators is primitive with a positive leading coefficient
    out.push([clearDenoms([...g.coeffs].reverse()), k]);
  }
  return out.sort((u, v) => u[0].length - v[0].length || u[1] - v[1] || cmpLists(u[0], v[0]));
}

/** Indices of the polynomials (of a list) a root belongs to, with multiplicities. */
type Indices = Map<number, number>;
/** An isolating interval of a root on an edge of a rectangle, with its factor over ZZ. */
type Edge = Iso<Indices>;

/**
 * Isolating intervals in [inf, sup] of the real roots of a list of
 * polynomials over QQ, with the indices of the polynomials each root belongs
 * to (SymPy dup_isolate_real_roots_list with basis=True).
 */
function isolateRealRootsList(polys: QP[], opts: IsolateOptions & { strict?: boolean }): Edge[] {
  const zeros = zeroInside(opts.inf, opts.sup);
  const zeroIndices: Indices = new Map();
  const factors = new Map<string, [P, Indices]>();
  polys.forEach((p0, i) => {
    const [j, p] = termsGcd(clearDenoms(p0));
    if (zeros && j > 0) zeroIndices.set(i, j);
    for (const [f, k] of factorListZZ(p)) {
      const key = f.join(',');
      const e = factors.get(key) ?? [f, new Map<number, number>()];
      e[1].set(i, k);
      factors.set(key, e);
    }
  });
  const [neg, pos] = realIsolateAndDisjoin([...factors.values()], opts);
  const zero: Edge[] = zeroIndices.size ? [[[QZERO, QZERO], zeroIndices, [1n, 0n]]] : [];
  return sortIntervals([...neg, ...zero, ...pos]);
}

// ---------------------------------------------------------------------------
// Complex roots: Collins-Krandick

/** A polynomial in x and y over QQ: c[i][j] is the coefficient of x**i*y**j. */
type Biv = Q[][];

/** f(x + I*y) = f1(x, y) + I*f2(x, y) (SymPy dup_real_imag). */
function realImag(f: QP): [Biv, Biv] {
  const n = f.length - 1;
  const zero = (): Biv => Array.from({ length: n + 1 }, () => Array.from({ length: n + 1 }, () => QZERO));
  const [f1, f2] = [zero(), zero()];
  f.forEach((a, i) => {
    const m = n - i;
    let binom = 1n;
    for (let k = 0; k <= m; k++) {
      // C(m, k) a x**(m - k) (I y)**k
      const c = qmul(a, R(binom));
      const row = at(k % 2 === 0 ? f1 : f2, m - k);
      row[k] = k % 4 < 2 ? qadd(at(row, k), c) : qsub(at(row, k), c);
      binom = (binom * BigInt(m - k)) / BigInt(k + 1);
    }
  });
  return [f1, f2];
}

const stripQ = (f: QP): QP => {
  let i = 0;
  while (i < f.length && at(f, i).isZero) i++;
  return f.slice(i);
};
/** f(a) by Horner (SymPy dup_eval). */
const evalQ = (f: QP, a: Q): Q => f.reduce((acc, c) => qadd(qmul(acc, a), c), QZERO);
/** f(x, y) at y = v, a polynomial in x (SymPy dmp_eval_in(f, v, 1, 1)). */
const atY = (f: Biv, v: Q): QP => stripQ(f.map((row) => evalQ([...row].reverse(), v)).reverse());
/** f(x, y) at x = s, a polynomial in y (SymPy dmp_eval_in(f, s, 0, 1)). */
const atX = (f: Biv, s: Q): QP => stripQ(first(f).map((_, j) => evalQ(f.map((row) => at(row, j)).reverse(), s)).reverse());

const OO = 'OO';
const [Q1, Q2, Q3, Q4] = ['Q1', 'Q2', 'Q3', 'Q4'];
const [A1, A2, A3, A4] = ['A1', 'A2', 'A3', 'A4'];

const rulesFrom = (spec: [string, number][]) => new Map(spec);
const RULES_SIMPLE = rulesFrom([
  ['Q1 Q1', 0], ['Q2 Q2', 0], ['Q3 Q3', 0], ['Q4 Q4', 0],
  ['A1 Q1', 1], ['A2 Q2', 1], ['A3 Q3', 1], ['A4 Q4', 1],
  ['A1 Q4', 2], ['A2 Q1', 2], ['A3 Q2', 2], ['A4 Q3', 2],
  ['Q1 A2', 3], ['Q2 A3', 3], ['Q3 A4', 3], ['Q4 A1', 3],
  ['Q1 A1', 4], ['Q2 A2', 4], ['Q3 A3', 4], ['Q4 A4', 4],
  ['Q1 Q2', 5], ['Q2 Q3', 5], ['Q3 Q4', 5], ['Q4 Q1', 5],
  ['Q1 Q4', -5], ['Q2 Q1', -5], ['Q3 Q2', -5], ['Q4 Q3', -5],
]);
/** The rotations [q1, q2] and [q1, OO, q2] with the same rule. */
const both = (spec: [string, number][]): [string, number][] => spec.flatMap(([k, v]): [string, number][] => {
  const [a, b] = k.split(' ');
  return [[k, v], [`${a} OO ${b}`, v]];
});
const RULES_AMBIGUOUS = rulesFrom([
  ['A1 OO Q1', -1], ['A2 OO Q2', -1], ['A3 OO Q3', -1], ['A4 OO Q4', -1],
  ['A1 OO Q4', -2], ['A2 OO Q1', -2], ['A3 OO Q2', -2], ['A4 OO Q3', -2],
  ['Q1 OO A2', -3], ['Q2 OO A3', -3], ['Q3 OO A4', -3], ['Q4 OO A1', -3],
  ['Q1 OO A1', -4], ['Q2 OO A2', -4], ['Q3 OO A3', -4], ['Q4 OO A4', -4],
  ...both([
    ['A1 A3', 7], ['A2 A4', 7], ['A3 A1', 7], ['A4 A2', 7],
    ['Q1 Q3', 8], ['Q2 Q4', 8], ['Q3 Q1', 8], ['Q4 Q2', 8],
    ['A1 A2', 9], ['A2 A3', 9], ['A3 A4', 9], ['A4 A1', 9],
    ['A1 A4', 10], ['A2 A1', 10], ['A3 A2', 10], ['A4 A3', 10],
    ['Q1 A3', 11], ['Q2 A4', 11], ['Q3 A1', 11], ['Q4 A2', 11],
    ['Q1 A4', 12], ['Q2 A1', 12], ['Q3 A2', 12], ['Q4 A3', 12],
    ['A1 Q3', 13], ['A2 Q4', 13], ['A3 Q1', 13], ['A4 Q2', 13],
    ['A1 Q2', 14], ['A2 Q3', 14], ['A3 Q4', 14], ['A4 Q1', 14],
  ]),
  ['Q1 OO Q2', 15], ['Q2 OO Q3', 15], ['Q3 OO Q4', 15], ['Q4 OO Q1', 15],
  ['Q1 OO Q4', 16], ['Q2 OO Q1', 16], ['Q3 OO Q2', 16], ['Q4 OO Q3', 16],
  ['A1 OO A1', 17], ['A2 OO A2', 17], ['A3 OO A3', 17], ['A4 OO A4', 17],
  ['Q1 OO Q1', 18], ['Q2 OO Q2', 18], ['Q3 OO Q3', 18], ['Q4 OO Q4', 18],
]);
/** The contributions of the rules to twice the winding number, without and with the correction. */
const VALUES = new Map<number, [number, number][]>([
  [0, [[0, 1]]], [1, [[1, 4]]], [2, [[-1, 4]]], [3, [[1, 4]]], [4, [[-1, 4]]],
  [-1, [[9, 4], [1, 4]]], [-2, [[7, 4], [-1, 4]]], [-3, [[9, 4], [1, 4]]], [-4, [[7, 4], [-1, 4]]],
  [5, [[1, 2]]], [-5, [[-1, 2]]],
  [7, [[1, 1], [-1, 1]]], [8, [[1, 1], [-1, 1]]], [9, [[1, 2], [-3, 2]]], [10, [[3, 2], [-1, 2]]],
  [11, [[3, 4], [-5, 4]]], [12, [[5, 4], [-3, 4]]], [13, [[5, 4], [-3, 4]]], [14, [[3, 4], [-5, 4]]],
  [15, [[1, 2], [-3, 2]]], [16, [[3, 2], [-1, 2]]], [17, [[2, 1], [0, 1]]], [18, [[2, 1], [0, 1]]],
]);

/**
 * The half-axis (or origin) of a point on an axis (SymPy _classify_point).
 * It is only used at roots of f1 or f2, so SymPy's None off the axes does not occur.
 */
function classifyPoint(re: Q, im: Q): string {
  if (re.isZero && im.isZero) return OO;
  if (re.isZero) return im.isPositive ? A2 : A4;
  return re.isPositive ? A1 : A3;
}

/** The sequence of extended quadrants along an edge from s to t (SymPy _intervals_to_quadrants). */
function intervalsToQuadrants(intervals0: Edge[], f1: QP, f2: QP, s: Q, t: Q): string[] {
  let intervals = intervals0;
  if (!intervals.length) return [];
  const Q: string[] = [];
  // one of the parts vanishes on the edge: the other one changes sign at its roots
  const onAxis = (g: QP, idx: number, pos: string, neg: string): string[] => {
    const [[a, b]] = first(intervals);
    let sgn: number;
    if (qeq(a, b) && qeq(b, s)) {
      if (intervals.length === 1) return evalQ(g, t).isPositive ? [OO, pos] : [OO, neg];
      const [[a1]] = at(intervals, 1);
      sgn = evalQ(g, qhalf(qadd(s, a1))).isPositive ? 1 : -1;
      Q.push(OO, sgn > 0 ? pos : neg);
      intervals = intervals.slice(1);
    } else {
      sgn = evalQ(g, s).isPositive ? 1 : -1;
      Q.push(sgn > 0 ? pos : neg);
    }
    for (const [[a1], indices] of intervals) {
      Q.push(OO);
      if (getOrThrow(indices, idx) % 2 === 1) sgn = -sgn;
      if (!qeq(a1, t)) Q.push(sgn > 0 ? pos : neg);
    }
    return Q;
  };
  if (!f1.length) return onAxis(f2, 1, A2, A4);
  if (!f2.length) return onAxis(f1, 0, A1, A3);
  let re = evalQ(f1, s);
  let im = evalQ(f2, s);
  if (re.isZero || im.isZero) {
    Q.push(classifyPoint(re, im));
    const p = intervals.length === 1 ? t : qhalf(qadd(s, at(intervals, 1)[0][0]));
    re = evalQ(f1, p);
    im = evalQ(f2, p);
    intervals = intervals.slice(1);
  }
  let f1sgn = re.isPositive ? 1 : -1;
  let f2sgn = im.isPositive ? 1 : -1;
  const sgn = () => (f1sgn > 0 ? (f2sgn > 0 ? Q1 : Q4) : f2sgn > 0 ? Q2 : Q3);
  Q.push(sgn());
  for (const [[a, b], indices] of intervals) {
    if (qeq(a, b)) Q.push(classifyPoint(evalQ(f1, a), evalQ(f2, a)));
    if ((indices.get(0) ?? 0) % 2 === 1) f1sgn = -f1sgn;
    if ((indices.get(1) ?? 0) % 2 === 1) f2sgn = -f2sgn;
    if (!(qeq(a, b) && qeq(b, t))) Q.push(sgn());
  }
  return Q;
}

/** Rules of the traversal of the four edges (SymPy _traverse_quadrants; exclude is True or None). */
function traverseQuadrants(QQ: readonly string[][], exclude: boolean): [number, number][] {
  const edges = exclude ? [1, 1, 0, 0] : [0, 0, 0, 0];
  // the corner between edge j and edge i = j + 1
  const corners = exclude ? [1, 1, 0, 1] : [0, 0, 0, 0];
  const rules: [number, number][] = [];
  QQ.forEach((Q0, i) => {
    if (!Q0.length) return;
    let Q = last(Q0) === OO ? Q0.slice(0, -1) : Q0;
    if (first(Q) === OO) {
      const j = (i + 3) % 4;
      Q = Q.slice(1);
      const qq = [at(at(QQ, j), -2), OO, first(Q)];
      rules.push([getOrThrow(RULES_AMBIGUOUS, qq.join(' ')), at(corners, j)]);
    }
    let q1 = first(Q);
    let k = 1;
    while (k < Q.length) {
      const q2 = at(Q, k++);
      let qq: string[];
      if (q2 !== OO) {
        qq = [q1, q2];
        const simple = RULES_SIMPLE.get(qq.join(' '));
        rules.push(simple === undefined ? [getOrThrow(RULES_AMBIGUOUS, qq.join(' ')), at(edges, i)] : [simple, 0]);
      } else {
        qq = [q1, q2, at(Q, k++)];
        rules.push([getOrThrow(RULES_AMBIGUOUS, qq.join(' ')), at(edges, i)]);
      }
      q1 = last(qq);
    }
  });
  return rules;
}

const reverseIntervals = (intervals: Edge[]): Edge[] => [...intervals].reverse().map(([[a, b], indices, f]) => [[b, a], indices, f]);

/** The number of roots inside the traversed rectangle (SymPy _winding_number). */
function windingNumber(T: [number, number][]): number {
  let s = QZERO;
  for (const [t, i] of T) {
    const [p, q] = at(getOrThrow(VALUES, t), i);
    s = qadd(s, R(BigInt(p), BigInt(q)));
  }
  return Number(s.p / (2n * s.q));
}

type Four<T> = [T, T, T, T];
/** A rectangle of the bisection: number of roots, corners, edge intervals, quadrant sequences, edge polynomials. */
interface Rect {
  N: number;
  a: [Q, Q];
  b: [Q, Q];
  I: Four<Edge[]>;
  Q: Four<string[]>;
  F1: Four<QP>;
  F2: Four<QP>;
}

const edgeOpts = (inf: Q, sup: Q) => ({ inf, sup, fast: true, strict: true });

/** Split the intervals of an edge crossed by the bisecting line at c into its two parts. */
function splitEdge(I: Edge[], c: Q, reversed: boolean): [Edge[], Edge[]] {
  const lo: Edge[] = [];
  const hi: Edge[] = [];
  for (const iv of I) {
    const [[s, t], indices, h] = iv;
    let [a, b] = reversed ? [t, s] : [s, t];
    if (qeq(a, b)) {
      if (qeq(a, c)) {
        lo.push(iv);
        hi.push(iv);
      } else (qlt(a, c) ? lo : hi).push(iv);
    } else if (qle(b, c)) lo.push(iv);
    else if (qle(c, a)) hi.push(iv);
    else {
      [a, b] = refineRealRoot(h, a, b, { disjoint: c, fast: true });
      const e: Edge = [reversed ? [b, a] : [a, b], indices, h];
      if (qle(b, c)) lo.push(e);
      if (qle(c, a)) hi.push(e);
    }
  }
  return [lo, hi];
}

function rect(N: number, a: [Q, Q], b: [Q, Q], I: Four<Edge[]>, Q: Four<string[]>, F1: Four<QP>, F2: Four<QP>): Rect {
  return { N, a, b, I, Q, F1, F2 };
}

/** Vertical bisection step (SymPy _vertical_bisection). */
function verticalBisection({ a: [u, v], b: [s, t], I, Q, F1, F2 }: Rect, f1: Biv, f2: Biv): [Rect, Rect] {
  const [IL1, IL2, IL3, IL4] = I;
  const [, QL2, , QL4] = Q;
  const [f1L1, f1L2, f1L3, f1L4] = F1;
  const [f2L1, f2L2, f2L3, f2L4] = F2;
  const x = qhalf(qadd(u, s));
  const f1V = atX(f1, x);
  const f2V = atX(f2, x);
  const IV = isolateRealRootsList([f1V, f2V], edgeOpts(v, t));
  const [IL1L, IL1R] = splitEdge(IL1, x, false);
  const [IL3L, IL3R] = splitEdge(IL3, x, true);
  const IL: Four<Edge[]> = [IL1L, IV, IL3L, IL4];
  const IR: Four<Edge[]> = [IL1R, IL2, IL3R, reverseIntervals(IV)];
  const QL: Four<string[]> = [
    intervalsToQuadrants(IL1L, f1L1, f2L1, u, x),
    intervalsToQuadrants(IV, f1V, f2V, v, t),
    intervalsToQuadrants(IL3L, f1L3, f2L3, x, u),
    QL4,
  ];
  const QR: Four<string[]> = [
    intervalsToQuadrants(IL1R, f1L1, f2L1, x, s),
    QL2,
    intervalsToQuadrants(IL3R, f1L3, f2L3, s, x),
    intervalsToQuadrants(at(IR, 3), f1V, f2V, t, v),
  ];
  return [
    rect(windingNumber(traverseQuadrants(QL, true)), [u, v], [x, t], IL, QL, [f1L1, f1V, f1L3, f1L4], [f2L1, f2V, f2L3, f2L4]),
    rect(windingNumber(traverseQuadrants(QR, true)), [x, v], [s, t], IR, QR, [f1L1, f1L2, f1L3, f1V], [f2L1, f2L2, f2L3, f2V]),
  ];
}

/** Horizontal bisection step (SymPy _horizontal_bisection). */
function horizontalBisection({ a: [u, v], b: [s, t], I, Q, F1, F2 }: Rect, f1: Biv, f2: Biv): [Rect, Rect] {
  const [IL1, IL2, IL3, IL4] = I;
  const [QL1, , QL3] = Q;
  const [f1L1, f1L2, f1L3, f1L4] = F1;
  const [f2L1, f2L2, f2L3, f2L4] = F2;
  const y = qhalf(qadd(v, t));
  const f1H = atY(f1, y);
  const f2H = atY(f2, y);
  const IH = isolateRealRootsList([f1H, f2H], edgeOpts(u, s));
  const [IL2B, IL2U] = splitEdge(IL2, y, false);
  const [IL4B, IL4U] = splitEdge(IL4, y, true);
  const IB: Four<Edge[]> = [IL1, IL2B, reverseIntervals(IH), IL4B];
  const IU: Four<Edge[]> = [IH, IL2U, IL3, IL4U];
  const QB: Four<string[]> = [
    QL1,
    intervalsToQuadrants(IL2B, f1L2, f2L2, v, y),
    intervalsToQuadrants(at(IB, 2), f1H, f2H, s, u),
    intervalsToQuadrants(IL4B, f1L4, f2L4, y, v),
  ];
  const QU: Four<string[]> = [
    intervalsToQuadrants(IH, f1H, f2H, u, s),
    intervalsToQuadrants(IL2U, f1L2, f2L2, y, t),
    QL3,
    intervalsToQuadrants(IL4U, f1L4, f2L4, t, y),
  ];
  return [
    rect(windingNumber(traverseQuadrants(QB, true)), [u, v], [s, y], IB, QB, [f1L1, f1L2, f1H, f1L4], [f2L1, f2L2, f2H, f2L4]),
    rect(windingNumber(traverseQuadrants(QU, true)), [u, y], [s, t], IU, QU, [f1H, f1L2, f1L3, f1L4], [f2H, f2L2, f2L3, f2L4]),
  ];
}

/** Bisect across the longer side (SymPy: vertical when s - u > t - v). */
const bisect = (r: Rect, f1: Biv, f2: Biv): [Rect, Rect] =>
  qlt(qsub(r.b[1], r.a[1]), qsub(r.b[0], r.a[0])) ? verticalBisection(r, f1, f2) : horizontalBisection(r, f1, f2);

/** The rectangle [inf, sup] with its edges: intervals, quadrant sequences and polynomials. */
function edgeRect(f1: Biv, f2: Biv, [u, v]: [Q, Q], [s, t]: [Q, Q], exclude: boolean): Rect {
  const F1: Four<QP> = [atY(f1, v), atX(f1, s), atY(f1, t), atX(f1, u)];
  const F2: Four<QP> = [atY(f2, v), atX(f2, s), atY(f2, t), atX(f2, u)];
  const I: Four<Edge[]> = [
    isolateRealRootsList([F1[0], F2[0]], edgeOpts(u, s)),
    isolateRealRootsList([F1[1], F2[1]], edgeOpts(v, t)),
    reverseIntervals(isolateRealRootsList([F1[2], F2[2]], edgeOpts(u, s))),
    reverseIntervals(isolateRealRootsList([F1[3], F2[3]], edgeOpts(v, t))),
  ];
  const Q: Four<string[]> = [
    intervalsToQuadrants(I[0], F1[0], F2[0], u, s),
    intervalsToQuadrants(I[1], F1[1], F2[1], v, t),
    intervalsToQuadrants(I[2], F1[2], F2[2], s, u),
    intervalsToQuadrants(I[3], F1[3], F2[3], t, v),
  ];
  return rect(windingNumber(traverseQuadrants(Q, exclude)), [u, v], [s, t], I, Q, F1, F2);
}

const toQQ = (f: readonly (bigint | Q)[]): QP => f.map((c) => (typeof c === 'bigint' ? R(c) : c));
/** 2*max(|c|/|lc|): a bound on the moduli of the roots. */
function rootBound(f: QP): Q {
  const lc = qabs(first(f));
  return qmul(R(2n), f.reduce((m, c) => {
    const r = qdiv(qabs(c), lc);
    return qlt(m, r) ? r : m;
  }, QZERO));
}

/**
 * The number of roots of f in the rectangle [inf, sup] (corners as
 * [re, im]); roots on the boundary count (SymPy dup_count_complex_roots).
 */
export function countComplexRoots(f0: readonly (bigint | Q)[], inf?: [Q, Q], sup?: [Q, Q]): number {
  const f = toQQ(f0);
  const B = rootBound(f);
  const [f1, f2] = realImag(f);
  return edgeRect(f1, f2, inf ?? [qneg(B), qneg(B)], sup ?? [B, B], false).N;
}

/** An isolating rectangle of a non-real root (SymPy ComplexInterval); conj selects the conjugate root below the real axis. */
export class ComplexInterval {
  constructor(
    readonly a: [Q, Q],
    readonly b: [Q, Q],
    private readonly I: Four<Edge[]>,
    private readonly Q: Four<string[]>,
    private readonly F1: Four<QP>,
    private readonly F2: Four<QP>,
    private readonly f1: Biv,
    private readonly f2: Biv,
    readonly conj = false,
  ) {}
  get ax(): Q {
    return this.a[0];
  }
  get ay(): Q {
    return this.conj ? qneg(this.b[1]) : this.a[1];
  }
  get bx(): Q {
    return this.b[0];
  }
  get by(): Q {
    return this.conj ? qneg(this.a[1]) : this.b[1];
  }
  get dx(): Q {
    return qsub(this.b[0], this.a[0]);
  }
  get dy(): Q {
    return qsub(this.b[1], this.a[1]);
  }
  /** The center [re, im]. */
  get center(): [Q, Q] {
    return [qhalf(qadd(this.ax, this.bx)), qhalf(qadd(this.ay, this.by))];
  }
  /** The corners [[ax, ay], [bx, by]]. */
  asTuple(): [[Q, Q], [Q, Q]] {
    return [[this.ax, this.ay], [this.bx, this.by]];
  }
  toString(): string {
    return `(${this.ax.toString()}, ${this.bx.toString()}) x (${this.ay.toString()}, ${this.by.toString()})`;
  }
  /** The rectangle of the conjugate root. */
  conjugate(): ComplexInterval {
    return new ComplexInterval(this.a, this.b, this.I, this.Q, this.F1, this.F2, this.f1, this.f2, true);
  }
  /** Do the rectangles not intersect? */
  isDisjoint(other: ComplexInterval): boolean {
    if (this.conj !== other.conj) return true;
    if (qlt(this.bx, other.ax) || qlt(other.bx, this.ax)) return true;
    return qlt(this.by, other.ay) || qlt(other.by, this.ay);
  }
  /** One bisection keeping the half with the root. */
  private innerRefine(): ComplexInterval {
    const [lo, hi] = bisect(rect(1, this.a, this.b, this.I, this.Q, this.F1, this.F2), this.f1, this.f2);
    const { a, b, I, Q, F1, F2 } = lo.N === 1 ? lo : hi;
    return new ComplexInterval(a, b, I, Q, F1, F2, this.f1, this.f2, this.conj);
  }
  /** Refine both rectangles until they are disjoint. */
  refineDisjoint(other0: ComplexInterval): [ComplexInterval, ComplexInterval] {
    let expr: ComplexInterval = this;
    let other = other0;
    while (!expr.isDisjoint(other)) [expr, other] = [expr.innerRefine(), other.innerRefine()];
    return [expr, other];
  }
  /** Refine until the sides are shorter than dx and dy. */
  refineSize(dx: Q, dy: Q = dx): ComplexInterval {
    let expr: ComplexInterval = this;
    while (!(qlt(expr.dx, dx) && qlt(expr.dy, dy))) expr = expr.innerRefine();
    return expr;
  }
  /** Refine the given number of bisection steps. */
  refineStep(steps = 1): ComplexInterval {
    let expr: ComplexInterval = this;
    for (let i = 0; i < steps; i++) expr = expr.innerRefine();
    return expr;
  }
  /** One bisection step. */
  refine(): ComplexInterval {
    return this.innerRefine();
  }
}

/**
 * Isolating rectangles of the non-real roots of a square-free polynomial,
 * each conjugate (below the real axis) before its root, by increasing
 * lower-left corner (SymPy dup_isolate_complex_roots_sqf with blackbox=True).
 */
export function isolateComplexRootsSqf(f0: readonly (bigint | Q)[], { eps, inf, sup }: { eps?: Q | undefined; inf?: Q | undefined; sup?: Q | undefined } = {}): ComplexInterval[] {
  const f = toQQ(f0);
  if (f.length <= 1) return [];
  const B = rootBound(f);
  const [u, v, s, t] = [inf ?? qneg(B), QZERO, sup ?? B, B];
  if (!qlt(u, s)) throw new RangeError('not a valid complex isolation rectangle');
  const [f1, f2] = realImag(f);
  const start = edgeRect(f1, f2, [u, v], [s, t], false);
  if (!start.N) return [];
  const rectangles: Rect[] = [start];
  const roots: ComplexInterval[] = [];
  const small = ({ a, b }: Rect) => eps === undefined || (qlt(qsub(b[0], a[0]), eps) && qlt(qsub(b[1], a[1]), eps));
  while (rectangles.length) {
    // depth first: the rectangle of least area (SymPy _depth_first_select)
    let j = 0;
    const area = ({ a, b }: Rect) => qmul(qsub(b[0], a[0]), qsub(b[1], a[1]));
    rectangles.forEach((r, i) => {
      if (qlt(area(r), area(at(rectangles, j)))) j = i;
    });
    const [r] = rectangles.splice(j, 1);
    for (const D of bisect(defined(r), f1, f2)) {
      if (D.N < 1) continue;
      if (D.N === 1 && small(D)) roots.push(new ComplexInterval(D.a, D.b, D.I, D.Q, D.F1, D.F2, f1, f2));
      else rectangles.push(D);
    }
  }
  roots.sort((x, y) => cmp(x.ax, y.ax) || cmp(x.ay, y.ay));
  return roots.flatMap((r) => [r.conjugate(), r]);
}
