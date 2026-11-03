// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real root isolation by continued fractions (port of SymPy
 * polys/rootisolation.py: dup_isolate_real_roots, dup_refine_real_root).
 *
 * Polynomials are dense bigint arrays, highest degree first (SymPy's dup).
 */

import { at, first, last } from '../core/guard';
import { Rational } from '../core/nodes';

type P = bigint[];
type M = [bigint, bigint, bigint, bigint];
type Q = Rational;

const R = (p: bigint, q: bigint = 1n): Q => Rational.of(p, q);

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

/** f(x + a) (Taylor shift). */
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
const reverse = (f: P): P => strip([...f].reverse());
/** f(-x). */
const mirror = (f: P): P => {
  const n = f.length - 1;
  return f.map((c, i) => ((n - i) % 2 === 1 ? -c : c));
};
/** f/x for f(0) = 0. */
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

/**
 * SymPy dup_root_upper_bound (Kioustelidis/Akritas): a power of two. f has a
 * sign variation (it is only used for polynomials with a positive root), so
 * after making the leading coefficient positive some coefficient is negative,
 * and a positive one (the leading coefficient) follows it.
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

function rootLowerBound(f: P): bigint {
  const b = rootUpperBound(reverse(f));
  // int(1/b)
  return b.q / b.p;
}

/** f(x + n) with the Mobius map composed with x -> x + n. */
const shiftBy = (f: P, n: bigint, [a, b, c, d]: M): [P, M] => [shift(f, n), [a, n * a + b, c, n * c + d]];

function stepRefine(f0: P, M0: M): [P, M] {
  if (M0[0] === M0[1] && M0[2] === M0[3]) return [f0, M0];
  const A = rootLowerBound(f0);
  // shift by the lower bound (when at least 1), then by 1; a root at the shift point is exact
  let [f, m] = [f0, M0];
  let [g, gm] = [f0, M0];
  for (const n of A >= 1n ? [A, 1n] : [1n]) {
    [g, gm] = [f, m];
    [f, m] = shiftBy(g, n, gm);
    if (TC(f) === 0n) return [f, [m[1], m[1], m[3], m[3]]];
  }
  if (signVariations(f) === 1) return [f, m];
  // the root is in (0, 1) of g: x -> 1/(x + 1). g(1) != 0, so the shifted reverse has no root at 0
  const [a, b, c, d] = gm;
  return [shift(reverse(g), 1n), [b, a + b, d, c + d]];
}

const interval = ([a, b, c, d]: M): [Q, Q] => {
  const s = R(a, c);
  const t = R(b, d);
  return cmp(s, t) <= 0 ? [s, t] : [t, s];
};
const cmp = (x: Q, y: Q) => {
  const v = x.p * y.q - y.p * x.q;
  return v < 0n ? -1 : v > 0n ? 1 : 0;
};
const width = ([a, b, c, d]: M): Q => {
  const v = R(a, c);
  const w = R(b, d);
  const diff = R(v.p * w.q - w.p * v.q, v.q * w.q);
  return diff.p < 0n ? R(-diff.p, diff.q) : diff;
};

function innerRefine(f0: P, M0: M, eps?: Q, steps?: number): [P, M] {
  let f = f0;
  let m = M0;
  while (m[2] === 0n) [f, m] = stepRefine(f, m);
  if (eps !== undefined && steps !== undefined) {
    for (let i = 0; i < steps && cmp(width(m), eps) >= 0; i++) [f, m] = stepRefine(f, m);
  } else {
    if (eps !== undefined) while (cmp(width(m), eps) >= 0) [f, m] = stepRefine(f, m);
    if (steps !== undefined) for (let i = 0; i < steps; i++) [f, m] = stepRefine(f, m);
  }
  return [f, m];
}

/**
 * f(x + n) with the Mobius map shifted; a root at the shift point is recorded
 * as exact and divided out. Returns [f, M, 1 if a root was taken out else 0].
 */
function shiftOut(f0: P, n: bigint, m0: M, roots: [P, M][]): [P, M, number] {
  const [f, m] = shiftBy(f0, n, m0);
  if (TC(f) !== 0n) return [f, m, 0];
  roots.push([f, [m[1], m[1], m[3], m[3]]]);
  return [rshift(f, 1), m, 1];
}

function innerIsolate(f0: P, eps?: Q): [P, M][] {
  let f = f0;
  const k0 = signVariations(f);
  if (k0 === 0) return [];
  const roots: [P, M][] = [];
  if (k0 === 1) return [innerRefine(f, [1n, 0n, 0n, 1n], eps)];
  const stack: [bigint, bigint, bigint, bigint, P, number][] = [[1n, 0n, 0n, 1n, f, k0]];
  for (let top = stack.pop(); top !== undefined; top = stack.pop()) {
    let [a, b, c, d, g, k] = top;
    f = g;
    const A = rootLowerBound(f);
    if (A >= 1n) {
      [f, [a, b, c, d]] = shiftOut(f, A, [a, b, c, d], roots);
      k = signVariations(f);
      if (k === 0) continue;
      if (k === 1) {
        roots.push(innerRefine(f, [a, b, c, d], eps));
        continue;
      }
    }
    let [f1, [a1, b1, c1, d1], r]: [P | undefined, M, number] = shiftOut(f, 1n, [a, b, c, d], roots);
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
    // f1 is only missing when k = 2 with the root at 1 taken out (k1 = 0, k2 = 1): f(1) = 0
    f1 ??= rshift(shift(reverse(f), 1n), 1);
    if (k1 === 1) roots.push(innerRefine(f1, [a1, b1, c1, d1], eps));
    else stack.push([a1, b1, c1, d1, f1, k1]);
    if (!k2) continue;
    if (f2 === undefined) {
      f2 = shift(reverse(f), 1n);
      if (TC(f2) === 0n) f2 = rshift(f2, 1);
    }
    if (k2 === 1) roots.push(innerRefine(f2, [a2, b2, c2, d2], eps));
    else stack.push([a2, b2, c2, d2, f2, k2]);
  }
  return roots;
}

function disjoint(M1: M, N1: M): boolean {
  let [a1, b1, c1, d1] = M1;
  let [a2, b2, c2, d2] = N1;
  if (a1 * d1 === b1 * c1 && a2 * d2 === b2 * c2) return true;
  if (a1 * d1 > b1 * c1) [a1, c1, b1, d1] = [b1, d1, a1, c1];
  if (a2 * d2 > b2 * c2) [a2, c2, b2, d2] = [b2, d2, a2, c2];
  return a2 * d1 >= c2 * b1 || b2 * c1 <= d2 * a1;
}

/**
 * Isolating intervals of the real roots of an integer polynomial given by
 * its square-free factors [(f, multiplicity)] (SymPy dup_isolate_real_roots).
 * Returns [[s, t], multiplicity] sorted by the intervals.
 */
export function isolateRealRoots(factors: [P, number][], eps?: Q): [[Q, Q], number][] {
  type E = [P, M, number];
  const pos: E[] = [];
  const neg: E[] = [];
  let zeroMult = 0;
  for (const [f0, k] of factors) {
    let f = strip(f0);
    let j = 0;
    while (f.length > 1 && TC(f) === 0n) {
      f = rshift(f, 1);
      j++;
    }
    if (j > 0) zeroMult += j * k;
    if (degree(f) <= 0) continue;
    for (const [g, m] of innerIsolate(f, eps)) pos.push([g, m, k]);
    for (const [g, m] of innerIsolate(mirror(f), eps)) neg.push([g, m, k]);
  }
  const disjoin = (list: E[]) => {
    for (let i = 0; i < list.length; i++) {
      for (let j = i + 1; j < list.length; j++) {
        let [f, m, k] = at(list, i);
        let [g, n, l] = at(list, j);
        while (!disjoint(m, n)) {
          [f, m] = innerRefine(f, m, undefined, 1);
          [g, n] = innerRefine(g, n, undefined, 1);
        }
        list[i] = [f, m, k];
        list[j] = [g, n, l];
      }
    }
  };
  if (factors.length > 1) {
    disjoin(pos);
    disjoin(neg);
  }
  const out: [[Q, Q], number][] = [];
  for (const [, m, k] of neg) {
    const [u, v] = interval(m);
    out.push([[R(-v.p, v.q), R(-u.p, u.q)], k]);
  }
  if (zeroMult) out.push([[R(0n), R(0n)], zeroMult]);
  for (const [, m, k] of pos) out.push([interval(m), k]);
  out.sort((x, y) => cmp(x[0][0], y[0][0]) || cmp(x[0][1], y[0][1]));
  return out;
}

/** Refine an isolating interval (s, t) of a root of f to width < eps (SymPy dup_refine_real_root). */
export function refineRealRoot(f0: P, s0: Q, t0: Q, eps?: Q, steps?: number): [Q, Q] {
  let f = f0;
  let [s, t] = cmp(s0, t0) <= 0 ? [s0, t0] : [t0, s0];
  if (cmp(s, t) === 0) return [s, t];
  let negative = false;
  if (s.p < 0n) {
    if (t.p <= 0n) {
      f = mirror(f);
      [s, t] = [R(-t.p, t.q), R(-s.p, s.q)];
      negative = true;
    } else throw new RangeError(`Cannot refine a real root in (${s.toString()}, ${t.toString()})`);
  }
  const m: M = [s.p, t.p, s.q, t.q];
  // f transformed by the Mobius map x -> (a*x + b)/(c*x + d)
  const tr = transform(f, m);
  if (signVariations(tr) !== 1) throw new RangeError(`there should be exactly one root in (${s.toString()}, ${t.toString()}) interval`);
  const [, mm] = innerRefine(tr, m, eps, steps);
  const [u, v] = interval(mm);
  return negative ? [R(-v.p, v.q), R(-u.p, u.q)] : [u, v];
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
