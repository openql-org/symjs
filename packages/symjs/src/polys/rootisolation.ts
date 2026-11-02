// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real root isolation by continued fractions (port of SymPy
 * polys/rootisolation.py: dup_isolate_real_roots, dup_refine_real_root).
 *
 * Polynomials are dense bigint arrays, highest degree first (SymPy's dup).
 */

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
const LC = (f: P) => strip(f)[0] ?? 0n;
const TC = (f: P) => (f.length ? f[f.length - 1]! : 0n);

/** floor(log2(a)) for a > 0. */
const ilog2 = (a: bigint) => a.toString(2).length - 1;

/** f(x + a) (Taylor shift). */
function shift(f0: P, a: bigint): P {
  const f = [...f0];
  const n = f.length - 1;
  for (let i = n; i > 0; i--) for (let j = 0; j < i; j++) f[j + 1] = f[j + 1]! + a * f[j]!;
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

/** SymPy dup_root_upper_bound (Kioustelidis/Akritas): a power of two, or undefined. */
function rootUpperBound(f0: P): Q | undefined {
  let f = f0;
  const n = f.length;
  const t: number[] = Array(n).fill(1);
  if (LC(f) < 0n) f = f.map((c) => -c);
  f = [...f].reverse();
  const P: number[] = [];
  for (let i = 0; i < n; i++) {
    if (f[i]! >= 0n) continue;
    const a = ilog2(-f[i]!);
    const QL: [number, number][] = [];
    for (let j = i + 1; j < n; j++) {
      if (f[j]! <= 0n) continue;
      const q = t[j]! + a - ilog2(f[j]!);
      QL.push([Math.floor(q / (j - i)), j]);
    }
    if (!QL.length) continue;
    const q = QL.reduce((m, v) => (v[0] < m[0] || (v[0] === m[0] && v[1] < m[1]) ? v : m));
    t[q[1]] = t[q[1]]! + 1;
    P.push(q[0]);
  }
  if (!P.length) return undefined;
  const e = Math.max(...P) + 1;
  return e >= 0 ? R(2n ** BigInt(e)) : R(1n, 2n ** BigInt(-e));
}

function rootLowerBound(f: P): bigint {
  const b = rootUpperBound(reverse(f));
  if (b === undefined) return 0n;
  // int(1/b)
  return b.q / b.p;
}

function stepRefine(f0: P, M0: M): [P, M] {
  let f = f0;
  let [a, b, c, d] = M0;
  if (a === b && c === d) return [f, [a, b, c, d]];
  const A = rootLowerBound(f);
  if (A >= 1n) {
    f = shift(f, A);
    b = A * a + b;
    d = A * c + d;
    if (TC(f) === 0n) return [f, [b, b, d, d]];
  }
  const g = f;
  f = shift(f, 1n);
  const [a1, b1, c1, d1] = [a, a + b, c, c + d];
  if (TC(f) === 0n) return [f, [b1, b1, d1, d1]];
  const k = signVariations(f);
  if (k === 1) [a, b, c, d] = [a1, b1, c1, d1];
  else {
    f = shift(reverse(g), 1n);
    if (TC(f) === 0n) f = rshift(f, 1);
    [a, b, c, d] = [b, a + b, d, c + d];
  }
  return [f, [a, b, c, d]];
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

function innerIsolate(f0: P, eps?: Q): [P, M][] {
  let f = f0;
  const k0 = signVariations(f);
  if (k0 === 0) return [];
  const roots: [P, M][] = [];
  if (k0 === 1) return [innerRefine(f, [1n, 0n, 0n, 1n], eps)];
  const stack: [bigint, bigint, bigint, bigint, P, number][] = [[1n, 0n, 0n, 1n, f, k0]];
  while (stack.length) {
    let [a, b, c, d, g, k] = stack.pop()!;
    f = g;
    const A = rootLowerBound(f);
    if (A >= 1n) {
      f = shift(f, A);
      b = A * a + b;
      d = A * c + d;
      if (TC(f) === 0n) {
        roots.push([f, [b, b, d, d]]);
        f = rshift(f, 1);
      }
      k = signVariations(f);
      if (k === 0) continue;
      if (k === 1) {
        roots.push(innerRefine(f, [a, b, c, d], eps));
        continue;
      }
    }
    let f1: P | undefined = shift(f, 1n);
    let [a1, b1, c1, d1] = [a, a + b, c, c + d];
    let r = 0;
    if (TC(f1) === 0n) {
      roots.push([f1, [b1, b1, d1, d1]]);
      f1 = rshift(f1, 1);
      r = 1;
    }
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
    if (f1 === undefined) {
      f1 = shift(reverse(f), 1n);
      if (TC(f1) === 0n) f1 = rshift(f1, 1);
    }
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
        let [f, m, k] = list[i]!;
        let [g, n, l] = list[j]!;
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
    } else throw new Error(`Cannot refine a real root in (${s}, ${t})`);
  }
  const m: M = [s.p, t.p, s.q, t.q];
  // f transformed by the Mobius map x -> (a*x + b)/(c*x + d)
  const tr = transform(f, m);
  if (signVariations(tr) !== 1) throw new Error(`there should be exactly one root in (${s}, ${t}) interval`);
  const [, mm] = innerRefine(tr, m, eps, steps);
  const [u, v] = interval(mm);
  return negative ? [R(-v.p, v.q), R(-u.p, u.q)] : [u, v];
}

/** (c*x + d)**n * f((a*x + b)/(c*x + d)) (SymPy dup_transform with p = a*x + b, q = c*x + d). */
function transform(f: P, [a, b, c, d]: M): P {
  const n = f.length - 1;
  const mulP = (x: P, y: P): P => {
    const r: bigint[] = Array(x.length + y.length - 1).fill(0n);
    for (let i = 0; i < x.length; i++) for (let j = 0; j < y.length; j++) r[i + j] = r[i + j]! + x[i]! * y[j]!;
    return r;
  };
  const addP = (x: P, y: P): P => {
    const L = Math.max(x.length, y.length);
    const xx = Array(L - x.length).fill(0n).concat(x);
    const yy = Array(L - y.length).fill(0n).concat(y);
    return xx.map((v, i) => v + yy[i]!);
  };
  const p: P = [a, b];
  const q: P = [c, d];
  let res: P = [0n];
  for (let i = 0; i <= n; i++) {
    // coefficient f[i] of x**(n - i): p**(n - i) * q**i
    let term: P = [f[i]!];
    for (let k = 0; k < n - i; k++) term = mulP(term, p);
    for (let k = 0; k < i; k++) term = mulP(term, q);
    res = addP(res, term);
  }
  return strip(res);
}
