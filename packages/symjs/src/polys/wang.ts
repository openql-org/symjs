// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Factorization of multivariate integer polynomials by Wang's Enhanced
 * Extended Zassenhaus (EEZ) algorithm: a port of SymPy's dmp_zz_wang and its
 * helpers (dmp_zz_wang_test_points, dmp_zz_wang_lead_coeffs,
 * dup_zz_diophantine, dmp_zz_diophantine, dmp_zz_wang_hensel_lifting) from
 * sympy/polys/factortools.py (SymPy, BSD 3-Clause license).
 *
 * Polynomials are sparse maps from exponent tuples (one exponent per
 * variable, the main variable x_0 first) to nonzero integer coefficients;
 * every polynomial of one factorization has the same number of variables.
 */

import { at, defined, first, last } from '../core/guard';
import { Rational } from '../core/nodes';
import { gcd as igcd, iroot } from '../core/numbers';
import { nextprime } from '../ntheory/generate';
import { UPoly } from './poly';
import { derivative, padd, pdivmod, pgcd, pgcdex, pmod, pmul, zassenhaus } from './zassenhaus';

/** A term: the exponents of the variables and a nonzero integer coefficient. */
export interface ZTerm {
  e: readonly number[];
  c: bigint;
}
/** A sparse polynomial with integer coefficients, keyed by the exponent tuple. */
export type ZPoly = Map<string, ZTerm>;
/** A univariate integer polynomial, lowest degree first. */
type P = bigint[];

const keyOf = (e: readonly number[]): string => e.join(',');

function addTerm(f: ZPoly, e: readonly number[], c: bigint): void {
  if (c === 0n) return;
  const k = keyOf(e);
  const s = (f.get(k)?.c ?? 0n) + c;
  if (s === 0n) f.delete(k);
  else f.set(k, { e, c: s });
}

/** The polynomial with the given terms (like terms are added). */
export function zpoly(terms: Iterable<readonly [readonly number[], bigint]>): ZPoly {
  const f: ZPoly = new Map();
  for (const [e, c] of terms) addTerm(f, e, c);
  return f;
}

const terms = (f: ZPoly): ZTerm[] => [...f.values()];
const add = (f: ZPoly, g: ZPoly): ZPoly => zpoly([...terms(f), ...terms(g)].map((t) => [t.e, t.c] as const));
const sub = (f: ZPoly, g: ZPoly): ZPoly => zpoly([...terms(f).map((t) => [t.e, t.c] as const), ...terms(g).map((t) => [t.e, -t.c] as const)]);
const mapCoeffs = (f: ZPoly, fn: (c: bigint) => bigint): ZPoly => zpoly(terms(f).map((t) => [t.e, fn(t.c)] as const));

function mul(f: ZPoly, g: ZPoly): ZPoly {
  const out: ZPoly = new Map();
  for (const s of f.values()) for (const t of g.values()) addTerm(out, s.e.map((k, i) => k + at(t.e, i)), s.c * t.c);
  return out;
}

const one = (n: number): ZPoly => zpoly([[Array<number>(n).fill(0), 1n]]);
const product = (F: readonly ZPoly[], n: number): ZPoly => F.reduce(mul, one(n));
/** x_i - a. */
const linear = (n: number, i: number, a: bigint): ZPoly =>
  zpoly([
    [Array.from({ length: n }, (_, j) => (j === i ? 1 : 0)), 1n],
    [Array<number>(n).fill(0), -a],
  ]);

const babs = (a: bigint): bigint => (a < 0n ? -a : a);
/** The symmetric representative of c modulo p (SymPy dup_trunc, gf_int). */
const symMod = (c: bigint, p: bigint): bigint => {
  const r = ((c % p) + p) % p;
  return r > p / 2n ? r - p : r;
};
const trunc = (f: ZPoly, p: bigint): ZPoly => mapCoeffs(f, (c) => symMod(c, p));
const factorial = (k: number): bigint => {
  let r = 1n;
  for (let i = 2; i <= k; i++) r *= BigInt(i);
  return r;
};

const degIn = (f: ZPoly, i: number): number => Math.max(-1, ...terms(f).map((t) => at(t.e, i)));
const setExp = (e: readonly number[], i: number, k: number): number[] => e.map((x, j) => (j === i ? k : x));

/** f with x_i = a. */
const evalIn = (f: ZPoly, i: number, a: bigint): ZPoly => zpoly(terms(f).map((t) => [setExp(t.e, i, 0), t.c * a ** BigInt(at(t.e, i))] as const));

/** The k-th derivative of f in x_i at x_i = a (SymPy dmp_diff_eval_in). */
function diffEvalIn(f: ZPoly, i: number, k: number, a: bigint): ZPoly {
  const out: [number[], bigint][] = [];
  for (const t of f.values()) {
    const m = at(t.e, i);
    if (m < k) continue;
    let c = t.c;
    for (let j = 0; j < k; j++) c *= BigInt(m - j);
    out.push([setExp(t.e, i, 0), c * a ** BigInt(m - k)]);
  }
  return zpoly(out);
}

/** f at x_i = A[i - 1] for every i >= 1: an integer polynomial in x_0. */
const evalTail = (f: ZPoly, A: readonly bigint[]): ZPoly => A.reduce((g, a, i) => evalIn(g, i + 1, a), f);
/** The value of a polynomial free of x_0 at x_i = A[i - 1]. */
const evalAll = (f: ZPoly, A: readonly bigint[]): bigint => first(toDup(evalTail(f, A)).concat([0n]));

/** Lexicographic comparison of distinct exponent tuples. */
function cmpLex(a: readonly number[], b: readonly number[]): number {
  const i = a.findIndex((k, j) => k !== at(b, j));
  return at(a, i) - at(b, i);
}
const leadTerm = (f: ZPoly): ZTerm => terms(f).reduce((s, t) => (cmpLex(t.e, s.e) > 0 ? t : s));

/** The leading coefficient in x_0 (a polynomial in the other variables). */
function lc0(f: ZPoly): ZPoly {
  const d = degIn(f, 0);
  return zpoly(terms(f).filter((t) => at(t.e, 0) === d).map((t) => [setExp(t.e, 0, 0), t.c] as const));
}

/** Exact quotient f / g (g divides f). */
function exquo(f: ZPoly, g: ZPoly): ZPoly {
  const lt = leadTerm(g);
  let r = f;
  const q: ZPoly = new Map();
  // each step removes the leading term of r and adds only smaller ones
  while (r.size) {
    const t = leadTerm(r);
    const m = zpoly([[t.e.map((k, i) => k - at(lt.e, i)), t.c / lt.c]]);
    for (const s of m.values()) addTerm(q, s.e, s.c);
    r = sub(r, mul(m, g));
  }
  return q;
}

/** A polynomial in x_0 only as a dense list, lowest degree first. */
function toDup(f: ZPoly): P {
  const out: P = Array<bigint>(degIn(f, 0) + 1).fill(0n);
  for (const t of f.values()) out[at(t.e, 0)] = t.c;
  return out;
}
const fromDup = (g: readonly bigint[], n: number): ZPoly => zpoly(g.map((c, k) => [Array.from({ length: n }, (_, j) => (j ? 0 : k)), c] as const));

const toInt = (g: P, p: bigint): P => g.map((c) => symMod(c, p));
const lshift = (g: P, m: number): P => [...Array<bigint>(m).fill(0n), ...g];

/** s_i with sum s_i * prod_{j != i} F_j = x**m modulo p and deg s_i < deg F_i (SymPy dup_zz_diophantine). */
function dupDiophantine(F: readonly P[], m: number, p: bigint): P[] {
  if (F.length === 2) {
    const [a, b] = [pmod(first(F), p), pmod(last(F), p)];
    const [s0, t0] = pgcdex(b, a, p);
    const [q, s] = pdivmod(lshift(s0, m), a, p);
    const t = padd(lshift(t0, m), pmul(q, b, p), p);
    return [toInt(s, p), toInt(t, p)];
  }
  const G: P[] = [last(F)];
  for (let i = F.length - 2; i >= 1; i--) G.unshift(toDup(mul(fromDup(at(F, i), 1), fromDup(first(G), 1))));
  const S: P[] = [];
  let T: P = [1n];
  for (let i = 0; i < G.length; i++) {
    const [t, s] = diophantineUni([at(G, i), at(F, i)], T, p);
    T = defined(t, 'solution');
    S.push(defined(s, 'solution'));
  }
  S.push(T);
  return S.map((s, i) => toInt(pdivmod(lshift(pmod(s, p), m), pmod(at(F, i), p), p)[1], p));
}

/** dmp_zz_diophantine without evaluation points: c is a polynomial in x_0. */
function diophantineUni(F: readonly P[], c: P, p: bigint): P[] {
  let S: P[] = F.map(() => []);
  c.forEach((coeff, m) => {
    if (coeff === 0n) return;
    const T = dupDiophantine(F, m, p);
    S = S.map((s, j) => {
      const t = at(T, j).map((x) => x * coeff);
      return toInt(Array.from({ length: Math.max(s.length, t.length) }, (_, i) => (s[i] ?? 0n) + (t[i] ?? 0n)), p);
    });
  });
  return S;
}

/** Multivariate Diophantine equations modulo p (SymPy dmp_zz_diophantine); A are the points of x_1..x_k. */
function diophantine(F: readonly ZPoly[], c: ZPoly, A: readonly bigint[], d: number, p: bigint, n: number): ZPoly[] {
  if (!A.length) return diophantineUni(F.map(toDup), toDup(c), p).map((s) => fromDup(s, n));
  const k = A.length;
  const a = last(A);
  const A1 = A.slice(0, -1);
  const e = product(F, n);
  const B = F.map((f) => exquo(e, f));
  const G = F.map((f) => evalIn(f, k, a));
  let S = diophantine(G, evalIn(c, k, a), A1, d, p, n);
  let r = c;
  S.forEach((s, i) => {
    r = sub(r, mul(s, at(B, i)));
  });
  r = trunc(r, p);
  const m = linear(n, k, a);
  let M = one(n);
  // a zero derivative gives zero corrections, as the equations are linear
  for (let j = 0; j < d && r.size; j++) {
    M = mul(M, m);
    const C = mapCoeffs(diffEvalIn(r, k, j + 1, a), (x) => x / factorial(j + 1));
    const T = diophantine(G, C, A1, d, p, n).map((t) => mul(t, M));
    S = S.map((s, i) => add(s, at(T, i)));
    T.forEach((t, i) => {
      r = sub(r, mul(t, at(B, i)));
    });
    r = trunc(r, p);
  }
  return S.map((s) => trunc(s, p));
}

/** Parallel Hensel lifting of the univariate factors H with true leading coefficients LC (SymPy dmp_zz_wang_hensel_lifting). */
function henselLifting(f: ZPoly, H0: readonly P[], LC: readonly ZPoly[], A: readonly bigint[], p: bigint, n: number): ZPoly[] | undefined {
  const u = A.length;
  const S: ZPoly[] = [f];
  for (let i = u; i >= 2; i--) S.unshift(trunc(evalIn(first(S), i, at(A, i - 1)), p));
  const d = Math.max(...A.map((_, i) => degIn(f, i + 1)));
  const degs = H0.map((h) => h.length - 1);
  let H = H0.map((h) => fromDup(h, n));
  for (let w = 1; w <= u; w++) {
    const s = at(S, w - 1);
    const a = at(A, w - 1);
    const G = [...H];
    const I = A.slice(0, w - 1);
    H = H.map((h, i) => {
      let lc = at(LC, i);
      for (let v = w + 1; v <= u; v++) lc = evalIn(lc, v, at(A, v - 1));
      const dh = at(degs, i);
      const rest = terms(h).filter((t) => at(t.e, 0) !== dh);
      return zpoly([...rest.map((t) => [t.e, t.c] as const), ...terms(trunc(lc, p)).map((t) => [setExp(t.e, 0, dh), t.c] as const)]);
    });
    const m = linear(n, w, a);
    let M = one(n);
    let c = sub(s, product(H, n));
    const dj = degIn(s, w);
    for (let k = 0; k < dj && c.size; k++) {
      M = mul(M, m);
      const C = mapCoeffs(diffEvalIn(c, w, k + 1, a), (x) => x / factorial(k + 1));
      const T = diophantine(G, C, I, d, p, n);
      H = H.map((h, i) => trunc(add(h, mul(at(T, i), M)), p));
      c = trunc(sub(s, product(H, n)), p);
    }
  }
  return sub(product(H, n), f).size ? undefined : H;
}

/** SymPy dmp_zz_wang_non_divisors: whether every E_i has a prime factor not dividing cs*ct and the earlier E_j. */
function nonDivisors(E: readonly bigint[], cs: bigint, ct: bigint): boolean {
  const result = [cs * ct];
  for (const e of E) {
    let q = babs(e);
    for (const r0 of [...result].reverse()) {
      let r = r0;
      while (r !== 1n) {
        r = igcd(r, q);
        q /= r;
      }
      if (q === 1n) return false;
    }
    result.push(q);
  }
  return true;
}

interface Config {
  cs: bigint;
  s: P;
  E: bigint[];
  H: P[];
  A: bigint[];
}

const primitive = (g: P): [bigint, P] => {
  const c = g.reduce((x, y) => igcd(x, y), 0n);
  const s = (last(g) < 0n ? -1n : 1n) * c;
  return [s, g.map((x) => x / s)];
};

/** A prime for the square-free test modulo p. */
const SQF_PRIME = 2147483647n;

/**
 * Whether an integer polynomial of positive degree is square-free (SymPy dup_sqf_p): a gcd of
 * degree 0 with the derivative modulo a prime not dividing the leading coefficient proves it,
 * otherwise the gcd over QQ decides.
 */
function squareFree(g: P): boolean {
  if (last(g) % SQF_PRIME !== 0n && pgcd(g, derivative(g), SQF_PRIME).length === 1) return true;
  const u = new UPoly(g.map((c) => Rational.of(c)));
  return u.gcd(u.derivative()).degree === 0;
}

/** SymPy dmp_zz_wang_test_points: (cs, the primitive image s, E) or undefined for an unlucky point. */
function testPoints(f: ZPoly, T: readonly ZPoly[], ct: bigint, A: readonly bigint[]): Omit<Config, 'H' | 'A'> | undefined {
  if (evalAll(lc0(f), A) === 0n) return undefined;
  const image = toDup(evalTail(f, A));
  if (!squareFree(image)) return undefined;
  const [cs, s] = primitive(image);
  const E = T.map((t) => evalAll(t, A));
  return nonDivisors(E, cs, ct) ? { cs, s, E } : undefined;
}

/** SymPy dmp_zz_wang_lead_coeffs: the scaled f, the univariate factors and their true leading coefficients. */
function leadCoeffs(f0: ZPoly, T: readonly ZPoly[], cs0: bigint, E: readonly bigint[], H: readonly P[], A: readonly bigint[], n: number): [ZPoly, P[], ZPoly[]] | undefined {
  const J = E.map(() => false);
  const C = H.map((h) => {
    let c = one(n);
    let d = last(h) * cs0;
    for (let i = E.length - 1; i >= 0; i--) {
      const e = at(E, i);
      let k = 0;
      while (d % e === 0n) {
        d /= e;
        k++;
      }
      if (k) {
        for (let j = 0; j < k; j++) c = mul(c, at(T, i));
        J[i] = true;
      }
    }
    return c;
  });
  if (!J.every(Boolean)) return undefined;
  let cs = cs0;
  const HH: P[] = [];
  const CC = C.map((c, i) => {
    let h = at(H, i);
    let d = evalAll(c, A);
    const lc = last(h);
    let cc: bigint;
    // (an inexact quotient only occurs for extraneous factors, which the lifting rejects)
    if (cs === 1n) cc = lc / d;
    else {
      const g = igcd(lc, d);
      [d, cc] = [d / g, lc / g];
      h = h.map((x) => x * d);
      cs /= d;
    }
    HH.push(h);
    return mapCoeffs(c, (x) => x * cc);
  });
  if (cs === 1n) return [f0, HH, CC];
  const s = cs;
  return [mapCoeffs(f0, (x) => x * s ** BigInt(H.length - 1)), HH.map((h) => h.map((x) => x * s)), CC.map((c) => mapCoeffs(c, (x) => x * s))];
}

/** Mignotte bound of a multivariate integer polynomial (SymPy dmp_zz_mignotte_bound). */
function mignotte(f: ZPoly, n: number): bigint {
  const a = terms(f).reduce((m, t) => (babs(t.c) > m ? babs(t.c) : m), 0n);
  const b = babs(leadTerm(f).c);
  const N = Array.from({ length: n }, (_, i) => degIn(f, i)).reduce((x, y) => x + y, 0);
  return iroot(BigInt(N + 1), 2n) * 2n ** BigInt(N) * a * b;
}

/** A deterministic generator of integers in [lo, hi] (SymPy draws random ones). */
export type RandInt = (lo: number, hi: number) => number;
function lcgRandInt(): RandInt {
  let state = 12345;
  return (lo, hi) => {
    state = (state * 1103515245 + 12345) % 2147483648;
    return lo + (state % (hi - lo + 1));
  };
}

/**
 * The irreducible factors over ZZ of a primitive square-free polynomial f in
 * n >= 2 variables, of positive degree in x_0 and primitive as a polynomial
 * in x_0 (SymPy dmp_zz_wang). lcFactor factors the leading coefficient in x_0
 * into its content and irreducible factors. The factors are primitive with a
 * positive leading coefficient in lexicographic order, unless f is
 * irreducible, which is returned as it is.
 */
export function wangFactor(f: ZPoly, n: number, lcFactor: (lc: ZPoly) => [bigint, ZPoly[]], randint: RandInt = lcgRandInt(), mod0?: number): ZPoly[] {
  const u = n - 1;
  const [ct, T] = lcFactor(lc0(f));
  const p = nextprime(mignotte(f, n));
  let mod = mod0 ?? (u === 1 ? 2 : 1);
  const history = new Set<string>();
  let configs: Config[] = [];
  let r: number | undefined;
  const A0 = Array<bigint>(u).fill(0n);
  const t0 = testPoints(f, T, ct, A0);
  if (t0) {
    const H = zassenhaus(t0.s);
    r = H.length;
    if (r === 1) return [f];
    configs = [{ ...t0, H, A: A0 }];
  }
  while (configs.length < 3) {
    for (let i = 0; i < 5 && configs.length < 3; i++) {
      const A = Array.from({ length: u }, () => BigInt(randint(-mod, mod)));
      const key = A.join(',');
      if (history.has(key)) continue;
      history.add(key);
      const tp = testPoints(f, T, ct, A);
      if (!tp) continue;
      const H = zassenhaus(tp.s);
      const rr = H.length;
      if (r !== undefined && rr > r) continue;
      if (r !== undefined && rr < r) configs = [];
      r = rr;
      if (r === 1) return [f];
      configs.push({ ...tp, H, A });
    }
    if (configs.length < 3) mod += 2;
  }
  const norm = (s: P): bigint => s.reduce((m, c) => (babs(c) > m ? babs(c) : m), 0n);
  const best = configs.reduce((b, c) => (norm(c.s) < norm(b.s) ? c : b));
  const lead = leadCoeffs(f, T, best.cs, best.E, best.H, best.A, n);
  const factors = lead && henselLifting(lead[0], lead[1], lead[2], best.A, p, n);
  // an extraneous univariate factorization: SymPy restarts with a larger range of points
  if (!factors) return wangFactor(f, n, lcFactor, randint, mod + 1);
  return factors.map((g) => {
    const c = terms(g).reduce((x, t) => igcd(x, t.c), 0n);
    const s = leadTerm(g).c < 0n ? -c : c;
    return mapCoeffs(g, (x) => x / s);
  });
}
