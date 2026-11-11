// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Chinese remainder theorem (SymPy sympy.ntheory.modular: crt,
 * crt1, crt2, solve_congruence, symmetric_residue, and galoistools gf_crt).
 */

import { at } from '../core/guard';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import type { IntLike } from './intutil';
import { asInt, fdiv, gcdN, gcdext, pmod, prod } from './intutil';
import { isprime } from './primetest';

/** The residue of a modulo m in (-m/2, m/2] (SymPy symmetric_residue); a is a residue in [0, m). */
export function symmetricResidue(aIn: IntLike, mIn: IntLike): bigint {
  const a = asInt(aIn);
  const m = asInt(mIn);
  return a <= fdiv(m, 2n) ? a : a - m;
}

/** @internal SymPy gf_crt over ZZ. */
export function gfCrt(U: readonly bigint[], M: readonly bigint[]): bigint {
  const p = prod(M);
  let v = 0n;
  M.forEach((m, i) => {
    const e = fdiv(p, m);
    const s = gcdext(e, m)[1];
    v += e * pmod(at(U, i) * s, m);
  });
  return pmod(v, p);
}

/** @internal SymPy gf_crt1 over ZZ: [prod(M), E, S]. */
export function gfCrt1(M: readonly bigint[]): [bigint, bigint[], bigint[]] {
  const p = prod(M);
  const E: bigint[] = [];
  const S: bigint[] = [];
  for (const m of M) {
    const e = fdiv(p, m);
    E.push(e);
    S.push(pmod(gcdext(e, m)[1], m));
  }
  return [p, E, S];
}

/** @internal SymPy gf_crt2 over ZZ. */
export function gfCrt2(U: readonly bigint[], M: readonly bigint[], p: bigint, E: readonly bigint[], S: readonly bigint[]): bigint {
  let v = 0n;
  M.forEach((m, i) => {
    v += at(E, i) * pmod(at(U, i) * at(S, i), m);
  });
  return pmod(v, p);
}

/**
 * The integer x with x = v[i] (mod m[i]) and the product of the moduli,
 * [x, M] (SymPy crt); NoMatch when the congruences are inconsistent.
 * `check: false` skips the check for non-coprime moduli.
 */
export function crt(m: readonly IntLike[], v: readonly IntLike[], opts: { symmetric?: boolean; check?: boolean } = {}): [bigint, bigint] | NoMatchResult {
  const symmetric = opts.symmetric ?? false;
  const check = opts.check ?? true;
  const ms = m.map((x) => asInt(x));
  const vs = v.map((x) => asInt(x));
  let result = gfCrt(vs, ms);
  let mm = prod(ms);
  if (check) {
    if (!vs.every((vi, i) => pmod(vi, at(ms, i)) === pmod(result, at(ms, i)))) {
      const r = solveCongruence(...vs.map((vi, i): [bigint, bigint] => [vi, at(ms, i)]), { check: false, symmetric });
      if (isNoMatch(r)) return NoMatch;
      [result, mm] = r;
    }
  }
  if (symmetric) return [symmetricResidue(result, mm), mm];
  return [result, mm];
}

/** An [r, m] pair (not the options object). */
const isCongruence = (a: Congruence | SolveCongruenceOptions): a is Congruence => Array.isArray(a);

/** The tuple [prod(m), E, S] for repeated use in crt2 (SymPy crt1). */
export function crt1(m: readonly IntLike[]): [bigint, bigint[], bigint[]] {
  return gfCrt1(m.map((x) => asInt(x)));
}

/** crt with the precomputed values of crt1 (SymPy crt2). */
export function crt2(m: readonly IntLike[], v: readonly IntLike[], mmIn: IntLike, e: readonly IntLike[], s: readonly IntLike[], symmetric = false): [bigint, bigint] {
  const ints = (xs: readonly IntLike[]): bigint[] => xs.map((x) => asInt(x));
  const mm = asInt(mmIn);
  const result = gfCrt2(ints(v), ints(m), mm, ints(e), ints(s));
  return symmetric ? [symmetricResidue(result, mm), mm] : [result, mm];
}

/** A congruence n = r (mod m) as the pair [r, m]. */
export type Congruence = readonly [IntLike, IntLike];

/** The options of {@link solveCongruence}. */
export interface SolveCongruenceOptions {
  /** The solution as a symmetric residue (in (-m/2, m/2]). */
  readonly symmetric?: boolean;
  /** Reduce repeated moduli and use crt when all moduli are prime (default true). */
  readonly check?: boolean;
}

/**
 * The solution [n, m] of the congruences n = r (mod m), each given as an
 * [r, m] pair, followed by the options (SymPy
 * `solve_congruence(*remainder_modulus_pairs, **hint)`); NoMatch when there
 * is none.
 *
 * `solveCongruence([2, 3], [3, 5], [2, 7])` is `[23n, 105n]`.
 */
export function solveCongruence(...args: readonly (Congruence | SolveCongruenceOptions)[]): [bigint, bigint] | NoMatchResult {
  const pairs = args.filter(isCongruence);
  const opts = args.find((a): a is SolveCongruenceOptions => !isCongruence(a)) ?? {};
  const symmetric = opts.symmetric ?? false;
  const combine = (c1: [bigint, bigint], c2: [bigint, bigint]): [bigint, bigint] | undefined => {
    const [a1, m1] = c1;
    const [a2, m2] = c2;
    let [a, b, c] = [m1, a2 - a1, m2];
    const g = gcdN(a, b, c);
    [a, b, c] = [fdiv(a, g), fdiv(b, g), fdiv(c, g)];
    if (a !== 1n) {
      const [g2, invA] = gcdext(a, c);
      if (g2 !== 1n) return undefined;
      b *= invA;
    }
    return [a1 + m1 * b, m1 * c];
  };
  let rm: [bigint, bigint][] = pairs.map(([r, m]) => [asInt(r), asInt(m)]);
  if (opts.check ?? true) {
    const uniq = new Map<bigint, bigint>();
    for (const [r0, m] of rm) {
      const r = pmod(r0, m);
      const u = uniq.get(m);
      if (u !== undefined) {
        if (r !== u) return NoMatch;
        continue;
      }
      uniq.set(m, r);
    }
    rm = [...uniq].map(([m, r]) => [r, m]);
    if (rm.every(([, m]) => isprime(m))) {
      return crt(
        rm.map(([, m]) => m),
        rm.map(([r]) => r),
        { symmetric, check: false },
      );
    }
  }
  let rv: [bigint, bigint] = [0n, 1n];
  for (const rmi of rm) {
    const c = combine(rv, rmi);
    if (c === undefined) return NoMatch;
    rv = [pmod(c[0], c[1]), c[1]];
  }
  const [n, m] = rv;
  return symmetric ? [symmetricResidue(n, m), m] : [n, m];
}
