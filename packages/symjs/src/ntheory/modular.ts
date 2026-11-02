// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Chinese remainder theorem (SymPy sympy.ntheory.modular: crt,
 * crt1, crt2, solve_congruence, symmetric_residue, and galoistools gf_crt).
 */

import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import type { IntLike } from './intutil';
import { asInt, fdiv, gcdN, gcdext, pmod, prod } from './intutil';
import { isprime } from './primetest';

/** The residue of a modulo m in (-m/2, m/2] (SymPy symmetric_residue). */
export function symmetricResidue(a: bigint, m: bigint): bigint {
  return a <= fdiv(m, 2n) ? a : a - m;
}

/** @internal SymPy gf_crt over ZZ. */
export function gfCrt(U: readonly bigint[], M: readonly bigint[]): bigint {
  const p = prod(M);
  let v = 0n;
  M.forEach((m, i) => {
    const e = fdiv(p, m);
    const s = gcdext(e, m)[1];
    v += e * pmod(U[i]! * s, m);
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
    v += E[i]! * pmod(U[i]! * S[i]!, m);
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
    if (!vs.every((vi, i) => pmod(vi, ms[i]!) === pmod(result, ms[i]!))) {
      const r = solveCongruence(
        vs.map((vi, i): [bigint, bigint] => [vi, ms[i]!]),
        { check: false, symmetric },
      );
      if (r === NoMatch) return NoMatch;
      [result, mm] = r as [bigint, bigint];
    }
  }
  if (symmetric) return [symmetricResidue(result, mm), mm];
  return [result, mm];
}

/** The tuple [prod(m), E, S] for repeated use in crt2 (SymPy crt1). */
export function crt1(m: readonly IntLike[]): [bigint, bigint[], bigint[]] {
  return gfCrt1(m.map((x) => asInt(x)));
}

/** crt with the precomputed values of crt1 (SymPy crt2). */
export function crt2(m: readonly IntLike[], v: readonly IntLike[], mm: bigint, e: readonly bigint[], s: readonly bigint[], symmetric = false): [bigint, bigint] {
  const result = gfCrt2(
    v.map((x) => asInt(x)),
    m.map((x) => asInt(x)),
    mm,
    e,
    s,
  );
  return symmetric ? [symmetricResidue(result, mm), mm] : [result, mm];
}

/**
 * The solution [n, m] of the congruences n = r (mod m) given as [r, m]
 * pairs (SymPy solve_congruence), NoMatch when there is none.
 */
export function solveCongruence(pairs: readonly (readonly [IntLike, IntLike])[], opts: { symmetric?: boolean; check?: boolean } = {}): [bigint, bigint] | NoMatchResult {
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
