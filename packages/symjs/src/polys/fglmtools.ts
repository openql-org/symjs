// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/fglmtools.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/** @file Matrix FGLM conversion of zero-dimensional Groebner bases. */

import { NotImplementedError } from '../core/errors';
import { at, defined } from '../core/guard';
import type { Expr } from '../core/nodes';
import type { Domain } from './domains';
import type { Monom, OrderLike, PolyElement, PolyRing } from './rings';

const incr = (m: Monom, k: number): number[] => m.map((e, i) => e + Number(i === k));
const divides = (a: Monom, b: Monom): boolean => a.every((e, i) => e <= at(b, i));
const matvec = (M: readonly (readonly Expr[])[], v: readonly Expr[], K: Pick<Domain, 'zero' | 'add' | 'mul'>): Expr[] => M.map((r) => r.reduce((s, c, i) => K.add(s, K.mul(c, at(v, i))), K.zero));

/** The polynomial operations used by FGLM, independent of a representation. @internal */
export interface FglmPolynomial<P> {
  readonly LM: Monom;
  readonly isZero: boolean;
  terms(): [Monom, Expr][];
  rem(divisors: readonly P[]): P;
  sub(other: P): P;
  monic(): P;
}

/** Minimal ring operations shared by PolyRing and the expression Groebner basis. @internal */
export interface FglmRing<P> {
  readonly domain: Pick<Domain, 'zero' | 'one' | 'isField' | 'isZero' | 'add' | 'sub' | 'mul' | 'quo'>;
  readonly symbols: readonly unknown[];
  readonly zeroMonom: Monom;
  readonly one: P;
  readonly order: { readonly isGlobal: boolean; compare(a: Monom, b: Monom): number };
  clone(options: { order: OrderLike }): FglmRing<P>;
  termNew(monomial: Monom, coefficient: Expr): P;
  fromDict(terms: Iterable<readonly [Monom, Expr]>): P;
}

/** Convert a reduced Groebner basis of a zero-dimensional ideal to another monomial order. */
export function matrixFglm(F: readonly PolyElement[], ring: PolyRing, order: OrderLike): PolyElement[] {
  return matrixFglmBasis(F, ring, order);
}

/** The common quotient-space algorithm for both polynomial representations. @internal */
export function matrixFglmBasis<P extends FglmPolynomial<P>>(F: readonly P[], ring: FglmRing<P>, order: OrderLike): P[] {
  const target = ring.clone({ order });
  const K = ring.domain;
  if (!K.isField) throw new TypeError('FGLM requires a coefficient field');
  if (!ring.order.isGlobal || !target.order.isGlobal) throw new RangeError('FGLM requires global monomial orders');
  const leading = F.filter((g) => !g.isZero).map((g) => g.LM);
  // The unit ideal has a zero-dimensional quotient vector space; its reduced Groebner basis is [1].
  if (leading.some((m) => m.every((e) => e === 0))) return [target.one];
  if (!ring.symbols.every((_, i) => leading.some((m) => at(m, i) > 0 && m.every((e, j) => j === i || e === 0)))) {
    throw new NotImplementedError('FGLM requires a zero-dimensional ideal');
  }
  const basis: Monom[] = [];
  const seen = new Set<string>();
  let candidates: Monom[] = [ring.zeroMonom];
  while (candidates.length) {
    const m = defined(candidates.pop());
    if (seen.has(m.join(','))) continue;
    seen.add(m.join(','));
    basis.push(m);
    candidates.push(...ring.symbols.map((_, i) => incr(m, i)).filter((n) => leading.every((lm) => !divides(lm, n))));
  }
  basis.sort((a, b) => ring.order.compare(a, b));
  const indices = new Map(basis.map((m, i) => [m.join(','), i]));
  const n = basis.length;
  const matrices = ring.symbols.map((_, k) => {
    const M = basis.map(() => basis.map(() => K.zero));
    basis.forEach((m, i) => {
      for (const [term, c] of ring.termNew(incr(m, k), K.one).rem(F).terms()) at(M, defined(indices.get(term.join(','))))[i] = c;
    });
    return M;
  });
  const S: Monom[] = [ring.zeroMonom];
  const V: Expr[][] = [basis.map((_, i) => i === 0 ? K.one : K.zero)];
  const P = basis.map((_, i) => basis.map((__, j) => i === j ? K.one : K.zero));
  const G: P[] = [];
  let pending: [number, number][] = ring.symbols.map((_, i) => [i, 0]);
  while (pending.length) {
    pending.sort(([i, j], [k, l]) => target.order.compare(incr(at(S, l), k), incr(at(S, j), i)));
    const [k, j] = defined(pending.pop());
    const m = incr(at(S, j), k);
    const v = matvec(at(matrices, k), at(V, j), K);
    const lambda = matvec(P, v, K);
    const s = S.length;
    if (lambda.slice(s).every((c) => K.isZero(c))) {
      const rest = target.fromDict(S.map((term, i) => [term, at(lambda, i)]));
      const g = target.termNew(m, K.one).sub(rest);
      if (!g.isZero) G.push(g);
    } else {
      const pivot = lambda.findIndex((c, i) => i >= s && !K.isZero(c));
      const d = at(lambda, pivot);
      for (let r = 0; r < n; r++) {
        if (r !== pivot) P[r] = at(P, r).map((c, i) => K.sub(c, K.quo(K.mul(at(at(P, pivot), i), at(lambda, r)), d)));
      }
      P[pivot] = at(P, pivot).map((c) => K.quo(c, d));
      [P[pivot], P[s]] = [at(P, s), at(P, pivot)];
      S.push(m);
      V.push(v);
      pending.push(...ring.symbols.map((_, i): [number, number] => [i, s]));
    }
    pending = pending.filter(([i, l]) => G.every((g) => !divides(g.LM, incr(at(S, l), i))));
  }
  return G.map((g) => g.monic()).sort((a, b) => target.order.compare(b.LM, a.LM));
}
