// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Egyptian fractions (SymPy sympy.ntheory.egyptian_fraction) with
 * the Greedy, Graham Jewett, Takenouchi and Golomb algorithms.
 */

import { at } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import { gcd } from '../core/numbers';
import { fdiv, invert, pmod } from './intutil';

/** The algorithms of egyptianFraction. */
export type EgyptianAlgorithm = 'Greedy' | 'Graham Jewett' | 'Takenouchi' | 'Golomb';

function greedy(xIn: bigint, yIn: bigint): bigint[] {
  const out: bigint[] = [];
  let x = xIn;
  let y = yIn;
  while (x !== 1n) {
    const a = pmod(-y, x);
    const b = y * (fdiv(y, x) + 1n);
    const c = gcd(a, b);
    out.push(fdiv(y, x) + 1n);
    [x, y] = c > 1n ? [a / c, b / c] : [a, b];
  }
  out.push(y);
  return out;
}

const cmp = (a: bigint, b: bigint): number => (a < b ? -1 : a > b ? 1 : 0);
const hasDup = (l: bigint[]): boolean => new Set(l).size !== l.length;

const isIntPair = (r: ExprLike | readonly [bigint | number, bigint | number]): r is readonly [bigint | number, bigint | number] => Array.isArray(r);

function grahamJewett(x: bigint, y: bigint): bigint[] {
  const l = new Array<bigint>(Number(x)).fill(y);
  while (hasDup(l)) {
    l.sort(cmp);
    let i = 0;
    for (; i < l.length - 1; i++) if (l[i] === l[i + 1]) break;
    const li = at(l, i);
    l[i + 1] = li + 1n;
    l.push(li * (li + 1n));
  }
  return l.sort(cmp);
}

function takenouchi(x: bigint, y: bigint): bigint[] {
  if (x === 3n) {
    if (y % 2n === 0n) return [y / 2n, y];
    const i = (y - 1n) / 2n;
    const j = i + 1n;
    const k = j + i;
    return [j, k, j * k];
  }
  const l = new Array<bigint>(Number(x)).fill(y);
  while (hasDup(l)) {
    l.sort(cmp);
    let i = 0;
    for (; i < l.length - 1; i++) if (l[i] === l[i + 1]) break;
    const k = at(l, i);
    if (k % 2n === 0n) {
      l[i] = k / 2n;
      l.splice(i + 1, 1);
    } else {
      l[i] = (k + 1n) / 2n;
      l[i + 1] = (k * (k + 1n)) / 2n;
    }
  }
  return l.sort(cmp);
}

function golomb(x: bigint, y: bigint): bigint[] {
  if (x === 1n) return [y];
  const xp = invert(x, y);
  const rv = [xp * y, ...golomb(fdiv(x * xp - 1n, y), xp)];
  return rv.sort(cmp);
}

/**
 * The denominators of an Egyptian fraction expansion of the positive
 * rational r (SymPy egyptian_fraction); r is a Rational or a [p, q] pair.
 */
export function egyptianFraction(r: ExprLike | readonly [bigint | number, bigint | number], algorithm: EgyptianAlgorithm = 'Greedy'): bigint[] {
  let q: Rational;
  if (isIntPair(r)) {
    q = Rational.of(BigInt(r[0]), BigInt(r[1]));
  } else {
    const e = sympify(r);
    if (!(e instanceof Rational)) throw new TypeError('Value must be a Rational or tuple of ints');
    q = e;
  }
  if (q.p <= 0n) throw new RangeError('Value must be positive');
  const x0 = q.p;
  const y0 = q.q;
  if (y0 === 1n && x0 === 2n) return [1n, 2n, 3n, 6n];
  if (x0 === y0 + 1n) return [1n, y0];
  // egypt_harmonic: the prefix 1 + 1/2 + ... + 1/d <= r
  const prefix: bigint[] = [];
  let accP = 0n;
  let accQ = 1n;
  let d = 1n;
  for (;;) {
    const np = accP * d + accQ;
    const nq = accQ * d;
    if (np * y0 > x0 * nq) break;
    const g = gcd(np, nq);
    [accP, accQ] = [np / g, nq / g];
    prefix.push(d);
    d++;
  }
  const rem = Rational.of(x0 * accQ - accP * y0, y0 * accQ);
  if (rem.p === 0n) return prefix;
  const [x, y] = [rem.p, rem.q];
  let postfix: bigint[];
  switch (algorithm) {
    case 'Greedy':
      postfix = greedy(x, y);
      break;
    case 'Graham Jewett':
      postfix = grahamJewett(x, y);
      break;
    case 'Takenouchi':
      postfix = takenouchi(x, y);
      break;
    case 'Golomb':
      postfix = golomb(x, y);
      break;
  }
  return [...prefix, ...postfix];
}
