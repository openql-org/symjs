// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The root system of a simple Lie algebra (SymPy sympy.liealgebras.root_system).
 */

import type { Matrix } from '../matrices/matrix';
import { Rational } from '../core/nodes';
import { at, expectType } from '../core/guard';
import { add } from '../core/ops';
import type { CartanTypeLike, StandardCartan } from './cartantype';
import { CartanType } from './cartantype';
import type { Root, RootCoordinate } from './standard';

/** The sum of two root coordinates (numbers stay numbers). */
function addCoord(a: RootCoordinate, b: RootCoordinate): RootCoordinate {
  if (typeof a === 'number' && typeof b === 'number') return a + b;
  const s = expectType(add(a, b), (x): x is Rational => x instanceof Rational, 'rational coordinate');
  return s.q === 1n && Number.isSafeInteger(Number(s.p)) ? Number(s.p) : s;
}
const keyOf = (r: Root): string => r.map(String).join(',');

/** SymPy RootSystem: the root system of a Cartan type. */
export class RootSystem {
  /** The Cartan type. */
  readonly cartanType: StandardCartan;
  constructor(cartantype: CartanTypeLike) {
    this.cartanType = CartanType(cartantype);
  }
  /** SymPy simple_roots: the simple roots, numbered from 1. */
  simpleRoots(): Map<number, Root> {
    const n = this.cartanType.rank();
    return new Map(Array.from({ length: n }, (_x, i) => [i + 1, this.cartanType.simpleRoot(i + 1)] as const));
  }
  /** SymPy all_roots: the positive roots followed by their negatives. */
  allRoots(): Map<number, Root> {
    const alpha = this.cartanType.positiveRoots();
    let k = alpha.size;
    for (const root of [...alpha.values()]) alpha.set(++k, root.map((x) => (typeof x === 'number' ? -x : expectType(x.neg(), (y): y is Rational => y instanceof Rational, 'rational coordinate'))));
    return alpha;
  }
  /** SymPy root_space: the span of the simple roots, as text. */
  rootSpace(): string {
    return Array.from({ length: this.cartanType.rank() }, (_x, i) => `alpha[${i + 1}]`).join(' + ');
  }
  /** SymPy add_simple_roots: the sum of the simple roots of indices root1 and root2. */
  addSimpleRoots(root1: number, root2: number): Root {
    const alpha = this.simpleRoots();
    const a1 = alpha.get(root1);
    const a2 = alpha.get(root2);
    if (a1 === undefined || a2 === undefined) throw new RangeError("You've used a root that doesn't exist!");
    return a1.map((x, i) => addCoord(x, at(a2, i)));
  }
  /** SymPy add_as_roots: the sum of two roots when it is a root, else a message saying it is not. */
  addAsRoots(root1: readonly RootCoordinate[], root2: readonly RootCoordinate[]): Root | string {
    // (zip: the shorter root decides the length)
    const sum = root1.slice(0, Math.min(root1.length, root2.length)).map((x, i) => addCoord(x, at(root2, i)));
    const roots = new Set([...this.allRoots().values()].map(keyOf));
    return roots.has(keyOf(sum)) ? sum : 'The sum of these two roots is not a root';
  }
  /** SymPy cartan_matrix: the Cartan matrix of the Cartan type. */
  cartanMatrix(): Matrix {
    return this.cartanType.cartanMatrix();
  }
  /** SymPy dynkin_diagram: the Dynkin diagram of the Cartan type. */
  dynkinDiagram(): string {
    return this.cartanType.dynkinDiagram();
  }
}
