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

/**
 * The root system of a Cartan type.
 *
 * @see SymPy `sympy.liealgebras.root_system.RootSystem`
 */
export class RootSystem {
  /**
   * The Cartan type.
   *
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.cartan_type`
   */
  readonly cartanType: StandardCartan;
  /**
   * Builds the root system belonging to the specified Cartan type.
   *
   * @param cartantype - Cartan series and rank.
   */
  constructor(cartantype: CartanTypeLike) {
    this.cartanType = CartanType(cartantype);
  }
  /**
   * The simple roots, numbered from 1.
   *
   * @returns The indexed simple roots.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.simple_roots`
   */
  simpleRoots(): Map<number, Root> {
    const n = this.cartanType.rank();
    return new Map(Array.from({ length: n }, (_x, i) => [i + 1, this.cartanType.simpleRoot(i + 1)] as const));
  }
  /**
   * The positive roots followed by their negatives.
   *
   * @returns The indexed positive and negative roots.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.all_roots`
   */
  allRoots(): Map<number, Root> {
    const alpha = this.cartanType.positiveRoots();
    let k = alpha.size;
    for (const root of [...alpha.values()]) alpha.set(++k, root.map((x) => (typeof x === 'number' ? -x : expectType(x.neg(), (y): y is Rational => y instanceof Rational, 'rational coordinate'))));
    return alpha;
  }
  /**
   * The span of the simple roots, as text.
   *
   * @returns The span of the simple roots as text.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.root_space`
   */
  rootSpace(): string {
    return Array.from({ length: this.cartanType.rank() }, (_x, i) => `alpha[${i + 1}]`).join(' + ');
  }
  /**
   * The sum of the simple roots of indices root1 and root2.
   *
   * @param root1 - First one-based simple-root index.
   * @param root2 - Second one-based simple-root index.
   * @returns The coordinate sum of the simple roots.
   * @throws RangeError when the simple-root index is outside the series.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.add_simple_roots`
   */
  addSimpleRoots(root1: number, root2: number): Root {
    const alpha = this.simpleRoots();
    const a1 = alpha.get(root1);
    const a2 = alpha.get(root2);
    if (a1 === undefined || a2 === undefined) throw new RangeError("You've used a root that doesn't exist!");
    return a1.map((x, i) => addCoord(x, at(a2, i)));
  }
  /**
   * The sum of two roots when it is a root, else a message saying it is not.
   *
   * @param root1 - First root or root index.
   * @param root2 - Second root or root index.
   * @returns The sum if it is a root, otherwise an explanatory string.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.add_as_roots`
   */
  addAsRoots(root1: readonly RootCoordinate[], root2: readonly RootCoordinate[]): Root | string {
    // (zip: the shorter root decides the length)
    const sum = root1.slice(0, Math.min(root1.length, root2.length)).map((x, i) => addCoord(x, at(root2, i)));
    const roots = new Set([...this.allRoots().values()].map(keyOf));
    return roots.has(keyOf(sum)) ? sum : 'The sum of these two roots is not a root';
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    return this.cartanType.cartanMatrix();
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.root_system.RootSystem.dynkin_diagram`
   */
  dynkinDiagram(): string {
    return this.cartanType.dynkinDiagram();
  }
}
