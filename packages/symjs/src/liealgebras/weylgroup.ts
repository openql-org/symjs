// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Weyl group of a simple Lie algebra (SymPy sympy.liealgebras.weyl_group):
 * generators, order, the matrices of products of reflections and their orders.
 */

import { Rational } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import { Matrix } from '../matrices/matrix';
import type { CartanTypeLike, StandardCartan } from './cartantype';
import { CartanType } from './cartantype';
import { chain, labels } from './standard';

const factorial = (n: number): bigint => {
  let r = 1n;
  for (let i = 2n; i <= BigInt(n); i++) r *= i;
  return r;
};
/** The largest order element_order looks for (larger than any element order of the exceptional groups). */
const MAX_ORDER = 64;
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const gcd = (a: number, b: number): number => (b === 0 ? a : gcd(b, a % b));

/** The identity matrix of size n with some entries replaced. */
function eyeWith(n: number, entries: readonly (readonly [number, number, number])[]): Matrix {
  const m = new Map(entries.map(([i, j, v]) => [`${i},${j}`, v] as const));
  return Matrix.fromFunction(n, n, (i, j) => R(m.get(`${i},${j}`) ?? (i === j ? 1 : 0)));
}
/** The permutation matrix swapping a - 1 and a. */
const swap = (n: number, a: number): Matrix => eyeWith(n, [[a - 1, a - 1, 0], [a - 1, a, 1], [a, a - 1, 1], [a, a, 0]]);

const G_GENS = [Matrix.of([[1, 0, 0], [0, 0, 1], [0, 1, 0]]), Matrix.of([[R(2, 3), R(2, 3), R(-1, 3)], [R(2, 3), R(-1, 3), R(2, 3)], [R(-1, 3), R(2, 3), R(2, 3)]])];
const h = R(1, 2);
const nh = R(-1, 2);
const F_GENS = [
  Matrix.of([[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]]),
  Matrix.of([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]),
  Matrix.of([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]]),
  Matrix.of([[h, h, h, h], [h, h, nh, nh], [h, nh, h, nh], [h, nh, nh, h]]),
];
const q = R(1, 4);
const nq = R(-1, 4);
// the first reflection of E_8 (SymPy weyl_group)
const E_GEN1 = Matrix.of([
  [R(3, 4), q, q, q, q, q, q, nq],
  [q, R(3, 4), nq, nq, nq, nq, q, nq],
  [q, nq, R(3, 4), nq, nq, nq, nq, q],
  [q, nq, nq, R(3, 4), nq, nq, nq, q],
  [q, nq, nq, nq, R(3, 4), nq, nq, q],
  [q, nq, nq, nq, nq, R(3, 4), nq, q],
  [q, nq, nq, nq, nq, nq, R(-3, 4), q],
  [q, nq, nq, nq, nq, nq, nq, R(3, 4)],
]);

/** SymPy WeylGroup: the Weyl group of a Cartan type, whose elements are written as products of reflections 'r1*r2*...'. */
export class WeylGroup {
  /** The Cartan type. */
  readonly cartanType: StandardCartan;
  constructor(cartantype: CartanTypeLike) {
    this.cartanType = CartanType(cartantype);
  }
  /** SymPy generators: the names r1, ..., rn of the simple reflections. */
  generators(): string[] {
    return Array.from({ length: this.cartanType.rank() }, (_x, i) => `r${i + 1}`);
  }
  /** SymPy group_order: the order of the group (exact; SymPy gives an mpmath float). */
  groupOrder(): bigint {
    const n = this.cartanType.rank();
    switch (this.cartanType.series) {
      case 'A':
        return factorial(n + 1);
      case 'B':
      case 'C':
        return factorial(n) * 2n ** BigInt(n);
      case 'D':
        return factorial(n) * 2n ** BigInt(n - 1);
      case 'E':
        return at([51840n, 2903040n, 696729600n], n - 6);
      case 'F':
        return 1152n;
      default:
        return 12n;
    }
  }
  /** SymPy group_name: a description of the group. */
  groupName(): string {
    const n = this.cartanType.rank();
    switch (this.cartanType.series) {
      case 'A':
        return `S${n + 1}: the symmetric group acting on ${n + 1} elements.`;
      case 'B':
      case 'C':
        return `The hyperoctahedral group acting on ${2 * n} elements.`;
      case 'D':
        return `The symmetry group of the ${n}-dimensional demihypercube.`;
      case 'E':
        return `The symmetry group of the ${n}-polytope.`;
      case 'F':
        return 'The symmetry group of the 24-cell, or icositetrachoron.';
      default:
        return 'D6, the dihedral group of order 12, and symmetry group of the hexagon.';
    }
  }
  /** The reflection indices of an element 'r1*r2*...' (SymPy reads every third character). */
  private reflections(weylelt: string): number[] {
    return weylelt.split('').filter((_c, i) => i % 3 === 1).map((c) => Number(c));
  }
  /** SymPy delete_doubles: adjacent equal reflections removed in one pass. */
  deleteDoubles(reflections: readonly number[]): number[] {
    const copy = [...reflections];
    // (SymPy iterates over the list it shortens: after a deletion the next element is skipped)
    for (let i = 0; i < copy.length; i++) if (i < copy.length - 1 && copy[i + 1] === copy[i]) copy.splice(i, 2);
    return copy;
  }
  /** SymPy matrix_form: the matrix of the element 'r1*r2*...' in the standard basis. */
  matrixForm(weylelt: string): Matrix {
    const n = this.cartanType.rank();
    const series = this.cartanType.series;
    const size = series === 'A' ? n + 1 : series === 'G' ? 3 : series === 'E' ? 8 : n;
    let m = eyeWith(size, []);
    for (const a of this.reflections(weylelt)) m = m.mul(this.reflection(a, size));
    return m;
  }
  /** The matrix of the simple reflection r_a. */
  private reflection(a: number, size: number): Matrix {
    const n = this.cartanType.rank();
    switch (this.cartanType.series) {
      case 'A':
        return swap(size, a);
      case 'D':
        return a < n ? swap(size, a) : eyeWith(size, [[n - 2, n - 1, -1], [n - 2, n - 2, 0], [n - 1, n - 2, -1], [n - 1, n - 1, 0]]);
      case 'G':
        return at(G_GENS, a === 1 ? 0 : 1);
      case 'F':
        return at(F_GENS, Math.min(a, 4) - 1);
      case 'E':
        if (a === 1) return E_GEN1;
        if (a === 2) return eyeWith(8, [[0, 0, 0], [0, 1, -1], [1, 0, -1], [1, 1, 0]]);
        return swap(8, a - 2);
      default:
        // B and C
        return a === 1 ? eyeWith(size, [[0, 0, -1]]) : swap(size, a - 1);
    }
  }
  /** SymPy element_order: the order of the element 'r1*r2*...'. */
  elementOrder(weylelt: string): number {
    if (this.cartanType.series === 'G') {
      // a dihedral group: reflections cancel in pairs, an odd product is a reflection
      let m = this.deleteDoubles(this.reflections(weylelt));
      while (this.deleteDoubles(m).length !== m.length) m = this.deleteDoubles(m);
      if (m.length % 2 === 1) return 2;
      if (m.length === 0) return 1;
      const k = m.length / 2;
      return 6 / gcd(k, 6);
    }
    const a = this.matrixForm(weylelt);
    const id = eyeWith(a.rows, []);
    let p = a;
    let order = 1;
    while (!p.equals(id)) {
      // (the first reflection matrix of the E series, taken from SymPy, does not generate a finite group with the
      // others: SymPy loops forever on r1*r2 of E6)
      if (order >= MAX_ORDER) throw new NotImplementedError(`no finite order found for ${weylelt}`);
      p = p.mul(a);
      order++;
    }
    return order;
  }
  /** SymPy coxeter_diagram: the Coxeter diagram as text. */
  coxeterDiagram(): string {
    const n = this.cartanType.rank();
    switch (this.cartanType.series) {
      case 'B':
      case 'C':
        return `${chain(n - 1)}===0\n${labels(1, n)}`;
      case 'F':
        return `0---0===0---0\n${labels(1, 4)}`;
      case 'G':
        return '0≡≡≡0\n1   2';
      default:
        return this.cartanType.dynkinDiagram();
    }
  }
}
