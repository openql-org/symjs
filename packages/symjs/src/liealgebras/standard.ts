// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The base class of the Cartan types of the simple Lie algebras (SymPy
 * Standard_Cartan of sympy.liealgebras.cartan_type).
 */

import type { Expr } from '../core/nodes';
import { Rational } from '../core/nodes';
import { Matrix } from '../matrices/matrix';

/** Represents one coordinate of a root as an integer, a rational number or a floating-point value. */
export type RootCoordinate = number | Rational;
/** A root: its coordinates in the standard basis. */
export type Root = RootCoordinate[];

/** A root with 1 at i and -1 at j among n coordinates (SymPy basic_root). */
export function basicRoot(n: number, i: number, j: number): Root {
  const root: Root = Array<RootCoordinate>(n).fill(0);
  root[i] = 1;
  root[j] = -1;
  return root;
}

/** Creates a root with `n` coordinates, each equal to `v`. */
export const filled = (n: number, v: RootCoordinate): Root => Array<RootCoordinate>(n).fill(v);

/** The n x n matrix 2*I with the given off-diagonal entries. */
export function cartanFrom(n: number, entries: readonly (readonly [number, number, number])[]): Matrix {
  const m = new Map(entries.map(([i, j, v]) => [`${i},${j}`, v] as const));
  return Matrix.fromFunction(n, n, (i, j): Expr => Rational.of(BigInt(m.get(`${i},${j}`) ?? (i === j ? 2 : 0))));
}

/** The labels 1, ..., n of a Dynkin diagram, separated by three spaces. */
export const labels = (from: number, to: number): string => Array.from({ length: to - from + 1 }, (_x, i) => String(from + i)).join('   ');
/** Draws a chain of `n` Dynkin diagram nodes joined by single bonds. */
export const chain = (n: number): string => Array<string>(n).fill('0').join('---');

/**
 * A Cartan type of series A-G and rank n.
 *
 * @see SymPy `sympy.liealgebras.cartan_type.Standard_Cartan`
 */
export abstract class StandardCartan {
  /**
   * Records the series and rank of a Cartan type.
   *
   * @param series - Letter identifying the Cartan family.
   * @param n - Rank of the Cartan type.
   */
  constructor(
    /**
     * The series letter (A, B, C, D, E, F or G).
     *
     * @see SymPy `sympy.liealgebras.cartan_type.Standard_Cartan.series`
     */
    readonly series: string,
    /**
     * The rank.
     *
     * @see SymPy `sympy.liealgebras.cartan_type.Standard_Cartan.n`
     */
    readonly n: number,
  ) {}
  /**
   * The rank of the Lie algebra.
   *
   * @returns The number of simple roots.
   * @see SymPy `sympy.liealgebras.cartan_type.Standard_Cartan.rank`
   */
  rank(): number {
    return this.n;
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   */
  abstract dimension(): number;
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   */
  abstract simpleRoot(i: number): Root;
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   */
  abstract positiveRoots(): Map<number, Root>;
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   */
  abstract roots(): number;
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   */
  abstract cartanMatrix(): Matrix;
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @returns The dimension of the Lie algebra.
   */
  abstract basis(): RootCoordinate;
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   */
  abstract dynkinDiagram(): string;
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.liealgebras.cartan_type.Standard_Cartan.__str__`
   */
  toString(): string {
    return `${this.series}${this.n}`;
  }
}
