// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The base class of the Cartan types of the simple Lie algebras (SymPy
 * Standard_Cartan of sympy.liealgebras.cartan_type).
 */

import type { Expr } from '../core/nodes';
import { Rational } from '../core/nodes';
import { Matrix } from '../matrices/matrix';

/** A coordinate of a root: an integer, a rational or (in SymPy's E series simple roots) a float. */
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

/** n copies of a coordinate. */
export const filled = (n: number, v: RootCoordinate): Root => Array<RootCoordinate>(n).fill(v);

/** The n x n matrix 2*I with the given off-diagonal entries. */
export function cartanFrom(n: number, entries: readonly (readonly [number, number, number])[]): Matrix {
  const m = new Map(entries.map(([i, j, v]) => [`${i},${j}`, v] as const));
  return Matrix.fromFunction(n, n, (i, j): Expr => Rational.of(BigInt(m.get(`${i},${j}`) ?? (i === j ? 2 : 0))));
}

/** The labels 1, ..., n of a Dynkin diagram, separated by three spaces. */
export const labels = (from: number, to: number): string => Array.from({ length: to - from + 1 }, (_x, i) => String(from + i)).join('   ');
/** n nodes joined by single bonds. */
export const chain = (n: number): string => Array<string>(n).fill('0').join('---');

/** SymPy Standard_Cartan: a Cartan type of series A-G and rank n. */
export abstract class StandardCartan {
  constructor(
    /** The series letter (A, B, C, D, E, F or G). */
    readonly series: string,
    /** The rank. */
    readonly n: number,
  ) {}
  /** SymPy rank: the rank of the Lie algebra. */
  rank(): number {
    return this.n;
  }
  /** SymPy dimension: the dimension of the vector space of the root system. */
  abstract dimension(): number;
  /** SymPy simple_root(i): the i-th simple root (1-based). */
  abstract simpleRoot(i: number): Root;
  /** SymPy positive_roots: the positive roots, numbered from 1. */
  abstract positiveRoots(): Map<number, Root>;
  /** SymPy roots: the number of roots. */
  abstract roots(): number;
  /** SymPy cartan_matrix: the Cartan matrix. */
  abstract cartanMatrix(): Matrix;
  /** SymPy basis: the number of independent generators of the Lie algebra. */
  abstract basis(): RootCoordinate;
  /** SymPy dynkin_diagram: the Dynkin diagram as text. */
  abstract dynkinDiagram(): string;
  /** SymPy str: the series and rank, e.g. A3. */
  toString(): string {
    return `${this.series}${this.n}`;
  }
}
