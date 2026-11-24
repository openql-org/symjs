// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/generators.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.generators: the elements of the symmetric,
 * cyclic, alternating and dihedral groups (generators of permutations, like
 * SymPy's Python generators) and the generators of the Rubik's cube groups
 * (rubik, rubik_cube_generators).
 */

import { at } from '../core/guard';
import { permutations } from '../utilities/itertools';
import { Permutation } from './permutations';

const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const rotateLeft = (a: readonly number[], k: number): number[] => [...a.slice(k), ...a.slice(0, k)];

/**
 * Enumerates all permutations of the given degree in lexicographic order of their array forms.
 * @param n - The number of points in the permutation action.
 * @returns An iterator over the permutations in enumeration order.
 * @see SymPy `sympy.combinatorics.generators.symmetric`
 * @example
 * ```ts
 * import { symmetric } from '@symjs/symjs';
 *
 * [...symmetric(3)].map(String); // => [(2), (1 2), (2)(0 1), (0 1 2), (0 2 1), (0 2)]
 * ```
 */
export function* symmetric(n: number): Generator<Permutation, void, undefined> {
  for (const perm of permutations(range(n))) yield new Permutation(perm);
}

/**
 * The n permutations of the cyclic group of order n, the
 * powers of the left rotation of [0, 1, ..., n - 1].
 * @param n - The number of points in the permutation action.
 * @returns An iterator over the permutations in enumeration order.
 * @see SymPy `sympy.combinatorics.generators.cyclic`
 * @example
 * ```ts
 * import { cyclic } from '@symjs/symjs';
 *
 * [...cyclic(3)].map(String); // => [(2), (0 1 2), (0 2 1)]
 * ```
 */
export function* cyclic(n: number): Generator<Permutation, void, undefined> {
  let gen = range(n);
  for (let i = 0; i < n; i++) {
    yield new Permutation(gen);
    gen = rotateLeft(gen, 1);
  }
}

/**
 * The even permutations of the symmetric group, the
 * alternating group of order n!/2.
 * @param n - The number of points in the permutation action.
 * @returns An iterator over the permutations in enumeration order.
 * @see SymPy `sympy.combinatorics.generators.alternating`
 * @example
 * ```ts
 * import { alternating } from '@symjs/symjs';
 *
 * [...alternating(3)].map(String); // => [(2), (0 1 2), (0 2 1)]
 * ```
 */
export function* alternating(n: number): Generator<Permutation, void, undefined> {
  for (const perm of permutations(range(n))) {
    const p = new Permutation(perm);
    if (p.isEven) yield p;
  }
}

/**
 * The 2n permutations of the dihedral group of order 2n,
 * the rotations of an n-gon each followed by its reflection; for n = 1 and
 * n = 2 the groups of order 2 and 4 on 2 and 4 points (as in SymPy).
 * @param n - The number of points in the permutation action.
 * @returns An iterator over the permutations in enumeration order.
 * @see SymPy `sympy.combinatorics.generators.dihedral`
 * @example
 * ```ts
 * import { dihedral } from '@symjs/symjs';
 *
 * [...dihedral(3)].map(String); // => [(2), (0 2), (0 1 2), (1 2), (0 2 1), (2)(0 1)]
 * ```
 */
export function* dihedral(n: number): Generator<Permutation, void, undefined> {
  if (n === 1) {
    yield new Permutation([0, 1]);
    yield new Permutation([1, 0]);
  } else if (n === 2) {
    for (const a of [[0, 1, 2, 3], [1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]]) yield new Permutation(a);
  } else {
    let gen = range(n);
    for (let i = 0; i < n; i++) {
      yield new Permutation(gen);
      yield new Permutation([...gen].reverse());
      gen = rotateLeft(gen, 1);
    }
  }
}

/**
 * Returns the six face turns of a 3×3×3 cube as permutations of its 48 movable facets.
 *
 * @see SymPy `sympy.combinatorics.generators.rubik_cube_generators`
 */
export function rubikCubeGenerators(): Permutation[] {
  const a = [
    [[1, 3, 8, 6], [2, 5, 7, 4], [9, 33, 25, 17], [10, 34, 26, 18], [11, 35, 27, 19]],
    [[9, 11, 16, 14], [10, 13, 15, 12], [1, 17, 41, 40], [4, 20, 44, 37], [6, 22, 46, 35]],
    [[17, 19, 24, 22], [18, 21, 23, 20], [6, 25, 43, 16], [7, 28, 42, 13], [8, 30, 41, 11]],
    [[25, 27, 32, 30], [26, 29, 31, 28], [3, 38, 43, 19], [5, 36, 45, 21], [8, 33, 48, 24]],
    [[33, 35, 40, 38], [34, 37, 39, 36], [3, 9, 46, 32], [2, 12, 47, 29], [1, 14, 48, 27]],
    [[41, 43, 48, 46], [42, 45, 47, 44], [14, 22, 30, 38], [15, 23, 31, 39], [16, 24, 32, 40]],
  ];
  return a.map((x) => new Permutation(x.map((xi) => xi.map((i) => i - 1)), { size: 48 }));
}

type Face = 'U' | 'F' | 'R' | 'B' | 'L' | 'D';

/**
 * Returns generators of the n × n × n cube group as permutations of its 6n² facets, using slice
 * turns about each of the three axes.
 *
 * @see SymPy `sympy.combinatorics.generators.rubik`
 */
export function rubik(n: number): Permutation[] {
  if (!Number.isSafeInteger(n) || n < 2) throw new RangeError('dimension of cube must be > 1');
  const names: Face[] = ['U', 'F', 'R', 'B', 'L', 'D'];
  let count = 0;
  const mk = (): number[][] => Array.from({ length: n }, () => Array.from({ length: n }, () => count++));
  const faces: Record<Face, number[][]> = { U: mk(), F: mk(), R: mk(), B: mk(), L: mk(), D: mk() };
  const getr = (f: Face, i: number): number[] => faces[f].map((row) => at(row, n - i));
  const getl = (f: Face, i: number): number[] => faces[f].map((row) => at(row, i - 1));
  const getu = (f: Face, i: number): number[] => [...at(faces[f], i - 1)];
  const getd = (f: Face, i: number): number[] => [...at(faces[f], n - i)];
  const setr = (f: Face, i: number, s: readonly number[]): void => faces[f].forEach((row, r) => (row[n - i] = at(s, r)));
  const setl = (f: Face, i: number, s: readonly number[]): void => faces[f].forEach((row, r) => (row[i - 1] = at(s, r)));
  const setu = (f: Face, i: number, s: readonly number[]): void => void (faces[f][i - 1] = [...s]);
  const setd = (f: Face, i: number, s: readonly number[]): void => void (faces[f][n - i] = [...s]);
  const cw = (F: Face, times = 1): void => {
    for (let k = 0; k < times; k++) {
      const face = faces[F];
      const rv: number[] = [];
      for (let c = 0; c < n; c++) for (let r = n - 1; r >= 0; r--) rv.push(at(at(face, r), c));
      faces[F] = Array.from({ length: n }, (_, r) => rv.slice(r * n, r * n + n));
    }
  };
  const ccw = (F: Face): void => cw(F, 3);
  const fcw = (iIn: number, times = 1): void => {
    for (let k = 0; k < times; k++) {
      if (iIn === 0) cw('F');
      const i = iIn + 1;
      const temp = getr('L', i);
      setr('L', i, getu('D', i));
      setu('D', i, getl('R', i).reverse());
      setl('R', i, getd('U', i));
      setd('U', i, temp.reverse());
    }
  };
  const fccw = (i: number): void => fcw(i, 3);
  const FCW = (times = 1): void => {
    for (let k = 0; k < times; k++) {
      cw('F');
      ccw('B');
      cw('U');
      const t = faces.U;
      cw('L');
      faces.U = faces.L;
      cw('D');
      faces.L = faces.D;
      cw('R');
      faces.D = faces.R;
      faces.R = t;
    }
  };
  const FCCW = (): void => FCW(3);
  const UCW = (times = 1): void => {
    for (let k = 0; k < times; k++) {
      cw('U');
      ccw('D');
      const t = faces.F;
      faces.F = faces.R;
      faces.R = faces.B;
      faces.B = faces.L;
      faces.L = t;
    }
  };
  const UCCW = (): void => UCW(3);
  const g: Permutation[] = [];
  const perm = (): void => void g.push(new Permutation(names.flatMap((f) => faces[f].flat())));
  for (let i = 0; i < n - 1; i++) {
    fcw(i);
    perm();
    fccw(i);
  }
  UCW();
  for (let i = 0; i < n - 1; i++) {
    fcw(i);
    UCCW();
    perm();
    UCW();
    fccw(i);
  }
  UCCW();
  FCW();
  UCCW();
  FCCW();
  for (let i = 0; i < n - 1; i++) {
    fcw(i);
    FCW();
    UCW();
    FCCW();
    perm();
    FCW();
    UCCW();
    FCCW();
    fccw(i);
  }
  return g;
}
