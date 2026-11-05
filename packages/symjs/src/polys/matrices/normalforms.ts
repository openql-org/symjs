// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/normalforms.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The Smith and Hermite normal forms of a DomainMatrix (SymPy
 * smith_normal_form, smith_normal_decomp, invariant_factors,
 * hermite_normal_form).
 */

import { DomainError } from '../../core/errors';
import { at } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { Rational } from '../../core/nodes';
import { symmetricResidue } from '../../ntheory/modular';
import type { Domain } from '../domains';
import { QQ, ZZ } from '../domains';
import type { Shape } from './ddm';
import { DDM } from './ddm';
import { canonicalUnit, div, exquo, gcd, gcdex, isPID, isZZ, rat } from './domainops';
import { DomainMatrix } from './domainmatrix';
import { DMDomainError, DMShapeError } from './exceptions';

/** SymPy smith_normal_form: the diagonal matrix of the invariant factors. */
export function smithNormalForm(m: DomainMatrix): DomainMatrix {
  return DomainMatrix.diag(invariantFactors(m), m.domain, m.shape);
}

/** SymPy is_smith_normal_form: diagonal with each diagonal element dividing the next. */
export function isSmithNormalForm(mIn: DomainMatrix): boolean {
  const K = mIn.domain;
  const [rows, cols] = mIn.shape;
  const m = mIn.toList();
  for (let i = 0; i < rows; i++) for (let j = 0; j < cols; j++) if (i !== j && !K.isZero(at(at(m, i), j))) return false;
  for (let i = 1; i < Math.min(rows, cols); i++) {
    const prev = at(at(m, i - 1), i - 1);
    const cur = at(at(m, i), i);
    if (K.isZero(prev)) {
      if (!K.isZero(cur)) return false;
    } else if (!K.isZero(div(K, cur, prev)[1])) return false;
  }
  return true;
}

/** Columns i and j replaced by a*col_i + b*col_j and c*col_i + d*col_j (in place). */
function addColumns(m: Expr[][], i: number, j: number, a: Expr, b: Expr, c: Expr, d: Expr, K: Domain): void {
  for (const row of m) {
    const e = at(row, i);
    row[i] = K.add(K.mul(a, e), K.mul(b, at(row, j)));
    row[j] = K.add(K.mul(c, e), K.mul(d, at(row, j)));
  }
}

/** Rows i and j replaced by a*row_i + b*row_j and c*row_i + d*row_j (in place). */
function addRows(m: Expr[][], i: number, j: number, a: Expr, b: Expr, c: Expr, d: Expr, K: Domain): void {
  const [ri, rj] = [at(m, i), at(m, j)];
  ri.forEach((e, k) => {
    ri[k] = K.add(K.mul(a, e), K.mul(b, at(rj, k)));
    rj[k] = K.add(K.mul(c, e), K.mul(d, at(rj, k)));
  });
}

/** SymPy invariant_factors: the invariant factors of a matrix over a principal ideal domain. */
export function invariantFactors(m: DomainMatrix): Expr[] {
  return smithNormalDecomp0(m.toList(), m.domain, m.shape, false)[0];
}

/** SymPy smith_normal_decomp: [smf, s, t] with smf = s*m*t and s, t invertible. */
export function smithNormalDecomp(m: DomainMatrix): [DomainMatrix, DomainMatrix, DomainMatrix] {
  const K = m.domain;
  const [rows, cols] = m.shape;
  const [invs, s, t] = smithNormalDecomp0(m.toList(), K, m.shape, true);
  return [DomainMatrix.diag(invs, K, m.shape).toDense(), new DomainMatrix(s, [rows, rows], K), new DomainMatrix(t, [cols, cols], K)];
}

const eyeRows = (n: number, K: Domain): Expr[][] => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (i === j ? K.one : K.zero)));

/** SymPy _smith_normal_decomp: [invariant factors, s, t] (s and t only with full). */
function smithNormalDecomp0(m: Expr[][], K: Domain, shape: Shape, full: boolean): [Expr[], Expr[][], Expr[][]] {
  if (!isPID(K)) throw new DomainError(`The matrix entries must be over a principal ideal domain, but got ${K.toString()}`);
  const [rows, cols] = shape;
  let s = eyeRows(rows, K);
  let t = eyeRows(cols, K);
  if (rows === 0 || cols === 0) return [[], s, t];
  const [zero, one] = [K.zero, K.one];
  const isZ = (e: Expr): boolean => K.isZero(e);

  const clearColumn = (): void => {
    let pivot = at(at(m, 0), 0);
    for (let j = 1; j < rows; j++) {
      const mj0 = at(at(m, j), 0);
      if (isZ(mj0)) continue;
      const [d, r] = div(K, mj0, pivot);
      if (isZ(r)) {
        addRows(m, 0, j, one, zero, K.neg(d), one, K);
        if (full) addRows(s, 0, j, one, zero, K.neg(d), one, K);
      } else {
        const [a, b, g] = gcdex(K, pivot, mj0);
        const [d0, dj] = [exquo(K, mj0, g), exquo(K, pivot, g)];
        addRows(m, 0, j, a, b, d0, K.neg(dj), K);
        if (full) addRows(s, 0, j, a, b, d0, K.neg(dj), K);
        pivot = g;
      }
    }
  };
  const clearRow = (): void => {
    let pivot = at(at(m, 0), 0);
    for (let j = 1; j < cols; j++) {
      const m0j = at(at(m, 0), j);
      if (isZ(m0j)) continue;
      const [d, r] = div(K, m0j, pivot);
      if (isZ(r)) {
        addColumns(m, 0, j, one, zero, K.neg(d), one, K);
        if (full) addColumns(t, 0, j, one, zero, K.neg(d), one, K);
      } else {
        const [a, b, g] = gcdex(K, pivot, m0j);
        const [d0, dj] = [exquo(K, m0j, g), exquo(K, pivot, g)];
        addColumns(m, 0, j, a, b, d0, K.neg(dj), K);
        if (full) addColumns(t, 0, j, a, b, d0, K.neg(dj), K);
        pivot = g;
      }
    }
  };

  const swapRows = (x: Expr[][], i: number): void => {
    [x[0], x[i]] = [at(x, i), at(x, 0)];
  };
  const swapCols = (x: Expr[][], i: number): void => {
    for (const row of x) [row[0], row[i]] = [at(row, i), at(row, 0)];
  };
  // a nonzero element to the top left corner (SymPy compares the index with zero)
  const ind = Array.from({ length: rows }, (_, i) => i).filter((i) => !isZ(at(at(m, i), 0)));
  if (ind.length && at(ind, 0) !== 0) {
    swapRows(m, at(ind, 0));
    if (full) swapRows(s, at(ind, 0));
  } else if (!ind.length) {
    const indc = Array.from({ length: cols }, (_, j) => j).filter((j) => !isZ(at(at(m, 0), j)));
    if (indc.length && at(indc, 0) !== 0) {
      swapCols(m, at(indc, 0));
      if (full) swapCols(t, at(indc, 0));
    }
  }
  while (at(m, 0).slice(1).some((e) => !isZ(e)) || m.slice(1).some((row) => !isZ(at(row, 0)))) {
    clearColumn();
    clearRow();
  }
  const m00 = at(at(m, 0), 0);
  if (!isZ(m00)) {
    const c = K.isField ? K.quo(one, m00) : canonicalUnit(K, m00);
    if (!K.isOne(c)) {
      at(m, 0)[0] = K.mul(m00, c);
      if (full) s[0] = at(s, 0).map((e) => K.mul(e, c));
    }
  }
  let invs: Expr[];
  if (rows === 1 || cols === 1) invs = [];
  else {
    const lowerRight = m.slice(1).map((r) => r.slice(1));
    const [inv1, sSmall, tSmall] = smithNormalDecomp0(lowerRight, K, [rows - 1, cols - 1], full);
    invs = inv1;
    if (full) {
      const s2 = [[one, ...Array.from({ length: rows - 1 }, () => zero)], ...sSmall.map((row) => [zero, ...row])];
      const t2 = [[one, ...Array.from({ length: cols - 1 }, () => zero)], ...tSmall.map((row) => [zero, ...row])];
      const dm = (x: Expr[][]): DDM => new DDM(x, [x.length, at(x, 0).length], K);
      s = dm(s2).matmul(dm(s)).toList();
      t = dm(t).matmul(dm(t2)).toList();
    }
  }
  const top = at(at(m, 0), 0);
  let result: Expr[];
  if (!isZ(top)) {
    result = [top, ...invs];
    for (let i = 0; i < result.length - 1; i++) {
      const [a, b] = [at(result, i), at(result, i + 1)];
      if (isZ(b) || isZ(div(K, b, a)[1])) break;
      let x = zero;
      let y = zero;
      let d: Expr;
      if (full) [x, y, d] = gcdex(K, a, b);
      else d = gcd(K, a, b);
      const alpha = div(K, a, d)[0];
      if (full) {
        const beta = div(K, b, d)[0];
        addRows(s, i, i + 1, one, zero, x, one, K);
        addColumns(t, i, i + 1, one, y, zero, one, K);
        addRows(s, i, i + 1, one, K.neg(alpha), zero, one, K);
        addColumns(t, i, i + 1, one, zero, K.neg(beta), one, K);
        addRows(s, i, i + 1, zero, one, K.neg(one), zero, K);
      }
      result[i + 1] = K.mul(b, alpha);
      result[i] = d;
    }
  } else {
    if (full) {
      if (rows > 1) s = [...s.slice(1), at(s, 0)];
      if (cols > 1) t = t.map((row) => [...row.slice(1), at(row, 0)]);
    }
    result = [...invs, top];
  }
  return [result, s, t];
}

/** SymPy _gcdex: ZZ.gcdex with x = sign(a), y = 0 when a divides b. */
function gcdexHnf(a: bigint, b: bigint): [bigint, bigint, bigint] {
  const [x, y, g] = gcdex(ZZ, Rational.of(a), Rational.of(b));
  if (a !== 0n && b % a === 0n) return [a < 0n ? -1n : 1n, 0n, rat(g).p];
  return [rat(x).p, rat(y).p, rat(g).p];
}

/** Python floor division of integers. */
const fdiv = (a: bigint, b: bigint): bigint => {
  const q = a / b;
  return (a % b !== 0n && a < 0n !== b < 0n) ? q - 1n : q;
};
/** Python modulo of integers. */
const fmod = (a: bigint, b: bigint): bigint => a - b * fdiv(a, b);

function addColumnsInt(m: bigint[][], i: number, j: number, a: bigint, b: bigint, c: bigint, d: bigint): void {
  for (const row of m) {
    const e = at(row, i);
    row[i] = a * e + b * at(row, j);
    row[j] = c * e + d * at(row, j);
  }
}

const toInts = (A: DomainMatrix): bigint[][] => A.toList().map((row) => row.map((e) => rat(e).p));
const fromInts = (A: readonly (readonly bigint[])[], shape: Shape): DDM =>
  new DDM(
    A.map((row) => row.map((e) => Rational.of(e))),
    shape,
    ZZ,
  );

/** SymPy _hermite_normal_form: the HNF by column operations (Cohen, Algorithm 2.4.5). */
function hermiteNormalForm0(Ain: DomainMatrix): DomainMatrix {
  const [m, n] = Ain.shape;
  const A = toInts(Ain);
  let k = n;
  for (let i = m - 1; i >= 0; i--) {
    if (k === 0) break;
    k--;
    const Ai = at(A, i);
    for (let j = k - 1; j >= 0; j--) {
      if (at(Ai, j) !== 0n) {
        const [u, v, d] = gcdexHnf(at(Ai, k), at(Ai, j));
        const [r, s] = [fdiv(at(Ai, k), d), fdiv(at(Ai, j), d)];
        addColumnsInt(A, k, j, u, v, -s, r);
      }
    }
    let b = at(Ai, k);
    if (b < 0n) {
      addColumnsInt(A, k, k, -1n, 0n, -1n, 0n);
      b = -b;
    }
    if (b === 0n) k++;
    else {
      for (let j = k + 1; j < n; j++) {
        const q = fdiv(at(Ai, j), b);
        addColumnsInt(A, j, k, 1n, -q, 0n, 1n);
      }
    }
  }
  return new DomainMatrix(fromInts(A, [m, n])).extractSlice([null, null], [k, null]);
}

/** SymPy _hermite_normal_form_modulo_D: the HNF of a full-rank matrix modulo a multiple D of its determinant (Cohen, Algorithm 2.4.8). */
function hermiteNormalFormModuloD(Ain: DomainMatrix, D: bigint): DomainMatrix {
  if (D < 1n) throw new DMDomainError('Modulus D must be positive element of domain ZZ.');
  const [m, n] = Ain.shape;
  if (n < m) throw new DMShapeError('Matrix must have at least as many columns as rows.');
  const addColumnsModR = (M: bigint[][], R: bigint, i: number, j: number, a: bigint, b: bigint, c: bigint, d: bigint): void => {
    for (const row of M) {
      const e = at(row, i);
      row[i] = symmetricResidue(fmod(a * e + b * at(row, j), R), R);
      row[j] = symmetricResidue(fmod(c * e + d * at(row, j), R), R);
    }
  };
  const W: bigint[][] = Array.from({ length: m }, () => Array.from({ length: m }, () => 0n));
  const A = toInts(Ain);
  let k = n;
  let R = D;
  for (let i = m - 1; i >= 0; i--) {
    k--;
    const Ai = at(A, i);
    for (let j = k - 1; j >= 0; j--) {
      if (at(Ai, j) !== 0n) {
        const [u, v, d] = gcdexHnf(at(Ai, k), at(Ai, j));
        const [r, s] = [fdiv(at(Ai, k), d), fdiv(at(Ai, j), d)];
        addColumnsModR(A, R, k, j, u, v, -s, r);
      }
    }
    let b = at(Ai, k);
    if (b === 0n) Ai[k] = b = R;
    const [u, , d] = gcdexHnf(b, R);
    for (let ii = 0; ii < m; ii++) at(W, ii)[i] = fmod(u * at(at(A, ii), k), R);
    const Wi = at(W, i);
    if (at(Wi, i) === 0n) Wi[i] = R;
    for (let j = i + 1; j < m; j++) {
      const q = fdiv(at(Wi, j), at(Wi, i));
      addColumnsInt(W, j, i, 1n, -q, 0n, 1n);
    }
    R = fdiv(R, d);
  }
  return new DomainMatrix(fromInts(W, [m, m]));
}

/**
 * SymPy hermite_normal_form: the Hermite normal form of a matrix over ZZ;
 * with D (a positive multiple of the determinant of a full-rank matrix) the
 * computation is done modulo D.
 */
export function hermiteNormalForm(A: DomainMatrix, opts: { D?: bigint | number; checkRank?: boolean } = {}): DomainMatrix {
  if (!isZZ(A.domain)) throw new DMDomainError('Matrix must be over domain ZZ.');
  if (opts.D !== undefined && (!opts.checkRank || A.convertTo(QQ).rank() === A.shape[0])) return hermiteNormalFormModuloD(A, BigInt(opts.D));
  return hermiteNormalForm0(A);
}
