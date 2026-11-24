// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file More of SymPy's matrix methods: Berkowitz minors, Householder
 * bidiagonalization and Hessenberg form, singular value decomposition,
 * LU variants, LLL reduction, elementary operations, permutations by
 * swaps, block decompositions, the dual tensor and helpers for indexing
 * and printing.
 */

import { Random } from '../ntheory/random';
import { MatrixError, SympifyError } from '../core/errors';
import { at, defined, last } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Expr, Rational, S, Sym, type Assumptions } from '../core/nodes';
import { add, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { abs } from '../functions/elementary/elementary';
import { sign } from '../functions/special/special';
import { str } from '../printing/str';
import { ExprMap } from '../core/exprmap';
import { Matrix } from './matrix';
import { BlockDiagMatrix, BlockMatrix } from './expressions/blockmatrix';
import { PermutationMatrix, PermutationNode } from './expressions/permutation';
import { connectedComponents, diagonalize, jordanBlock, jordanForm, norm, qrDecomposition, stronglyConnectedComponents } from './linalg';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;
const rows = (m: Matrix): Expr[][] => m.toArray();
const range = (a: number, b: number): number[] => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
/** The entry (i, j) of a row-major grid; throws when out of range. */
const get2 = <T>(g: readonly (readonly T[])[], i: number, j: number): T => at(at(g, i), j);

// ---------------------------------------------------------------------------
// Berkowitz
// ---------------------------------------------------------------------------

/**
 * Computes the characteristic polynomial coefficients of successive leading principal submatrices.
 * @param M - The input matrix.
 * @returns The characteristic polynomial coefficients of successive leading principal submatrices.
 * @throws RangeError when the matrix is not square.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.berkowitz`
 */
export function berkowitz(M: Matrix): Expr[][] {
  const berk: Expr[][] = [[S.One]];
  if (M.rows === 0 || M.cols === 0) return berk;
  if (!M.isSquare) throw new RangeError('berkowitz: matrix must be square');
  const N = M.rows;
  let A = M;
  const transforms: Matrix[] = [];
  for (let n = N; n > 1; n--) {
    const k = n - 1;
    const R = A.slice([k], range(0, k)).scale(-1);
    const C = A.slice(range(0, k), [k]);
    const a = mul(-1, A.get(k, k));
    A = A.slice(range(0, k), range(0, k));
    const items: Matrix[] = [C];
    let item = C;
    for (let i = 0; i < n - 2; i++) {
      item = A.mul(item);
      items.push(item);
    }
    const vals: Expr[] = [S.One, a, ...items.map((B) => R.mul(B).get(0, 0))];
    const T = Matrix.fromFunction(n + 1, n, (i, j) => (i >= j && i - j < vals.length ? at(vals, i - j) : 0));
    transforms[k - 1] = T;
  }
  let poly = Matrix.of([[S.One], [mul(-1, A.get(0, 0))]]);
  const polys: Matrix[] = [poly];
  for (const T of transforms) {
    poly = T.mul(poly);
    polys.push(poly);
  }
  return [...berk, ...polys.map((p) => p.data.map((e) => e))];
}

/**
 * The eigenvalues with their multiplicities.
 * @param M - The input matrix.
 * @returns A map from each eigenvalue to its algebraic multiplicity.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.berkowitz_eigenvals`
 */
export function berkowitzEigenvals(M: Matrix): ExprMap<number> {
  const out = new ExprMap<number>();
  for (const v of M.eigenvals()) out.set(v, (out.get(v) ?? 0) + 1);
  return out;
}

/**
 * Computes the determinants of successive leading principal submatrices.
 * @param M - The input matrix.
 * @returns The determinants of successive leading principal submatrices.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.berkowitz_minors`
 */
export function berkowitzMinors(M: Matrix): Expr[] {
  let sgn: Expr = S.One;
  const out: Expr[] = [];
  for (const p of berkowitz(M)) {
    out.push(mul(sgn, last(p)));
    sgn = mul(-1, sgn);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Householder reflections
// ---------------------------------------------------------------------------

/** SymPy _householder_vector: v (v[0] = 1) and beta with (I - beta v v^H) x = multiple of e1. */
function householderVector(x: Matrix): [Matrix, Expr] {
  const x0 = x.get(0, 0);
  // x0 / |x0| (SymPy's NaN for x0 = 0 fails the comparison below: any unit q works, take 1)
  const q = isZeroExpr(x0) ? S.One : mul(x0, pow(abs(x0), -1));
  const nx = norm(x);
  const vPlus = x.with(0, 0, add(x0, mul(q, nx)));
  const vMinus = x.with(0, 0, sub(x0, mul(q, nx)));
  const tail = x.slice(range(1, x.rows), [0]);
  if (tail.rows === 0 || isZeroExpr(norm(tail))) return [x.with(0, 0, 1), S.Zero];
  let v = norm(vPlus).toNumber() <= norm(vMinus).toNumber() ? vPlus : vMinus;
  v = v.scale(pow(v.get(0, 0), -1));
  return [v, mul(2, pow(pow(norm(v), 2), -1))];
}

/** Replace the block of A starting at (r, c) by B. */
function setBlock(A: Matrix, r: number, c: number, B: Matrix): Matrix {
  return Matrix.fromFunction(A.rows, A.cols, (i, j) => (i >= r && j >= c && i - r < B.rows && j - c < B.cols ? B.get(i - r, j - c) : A.get(i, j)));
}

function bidiagHouseholder(M: Matrix, withUV: boolean): [Matrix, Matrix, Matrix] {
  const m = M.rows;
  const n = M.cols;
  let A = M;
  let U = Matrix.eye(m);
  let V = Matrix.eye(n);
  for (let i = 0; i < Math.min(m, n); i++) {
    let [v, bet] = householderVector(A.slice(range(i, m), [i]));
    let hh = Matrix.eye(m - i).sub(v.mul(v.H).scale(bet));
    A = setBlock(A, i, i, hh.mul(A.slice(range(i, m), range(i, n))));
    if (withUV) U = U.mul(setBlock(Matrix.eye(m), i, i, hh));
    if (i + 1 <= n - 2) {
      [v, bet] = householderVector(A.slice([i], range(i + 1, n)).T);
      hh = Matrix.eye(n - i - 1).sub(v.mul(v.H).scale(bet));
      A = setBlock(A, i, i + 1, A.slice(range(i, m), range(i + 1, n)).mul(hh));
      if (withUV) V = setBlock(Matrix.eye(n), i + 1, i + 1, hh).mul(V);
    }
  }
  return [U, A, V];
}

/**
 * The bidiagonal form by Householder reflections.
 * @param M - The input matrix.
 * @param upper - Whether to construct the upper bidiagonal form.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.bidiagonalize`
 */
export function bidiagonalize(M: Matrix, upper = true): Matrix {
  return upper ? bidiagHouseholder(M, false)[1] : bidiagHouseholder(M.H, false)[1].H;
}

/**
 * Reduces the matrix to bidiagonal form and computes the left and right transformations.
 * @param M - The input matrix.
 * @param upper - Whether to construct the upper bidiagonal form.
 * @returns The factors `[U, B, Vᴴ]` whose product is the input.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.bidiagonal_decomposition`
 */
export function bidiagonalDecomposition(M: Matrix, upper = true): [Matrix, Matrix, Matrix] {
  if (upper) return bidiagHouseholder(M, true);
  const [U, B, V] = bidiagHouseholder(M.H, true);
  return [V.H, B.H, U.H];
}

/**
 * Reduces the matrix to upper Hessenberg form by a unitary similarity transformation.
 * @param A - The input matrix.
 * @returns The factors `[H, P]` satisfying `A = P*H*Pᴴ`.
 * @throws RangeError when the matrix is not square.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.upper_hessenberg_decomposition`
 * @example
 * ```ts
 * import { Matrix, upperHessenbergDecomposition } from '@symjs/symjs';
 *
 * const A = Matrix.of([[1, 2], [3, 4]]);
 * const [H, P] = upperHessenbergDecomposition(A);
 * P.mul(H).mul(P.H).equals(A); // => True
 * ```
 */
export function upperHessenbergDecomposition(A: Matrix): [Matrix, Matrix] {
  if (!A.isSquare) throw new RangeError('Matrix must be square.');
  const n = A.cols;
  let P = Matrix.eye(n);
  let H = A;
  for (let j = 0; j < n - 2; j++) {
    let u = H.slice(range(j + 1, n), [j]);
    if (u.slice(range(1, u.rows), [0]).isZero) continue;
    const s = sign(u.get(0, 0));
    u = u.with(0, 0, isZeroExpr(s) ? add(u.get(0, 0), norm(u)) : add(u.get(0, 0), mul(s, norm(u))));
    const v = u.scale(pow(norm(u), -1));
    const lower = H.slice(range(j + 1, n), range(0, n));
    H = setBlock(H, j + 1, 0, lower.sub(v.scale(2).mul(v.H.mul(lower))));
    const right = H.slice(range(0, n), range(j + 1, n));
    H = setBlock(H, 0, j + 1, right.sub(right.mul(v.scale(2)).mul(v.H)));
    const pr = P.slice(range(0, n), range(j + 1, n));
    P = setBlock(P, 0, j + 1, pr.sub(pr.mul(v.scale(2)).mul(v.H)));
  }
  return [H, P];
}

/**
 * Factors the matrix using its nonzero singular values and corresponding singular vectors.
 * @param A - The input matrix.
 * @returns The factors `[U, S, V]` satisfying `A = U*S*Vᴴ`.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.singular_value_decomposition`
 * @example
 * ```ts
 * import { Matrix, singularValueDecomposition } from '@symjs/symjs';
 * singularValueDecomposition(Matrix.of([[1, 2], [2, 1]]))[1].toArray(); // => [[1, 0], [0, 3]]
 * ```
 */
export function singularValueDecomposition(A: Matrix): [Matrix, Matrix, Matrix] {
  const AH = A.H;
  const tall = A.rows >= A.cols;
  const [W, D] = diagonalize(tall ? AH.mul(A) : A.mul(AH));
  const ranked = range(0, D.rows).filter((i) => !isZeroExpr(D.get(i, i)));
  const Wr = W.slice(range(0, W.rows), ranked);
  const Sg = Matrix.diag(...ranked.map((i) => sqrt(D.get(i, i))));
  const [Q] = qrDecomposition(Wr);
  if (tall) return [A.mul(Q).mul(Sg.inv()), Sg, Q];
  return [Q, Sg, AH.mul(Q).mul(Sg.inv())];
}

// ---------------------------------------------------------------------------
// LU variants
// ---------------------------------------------------------------------------

/**
 * L (below the diagonal, unit
 * diagonal implied) and U in one matrix, and the row swaps.
 * @param M - The input matrix.
 * @param rankcheck - Whether to reject a rank deficiency.
 * @returns The packed lower and upper factors and the row swaps used during pivoting.
 * @throws RangeError when the matrix is rank deficient.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LUdecomposition_Simple`
 */
export function luDecompositionSimple(M: Matrix, rankcheck = false): [Matrix, [number, number][]] {
  if (M.rows === 0 || M.cols === 0) return [Matrix.zeros(M.rows, M.cols), []];
  const lu = rows(M);
  const swaps: [number, number][] = [];
  let pivotCol = 0;
  for (let pivotRow = 0; pivotRow < M.rows - 1; pivotRow++) {
    let cand = -1;
    while (pivotCol !== M.cols) {
      cand = range(pivotRow, M.rows).find((r) => !isZeroExpr(get2(lu, r, pivotCol))) ?? -1;
      if (cand >= 0) break;
      pivotCol++;
    }
    if (rankcheck && pivotCol !== pivotRow) throw new RangeError('Matrix is rank deficient');
    if (cand < 0) return [Matrix.of(lu), swaps];
    if (cand !== pivotRow) {
      swaps.push([pivotRow, cand]);
      const rowP = at(lu, pivotRow);
      const rowC = at(lu, cand);
      for (const c of [...range(0, pivotRow), ...range(pivotCol, M.cols)]) {
        const t = at(rowP, c);
        rowP[c] = at(rowC, c);
        rowC[c] = t;
      }
    }
    const pivRow = at(lu, pivotRow);
    const pivInv = pow(at(pivRow, pivotCol), -1);
    for (let r = pivotRow + 1; r < M.rows; r++) {
      const lr = at(lu, r);
      const f = mul(at(lr, pivotCol), pivInv);
      lr[pivotRow] = f;
      for (let c = pivotCol + 1; c < M.cols; c++) lr[c] = sub(at(lr, c), mul(f, at(pivRow, c)));
    }
    if (pivotRow !== pivotCol) for (let r = pivotRow + 1; r < M.rows; r++) at(lu, r)[pivotCol] = S.Zero;
    pivotCol++;
    if (pivotCol === M.cols) break;
  }
  const lastPivot = Math.min(M.rows, M.cols) - 1;
  if (rankcheck && isZeroExpr(get2(lu, lastPivot, lastPivot))) throw new RangeError('Matrix is rank deficient');
  return [Matrix.of(lu), swaps];
}

/**
 * Computes the fraction-free LU decomposition with a row permutation and a diagonal denominator.
 * @param M - The input matrix.
 * @returns The matrices `[P, L, D, U]` satisfying `P*A = L*D⁻¹*U`.
 * @throws MatrixError when the matrix is rank deficient.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LUdecompositionFF`
 */
export function luDecompositionFF(M: Matrix): [Matrix, Matrix, Matrix, Matrix] {
  const n = M.rows;
  const m = M.cols;
  const U = rows(M);
  const L = rows(Matrix.eye(n));
  const P = rows(Matrix.eye(n));
  const DD = rows(Matrix.zeros(n, n));
  let oldpivot: Expr = S.One;
  for (let k = 0; k < n - 1; k++) {
    if (isZeroExpr(get2(U, k, k))) {
      const kp = range(k + 1, n).find((r) => !isZeroExpr(get2(U, r, k)));
      if (kp === undefined) throw new MatrixError('Matrix is not full rank');
      const Uk = at(U, k);
      const Ukp = at(U, kp);
      for (let c = k; c < m; c++) [Uk[c], Ukp[c]] = [at(Ukp, c), at(Uk, c)];
      const Lk = at(L, k);
      const Lkp = at(L, kp);
      for (let c = 0; c < k; c++) [Lk[c], Lkp[c]] = [at(Lkp, c), at(Lk, c)];
      [P[k], P[kp]] = [at(P, kp), at(P, k)];
    }
    const Uk = at(U, k);
    const Ukk = at(Uk, k);
    at(L, k)[k] = Ukk;
    at(DD, k)[k] = mul(oldpivot, Ukk);
    const oldInv = pow(oldpivot, -1);
    for (let i = k + 1; i < n; i++) {
      const Ui = at(U, i);
      const Uik = at(Ui, k);
      at(L, i)[k] = Uik;
      for (let j = k + 1; j < m; j++) Ui[j] = mul(sub(mul(Ukk, at(Ui, j)), mul(at(Uk, j), Uik)), oldInv);
      Ui[k] = S.Zero;
    }
    oldpivot = Ukk;
  }
  at(DD, n - 1)[n - 1] = oldpivot;
  return [Matrix.of(P), Matrix.of(L), Matrix.of(DD), Matrix.of(U)];
}

// ---------------------------------------------------------------------------
// LLL
// ---------------------------------------------------------------------------

type Q = [bigint, bigint];
/** p/q in lowest terms; q > 0 (the denominators are products of positive ones, and qdiv divides by squared norms only). */
const qn = (p: bigint, q = 1n): Q => {
  const g = gcdBig(p < 0n ? -p : p, q);
  return g > 1n ? [p / g, q / g] : [p, q];
};
function gcdBig(aIn: bigint, bIn: bigint): bigint {
  let a = aIn;
  let b = bIn;
  while (b) [a, b] = [b, a % b];
  // b starts as a denominator (positive), so a >= 1
  return a;
}
const qadd = (a: Q, b: Q): Q => qn(a[0] * b[1] + b[0] * a[1], a[1] * b[1]);
const qsub = (a: Q, b: Q): Q => qn(a[0] * b[1] - b[0] * a[1], a[1] * b[1]);
const qmul = (a: Q, b: Q): Q => qn(a[0] * b[0], a[1] * b[1]);
const qdiv = (a: Q, b: Q): Q => {
  if (b[0] === 0n) throw new MatrixError('input matrix contains linearly dependent rows');
  return qn(a[0] * b[1], a[1] * b[0]);
};
const qcmp = (a: Q, b: Q): number => {
  const d = a[0] * b[1] - b[0] * a[1];
  return d > 0n ? 1 : d < 0n ? -1 : 0;
};
/** floor(x + 1/2) */
const closestInteger = (x: Q): bigint => {
  const num = 2n * x[0] + x[1];
  const den = 2n * x[1];
  const q = num / den;
  return num % den !== 0n && num < 0n ? q - 1n : q;
};

function lllCore(M: Matrix, delta: Q, withT: boolean): [Matrix, Matrix | undefined] {
  const m = M.rows;
  const n = M.cols;
  if (m > n) throw new RangeError('input matrix must have shape (m, n) with m <= n');
  const y: bigint[][] = rows(M).map((r) =>
    r.map((e) => {
      if (!(e instanceof Rational && e.q === 1n)) throw new TypeError('input matrix domain must be ZZ');
      return e.p;
    }),
  );
  const T: bigint[][] = range(0, m).map((i) => range(0, m).map((j) => (i === j ? 1n : 0n)));
  const ystar: Q[][] = range(0, m).map(() => range(0, n).map(() => [0n, 1n] as Q));
  const mu: Q[][] = range(0, m).map(() => range(0, m).map(() => [0n, 1n] as Q));
  const g: Q[] = range(0, m).map(() => [0n, 1n] as Q);
  const half: Q = [1n, 2n];
  const qabs = (a: Q): Q => [a[0] < 0n ? -a[0] : a[0], a[1]];
  for (let i = 0; i < m; i++) {
    const yi = at(y, i);
    const mui = at(mu, i);
    let ys = yi.map((v) => [v, 1n] as Q);
    for (let j = 0; j < i; j++) {
      const ysj = at(ystar, j);
      let dot: Q = [0n, 1n];
      for (let z = 0; z < n; z++) dot = qadd(dot, qmul([at(yi, z), 1n], at(ysj, z)));
      const muij = qdiv(dot, at(g, j));
      mui[j] = muij;
      ys = ys.map((v, z) => qsub(v, qmul(muij, at(ysj, z))));
    }
    ystar[i] = ys;
    g[i] = ys.reduce<Q>((s, v) => qadd(s, qmul(v, v)), [0n, 1n]);
  }
  const lovasz = (k: number) => {
    const muk = get2(mu, k, k - 1);
    return qcmp(at(g, k), qmul(qsub(delta, qmul(muk, muk)), at(g, k - 1))) >= 0;
  };
  const small = (k: number, j: number) => qcmp(qabs(get2(mu, k, j)), half) <= 0;
  const reduce = (k: number, j: number) => {
    const muk = at(mu, k);
    const muj = at(mu, j);
    const r = closestInteger(at(muk, j));
    const yj = at(y, j);
    y[k] = at(y, k).map((v, z) => v - r * at(yj, z));
    for (let z = 0; z < j; z++) muk[z] = qsub(at(muk, z), qmul([r, 1n], at(muj, z)));
    muk[j] = qsub(at(muk, j), [r, 1n]);
    const Tj = at(T, j);
    T[k] = at(T, k).map((v, z) => v - r * at(Tj, z));
  };
  let k = 1;
  while (k < m) {
    if (!small(k, k - 1)) reduce(k, k - 1);
    if (lovasz(k)) {
      for (let l = k - 2; l >= 0; l--) if (!small(k, l)) reduce(k, l);
      k++;
    } else {
      const muk = at(mu, k);
      const muk1 = at(mu, k - 1);
      const nu = at(muk, k - 1);
      const gk1 = at(g, k - 1);
      const alpha = qadd(at(g, k), qmul(qmul(nu, nu), gk1));
      const beta = qdiv(gk1, alpha);
      muk[k - 1] = qmul(nu, beta);
      g[k] = qmul(at(g, k), beta);
      g[k - 1] = alpha;
      [y[k], y[k - 1]] = [at(y, k - 1), at(y, k)];
      for (let z = 0; z < k - 1; z++) [muk[z], muk1[z]] = [at(muk1, z), at(muk, z)];
      for (let i = k + 1; i < m; i++) {
        const mui = at(mu, i);
        const xi = at(mui, k);
        const muik = qsub(at(mui, k - 1), qmul(nu, xi));
        mui[k] = muik;
        mui[k - 1] = qadd(qmul(at(muk, k - 1), muik), xi);
      }
      [T[k], T[k - 1]] = [at(T, k - 1), at(T, k)];
      k = Math.max(k - 1, 1);
    }
  }
  return [Matrix.of(y), withT ? Matrix.of(T) : undefined];
}

const deltaQ = (d: ExprLike): Q => {
  const e = sympify(d);
  if (!(e instanceof Rational)) throw new TypeError('delta must be a rational number');
  if (e.p * 4n <= e.q || e.p >= e.q) throw new RangeError('delta must lie in range (0.25, 1)');
  return [e.p, e.q];
};

/**
 * An LLL-reduced basis of the integer row lattice.
 * @param M - The input matrix.
 * @param delta - The LLL reduction parameter, strictly between one quarter and one.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.lll`
 * @example
 * ```ts
 * import { Matrix, lll } from '@symjs/symjs';
 * lll(Matrix.of([[1, 2, 3], [4, 5, 6]])).toArray(); // => [[2, 1, 0], [-1, 1, 3]]
 * ```
 */
export function lll(M: Matrix, delta: ExprLike = Rational.of(3n, 4n)): Matrix {
  return lllCore(M, deltaQ(delta), false)[0];
}
/**
 * Reduces the integer row basis by LLL and tracks the unimodular transformation.
 * @param M - The input matrix.
 * @param delta - The LLL reduction parameter, strictly between one quarter and one.
 * @returns The reduced basis and its change-of-basis matrix.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.lll_transform`
 * @example
 * ```ts
 * import { Matrix, lllTransform } from '@symjs/symjs';
 *
 * const A = Matrix.of([[1, 2], [3, 4]]);
 * const [B, T] = lllTransform(A);
 * T.mul(A).equals(B); // => True
 * ```
 */
export function lllTransform(M: Matrix, delta: ExprLike = Rational.of(3n, 4n)): [Matrix, Matrix] {
  const [B, T] = lllCore(M, deltaQ(delta), true);
  return [B, defined(T, 'transform matrix')];
}

// ---------------------------------------------------------------------------
// Elementary operations, permutations, deletion
// ---------------------------------------------------------------------------

/** Options of elementaryRowOp/elementaryColOp. */
export interface ElementaryOp {
  /** 'n->kn' (scale), 'n<->m' (swap) or 'n->n+km' (add a multiple). */
  op?: 'n->kn' | 'n<->m' | 'n->n+km';
  /** The row/column changed. */
  index?: number;
  /** The scale factor or multiple of the source row or column. */
  k?: ExprLike;
  /** The first row or column index. */
  index1?: number;
  /** The second row or column index. */
  index2?: number;
}

function elementary(M: Matrix, o: ElementaryOp, onCols: boolean): Matrix {
  const A = onCols ? M.T : M;
  const op = o.op ?? 'n->kn';
  const len = A.rows;
  const kind = onCols ? 'col' : 'row';
  // SymPy accepts no negative indices: "This matrix does not have a row '-1'"
  const norm1 = (i: number | undefined, what: string): number => {
    if (i === undefined) throw new TypeError(`${what} must be given`);
    if (i < 0 || i >= len) throw new RangeError(`This matrix does not have a ${kind} '${i}'`);
    return i;
  };
  let R: Matrix;
  if (op === 'n->kn') {
    const r = norm1(o.index ?? o.index1, 'index');
    const k = sympify(o.k ?? 1);
    R = Matrix.fromFunction(A.rows, A.cols, (i, j) => (i === r ? mul(k, A.get(i, j)) : A.get(i, j)));
  } else if (op === 'n<->m') {
    const r1 = norm1(o.index1 ?? o.index, 'index1');
    const r2 = norm1(o.index2 ?? (o.k === undefined ? undefined : Number(sympify(o.k).toNumber())), 'index2');
    if (r1 === r2) throw new RangeError(`For a ${kind} operation 'n<->m' you must provide two different ${kind}s`);
    R = Matrix.fromFunction(A.rows, A.cols, (i, j) => A.get(i === r1 ? r2 : i === r2 ? r1 : i, j));
  } else {
    const r = norm1(o.index ?? o.index1, 'index');
    const r2 = norm1(o.index2 ?? o.index1, 'index2');
    if (r === r2) throw new RangeError(`For a ${kind} operation 'n->n+km' \`${kind}\` and \`${kind}2\` must be different.`);
    const k = sympify(o.k ?? 1);
    R = Matrix.fromFunction(A.rows, A.cols, (i, j) => (i === r ? add(A.get(i, j), mul(k, A.get(r2, j))) : A.get(i, j)));
  }
  return onCols ? R.T : R;
}

/**
 * Scales a row, exchanges two rows or adds a multiple of one row to another.
 * @param M - The input matrix.
 * @param o - The operation, indices and scale factor in {@link ElementaryOp}.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.elementary_row_op`
 * @remarks SymPy prints this result as `Matrix([[1, 0, 0], [0, 5, 0], [0, 0, 1]])`.
 * @example
 * ```ts
 * import { Matrix, elementaryRowOp } from '@symjs/symjs';
 * elementaryRowOp(Matrix.of([[1, 0, 0], [0, 1, 0], [0, 0, 1]]), { op: 'n->kn', index: 1, k: 5 }); // => Matrix([
 * //   [1, 0, 0],
 * //   [0, 5, 0],
 * //   [0, 0, 1]])
 * ```
 */
export function elementaryRowOp(M: Matrix, o: ElementaryOp): Matrix {
  return elementary(M, o, false);
}
/**
 * Scales a column, exchanges two columns or adds a multiple of one column to another.
 * @param M - The input matrix.
 * @param o - The operation, indices and scale factor in {@link ElementaryOp}.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.elementary_col_op`
 * @remarks SymPy prints this result as `Matrix([[1, 0, 0], [0, 5, 0], [0, 0, 1]])`.
 * @example
 * ```ts
 * import { Matrix, elementaryColOp } from '@symjs/symjs';
 * elementaryColOp(Matrix.of([[1, 0, 0], [0, 1, 0], [0, 0, 1]]), { op: 'n->kn', index: 1, k: 5 }); // => Matrix([
 * //   [1, 0, 0],
 * //   [0, 5, 0],
 * //   [0, 0, 1]])
 * ```
 */
export function elementaryColOp(M: Matrix, o: ElementaryOp): Matrix {
  return elementary(M, o, true);
}

/**
 * Applies row swaps in the specified order.
 * @param M - The input matrix.
 * @param perm - The permutation to apply.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.permuteFwd`
 */
export function permuteFwd(M: Matrix, perm: readonly (readonly [number, number])[] | readonly number[]): Matrix {
  return M.permute(perm);
}
/**
 * Undoes a sequence of row swaps by applying them in reverse order.
 * @param M - The input matrix.
 * @param perm - The permutation to apply.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.permuteBkwd`
 */
export function permuteBkwd(M: Matrix, perm: readonly (readonly [number, number])[] | readonly number[]): Matrix {
  return M.permute(perm, { direction: 'backward' });
}

/**
 * Returns a copy of the matrix with the specified row removed.
 * @param M - The input matrix.
 * @param i - The zero-based row index.
 * @returns A copy of the matrix with the specified row removed.
 * @throws RangeError when the row index is out of bounds.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.row_del`
 * @remarks SymPy prints this result as `Matrix([[1, 2, 3], [4, 5, 6]])`.
 * @example
 * ```ts
 * import { Matrix, rowDel } from '@symjs/symjs';
 * rowDel(Matrix.of([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), 2); // => Matrix([
 * //   [1, 2, 3],
 * //   [4, 5, 6]])
 * ```
 */
export function rowDel(M: Matrix, i: number): Matrix {
  const r = i < 0 ? i + M.rows : i;
  if (r < 0 || r >= M.rows) throw new RangeError(`Row ${i} is out of range.`);
  return M.slice(range(0, M.rows).filter((k) => k !== r), range(0, M.cols));
}
/**
 * Returns a copy of the matrix with the specified column removed.
 * @param M - The input matrix.
 * @param j - The zero-based column index.
 * @returns A copy of the matrix with the specified column removed.
 * @throws RangeError when the column index is out of bounds.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.col_del`
 * @remarks SymPy prints this result as `Matrix([[1, 2], [4, 5], [7, 8]])`.
 * @example
 * ```ts
 * import { Matrix, colDel } from '@symjs/symjs';
 * colDel(Matrix.of([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), 2); // => Matrix([
 * //   [1, 2],
 * //   [4, 5],
 * //   [7, 8]])
 * ```
 */
export function colDel(M: Matrix, j: number): Matrix {
  const c = j < 0 ? j + M.cols : j;
  if (c < 0 || c >= M.cols) throw new RangeError(`Column ${j} is out of range.`);
  return M.slice(range(0, M.rows), range(0, M.cols).filter((k) => k !== c));
}

// ---------------------------------------------------------------------------
// Blocks and graph decompositions
// ---------------------------------------------------------------------------

/**
 * Returns the square blocks along the diagonal.
 * @param M - The input matrix.
 * @returns The square blocks along the diagonal.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.get_diag_blocks`
 * @example
 * ```ts
 * import { Matrix, getDiagBlocks } from '@symjs/symjs';
 * getDiagBlocks(Matrix.diag(1, 2, 3)).map(block => block.toArray()); // => [[[1]], [[2]], [[3]]]
 * ```
 */
export function getDiagBlocks(M: Matrix): Matrix[] {
  const out: Matrix[] = [];
  let start = 0;
  const n = M.rows;
  while (start < n) {
    let size = 1;
    // grow the block while it is coupled to what follows
    for (;;) {
      const end = start + size;
      let coupled = false;
      for (let i = start; i < end && !coupled; i++) {
        for (let j = end; j < n && !coupled; j++) if (!isZeroExpr(M.get(i, j)) || !isZeroExpr(M.get(j, i))) coupled = true;
      }
      if (!coupled || end >= n) break;
      size++;
    }
    out.push(M.slice(range(start, start + size), range(start, start + size)));
    start += size;
  }
  return out;
}

/**
 * Permutes the matrix into blocks corresponding to the connected components of its graph.
 * @param M - The input matrix.
 * @returns The permutation matrix and the block-diagonal matrix of connected components.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.connected_components_decomposition`
 * @example
 * ```ts
 * import { Matrix, connectedComponentsDecomposition } from '@symjs/symjs';
 * connectedComponentsDecomposition(Matrix.diag(1, 2))[1].blockshape; // => [2, 2]
 * ```
 */
export function connectedComponentsDecomposition(M: Matrix): [PermutationMatrix, BlockDiagMatrix] {
  const blocks = connectedComponents(M);
  return [PermutationMatrix(new PermutationNode(blocks.flat())), BlockDiagMatrix(...blocks.map((b) => M.slice(b, b)))];
}

/**
 * Permutes the matrix into triangular block form using the strongly connected components of its graph.
 * @param M - The input matrix.
 * @param lower - Whether the component blocks form a lower triangular matrix.
 * @returns The permutation matrix and the block-triangular matrix of strongly connected components.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.strongly_connected_components_decomposition`
 * @example
 * ```ts
 * import { Matrix, stronglyConnectedComponentsDecomposition } from '@symjs/symjs';
 * stronglyConnectedComponentsDecomposition(Matrix.diag(1, 2))[1].blockshape; // => [2, 2]
 * ```
 */
export function stronglyConnectedComponentsDecomposition(M: Matrix, lower = true): [PermutationMatrix, BlockMatrix] {
  let blocks = stronglyConnectedComponents(M);
  if (!lower) blocks = [...blocks].reverse();
  return [PermutationMatrix(new PermutationNode(blocks.flat())), BlockMatrix(blocks.map((r) => blocks.map((c) => M.slice(r, c))))];
}

/**
 * An n x n Jordan block.
 * @param eigenval - The eigenvalue along the diagonal.
 * @param n - The order of the square matrix.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.jordan_cell`
 */
export function jordanCell(eigenval: ExprLike, n: number): Matrix {
  return jordanBlock(n, eigenval);
}
/**
 * Finds the Jordan blocks and their change of basis.
 * @param M - The input matrix.
 * @returns The Jordan blocks and their change of basis.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.jordan_cells`
 */
export function jordanCells(M: Matrix): [Matrix, Matrix[]] {
  const [P, J] = jordanForm(M);
  return [P, getDiagBlocks(J)];
}

// ---------------------------------------------------------------------------
// Dual tensor
// ---------------------------------------------------------------------------

/** SymPy eval_levicivita: the Levi-Civita symbol of integers. */
function leviCivita(...a: number[]): Expr {
  let num = 1n;
  let den = 1n;
  for (const [i, ai] of a.entries()) {
    for (const aj of a.slice(i + 1)) num *= BigInt(aj - ai);
    let f = 1n;
    for (let k = 2n; k <= BigInt(i); k++) f *= k;
    den *= f;
  }
  return Rational.of(num, den);
}

/**
 * Returns the dual of a matrix.
 * @param M - The input matrix.
 * @returns The dual of a matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.dual`
 */
export function dual(M: Matrix): Matrix {
  const n = M.rows;
  const w = rows(Matrix.zeros(n));
  const symmetric = M.isSquare && M.equals(M.T);
  if (symmetric) return Matrix.zeros(n);
  for (let i = 1; i < n; i++) {
    for (let j = 1; j < n; j++) {
      let acc: Expr = S.Zero;
      for (let k = 1; k < n; k++) acc = add(acc, mul(leviCivita(i, j, 0, k), M.get(0, k)));
      at(w, i)[j] = acc;
      at(w, j)[i] = mul(-1, acc);
    }
  }
  for (let l = 1; l < n; l++) {
    let acc: Expr = S.Zero;
    for (let a = 1; a < n; a++) for (let b = 1; b < n; b++) acc = add(acc, mul(leviCivita(0, l, a, b), M.get(a, b)));
    acc = mul(acc, Rational.of(1n, 2n));
    at(w, 0)[l] = mul(-1, acc);
    at(w, l)[0] = acc;
  }
  return Matrix.of(w);
}

// ---------------------------------------------------------------------------
// Iteration, indexing and printing
// ---------------------------------------------------------------------------

/**
 * Lists nonzero entries with their row and column indices in row-major order.
 * @param M - The input matrix.
 * @returns The positions and values of nonzero entries in row-major order.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.iter_items`
 * @example
 * ```ts
 * import { Matrix, iterItems } from '@symjs/symjs';
 * iterItems(Matrix.of([[0, 1], [2, 3]])); // => [[[0, 1], 1], [[1, 0], 2], [[1, 1], 3]]
 * ```
 */
export function iterItems(M: Matrix): [[number, number], Expr][] {
  const out: [[number, number], Expr][] = [];
  for (let i = 0; i < M.rows; i++) for (let j = 0; j < M.cols; j++) if (!isZeroExpr(M.get(i, j))) out.push([[i, j], M.get(i, j)]);
  return out;
}
/**
 * The nonzero entries in row-major order.
 * @param M - The input matrix.
 * @returns The resulting expressions in order.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.iter_values`
 * @example
 * ```ts
 * import { Matrix, iterValues } from '@symjs/symjs';
 * iterValues(Matrix.of([[0, 1], [2, 3]])); // => [1, 2, 3]
 * ```
 */
export function iterValues(M: Matrix): Expr[] {
  return iterItems(M).map(([, v]) => v);
}

/** A slice of indices (Python slice: start, stop, step; null for the default). */
export interface IndexSlice {
  /** The first included index. */
  start?: number | null;
  /** The exclusive ending index. */
  stop?: number | null;
  /** The signed stride between consecutive indices. */
  step?: number | null;
}

const a2idx = (j: number, n: number): number => {
  const k = j < 0 ? j + n : j;
  if (k < 0 || k >= n) throw new RangeError(`Index out of range: a[${j}]`);
  return k;
};
/** Python slice.indices(n)[:2]: the normalized start and stop. */
const sliceBounds = (s: IndexSlice, n: number): [number, number] => {
  const step = s.step ?? 1;
  const clamp = (v: number | null | undefined, dflt: number): number => {
    if (v === null || v === undefined) return dflt;
    const w = v < 0 ? v + n : v;
    return step > 0 ? Math.min(Math.max(w, 0), n) : Math.min(Math.max(w, -1), n - 1);
  };
  return step > 0 ? [clamp(s.start, 0), clamp(s.stop, n)] : [clamp(s.start, n - 1), clamp(s.stop, -1)];
};
const isSlice = (k: unknown): k is IndexSlice => typeof k === 'object' && k !== null;
type IndexKey = number | IndexSlice | readonly [number | IndexSlice, number | IndexSlice];
const isKeyPair = (k: IndexKey): k is readonly [number | IndexSlice, number | IndexSlice] => Array.isArray(k);

/**
 * A key normalized to valid indices; slices are kept,
 * a flat index becomes [row, column].
 * @param M - The input matrix.
 * @param key - The index or pair of indices to select.
 * @returns A key normalized to valid indices.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.key2ij`
 */
export function key2ij(M: Matrix, key: IndexKey): [number | IndexSlice, number | IndexSlice] | [number, number] {
  if (isKeyPair(key)) {
    const [a, b] = key;
    return [isSlice(a) ? a : a2idx(a, M.rows), isSlice(b) ? b : a2idx(b, M.cols)];
  }
  if (isSlice(key)) return sliceBounds(key, M.rows * M.cols);
  const k = a2idx(key, M.rows * M.cols);
  return [Math.floor(k / M.cols), k % M.cols];
}
/**
 * Converts a row and column selection to half-open index bounds.
 * @param M - The input matrix.
 * @param keys - The row and column selectors.
 * @returns The start and exclusive end for the rows, followed by the corresponding column bounds.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.key2bounds`
 */
export function key2bounds(M: Matrix, keys: readonly [number | IndexSlice, number | IndexSlice]): [number, number, number, number] {
  const bounds = (k: number | IndexSlice, n: number): [number, number] => {
    if (isSlice(k)) return n === 0 ? [0, 0] : sliceBounds(k, n);
    const lo = a2idx(k, n);
    return [lo, lo + 1];
  };
  const [rlo, rhi] = bounds(keys[0], M.rows);
  const [clo, chi] = bounds(keys[1], M.cols);
  return [rlo, rhi, clo, chi];
}

/**
 * The pattern of nonzero entries, one line per row.
 * @param M - The input matrix.
 * @param symb - The marker for a nonzero entry.
 * @returns The formatted text.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.print_nonzero`
 * @example
 * ```ts
 * import { Matrix, printNonzero } from '@symjs/symjs';
 * printNonzero(Matrix.of([[0, 1, 2], [3, 4, 5]])); // => [ XX]
 * //   [XXX]
 * ```
 */
export function printNonzero(M: Matrix, symb = 'X'): string {
  const lines: string[] = [];
  for (let i = 0; i < M.rows; i++) {
    let line = '';
    for (let j = 0; j < M.cols; j++) line += isZeroExpr(M.get(i, j)) ? ' ' : symb;
    lines.push(`[${line}]`);
  }
  return lines.join('\n');
}

/** Options of table. */
export interface TableOptions {
  /** Text placed before the first entry of each row. */
  rowstart?: string;
  /** Text placed after the last entry of each row. */
  rowend?: string;
  /** Text separating adjacent rows. */
  rowsep?: string;
  /** Text separating adjacent columns. */
  colsep?: string;
  /** The horizontal alignment of entries within a column. */
  align?: 'left' | 'right' | 'center' | '<' | '>' | '^';
  /** Printer of the entries; str by default. */
  printer?: (e: Expr) => string;
}

/**
 * The entries as aligned text.
 * @param M - The input matrix.
 * @param opts - The settings described by {@link TableOptions}.
 * @returns The formatted rows joined as a string.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.table`
 * @example
 * ```ts
 * import { Matrix, table } from '@symjs/symjs';
 * table(Matrix.of([[1, 2], [-33, 4]])); // => [  1, 2]
 * //   [-33, 4]
 * ```
 */
export function table(M: Matrix, opts: TableOptions = {}): string {
  if (M.rows === 0 || M.cols === 0) return '[]';
  const p = opts.printer ?? str;
  const cells = rows(M).map((r) => r.map(p));
  const widths = range(0, M.cols).map((j) => Math.max(...cells.map((r) => at(r, j).length)));
  const align = { left: 'l', '<': 'l', right: 'r', '>': 'r', center: 'c', '^': 'c' }[opts.align ?? 'right'];
  const pad = (s: string, w: number): string => {
    if (align === 'l') return s.padEnd(w);
    if (align === 'r') return s.padStart(w);
    // Python str.center: the extra space goes to the right when the padding is odd and the width is even
    const total = w - s.length;
    const left = Math.floor(total / 2) + (total % 2 && w % 2 ? 1 : 0);
    return ' '.repeat(left) + s + ' '.repeat(total - left);
  };
  return cells.map((r) => `${opts.rowstart ?? '['}${r.map((c, j) => pad(c, at(widths, j))).join(opts.colsep ?? ', ')}${opts.rowend ?? ']'}`).join(opts.rowsep ?? '\n');
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

/**
 * Returns the (2n+1) x (2n+1) Wilkinson matrices [W-, W+].
 * @param n - The half-band size, giving matrices of order `2*n + 1`.
 * @returns The (2n+1) x (2n+1) Wilkinson matrices [W-, W+].
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.wilkinson`
 * @example
 * ```ts
 * import { wilkinson } from '@symjs/symjs';
 * wilkinson(3)[0].diagonal().toArray(); // => [[-3, -2, -1, 0, 1, 2, 3]]
 * ```
 */
export function wilkinson(n: number): [Matrix, Matrix] {
  const size = 2 * n + 1;
  const off = (i: number, j: number) => (Math.abs(i - j) === 1 ? 1 : 0);
  const minus = Matrix.fromFunction(size, size, (i, j) => (i === j ? i - n : off(i, j)));
  const plus = Matrix.fromFunction(size, size, (i, j) => (i === j ? Math.abs(i - n) : off(i, j)));
  return [minus, plus];
}

/** Options of randMatrix (SymPy). */
export interface RandMatrixOptions {
  /** The smallest permitted entry. */
  min?: number;
  /** The largest permitted entry. */
  max?: number;
  /** The seed controlling random draws. */
  seed?: number;
  /** Whether the entries should be mirrored across the diagonal. */
  symmetric?: boolean;
  /** Percentage of nonzero entries (approximately). */
  percent?: number;
  /** A generator of numbers in [0, 1); seeded by `seed` when omitted. */
  prng?: () => number;
}

/**
 * Generates a matrix with random integer entries within the specified bounds.
 * @param r - The number of rows.
 * @param c - The number of columns.
 * @param opts - The settings described by {@link RandMatrixOptions}.
 * @returns The sampled integer matrix.
 * @throws RangeError when symmetry is requested with unequal dimensions or the bounds for random entries are inconsistent.
 * @see SymPy `sympy.matrices.dense.randMatrix`
 * @example
 * ```ts
 * import { randMatrix } from '@symjs/symjs';
 * randMatrix(3, 3, { seed: 1 }).equals(randMatrix(3, 3, { seed: 1 })); // => True
 * ```
 */
export function randMatrix(r: number, c: number = r, opts: RandMatrixOptions = {}): Matrix {
  if (opts.symmetric && r !== c) throw new RangeError('For symmetric matrices, r must equal c');
  const generator = new Random(opts.seed);
  const rnd = opts.prng;
  const below = (n: number): number => rnd ? Math.floor(rnd() * n) : Number(generator.randbelow(BigInt(n)));
  const lo = opts.min ?? 0;
  const hi = opts.max ?? 99;
  const data = Matrix.zeros(r, c).toArray();
  const cells = range(0, r * c);
  const k = Math.floor(cells.length * (opts.percent ?? 100) / 100);
  if (k < 0 || k > cells.length || hi < lo) throw new RangeError('Invalid random matrix range');
  let indices = cells;
  if (opts.percent !== undefined && opts.percent !== 100) {
    indices = [];
    const setSize = 21 + (k > 5 ? 4 ** Math.ceil(Math.log(3 * k) / Math.log(4)) : 0);
    if (cells.length <= setSize) {
      for (let i = 0; i < k; i++) {
        const j = below(cells.length - i);
        indices.push(at(cells, j));
        cells[j] = at(cells, cells.length - i - 1);
      }
    } else {
      const selected = new Set<number>();
      while (selected.size < k) selected.add(below(cells.length));
      indices = [...selected];
    }
  }
  for (const cell of indices) {
    const i = Math.floor(cell / c);
    const j = cell % c;
    if (opts.symmetric && i > j) continue;
    const value = Rational.of(lo + below(hi - lo + 1));
    at(data, i)[j] = value;
    if (opts.symmetric) at(data, j)[i] = value;
  }
  return Matrix.fromFunction(r, c, (i, j) => get2(data, i, j));
}

/**
 * Nested arrays of symbols prefix_i_j...; the shape is a length or a list of lengths.
 * @param prefix - The prefix for generated symbol names.
 * @param shape - The dimensions of the array.
 * @param assumptions - The assumptions to apply.
 * @returns An array of indexed symbols arranged in the requested shape.
 * @see SymPy `sympy.matrices.dense.symarray`
 * @example
 * ```ts
 * import { symarray } from '@symjs/symjs';
 * symarray('a', 3); // => [a_0, a_1, a_2]
 * ```
 */
export function symarray(prefix: string, shape: number | readonly number[], assumptions: Assumptions = {}): unknown[] {
  const dims = typeof shape === 'number' ? [shape] : [...shape];
  const build = (level: number, idx: number[]): unknown[] =>
    range(0, at(dims, level)).map((i) => (level === dims.length - 1 ? new Sym(`${prefix}_${[...idx, i].join('_')}`, assumptions) : build(level + 1, [...idx, i])));
  return build(0, []);
}

/**
 * The entries as nested arrays; `float` converts them to numbers.
 * @param M - The input matrix.
 * @param dtype - Whether entries stay symbolic or convert to floating-point numbers.
 * @returns The entries as nested arrays.
 * @see SymPy `sympy.matrices.dense.matrix2numpy`
 */
export function matrix2numpy(M: Matrix, dtype: 'object' | 'float' = 'object'): (Expr | number)[][] {
  return rows(M).map((r) => r.map((e) => (dtype === 'float' ? e.toNumber() : e)));
}
/** v as an expression; throws SympifyError (as sympify does) for anything but an Expr, number or bigint. */
const toExpr = (v: unknown): Expr => {
  if (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint') return sympify(v);
  throw new SympifyError(`Cannot convert ${String(v)} to an expression`, v);
};
/**
 * Returns a (nested) list as an array of expressions.
 * @param list - The nested sequence of entries to convert.
 * @param dtype - Whether entries stay symbolic or convert to floating-point numbers.
 * @returns A (nested) list as an array of expressions.
 * @see SymPy `sympy.matrices.dense.list2numpy`
 */
export function list2numpy(list: readonly unknown[], dtype: 'object' | 'float' = 'object'): unknown[] {
  return list.map((v) => (Array.isArray(v) ? list2numpy(v, dtype) : dtype === 'float' ? toExpr(v).toNumber() : toExpr(v)));
}

