// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/rref.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The reduced row echelon form of a DomainMatrix with the method
 * chosen by the domain and the shape of the matrix: Gauss-Jordan over the
 * field (GJ), fraction-free elimination (FF), or fraction-free elimination
 * after clearing denominators row by row (CD), on the sparse or dense
 * representation (SymPy _dm_rref, _dm_rref_den).
 */

import { at } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { lcm as ilcm } from '../../core/numbers';
import { DDM } from './ddm';
import { ddmIrref, ddmIrrefDen, usePartialPivot } from './dense';
import { bitLength, hasAssocField, isQQ, isZZ, rat } from './domainops';
import type { DomainMatrix } from './domainmatrix';
import { SDM, sdmIrref, sdmRrefDen } from './sdm';

/** A method of rref: GJ, FF, CD, optionally with _dense. */
export type RrefMethod = 'auto' | 'GJ' | 'FF' | 'CD' | 'GJ_dense' | 'FF_dense' | 'CD_dense';
type Fmt = 'dense' | 'sparse';

/** SymPy _dm_rref: [rref over the field, pivots]. */
export function dmRref(Min: DomainMatrix, opts: { method?: RrefMethod } = {}): [DomainMatrix, number[]] {
  const [method, useFmt] = dmRrefChooseMethod(Min, opts.method ?? 'auto', false);
  const [M, oldFmt] = dmToFmt(Min, useFmt);
  let rref: DomainMatrix;
  let pivots: number[];
  if (method === 'GJ') [rref, pivots] = dmRrefGJ(toField(M));
  else if (method === 'FF') {
    const [rf, den, p] = dmRrefDenFF(M);
    [rref, pivots] = [toField(rf).div(den), p];
  } else {
    const [, Mr] = M.clearDenomsRowwise(true);
    const [rf, den, p] = dmRrefDenFF(Mr);
    [rref, pivots] = [toField(rf).div(den), p];
  }
  return [dmToFmt(rref, oldFmt)[0], pivots];
}

/** SymPy _dm_rref_den: [fraction-free rref, denominator, pivots]. */
export function dmRrefDen(Min: DomainMatrix, opts: { method?: RrefMethod; keepDomain?: boolean } = {}): [DomainMatrix, Expr, number[]] {
  const keepDomain = opts.keepDomain ?? true;
  const [method, useFmt] = dmRrefChooseMethod(Min, opts.method ?? 'auto', true);
  const [M, oldFmt] = dmToFmt(Min, useFmt);
  let rref: DomainMatrix;
  let den: Expr;
  let pivots: number[];
  if (method === 'FF') [rref, den, pivots] = dmRrefDenFF(M);
  else if (method === 'GJ') {
    const [rf, p] = dmRrefGJ(toField(M));
    pivots = p;
    if (keepDomain && !rf.domain.equals(M.domain)) {
      rref = rf.clearDenoms(true)[1];
      den = pivots.length ? rref.getitem(0, at(pivots, 0)).element : rref.domain.one;
    } else [rref, den] = [rf, rf.domain.one];
  } else {
    const [, Mr] = M.clearDenomsRowwise(true);
    const [rr, d, p] = dmRrefDenFF(Mr);
    pivots = p;
    if (keepDomain && !rr.domain.equals(M.domain)) [rref, den] = [toField(rr).div(d), M.domain.one];
    else [rref, den] = [rr, pivots.length ? rr.getitem(0, at(pivots, 0)).element : rr.domain.one];
  }
  return [dmToFmt(rref, oldFmt)[0], den, pivots];
}

function dmToFmt(M: DomainMatrix, fmt: Fmt): [DomainMatrix, Fmt] {
  const oldFmt = M.rep.fmt;
  if (oldFmt === fmt) return [M, oldFmt];
  return [fmt === 'dense' ? M.toDense() : M.toSparse(), oldFmt];
}

function dmRrefGJ(M: DomainMatrix): [DomainMatrix, number[]] {
  const rep = M.rep;
  if (rep instanceof SDM) {
    const [d, pivots] = sdmIrref(rep.data, M.domain);
    return [M.fromRep(new SDM(d, M.shape, M.domain)), pivots];
  }
  const ddm = rep.toDdm().copy();
  const pivots = ddmIrref(ddm.data, usePartialPivot(M.domain), M.domain);
  return [M.fromRep(new DDM(ddm.data, M.shape, M.domain)), pivots];
}

function dmRrefDenFF(M: DomainMatrix): [DomainMatrix, Expr, number[]] {
  const rep = M.rep;
  if (rep instanceof SDM) {
    const [d, den, pivots] = sdmRrefDen(rep.data, M.domain);
    return [M.fromRep(new SDM(d, M.shape, M.domain)), den, pivots];
  }
  const ddm = rep.toDdm().copy();
  const [den, pivots] = ddmIrrefDen(ddm.data, M.domain);
  return [M.fromRep(new DDM(ddm.data, M.shape, M.domain)), den, pivots];
}

/** SymPy _dm_rref_choose_method: [method, format]. */
export function dmRrefChooseMethod(M: DomainMatrix, methodIn: RrefMethod, denominator: boolean): [string, Fmt] {
  if (methodIn !== 'auto') return methodIn.endsWith('_dense') ? [methodIn.slice(0, -'_dense'.length), 'dense'] : [methodIn, 'sparse'];
  const K = M.domain;
  if (isZZ(K)) return [dmRrefChooseMethodZZ(M), 'sparse'];
  if (isQQ(K)) return [dmRrefChooseMethodQQ(M), 'sparse'];
  if (usePartialPivot(K)) return ['GJ', 'dense'];
  if (K.toString() === 'EX' && M.rep.fmt === 'dense' && !denominator) return ['GJ', 'dense'];
  return [denominator ? 'FF' : 'GJ', 'sparse'];
}

/** SymPy _dm_rref_choose_method_QQ. */
function dmRrefChooseMethodQQ(M: DomainMatrix): string {
  const [density, , ncols] = dmRowDensity(M);
  if (density < Math.min(5, ncols / 2)) return 'GJ';
  const elements = M.toFlatNz()[0].map(rat);
  const numerBits = Math.max(1, ...elements.map((e) => bitLength(e.p)));
  let denomLcm = 1n;
  for (const e of elements) {
    denomLcm = ilcm(denomLcm, e.q);
    if (bitLength(denomLcm) > 5 * numerBits) return 'GJ';
  }
  return bitLength(denomLcm) < 50 ? 'CD' : 'FF';
}

/** The tuning parameter of the ZZ method choice (SymPy PARAM). */
const PARAM = 10000;

/** SymPy _dm_rref_choose_method_ZZ. */
function dmRrefChooseMethodZZ(M: DomainMatrix): string {
  const [density, nrowsNz, ncols] = dmRowDensity(M);
  if (nrowsNz < 10) return density < ncols / 2 ? 'GJ' : 'FF';
  if (density < 5) return 'GJ';
  if (density > 5 + PARAM / nrowsNz) return 'FF';
  const bits = Math.max(1, ...M.toFlatNz()[0].map((e) => bitLength(rat(e).p)));
  const wideness = Math.max(1, ((2 / 3) * ncols) / nrowsNz);
  const maxDensity = (5 + PARAM / (nrowsNz * bits ** 2)) * wideness;
  return density < maxDensity ? 'GJ' : 'FF';
}

/** [average number of nonzero elements of the nonzero rows, number of nonzero rows, columns]. */
function dmRowDensity(M: DomainMatrix): [number, number, number] {
  const ncols = M.shape[1];
  const rowsNz = [...M.rep.toSdm().data.values()];
  if (!rowsNz.length) return [0, 0, ncols];
  return [rowsNz.reduce((s, r) => s + r.size, 0) / rowsNz.length, rowsNz.length, ncols];
}

const toField = (M: DomainMatrix): DomainMatrix => (hasAssocField(M.domain) ? M.toField() : M);
