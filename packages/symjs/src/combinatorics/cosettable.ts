// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/coset_table.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.coset_table: coset tables of a subgroup of
 * a finitely presented group and the Todd-Coxeter coset enumeration, both
 * the relator-based (HLT) and the coset-table-based (Felsch) strategies, and
 * the modified enumeration that tracks the subgroup generators.
 */

import { at, defined } from '../core/guard';
import type { FreeGroup, FreeGroupElement } from './freegroups';
import { freeGroup, uniqueWords } from './freegroups';

/** The part of a finitely presented group a coset table uses. */
export interface CosetGroup {
  readonly generators: readonly FreeGroupElement[];
  readonly relators: readonly FreeGroupElement[];
  readonly identity: FreeGroupElement;
  toString(): string;
}

/** A row of a coset table: the coset each letter of A leads to (null where not yet defined). */
export type CosetRow = (number | null)[];

/** The ValueError of a coset enumeration that defines more cosets than allowed. */
export class CosetLimitExceeded extends RangeError {
  constructor(limit: number) {
    super(`the coset enumeration has defined more than ${limit} cosets. Try with a greater value max number of cosets `);
    this.name = 'CosetLimitExceeded';
  }
}

/** The column of a letter (+(i+1) is generator i, -(i+1) its inverse): generator i at 2i, its inverse at 2i + 1. */
const column = (c: number): number => 2 * (Math.abs(c) - 1) + (c < 0 ? 1 : 0);

/**
 * Python's bisect_left on a sorted list.
 */
function bisectLeft(a: readonly number[], x: number): number {
  let lo = 0;
  let hi = a.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (at(a, mid) < x) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

/**
 * SymPy CosetTable(fp_grp, subgroup, max_cosets): the coset table of a
 * subgroup of a finitely presented group, built by coset enumeration.
 * Columns are the generators and their inverses in the order of A.
 */
export class CosetTable {
  /** SymPy coset_table_max_limit: the default maximum number of cosets. */
  static cosetTableMaxLimit = 4096000;
  /** SymPy max_stack_size: the deduction stack size that triggers a look-ahead. */
  static maxStackSize = 100;
  readonly fpGroup: CosetGroup;
  readonly subgroup: readonly FreeGroupElement[];
  /** SymPy coset_table_limit. */
  readonly cosetTableLimit: number;
  /** SymPy p: the coset each coset is equivalent to (p[i] = i for a live coset). */
  p: number[];
  /** SymPy A: the generators and their inverses. */
  readonly A: FreeGroupElement[];
  /** SymPy table. */
  table: CosetRow[];
  /** SymPy P: the subgroup words of the modified enumeration. */
  P: (FreeGroupElement | null)[][];
  /** SymPy deduction_stack: the (coset, letter column) deductions to process. */
  deductionStack: [number, number][];
  /** @internal SymPy _grp: the free group on the subgroup generators (a_0, a_1, ...). */
  readonly grp: FreeGroup;
  /** @internal SymPy p_p: the subgroup words of the coincident cosets. */
  pP: Map<number, FreeGroupElement>;
  /** @internal SymPy _schreier_free_group, _schreier_generators, ... of a Reidemeister-Schreier presentation. */
  schreier: {
    freeGroup?: FreeGroup;
    generators?: FreeGroupElement[];
    genElements?: Map<string, FreeGroupElement>;
    relators?: FreeGroupElement[];
  } = {};
  /** SymPy schreier_generators and reidemeister_relators, once computed. */
  schreierGenerators: FreeGroupElement[] = [];
  reidemeisterRelators: FreeGroupElement[] = [];

  constructor(fpGroup: CosetGroup, subgroup: readonly FreeGroupElement[], maxCosets?: number) {
    this.fpGroup = fpGroup;
    this.subgroup = subgroup;
    this.cosetTableLimit = maxCosets !== undefined && maxCosets !== 0 ? maxCosets : CosetTable.cosetTableMaxLimit;
    this.p = [0];
    this.A = fpGroup.generators.flatMap((g) => [g, g.inverse()]);
    this.P = [this.#emptyRow()];
    this.table = [this.#emptyRow()];
    this.deductionStack = [];
    this.grp = defined(freeGroup(subgroup.map((_h, i) => `a_${i}`).join(', '))[0], 'free group');
    this.pP = new Map();
  }

  #emptyRow(): null[] {
    return Array<null>(this.A.length).fill(null);
  }

  /** The column of a letter of A (SymPy A_dict[x]). */
  #col(x: FreeGroupElement): number {
    if (x.length !== 1) throw new RangeError(`${String(x)} is not a letter`);
    return column(at(x.letters, 0));
  }

  /** SymPy A_dict: the column of each letter. */
  get ADict(): Map<FreeGroupElement, number> {
    return new Map(this.A.map((x, i) => [x, i]));
  }

  /** SymPy A_dict_inv: the column of each letter's inverse. */
  get ADictInv(): Map<FreeGroupElement, number> {
    return new Map(this.A.map((x, i) => [x, i ^ 1]));
  }

  /** SymPy omega: the live cosets. */
  get omega(): number[] {
    return this.p.flatMap((c, i) => (c === i ? [i] : []));
  }

  /** SymPy copy(): a copy of the table, p and the deduction stack. */
  copy(): CosetTable {
    const c = new CosetTable(this.fpGroup, this.subgroup);
    c.table = this.table.map((r) => [...r]);
    c.p = [...this.p];
    c.deductionStack = [...this.deductionStack];
    return c;
  }

  toString(): string {
    return `Coset Table on ${String(this.fpGroup)} with ${listStr(this.subgroup)} as subgroup generators`;
  }

  /** SymPy n: the number of cosets, 1 + the largest live one. */
  get n(): number {
    if (!this.table.length) return 0;
    return Math.max(...this.omega) + 1;
  }

  /** SymPy is_complete(): whether every live coset has all its entries. */
  isComplete(): boolean {
    return this.omega.every((c) => !at(this.table, c).includes(null));
  }

  /** @internal SymPy define(alpha, x, modified) with x a column. */
  defineCol(alpha: number, x: number, modified = false): void {
    const table = this.table;
    const len = table.length;
    if (len >= this.cosetTableLimit) throw new CosetLimitExceeded(this.cosetTableLimit);
    table.push(this.#emptyRow());
    this.P.push(this.#emptyRow());
    const beta = len;
    this.p.push(beta);
    at(table, alpha)[x] = beta;
    at(table, beta)[x ^ 1] = alpha;
    if (modified) {
      at(this.P, alpha)[x] = this.grp.identity;
      at(this.P, beta)[x ^ 1] = this.grp.identity;
      this.pP.set(beta, this.grp.identity);
    }
  }

  /** SymPy define(alpha, x, modified): define a new coset alpha^x. */
  define(alpha: number, x: FreeGroupElement, modified = false): void {
    this.defineCol(alpha, this.#col(x), modified);
  }

  /** @internal SymPy define_c(alpha, x) with x a column. */
  defineCCol(alpha: number, x: number): void {
    const table = this.table;
    const len = table.length;
    if (len >= this.cosetTableLimit) throw new CosetLimitExceeded(this.cosetTableLimit);
    table.push(this.#emptyRow());
    const beta = len;
    this.p.push(beta);
    at(table, alpha)[x] = beta;
    at(table, beta)[x ^ 1] = alpha;
    this.deductionStack.push([alpha, x]);
  }

  /** SymPy define_c(alpha, x): define a new coset for the Felsch strategy. */
  defineC(alpha: number, x: FreeGroupElement): void {
    this.defineCCol(alpha, this.#col(x));
  }

  #entry(f: number, x: number): number | null {
    return at(at(this.table, f), x);
  }

  /** SymPy scan_c(alpha, word): scan word under the Felsch strategy. */
  scanC(alpha: number, word: FreeGroupElement): void {
    const w = word.letters.map(column);
    const table = this.table;
    let f = alpha;
    let i = 0;
    let b = alpha;
    let j = w.length - 1;
    let t: number | null;
    while (i <= j && (t = this.#entry(f, at(w, i))) !== null) {
      f = t;
      i++;
    }
    if (i > j) {
      if (f !== b) this.coincidenceC(f, b);
      return;
    }
    while (j >= i && (t = this.#entry(b, at(w, j) ^ 1)) !== null) {
      b = t;
      j--;
    }
    if (j < i) this.coincidenceC(f, b);
    else if (j === i) {
      at(table, f)[at(w, i)] = b;
      at(table, b)[at(w, i) ^ 1] = f;
      this.deductionStack.push([f, at(w, i)]);
    }
  }

  /** SymPy coincidence_c(alpha, beta): process the coincidence of two cosets (Felsch strategy). */
  coincidenceC(alpha: number, beta: number): void {
    const table = this.table;
    const q: number[] = [];
    this.merge(alpha, beta, q);
    while (q.length > 0) {
      const gamma = defined(q.shift(), 'queue');
      for (let x = 0; x < this.A.length; x++) {
        const delta = at(at(table, gamma), x);
        if (delta !== null) {
          at(table, delta)[x ^ 1] = null;
          this.deductionStack.push([delta, x ^ 1]);
          const mu = this.rep(gamma);
          const nu = this.rep(delta);
          const tm = at(at(table, mu), x);
          const tn = at(at(table, nu), x ^ 1);
          if (tm !== null) this.merge(nu, tm, q);
          else if (tn !== null) this.merge(mu, tn, q);
          else {
            at(table, mu)[x] = nu;
            at(table, nu)[x ^ 1] = mu;
          }
        }
      }
    }
  }

  /** @internal SymPy scan(alpha, word, y, fill, modified) on the columns of a word. */
  scanCols(alpha: number, w: readonly number[], y?: FreeGroupElement, fill = false, modified = false): void {
    const table = this.table;
    const P = this.P;
    let f = alpha;
    let i = 0;
    let b = alpha;
    let j = w.length - 1;
    let bP = y;
    let fP = this.grp.identity;
    let flag = false;
    let t: number | null;
    while (fill || !flag) {
      flag = true;
      while (i <= j && (t = this.#entry(f, at(w, i))) !== null) {
        if (modified) fP = fP.mul(defined(at(at(P, f), at(w, i)), 'P entry'));
        f = t;
        i++;
      }
      if (i > j) {
        if (f !== b) {
          if (modified) this.modifiedCoincidence(f, b, fP.inverse().mul(defined(y, 'y')));
          else this.coincidence(f, b);
        }
        return;
      }
      while (j >= i && (t = this.#entry(b, at(w, j) ^ 1)) !== null) {
        if (modified) bP = defined(bP, 'y').mul(defined(at(at(P, b), at(w, j) ^ 1), 'P entry'));
        b = t;
        j--;
      }
      if (j < i) {
        if (modified) this.modifiedCoincidence(f, b, fP.inverse().mul(defined(bP, 'y')));
        else this.coincidence(f, b);
      } else if (j === i) {
        at(table, f)[at(w, i)] = b;
        at(table, b)[at(w, i) ^ 1] = f;
        if (modified) {
          const bp = defined(bP, 'y');
          at(P, f)[at(w, i)] = fP.inverse().mul(bp);
          at(P, b)[at(w, i) ^ 1] = bp.inverse().mul(fP);
        }
        return;
      } else if (fill) this.defineCol(f, at(w, i), modified);
    }
  }

  /** SymPy scan(alpha, word, y, fill, modified): scan word from coset alpha (HLT strategy). */
  scan(alpha: number, word: FreeGroupElement, y?: FreeGroupElement, fill = false, modified = false): void {
    this.scanCols(alpha, word.letters.map(column), y, fill, modified);
  }

  /** SymPy scan_check(alpha, word): scan without defining cosets; false on an incompatibility. */
  scanCheck(alpha: number, word: FreeGroupElement): boolean {
    const w = word.letters.map(column);
    const table = this.table;
    let f = alpha;
    let i = 0;
    let b = alpha;
    let j = w.length - 1;
    let t: number | null;
    while (i <= j && (t = this.#entry(f, at(w, i))) !== null) {
      f = t;
      i++;
    }
    if (i > j) return f === b;
    while (j >= i && (t = this.#entry(b, at(w, j) ^ 1)) !== null) {
      b = t;
      j--;
    }
    if (j < i) return false;
    if (j === i) {
      at(table, f)[at(w, i)] = b;
      at(table, b)[at(w, i) ^ 1] = f;
    }
    return true;
  }

  /** SymPy merge(k, lamda, q, w, modified): merge the classes of two cosets. */
  merge(k: number, lamda: number, q: number[], w?: FreeGroupElement, modified = false): void {
    const phi = this.rep(k, modified);
    const psi = this.rep(lamda, modified);
    if (phi !== psi) {
      const mu = Math.min(phi, psi);
      const v = Math.max(phi, psi);
      this.p[v] = mu;
      if (modified) {
        const ww = defined(w, 'w');
        if (v === phi) this.pP.set(phi, this.#pp(k).inverse().mul(ww).mul(this.#pp(lamda)));
        else this.pP.set(psi, this.#pp(lamda).inverse().mul(ww.inverse()).mul(this.#pp(k)));
      }
      q.push(v);
    }
  }

  #pp(k: number): FreeGroupElement {
    return defined(this.pP.get(k), 'p_p entry');
  }

  /** SymPy rep(k, modified): the representative of the class of k, compressing the path. */
  rep(k: number, modified = false): number {
    const p = this.p;
    let lamda = k;
    let rho = at(p, lamda);
    const s = modified ? [...p] : [];
    while (rho !== lamda) {
      if (modified) s[rho] = lamda;
      lamda = rho;
      rho = at(p, lamda);
    }
    if (modified) {
      rho = at(s, lamda);
      while (rho !== k) {
        const mu = rho;
        rho = at(s, mu);
        p[rho] = lamda;
        this.pP.set(rho, this.#pp(rho).mul(this.#pp(mu)));
      }
    } else {
      let mu = k;
      rho = at(p, mu);
      while (rho !== lamda) {
        p[mu] = lamda;
        mu = rho;
        rho = at(p, mu);
      }
    }
    return lamda;
  }

  /** SymPy coincidence(alpha, beta, w, modified): process the coincidence of two cosets (HLT strategy). */
  coincidence(alpha: number, beta: number, w?: FreeGroupElement, modified = false): void {
    const table = this.table;
    const P = this.P;
    const q: number[] = [];
    if (modified) this.modifiedMerge(alpha, beta, defined(w, 'w'), q);
    else this.merge(alpha, beta, q);
    const pe = (r: number, x: number): FreeGroupElement => defined(at(at(P, r), x), 'P entry');
    while (q.length > 0) {
      const gamma = defined(q.shift(), 'queue');
      for (let x = 0; x < this.A.length; x++) {
        const delta = at(at(table, gamma), x);
        if (delta === null) continue;
        at(table, delta)[x ^ 1] = null;
        const mu = this.rep(gamma, modified);
        const nu = this.rep(delta, modified);
        const tm = at(at(table, mu), x);
        const tn = at(at(table, nu), x ^ 1);
        if (tm !== null) {
          if (modified) {
            const v = this.#pp(delta).inverse().mul(pe(gamma, x).inverse()).mul(this.#pp(gamma)).mul(pe(mu, x));
            this.modifiedMerge(nu, tm, v, q);
          } else this.merge(nu, tm, q);
        } else if (tn !== null) {
          if (modified) {
            const v = this.#pp(gamma).inverse().mul(pe(gamma, x)).mul(this.#pp(delta)).mul(pe(mu, x ^ 1));
            this.modifiedMerge(mu, tn, v, q);
          } else this.merge(mu, tn, q);
        } else {
          at(table, mu)[x] = nu;
          at(table, nu)[x ^ 1] = mu;
          if (modified) {
            const v = this.#pp(gamma).inverse().mul(pe(gamma, x)).mul(this.#pp(delta));
            at(P, mu)[x] = v;
            at(P, nu)[x ^ 1] = v.inverse();
          }
        }
      }
    }
  }

  /** SymPy scan_and_fill(alpha, word): scan word, defining cosets where the scan stops. */
  scanAndFill(alpha: number, word: FreeGroupElement): void {
    this.scan(alpha, word, undefined, true);
  }

  /** SymPy scan_and_fill_c(alpha, word): scan and fill under the Felsch strategy. */
  scanAndFillC(alpha: number, word: FreeGroupElement): void {
    const w = word.letters.map(column);
    const table = this.table;
    let f = alpha;
    let i = 0;
    let b = alpha;
    let j = w.length - 1;
    let t: number | null;
    for (;;) {
      while (i <= j && (t = this.#entry(f, at(w, i))) !== null) {
        f = t;
        i++;
      }
      if (i > j) {
        if (f !== b) this.coincidenceC(f, b);
        return;
      }
      while (j >= i && (t = this.#entry(b, at(w, j) ^ 1)) !== null) {
        b = t;
        j--;
      }
      if (j < i) this.coincidenceC(f, b);
      else if (j === i) {
        at(table, f)[at(w, i)] = b;
        at(table, b)[at(w, i) ^ 1] = f;
        this.deductionStack.push([f, at(w, i)]);
      } else this.defineCCol(f, at(w, i));
    }
  }

  /** SymPy look_ahead(): scan every relator from every live coset. */
  lookAhead(): void {
    const R = this.fpGroup.relators;
    const p = this.p;
    for (const beta of this.omega) {
      for (const w of R) {
        this.scan(beta, w);
        if (at(p, beta) < beta) break;
      }
    }
  }

  /** SymPy process_deductions(R_c_x, R_c_x_inv): process the deduction stack (Felsch strategy). */
  processDeductions(RcX: readonly FreeGroupElement[], RcXInv: readonly FreeGroupElement[]): void {
    const p = this.p;
    const table = this.table;
    while (this.deductionStack.length > 0) {
      let alpha: number;
      let x: number;
      if (this.deductionStack.length >= CosetTable.maxStackSize) {
        this.lookAhead();
        this.deductionStack.length = 0;
        continue;
      } else {
        [alpha, x] = defined(this.deductionStack.pop(), 'deduction');
        if (at(this.p, alpha) === alpha) {
          for (const w of RcX) {
            this.scanC(alpha, w);
            if (at(this.p, alpha) < alpha) break;
          }
        }
      }
      const beta = at(at(table, alpha), x);
      if (beta !== null && at(p, beta) === beta) {
        for (const w of RcXInv) {
          this.scanC(beta, w);
          if (at(this.p, beta) < beta) break;
        }
      }
    }
  }

  /** SymPy process_deductions_check(R_c_x, R_c_x_inv): check the deductions without defining cosets. */
  processDeductionsCheck(RcX: readonly FreeGroupElement[], RcXInv: readonly FreeGroupElement[]): boolean {
    const table = this.table;
    while (this.deductionStack.length > 0) {
      const [alpha, x] = defined(this.deductionStack.pop(), 'deduction');
      if (!RcX.every((w) => this.scanCheck(alpha, w))) return false;
      const beta = at(at(table, alpha), x);
      if (beta !== null && !RcXInv.every((w) => this.scanCheck(beta, w))) return false;
    }
    return true;
  }

  /** SymPy switch(beta, gamma): interchange two cosets. */
  switch(beta: number, gamma: number): void {
    const table = this.table;
    for (let x = 0; x < this.A.length; x++) {
      const z = at(at(table, gamma), x);
      at(table, gamma)[x] = at(at(table, beta), x);
      at(table, beta)[x] = z;
      for (let alpha = 0; alpha < this.p.length; alpha++) {
        if (at(this.p, alpha) !== alpha) continue;
        const row = at(table, alpha);
        if (row[x] === beta) row[x] = gamma;
        else if (row[x] === gamma) row[x] = beta;
      }
    }
  }

  /** SymPy standardize(): renumber the cosets in the standard order (a complete, compressed table). */
  standardize(): void {
    let gamma = 1;
    const n = this.n;
    for (let alpha = 0; alpha < n; alpha++) {
      for (let x = 0; x < this.A.length; x++) {
        const beta = at(at(this.table, alpha), x);
        if (beta !== null && beta >= gamma) {
          if (beta > gamma) this.switch(gamma, beta);
          gamma++;
          if (gamma === n) return;
        }
      }
    }
  }

  /** SymPy compress(): remove the dead cosets and renumber the live ones. */
  compress(): void {
    let gamma = -1;
    const table = this.table;
    const chi = this.p.flatMap((c, i) => (c !== i ? [i] : []));
    for (const alpha of this.omega) {
      gamma++;
      if (gamma !== alpha) for (let x = 0; x < this.A.length; x++) at(table, gamma)[x] = at(at(table, alpha), x);
    }
    this.p = Array.from({ length: gamma + 1 }, (_, i) => i);
    table.length = this.p.length;
    for (const row of table) {
      for (let j = 0; j < this.A.length; j++) {
        const v = at(row, j);
        if (v !== null) row[j] = v - bisectLeft(chi, v);
      }
    }
  }

  /** SymPy conjugates(R): the cyclic conjugates of the relators and their inverses, by first letter. */
  conjugates(R: Iterable<FreeGroupElement>): FreeGroupElement[][] {
    return conjugatesByLetter(this.A, R);
  }

  /** SymPy coset_representative(coset): a word leading from the subgroup's coset 0 to this coset (standardized table). */
  cosetRepresentative(coset: number): FreeGroupElement {
    for (let x = 0; x < this.A.length; x++) {
      const gamma = at(at(this.table, coset), x);
      if (coset === 0) return this.fpGroup.identity;
      if (gamma !== null && gamma < coset) return this.cosetRepresentative(gamma).mul(at(this.A, x).inverse());
    }
    throw new RangeError(`no representative of coset ${coset}: the table is not standardized`);
  }

  /** SymPy modified_define(alpha, x). */
  modifiedDefine(alpha: number, x: FreeGroupElement): void {
    this.define(alpha, x, true);
  }

  /** SymPy modified_scan(alpha, w, y, fill). */
  modifiedScan(alpha: number, w: FreeGroupElement, y: FreeGroupElement, fill = false): void {
    this.scan(alpha, w, y, fill, true);
  }

  /** SymPy modified_scan_and_fill(alpha, w, y). */
  modifiedScanAndFill(alpha: number, w: FreeGroupElement, y: FreeGroupElement): void {
    this.modifiedScan(alpha, w, y, true);
  }

  /** SymPy modified_merge(k, lamda, w, q). */
  modifiedMerge(k: number, lamda: number, w: FreeGroupElement, q: number[]): void {
    this.merge(k, lamda, q, w, true);
  }

  /** SymPy modified_rep(k). */
  modifiedRep(k: number): void {
    this.rep(k, true);
  }

  /** SymPy modified_coincidence(alpha, beta, w). */
  modifiedCoincidence(alpha: number, beta: number, w: FreeGroupElement): void {
    this.coincidence(alpha, beta, w, true);
  }
}

/** Python's str of a list of words. */
export const listStr = (items: readonly unknown[]): string => `[${items.map(String).join(', ')}]`;

/** The cyclic conjugates of the relators and of their inverses, grouped by the letter they start with (SymPy CosetTable.conjugates). */
export function conjugatesByLetter(A: readonly FreeGroupElement[], R: Iterable<FreeGroupElement>): FreeGroupElement[][] {
  const all = uniqueWords([...R].flatMap((rel) => [...rel.cyclicConjugates(), ...rel.inverse().cyclicConjugates()]));
  const remaining = new Map(all.map((w) => [w.key, w]));
  return A.map((x) => {
    const r = [...remaining.values()].filter((w) => w.length > 0 && w.getItem(0).equals(x));
    for (const w of r) remaining.delete(w.key);
    return r;
  });
}

/** Options of the coset enumerations. */
export interface CosetEnumerationOptions {
  /** The maximum number of cosets (default CosetTable.cosetTableMaxLimit). */
  maxCosets?: number;
  /** A partial coset table to continue from. */
  draft?: CosetTable;
  /** Return the incomplete table when the maximum is reached instead of throwing. */
  incomplete?: boolean;
  /** Track the subgroup generators (SymPy modified_coset_enumeration_r). */
  modified?: boolean;
}

/**
 * SymPy coset_enumeration_r(fp_grp, Y, max_cosets, draft, incomplete,
 * modified): the coset table of the subgroup generated by Y, by the
 * relator-based (HLT) strategy.
 */
export function cosetEnumerationR(fpGroup: CosetGroup, Y: readonly FreeGroupElement[], opts: CosetEnumerationOptions = {}): CosetTable {
  const { maxCosets, draft, incomplete = false, modified = false } = opts;
  const C = new CosetTable(fpGroup, Y, maxCosets);
  if (draft) {
    // SymPy copies the list of rows (the rows are shared with the draft)
    C.table = [...draft.table];
    C.p = [...draft.p];
  }
  const R = fpGroup.relators.map((w) => w.letters.map(column));
  const p = C.p;
  const fill = (alpha: number, w: readonly number[], y?: FreeGroupElement): void => C.scanCols(alpha, w, y, true, modified);
  Y.forEach((y, i) => fill(0, y.letters.map(column), modified ? at(C.grp.generators, i) : undefined));
  let alpha = 0;
  while (alpha < C.n) {
    if (at(p, alpha) === alpha) {
      try {
        for (const w of R) {
          fill(alpha, w, modified ? C.grp.identity : undefined);
          if (at(p, alpha) < alpha) break;
        }
        if (at(p, alpha) === alpha) {
          for (let x = 0; x < C.A.length; x++) if ((at(at(C.table, alpha), x)) === null) C.defineCol(alpha, x, modified);
        }
      } catch (e) {
        if (e instanceof CosetLimitExceeded && incomplete) return C;
        throw e;
      }
    }
    alpha++;
  }
  return C;
}

/** SymPy modified_coset_enumeration_r(fp_grp, Y, max_cosets, draft, incomplete). */
export function modifiedCosetEnumerationR(fpGroup: CosetGroup, Y: readonly FreeGroupElement[], opts: Omit<CosetEnumerationOptions, 'modified'> = {}): CosetTable {
  return cosetEnumerationR(fpGroup, Y, { ...opts, modified: true });
}

/**
 * SymPy coset_enumeration_c(fp_grp, Y, max_cosets, draft, incomplete): the
 * coset table of the subgroup generated by Y, by the coset-table-based
 * (Felsch) strategy.
 */
export function cosetEnumerationC(fpGroup: CosetGroup, Y: readonly FreeGroupElement[], opts: Omit<CosetEnumerationOptions, 'modified'> = {}): CosetTable {
  const { maxCosets, draft, incomplete = false } = opts;
  const X = fpGroup.generators;
  const C = new CosetTable(fpGroup, Y, maxCosets);
  if (draft) {
    C.table = [...draft.table];
    C.p = [...draft.p];
    C.deductionStack = draft.deductionStack;
    for (let alpha = 0; alpha < C.table.length; alpha++) {
      for (let i = 0; i < X.length; i++) if ((at(at(C.table, alpha), 2 * i)) !== null) C.deductionStack.push([alpha, 2 * i]);
    }
  }
  const RcList = conjugatesByLetter(C.A, fpGroup.relators.map((rel) => rel.identityCyclicReduction()));
  for (const w of Y) C.scanAndFillC(0, w);
  for (let x = 0; x < C.A.length; x++) C.processDeductions(at(RcList, x), at(RcList, x ^ 1));
  let alpha = 0;
  while (alpha < C.table.length) {
    if (at(C.p, alpha) === alpha) {
      try {
        for (let x = 0; x < C.A.length; x++) {
          if (at(C.p, alpha) !== alpha) break;
          if ((at(at(C.table, alpha), x)) === null) {
            C.defineCCol(alpha, x);
            C.processDeductions(at(RcList, x), at(RcList, x ^ 1));
          }
        }
      } catch (e) {
        if (e instanceof CosetLimitExceeded && incomplete) return C;
        throw e;
      }
    }
    alpha++;
  }
  return C;
}
