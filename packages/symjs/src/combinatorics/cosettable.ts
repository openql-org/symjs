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
  /** The generators in their defining order. */
  readonly generators: readonly FreeGroupElement[];
  /** The words imposed as defining relations. */
  readonly relators: readonly FreeGroupElement[];
  /** The identity. */
  readonly identity: FreeGroupElement;
  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string;
}

/** The cosets reached by applying each generator or inverse to one coset. An unfilled entry is `null`. */
export type CosetRow = (number | null)[];

/** Signals that a coset enumeration has reached its coset limit. */
export class CosetLimitExceeded extends RangeError {
  /**
   * Constructs a `CosetLimitExceeded`.
   * @param limit - The maximum number of cosets or rules permitted.
   */
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
 * The coset table of a
 * subgroup of a finitely presented group, built by coset enumeration.
 * Columns are the generators and their inverses in the order of A.
 * @see SymPy `sympy.combinatorics.coset_table.CosetTable`
 */
export class CosetTable {
  /**
   * The default maximum number of cosets.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.coset_table_max_limit`
   */
  static cosetTableMaxLimit = 4096000;
  /**
   * The deduction stack size that triggers a look-ahead.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.max_stack_size`
   */
  static maxStackSize = 100;
  /**
   * The finitely presented group whose cosets are enumerated.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.fp_group`
   */
  readonly fpGroup: CosetGroup;
  /**
   * The generators of the subgroup whose cosets are enumerated.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.subgroup`
   */
  readonly subgroup: readonly FreeGroupElement[];
  /**
   * The maximum number of cosets allowed in this table.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.coset_table_limit`
   */
  readonly cosetTableLimit: number;
  /**
   * The coset each coset is equivalent to (p[i] = i for a live coset).
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.p`
   */
  p: number[];
  /**
   * The generators and their inverses.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.A`
   */
  readonly A: FreeGroupElement[];
  /**
   * The transition rows indexed by coset and generator letter.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.table`
   */
  table: CosetRow[];
  /**
   * The subgroup words of the modified enumeration.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.P`
   */
  P: (FreeGroupElement | null)[][];
  /**
   * The (coset, letter column) deductions to process.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.deduction_stack`
   */
  deductionStack: [number, number][];
  /** The free group on the subgroup generators (a_0, a_1, ...). @internal */
  readonly grp: FreeGroup;
  /** The subgroup words of the coincident cosets. @internal */
  pP: Map<number, FreeGroupElement>;
  /** The free generators and relators discovered during subgroup rewriting. @internal */
  schreier: {
    freeGroup?: FreeGroup;
    generators?: FreeGroupElement[];
    genElements?: Map<string, FreeGroupElement>;
    relators?: FreeGroupElement[];
  } = {};
  /** The Schreier generators obtained from the coset representatives. */
  schreierGenerators: FreeGroupElement[] = [];
  /** The relators of the subgroup presentation. */
  reidemeisterRelators: FreeGroupElement[] = [];

  /**
   * Constructs a `CosetTable`.
   * @param fpGroup - The finitely presented group being enumerated.
   * @param subgroup - Generators of the subgroup.
   * @param maxCosets - The maximum number of cosets to define.
   */
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

  /**
   * Gets the column of each letter.
   * @returns The column of each letter.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.A_dict`
   */
  get ADict(): Map<FreeGroupElement, number> {
    return new Map(this.A.map((x, i) => [x, i]));
  }

  /**
   * Gets the column of each letter's inverse.
   * @returns The column of each letter's inverse.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.A_dict_inv`
   */
  get ADictInv(): Map<FreeGroupElement, number> {
    return new Map(this.A.map((x, i) => [x, i ^ 1]));
  }

  /**
   * Gets the live cosets.
   * @returns The live cosets.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.omega`
   */
  get omega(): number[] {
    return this.p.flatMap((c, i) => (c === i ? [i] : []));
  }

  /**
   * Returns a copy of the table, p and the deduction stack.
   * @returns A copy of the table, p and the deduction stack.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.copy`
   */
  copy(): CosetTable {
    const c = new CosetTable(this.fpGroup, this.subgroup);
    c.table = this.table.map((r) => [...r]);
    c.p = [...this.p];
    c.deductionStack = [...this.deductionStack];
    return c;
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return `Coset Table on ${String(this.fpGroup)} with ${listStr(this.subgroup)} as subgroup generators`;
  }

  /**
   * Gets the number of cosets, 1 + the largest live one.
   * @returns The number of cosets, 1 + the largest live one.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.n`
   */
  get n(): number {
    if (!this.table.length) return 0;
    return Math.max(...this.omega) + 1;
  }

  /**
   * Whether every live coset has all its entries.
   * @returns Whether the object is complete.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.is_complete`
   */
  isComplete(): boolean {
    return this.omega.every((c) => !at(this.table, c).includes(null));
  }

  /**
   * Defines a new coset as the image of the starting coset under the given generator column.
   * @param alpha - The starting coset label.
   * @param x - The column of the generator letter.
   * @param modified - Whether to record subgroup words during enumeration.
   * @throws CosetLimitExceeded when enumeration would exceed the coset limit.
   * @internal
   */
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

  /**
   * Define a new coset alpha^x.
   * @param alpha - The starting coset label.
   * @param x - The generator letter labeling the transition.
   * @param modified - Whether to record subgroup words during enumeration.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.define`
   */
  define(alpha: number, x: FreeGroupElement, modified = false): void {
    this.defineCol(alpha, this.#col(x), modified);
  }

  /**
   * Defines a new coset and records the transition for deduction processing.
   * @param alpha - The starting coset label.
   * @param x - The column of the generator letter.
   * @throws CosetLimitExceeded when enumeration would exceed the coset limit.
   * @internal
   */
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

  /**
   * Define a new coset for the Felsch strategy.
   * @param alpha - The starting coset label.
   * @param x - The generator letter labeling the transition.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.define_c`
   */
  defineC(alpha: number, x: FreeGroupElement): void {
    this.defineCCol(alpha, this.#col(x));
  }

  #entry(f: number, x: number): number | null {
    return at(at(this.table, f), x);
  }

  /**
   * Scan word under the Felsch strategy.
   * @param alpha - The starting coset label.
   * @param word - The group word to examine.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.scan_c`
   */
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

  /**
   * Process the coincidence of two cosets (Felsch strategy).
   * @param alpha - The starting coset label.
   * @param beta - The second coset label.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.coincidence_c`
   */
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

  /**
   * Scans a word expressed as generator columns from the given coset.
   * @param alpha - The starting coset label.
   * @param w - The group word to scan or rewrite.
   * @param y - The subgroup word associated with this scan.
   * @param fill - Whether to define cosets wherever the scan stops.
   * @param modified - Whether to record subgroup words during enumeration.
   * @internal
   */
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

  /**
   * Scan word from coset alpha (HLT strategy).
   * @param alpha - The starting coset label.
   * @param word - The group word to examine.
   * @param y - The subgroup word associated with this scan.
   * @param fill - Whether to define cosets wherever the scan stops.
   * @param modified - Whether to record subgroup words during enumeration.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.scan`
   */
  scan(alpha: number, word: FreeGroupElement, y?: FreeGroupElement, fill = false, modified = false): void {
    this.scanCols(alpha, word.letters.map(column), y, fill, modified);
  }

  /**
   * Scans a relator for deductions and detects inconsistent coset transitions.
   * @param alpha - The starting coset label.
   * @param word - The group word to examine.
   * @returns Whether the relator scan succeeded without a contradiction.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.scan_check`
   */
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

  /**
   * Merge the classes of two cosets.
   * @param k - The first coset label.
   * @param lamda - The second coset label.
   * @param q - The queue of coincident cosets to process.
   * @param w - The group word to scan or rewrite.
   * @param modified - Whether to record subgroup words during enumeration.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.merge`
   */
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

  /**
   * Returns the representative of the class of k, compressing the path.
   * @param k - The first coset label.
   * @param modified - Whether to record subgroup words during enumeration.
   * @returns The representative of the class of k, compressing the path.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.rep`
   */
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

  /**
   * Process the coincidence of two cosets (HLT strategy).
   * @param alpha - The starting coset label.
   * @param beta - The second coset label.
   * @param w - The group word to scan or rewrite.
   * @param modified - Whether to record subgroup words during enumeration.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.coincidence`
   */
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

  /**
   * Scan word, defining cosets where the scan stops.
   * @param alpha - The starting coset label.
   * @param word - The group word to examine.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.scan_and_fill`
   */
  scanAndFill(alpha: number, word: FreeGroupElement): void {
    this.scan(alpha, word, undefined, true);
  }

  /**
   * Scan and fill under the Felsch strategy.
   * @param alpha - The starting coset label.
   * @param word - The group word to examine.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.scan_and_fill_c`
   */
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

  /**
   * Scan every relator from every live coset.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.look_ahead`
   */
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

  /**
   * Process the deduction stack (Felsch strategy).
   * @param RcX - Relator conjugates starting with the deduction letter.
   * @param RcXInv - Relator conjugates starting with the inverse letter.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.process_deductions`
   */
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

  /**
   * Check the deductions without defining cosets.
   * @param RcX - Relator conjugates starting with the deduction letter.
   * @param RcXInv - Relator conjugates starting with the inverse letter.
   * @returns Whether all pending deductions are consistent with the relators.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.process_deductions_check`
   */
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

  /**
   * Interchange two cosets.
   * @param beta - The second coset label.
   * @param gamma - The coset label to identify.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.switch`
   */
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

  /**
   * Renumber the cosets in the standard order (a complete, compressed table).
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.standardize`
   */
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

  /**
   * Remove the dead cosets and renumber the live ones.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.compress`
   */
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

  /**
   * The cyclic conjugates of the relators and their inverses, by first letter.
   * @param R - The relators whose cyclic conjugates are required.
   * @returns The resulting group elements.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.conjugates`
   */
  conjugates(R: Iterable<FreeGroupElement>): FreeGroupElement[][] {
    return conjugatesByLetter(this.A, R);
  }

  /**
   * A word leading from the subgroup's coset 0 to this coset (standardized table).
   * @param coset - The coset label whose representative is sought.
   * @returns The resulting group word.
   * @throws RangeError when the table has no standardized representative for the coset.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.coset_representative`
   */
  cosetRepresentative(coset: number): FreeGroupElement {
    for (let x = 0; x < this.A.length; x++) {
      const gamma = at(at(this.table, coset), x);
      if (coset === 0) return this.fpGroup.identity;
      if (gamma !== null && gamma < coset) return this.cosetRepresentative(gamma).mul(at(this.A, x).inverse());
    }
    throw new RangeError(`no representative of coset ${coset}: the table is not standardized`);
  }

  /**
   * Define a function p_p from from [1..n] to A* as an additional component of the modified coset table.
   * @param alpha - The starting coset label.
   * @param x - The generator letter labeling the transition.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_define`
   */
  modifiedDefine(alpha: number, x: FreeGroupElement): void {
    this.define(alpha, x, true);
  }

  /**
   * Scans a word while tracking subgroup words on the coset transitions.
   * @param alpha - The starting coset label.
   * @param w - The group word to scan or rewrite.
   * @param y - The subgroup word associated with this scan.
   * @param fill - Whether to define cosets wherever the scan stops.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_scan`
   */
  modifiedScan(alpha: number, w: FreeGroupElement, y: FreeGroupElement, fill = false): void {
    this.scan(alpha, w, y, fill, true);
  }

  /**
   * Scans the relator and fills missing cosets while tracking subgroup words.
   * @param alpha - The starting coset label.
   * @param w - The group word to scan or rewrite.
   * @param y - The subgroup word associated with this scan.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_scan_and_fill`
   */
  modifiedScanAndFill(alpha: number, w: FreeGroupElement, y: FreeGroupElement): void {
    this.modifiedScan(alpha, w, y, true);
  }

  /**
   * Parameters ==========.
   * @param k - The first coset label.
   * @param lamda - The second coset label.
   * @param w - The group word to scan or rewrite.
   * @param q - The queue of coincident cosets to process.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_merge`
   */
  modifiedMerge(k: number, lamda: number, w: FreeGroupElement, q: number[]): void {
    this.merge(k, lamda, q, w, true);
  }

  /**
   * Parameters ==========.
   * @param k - The first coset label.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_rep`
   */
  modifiedRep(k: number): void {
    this.rep(k, true);
  }

  /**
   * Parameters ==========.
   * @param alpha - The starting coset label.
   * @param beta - The second coset label.
   * @param w - The group word to scan or rewrite.
   * @see SymPy `sympy.combinatorics.coset_table.CosetTable.modified_coincidence`
   */
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
  /** Track the subgroup generators. */
  modified?: boolean;
}

/**
 * Enumerates right cosets by scanning the presentation relators.
 * @param fpGroup - The finitely presented group being enumerated.
 * @param Y - Generators required to lie in the subgroup.
 * @param opts - The settings described by {@link CosetEnumerationOptions}.
 * @returns The enumerated coset table.
 * @throws CosetLimitExceeded when enumeration reaches the coset limit and an incomplete table was not requested.
 * @see SymPy `sympy.combinatorics.coset_table.coset_enumeration_r`
 * @example
 * ```ts
 * import { FpGroup, cosetEnumerationR, freeGroup } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * cosetEnumerationR(G, []).table; // => [[1, 2], [2, 0], [0, 1]]
 * ```
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

/**
 * Enumerates right cosets using relators and records the subgroup words for each transition.
 * @param fpGroup - The finitely presented group being enumerated.
 * @param Y - Generators required to lie in the subgroup.
 * @param opts - The enumeration limit, starting table and handling of incomplete enumeration.
 * @returns The coset table with its subgroup words.
 * @throws CosetLimitExceeded when enumeration reaches the coset limit and an incomplete table was not requested.
 * @see SymPy `sympy.combinatorics.coset_table.modified_coset_enumeration_r`
 * @example
 * ```ts
 * import { FpGroup, freeGroup, modifiedCosetEnumerationR } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * modifiedCosetEnumerationR(G, []).table; // => [[1, 2], [2, 0], [0, 1]]
 * ```
 */
export function modifiedCosetEnumerationR(fpGroup: CosetGroup, Y: readonly FreeGroupElement[], opts: Omit<CosetEnumerationOptions, 'modified'> = {}): CosetTable {
  return cosetEnumerationR(fpGroup, Y, { ...opts, modified: true });
}

/**
 * Enumerates right cosets by filling the coset table and processing deductions.
 * @param fpGroup - The finitely presented group being enumerated.
 * @param Y - Generators required to lie in the subgroup.
 * @param opts - The enumeration limit, starting table and handling of incomplete enumeration.
 * @returns The enumerated coset table.
 * @throws CosetLimitExceeded when enumeration reaches the coset limit and an incomplete table was not requested.
 * @see SymPy `sympy.combinatorics.coset_table.coset_enumeration_c`
 * @example
 * ```ts
 * import { FpGroup, cosetEnumerationC, freeGroup } from '@symjs/symjs';
 *
 * const [F, x] = freeGroup('x');
 * const G = new FpGroup(F, [x.pow(3)]);
 * cosetEnumerationC(G, []).table; // => [[1, 2], [2, 0], [0, 1]]
 * ```
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
