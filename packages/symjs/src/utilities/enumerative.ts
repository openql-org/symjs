// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of the parts of SymPy's `sympy.utilities.enumerative` used by
 * `multiset_partitions`: Knuth's Algorithm 7.1.2.5M (`multiset_partitions_taocp`),
 * the range-restricted traversal (`MultisetPartitionTraverser.enum_range`)
 * and `list_visitor`.
 */

import { at } from '../core/guard';

/** One component of one part of the current partition (SymPy PartComponent). */
export class PartComponent {
  /** Component number. */
  c = 0;
  /** The as yet unpartitioned amount in component c before this triple. */
  u = 0;
  /** Amount of the c component in the current part (v <= u). */
  v = 0;

  toString(): string {
    return `c:${this.c} u:${this.u} v:${this.v}`;
  }
}

/** The state of a partition enumeration: frame array f, index of the last part and the stack. */
export type PartitionState = readonly [f: number[], lpart: number, pstack: PartComponent[]];

/**
 * SymPy `multiset_partitions_taocp(multiplicities)`: enumerate the
 * partitions of a multiset with the given multiplicities (the state is
 * reused between steps; decode it with {@link listVisitor}).
 */
export function* multisetPartitionsTaocp(multiplicities: readonly number[]): Generator<PartitionState, void, undefined> {
  const m = multiplicities.length;
  const n = multiplicities.reduce((a, b) => a + b, 0);
  const pstack = Array.from({ length: n * m + 1 }, () => new PartComponent());
  const f: number[] = new Array<number>(n + 1).fill(0);
  for (let j = 0; j < m; j++) {
    const ps = at(pstack, j);
    ps.c = j;
    ps.u = at(multiplicities, j);
    ps.v = at(multiplicities, j);
  }
  f[0] = 0;
  let a = 0;
  let lpart = 0;
  f[1] = m;
  let b = m;
  for (;;) {
    for (;;) {
      // M2: subtract v from u
      let k = b;
      let x = false;
      for (let j = a; j < b; j++) {
        const pk = at(pstack, k);
        const pj = at(pstack, j);
        pk.u = pj.u - pj.v;
        if (pk.u === 0) {
          x = true;
        } else if (!x) {
          pk.c = pj.c;
          pk.v = Math.min(pj.v, pk.u);
          x = pk.u < pj.v;
          k++;
        } else {
          pk.c = pj.c;
          pk.v = pk.u;
          k++;
        }
      }
      // M3: push if nonzero
      if (k > b) {
        a = b;
        b = k;
        lpart++;
        f[lpart + 1] = b;
      } else {
        break;
      }
    }
    // M4: visit a partition
    yield [f, lpart, pstack];
    // M5: decrease v
    for (;;) {
      let j = b - 1;
      while (at(pstack, j).v === 0) j--;
      if (j === a && at(pstack, j).v === 1) {
        // M6: backtrack
        if (lpart === 0) return;
        lpart--;
        b = a;
        a = at(f, lpart);
      } else {
        at(pstack, j).v -= 1;
        for (let k = j + 1; k < b; k++) at(pstack, k).v = at(pstack, k).u;
        break;
      }
    }
  }
}

/** SymPy `list_visitor(state, components)`: the partition as a list of lists. */
export function listVisitor<T>(state: PartitionState, components: readonly T[]): T[][] {
  const [f, lpart, pstack] = state;
  const partition: T[][] = [];
  for (let i = 0; i <= lpart; i++) {
    const part: T[] = [];
    for (let s = at(f, i); s < at(f, i + 1); s++) {
      const ps = at(pstack, s);
      for (let r = 0; r < ps.v; r++) part.push(at(components, ps.c));
    }
    partition.push(part);
  }
  return partition;
}

/** SymPy `MultisetPartitionTraverser` (the enumeration with a range of part counts). */
export class MultisetPartitionTraverser {
  pstack: PartComponent[] = [];
  f: number[] = [];
  lpart = 0;
  discarded = 0;

  private initializeEnumeration(multiplicities: readonly number[]): void {
    const numComponents = multiplicities.length;
    const cardinality = multiplicities.reduce((a, b) => a + b, 0);
    this.pstack = Array.from({ length: numComponents * cardinality + 1 }, () => new PartComponent());
    this.f = new Array<number>(cardinality + 1).fill(0);
    for (let j = 0; j < numComponents; j++) {
      const ps = at(this.pstack, j);
      ps.c = j;
      ps.u = at(multiplicities, j);
      ps.v = at(multiplicities, j);
    }
    this.f[0] = 0;
    this.f[1] = numComponents;
    this.lpart = 0;
  }

  /** Decrement the part like a multi-digit number whose leading digit stays positive. */
  decrementPart(part: readonly PartComponent[]): boolean {
    const plen = part.length;
    for (let j = plen - 1; j >= 0; j--) {
      const pj = at(part, j);
      if ((j === 0 && pj.v > 1) || (j > 0 && pj.v > 0)) {
        pj.v -= 1;
        for (let k = j + 1; k < plen; k++) at(part, k).v = at(part, k).u;
        return true;
      }
    }
    return false;
  }

  /** Decrement, failing when the part can only have children with more than ub parts. */
  decrementPartSmall(part: readonly PartComponent[], ub: number): boolean {
    if (this.lpart >= ub - 1) return false;
    const plen = part.length;
    const p0 = at(part, 0);
    const decrement = (j: number): boolean => {
      at(part, j).v -= 1;
      for (let k = j + 1; k < plen; k++) at(part, k).v = at(part, k).u;
      return !(plen > 1 && at(part, 1).v === 0 && p0.u - p0.v === (ub - this.lpart - 1) * p0.v);
    };
    for (let j = plen - 1; j > 0; j--) if (at(part, j).v > 0) return decrement(j);
    if ((p0.v - 1) * (ub - this.lpart) < p0.u) return false;
    // here p0.v > 1, as p0.u >= 1 and ub - lpart >= 2 (SymPy also tests p0.v > 1 and returns False otherwise)
    return decrement(0);
  }

  /** Decrement (when amt is 1) and enforce that more than lb parts remain reachable. */
  decrementPartLarge(part: readonly PartComponent[], amt: number, lb: number): boolean {
    if (amt === 1 && !this.decrementPart(part)) return false;
    const minUnalloc = lb - this.lpart;
    if (minUnalloc <= 0) return true;
    let totalMult = 0;
    let totalAlloc = 0;
    for (const pc of part) {
      totalMult += pc.u;
      totalAlloc += pc.v;
    }
    if (totalMult <= minUnalloc) return false;
    let deficit = minUnalloc - (totalMult - totalAlloc);
    if (deficit <= 0) return true;
    for (let i = part.length - 1; i > 0; i--) {
      const pi = at(part, i);
      if (pi.v >= deficit) {
        pi.v -= deficit;
        return true;
      }
      deficit -= pi.v;
      pi.v = 0;
    }
    // the first component keeps (total allocation) - (initial deficit) = totalMult - minUnalloc > 0
    // (SymPy returns False here, "this shouldn't happen")
    at(part, 0).v -= deficit;
    return true;
  }

  /** Combination of the small and large decrements. */
  decrementPartRange(part: readonly PartComponent[], lb: number, ub: number): boolean {
    return this.decrementPartSmall(part, ub) && this.decrementPartLarge(part, 0, lb);
  }

  /** Spread the unallocated multiplicity of the top part into a new part. */
  spreadPartMultiplicity(): boolean {
    let k = at(this.f, this.lpart + 1);
    const base = k;
    let changed = false;
    for (let j = at(this.f, this.lpart); j < at(this.f, this.lpart + 1); j++) {
      const pk = at(this.pstack, k);
      const pj = at(this.pstack, j);
      pk.u = pj.u - pj.v;
      if (pk.u === 0) {
        changed = true;
      } else {
        pk.c = pj.c;
        if (changed) {
          pk.v = pk.u;
        } else if (pk.u < pj.v) {
          pk.v = pk.u;
          changed = true;
        } else {
          pk.v = pj.v;
        }
        k++;
      }
    }
    if (k > base) {
      this.lpart++;
      this.f[this.lpart + 1] = k;
      return true;
    }
    return false;
  }

  /** The current top part on the stack. */
  topPart(): PartComponent[] {
    return this.pstack.slice(this.f[this.lpart], this.f[this.lpart + 1]);
  }

  /** Enumerate the partitions of a multiset with lb < (number of parts) <= ub. */
  *enumRange(multiplicities: readonly number[], lb: number, ub: number): Generator<PartitionState, void, undefined> {
    this.discarded = 0;
    // no number of parts k with lb < k <= ub (SymPy raises IndexError for ub = 1 <= lb; symjs looped forever)
    if (ub <= 0 || lb >= ub || lb >= multiplicities.reduce((a, b) => a + b, 0)) return;
    this.initializeEnumeration(multiplicities);
    this.decrementPartLarge(this.topPart(), 0, lb);
    for (;;) {
      let good = true;
      while (this.spreadPartMultiplicity()) {
        // never fails (SymPy counts a failure as discarded): the spread part has all the elements its
        // parent left unallocated, at least lb - lpart + 1 of them, so more than lb - lpart
        this.decrementPartLarge(this.topPart(), 0, lb);
        if (this.lpart >= ub) {
          this.discarded++;
          good = false;
          this.lpart = ub - 2;
          break;
        }
      }
      if (good) yield [this.f, this.lpart, this.pstack];
      while (!this.decrementPartRange(this.topPart(), lb, ub)) {
        if (this.lpart === 0) return;
        this.lpart--;
      }
    }
  }
}
