// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The DPLL SAT solver of SymPy (sympy.logic.algorithms.dpll2): watched
 * literals, unit propagation and the VSIDS decision heuristic, enumerating
 * the models of a CNF given as clauses of signed variable numbers.
 */

/** Min-heap of [score, literal] pairs ordered like Python tuples. */
class LitHeap {
  private readonly items: [number, number][] = [];
  get size(): number {
    return this.items.length;
  }
  private static less(a: readonly [number, number], b: readonly [number, number]): boolean {
    return a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
  }
  peek(): [number, number] {
    return this.items[0]!;
  }
  push(x: [number, number]): void {
    const h = this.items;
    h.push(x);
    let i = h.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!LitHeap.less(h[i]!, h[p]!)) break;
      [h[i], h[p]] = [h[p]!, h[i]!];
      i = p;
    }
  }
  pop(): [number, number] {
    const h = this.items;
    const top = h[0]!;
    const last = h.pop()!;
    if (h.length) {
      h[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < h.length && LitHeap.less(h[l]!, h[m]!)) m = l;
        if (r < h.length && LitHeap.less(h[r]!, h[m]!)) m = r;
        if (m === i) break;
        [h[i], h[m]] = [h[m]!, h[i]!];
        i = m;
      }
    }
    return top;
  }
}

interface Level {
  decision: number;
  varSettings: Set<number>;
  flipped: boolean;
}

const level = (decision: number, flipped = false): Level => ({ decision, varSettings: new Set(), flipped });

/**
 * SymPy SATSolver (dpll2) without clause learning: `findModels` yields
 * every model as the set of true/false literals of variables 1..n.
 */
export class SATSolver {
  private readonly clauses: number[][];
  private readonly sentinels = new Map<number, Set<number>>();
  private readonly occurrence = new Map<number, number>();
  private readonly variableSet: boolean[];
  private readonly varSettings = new Set<number>();
  private unitQueue: number[] = [];
  private isUnsatisfied = false;
  private readonly levels: Level[] = [level(0)];
  private readonly heap = new LitHeap();
  private readonly scores = new Map<number, number>();

  constructor(clauses: readonly (readonly number[])[], nvars: number) {
    this.variableSet = new Array<boolean>(nvars + 1).fill(false);
    this.clauses = clauses.map((c) => [...c]);
    this.clauses.forEach((clause, i) => {
      if (clause.length === 0) {
        this.isUnsatisfied = true;
        return;
      }
      if (clause.length === 1) {
        this.unitQueue.push(clause[0]!);
        return;
      }
      this.sentinel(clause[0]!).add(i);
      this.sentinel(clause[clause.length - 1]!).add(i);
      for (const lit of clause) this.occurrence.set(lit, (this.occurrence.get(lit) ?? 0) + 1);
    });
    for (let v = 1; v <= nvars; v++) {
      this.scores.set(v, -(this.occurrence.get(v) ?? 0));
      this.scores.set(-v, -(this.occurrence.get(-v) ?? 0));
      this.heap.push([this.scores.get(v)!, v]);
      this.heap.push([this.scores.get(-v)!, -v]);
    }
  }

  private sentinel(lit: number): Set<number> {
    let s = this.sentinels.get(lit);
    if (!s) {
      s = new Set();
      this.sentinels.set(lit, s);
    }
    return s;
  }

  private get current(): Level {
    return this.levels[this.levels.length - 1]!;
  }

  /** The models, each as the assigned literals (positive = true). */
  *findModels(): Generator<number[]> {
    if (this.isUnsatisfied) return;
    let flipVar = false;
    this.simplify();
    if (this.unsatisfied()) return;
    for (;;) {
      let lit: number;
      if (flipVar) {
        flipVar = false;
        lit = this.current.decision;
      } else {
        lit = this.decide();
        if (lit === 0) {
          yield [...this.varSettings];
          while (this.current.flipped) this.undo();
          if (this.levels.length === 1) return;
          const flip = -this.current.decision;
          this.undo();
          this.levels.push(level(flip, true));
          flipVar = true;
          continue;
        }
        this.levels.push(level(lit));
      }
      this.assign(lit);
      this.simplify();
      if (this.unsatisfied()) {
        this.isUnsatisfied = false;
        while (this.current.flipped) {
          this.undo();
          if (this.levels.length === 1) return;
        }
        const flip = -this.current.decision;
        this.undo();
        this.levels.push(level(flip, true));
        flipVar = true;
      }
    }
  }

  /** A conflict was found (read through a method: simplify() changes it). */
  private unsatisfied(): boolean {
    return this.isUnsatisfied;
  }

  private clauseSat(c: number): boolean {
    return this.clauses[c]!.some((l) => this.varSettings.has(l));
  }

  private assign(lit: number): void {
    this.varSettings.add(lit);
    this.current.varSettings.add(lit);
    this.variableSet[Math.abs(lit)] = true;
    for (const c of [...this.sentinel(-lit)]) {
      if (this.clauseSat(c)) continue;
      let other: number | undefined;
      for (const nl of this.clauses[c]!) {
        if (nl === -lit) continue;
        if (this.sentinel(nl).has(c)) other = nl;
        else if (!this.variableSet[Math.abs(nl)]) {
          this.sentinel(-lit).delete(c);
          this.sentinel(nl).add(c);
          other = undefined;
          break;
        }
      }
      if (other !== undefined) this.unitQueue.push(other);
    }
  }

  private undo(): void {
    for (const lit of this.current.varSettings) {
      this.varSettings.delete(lit);
      const v = Math.abs(lit);
      this.heap.push([this.scores.get(v)!, v]);
      this.heap.push([this.scores.get(-v)!, -v]);
      this.variableSet[v] = false;
    }
    this.levels.pop();
  }

  private simplify(): void {
    while (this.unitQueue.length) {
      const next = this.unitQueue.pop()!;
      if (this.varSettings.has(-next)) {
        this.isUnsatisfied = true;
        this.unitQueue = [];
        return;
      }
      this.assign(next);
    }
  }

  /** VSIDS: the unassigned literal with the lowest score (0 when all variables are set). */
  private decide(): number {
    if (this.heap.size === 0) return 0;
    while (this.variableSet[Math.abs(this.heap.peek()[1])]) {
      this.heap.pop();
      if (this.heap.size === 0) return 0;
    }
    return this.heap.pop()[1];
  }
}
