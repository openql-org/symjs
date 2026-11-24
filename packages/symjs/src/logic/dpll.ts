// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The DPLL SAT solver of SymPy (sympy.logic.algorithms.dpll2): watched
 * literals, unit propagation and the VSIDS decision heuristic, enumerating
 * the models of a CNF given as clauses of signed variable numbers.
 */

import { at, getOrThrow, last } from '../core/guard';

/** Min-heap of [score, literal] pairs ordered like Python tuples. */
class LitHeap {
  private readonly items: [number, number][] = [];
  restore(items: readonly (readonly [number, number])[]): void {
    this.items.splice(0, this.items.length, ...items.map(([score, lit]): [number, number] => [score, lit]));
  }
  snapshot(): [number, number][] {
    return this.items.map(([score, lit]) => [score, lit]);
  }
  get size(): number {
    return this.items.length;
  }
  private static less(a: readonly [number, number], b: readonly [number, number]): boolean {
    return a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
  }
  peek(): [number, number] {
    return at(this.items, 0);
  }
  push(x: [number, number]): void {
    const h = this.items;
    // sift up: move the hole at the end towards the root, then drop x into it
    let i = h.length;
    h.push(x);
    while (i > 0) {
      const p = (i - 1) >> 1;
      const parent = h[p];
      if (parent === undefined || !LitHeap.less(x, parent)) break;
      h[i] = parent;
      i = p;
    }
    h[i] = x;
  }
  pop(): [number, number] {
    const h = this.items;
    const top = at(h, 0);
    const x = last(h);
    h.pop();
    const n = h.length;
    if (n === 0) return top;
    // sift down: move the hole at the root towards the leaves, then drop x into it
    let i = 0;
    for (;;) {
      const l = 2 * i + 1;
      const left = h[l];
      if (left === undefined) break;
      const right = h[l + 1];
      const [m, child] = right !== undefined && LitHeap.less(right, left) ? [l + 1, right] : [l, left];
      if (!LitHeap.less(child, x)) break;
      h[i] = child;
      i = m;
    }
    h[i] = x;
    return top;
  }
}

/**
 * One decision level of the SAT search.
 *
 * @see SymPy `sympy.logic.algorithms.dpll2.Level`
 */
export class Level {
  /** The signed literals assigned at this search level or solver state. */
  readonly varSettings = new Set<number>();
  /**
   * Creates a Level instance.
   *
   * @param decision - The literal chosen at this decision level.
   * @param flipped - Whether the opposite choice has already been tried.
   */
  constructor(
    /** The decision literal for this level of the SAT search. */
    readonly decision: number,
    /** Indicates whether the opposite decision has already been tried. */
    readonly flipped = false) {}
}

/** A complete DPLL search checkpoint; containers are copied when restored. */
export interface SATSolverState {
  clauses: readonly (readonly number[])[];
  variables: number;
  settings: readonly number[];
  variableSet: readonly boolean[];
  sentinels: readonly (readonly [number, readonly number[]])[];
  scores: readonly (readonly [number, number])[];
  heap: readonly (readonly [number, number])[];
  learned: number;
  levels: readonly { decision: number; flipped: boolean; settings: readonly number[] }[];
  queue: readonly number[];
  unsatisfied: boolean;
}

/**
 * Enumerates the satisfying assignments of a propositional formula encoded as clauses of signed integers.
 *
 * @see SymPy `sympy.logic.algorithms.dpll2.SATSolver`
 */
export class SATSolver {
  /** The clauses constraining a satisfying assignment. */
  readonly clauses: number[][];
  /** The watched literals used to detect unit clauses. */
  readonly sentinels = new Map<number, Set<number>>();
  private readonly occurrence = new Map<number, number>();
  /** Flags indicating which variable indices currently have assignments. */
  readonly variableSet: boolean[];
  /** The signed literals assigned at this search level or solver state. */
  readonly varSettings = new Set<number>();
  private unitQueue: number[] = [];
  private isUnsatisfied = false;
  private readonly levels: Level[] = [new Level(0)];
  private readonly heap = new LitHeap();
  private readonly scores = new Map<number, number>();
  /** The number of clauses learned before the checkpoint (this solver does not learn new clauses). */
  numLearnedClauses = 0;

  /**
   * Represents the current VSIDS heap, including stale entries, in heap order.
   *
   * @returns The current VSIDS heap, including stale entries, in heap order.
   */
  get litHeap(): [number, number][] {
    return this.heap.snapshot();
  }

  /**
   * Represents the current VSIDS scores by signed literal.
   *
   * @returns The current VSIDS scores by signed literal.
   */
  get litScores(): Map<number, number> {
    return new Map(this.scores);
  }

  /**
   * Restore a checkpoint, including pending propagation and decision levels.
   *
   * @param state - The checkpoint containing the clauses, assignments and decision levels.
   * @returns A solver initialized from the saved search state.
   * @throws RangeError when the checkpoint arrays have incompatible dimensions.
   */
  static fromState(state: SATSolverState): SATSolver {
    if (state.levels.length === 0 || state.variableSet.length !== state.variables + 1) throw new RangeError('Invalid SAT checkpoint dimensions');
    const solver = new SATSolver(state.clauses, state.variables);
    for (const lit of state.settings) solver.varSettings.add(lit);
    solver.variableSet.splice(0, solver.variableSet.length, ...state.variableSet);
    solver.sentinels.clear();
    for (const [lit, clauses] of state.sentinels) solver.sentinels.set(lit, new Set(clauses));
    solver.scores.clear();
    for (const [lit, score] of state.scores) solver.scores.set(lit, score);
    solver.heap.restore(state.heap);
    solver.numLearnedClauses = state.learned;
    solver.levels.splice(0, solver.levels.length, ...state.levels.map((entry) => {
      const restored = new Level(entry.decision, entry.flipped);
      for (const lit of entry.settings) restored.varSettings.add(lit);
      return restored;
    }));
    solver.unitQueue = [...state.queue];
    solver.isUnsatisfied = state.unsatisfied;
    return solver;
  }

  /**
   * Save the search state without sharing mutable containers with the solver.
   *
   * @returns A snapshot of the SAT search state.
   */
  toState(): SATSolverState {
    return {
      clauses: this.clauses.map((clause) => [...clause]), variables: this.variableSet.length - 1,
      settings: [...this.varSettings], variableSet: [...this.variableSet],
      sentinels: [...this.sentinels].map(([lit, clauses]) => [lit, [...clauses]]),
      scores: [...this.scores], heap: this.heap.snapshot(), learned: this.numLearnedClauses,
      levels: this.levels.map((entry) => ({ decision: entry.decision, flipped: entry.flipped, settings: [...entry.varSettings] })),
      queue: [...this.unitQueue], unsatisfied: this.isUnsatisfied,
    };
  }

  /**
   * Creates a SATSolver instance.
   *
   * @param clauses - The clauses whose conjunction is being tested.
   * @param nvars - The number of Boolean variables numbered from one.
   */
  constructor(clauses: readonly (readonly number[])[], nvars: number) {
    this.variableSet = new Array<boolean>(nvars + 1).fill(false);
    this.clauses = clauses.map((c) => [...c]);
    this.clauses.forEach((clause, i) => {
      if (clause.length === 0) {
        this.isUnsatisfied = true;
        return;
      }
      if (clause.length === 1) {
        this.unitQueue.push(at(clause, 0));
        return;
      }
      this.sentinel(at(clause, 0)).add(i);
      this.sentinel(last(clause)).add(i);
      for (const lit of clause) this.occurrence.set(lit, (this.occurrence.get(lit) ?? 0) + 1);
    });
    for (let v = 1; v <= nvars; v++) {
      this.scores.set(v, -(this.occurrence.get(v) ?? 0));
      this.scores.set(-v, -(this.occurrence.get(-v) ?? 0));
      this.heap.push([getOrThrow(this.scores, v), v]);
      this.heap.push([getOrThrow(this.scores, -v), -v]);
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
    return last(this.levels);
  }

  /**
   * The models, each as the assigned literals (positive = true).
   *
   * @param feasible - An optional predicate that rejects infeasible assignments.
   * @returns An iterator over satisfying assignments as signed literals.
   * @example
   * ```ts
   * import { SATSolver } from '@symjs/symjs/logic';
   * const solver = new SATSolver([[1], [-1, 2]], 2);
   * [...solver.findModels()]; // => [[1, 2]]
   * ```
   */
  *findModels(feasible?: (assignment: ReadonlySet<number>) => boolean): Generator<number[]> {
    if (this.isUnsatisfied) return;
    let flipVar = false;
    this.simplify();
    if (this.unsatisfied() || feasible?.(this.varSettings) === false) return;
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
          this.levels.push(new Level(flip, true));
          flipVar = true;
          continue;
        }
        this.levels.push(new Level(lit));
      }
      this.assign(lit);
      this.simplify();
      if (this.unsatisfied() || feasible?.(this.varSettings) === false) {
        this.isUnsatisfied = false;
        while (this.current.flipped) {
          this.undo();
          if (this.levels.length === 1) return;
        }
        const flip = -this.current.decision;
        this.undo();
        this.levels.push(new Level(flip, true));
        flipVar = true;
      }
    }
  }

  /** A conflict was found (read through a method: simplify() changes it). */
  private unsatisfied(): boolean {
    return this.isUnsatisfied;
  }

  private clauseSat(c: number): boolean {
    return at(this.clauses, c).some((l) => this.varSettings.has(l));
  }

  private assign(lit: number): void {
    this.varSettings.add(lit);
    this.current.varSettings.add(lit);
    this.variableSet[Math.abs(lit)] = true;
    for (const c of [...this.sentinel(-lit)]) {
      if (this.clauseSat(c)) continue;
      let other: number | undefined;
      for (const nl of at(this.clauses, c)) {
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
      this.heap.push([getOrThrow(this.scores, v), v]);
      this.heap.push([getOrThrow(this.scores, -v), -v]);
      this.variableSet[v] = false;
    }
    this.levels.pop();
  }

  private simplify(): void {
    for (let next = this.unitQueue.pop(); next !== undefined; next = this.unitQueue.pop()) {
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
