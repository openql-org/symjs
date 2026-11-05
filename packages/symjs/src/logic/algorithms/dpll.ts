// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The recursive DPLL algorithm of SymPy (sympy.logic.algorithms.dpll):
 * satisfiability of clauses in a partial model, on expressions and on the
 * integer representation of clauses, with its helpers (unit propagation,
 * pure symbols and unit clauses).
 */

import { at } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { BoolAtom, impl } from '../../core/nodes';
import { ExprMap } from '../../core/exprmap';
import { ordered } from '../../core/match';
import type { Truth } from '../../core/truth';
import type { NoMatchResult } from '../../core/truth';
import { NoMatch, isNoMatch } from '../../core/truth';
import type { BoolLike } from '../boolalg';
import { conjuncts, disjuncts, findPredicates, isOp, notFn, orFn, toBool } from '../boolalg';
import { toIntRepr } from '../normalforms';
import { toCnf } from '../minimize';
import { literalSymbol, plTrue, satisfiable } from '../inference';

/** A model of the integer representation: variable number -> value. */
export type IntModel = Map<number, boolean>;

/**
 * SymPy dpll_satisfiable (of both sympy.logic.algorithms.dpll and dpll2): a
 * model of the propositional sentence (a Map from its atoms to true/false),
 * or false when it is unsatisfiable. With `allModels` an iterator over every
 * model, as satisfiable gives it.
 */
export function dpllSatisfiable(expr: BoolLike, opts?: { allModels?: false }): ExprMap<boolean> | false;
export function dpllSatisfiable(expr: BoolLike, opts: { allModels: true }): Generator<ExprMap<boolean> | false, void, unknown>;
export function dpllSatisfiable(expr: BoolLike, opts: { allModels?: boolean } = {}): ExprMap<boolean> | false | Generator<ExprMap<boolean> | false, void, unknown> {
  const e = toBool(expr);
  if (opts.allModels === true) return satisfiable(e, { allModels: true });
  const clauses = conjuncts(toCnf(e));
  if (clauses.some((c) => c instanceof BoolAtom && !c.value)) return false;
  const symbols = ordered(findPredicates(e));
  const result = dpllIntRepr(
    toIntRepr(clauses, symbols),
    new Set(symbols.map((_s, i) => i + 1)),
    new Map(),
  );
  if (result === false) return false;
  const out = new ExprMap<boolean>();
  for (const [k, v] of result) out.set(at(symbols, k - 1), v);
  return out;
}

const negate = (p: Expr): Expr => notFn(p);

/**
 * SymPy dpll: the satisfiability of the clauses (an array of conjuncts) in the
 * partial model; a completed model, or false.
 */
export function dpll(clausesIn: readonly BoolLike[], symbolsIn: readonly BoolLike[], modelIn: ReadonlyMap<BoolLike, boolean>): ExprMap<boolean> | false {
  const model = new ExprMap<boolean>([...modelIn].map(([k, v]) => [toBool(k), v] as const));
  return dpllRec(clausesIn.map(toBool), symbolsIn.map(toBool), model);
}

function dpllRec(clauses0: readonly Expr[], symbols: Expr[], model: ExprMap<boolean>): ExprMap<boolean> | false {
  let clauses = [...clauses0];
  // the DP kernel
  for (let r = findUnitClause(clauses, model); !isNoMatch(r); r = findUnitClause(clauses, model)) {
    const [p, value] = r;
    model.set(p, value);
    remove(symbols, p);
    clauses = unitPropagate(clauses, value ? p : negate(p));
  }
  for (let r = findPureSymbol(symbols, clauses); !isNoMatch(r); r = findPureSymbol(symbols, clauses)) {
    const [p, value] = r;
    model.set(p, value);
    remove(symbols, p);
    clauses = unitPropagate(clauses, value ? p : negate(p));
  }
  const unknown: Expr[] = [];
  for (const c of clauses) {
    const val = plTrue(c, model);
    if (val === false) return false;
    if (val !== true) unknown.push(c);
  }
  if (!unknown.length) return model;
  const p = symbols.pop();
  if (p === undefined) throw new RangeError('dpll: an undecided clause has a symbol outside the list of symbols');
  const modelCopy = new ExprMap(model);
  model.set(p, true);
  modelCopy.set(p, false);
  const symbolsCopy = [...symbols];
  const first = dpllRec(unitPropagate(unknown, p), symbols, model);
  return first === false ? dpllRec(unitPropagate(unknown, negate(p)), symbolsCopy, modelCopy) : first;
}

function remove(symbols: Expr[], p: Expr): void {
  const i = symbols.findIndex((s) => s.key === p.key);
  if (i < 0) throw new RangeError(`dpll: ${impl.str(p)} is not in the list of symbols`);
  symbols.splice(i, 1);
}

/**
 * SymPy dpll_int_repr: dpll on clauses in integer representation (sets of
 * signed variable numbers); a completed model, or false.
 */
export function dpllIntRepr(clausesIn: readonly ReadonlySet<number>[], symbolsIn: ReadonlySet<number>, modelIn: ReadonlyMap<number, boolean>): IntModel | false {
  let clauses = [...clausesIn];
  const symbols = new Set(symbolsIn);
  const model: IntModel = new Map(modelIn);
  for (let r = findUnitClauseIntRepr(clauses, model); !isNoMatch(r); r = findUnitClauseIntRepr(clauses, model)) {
    const [p, value] = r;
    model.set(p, value);
    symbols.delete(p);
    clauses = unitPropagateIntRepr(clauses, value ? p : -p);
  }
  for (let r = findPureSymbolIntRepr(symbols, clauses); !isNoMatch(r); r = findPureSymbolIntRepr(symbols, clauses)) {
    const [p, value] = r;
    model.set(p, value);
    symbols.delete(p);
    clauses = unitPropagateIntRepr(clauses, value ? p : -p);
  }
  const unknown: Set<number>[] = [];
  for (const c of clauses) {
    const val = plTrueIntRepr(c, model);
    if (val === false) return false;
    if (val !== true) unknown.push(new Set(c));
  }
  if (!unknown.length) return model;
  if (!symbols.size) throw new RangeError('dpll_int_repr: an undecided clause has a variable outside the set of symbols');
  // Python's set.pop() takes the smallest small integer
  const p = Math.min(...symbols);
  symbols.delete(p);
  const modelCopy = new Map(model);
  model.set(p, true);
  modelCopy.set(p, false);
  const first = dpllIntRepr(unitPropagateIntRepr(unknown, p), symbols, model);
  return first === false ? dpllIntRepr(unitPropagateIntRepr(unknown, -p), symbols, modelCopy) : first;
}

/**
 * SymPy pl_true_int_repr: the value of a clause (the set of literals of an
 * Or) in the model; 'unknown' (SymPy None) when it is not decided.
 */
export function plTrueIntRepr(clause: ReadonlySet<number>, model: ReadonlyMap<number, boolean> = new Map()): Truth {
  let result: Truth = false;
  for (const lit of clause) {
    const v = model.get(Math.abs(lit));
    const p = v === undefined ? undefined : lit < 0 ? !v : v;
    if (p === true) return true;
    if (p === undefined) result = 'unknown';
  }
  return result;
}

/**
 * SymPy unit_propagate: the clauses simplified by the unit clause `symbol`
 * (clauses containing it are dropped, its negation is deleted from the others).
 */
export function unitPropagate(clauses: readonly BoolLike[], symbolIn: BoolLike): Expr[] {
  const symbol = toBool(symbolIn);
  const neg = negate(symbol).key;
  const out: Expr[] = [];
  for (const c0 of clauses) {
    const c = toBool(c0);
    if (!isOp(c, 'Or')) {
      out.push(c);
      continue;
    }
    // (an evaluated Or never holds a literal together with its negation)
    const keys = c.args.map((a) => a.key);
    if (keys.includes(neg)) out.push(orFn(...c.args.filter((a) => a.key !== neg)));
    else if (!keys.includes(symbol.key)) out.push(c);
  }
  return out;
}

/** SymPy unit_propagate_int_repr: unit_propagate on the integer representation. */
export function unitPropagateIntRepr(clauses: readonly ReadonlySet<number>[], s: number): Set<number>[] {
  return clauses.filter((c) => !c.has(s)).map((c) => new Set([...c].filter((l) => l !== -s)));
}

/**
 * SymPy find_pure_symbol: a symbol that occurs only positively (or only
 * negatively) in the clauses, with the value that makes it true; NoMatch
 * (SymPy (None, None)) when there is none.
 */
export function findPureSymbol(symbols: readonly BoolLike[], unknownClauses: readonly BoolLike[]): [Expr, boolean] | NoMatchResult {
  const ds = unknownClauses.map((c) => new Set(disjuncts(c).map((d) => d.key)));
  for (const s0 of symbols) {
    const s = toBool(s0);
    const pos = ds.some((d) => d.has(s.key));
    const neg = ds.some((d) => d.has(negate(s).key));
    if (pos !== neg) return [s, pos];
  }
  return NoMatch;
}

/** SymPy find_pure_symbol_int_repr: find_pure_symbol on the integer representation. */
export function findPureSymbolIntRepr(symbols: ReadonlySet<number>, unknownClauses: readonly ReadonlySet<number>[]): [number, boolean] | NoMatchResult {
  const all = new Set(unknownClauses.flatMap((c) => [...c]));
  const pos = [...symbols].filter((s) => all.has(s)).sort((a, b) => a - b);
  const neg = [...symbols].map((s) => -s).filter((s) => all.has(s)).sort((a, b) => a - b);
  for (const p of pos) if (!neg.includes(-p)) return [p, true];
  for (const p of neg) if (!pos.includes(-p)) return [-p, false];
  return NoMatch;
}

/**
 * SymPy find_unit_clause: a clause with exactly one symbol not bound in the
 * model, as that symbol and the value making its literal true; NoMatch
 * (SymPy (None, None)) when there is none.
 */
export function findUnitClause(clauses: readonly BoolLike[], model: ReadonlyMap<BoolLike, boolean>): [Expr, boolean] | NoMatchResult {
  const bound = new Set([...model.keys()].map((k) => toBool(k).key));
  for (const c of clauses) {
    const free = disjuncts(c).filter((l) => !bound.has(literalSymbol(l).key));
    const l = free[0];
    if (free.length === 1 && l !== undefined) return [literalSymbol(l), !isOp(l, 'Not')];
  }
  return NoMatch;
}

/** SymPy find_unit_clause_int_repr: find_unit_clause on the integer representation. */
export function findUnitClauseIntRepr(clauses: readonly ReadonlySet<number>[], model: ReadonlyMap<number, boolean>): [number, boolean] | NoMatchResult {
  for (const c of clauses) {
    const unbound = [...c].filter((l) => !model.has(Math.abs(l)));
    const p = unbound[0];
    if (unbound.length === 1 && p !== undefined) return p < 0 ? [-p, false] : [p, true];
  }
  return NoMatch;
}
