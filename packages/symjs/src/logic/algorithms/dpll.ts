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
 * Searches for a satisfying assignment using the Davis–Putnam–Logemann–Loveland algorithm.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - `allModels` requests all models.
 * @returns A satisfying assignment, or `false` for an unsatisfiable formula.
 * @see SymPy `sympy.logic.algorithms.dpll.dpll_satisfiable`
 * @example
 * ```ts
 * import { dpllSatisfiable, ex } from '@symjs/symjs';
 * dpllSatisfiable(ex`A & ~B`); // => {A: True, B: False}
 * ```
 */
export function dpllSatisfiable(expr: BoolLike, opts?: { allModels?: false }): ExprMap<boolean> | false;
/**
 * Searches for a satisfying assignment using the Davis–Putnam–Logemann–Loveland algorithm.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - `allModels` requests all models.
 * @returns An iterator over satisfying assignments.
 * @see SymPy `sympy.logic.algorithms.dpll.dpll_satisfiable`
 */
export function dpllSatisfiable(expr: BoolLike, opts: { allModels: true }): Generator<ExprMap<boolean> | false, void, unknown>;
/**
 * Searches for a satisfying assignment using the Davis–Putnam–Logemann–Loveland algorithm.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - `allModels` requests all models.
 * @returns An iterator over satisfying assignments.
 * @see SymPy `sympy.logic.algorithms.dpll.dpll_satisfiable`
 */
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
 * Searches for a satisfying assignment extending the partial model of the clauses.
 *
 * @param clausesIn - The clauses whose conjunction is being tested.
 * @param symbolsIn - The variables still available for branching.
 * @param modelIn - The partial assignment of truth values.
 * @returns A satisfying assignment, or `false` for an unsatisfiable formula.
 * @see SymPy `sympy.logic.algorithms.dpll.dpll`
 * @example
 * ```ts
 * import { dpll, ex } from '@symjs/symjs';
 * dpll([ex`A`, ex`B`, ex`D`], [ex`A`, ex`B`], new Map([[ex`D`, false]])); // => False
 * ```
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
 * Solves a Boolean clause system encoded as signed integer literals.
 *
 * @param clausesIn - The clauses whose conjunction is being tested.
 * @param symbolsIn - The variables still available for branching.
 * @param modelIn - The partial assignment of truth values.
 * @returns A satisfying assignment, or `false` for an unsatisfiable formula.
 * @throws RangeError when an undecided clause has a variable outside the set of symbols.
 * @see SymPy `sympy.logic.algorithms.dpll.dpll_int_repr`
 * @example
 * ```ts
 * import { dpllIntRepr } from '@symjs/symjs';
 * dpllIntRepr([new Set([1]), new Set([2]), new Set([3])], new Set([1, 2]), new Map([[3, false]])); // => False
 * ```
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
 * The value of a clause (the set of literals of an
 * Or) in the model; 'unknown' when it is not decided.
 *
 * @param clause - The disjunction of signed literals.
 * @param model - The partial assignment of truth values.
 * @returns The truth value under the assignment, or `'unknown'` if undetermined.
 * @see SymPy `sympy.logic.algorithms.dpll.pl_true_int_repr`
 * @example
 * ```ts
 * import { plTrueIntRepr } from '@symjs/symjs';
 * plTrueIntRepr(new Set([1, 2]), new Map([[1, false], [2, false]])); // => False
 * ```
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
 * The clauses simplified by the unit clause `symbol`
 * (clauses containing it are dropped, its negation is deleted from the others).
 *
 * @param clauses - The clauses whose conjunction is being tested.
 * @param symbolIn - The literal assumed true.
 * @returns The clauses remaining after propagation.
 * @see SymPy `sympy.logic.algorithms.dpll.unit_propagate`
 * @example
 * ```ts
 * import { ex, unitPropagate } from '@symjs/symjs';
 * unitPropagate([ex`A | B`, ex`D | ~B`, ex`B`], ex`B`); // => [D, B]
 * ```
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

/**
 * Simplifies integer clauses under the assumption that a signed literal is true.
 *
 * @param clauses - The clauses whose conjunction is being tested.
 * @param s - The signed integer literal assumed true.
 * @returns The remaining unsatisfied clauses with the negated literal removed.
 * @see SymPy `sympy.logic.algorithms.dpll.unit_propagate_int_repr`
 * @example
 * ```ts
 * import { unitPropagateIntRepr } from '@symjs/symjs';
 * unitPropagateIntRepr([new Set([1, 2]), new Set([3, -2]), new Set([2])], 2); // => [{3}]
 * ```
 */
export function unitPropagateIntRepr(clauses: readonly ReadonlySet<number>[], s: number): Set<number>[] {
  return clauses.filter((c) => !c.has(s)).map((c) => new Set([...c].filter((l) => l !== -s)));
}

/**
 * A symbol that occurs only positively (or only
 * negatively) in the clauses, with the value that makes it true; NoMatch
 * (SymPy (None, None)) when there is none.
 *
 * @remarks SymPy returns `(A, True)`.
 *
 * @param symbols - The variables to test for a single polarity.
 * @param unknownClauses - The clauses still undecided by the assignment.
 * @returns A pure literal’s variable and polarity, or `NoMatch`.
 * @see SymPy `sympy.logic.algorithms.dpll.find_pure_symbol`
 * @example
 * ```ts
 * import { ex, findPureSymbol } from '@symjs/symjs';
 * findPureSymbol([ex`A`, ex`B`, ex`D`], [ex`A | ~B`, ex`~B | ~D`, ex`A | D`]); // => [A, True]
 * ```
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

/**
 * Searches integer clauses for a variable appearing with only one sign.
 *
 * @remarks SymPy returns `(1, True)`.
 *
 * @param symbols - The variables to test for a single polarity.
 * @param unknownClauses - The clauses still undecided by the assignment.
 * @returns A pure literal’s variable and polarity, or `NoMatch`.
 * @see SymPy `sympy.logic.algorithms.dpll.find_pure_symbol_int_repr`
 * @example
 * ```ts
 * import { findPureSymbolIntRepr } from '@symjs/symjs';
 * findPureSymbolIntRepr(new Set([1, 2, 3]), [new Set([1, -2]), new Set([-3, -2]), new Set([1, 3])]); // => [1, True]
 * ```
 */
export function findPureSymbolIntRepr(symbols: ReadonlySet<number>, unknownClauses: readonly ReadonlySet<number>[]): [number, boolean] | NoMatchResult {
  const all = new Set(unknownClauses.flatMap((c) => [...c]));
  const pos = [...symbols].filter((s) => all.has(s)).sort((a, b) => a - b);
  const neg = [...symbols].map((s) => -s).filter((s) => all.has(s)).sort((a, b) => a - b);
  for (const p of pos) if (!neg.includes(-p)) return [p, true];
  for (const p of neg) if (!pos.includes(-p)) return [-p, false];
  return NoMatch;
}

/**
 * A clause with exactly one symbol not bound in the
 * model, as that symbol and the value making its literal true; NoMatch
 * (SymPy (None, None)) when there is none.
 *
 * @remarks SymPy returns `(B, False)`.
 *
 * @param clauses - The clauses whose conjunction is being tested.
 * @param model - The partial assignment of truth values.
 * @returns The remaining variable and required truth value, or `NoMatch`.
 * @see SymPy `sympy.logic.algorithms.dpll.find_unit_clause`
 * @example
 * ```ts
 * import { ex, findUnitClause } from '@symjs/symjs';
 * findUnitClause([ex`A | B | D`, ex`B | ~D`, ex`A | ~B`], new Map([[ex`A`, true]])); // => [B, False]
 * ```
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

/**
 * Finds the literal forced by a clause with one unassigned variable.
 *
 * @remarks SymPy returns `(2, False)`.
 *
 * @param clauses - The clauses whose conjunction is being tested.
 * @param model - The partial assignment of truth values.
 * @returns The remaining variable and required truth value, or `NoMatch`.
 * @see SymPy `sympy.logic.algorithms.dpll.find_unit_clause_int_repr`
 * @example
 * ```ts
 * import { findUnitClauseIntRepr } from '@symjs/symjs';
 * findUnitClauseIntRepr([new Set([1, 2, 3]), new Set([2, -3]), new Set([1, -2])], new Map([[1, true]])); // => [2, False]
 * ```
 */
export function findUnitClauseIntRepr(clauses: readonly ReadonlySet<number>[], model: ReadonlyMap<number, boolean>): [number, boolean] | NoMatchResult {
  for (const c of clauses) {
    const unbound = [...c].filter((l) => !model.has(Math.abs(l)));
    const p = unbound[0];
    if (unbound.length === 1 && p !== undefined) return p < 0 ? [-p, false] : [p, true];
  }
  return NoMatch;
}
