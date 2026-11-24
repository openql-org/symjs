// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Inference in propositional logic (SymPy logic.inference):
 * satisfiable with SymPy's DPLL solver, valid, entails, pl_true, the
 * propositional knowledge base PropKB, literal_symbol and Boolean.equals.
 */

import { at, getOrThrow } from '../core/guard';
import type { Expr } from '../core/nodes';
import { BoolAtom, Rel, S, Sym, impl } from '../core/nodes';
import { ExprMap } from '../core/exprmap';
import { ordered } from '../core/match';
import type { Truth } from '../core/truth';
import { NotImplementedError } from '../core/errors';
import { BoolOp } from '../core/boolalg';
import type { BoolLike } from './boolalg';
import { Equivalent, LogicGate, LogicOp, andFn, boolXreplace, collect, conjuncts, evalBool, isBooleanFunction, isOp, notFn, toBool } from './boolalg';
import { combinations } from './normalforms';
import { toCnf } from './minimize';
import type { EncodedCNF } from '../assumptions/cnf';
import { linearSatisfiable } from './algorithms/lratheory';
import { SATSolver } from './dpll';

// ---------------------------------------------------------------------------
// CNF encoding (SymPy assumptions.cnf: to_NNF, distribute_AND_over_OR, EncodedCNF)

interface Lit {
  readonly atom: Expr;
  readonly neg: boolean;
}
type Nnf = { readonly t: 'lit'; readonly lit: Lit } | { readonly t: 'and' | 'or'; readonly args: readonly Nnf[] };
type Clause = Map<string, Lit>;

const litKey = (l: Lit): string => `${l.neg ? '~' : ''}${l.atom.key}`;
const lit = (atom: Expr, neg = false): Nnf => ({ t: 'lit', lit: { atom, neg } });

function invert(n: Nnf): Nnf {
  if (n.t === 'lit') return { t: 'lit', lit: { atom: n.lit.atom, neg: !n.lit.neg } };
  return { t: n.t === 'and' ? 'or' : 'and', args: n.args.map(invert) };
}

function xorNnf(args: readonly Nnf[]): Nnf {
  const cl: Nnf[] = [];
  for (let i = 0; i <= args.length; i += 2) {
    for (const neg of combinations(args.length, i)) cl.push({ t: 'or', args: args.map((s, j) => (neg.includes(j) ? invert(s) : s)) });
  }
  return { t: 'and', args: cl };
}

function toNNF(e: Expr): Nnf {
  const sub = (): Nnf[] => e.args.map(toNNF);
  if (e instanceof LogicOp) {
    const xs = sub();
    if (e.name === 'Implies') return { t: 'or', args: [invert(at(xs, 0)), at(xs, 1)] };
    return { t: 'and', args: xs.map((a, i) => ({ t: 'or', args: [invert(a), at(xs, (i + 1) % xs.length)] })) };
  }
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'Not':
        return invert(toNNF(at(e.args, 0)));
      case 'And':
        return { t: 'and', args: sub() };
      case 'Or':
        return { t: 'or', args: sub() };
      case 'Xor':
        return xorNnf(sub());
      case 'ITE': {
        const xs = sub();
        const [l, m, r] = [at(xs, 0), at(xs, 1), at(xs, 2)];
        return { t: 'and', args: [{ t: 'or', args: [invert(l), m] }, { t: 'or', args: [l, r] }] };
      }
    }
  }
  if (e instanceof LogicGate) {
    if (e.gate === 'ITE') {
      const xs = sub();
      const [l, m, r] = [at(xs, 0), at(xs, 1), at(xs, 2)];
      return { t: 'and', args: [{ t: 'or', args: [invert(l), m] }, { t: 'or', args: [l, r] }] };
    }
    if (e.gate === 'Nand') return invert({ t: 'and', args: sub() });
    if (e.gate === 'Nor') return invert({ t: 'or', args: sub() });
    return invert(xorNnf(sub()));
  }
  return lit(e);
}

function toClauses(n: Nnf): Map<string, Clause> {
  if (n.t === 'lit') {
    const c: Clause = new Map([[litKey(n.lit), n.lit]]);
    return new Map([[clauseKey(c), c]]);
  }
  const parts = n.args.map(toClauses);
  if (n.t === 'and') {
    const out = new Map<string, Clause>();
    for (const p of parts) for (const [k, c] of p) out.set(k, c);
    return out;
  }
  let acc = at(parts, 0);
  for (const p of parts.slice(1)) {
    const next = new Map<string, Clause>();
    for (const a of acc.values()) {
      for (const b of p.values()) {
        const c = new Map([...a, ...b]);
        next.set(clauseKey(c), c);
      }
    }
    acc = next;
  }
  return acc;
}

const clauseKey = (c: Clause): string => [...c.keys()].sort().join('|');

interface Encoded {
  readonly symbols: Expr[];
  readonly clauses: number[][];
  readonly unsat: boolean;
}

/** The CNF of expr as clauses of signed variable numbers; the variables are numbered in SymPy's ordered() order. */
function encode(e: Expr): Encoded {
  const clauses = [...toClauses(toNNF(e)).values()];
  const atoms = new Map<string, Expr>();
  for (const c of clauses) for (const l of c.values()) if (l.atom.key !== S.false.key) atoms.set(l.atom.key, l.atom);
  const symbols = ordered([...atoms.values()]);
  const index = new Map(symbols.map((s, i) => [s.key, i + 1] as const));
  let unsat = false;
  const data: number[][] = [];
  for (const c of clauses) {
    const ints = [...c.values()].map((l) => (l.atom.key === S.false.key ? 0 : l.neg ? -getOrThrow(index, l.atom.key) : getOrThrow(index, l.atom.key)));
    if (ints.length === 1 && ints[0] === 0) unsat = true;
    // a false literal adds nothing to a clause
    data.push([...new Set(ints.filter((x) => x !== 0))].sort((a, b) => a - b));
  }
  data.sort((a, b) => a.length - b.length || a.join(',').localeCompare(b.join(',')));
  return { symbols, clauses: data, unsat };
}

/** Keep the clause numbering supplied by an EncodedCNF, including sparse encodings. */
function fromEncoded(input: EncodedCNF): Encoded {
  const symbols: Expr[] = [];
  const indices = new Map<number, number>();
  for (const [atom, code] of input.encoding) {
    if (typeof atom === 'function') throw new TypeError('SAT models require applied predicates');
    indices.set(code, symbols.push(atom));
  }
  const clauses = input.data.map((clause) => [...clause].filter((v) => v !== 0)
    .map((v) => Math.sign(v) * getOrThrow(indices, Math.abs(v))));
  return { symbols, clauses, unsat: clauses.some((clause) => !clause.length) };
}

type Feasibility = (assignment: ReadonlySet<number>) => boolean;

function toModel(symbols: readonly Expr[], lits: readonly number[]): ExprMap<boolean> {
  const sorted = [...lits].sort((a, b) => Math.abs(a) - Math.abs(b));
  return new ExprMap(sorted.map((l) => [at(symbols, Math.abs(l) - 1), l > 0] as const));
}

function firstModel(clauses: readonly (readonly number[])[], n: number, feasible?: Feasibility): number[] | undefined {
  const r = new SATSolver(clauses, n).findModels(feasible).next();
  return r.done === true ? undefined : r.value;
}

/** A model whose set of true variables is minimal (no model makes a proper subset true). */
function minimize(clauses: readonly (readonly number[])[], n: number, model0: number[], feasible?: Feasibility): number[] {
  let model = model0;
  for (;;) {
    const trues = model.filter((l) => l > 0);
    if (!trues.length) return model;
    const falses = model.filter((l) => l < 0);
    const next = firstModel([...clauses, ...falses.map((l) => [l]), trues.map((l) => -l)], n, feasible);
    if (!next) return model;
    model = next;
  }
}

/** Options of satisfiable. */
export interface SatisfiableOptions {
  /** Returns an iterator over all models (or over the single value false). */
  allModels?: boolean;
  /** Require linear real arithmetic predicates to have a common solution. */
  useLraTheory?: boolean;
  /** Returns models whose set of true variables is minimal. */
  minimal?: boolean;
}

/**
 * A model (a Map from the atoms to true/false) of the
 * propositional sentence, or false when it is unsatisfiable. With
 * `allModels` an iterator over every model (yielding only false when there
 * is none). `satisfiable(true)` is the model {True: true}.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - `allModels` requests all models.
 * @returns A satisfying assignment, or `false` for an unsatisfiable formula.
 * @see SymPy `sympy.logic.inference.satisfiable`
 * @example
 * ```ts
 * import { satisfiable } from '@symjs/symjs';
 * satisfiable(true); // => {True: True}
 * ```
 */
export function satisfiable(expr: BoolLike | EncodedCNF, opts?: SatisfiableOptions & { allModels?: false }): ExprMap<boolean> | false;
/**
 * A model (a Map from the atoms to true/false) of the
 * propositional sentence, or false when it is unsatisfiable. With
 * `allModels` an iterator over every model (yielding only false when there
 * is none). `satisfiable(true)` is the model {True: true}.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - `allModels` requests all models.
 * @returns An iterator over satisfying assignments.
 * @see SymPy `sympy.logic.inference.satisfiable`
 */
export function satisfiable(expr: BoolLike | EncodedCNF, opts: SatisfiableOptions & { allModels: true }): Generator<ExprMap<boolean> | false, void, unknown>;
/**
 * A model (a Map from the atoms to true/false) of the
 * propositional sentence, or false when it is unsatisfiable. With
 * `allModels` an iterator over every model (yielding only false when there
 * is none). `satisfiable(true)` is the model {True: true}.
 *
 * @param expr - The Boolean expression to examine.
 * @param opts - The satisfiable settings.
 * @returns An iterator over satisfying assignments.
 * @see SymPy `sympy.logic.inference.satisfiable`
 */
export function satisfiable(expr: BoolLike | EncodedCNF, opts: SatisfiableOptions = {}): ExprMap<boolean> | false | Generator<ExprMap<boolean> | false, void, unknown> {
  const { symbols, clauses, unsat } = typeof expr === 'object' && 'encoding' in expr ? fromEncoded(expr) : encode(toBool(expr));
  const feasible = opts.useLraTheory ? (lits: ReadonlySet<number>): boolean => linearSatisfiable(andFn(...[...lits].map((lit) => {
    const atom = at(symbols, Math.abs(lit) - 1);
    return lit > 0 ? atom : notFn(atom);
  }))) : undefined;
  const n = symbols.length;
  const models = function* (): Generator<number[], void, unknown> {
    if (unsat) return;
    if (!opts.minimal) {
      yield* new SATSolver(clauses, n).findModels(feasible);
      return;
    }
    const cs = [...clauses];
    for (;;) {
      const m = firstModel(cs, n, feasible);
      if (!m) return;
      const min = minimize(cs, n, m, feasible);
      yield min;
      // no later model makes a superset of these variables true
      cs.push(min.filter((l) => l > 0).map((l) => -l));
    }
  };
  if (!opts.allModels) {
    const r = models().next();
    return r.done === true ? false : toModel(symbols, r.value);
  }
  return (function* (): Generator<ExprMap<boolean> | false, void, unknown> {
    let any = false;
    for (const m of models()) {
      any = true;
      yield toModel(symbols, m);
    }
    if (!any) yield false;
  })();
}

/**
 * Checks whether a proposition is true under every truth assignment.
 *
 * @param expr - The Boolean expression to examine.
 * @returns Whether the proposition is true for every assignment.
 * @see SymPy `sympy.logic.inference.valid`
 * @example
 * ```ts
 * import { ex, valid } from '@symjs/symjs';
 * valid(ex`A | B`); // => False
 * ```
 */
export function valid(expr: BoolLike): boolean {
  return satisfiable(notFn(toBool(expr))) === false;
}

/**
 * Tests whether a set of premises implies a proposition. With no premises, this tests validity.
 *
 * @param expr - The Boolean expression to examine.
 * @param formulaSet - The premises from which to test entailment.
 * @returns Whether the premises imply the proposition.
 * @see SymPy `sympy.logic.inference.entails`
 * @example
 * ```ts
 * import { entails, ex } from '@symjs/symjs';
 * entails(ex`Implies(A, B)`); // => False
 * ```
 */
export function entails(expr: BoolLike, formulaSet: Iterable<BoolLike> = []): boolean {
  return satisfiable(andFn(...[...formulaSet].map(toBool), notFn(toBool(expr)))) === false;
}

/**
 * The value of expr under a (partial) assignment of its
 * symbols; 'unknown' when not obvious. With `deep` the value
 * under a partial assignment is decided by satisfiability.
 *
 * @param expr - The Boolean expression to examine.
 * @param model - Mapping of symbols to boolean values to indicate assignment.
 * @param deep - Gives the value of the expression under partial assignments correctly.
 * @returns The truth value under the assignment, or `'unknown'` if undetermined.
 * @see SymPy `sympy.logic.inference.pl_true`
 * @example
 * ```ts
 * import { ex, plTrue } from '@symjs/symjs';
 * plTrue(ex`A & B`, new Map([[ex`A`, false]])); // => False
 * ```
 */
export function plTrue(expr: BoolLike, model: ReadonlyMap<Expr, BoolLike> = new Map(), deep = false): Truth {
  const e = toBool(expr);
  if (e instanceof BoolAtom) return e.value;
  const validate = (x: Expr): boolean => x instanceof Sym || x instanceof BoolAtom || (isBooleanFunction(x) && x.args.every(validate));
  if (!validate(e)) throw new RangeError(`${impl.str(e)} is not a valid boolean expression`);
  const reps = new Map<string, Expr>();
  for (const [k, v] of model) {
    const b = toBool(v);
    if (b instanceof BoolAtom) reps.set(toBool(k).key, b);
  }
  const result = boolXreplace(e, reps);
  if (result instanceof BoolAtom) return result.value;
  if (deep) {
    const env = new Map(collect(result, (x) => x.args.length === 0).map((a) => [a.key, true] as const));
    if (evalBool(result, env)) {
      if (valid(result)) return true;
    } else if (satisfiable(result) === false) return false;
  }
  return 'unknown';
}

/**
 * Returns the symbol of a literal (without the negation).
 *
 * @param literal - The symbol or its negation.
 * @returns The symbol of a literal (without the negation).
 * @throws RangeError when the argument is not a Boolean literal.
 * @see SymPy `sympy.logic.inference.literal_symbol`
 * @example
 * ```ts
 * import { ex, literalSymbol } from '@symjs/symjs';
 * literalSymbol(ex`A`); // => A
 * ```
 */
export function literalSymbol(literal: BoolLike): Expr {
  const e = toBool(literal);
  if (e instanceof BoolAtom || e instanceof Sym) return e;
  if (isOp(e, 'Not')) return literalSymbol(at(e.args, 0));
  throw new RangeError('Argument must be a boolean literal.');
}

/**
 * A knowledge base of propositional clauses.
 *
 * @see SymPy `sympy.logic.inference.PropKB`
 */
export class PropKB {
  private readonly clauseMap = new Map<string, Expr>();
  /**
   * A knowledge base, optionally told a first sentence.
   *
   * @param sentence - The proposition to assert or query.
   */
  constructor(sentence?: BoolLike) {
    if (sentence !== undefined) this.tell(sentence);
  }
  /**
   * Adds the clauses of the sentence (in CNF).
   *
   * @param sentence - The proposition to assert or query.
   * @see SymPy `sympy.logic.inference.PropKB.tell`
   */
  tell(sentence: BoolLike): void {
    for (const c of conjuncts(toCnf(sentence))) this.clauseMap.set(c.key, c);
  }
  /**
   * Tests whether the knowledge base entails the query.
   *
   * @param query - The proposition to assert or query.
   * @returns Whether the premises imply the proposition.
   * @see SymPy `sympy.logic.inference.PropKB.ask`
   * @example
   * ```ts
   * import { ex, PropKB } from '@symjs/symjs';
   * const facts = new PropKB(ex`A & B`);
   * facts.ask(ex`A`); // => True
   * ```
   */
  ask(query: BoolLike): boolean {
    return entails(query, this.clauseMap.values());
  }
  /**
   * Removes the clauses of the sentence.
   *
   * @param sentence - The proposition to assert or query.
   * @see SymPy `sympy.logic.inference.PropKB.retract`
   */
  retract(sentence: BoolLike): void {
    for (const c of conjuncts(toCnf(sentence))) this.clauseMap.delete(c.key);
  }
  /**
   * Represents the clauses, ordered.
   *
   * @returns The clauses, ordered.
   * @see SymPy `sympy.logic.inference.PropKB.clauses`
   */
  get clauses(): Expr[] {
    return ordered([...this.clauseMap.values()]);
  }
}

/**
 * Both formulas have the same atoms and the same truth
 * table. Relations are not supported (NotImplementedError, as in SymPy).
 *
 * @param a - The first Boolean formula.
 * @param b - The formula to compare with the first.
 * @returns Whether the two formulas have the same truth table.
 * @throws NotImplementedError when the requested operation does not support relational expressions.
 * @see SymPy `sympy.logic.boolalg.Boolean.equals`
 * @example
 * ```ts
 * import { booleanEquals, ex } from '@symjs/symjs';
 * booleanEquals(ex`~(A & B)`, ex`~A | ~B`); // => True
 * ```
 */
export function booleanEquals(a: BoolLike, b: BoolLike): boolean {
  const x = toBool(a);
  const y = toBool(b);
  const isRel = (e: Expr): boolean => e instanceof Rel;
  if (collect(x, isRel).length || collect(y, isRel).length) throw new NotImplementedError('handling of relationals');
  const atoms = (e: Expr): string[] =>
    collect(e, (t) => t.args.length === 0)
      .map((t) => t.key)
      .sort();
  const ax = atoms(x);
  const ay = atoms(y);
  return ax.length === ay.length && ax.every((k, i) => k === ay[i]) && satisfiable(notFn(Equivalent(x, y))) === false;
}
