// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The conjunctive normal form of the assumption system (SymPy
 * sympy.assumptions.cnf): literals, the low-level AND and OR, the negation
 * normal form with the decomposition of composite predicates, the CNF as a
 * set of clauses and its encoding into signed variable numbers for the SAT
 * solver.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE). A literal holds an
 * expression (usually an applied predicate such as Q.even(x)) or an
 * unapplied predicate such as Q.even; sets of literals, clauses and
 * predicates compare structurally.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rel, S } from '../core/nodes';
import { BoolOp, and, not, or } from '../core/boolalg';
import { sympify } from '../core/ops';
import type { Predicate } from '../core/refine';
import { AppliedPredicate } from '../core/refine';
import { at, first, getOrThrow, pair } from '../core/guard';
import { LogicGate, LogicOp } from '../logic/boolalg';
import { combinations } from '../logic/normalforms';
import { getCompositePredicates } from './facts';

/** What a literal holds: an expression (an applied predicate, a relation, true, ...) or an unapplied predicate. */
export type PredicateLike = Expr | Predicate;

/**
 * The structural key of an expression or of an unapplied predicate.
 *
 * @param p - Predicate to look up.
 * @returns A structural key suitable for comparing literals.
 */
export const predicateLikeKey = (p: PredicateLike): string => (typeof p === 'function' ? `Predicate:${p.predicateName}` : p.key);

const predicateLikeStr = (p: PredicateLike): string => String(p);

/**
 * The smallest element of a CNF (SymPy Literal): an expression or a
 * predicate, negated or not. `new Literal(not(Q.even(x)))` is
 * `Literal(Q.even(x), True)`.
 *
 * @see SymPy `sympy.assumptions.cnf.Literal`
 * @example
 * ```ts
 * import { Literal, Q, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * new Literal(Q.even(x)).toString(); // => Literal(Q.even(x), False)
 * ```
 */
export class Literal {
  /** The expression or predicate. */
  readonly lit: PredicateLike;
  /** The literal is negated. */
  readonly isNot: boolean;
  /**
   * Constructs a new `Literal`.
   *
   * @param lit - Expression or predicate represented by the literal.
   * @param isNot - Whether the literal is negated.
   */
  constructor(lit: PredicateLike | boolean, isNot = false) {
    const l: PredicateLike = typeof lit === 'boolean' ? (lit ? S.true : S.false) : lit;
    // SymPy sets is_Not to True for a Not whatever is_Not says; ~~p is p, so a negated Not is the plain literal
    if (l instanceof BoolOp && !(l instanceof LogicOp) && l.op === 'Not') {
      this.lit = at(l.args, 0);
      this.isNot = !isNot;
    } else {
      this.lit = l;
      this.isNot = isNot;
    }
  }
  /**
   * The expression or predicate.
   *
   * @returns The expression or predicate.
   * @see SymPy `sympy.assumptions.cnf.Literal.arg`
   */
  get arg(): PredicateLike {
    return this.lit;
  }
  /**
   * Structural key.
   *
   * @returns A stable key for structural comparisons.
   */
  get key(): string {
    return `${this.isNot ? '~' : ''}${predicateLikeKey(this.lit)}`;
  }
  /**
   * The predicate applied to expr; the literal must hold an unapplied predicate.
   *
   * @param expr - Expression to evaluate.
   * @returns The formula with each predicate applied to the expression.
   * @throws TypeError when the literal cannot be applied as a predicate.
   * @see SymPy `sympy.assumptions.cnf.Literal.rcall`
   */
  rcall(expr: ExprLike): Literal {
    const lit = this.lit;
    if (typeof lit !== 'function') throw new TypeError(`${String(lit)} is not a predicate`);
    return new Literal(lit(expr), this.isNot);
  }
  /**
   * The negated literal (SymPy ~).
   *
   * @returns The negated formula.
   * @see SymPy `sympy.assumptions.cnf.Literal.__invert__`
   */
  invert(): Literal {
    return new Literal(this.lit, !this.isNot);
  }
  /**
   * Structural equality (SymPy ==).
   *
   * @param other - Other operand.
   * @returns Whether both objects have the same structure.
   */
  equals(other: Literal): boolean {
    return this.key === other.key;
  }
  /**
   * Formats the predicate and negation flag as a literal.
   *
   * @returns The formatted expression.
   */
  toString(): string {
    return `Literal(${predicateLikeStr(this.lit)}, ${this.isNot ? 'True' : 'False'})`;
  }
}

/** A literal, conjunction or disjunction in negation normal form. */
export type NNF = Literal | OR | AND;

const nnfKey = (a: NNF): string => a.key;
const sortedByStr = (xs: readonly NNF[]): NNF[] => [...xs].sort((a, b) => (String(a) < String(b) ? -1 : String(a) > String(b) ? 1 : 0));

/**
 * A low-level disjunction of the negation normal form.
 *
 * @see SymPy `sympy.assumptions.cnf.OR`
 */
export class OR {
  /**
   * The arguments as given.
   *
   * @see SymPy `sympy.assumptions.cnf.OR._args`
   */
  readonly rawArgs: readonly NNF[];
  /**
   * Constructs a new `OR`.
   *
   * @param args - The operands in negation normal form.
   */
  constructor(...args: NNF[]) {
    this.rawArgs = args;
  }
  /**
   * The arguments sorted by their str form.
   *
   * @returns The arguments sorted by their str form.
   * @see SymPy `sympy.assumptions.cnf.OR.args`
   */
  get args(): NNF[] {
    return sortedByStr(this.rawArgs);
  }
  /**
   * Each argument applied to expr.
   *
   * @param expr - Expression to evaluate.
   * @returns The formula with each predicate applied to the expression.
   * @see SymPy `sympy.assumptions.cnf.OR.rcall`
   */
  rcall(expr: ExprLike): OR {
    return new OR(...this.rawArgs.map((a) => a.rcall(expr)));
  }
  /**
   * The negation: an AND of the negated arguments (SymPy ~).
   *
   * @returns The negated formula.
   * @see SymPy `sympy.assumptions.cnf.OR.__invert__`
   */
  invert(): AND {
    return new AND(...this.rawArgs.map((a) => a.invert()));
  }
  /**
   * Structural key.
   *
   * @returns A stable key for structural comparisons.
   */
  get key(): string {
    return `OR(${this.args.map(nnfKey).join(',')})`;
  }
  /**
   * Structural equality (SymPy ==).
   *
   * @param other - Other operand.
   * @returns Whether both objects have the same structure.
   */
  equals(other: NNF): boolean {
    return this.key === other.key;
  }
  /**
   * (a | b).
   *
   * @returns The formatted expression.
   */
  toString(): string {
    return `(${this.args.map(String).join(' | ')})`;
  }
}

/**
 * A low-level conjunction of the negation normal form.
 *
 * @see SymPy `sympy.assumptions.cnf.AND`
 */
export class AND {
  /**
   * The arguments as given.
   *
   * @see SymPy `sympy.assumptions.cnf.AND._args`
   */
  readonly rawArgs: readonly NNF[];
  /**
   * Constructs a new `AND`.
   *
   * @param args - The operands in negation normal form.
   */
  constructor(...args: NNF[]) {
    this.rawArgs = args;
  }
  /**
   * The arguments sorted by their str form.
   *
   * @returns The arguments sorted by their str form.
   * @see SymPy `sympy.assumptions.cnf.AND.args`
   */
  get args(): NNF[] {
    return sortedByStr(this.rawArgs);
  }
  /**
   * Each argument applied to expr.
   *
   * @param expr - Expression to evaluate.
   * @returns The formula with each predicate applied to the expression.
   * @see SymPy `sympy.assumptions.cnf.AND.rcall`
   */
  rcall(expr: ExprLike): AND {
    return new AND(...this.rawArgs.map((a) => a.rcall(expr)));
  }
  /**
   * The negation: an OR of the negated arguments (SymPy ~).
   *
   * @returns The negated formula.
   * @see SymPy `sympy.assumptions.cnf.AND.__invert__`
   */
  invert(): OR {
    return new OR(...this.rawArgs.map((a) => a.invert()));
  }
  /**
   * Structural key.
   *
   * @returns A stable key for structural comparisons.
   */
  get key(): string {
    return `AND(${this.args.map(nnfKey).join(',')})`;
  }
  /**
   * Structural equality (SymPy ==).
   *
   * @param other - Other operand.
   * @returns Whether both objects have the same structure.
   */
  equals(other: NNF): boolean {
    return this.key === other.key;
  }
  /**
   * (a & b).
   *
   * @returns The formatted expression.
   */
  toString(): string {
    return `(${this.args.map(String).join(' & ')})`;
  }
}

/**
 * Composite predicates and the primitive predicates whose disjunction each
 * one is (SymPy's composite_map: `Q.nonpositive: Q.negative | Q.zero` is
 * the entry `[Q.nonpositive, [Q.negative, Q.zero]]`).
 */
export type CompositeMap = ReadonlyMap<Predicate, readonly Predicate[]>;

const compositeOf = (map: CompositeMap, name: string): readonly Predicate[] | undefined => {
  for (const [p, parts] of map) if (p.predicateName === name) return parts;
  return undefined;
};

const REL_PREDICATES = { Eq: 'eq', Ne: 'ne', Gt: 'gt', Lt: 'lt', Ge: 'ge', Le: 'le' } as const;

const isNotNode = (e: Expr): e is BoolOp => e instanceof BoolOp && !(e instanceof LogicOp) && e.op === 'Not';
const isCoreOp = (e: Expr, op: 'And' | 'Or' | 'Xor' | 'ITE'): boolean => e instanceof BoolOp && !(e instanceof LogicOp) && e.op === op;
const isGate = (e: Expr, gate: 'Nand' | 'Nor' | 'Xnor' | 'ITE'): boolean => e instanceof LogicGate && e.gate === gate;

/** The clauses of a Xor of the arguments: every assignment with an even number of negations. */
function xorClauses(args: readonly Expr[], cmap: CompositeMap): AND {
  const nnfs = args.map((a) => toNNF(a, cmap));
  const cnfs: OR[] = [];
  for (let i = 0; i <= args.length; i += 2) {
    for (const neg of combinations(args.length, i)) {
      cnfs.push(new OR(...nnfs.map((s, j) => (neg.includes(j) ? s.invert() : s))));
    }
  }
  return new AND(...cnfs);
}

/**
 * The negation normal form of a boolean expression in terms
 * of AND, OR and Literal. Relations become the predicates Q.eq, Q.gt, ...;
 * the predicates of `compositeMap` are decomposed into their primitive
 * predicates.
 *
 * @param exprIn - Expression to evaluate.
 * @param compositeMap - Primitive predicates whose disjunction defines each composite predicate.
 * @returns A tree of literals, conjunctions and disjunctions.
 * @see SymPy `sympy.assumptions.cnf.to_NNF`
 * @example
 * ```ts
 * import { Q, and, not, symbols, toNNF } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * toNNF(and(Q.even(x), not(Q.positive(x)))).toString(); // => (Literal(Q.even(x), False) & Literal(Q.positive(x), True))
 * ```
 */
export function toNNF(exprIn: PredicateLike | ExprLike | boolean, compositeMap: CompositeMap = new Map()): NNF {
  if (typeof exprIn === 'function') {
    const parts = compositeOf(compositeMap, exprIn.predicateName);
    return parts === undefined ? new Literal(exprIn) : new OR(...parts.map((p) => toNNF(p, compositeMap)));
  }
  let expr = typeof exprIn === 'boolean' ? (exprIn ? S.true : S.false) : sympify(exprIn);
  if (expr instanceof Rel) expr = new AppliedPredicate(REL_PREDICATES[expr.op], [expr.lhs, expr.rhs]);
  if (isNotNode(expr)) return toNNF(at(expr.args, 0), compositeMap).invert();
  if (isCoreOp(expr, 'Or')) return new OR(...expr.args.map((a) => toNNF(a, compositeMap)));
  if (isCoreOp(expr, 'And')) return new AND(...expr.args.map((a) => toNNF(a, compositeMap)));
  if (isGate(expr, 'Nand')) return new AND(...expr.args.map((a) => toNNF(a, compositeMap))).invert();
  if (isGate(expr, 'Nor')) return new OR(...expr.args.map((a) => toNNF(a, compositeMap))).invert();
  if (isCoreOp(expr, 'Xor')) return xorClauses(expr.args, compositeMap);
  if (isGate(expr, 'Xnor')) return xorClauses(expr.args, compositeMap).invert();
  if (expr instanceof LogicOp && expr.name === 'Implies') {
    const [l, r] = pair(expr.args.map((a) => toNNF(a, compositeMap)));
    return new OR(l.invert(), r);
  }
  if (expr instanceof LogicOp) {
    // Equivalent: each argument implies the next, the last the first
    const nnfs = expr.args.map((a) => toNNF(a, compositeMap));
    return new AND(...nnfs.map((a, i) => new OR(a.invert(), at(nnfs, (i + 1) % nnfs.length))));
  }
  if (isCoreOp(expr, 'ITE') || isGate(expr, 'ITE')) {
    const lmr = expr.args.map((a) => toNNF(a, compositeMap));
    const l = at(lmr, 0);
    return new AND(new OR(l.invert(), at(lmr, 1)), new OR(l, at(lmr, 2)));
  }
  if (expr instanceof AppliedPredicate) {
    const parts = compositeOf(compositeMap, expr.predicate);
    if (parts !== undefined) return toNNF(or(...parts.map((p) => p(...expr.args))), compositeMap);
  }
  return new Literal(expr);
}

/** A clause: literals in a disjunction, without repetition. */
export type Clause = readonly Literal[];

const clauseKey = (c: Iterable<Literal>): string =>
  [...new Set([...c].map((l) => l.key))].sort().join('|');

const uniqueLiterals = (c: Iterable<Literal>): Literal[] => [...new Map([...c].map((l) => [l.key, l] as const)).values()];

/**
 * The CNF of an expression in negation
 * normal form.
 *
 * @param expr - Expression to evaluate.
 * @returns Equivalent clauses in conjunctive normal form.
 * @see SymPy `sympy.assumptions.cnf.distribute_AND_over_OR`
 */
export function distributeANDOverOR(expr: NNF): CNF {
  if (expr instanceof OR) {
    const parts = expr.rawArgs.map(distributeANDOverOR);
    return CNF.allOr(first(parts), ...parts.slice(1));
  }
  if (expr instanceof AND) {
    const parts = expr.rawArgs.map(distributeANDOverOR);
    return CNF.allAnd(first(parts), ...parts.slice(1));
  }
  return new CNF([[expr]]);
}

/**
 * The CNF of a boolean expression (SymPy CNF): a set of clauses, each a set
 * of literals.
 *
 * @see SymPy `sympy.assumptions.cnf.CNF`
 * @example
 * ```ts
 * import { CNF, Q, and, not, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * CNF.fromProp(and(Q.real(x), not(Q.zero(x)))).size; // => 2
 * ```
 */
export class CNF {
  private readonly map = new Map<string, Clause>();
  /**
   * Constructs a new `CNF`.
   *
   * @param clauses - Collections of literals, one collection per disjunction.
   */
  constructor(clauses: Iterable<Iterable<Literal>> = []) {
    this.addClauses(clauses);
  }
  /**
   * The clauses (SymPy clauses, a set of frozensets of literals).
   *
   * @returns The clauses.
   * @see SymPy `sympy.assumptions.cnf.CNF.clauses`
   */
  get clauses(): Clause[] {
    return [...this.map.values()];
  }
  /**
   * The number of clauses.
   *
   * @returns The number of clauses.
   */
  get size(): number {
    return this.map.size;
  }
  /**
   * Adds the CNF of a proposition.
   *
   * @param prop - Proposition to include.
   * @see SymPy `sympy.assumptions.cnf.CNF.add`
   */
  add(prop: PredicateLike | ExprLike | boolean): void {
    this.addClauses(CNF.toCNF(prop).clauses);
  }
  /**
   * Adds the CNF of every proposition and returns this CNF.
   *
   * @param props - Propositions to include.
   * @returns This formula with the added clauses.
   * @see SymPy `sympy.assumptions.cnf.CNF.extend`
   */
  extend(props: Iterable<PredicateLike | ExprLike | boolean>): CNF {
    for (const p of props) this.add(p);
    return this;
  }
  /**
   * A copy.
   *
   * @returns An independent copy.
   * @see SymPy `sympy.assumptions.cnf.CNF.copy`
   */
  copy(): CNF {
    return new CNF(this.clauses);
  }
  /**
   * Adds clauses.
   *
   * @param clauses - Collections of literals, one collection per disjunction.
   * @see SymPy `sympy.assumptions.cnf.CNF.add_clauses`
   */
  addClauses(clauses: Iterable<Iterable<Literal>>): void {
    for (const c of clauses) {
      const lits = uniqueLiterals(c);
      this.map.set(clauseKey(lits), lits);
    }
  }
  /**
   * The CNF of a proposition.
   *
   * @param prop - Proposition to include.
   * @returns The CNF of a proposition.
   * @see SymPy `sympy.assumptions.cnf.CNF.from_prop`
   */
  static fromProp(prop: PredicateLike | ExprLike | boolean): CNF {
    const res = new CNF();
    res.add(prop);
    return res;
  }
  /**
   * Adds the clauses of another CNF and returns this CNF (SymPy &=).
   *
   * @param other - Other operand.
   * @returns This formula with the added clauses.
   * @see SymPy `sympy.assumptions.cnf.CNF.__iand__`
   */
  iand(other: CNF): CNF {
    this.addClauses(other.clauses);
    return this;
  }
  /**
   * The expressions and predicates of the literals.
   *
   * @returns The expressions and predicates of the literals.
   * @see SymPy `sympy.assumptions.cnf.CNF.all_predicates`
   */
  allPredicates(): PredicateLike[] {
    const out = new Map<string, PredicateLike>();
    for (const c of this.map.values()) for (const l of c) out.set(predicateLikeKey(l.lit), l.lit);
    return [...out.values()];
  }
  /**
   * The disjunction with another CNF.
   *
   * @param cnf - Formula in conjunctive normal form.
   * @returns The disjunction with another CNF.
   * @see SymPy `sympy.assumptions.cnf.CNF._or`
   */
  or(cnf: CNF): CNF {
    const clauses: Literal[][] = [];
    for (const a of this.map.values()) for (const b of cnf.map.values()) clauses.push([...a, ...b]);
    return new CNF(clauses);
  }
  /**
   * The conjunction with another CNF.
   *
   * @param cnf - Formula in conjunctive normal form.
   * @returns The conjunction with another CNF.
   * @see SymPy `sympy.assumptions.cnf.CNF._and`
   */
  and(cnf: CNF): CNF {
    return new CNF([...this.clauses, ...cnf.clauses]);
  }
  /**
   * Negates the conjunction of clauses using De Morgan’s laws.
   *
   * @returns An equivalent CNF for the negated proposition.
   * @see SymPy `sympy.assumptions.cnf.CNF._not`
   * @remarks SymPy raises `IndexError` on the empty conjunction. Its negation is false, represented by one empty clause.
   * @example
   * ```ts
   * import { CNF } from '@symjs/symjs';
   *
   * const truth = new CNF();
   * truth.size; // => 0
   * truth.not().clauses; // => [[]]
   * ```
   */
  not(): CNF {
    const clss = this.clauses;
    if (clss.length === 0) return new CNF([[]]);
    let ll = new CNF(at(clss, -1).map((x) => [x.invert()]));
    for (const rest of clss.slice(0, -1)) ll = ll.or(new CNF(rest.map((x) => [x.invert()])));
    return ll;
  }
  /**
   * Every predicate applied to expr.
   *
   * @param expr - Expression to evaluate.
   * @returns The formula with each predicate applied to the expression.
   * @see SymPy `sympy.assumptions.cnf.CNF.rcall`
   */
  rcall(expr: ExprLike): CNF {
    const clauseList = this.clauses.map((clause) => new OR(...clause.map((arg) => arg.rcall(expr))));
    return distributeANDOverOR(new AND(...clauseList));
  }
  /**
   * The disjunction of CNFs.
   *
   * @param head - First formula.
   * @param rest - Remaining formulas.
   * @returns The disjunction of CNFs.
   * @see SymPy `sympy.assumptions.cnf.CNF.all_or`
   */
  static allOr(head: CNF, ...rest: CNF[]): CNF {
    let b = head.copy();
    for (const r of rest) b = b.or(r);
    return b;
  }
  /**
   * The conjunction of CNFs.
   *
   * @param head - First formula.
   * @param rest - Remaining formulas.
   * @returns The conjunction of CNFs.
   * @see SymPy `sympy.assumptions.cnf.CNF.all_and`
   */
  static allAnd(head: CNF, ...rest: CNF[]): CNF {
    let b = head.copy();
    for (const r of rest) b = b.and(r);
    return b;
  }
  /**
   * The CNF of a proposition, with the composite predicates decomposed.
   *
   * @param expr - Expression to evaluate.
   * @returns The CNF of a proposition, with the composite predicates decomposed.
   * @see SymPy `sympy.assumptions.cnf.CNF.to_CNF`
   */
  static toCNF(expr: PredicateLike | ExprLike | boolean): CNF {
    return distributeANDOverOR(toNNF(expr, getCompositePredicates()));
  }
  /**
   * The CNF as a boolean expression of the same form.
   *
   * @param cnf - Formula in conjunctive normal form.
   * @returns The CNF as a boolean expression of the same form.
   * @throws TypeError when a literal is an unapplied predicate.
   * @see SymPy `sympy.assumptions.cnf.CNF.CNF_to_cnf`
   */
  static CNFToCnf(cnf: CNF): Expr {
    const removeLiteral = (arg: Literal): Expr => {
      const lit = arg.lit;
      if (typeof lit === 'function') throw new TypeError(`${String(lit)} is not a boolean expression`);
      return arg.isNot ? not(lit) : lit;
    };
    return and(...cnf.clauses.map((clause) => or(...clause.map(removeLiteral))));
  }
  /**
   * (a | b) & (c).
   *
   * @returns The formatted expression.
   */
  toString(): string {
    return this.clauses.map((clause) => `(${clause.map(String).join(' | ')})`).join(' & ');
  }
}

/** A literal of an encoded clause: 0 for false, otherwise the signed number of its variable. */
type EncodedClause = Set<number>;

/**
 * A CNF whose literals are numbered for the SAT solver (SymPy EncodedCNF):
 * `data` holds the clauses as sets of signed variable numbers, `encoding`
 * the number of each expression or predicate.
 *
 * @see SymPy `sympy.assumptions.cnf.EncodedCNF`
 */
export class EncodedCNF {
  /**
   * The clauses as sets of signed variable numbers (0 is false).
   *
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.data`
   */
  data: EncodedClause[];
  private codes = new Map<string, [PredicateLike, number]>();
  /**
   * Constructs a new `EncodedCNF`.
   *
   * @param data - Clauses of signed integer identifiers.
   * @param encoding - Initial mapping from predicates to positive integer identifiers.
   */
  constructor(data: Iterable<Iterable<number>> = [], encoding: Iterable<readonly [PredicateLike, number]> = []) {
    this.data = [...data].map((c) => new Set(c));
    for (const [k, v] of encoding) this.codes.set(predicateLikeKey(k), [k, v]);
  }
  /**
   * Numbers the predicates of a CNF and encodes its clauses.
   *
   * @param cnf - Formula in conjunctive normal form.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.from_cnf`
   */
  fromCnf(cnf: CNF): void {
    this.codes = new Map(cnf.allPredicates().map((p, i) => [predicateLikeKey(p), [p, i + 1]] as const));
    this.data = cnf.clauses.map((clause) => this.encode(clause));
  }
  /**
   * The expressions and predicates in the order of their numbers.
   *
   * @returns The expressions and predicates in the order of their numbers.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.symbols`
   */
  get symbols(): PredicateLike[] {
    return [...this.codes.values()].map(([p]) => p);
  }
  /**
   * The variable numbers 1..n.
   *
   * @returns The variable numbers 1..n.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.variables`
   */
  get variables(): number[] {
    return Array.from({ length: this.codes.size }, (_v, i) => i + 1);
  }
  /**
   * The number of each expression and predicate.
   *
   * @returns The number of each expression and predicate.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.encoding`
   */
  get encoding(): Map<PredicateLike, number> {
    return new Map([...this.codes.values()].map(([p, n]) => [p, n] as const));
  }
  /**
   * The number of an expression or predicate (SymPy encoding[p]).
   *
   * @param p - Predicate to look up.
   * @returns The number of an expression or predicate.
   */
  encodingOf(p: PredicateLike): number {
    return getOrThrow(this.codes, predicateLikeKey(p))[1];
  }
  /**
   * A copy.
   *
   * @returns An independent copy.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.copy`
   */
  copy(): EncodedCNF {
    return new EncodedCNF(
      this.data.map((c) => new Set(c)),
      [...this.codes.values()],
    );
  }
  /**
   * Adds the CNF of a proposition.
   *
   * @param prop - Proposition to include.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.add_prop`
   */
  addProp(prop: PredicateLike | ExprLike | boolean): void {
    this.addFromCnf(CNF.fromProp(prop));
  }
  /**
   * Encodes and adds the clauses of a CNF.
   *
   * @param cnf - Formula in conjunctive normal form.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.add_from_cnf`
   */
  addFromCnf(cnf: CNF): void {
    this.data.push(...cnf.clauses.map((clause) => this.encode(clause)));
  }
  /**
   * The signed number of a literal, numbering a new expression.
   *
   * @param arg - Argument expression.
   * @returns The signed number of a literal, numbering a new expression.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.encode_arg`
   */
  encodeArg(arg: Literal): number {
    const k = predicateLikeKey(arg.lit);
    let entry = this.codes.get(k);
    if (entry === undefined) {
      entry = [arg.lit, this.codes.size + 1];
      this.codes.set(k, entry);
    }
    return arg.isNot ? -entry[1] : entry[1];
  }
  /**
   * The clause as signed numbers, a false literal as 0.
   *
   * @param clause - Literals of one disjunction.
   * @returns The clause as signed numbers, a false literal as 0.
   * @see SymPy `sympy.assumptions.cnf.EncodedCNF.encode`
   */
  encode(clause: Iterable<Literal>): Set<number> {
    return new Set([...clause].map((arg) => (typeof arg.lit !== 'function' && arg.lit.key === S.false.key ? 0 : this.encodeArg(arg))));
  }
}
