// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Inference in propositional logic (SymPy logic.inference):
 * satisfiable with SymPy's DPLL solver, valid, entails, pl_true, the
 * propositional knowledge base PropKB, literal_symbol and Boolean.equals.
 */

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
    if (e.name === 'Implies') return { t: 'or', args: [invert(xs[0]!), xs[1]!] };
    return { t: 'and', args: xs.map((a, i) => ({ t: 'or', args: [invert(a), xs[(i + 1) % xs.length]!] })) };
  }
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'Not':
        return invert(toNNF(e.args[0]!));
      case 'And':
        return { t: 'and', args: sub() };
      case 'Or':
        return { t: 'or', args: sub() };
      case 'Xor':
        return xorNnf(sub());
      case 'ITE': {
        const [l, m, r] = sub() as [Nnf, Nnf, Nnf];
        return { t: 'and', args: [{ t: 'or', args: [invert(l), m] }, { t: 'or', args: [l, r] }] };
      }
    }
  }
  if (e instanceof LogicGate) {
    if (e.gate === 'ITE') {
      const [l, m, r] = sub() as [Nnf, Nnf, Nnf];
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
  let acc = parts[0]!;
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
    const ints = [...c.values()].map((l) => (l.atom.key === S.false.key ? 0 : l.neg ? -index.get(l.atom.key)! : index.get(l.atom.key)!));
    if (ints.length === 1 && ints[0] === 0) unsat = true;
    // a false literal adds nothing to a clause
    data.push([...new Set(ints.filter((x) => x !== 0))].sort((a, b) => a - b));
  }
  data.sort((a, b) => a.length - b.length || a.join(',').localeCompare(b.join(',')));
  return { symbols, clauses: data, unsat };
}

function toModel(symbols: readonly Expr[], lits: readonly number[]): ExprMap<boolean> {
  const sorted = [...lits].sort((a, b) => Math.abs(a) - Math.abs(b));
  return new ExprMap(sorted.map((l) => [symbols[Math.abs(l) - 1]!, l > 0] as const));
}

function firstModel(clauses: readonly (readonly number[])[], n: number): number[] | undefined {
  const r = new SATSolver(clauses, n).findModels().next();
  return r.done === true ? undefined : r.value;
}

/** A model whose set of true variables is minimal (no model makes a proper subset true). */
function minimize(clauses: readonly (readonly number[])[], n: number, model0: number[]): number[] {
  let model = model0;
  for (;;) {
    const trues = model.filter((l) => l > 0);
    if (!trues.length) return model;
    const falses = model.filter((l) => l < 0);
    const next = firstModel([...clauses, ...falses.map((l) => [l]), trues.map((l) => -l)], n);
    if (!next) return model;
    model = next;
  }
}

/** Options of satisfiable (SymPy keyword arguments). */
export interface SatisfiableOptions {
  /** Return an iterator over all models (or over the single value false). */
  allModels?: boolean;
  /** Return models whose set of true variables is minimal (SymPy minimal, minisat22). */
  minimal?: boolean;
}

/**
 * SymPy satisfiable: a model (a Map from the atoms to true/false) of the
 * propositional sentence, or false when it is unsatisfiable. With
 * `allModels` an iterator over every model (yielding only false when there
 * is none). `satisfiable(true)` is the model {True: true}.
 */
export function satisfiable(expr: BoolLike, opts?: SatisfiableOptions & { allModels?: false }): ExprMap<boolean> | false;
export function satisfiable(expr: BoolLike, opts: SatisfiableOptions & { allModels: true }): Generator<ExprMap<boolean> | false, void, unknown>;
export function satisfiable(expr: BoolLike, opts: SatisfiableOptions = {}): ExprMap<boolean> | false | Generator<ExprMap<boolean> | false, void, unknown> {
  const { symbols, clauses, unsat } = encode(toBool(expr));
  const n = symbols.length;
  const models = function* (): Generator<number[], void, unknown> {
    if (unsat) return;
    if (!opts.minimal) {
      yield* new SATSolver(clauses, n).findModels();
      return;
    }
    const cs = [...clauses];
    for (;;) {
      const m = firstModel(cs, n);
      if (!m) return;
      const min = minimize(cs, n, m);
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

/** SymPy valid: the sentence is true under every assignment. */
export function valid(expr: BoolLike): boolean {
  return satisfiable(notFn(toBool(expr))) === false;
}

/**
 * SymPy entails: the formulas entail expr (with no formulas, expr is valid).
 */
export function entails(expr: BoolLike, formulaSet: Iterable<BoolLike> = []): boolean {
  return satisfiable(andFn(...[...formulaSet].map(toBool), notFn(toBool(expr)))) === false;
}

/**
 * SymPy pl_true: the value of expr under a (partial) assignment of its
 * symbols; 'unknown' (SymPy None) when not obvious. With `deep` the value
 * under a partial assignment is decided by satisfiability.
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

/** SymPy literal_symbol: the symbol of a literal (without the negation). */
export function literalSymbol(literal: BoolLike): Expr {
  const e = toBool(literal);
  if (e instanceof BoolAtom || e instanceof Sym) return e;
  if (isOp(e, 'Not')) return literalSymbol(e.args[0]!);
  throw new RangeError('Argument must be a boolean literal.');
}

/** SymPy PropKB: a knowledge base of propositional clauses. */
export class PropKB {
  private readonly clauseMap = new Map<string, Expr>();
  /** A knowledge base, optionally told a first sentence. */
  constructor(sentence?: BoolLike) {
    if (sentence !== undefined) this.tell(sentence);
  }
  /** Add the clauses of the sentence (in CNF). */
  tell(sentence: BoolLike): void {
    for (const c of conjuncts(toCnf(sentence))) this.clauseMap.set(c.key, c);
  }
  /** The query follows from the clauses. */
  ask(query: BoolLike): boolean {
    return entails(query, this.clauseMap.values());
  }
  /** Remove the clauses of the sentence. */
  retract(sentence: BoolLike): void {
    for (const c of conjuncts(toCnf(sentence))) this.clauseMap.delete(c.key);
  }
  /** The clauses, ordered. */
  get clauses(): Expr[] {
    return ordered([...this.clauseMap.values()]);
  }
}

/**
 * SymPy Boolean.equals: both formulas have the same atoms and the same truth
 * table. Relations are not supported (NotImplementedError, as in SymPy).
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
