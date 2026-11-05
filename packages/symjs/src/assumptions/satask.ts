// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Evaluation of a proposition under assumptions with a SAT solver
 * (SymPy sympy.assumptions.satask): the facts relevant to the expressions of
 * the proposition and the assumptions (the class facts of sathandlers and
 * the known facts between unary predicates) are encoded together, and the
 * proposition is true when its negation is unsatisfiable, false when it is
 * unsatisfiable itself.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { BoolAtom, ExtensionExpr, Rel, S, Sym } from '../core/nodes';
import { BoolOp, not } from '../core/boolalg';
import { atoms } from '../core/methods';
import type { Predicate } from '../core/refine';
import { AppliedPredicate, globalAssumptions } from '../core/refine';
import type { Truth } from '../core/truth';
import { getOrThrow } from '../core/guard';
import { SATSolver } from '../logic/dpll';
import type { PredicateLike } from './cnf';
import { CNF, EncodedCNF, predicateLikeKey } from './cnf';
import { classFactRegistry } from './sathandlers';
import { getAllKnownMatrixFacts, getAllKnownNumberFacts } from './askgenerated';

/** Options of satask (SymPy keyword arguments). */
export interface SataskOptions {
  /** Default assumptions (default the global assumptions). */
  context?: Iterable<Expr>;
  /** Also use the known facts between unary predicates (default true). */
  useKnownFacts?: boolean;
  /** How many times the relevant facts are extracted (default until no new fact is found). */
  iterations?: number;
}

/** A proposition or assumption: a boolean expression or true/false. */
type Prop = ExprLike | boolean;

/**
 * SymPy satask: the truth value of the proposition under the assumptions
 * and the context, decided by a SAT solver over every fact relevant to the
 * expressions involved; 'unknown' when it cannot be determined. Throws a
 * RangeError when the assumptions are inconsistent.
 */
export function satask(proposition: Prop, assumptions: Prop = true, opts: SataskOptions = {}): Truth {
  const context = [...(opts.context ?? globalAssumptions)];
  const props = CNF.fromProp(proposition);
  const negProps = CNF.fromProp(not(proposition));
  const assumptionsCnf = CNF.fromProp(assumptions);
  const contextCnf = new CNF().extend(context);
  const sat = getAllRelevantFacts(props, assumptionsCnf, contextCnf, opts.useKnownFacts ?? true, opts.iterations ?? Infinity);
  sat.addFromCnf(assumptionsCnf);
  if (context.length > 0) sat.addFromCnf(contextCnf);
  return checkSatisfiability(props, negProps, sat);
}

/** The encoded CNF has a model (SymPy satisfiable of an EncodedCNF); a false literal (0) is dropped from its clause. */
function isSatisfiable(enc: EncodedCNF): boolean {
  const clauses = enc.data.map((c) => [...c].filter((l) => l !== 0));
  const n = Math.max(0, ...clauses.flat().map(Math.abs));
  return new SATSolver(clauses, n).findModels().next().done !== true;
}

/**
 * SymPy check_satisfiability: true when only the proposition is consistent
 * with the facts, false when only its negation is, 'unknown' when both are;
 * a RangeError when neither is (inconsistent assumptions).
 */
export function checkSatisfiability(prop: CNF, negProp: CNF, factbase: EncodedCNF): Truth {
  const satTrue = factbase.copy();
  const satFalse = factbase.copy();
  satTrue.addFromCnf(prop);
  satFalse.addFromCnf(negProp);
  const canBeTrue = isSatisfiable(satTrue);
  const canBeFalse = isSatisfiable(satFalse);
  if (canBeTrue && canBeFalse) return 'unknown';
  if (canBeTrue) return true;
  if (canBeFalse) return false;
  throw new RangeError('Inconsistent assumptions');
}

/** SymPy find_symbols: every Symbol in a CNF or an expression. */
export function findSymbols(pred: CNF | PredicateLike): Set<Expr> {
  if (pred instanceof CNF) {
    const out = new Map<string, Expr>();
    for (const a of pred.allPredicates()) for (const s of findSymbols(a)) out.set(s.key, s);
    return new Set(out.values());
  }
  if (typeof pred === 'function') return new Set();
  return new Set(atoms(pred, (a) => a instanceof Sym));
}

const keysOf = (s: Iterable<Expr>): Set<string> => new Set([...s].map((e) => e.key));
const meets = (a: ReadonlySet<string>, b: ReadonlySet<string>): boolean => [...a].some((k) => b.has(k));

/**
 * SymPy extract_predargs: every expression in the argument of a predicate
 * of the proposition, and of the predicates of the assumptions and the
 * context that share symbols with it (transitively).
 */
export function extractPredargs(proposition: CNF, assumptions?: CNF, context?: CNF): Set<Expr> {
  const reqKeys = keysOf(findSymbols(proposition));
  const keys = new Map(proposition.allPredicates().map((p) => [predicateLikeKey(p), p] as const));
  const lkeys = new Map<string, PredicateLike>();
  for (const c of [assumptions, context]) for (const p of c?.allPredicates() ?? []) lkeys.set(predicateLikeKey(p), p);
  lkeys.delete(S.true.key);
  lkeys.delete(S.false.key);
  const symsOf = new Map([...lkeys].map(([k, l]) => [k, keysOf(findSymbols(l))] as const));
  for (;;) {
    const tmp = new Set<string>();
    for (const syms of symsOf.values()) if (meets(syms, reqKeys)) for (const s of syms) tmp.add(s);
    const fresh = [...tmp].filter((s) => !reqKeys.has(s));
    if (fresh.length === 0) break;
    for (const s of fresh) reqKeys.add(s);
  }
  for (const [k, l] of lkeys) if (meets(getOrThrow(symsOf, k), reqKeys)) keys.set(k, l);
  const exprs = new Map<string, Expr>();
  for (const key of keys.values()) {
    if (key instanceof AppliedPredicate) for (const a of key.args) exprs.set(a.key, a);
    // an unapplied predicate has no argument and no facts
    else if (typeof key !== 'function') exprs.set(key.key, key);
  }
  return new Set(exprs.values());
}

/**
 * SymPy get_relevant_clsfacts: the class facts (sathandlers) of the
 * expressions added to relevantFacts, and the expressions they introduce
 * that are not among exprs (the candidates of the next round).
 */
export function getRelevantClsfacts(exprs: Iterable<Expr>, relevantFacts: CNF = new CNF()): [Set<Expr>, CNF] {
  const given = [...exprs];
  const givenKeys = keysOf(given);
  let facts = relevantFacts;
  const newexprs = new Map<string, Expr>();
  for (const expr of given) {
    for (const fact of classFactRegistry.call(expr)) {
      const newfact = CNF.toCNF(fact);
      facts = facts.and(newfact);
      for (const key of newfact.allPredicates()) {
        if (key instanceof AppliedPredicate) for (const a of key.args) if (!givenKeys.has(a.key)) newexprs.set(a.key, a);
      }
    }
  }
  return [new Set(newexprs.values()), facts];
}

/** SymPy MatrixKind(NumberKind): a matrix expression. */
const isMatrixKind = (e: Expr): boolean => e instanceof ExtensionExpr && !e.isScalar;
/** SymPy NumberKind or UndefinedKind: neither a matrix nor a boolean. */
const isNumberKind = (e: Expr): boolean =>
  !isMatrixKind(e) && !(e instanceof BoolAtom || e instanceof Rel || e instanceof BoolOp || e instanceof AppliedPredicate);

/**
 * SymPy get_all_relevant_facts: the class facts relevant to the
 * proposition, the assumptions and the context, found by repeating
 * getRelevantClsfacts until no new expression appears (or `iterations`
 * times), with the known facts of every expression involved, as an
 * EncodedCNF.
 */
export function getAllRelevantFacts(proposition: CNF, assumptions: CNF, context: CNF, useKnownFacts = true, iterations = Infinity): EncodedCNF {
  let i = 0;
  let relevantFacts = new CNF();
  const allExprs = new Map<string, Expr>();
  let exprs: Set<Expr> = extractPredargs(proposition, assumptions, context);
  for (;;) {
    for (const e of exprs) allExprs.set(e.key, e);
    [exprs, relevantFacts] = getRelevantClsfacts(exprs, relevantFacts);
    i++;
    if (i >= iterations || exprs.size === 0) break;
  }
  let ctx = new EncodedCNF();
  if (useKnownFacts) {
    const all = [...allExprs.values()];
    const knownFactsCNF = new CNF();
    if (all.some(isMatrixKind)) knownFactsCNF.addClauses(getAllKnownMatrixFacts());
    if (all.some(isNumberKind)) knownFactsCNF.addClauses(getAllKnownNumberFacts());
    const kfEncoded = new EncodedCNF();
    kfEncoded.fromCnf(knownFactsCNF);
    // the known facts of each expression, on variables of their own
    const preds = kfEncoded.symbols.filter((p): p is Predicate => typeof p === 'function');
    const nLit = preds.length;
    const data: number[][] = [];
    const encoding: [Expr, number][] = [];
    all.forEach((expr, j) => {
      for (const p of preds) encoding.push([p(expr), encoding.length + 1]);
      for (const clause of kfEncoded.data) data.push([...clause].map((l) => (l > 0 ? l + j * nLit : l - j * nLit)));
    });
    ctx = new EncodedCNF(data, encoding);
  }
  ctx.addFromCnf(relevantFacts);
  return ctx;
}
