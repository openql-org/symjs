// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Two-level minimization of SymPy logic.boolalg: the Quine-McCluskey
 * algorithm with SymPy's prime implicant table heuristic (SOPform, POSform,
 * simplify_logic, to_cnf/to_dnf with simplify), the algebraic normal form
 * from a truth table (ANFform, anf_coeffs), minterms, maxterms and
 * monomials, and bool_map.
 */

import type { Expr } from '../core/nodes';
import { BoolAtom, Dummy, Rational, Rel, S, Sym, impl } from '../core/nodes';
import { ExprMap } from '../core/exprmap';
import { ordered } from '../core/match';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { NotImplementedError } from '../core/errors';
import type { BoolLike } from './boolalg';
import {
  andFn,
  boolXreplace,
  collect,
  evalBool,
  findPredicates,
  isBooleanFunction,
  isLiteral,
  isOp,
  notFn,
  orFn,
  relNegated,
  toBool,
  xorFn,
} from './boolalg';
import { distributeAndOverOr, distributeOrOverAnd, eliminateImplications, integerToTerm, isCnf, isDnf } from './normalforms';

/** A term of a truth table: 0, 1, or 3 for "don't care" after merging (SymPy's encoding). */
type Term = number[];

/** A minterm given as an integer, a list of bits, or a partial assignment of the variables. */
export type TermSpec = number | readonly number[] | ReadonlyMap<Expr, number>;

const sameTerm = (a: Term, b: Term): boolean => a.length === b.length && a.every((x, i) => x === b[i]);
const includesTerm = (xs: readonly Term[], t: Term): boolean => xs.some((x) => sameTerm(x, t));

/** SymPy _check_pair: the index where two terms differ when they differ in exactly one position, else -1. */
function checkPair(t1: Term, t2: Term): number {
  let index = -1;
  for (let x = 0; x < t1.length; x++) {
    if (t1[x] !== t2[x]) {
      if (index === -1) index = x;
      else return -1;
    }
  }
  return index;
}

/** SymPy _simplified_pairs: merge terms differing in one bit until no more merges are possible. */
function simplifiedPairs(terms: readonly Term[]): Term[] {
  if (!terms.length) return [];
  let simplified: Term[] = [];
  const todo: (number | null)[] = terms.map((_, i) => i);
  const termdict = new Map<number, number[]>();
  terms.forEach((t, n) => {
    const ones = t.filter((x) => x === 1).length;
    termdict.set(ones, [...(termdict.get(ones) ?? []), n]);
  });
  const nvars = terms[0]!.length;
  for (let k = 0; k < nvars; k++) {
    for (const i of termdict.get(k) ?? []) {
      for (const j of termdict.get(k + 1) ?? []) {
        const index = checkPair(terms[i]!, terms[j]!);
        if (index !== -1) {
          todo[i] = todo[j] = null;
          const newterm = [...terms[i]!];
          newterm[index] = 3;
          if (!includesTerm(simplified, newterm)) simplified.push(newterm);
        }
      }
    }
  }
  if (simplified.length) simplified = simplifiedPairs(simplified);
  for (const i of todo) if (i !== null) simplified.push(terms[i]!);
  return simplified;
}

/** SymPy _rem_redundancy: the prime implicant table with row/column dominance and SymPy's heuristic. */
function remRedundancy(l1: readonly Term[], terms: readonly Term[]): Term[] {
  if (!terms.length) return [];
  const nterms = terms.length;
  const nl1 = l1.length;
  const dom = terms.map(() => new Array<number>(nl1).fill(0));
  const colcount = new Array<number>(nl1).fill(0);
  const rowcount = new Array<number>(nterms).fill(0);
  l1.forEach((prime, pi) => {
    terms.forEach((term, ti) => {
      if (prime.every((t, n) => t === 3 || t === term[n])) {
        dom[ti]![pi] = 1;
        colcount[pi]!++;
        rowcount[ti]!++;
      }
    });
  });
  let changed = true;
  while (changed) {
    changed = false;
    for (let ri = 0; ri < nterms; ri++) {
      if (!rowcount[ri]) continue;
      const row = dom[ri]!;
      for (let r2 = 0; r2 < nterms; r2++) {
        if (ri !== r2 && rowcount[ri] && rowcount[ri]! <= rowcount[r2]!) {
          const row2 = dom[r2]!;
          if (row2.every((v, n) => v >= row[n]!)) {
            rowcount[r2] = 0;
            changed = true;
            row2.forEach((p, pi) => {
              if (p) {
                row2[pi] = 0;
                colcount[pi]!--;
              }
            });
          }
        }
      }
    }
    const colcache = new Map<number, number[]>();
    const column = (c: number): number[] => {
      let col = colcache.get(c);
      if (!col) {
        col = dom.map((r) => r[c]!);
        colcache.set(c, col);
      }
      return col;
    };
    for (let ci = 0; ci < nl1; ci++) {
      if (!colcount[ci]) continue;
      const col = column(ci);
      for (let c2 = 0; c2 < nl1; c2++) {
        if (ci !== c2 && colcount[c2] && colcount[ci]! >= colcount[c2]!) {
          const col2 = column(c2);
          if (col.every((v, n) => v >= col2[n]!)) {
            colcount[c2] = 0;
            changed = true;
            col2.forEach((t, ti) => {
              if (t && dom[ti]![c2]) {
                dom[ti]![c2] = 0;
                rowcount[ti]!--;
              }
            });
          }
        }
      }
    }
    if (!changed) {
      // heuristically select the prime implicant covering most terms
      let maxterms = 0;
      let best = -1;
      for (let ci = 0; ci < nl1; ci++) {
        if (colcount[ci]! > maxterms) {
          best = ci;
          maxterms = colcount[ci]!;
        }
      }
      if (best !== -1 && maxterms > 1) {
        const bestcol = colcache.get(best)!;
        for (let pi = 0; pi < nl1; pi++) {
          if (pi === best) continue;
          bestcol.forEach((t, ti) => {
            if (t && dom[ti]![pi]) {
              dom[ti]![pi] = 0;
              changed = true;
              rowcount[ti]!--;
              colcount[pi]!--;
            }
          });
        }
      }
    }
  }
  return l1.filter((_, i) => colcount[i]);
}

function inputToBinlist(inputs: readonly TermSpec[], variables: readonly Expr[]): Term[] {
  const bits = variables.length;
  const out: Term[] = [];
  for (const val of inputs) {
    if (typeof val === 'number') out.push(integerToTerm(val, bits));
    else if (val instanceof Map) {
      const spec = new Map([...val].map(([k, v]) => [toBool(k).key, v] as const));
      const free = variables.filter((v) => !spec.has(v.key));
      for (let k = 0; k < 2 ** free.length; k++) {
        const t = integerToTerm(k, free.length);
        const d = new Map(free.map((v, i) => [v.key, t[i]!] as const));
        out.push(variables.map((v) => spec.get(v.key) ?? d.get(v.key)!));
      }
    } else if (Array.isArray(val)) {
      if (val.length !== bits) throw new RangeError(`Each term must contain ${bits} bits as there are ${bits} variables (or be an integer).`);
      out.push([...(val as readonly number[])]);
    } else throw new TypeError('A term list can only contain lists, ints or dicts.');
  }
  return out;
}

const toVarsSOP = (t: Term, vars: readonly Expr[]): Expr => andFn(...t.flatMap((v, n) => (v === 3 ? [] : [v === 1 ? vars[n]! : notFn(vars[n]!)])));
const toVarsPOS = (t: Term, vars: readonly Expr[]): Expr => orFn(...t.flatMap((v, n) => (v === 3 ? [] : [v === 0 ? vars[n]! : notFn(vars[n]!)])));
const toVarsANF = (t: Term, vars: readonly Expr[]): Expr => {
  const xs = vars.filter((_, n) => t[n] === 1);
  return xs.length ? andFn(...xs) : S.true;
};

function prepare(variables: readonly BoolLike[], minterms: readonly TermSpec[], dontcares: readonly TermSpec[]): [Expr[], Term[], Term[]] {
  const vars = variables.map(toBool);
  const mins = inputToBinlist(minterms, vars);
  const dcs = inputToBinlist(dontcares, vars);
  for (const d of dcs) if (includesTerm(mins, d)) throw new RangeError(`[${d.join(', ')}] in minterms is also in dontcares`);
  return [vars, mins, dcs];
}

function sopForm(vars: readonly Expr[], minterms: readonly Term[], dontcares: readonly Term[]): Expr {
  const essential = remRedundancy(simplifiedPairs([...minterms, ...dontcares]), minterms);
  return orFn(...essential.map((t) => toVarsSOP(t, vars)));
}

function posForm(vars: readonly Expr[], minterms: readonly Term[], dontcares: readonly Term[]): Expr {
  const maxterms: Term[] = [];
  for (let k = 0; k < 2 ** vars.length; k++) {
    const t = integerToTerm(k, vars.length);
    if (!includesTerm(minterms, t) && !includesTerm(dontcares, t)) maxterms.push(t);
  }
  const essential = remRedundancy(simplifiedPairs([...maxterms, ...dontcares]), maxterms);
  return andFn(...essential.map((t) => toVarsPOS(t, vars)));
}

/**
 * SymPy SOPform: the smallest sum-of-products form (an Or of Ands) that is
 * true on the minterms, using the Quine-McCluskey algorithm. Terms are
 * integers, bit lists or partial assignments (Maps); false without minterms.
 */
export function SOPform(variables: readonly BoolLike[], minterms: readonly TermSpec[], dontcares: readonly TermSpec[] = []): Expr {
  if (!minterms.length) return S.false;
  const [vars, mins, dcs] = prepare(variables, minterms, dontcares);
  return sopForm(vars, mins, dcs);
}

/**
 * SymPy POSform: the smallest product-of-sums form (an And of Ors) that is
 * true on the minterms, using the Quine-McCluskey algorithm.
 */
export function POSform(variables: readonly BoolLike[], minterms: readonly TermSpec[], dontcares: readonly TermSpec[] = []): Expr {
  if (!minterms.length) return S.false;
  const [vars, mins, dcs] = prepare(variables, minterms, dontcares);
  return posForm(vars, mins, dcs);
}

/** SymPy anf_coeffs: the coefficients of the Zhegalkin polynomial of a truth table. */
export function anfCoeffs(truthvalues: readonly number[]): number[] {
  const n = truthvalues.length.toString(2).length - 1;
  if (truthvalues.length !== 2 ** n) throw new RangeError(`The number of truth values must be a power of two, got ${truthvalues.length}`);
  let coeffs: number[][] = truthvalues.map((v) => [v]);
  for (let i = 0; i < n; i++) {
    const tmp: number[][] = [];
    for (let j = 0; j < 2 ** (n - i - 1); j++) {
      const a = coeffs[2 * j]!;
      const b = coeffs[2 * j + 1]!;
      tmp.push([...a, ...a.map((x, k) => x ^ b[k]!)]);
    }
    coeffs = tmp;
  }
  return coeffs[0]!;
}

/** SymPy ANFform: the algebraic normal form (Zhegalkin polynomial) of a truth table. */
export function ANFform(variables: readonly BoolLike[], truthvalues: readonly number[]): Expr {
  const n = variables.length;
  if (truthvalues.length !== 2 ** n) throw new RangeError(`The number of truth values must be equal to 2^${n}, got ${truthvalues.length}`);
  const vars = variables.map(toBool);
  const coeffs = anfCoeffs(truthvalues);
  const terms: Expr[] = [];
  coeffs.forEach((c, i) => {
    if (c === 1) terms.push(toVarsANF(integerToTerm(i, n), vars));
  });
  return xorFn(terms, false);
}

const termOf = (k: number | readonly number[], n: number): Term => (typeof k === 'number' ? integerToTerm(k, n) : [...k]);

/** SymPy bool_minterm: the k-th minterm (1 = the variable, 0 = its negation). */
export function boolMinterm(k: number | readonly number[], variables: readonly BoolLike[]): Expr {
  return toVarsSOP(termOf(k, variables.length), variables.map(toBool));
}

/** SymPy bool_maxterm: the k-th maxterm (0 = the variable, 1 = its negation). */
export function boolMaxterm(k: number | readonly number[], variables: readonly BoolLike[]): Expr {
  return toVarsPOS(termOf(k, variables.length), variables.map(toBool));
}

/** SymPy bool_monomial: the k-th Zhegalkin monomial (the conjunction of the variables with bit 1). */
export function boolMonomial(k: number | readonly number[], variables: readonly BoolLike[]): Expr {
  return toVarsANF(termOf(k, variables.length), variables.map(toBool));
}

/** Options of simplifyLogic (SymPy keyword arguments). */
export interface SimplifyLogicOptions {
  /** 'cnf' or 'dnf' for the simplest form of that kind; otherwise the form with fewer arguments. */
  form?: 'cnf' | 'dnf' | null;
  /** Simplify the relations inside first (default true). */
  deep?: boolean;
  /** Minimize also with more than 8 variables (default false). */
  force?: boolean;
  /** Inputs where this expression is true are don't cares. */
  dontcare?: BoolLike;
}

/**
 * SymPy simplify_logic: the simplest SOP (DNF) or POS (CNF) form by the
 * Quine-McCluskey algorithm. Relations are treated as variables (a relation
 * and its negation as one variable). With more than 8 variables nothing is
 * minimized unless `force` is set.
 */
export function simplifyLogic(
  expr: BoolLike,
  form: SimplifyLogicOptions | 'cnf' | 'dnf' | null = null,
  deep = true,
  force = false,
  dontcare?: BoolLike,
): Expr {
  const o: SimplifyLogicOptions = typeof form === 'object' && form !== null ? form : { form, deep, force, dontcare };
  // the form may come from untyped callers
  const f = (o.form ?? null) as string | null;
  if (f !== null && f !== 'cnf' && f !== 'dnf') throw new RangeError('form can be cnf or dnf only');
  let e = toBool(expr);
  if (f !== null) {
    const ok = f === 'cnf' ? isCnf(e) : isDnf(e);
    if (ok && e.args.every(isLiteral)) return e;
  }
  const isRel = (x: Expr): boolean => x instanceof Rel;
  if (o.deep ?? true) {
    const rels = collect(e, isRel);
    if (rels.length) e = boolXreplace(e, new Map(rels.map((r) => [r.key, impl.simplify(r)] as const)));
  }
  if (!isBooleanFunction(e)) return e;
  // relations become dummy variables (a relation and its negation share one)
  let dc = o.dontcare === undefined ? undefined : toBool(o.dontcare);
  const repl = new Map<string, Expr>();
  const undo = new Map<string, Expr>();
  const rels = ordered([...collect(e, isRel), ...(dc ? collect(dc, isRel) : [])].filter((r, i, a) => a.findIndex((s) => s.key === r.key) === i));
  const pending = new Map(rels.map((r) => [r.key, r] as const));
  for (const r of rels) {
    if (!pending.has(r.key)) continue;
    pending.delete(r.key);
    const d = new Dummy();
    undo.set(d.key, r);
    repl.set(r.key, d);
    const nr = relNegated(r as Rel);
    if (pending.has(nr.key)) {
      repl.set(nr.key, notFn(d));
      pending.delete(nr.key);
    }
  }
  e = boolXreplace(e, repl);
  if (dc) dc = boolXreplace(dc, repl);
  let variables = findPredicates(e);
  const force0 = o.force ?? false;
  if (!force0 && variables.length > 8) return boolXreplace(e, undo);
  if (dc) {
    const all = new Map(variables.map((v) => [v.key, v] as const));
    for (const v of findPredicates(dc)) all.set(v.key, v);
    variables = [...all.values()];
    if (!force0 && variables.length > 8) {
      variables = findPredicates(e);
      dc = undefined;
    }
  }
  // constants first (as 1 or 0), then the variables in SymPy's order
  const isConst = (x: Expr): boolean => x instanceof BoolAtom || (x instanceof Rational && x.q === 1n && (x.p === 0n || x.p === 1n));
  const sorted = ordered(variables);
  const consts = sorted.filter(isConst);
  const vs = sorted.filter((x) => !isConst(x));
  const allVars = [...consts, ...vs];
  const c = consts.map((x) => (evalBool(x, new Map()) ? 1 : 0));
  let table = truthRows(vs, e, c);
  let dctable: Term[] = [];
  if (dc) {
    dctable = truthRows(vs, dc, c);
    table = table.filter((t) => !includesTerm(dctable, t));
  }
  const big = table.length >= 2 ** (allVars.length - 1);
  const result = f === 'dnf' || (f === null && big) ? sopForm(allVars, table, dctable) : posForm(allVars, table, dctable);
  return boolXreplace(result, undo);
}

/** SymPy _get_truthtable: the assignments (in counting order) where expr is true, prefixed by the constants. */
function truthRows(vars: readonly Expr[], e: Expr, c: readonly number[]): Term[] {
  const out: Term[] = [];
  for (let k = 0; k < 2 ** vars.length; k++) {
    const t = integerToTerm(k, vars.length);
    if (evalBool(e, new Map(vars.map((v, i) => [v.key, t[i] === 1] as const)))) out.push([...c, ...t]);
  }
  return out.length === 1 && out[0]!.length === 0 ? [] : out;
}

/** Options of toCnf and toDnf. */
export interface NormalFormOptions {
  /** Return the simplest form (Quine-McCluskey). */
  simplify?: boolean;
  /** Simplify also with more than 8 variables. */
  force?: boolean;
}

function toForm(expr: BoolLike, form: 'cnf' | 'dnf', simplify: boolean | NormalFormOptions, force: boolean): Expr {
  const o: NormalFormOptions = typeof simplify === 'object' ? simplify : { simplify, force };
  const e = toBool(expr);
  if (!isBooleanFunction(e)) return e;
  if (o.simplify) {
    if (!o.force && findPredicates(e).length > 8) {
      throw new RangeError('To simplify a logical expression with more than 8 variables may take a long time and requires the use of `force=True`.');
    }
    return simplifyLogic(e, form, true, o.force ?? false);
  }
  if (form === 'cnf' ? isCnf(e) : isDnf(e)) return e;
  const x = eliminateImplications(e);
  return form === 'cnf' ? distributeAndOverOr(x) : distributeOrOverAnd(x);
}

/**
 * SymPy to_cnf: conjunctive normal form. With `simplify` the simplest CNF
 * (Quine-McCluskey); more than 8 variables then require `force`.
 */
export function toCnf(expr: BoolLike, simplify: boolean | NormalFormOptions = false, force = false): Expr {
  return toForm(expr, 'cnf', simplify, force);
}

/**
 * SymPy to_dnf: disjunctive normal form. With `simplify` the simplest DNF
 * (Quine-McCluskey); more than 8 variables then require `force`.
 */
export function toDnf(expr: BoolLike, simplify: boolean | NormalFormOptions = false, force = false): Expr {
  return toForm(expr, 'dnf', simplify, force);
}

/** SymPy _finger: a fingerprint of every variable of a simplified (two-level) expression. */
function finger(eq: Expr): Map<string, Expr[]> {
  const syms = collect(eq, (x) => x instanceof Sym);
  type Info = [number, number, number, number, Map<string, number>];
  const d = new Map<string, Info>(syms.map((s) => [s.key, [0, 0, 0, 0, new Map()]] as const));
  const info = (x: Expr): Info => {
    const i = d.get(x.key);
    if (!i) throw new NotImplementedError('unexpected level of nesting');
    return i;
  };
  for (const a of eq.args) {
    if (a instanceof Sym) info(a)[0]++;
    else if (isOp(a, 'Not')) info(a.args[0]!)[1]++;
    else {
      const o = `${a.args.length},${a.args.filter((x) => isOp(x, 'Not')).length}`;
      for (const ai of a.args) {
        if (ai instanceof Sym) {
          const i = info(ai);
          i[2]++;
          i[4].set(o, (i[4].get(o) ?? 0) + 1);
        } else if (isOp(ai, 'Not')) info(ai.args[0]!)[3]++;
        else throw new NotImplementedError('unexpected level of nesting');
      }
    }
  }
  const inv = new Map<string, Expr[]>();
  for (const s of ordered(syms)) {
    const [a, b, c, dd, m] = d.get(s.key)!;
    const triples = [...m]
      .map(([k, n]) => [...k.split(',').map(Number), n])
      .sort((x, y) => x[0]! - y[0]! || x[1]! - y[1]! || x[2]! - y[2]!);
    const key = JSON.stringify([a, b, c, dd, triples]);
    inv.set(key, [...(inv.get(key) ?? []), s]);
  }
  return inv;
}

function matchBool(f1: Expr, f2: Expr): ExprMap<Expr> | undefined {
  const cls = (x: Expr): string => (x as { className?: string }).className ?? x.kind;
  if (cls(f1) !== cls(f2) || f1.kind !== f2.kind) return undefined;
  if (f1.args.length !== f2.args.length) return undefined;
  if (f1 instanceof Sym) return new ExprMap([[f1, f2]]);
  const a = finger(f1);
  const b = finger(f2);
  if (a.size !== b.size) return undefined;
  const m = new ExprMap<Expr>();
  for (const [k, xs] of a) {
    const ys = b.get(k);
    if (!ys || ys.length !== xs.length) return undefined;
    xs.forEach((x, i) => m.set(x, ys[i]!));
  }
  return m;
}

/**
 * SymPy bool_map: the simplified form of bool1 and a mapping of its
 * variables to those of bool2 under which both have the same truth table;
 * NoMatch when no such mapping is found (SymPy returns False or None).
 */
export function boolMap(bool1: BoolLike, bool2: BoolLike): [Expr, ExprMap<Expr>] | NoMatchResult {
  const a = simplifyLogic(bool1);
  const b = simplifyLogic(bool2);
  const m = matchBool(a, b);
  if (!m || m.size === 0) return NoMatch;
  const sortedMap = new ExprMap<Expr>(ordered([...m.keys()]).map((k) => [k, m.get(k)!] as const));
  return [a, sortedMap];
}
