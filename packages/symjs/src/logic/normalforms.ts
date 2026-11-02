// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Normal forms of SymPy logic.boolalg: negation normal form (to_nnf),
 * distribution of And/Or/Xor, the CNF/DNF/ANF tests, the algebraic normal
 * form (to_anf), truth tables and gate input counts.
 */

import type { Expr } from '../core/nodes';
import { Rational, S, Sym, impl } from '../core/nodes';
import { BoolOp } from '../core/boolalg';
import type { BoolLike } from './boolalg';
import {
  ITE,
  LogicGate,
  LogicOp,
  andFn,
  boolXreplace,
  isBoolean,
  isBooleanFunction,
  isITE,
  isLiteral,
  isOp,
  notFn,
  orFn,
  rebuildBool,
  toBool,
  xorFn,
} from './boolalg';

type Lattice = 'And' | 'Or';

/** Index combinations of size k of 0..n-1 in lexicographic order (itertools.combinations). */
export function combinations(n: number, k: number): number[][] {
  const out: number[][] = [];
  const cur: number[] = [];
  const go = (start: number): void => {
    if (cur.length === k) {
      out.push([...cur]);
      return;
    }
    for (let i = start; i < n; i++) {
      cur.push(i);
      go(i + 1);
      cur.pop();
    }
  };
  go(0);
  return out;
}

const mk = (op: Lattice, args: readonly Expr[]): Expr => (op === 'And' ? andFn(...args) : orFn(...args));

/** SymPy BooleanFunction._to_nnf for And and Or: the arguments in NNF, complementary pairs give the zero. */
function latticeToNnf(op: Lattice, args: readonly Expr[], simplify: boolean): Expr {
  const argset = new Map<string, Expr>();
  for (const a0 of args) {
    const arg = isLiteral(a0) ? a0 : nnf(a0, simplify);
    if (simplify) {
      for (const a of isOp(arg, op) ? arg.args : [arg]) {
        if (argset.has(notFn(a).key)) return op === 'And' ? S.false : S.true;
        argset.set(a.key, a);
      }
    } else argset.set(arg.key, arg);
  }
  return mk(op, [...argset.values()]);
}

/** Xor in NNF: the conjunction of the clauses with an even (Xor) or odd (Not Xor) number of negations. */
function xorClauses(args: readonly Expr[], start: number): Expr[] {
  const out: Expr[] = [];
  for (let i = start; i <= args.length; i += 2) {
    for (const neg of combinations(args.length, i)) {
      out.push(orFn(...args.map((s, j) => (neg.includes(j) ? notFn(s) : s))));
    }
  }
  return out;
}

/** The to_nnf method of each boolean class. */
function nnf(e: Expr, simplify: boolean): Expr {
  if (e instanceof LogicOp) {
    if (e.name === 'Implies') return latticeToNnf('Or', [notFn(e.args[0]!), e.args[1]!], simplify);
    const a = e.args;
    const cl = a.map((x, i) => orFn(notFn(x), a[(i + 1) % a.length]!));
    return latticeToNnf('And', cl, simplify);
  }
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'And':
      case 'Or':
        return latticeToNnf(e.op, e.args, simplify);
      case 'Not':
        return notToNnf(e, simplify);
      case 'Xor':
        return latticeToNnf('And', xorClauses(e.args, 0), simplify);
      case 'ITE': {
        const [a, b, c] = e.args as [Expr, Expr, Expr];
        return latticeToNnf('And', [orFn(notFn(a), b), orFn(a, c)], simplify);
      }
    }
  }
  if (e instanceof LogicGate && e.gate === 'ITE') {
    const [a, b, c] = e.args as [Expr, Expr, Expr];
    return latticeToNnf('And', [orFn(notFn(a), b), orFn(a, c)], simplify);
  }
  if (e instanceof LogicGate) {
    // BooleanFunction._to_nnf with the gate class: the arguments in NNF, then the gate (evaluated)
    return rebuildBool(e, e.args.map((a) => (isLiteral(a) ? a : nnf(a, simplify))));
  }
  return e;
}

function notToNnf(e: BoolOp, simplify: boolean): Expr {
  if (isLiteral(e)) return e;
  const x = e.args[0]!;
  const args = x.args;
  if (isOp(x, 'And')) return latticeToNnf('Or', args.map(notFn), simplify);
  if (isOp(x, 'Or')) return latticeToNnf('And', args.map(notFn), simplify);
  if (x instanceof LogicOp && x.name === 'Implies') return latticeToNnf('And', [args[0]!, notFn(args[1]!)], simplify);
  if (x instanceof LogicOp) return latticeToNnf('And', [orFn(...args), orFn(...args.map(notFn))], simplify);
  if (isOp(x, 'Xor')) return latticeToNnf('And', xorClauses(args, 1), simplify);
  if (isITE(x)) {
    const [a, b, c] = args as [Expr, Expr, Expr];
    return latticeToNnf('And', [orFn(a, notFn(c)), orFn(notFn(a), notFn(b))], simplify);
  }
  throw new TypeError(`Illegal operator ${(x as { className?: string }).className ?? x.kind} in expression`);
}

/**
 * SymPy is_nnf: only And, Or and Not, with Not applied to literals; with
 * `simplified` (default) no argument appears together with its negation.
 */
export function isNnf(expr: BoolLike, simplified = true): boolean {
  const e0 = toBool(expr);
  if (isLiteral(e0)) return true;
  const stack = [e0];
  while (stack.length) {
    const e = stack.pop()!;
    if (isOp(e, 'And') || isOp(e, 'Or')) {
      if (simplified) {
        const keys = new Set(e.args.map((a) => a.key));
        if (e.args.some((a) => keys.has(notFn(a).key))) return false;
      }
      stack.push(...e.args);
    } else if (!isLiteral(e)) return false;
  }
  return true;
}

/**
 * SymPy to_nnf: negation normal form (only And, Or and Not of literals).
 * With `simplify` (default) clauses with complementary literals are removed.
 */
export function toNnf(expr: BoolLike, simplify = true): Expr {
  const e = toBool(expr);
  if (isNnf(e, simplify)) return e;
  return nnf(e, simplify);
}

/** SymPy eliminate_implications: Implies and Equivalent rewritten with And, Or and Not. */
export function eliminateImplications(expr: BoolLike): Expr {
  return toNnf(expr, false);
}

function isForm(expr: BoolLike, f1: Lattice, f2: Lattice): boolean {
  const e = toBool(expr);
  const vals = isOp(e, f1) ? e.args : [e];
  for (const lit of vals) {
    if (isOp(lit, f2)) {
      if (!lit.args.every(isLiteral)) return false;
    } else if (!isLiteral(lit)) return false;
  }
  return true;
}

/** SymPy is_cnf: a conjunction of disjunctions of literals. */
export function isCnf(expr: BoolLike): boolean {
  return isForm(expr, 'And', 'Or');
}

/** SymPy is_dnf: a disjunction of conjunctions of literals. */
export function isDnf(expr: BoolLike): boolean {
  return isForm(expr, 'Or', 'And');
}

type DistOp = 'And' | 'Or' | 'Xor';
const mk3 = (op: DistOp, args: readonly Expr[]): Expr => (op === 'Xor' ? xorFn(args, false) : mk(op, args));

function distribute(e: Expr, outer: DistOp, inner: DistOp): Expr {
  if (isOp(e, inner)) {
    const conj = e.args.find((a) => isOp(a, outer));
    if (!conj) return e;
    const rest = mk3(
      inner,
      e.args.filter((a) => a !== conj),
    );
    return mk3(
      outer,
      conj.args.map((c) => distribute(mk3(inner, [c, rest]), outer, inner)),
    );
  }
  if (isOp(e, outer)) return mk3(outer, e.args.map((x) => distribute(x, outer, inner)));
  return e;
}

/** SymPy distribute_and_over_or: a sentence of And/Or of literals in CNF. */
export function distributeAndOverOr(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'And', 'Or');
}

/** SymPy distribute_or_over_and: a sentence of And/Or of literals in DNF (not simplified). */
export function distributeOrOverAnd(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'Or', 'And');
}

/** SymPy distribute_xor_over_and: a sentence of And/Xor of literals as an exclusive disjunction. */
export function distributeXorOverAnd(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'Xor', 'And');
}

const isSymbolLike = (e: Expr): boolean => e instanceof Sym;

/**
 * SymPy is_anf: true, false, a symbol, a conjunction of symbols, or an
 * exclusive disjunction of those (without negations).
 */
export function isAnf(expr: BoolLike): boolean {
  const e = toBool(expr);
  if (isLiteral(e) && !isOp(e, 'Not')) return true;
  if (isOp(e, 'And')) return e.args.every(isSymbolLike);
  if (isOp(e, 'Xor')) {
    for (const arg of e.args) {
      if (isOp(arg, 'And')) {
        if (!arg.args.every(isSymbolLike)) return false;
      } else if (isLiteral(arg)) {
        if (isOp(arg, 'Not')) return false;
      } else return false;
    }
    return true;
  }
  return false;
}

/** SymPy BooleanFunction._to_anf: the arguments in ANF (when deep), then the class with remove_true=False. */
function argsToAnf(args: readonly Expr[], deep: boolean): Expr[] {
  return args.map((a) => (deep && (!isLiteral(a) || isOp(a, 'Not')) ? anf(a, deep) : a));
}

function anf(e: Expr, deep: boolean): Expr {
  if (e instanceof LogicOp) {
    if (e.name === 'Implies') {
      const [a, b] = e.args as [Expr, Expr];
      return xorFn(argsToAnf([S.true, a, andFn(a, b)], deep), false);
    }
    const a = andFn(...e.args);
    const b = distributeXorOverAnd(andFn(...e.args.map((x) => toAnf(notFn(x), false))));
    return xorFn(argsToAnf([a, b], deep), false);
  }
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'And':
        return deep ? distributeXorOverAnd(andFn(...argsToAnf(e.args, deep))) : e;
      case 'Or': {
        const terms: Expr[] = [];
        for (let j = 1; j <= e.args.length; j++) {
          for (const c of combinations(e.args.length, j)) {
            const t = andFn(...c.map((i) => e.args[i]!));
            terms.push(deep ? toAnf(t, deep) : t);
          }
        }
        return xorFn(terms, false);
      }
      case 'Not':
        return xorFn(argsToAnf([S.true, e.args[0]!], deep), false);
      case 'Xor':
        return xorFn(argsToAnf(e.args, deep), false);
      case 'ITE':
        return ITE(...(argsToAnf(e.args, deep) as [Expr, Expr, Expr]));
    }
  }
  if (e instanceof LogicGate) return rebuildBool(e, argsToAnf(e.args, deep));
  return e;
}

/**
 * SymPy to_anf: algebraic normal form (Zhegalkin polynomial), an exclusive
 * disjunction of true and conjunctions of variables. With `deep` false only
 * the top level is converted.
 */
export function toAnf(expr: BoolLike, deep = true): Expr {
  const e = toBool(expr);
  if (isAnf(e)) return e;
  return anf(e, deep);
}

/** SymPy to_int_repr: CNF clauses as sets of signed variable indices (1-based). */
export function toIntRepr(clauses: readonly BoolLike[], symbols: readonly BoolLike[]): Set<number>[] {
  const index = new Map(symbols.map((s, i) => [toBool(s).key, i + 1] as const));
  const lookup = (e: Expr): number => {
    const i = index.get(e.key);
    if (i === undefined) throw new RangeError(`${impl.str(e)} is not in the list of symbols`);
    return i;
  };
  return clauses.map((c0) => {
    const c = toBool(c0);
    return new Set((isOp(c, 'Or') ? c.args : [c]).map((a) => (isOp(a, 'Not') ? -lookup(a.args[0]!) : lookup(a))));
  });
}

/** SymPy term_to_integer: the integer with the given base-2 digits. */
export function termToInteger(term: string | readonly number[]): number {
  const s = typeof term === 'string' ? term : term.join('');
  return parseInt(s, 2);
}

/** SymPy ibin (integer_to_term): the binary digits of n, padded to `bits` digits. */
export function integerToTerm(n: number, bits?: number): number[] {
  if (n < 0 || !Number.isInteger(n)) throw new RangeError(`expecting a non-negative integer, not ${n}`);
  const s = n.toString(2);
  if (bits !== undefined && s.length > bits) throw new RangeError(`${n} does not fit in ${bits} bits`);
  return s.padStart(bits ?? s.length, '0').split('').map(Number);
}

/**
 * SymPy truth_table: [inputs, value] for every assignment of 0/1 to the
 * variables in counting order, or only the values when `input` is false.
 * Empty when expr is neither a boolean function nor a literal.
 */
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input?: true): [number[], Expr][];
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input: false): Expr[];
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input = true): [number[], Expr][] | Expr[] {
  const vars = variables.map(toBool);
  const e = toBool(expr);
  if (!isBooleanFunction(e) && !isLiteral(e)) return [];
  const rows: [number[], Expr][] = [];
  for (let k = 0; k < 2 ** vars.length; k++) {
    const term = integerToTerm(k, vars.length);
    const reps = new Map(vars.map((v, i) => [v.key, Rational.of(BigInt(term[i]!))] as const));
    rows.push([term, boolXreplace(e, reps)]);
  }
  return input ? rows : rows.map(([, v]) => v);
}

const GATE_OPS = new Set(['And', 'Or', 'Xor', 'Not', 'ITE']);

/**
 * SymPy gateinputcount: the total number of inputs of the gates (And, Or,
 * Xor, Not, ITE, unevaluated Nand, Nor and Xnor) realizing the expression.
 */
export function gateinputcount(expr: BoolLike): number {
  const e = toBool(expr);
  if (!isBoolean(e)) throw new TypeError('Expression must be Boolean');
  const go = (x: Expr): number => {
    const gate = (x instanceof BoolOp && !(x instanceof LogicOp) && GATE_OPS.has(x.op)) || x instanceof LogicGate;
    return gate ? x.args.length + x.args.reduce((s, a) => s + go(a), 0) : 0;
  };
  return go(e);
}
