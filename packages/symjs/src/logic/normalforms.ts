// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Normal forms of SymPy logic.boolalg: negation normal form (to_nnf),
 * distribution of And/Or/Xor, the CNF/DNF/ANF tests, the algebraic normal
 * form (to_anf), truth tables and gate input counts.
 */

import { at, pair } from '../core/guard';
import type { Expr } from '../core/nodes';
import { Rational, S, Sym, impl, registerRewrite } from '../core/nodes';
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
function xorClauses(args: readonly Expr[], start: number, op: Lattice = 'Or'): Expr[] {
  const out: Expr[] = [];
  for (let i = start; i <= args.length; i += 2) {
    for (const neg of combinations(args.length, i)) {
      out.push(mk(op, args.map((s, j) => (neg.includes(j) ? notFn(s) : s))));
    }
  }
  return out;
}

registerRewrite('Xor', 'And', (args) => andFn(...xorClauses(args, 0)));
registerRewrite('Xor', 'Or', (args) => orFn(...xorClauses(args, (args.length + 1) % 2, 'And')));
registerRewrite('Or', 'Nand', (args) => notFn(andFn(...args.map(notFn))));
registerRewrite('And', 'Nor', (args) => notFn(orFn(...args.map(notFn))));

/** The to_nnf method of each boolean class. */
function nnf(e: Expr, simplify: boolean): Expr {
  if (e instanceof LogicOp) {
    if (e.name === 'Implies') return latticeToNnf('Or', [notFn(at(e.args, 0)), at(e.args, 1)], simplify);
    const a = e.args;
    const cl = a.map((x, i) => orFn(notFn(x), at(a, (i + 1) % a.length)));
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
        const [a, b, c] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
        return latticeToNnf('And', [orFn(notFn(a), b), orFn(a, c)], simplify);
      }
    }
  }
  if (e instanceof LogicGate && e.gate === 'ITE') {
    const [a, b, c] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
    return latticeToNnf('And', [orFn(notFn(a), b), orFn(a, c)], simplify);
  }
  if (e instanceof LogicGate) {
    // BooleanFunction._to_nnf with the gate class: the arguments in NNF, then the gate (evaluated)
    return rebuildBool(e, e.args.map((a) => (isLiteral(a) ? a : nnf(a, simplify))));
  }
  return e;
}

/** Not.to_nnf of a Not that is not a literal (nnf is only called on non-literals). */
function notToNnf(e: BoolOp, simplify: boolean): Expr {
  const x = at(e.args, 0);
  const args = x.args;
  if (isOp(x, 'And')) return latticeToNnf('Or', args.map(notFn), simplify);
  if (isOp(x, 'Or')) return latticeToNnf('And', args.map(notFn), simplify);
  if (x instanceof LogicOp && x.name === 'Implies') return latticeToNnf('And', [at(args, 0), notFn(at(args, 1))], simplify);
  if (x instanceof LogicOp) return latticeToNnf('And', [orFn(...args), orFn(...args.map(notFn))], simplify);
  if (isOp(x, 'Xor')) return latticeToNnf('And', xorClauses(args, 1), simplify);
  if (isITE(x)) {
    const [a, b, c] = [at(args, 0), at(args, 1), at(args, 2)];
    return latticeToNnf('And', [orFn(a, notFn(c)), orFn(notFn(a), notFn(b))], simplify);
  }
  // SymPy raises ValueError
  // the class name, as SymPy (Nand, f), else the node kind (Add)
  throw new RangeError(`Illegal operator ${'name' in x && typeof x.name === 'string' ? x.name : x.kind} in expression`);
}

/**
 * Only And, Or and Not, with Not applied to literals; with
 * `simplified` (default) no argument appears together with its negation.
 *
 * @param expr - The Boolean expression to examine.
 * @param simplified - Whether to simplify the Boolean normal form.
 * @returns Whether negations appear only on atoms and the requested simplifications hold.
 * @see SymPy `sympy.logic.boolalg.is_nnf`
 * @example
 * ```ts
 * import { ex, isNnf } from '@symjs/symjs';
 * isNnf(ex`~C | (A & B)`); // => True
 * ```
 */
export function isNnf(expr: BoolLike, simplified = true): boolean {
  const e0 = toBool(expr);
  if (isLiteral(e0)) return true;
  const stack = [e0];
  for (let e = stack.pop(); e !== undefined; e = stack.pop()) {
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
 * Negation normal form (only And, Or and Not of literals).
 * With `simplify` (default) clauses with complementary literals are removed.
 *
 * @param expr - The Boolean expression to examine.
 * @param simplify - Whether to simplify the Boolean normal form.
 * @returns An equivalent formula with negations applied only to literals.
 * @see SymPy `sympy.logic.boolalg.to_nnf`
 * @example
 * ```ts
 * import { ex, toNnf } from '@symjs/symjs';
 * toNnf(ex`~((C & D) | (~A & ~B))`); // => (A | B) & (~C | ~D)
 * ```
 */
export function toNnf(expr: BoolLike, simplify = true): Expr {
  const e = toBool(expr);
  if (isNnf(e, simplify)) return e;
  return nnf(e, simplify);
}

/**
 * Rewrites implications and equivalences using conjunction, disjunction and negation.
 *
 * @param expr - The Boolean expression to examine.
 * @returns An equivalent formula using conjunction, disjunction and negation.
 * @see SymPy `sympy.logic.boolalg.eliminate_implications`
 * @example
 * ```ts
 * import { eliminateImplications, ex } from '@symjs/symjs';
 * eliminateImplications(ex`Implies(A, B)`); // => B | ~A
 * ```
 */
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

/**
 * Tests whether a formula is a conjunction of clauses of literals.
 *
 * @param expr - The Boolean expression to examine.
 * @returns Whether the expression is in conjunctive normal form.
 * @see SymPy `sympy.logic.boolalg.is_cnf`
 * @example
 * ```ts
 * import { ex, isCnf } from '@symjs/symjs';
 * isCnf(ex`A | B | C`); // => True
 * ```
 */
export function isCnf(expr: BoolLike): boolean {
  return isForm(expr, 'And', 'Or');
}

/**
 * Tests whether a formula is a disjunction of conjunctions of literals.
 *
 * @param expr - The Boolean expression to examine.
 * @returns Whether the expression is in disjunctive normal form.
 * @see SymPy `sympy.logic.boolalg.is_dnf`
 * @example
 * ```ts
 * import { ex, isDnf } from '@symjs/symjs';
 * isDnf(ex`A | B | C`); // => True
 * ```
 */
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

/**
 * Returns a sentence of And/Or of literals in CNF.
 *
 * @param expr - The Boolean expression to examine.
 * @returns A sentence of And/Or of literals in CNF.
 * @see SymPy `sympy.logic.boolalg.distribute_and_over_or`
 * @example
 * ```ts
 * import { distributeAndOverOr, ex } from '@symjs/symjs';
 * distributeAndOverOr(ex`A | (~B & ~C)`); // => (A | ~B) & (A | ~C)
 * ```
 */
export function distributeAndOverOr(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'And', 'Or');
}

/**
 * Returns a sentence of And/Or of literals in DNF (not simplified).
 *
 * @param expr - The Boolean expression to examine.
 * @returns A sentence of And/Or of literals in DNF (not simplified).
 * @see SymPy `sympy.logic.boolalg.distribute_or_over_and`
 * @example
 * ```ts
 * import { distributeOrOverAnd, ex } from '@symjs/symjs';
 * distributeOrOverAnd(ex`C & (B | ~A)`); // => (B & C) | (C & ~A)
 * ```
 */
export function distributeOrOverAnd(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'Or', 'And');
}

/**
 * Returns a sentence of And/Xor of literals as an exclusive disjunction.
 *
 * @param expr - The Boolean expression to examine.
 * @returns A sentence of And/Xor of literals as an exclusive disjunction.
 * @see SymPy `sympy.logic.boolalg.distribute_xor_over_and`
 * @example
 * ```ts
 * import { And, Xor, distributeXorOverAnd, ex } from '@symjs/symjs';
 * distributeXorOverAnd(And(Xor(ex`A`, ex`B`), ex`C`)); // => (A & C) ^ (B & C)
 * ```
 */
export function distributeXorOverAnd(expr: BoolLike): Expr {
  return distribute(toBool(expr), 'Xor', 'And');
}

const isSymbolLike = (e: Expr): boolean => e instanceof Sym;

/**
 * True, false, a symbol, a conjunction of symbols, or an
 * exclusive disjunction of those (without negations).
 *
 * @param expr - The Boolean expression to examine.
 * @returns Whether the formula is in algebraic normal form.
 * @see SymPy `sympy.logic.boolalg.is_anf`
 * @example
 * ```ts
 * import { isAnf } from '@symjs/symjs';
 * isAnf(true); // => True
 * ```
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
      const [a, b] = pair(e.args);
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
            const t = andFn(...c.map((i) => at(e.args, i)));
            terms.push(deep ? toAnf(t, deep) : t);
          }
        }
        return xorFn(terms, false);
      }
      case 'Not':
        return xorFn(argsToAnf([S.true, at(e.args, 0)], deep), false);
      case 'Xor':
        return xorFn(argsToAnf(e.args, deep), false);
      case 'ITE': {
        const xs = argsToAnf(e.args, deep);
        return ITE(at(xs, 0), at(xs, 1), at(xs, 2));
      }
    }
  }
  if (e instanceof LogicGate) return rebuildBool(e, argsToAnf(e.args, deep));
  return e;
}

/**
 * Algebraic normal form (Zhegalkin polynomial), an exclusive
 * disjunction of true and conjunctions of variables. With `deep` false only
 * the top level is converted.
 *
 * @param expr - The Boolean expression to examine.
 * @param deep - Whether to process nested expressions.
 * @returns An exclusive disjunction of square-free monomials.
 * @see SymPy `sympy.logic.boolalg.to_anf`
 * @example
 * ```ts
 * import { ex, toAnf } from '@symjs/symjs';
 * toAnf(ex`~A`); // => A ^ True
 * ```
 */
export function toAnf(expr: BoolLike, deep = true): Expr {
  const e = toBool(expr);
  if (isAnf(e)) return e;
  return anf(e, deep);
}

/**
 * CNF clauses as sets of signed variable indices (1-based).
 *
 * @param clauses - The clauses whose conjunction is being tested.
 * @param symbols - The unknowns in the desired order.
 * @returns One set of signed integer literals per clause.
 * @see SymPy `sympy.logic.boolalg.to_int_repr`
 * @example
 * ```ts
 * import { ex, toIntRepr } from '@symjs/symjs';
 * toIntRepr([ex`A | B`, ex`~A`], [ex`A`, ex`B`]); // => [{1, 2}, {-1}]
 * ```
 */
export function toIntRepr(clauses: readonly BoolLike[], symbols: readonly BoolLike[]): Set<number>[] {
  const index = new Map(symbols.map((s, i) => [toBool(s).key, i + 1] as const));
  const lookup = (e: Expr): number => {
    const i = index.get(e.key);
    if (i === undefined) throw new RangeError(`${impl.str(e)} is not in the list of symbols`);
    return i;
  };
  return clauses.map((c0) => {
    const c = toBool(c0);
    return new Set((isOp(c, 'Or') ? c.args : [c]).map((a) => (isOp(a, 'Not') ? -lookup(at(a.args, 0)) : lookup(a))));
  });
}

/**
 * Returns the integer with the given base-2 digits.
 *
 * @param term - The binary digits in most-significant-first order.
 * @returns The integer with the given base-2 digits.
 * @see SymPy `sympy.logic.boolalg.term_to_integer`
 * @example
 * ```ts
 * import { termToInteger } from '@symjs/symjs';
 * termToInteger('100'); // => 4
 * ```
 */
export function termToInteger(term: string | readonly number[]): number {
  const s = typeof term === 'string' ? term : term.join('');
  return parseInt(s, 2);
}

/**
 * Returns a list of length ``bits`` corresponding to the binary value of ``n`` with small bits to the right (last). If bits is omitted, the length will be the number required to represent ``n``. If the bits are desired in reversed order, use the ``[::-1]`` slice of the returned list.
 *
 * @param n - The nonnegative truth-table row index.
 * @param bits - The width of the binary term.
 * @returns A list of length ``bits`` corresponding to the binary value of ``n`` with small bits to the right (last).
 * @see SymPy `sympy.logic.boolalg.integer_to_term`
 * @example
 * ```ts
 * import { integerToTerm } from '@symjs/symjs';
 * integerToTerm(2, 4); // => [0, 0, 1, 0]
 * ```
 */
export function integerToTerm(n: number, bits?: number): number[] {
  if (n < 0 || !Number.isInteger(n)) throw new RangeError(`expecting a non-negative integer, not ${n}`);
  const s = n.toString(2);
  if (bits !== undefined && s.length > bits) throw new RangeError(`${n} does not fit in ${bits} bits`);
  return s.padStart(bits ?? s.length, '0').split('').map(Number);
}

/**
 * Evaluates a Boolean formula at each binary assignment in counting order. Pass `false` for `input` to obtain just the output values.
 *
 * @param expr - The Boolean expression to examine.
 * @param variables - The variables in the requested order.
 * @param input - Indicates whether to return the input combinations.
 * @returns The truth-table rows in binary input order.
 * @see SymPy `sympy.logic.boolalg.truth_table`
 * @example
 * ```ts
 * import { ex, truthTable } from '@symjs/symjs';
 * truthTable(ex`A & B`, [ex`A`, ex`B`]); // => [[[0, 0], False], [[0, 1], False], [[1, 0], False], [[1, 1], True]]
 * ```
 */
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input?: true): [number[], Expr][];
/**
 * Evaluates a Boolean formula at each binary assignment in counting order. Pass `false` for `input` to obtain just the output values.
 *
 * @param expr - The Boolean expression to examine.
 * @param variables - The variables in the requested order.
 * @param input - Indicates whether to return the input combinations.
 * @returns The truth-table rows in binary input order.
 * @see SymPy `sympy.logic.boolalg.truth_table`
 */
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input: false): Expr[];
/**
 * Evaluates a Boolean formula at each binary assignment in counting order. Pass `false` for `input` to obtain just the output values.
 *
 * @param expr - The Boolean expression to examine.
 * @param variables - The variables in the requested order.
 * @param input - Indicates whether to return the input combinations.
 * @returns The truth-table rows in binary input order.
 * @see SymPy `sympy.logic.boolalg.truth_table`
 */
export function truthTable(expr: BoolLike, variables: readonly BoolLike[], input = true): [number[], Expr][] | Expr[] {
  const vars = variables.map(toBool);
  const e = toBool(expr);
  if (!isBooleanFunction(e) && !isLiteral(e)) return [];
  const rows: [number[], Expr][] = [];
  for (let k = 0; k < 2 ** vars.length; k++) {
    const term = integerToTerm(k, vars.length);
    const reps = new Map(vars.map((v, i) => [v.key, Rational.of(BigInt(at(term, i)))] as const));
    rows.push([term, boolXreplace(e, reps)]);
  }
  return input ? rows : rows.map(([, v]) => v);
}

const GATE_OPS = new Set(['And', 'Or', 'Xor', 'Not', 'ITE']);

/**
 * The total number of inputs of the gates (And, Or,
 * Xor, Not, ITE, unevaluated Nand, Nor and Xnor) realizing the expression.
 *
 * @param expr - The Boolean expression to examine.
 * @returns The total number of gate inputs in the expression.
 * @throws TypeError when the expression is not Boolean.
 * @see SymPy `sympy.logic.boolalg.gateinputcount`
 * @example
 * ```ts
 * import { ex, gateinputcount } from '@symjs/symjs';
 * gateinputcount(ex`x`); // => 0
 * ```
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
