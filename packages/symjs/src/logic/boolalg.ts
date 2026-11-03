// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Boolean functions of SymPy logic.boolalg that are not in the core:
 * Implies, Equivalent, Nand, Nor, Xnor, ITE and Exclusive, the Xor that keeps
 * `true` (remove_true=False), literals, conjuncts and disjuncts, and the
 * traversal helpers (substitution with re-evaluation, truth evaluation) the
 * normal forms, the minimization and the SAT solver build on.
 */

import { at, pair } from '../core/guard';
import type { BoolOpName } from '../core/boolalg';
import { BoolOp, and as coreAnd, not as coreNot, or as coreOr } from '../core/boolalg';
import type { ExprLike, RelOp } from '../core/nodes';
import { BoolAtom, Expr, ExtensionExpr, Float, Rational, Rel, S, Sym, impl, isNum } from '../core/nodes';
import { isZero as triIsZero } from '../core/assumptions';
import { ordered } from '../core/match';
import { rebuild } from '../core/traverse';
import { couldExtractMinusSign } from '../core/ops';
import { NotImplementedError } from '../core/errors';
import { AppliedPredicate } from '../core/refine';

/** An argument of the boolean constructors: an expression or a JavaScript boolean. */
export type BoolLike = ExprLike | boolean;

/** Options of the boolean constructors (SymPy evaluate=...). */
export interface LogicEvalOptions {
  /** Evaluate to a simpler form when possible (default true). */
  evaluate?: boolean;
}

/** @internal An expression from an ExprLike or a JavaScript boolean. */
export const toBool = (x: BoolLike): Expr => (typeof x === 'boolean' ? (x ? S.true : S.false) : impl.sympify(x));

const isTrueAtom = (e: Expr): boolean => e instanceof BoolAtom && e.value;
const isFalseAtom = (e: Expr): boolean => e instanceof BoolAtom && !e.value;

/** Names of the boolean functions printed as Name(args) with the precedence of Xor. */
export type LogicOpName = 'Implies' | 'Equivalent';

/**
 * SymPy Implies and Equivalent nodes. They are BoolOp nodes so that the core
 * printers parenthesize them inside And, Or, Xor and Not exactly like SymPy
 * (`z & (Implies(x, y))`, `~(Implies(x, y))`).
 */
export class LogicOp extends BoolOp {
  constructor(
    readonly name: LogicOpName,
    args: readonly Expr[],
  ) {
    // the op field carries the class name; LogicOp nodes are told apart by instanceof
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- core BoolOp.op is typed BoolOpName; LogicOp stores its own class name there (dispatch uses instanceof LogicOp)
    super(name as unknown as BoolOpName, args);
  }
  override get className(): string {
    return this.name;
  }
  /** Implies or Equivalent of new arguments (re-evaluated). */
  override withArgs(args: readonly Expr[]): Expr {
    return this.name === 'Implies' ? Implies(...args) : Equivalent(...args);
  }
  /** SymPy StrPrinter: Implies(a, b), Equivalent(a, b, ...). */
  override printStr(p: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(p).join(', ')})`;
  }
  /** SymPy LatexPrinter: a \Rightarrow b, a \Leftrightarrow b \Leftrightarrow c. */
  override printLatex(p: (e: Expr) => string): string {
    const sep = this.name === 'Implies' ? ' \\Rightarrow ' : ' \\Leftrightarrow ';
    return this.args.map((a) => (a instanceof BoolOp && a.op !== 'Not' ? `\\left(${p(a)}\\right)` : p(a))).join(sep);
  }
}

/** Names of the unevaluated gates (SymPy Nand(..., evaluate=False), ...). */
export type LogicGateName = 'Nand' | 'Nor' | 'Xnor' | 'ITE';

/**
 * An unevaluated Nand, Nor or Xnor gate or an ITE, printed Nand(a, b) and
 * ITE(a, b, c) like SymPy (function precedence: no parentheses inside And,
 * Or, Xor and Not).
 */
export class LogicGate extends ExtensionExpr {
  constructor(
    readonly gate: LogicGateName,
    args: readonly Expr[],
  ) {
    super(gate, args);
  }
  /** Rebuilding evaluates, like SymPy's func(*args). */
  withArgs(args: readonly Expr[]): Expr {
    return GATES[this.gate](args, true);
  }
}

/** e is a SymPy BooleanFunction (And, Or, Not, Xor, ITE, Implies, Equivalent, Nand, Nor, Xnor). */
export const isBooleanFunction = (e: Expr): boolean => e instanceof BoolOp || e instanceof LogicGate;

/** e is a SymPy Boolean (a boolean function, true/false, a relation, a symbol or an applied predicate such as Q.positive(x)). */
export const isBoolean = (e: Expr): boolean => isBooleanFunction(e) || e instanceof BoolAtom || e instanceof Rel || e instanceof Sym || e instanceof AppliedPredicate;

/** e is a BoolOp node of the given core operator (And, Or, Not, Xor, ITE). */
export const isOp = (e: Expr, op: BoolOpName): e is BoolOp => e instanceof BoolOp && !(e instanceof LogicOp) && e.op === op;

/** e is an ITE (the LogicGate of this module or the core BoolOp made by Piecewise). */
export const isITE = (e: Expr): boolean => isOp(e, 'ITE') || (e instanceof LogicGate && e.gate === 'ITE');

/** e is an Implies or Equivalent node. */
export const isLogicOp = (e: Expr, name: LogicOpName): e is LogicOp => e instanceof LogicOp && e.name === name;

/**
 * SymPy as_Boolean: 1 and true give true, 0 and false give false, a symbol
 * known to be zero or nonzero gives false or true, a Boolean is returned
 * unchanged; anything else is a TypeError.
 */
export function asBoolean(x: BoolLike): Expr {
  const e = toBool(x);
  if (e instanceof BoolAtom) return e;
  if (isNum(e) && e instanceof Rational && e.q === 1n && (e.p === 0n || e.p === 1n)) return e.p === 1n ? S.true : S.false;
  if (e instanceof Sym) {
    const z = triIsZero(e);
    if (z === undefined) return e;
    return z ? S.false : S.true;
  }
  if (isBoolean(e)) return e;
  throw new TypeError(`expecting bool or Boolean, not \`${impl.str(e)}\`.`);
}

/** Numbers 0 and 1 (and SymPy numbers in general) as false/true, other arguments unchanged. */
function numberToBool(e: Expr): Expr {
  if (isNum(e)) {
    const zero = e instanceof Rational ? e.p === 0n : e.isZero === true;
    return zero ? S.false : S.true;
  }
  return e;
}

// ---------------------------------------------------------------------------
// Relations: SymPy canonical and negated (used to recognize equal or
// complementary relations inside And, Or, Xor, Implies and Equivalent)

const REVERSED: Record<RelOp, RelOp> = { Eq: 'Eq', Ne: 'Ne', Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le' };
const NEGATED: Record<RelOp, RelOp> = { Eq: 'Ne', Ne: 'Eq', Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt' };

const reversedRel = (r: Rel): Rel => new Rel(REVERSED[r.op], r.rhs, r.lhs);
const reversedSign = (r: Rel): Rel => new Rel(r.op === 'Eq' || r.op === 'Ne' ? r.op : REVERSED[r.op], impl.mul(-1, r.lhs), impl.mul(-1, r.rhs));

/** SymPy Relational.negated: Not(x < y) is x >= y. */
export const relNegated = (r: Rel): Rel => new Rel(NEGATED[r.op], r.lhs, r.rhs);

/** SymPy Relational.canonical: numbers on the right, ordered sides, no leading minus sign. */
export function relCanonical(r0: Rel): Rel {
  let r = r0;
  if (isNumberExpr(r.rhs)) {
    // SymPy: only two Numbers (not sqrt(5) or pi) are put in increasing order
    if (isNumber(r.lhs) && isNumber(r.rhs) && greater(r.lhs, r.rhs)) r = reversedRel(r);
  } else if (isNumberExpr(r.lhs)) r = reversedRel(r);
  else if (at(ordered([r.lhs, r.rhs]), 0).key !== r.lhs.key) r = reversedRel(r);
  if (r.lhs instanceof BoolAtom || r.rhs instanceof BoolAtom) return r;
  if (couldExtractMinusSign(r.lhs)) return reversedSign(r);
  if (!isNumberExpr(r.rhs) && couldExtractMinusSign(r.rhs)) {
    const e1 = at(ordered([r.lhs, impl.mul(-1, r.rhs)]), 0);
    if (e1.key !== r.lhs.key) return reversedSign(reversedRel(r));
  }
  return r;
}

/** SymPy is_number: a numeric expression without symbols (2, sqrt(5), pi). */
const isNumberExpr = (e: Expr): boolean => !(e instanceof BoolAtom) && (e.isNumber || impl.freeSymbols(e).size === 0);

/** A SymPy Number: a rational or a float. */
const isNumber = (e: Expr): e is Rational | Float => e instanceof Rational || e instanceof Float;

/** a > b for two Numbers. */
function greater(a: Rational | Float, b: Rational | Float): boolean {
  const d = impl.add(a, impl.mul(-1, b));
  return d instanceof Rational ? d.p > 0n : d.toComplex().re > 0;
}

// ---------------------------------------------------------------------------
// And, Or, Not and Xor with SymPy's argument handling

/** SymPy And: numbers as booleans, equal relations merged, complementary relations give false. */
export function andFn(...xs: readonly BoolLike[]): Expr {
  return lattice('And', xs.map((x) => numberToBool(toBool(x))));
}

/** SymPy Or: numbers as booleans, equal relations merged, complementary relations give true. */
export function orFn(...xs: readonly BoolLike[]): Expr {
  return lattice('Or', xs.map((x) => numberToBool(toBool(x))));
}

function lattice(op: 'And' | 'Or', xs: readonly Expr[]): Expr {
  const r = op === 'And' ? coreAnd(...xs) : coreOr(...xs);
  if (!isOp(r, op)) return r;
  const seen: Rel[] = [];
  const kept: Expr[] = [];
  let dropped = false;
  for (const x of r.args) {
    if (x instanceof Rel) {
      const c = relCanonical(x);
      if (seen.some((s) => s.key === c.key)) {
        dropped = true;
        continue;
      }
      const nc = relCanonical(relNegated(c));
      if (seen.some((s) => s.key === nc.key)) return op === 'And' ? S.false : S.true;
      seen.push(c);
    }
    kept.push(x);
  }
  if (!dropped) return r;
  return op === 'And' ? coreAnd(...kept) : coreOr(...kept);
}

/** SymPy Not: numbers as booleans, double negation removed, relations negated. */
export function notFn(x: BoolLike): Expr {
  return coreNot(numberToBool(toBool(x)));
}

/**
 * SymPy Xor(*args, remove_true=...): true when an odd number of arguments
 * is true. With removeTrue (the default) a `true` argument becomes a
 * negation, Xor(x, True) = ~x; with removeTrue false it stays (x ^ True),
 * as in the algebraic normal form.
 */
export function xorFn(xs: readonly BoolLike[], removeTrue = true): Expr {
  const argset = new Map<string, Expr>();
  const toggle = (a: Expr): void => {
    if (argset.has(a.key)) argset.delete(a.key);
    else argset.set(a.key, a);
  };
  for (const x0 of xs) {
    let a = toBool(x0);
    if (isNum(a) || a instanceof BoolAtom) {
      if (isTrueAtom(numberToBool(a))) a = S.true;
      else continue;
    }
    if (isOp(a, 'Xor')) a.args.forEach(toggle);
    else toggle(a);
  }
  const rels = [...argset.values()].filter((r): r is Rel => r instanceof Rel).map((r) => [r, relCanonical(r), relCanonical(relNegated(r))] as const);
  let odd = false;
  const remove: [Expr, Expr][] = [];
  for (let i = 0; i < rels.length; i++) {
    const [r, c, nc] = at(rels, i);
    for (let j = i + 1; j < rels.length; j++) {
      const [rj, cj] = at(rels, j);
      if (cj.key === nc.key) {
        odd = !odd;
        remove.push([r, rj]);
        break;
      }
      if (cj.key === c.key) {
        remove.push([r, rj]);
        break;
      }
    }
  }
  if (odd) toggle(S.true);
  for (const [a, b] of remove) {
    argset.delete(a.key);
    argset.delete(b.key);
  }
  if (argset.size === 0) return S.false;
  if (argset.size === 1) return at([...argset.values()], 0);
  if (argset.has(S.true.key) && removeTrue) {
    argset.delete(S.true.key);
    return coreNot(xorFn([...argset.values()]));
  }
  return new BoolOp('Xor', ordered([...argset.values()]));
}

// ---------------------------------------------------------------------------
// Implies, Equivalent, gates, ITE, Exclusive

/**
 * SymPy Implies(a, b): logical implication, printed Implies(a, b). With a
 * boolean constant argument it is ~a | b; Implies(a, a) is true.
 */
export function Implies(...args: readonly BoolLike[]): Expr {
  if (args.length !== 2) throw new RangeError(`${args.length} operand(s) used for an Implies (pairs are required)`);
  const orig = args.map(toBool);
  const [A, B] = pair(orig.map(numberToBool));
  if (A instanceof BoolAtom || B instanceof BoolAtom) return orFn(notFn(A), B);
  if (A.key === B.key) return S.true;
  if (A instanceof Rel && B instanceof Rel) {
    const cb = relCanonical(B);
    if (relCanonical(A).key === cb.key) return S.true;
    if (relCanonical(relNegated(A)).key === cb.key) return B;
  }
  return new LogicOp('Implies', orig);
}

/**
 * SymPy Equivalent(*args): true when all arguments have the same truth
 * value, printed Equivalent(a, b, ...) with the arguments ordered.
 */
export function Equivalent(...args: readonly BoolLike[]): Expr {
  const argset = new Map<string, Expr>();
  for (const x0 of args) {
    const x = toBool(x0);
    const b = isNum(x) || x instanceof BoolAtom ? numberToBool(x) : x;
    argset.set(b.key, b);
  }
  const rels = [...argset.values()].filter((r): r is Rel => r instanceof Rel).map((r) => [r, relCanonical(r), relCanonical(relNegated(r))] as const);
  const remove: [Expr, Expr][] = [];
  for (let i = 0; i < rels.length; i++) {
    const [r, c, nc] = at(rels, i);
    for (let j = i + 1; j < rels.length; j++) {
      const [rj, cj] = at(rels, j);
      if (cj.key === nc.key) return S.false;
      if (cj.key === c.key) {
        remove.push([r, rj]);
        break;
      }
    }
  }
  // equal relations written differently (x > 1, 1 < x): one of them is enough
  for (const [, b] of remove) argset.delete(b.key);
  if (argset.size <= 1) return S.true;
  if (argset.has(S.true.key)) {
    argset.delete(S.true.key);
    return andFn(...argset.values());
  }
  if (argset.has(S.false.key)) {
    argset.delete(S.false.key);
    return andFn(...[...argset.values()].map(notFn));
  }
  return new LogicOp('Equivalent', ordered([...argset.values()]));
}

const GATES: Record<LogicGateName, (args: readonly Expr[], evaluate: boolean) => Expr> = {
  Nand: (args, ev) => (ev ? notFn(andFn(...args)) : new LogicGate('Nand', args)),
  Nor: (args, ev) => (ev ? notFn(orFn(...args)) : new LogicGate('Nor', args)),
  Xnor: (args, ev) => (ev ? notFn(xorFn(args)) : new LogicGate('Xnor', args)),
  ITE: (args, ev) => ITE(at(args, 0), at(args, 1), at(args, 2), { evaluate: ev }),
};

const splitOptions = (args: readonly (BoolLike | LogicEvalOptions)[]): [Expr[], boolean] => {
  const last = args[args.length - 1];
  const isOpts = (v: unknown): v is LogicEvalOptions => typeof v === 'object' && v !== null && !(v instanceof Expr);
  const toArg = (a: BoolLike | LogicEvalOptions): Expr => {
    if (isOpts(a)) throw new TypeError('the options object must be the last argument');
    return toBool(a);
  };
  if (args.length > 0 && isOpts(last)) return [args.slice(0, -1).map(toArg), last.evaluate !== false];
  return [args.map(toArg), true];
};

/** SymPy Nand(*args): Not(And(*args)); with `{ evaluate: false }` the unevaluated Nand(a, b). */
export function Nand(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Nand(xs, ev);
}

/** SymPy Nor(*args): Not(Or(*args)); with `{ evaluate: false }` the unevaluated Nor(a, b). */
export function Nor(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Nor(xs, ev);
}

/** SymPy Xnor(*args): Not(Xor(*args)); with `{ evaluate: false }` the unevaluated Xnor(a, b). */
export function Xnor(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Xnor(xs, ev);
}

/** SymPy Exclusive(*args): true when at most one argument is true. */
export function Exclusive(...args: readonly BoolLike[]): Expr {
  const xs = args.map(toBool);
  const out: Expr[] = [];
  for (let i = 0; i < xs.length; i++) for (let j = i + 1; j < xs.length; j++) out.push(notFn(andFn(at(xs, i), at(xs, j))));
  return andFn(...out);
}

/** SymPy binary_symbols: the symbols used as booleans. */
export function binarySymbols(e: Expr): Map<string, Expr> {
  const out = new Map<string, Expr>();
  if (e instanceof Sym) out.set(e.key, e);
  else if (e instanceof Rel) {
    if ((e.op === 'Eq' || e.op === 'Ne') && e.args.some((a) => a instanceof BoolAtom)) {
      if (e.lhs instanceof Sym) out.set(e.lhs.key, e.lhs);
      else if (e.rhs instanceof Sym) out.set(e.rhs.key, e.rhs);
    }
  } else if (isBooleanFunction(e)) {
    for (const a of e.args) {
      if (isBooleanFunction(a) || a instanceof Sym || (a instanceof Rel && (a.op === 'Eq' || a.op === 'Ne'))) {
        for (const [k, v] of binarySymbols(a)) out.set(k, v);
      }
    }
  }
  return out;
}

const isEqNe = (e: Expr): e is Rel => e instanceof Rel && (e.op === 'Eq' || e.op === 'Ne');

function iteEval(a0: Expr, b: Expr, c: Expr): Expr | undefined {
  let a = a0;
  if (isEqNe(a)) {
    const r = a;
    let hit = true;
    if (r.args.some(isTrueAtom)) a = isTrueAtom(r.rhs) ? r.lhs : r.rhs;
    else if (r.args.some(isFalseAtom)) a = isFalseAtom(r.rhs) ? notFn(r.lhs) : notFn(r.rhs);
    else hit = false;
    if (hit && r.op === 'Ne') a = notFn(a);
  }
  if (isTrueAtom(a)) return b;
  if (isFalseAtom(a)) return c;
  if (b.key === c.key) return b;
  if (isTrueAtom(b) && isFalseAtom(c)) return a;
  if (isFalseAtom(b) && isTrueAtom(c)) return notFn(a);
  if (a !== a0) return new LogicGate('ITE', [a, b, c]);
  return undefined;
}

/**
 * SymPy ITE(a, b, c): if a then b else c. Constant conditions and equal
 * branches evaluate; Eq/Ne of a binary symbol with true/false is read as
 * the symbol or its negation.
 */
export function ITE(a0: BoolLike, b0: BoolLike, c0: BoolLike, opts: LogicEvalOptions = {}): Expr {
  let a = toBool(a0);
  let b: Expr;
  let c: Expr;
  if (isEqNe(a)) {
    b = asBoolean(b0);
    c = asBoolean(c0);
    const bin = new Map([...binarySymbols(b), ...binarySymbols(c)]);
    const rest = new Map(a.args.map((x) => [x.key, x] as const));
    for (const k of bin.keys()) rest.delete(k);
    if (rest.size === 1) {
      const r = a;
      if (isTrueAtom(r.lhs)) a = r.rhs;
      else if (isTrueAtom(r.rhs)) a = r.lhs;
      else if (isFalseAtom(r.lhs)) a = notFn(r.rhs);
      else if (isFalseAtom(r.rhs)) a = notFn(r.lhs);
      else a = S.false;
      if (r.op === 'Ne') a = notFn(a);
    }
  } else {
    a = asBoolean(a);
    b = asBoolean(b0);
    c = asBoolean(c0);
  }
  const rv = opts.evaluate === false ? undefined : iteEval(a, b, c);
  return rv ?? new LogicGate('ITE', [a, b, c]);
}

// ---------------------------------------------------------------------------
// Structure

/**
 * SymPy is_literal: a symbol or other atom, a negated literal, or a
 * non-boolean expression whose arguments are atoms (x + y).
 */
export function isLiteral(e: Expr): boolean {
  if (isOp(e, 'Not')) return isLiteral(at(e.args, 0));
  if (e instanceof BoolAtom || e.args.length === 0) return true;
  return !isBooleanFunction(e) && e.args.every((a) => a.args.length === 0);
}

/** SymPy conjuncts: the arguments of an And, or the expression itself (ordered). */
export function conjuncts(expr: BoolLike): Expr[] {
  const e = toBool(expr);
  return isOp(e, 'And') ? [...e.args] : [e];
}

/** SymPy disjuncts: the arguments of an Or, or the expression itself (ordered). */
export function disjuncts(expr: BoolLike): Expr[] {
  const e = toBool(expr);
  return isOp(e, 'Or') ? [...e.args] : [e];
}

/** The boolean node rebuilt from new arguments with SymPy's evaluation. */
export function rebuildBool(e: Expr, args: readonly Expr[]): Expr {
  if (e instanceof LogicOp) return e.name === 'Implies' ? Implies(...args) : Equivalent(...args);
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'And':
        return andFn(...args);
      case 'Or':
        return orFn(...args);
      case 'Not':
        return notFn(at(args, 0));
      case 'Xor':
        return xorFn(args);
      case 'ITE':
        return ITE(at(args, 0), at(args, 1), at(args, 2));
    }
  }
  return rebuild(e, args);
}

/** SymPy xreplace through boolean functions (which the core traversal does not rebuild). */
export function boolXreplace(e: Expr, reps: ReadonlyMap<string, Expr>): Expr {
  if (reps.size === 0) return e;
  const go = (x: Expr): Expr => {
    const r = reps.get(x.key);
    if (r !== undefined) return r;
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    return args.some((a, i) => a !== x.args[i]) ? rebuildBool(x, args) : x;
  };
  return go(e);
}

/** All subexpressions satisfying pred (SymPy atoms(Type)), in traversal order without duplicates. */
export function collect(e: Expr, pred: (x: Expr) => boolean): Expr[] {
  const out = new Map<string, Expr>();
  const go = (x: Expr): void => {
    if (pred(x)) out.set(x.key, x);
    x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/** SymPy _find_predicates: the maximal subexpressions that are not boolean functions. */
export function findPredicates(e: Expr): Expr[] {
  const out = new Map<string, Expr>();
  const go = (x: Expr): void => {
    if (!isBooleanFunction(x)) out.set(x.key, x);
    else x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/** The truth value of e when every predicate has a value in env (keyed by expression key). */
export function evalBool(e: Expr, env: ReadonlyMap<string, boolean>): boolean {
  const v = env.get(e.key);
  if (v !== undefined) return v;
  if (e instanceof BoolAtom) return e.value;
  if (isNum(e)) return isTrueAtom(numberToBool(e));
  const args = (): boolean[] => e.args.map((a) => evalBool(a, env));
  if (e instanceof LogicOp) {
    const [a, ...rest] = args();
    return e.name === 'Implies' ? !a || at(rest, 0) : rest.every((b) => b === a);
  }
  if (e instanceof BoolOp) {
    switch (e.op) {
      case 'And':
        return args().every(Boolean);
      case 'Or':
        return args().some(Boolean);
      case 'Not':
        return !evalBool(at(e.args, 0), env);
      case 'Xor':
        return args().filter(Boolean).length % 2 === 1;
      case 'ITE':
        return evalBool(at(e.args, 0), env) ? evalBool(at(e.args, 1), env) : evalBool(at(e.args, 2), env);
    }
  }
  if (e instanceof LogicGate) {
    if (e.gate === 'ITE') return evalBool(at(e.args, 0), env) ? evalBool(at(e.args, 1), env) : evalBool(at(e.args, 2), env);
    const xs = args();
    if (e.gate === 'Nand') return !xs.every(Boolean);
    if (e.gate === 'Nor') return !xs.some(Boolean);
    return xs.filter(Boolean).length % 2 === 0;
  }
  throw new NotImplementedError(`cannot determine the truth value of ${impl.str(e)}`);
}
