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
import { BoolOp, booleanCalculus, and as coreAnd, not as coreNot, or as coreOr, xorArgs } from '../core/boolalg';
import type { ExprLike, RelOp } from '../core/nodes';
import { BoolAtom, Expr, ExtensionExpr, Float, Rational, Rel, S, Sym, impl, isNum } from '../core/nodes';
import { isZero as triIsZero } from '../core/assumptions';
import { Eq, piecewise } from '../core/logic';
import { ordered } from '../core/match';
import { rebuild } from '../core/traverse';
import { couldExtractMinusSign } from '../core/ops';
import { NotImplementedError } from '../core/errors';
import { AppliedPredicate, registerRefineHandler } from '../core/refine';
import { parserHooks } from '../parsing/parser';

/** An argument of the boolean constructors: an expression or a JavaScript boolean. */
export type BoolLike = ExprLike | boolean;

/** Options of the boolean constructors. */
export interface LogicEvalOptions {
  /** Evaluates to a simpler form when possible (default true). */
  evaluate?: boolean;
}

/** @internal An expression from an ExprLike or a JavaScript boolean. */
export const toBool = (x: BoolLike): Expr => (typeof x === 'boolean' ? (x ? S.true : S.false) : impl.sympify(x));

const isTrueAtom = (e: Expr): boolean => e instanceof BoolAtom && e.value;
const isFalseAtom = (e: Expr): boolean => e instanceof BoolAtom && !e.value;

/** Names of the boolean functions printed as Name(args) with the precedence of Xor. */
export type LogicOpName = 'Implies' | 'Equivalent';

/** Represents a symbolic implication or equivalence. */
export class LogicOp extends BoolOp {
  /**
   * Creates a LogicOp instance.
   *
   * @param name - The Boolean connective.
   * @param args - The propositions joined by the connective.
   */
  constructor(
    /** The name of the Boolean connective. */
    readonly name: LogicOpName,
    args: readonly Expr[],
  ) {
    // the op field carries the class name; LogicOp nodes are told apart by instanceof
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- core BoolOp.op is typed BoolOpName; LogicOp stores its own class name there (dispatch uses instanceof LogicOp)
    super(name as unknown as BoolOpName, args);
  }
  /**
   * Represents the symbolic class name used by printers.
   *
   * @returns The symbolic class name used by printers.
   */
  override get className(): string {
    return this.name;
  }
  /**
   * Implies or Equivalent of new arguments (re-evaluated).
   *
   * @param args - The operands in their defining order.
   * @returns The expression with the replacement operands.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return this.name === 'Implies' ? Implies(...args) : Equivalent(...args);
  }
  /**
   * Implies(a, b), Equivalent(a, b, ...).
   *
   * @param p - The callback for printing child expressions.
   * @returns The formatted text.
   */
  override printStr(p: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(p).join(', ')})`;
  }
  /**
   * A \Rightarrow b, a \Leftrightarrow b \Leftrightarrow c.
   *
   * @param p - The callback for printing child expressions.
   * @returns The formatted LaTeX source.
   */
  override printLatex(p: (e: Expr) => string): string {
    const sep = this.name === 'Implies' ? ' \\Rightarrow ' : ' \\Leftrightarrow ';
    return this.args.map((a) => (a instanceof BoolOp && a.op !== 'Not' ? `\\left(${p(a)}\\right)` : p(a))).join(sep);
  }
}

/** Names of the unevaluated gates. */
export type LogicGateName = 'Nand' | 'Nor' | 'Xnor' | 'ITE';

/** Represents an unevaluated Boolean gate with its operands. */
export class LogicGate extends ExtensionExpr {
  /**
   * Creates a LogicGate instance.
   *
   * @param gate - The gate applied to the operands.
   * @param args - The Boolean operands in gate order.
   */
  constructor(
    /** The Boolean gate represented by the node. */
    readonly gate: LogicGateName,
    args: readonly Expr[],
  ) {
    super(gate, args);
  }
  /**
   * Rebuilding evaluates, like SymPy's func(*args).
   *
   * @param args - The operands in their defining order.
   * @returns The expression with the replacement operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return GATES[this.gate](args, true);
  }
}

/** Tests whether the expression is a Boolean function, such as `And`, `Implies`, or `ITE`. */
export const isBooleanFunction = (e: Expr): boolean => e instanceof BoolOp || e instanceof LogicGate;

/** Tests whether the expression is a Boolean function, truth value, relation, symbol, or applied predicate. */
export const isBoolean = (e: Expr): boolean => isBooleanFunction(e) || e instanceof BoolAtom || e instanceof Rel || e instanceof Sym || e instanceof AppliedPredicate;

/** Tests whether the expression is a core Boolean operation with the specified operator. */
export const isOp = (e: Expr, op: BoolOpName): e is BoolOp => e instanceof BoolOp && !(e instanceof LogicOp) && e.op === op;

/** Tests whether the expression represents an if-then-else operation. */
export const isITE = (e: Expr): boolean => isOp(e, 'ITE') || (e instanceof LogicGate && e.gate === 'ITE');

/** Tests whether the expression is a logic node with the specified `Implies` or `Equivalent` operator. */
export const isLogicOp = (e: Expr, name: LogicOpName): e is LogicOp => e instanceof LogicOp && e.name === name;

/**
 * Converts Boolean expressions, zero, one and symbols with known truth values into symbolic Boolean values.
 *
 * @param x - The proposition, symbol or truth value to convert.
 * @returns A symbolic Boolean value or proposition.
 * @throws TypeError when the value has no Boolean interpretation.
 * @see SymPy `sympy.logic.boolalg.as_Boolean`
 * @example
 * ```ts
 * import { asBoolean } from '@symjs/symjs';
 * asBoolean(1); // => True
 * ```
 */
export function asBoolean(x: BoolLike): Expr {
  const e = toBool(x);
  if (e instanceof BoolAtom) return e;
  if (isNum(e) && e instanceof Rational && e.q === 1n && (e.p === 0n || e.p === 1n)) return e.p === 1n ? S.true : S.false;
  // the core knows a symbol to be nonzero (zero=False) but never to be zero
  if (e instanceof Sym) return triIsZero(e) === false ? S.true : e;
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

/**
 * Negates a relation while preserving its operands. For example, `x < y` becomes `x >= y`.
 *
 * @see SymPy `sympy.core.relational.Relational.negated`
 */
export const relNegated = (r: Rel): Rel => new Rel(NEGATED[r.op], r.lhs, r.rhs);

/**
 * Normalizes the order and signs of a relation's operands, placing a lone numeric operand on the
 * right.
 *
 * @see SymPy `sympy.core.relational.Relational.canonical`
 */
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

/**
 * Forms the logical conjunction of the arguments, interpreting numbers as truth values and
 * merging equivalent relations. Complementary relations give `false`.
 *
 * @see SymPy `sympy.logic.boolalg.And`
 */
export function andFn(...xs: readonly BoolLike[]): Expr {
  return lattice('And', xs.map((x) => numberToBool(toBool(x))));
}

/**
 * Forms the logical disjunction of the arguments, interpreting numbers as truth values and
 * merging equivalent relations. Complementary relations give `true`.
 *
 * @see SymPy `sympy.logic.boolalg.Or`
 */
export function orFn(...xs: readonly BoolLike[]): Expr {
  return lattice('Or', xs.map((x) => numberToBool(toBool(x))));
}

function lattice(op: 'And' | 'Or', xs: readonly Expr[]): Expr {
  const r = op === 'And' ? coreAnd(...xs) : coreOr(...xs);
  if (!isOp(r, op)) return r;
  // SymPy And looks at the flattened arguments in sorted order, Or at the given arguments in the given order
  const args = op === 'And' ? r.args : xs;
  const seen: Rel[] = [];
  const kept: Expr[] = [];
  let dropped = false;
  for (const x of args) {
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

/**
 * Negates a Boolean expression, interpreting numeric arguments as truth values, cancelling
 * double negation, and inverting relations.
 *
 * @see SymPy `sympy.logic.boolalg.Not`
 */
export function notFn(x: BoolLike): Expr {
  return coreNot(numberToBool(toBool(x)));
}

/**
 * Forms an exclusive disjunction, which is true when an odd number of arguments are true. By
 * default a `true` operand negates the remaining expression. Set `removeTrue` to `false` to
 * retain it for algebraic normal form.
 *
 * @see SymPy `sympy.logic.boolalg.Xor`
 */
export function xorFn(xs: readonly BoolLike[], removeTrue = true): Expr {
  return xorArgs(xs.map((x) => numberToBool(toBool(x))), removeTrue, relCanonical);
}

// ---------------------------------------------------------------------------
// Implies, Equivalent, gates, ITE, Exclusive

/**
 * Forms the implication from its first operand to its second operand.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns The implication from the first argument to the second.
 * @see SymPy `sympy.logic.boolalg.Implies`
 * @example
 * ```ts
 * import { Implies } from '@symjs/symjs';
 * Implies(true, true); // => True
 * ```
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
 * Tests whether all operands agree in truth value.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns The proposition that all arguments have the same truth value.
 * @see SymPy `sympy.logic.boolalg.Equivalent`
 * @example
 * ```ts
 * import { Equivalent, ex } from '@symjs/symjs';
 * Equivalent(ex`x`, ex`x`); // => True
 * ```
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

/**
 * Negates the conjunction of its operands.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns The negation of the conjunction.
 * @see SymPy `sympy.logic.boolalg.Nand`
 * @example
 * ```ts
 * import { Nand } from '@symjs/symjs';
 * Nand(true, true); // => False
 * ```
 */
export function Nand(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Nand(xs, ev);
}

/**
 * Negates the disjunction of its operands.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns The negation of the disjunction.
 * @see SymPy `sympy.logic.boolalg.Nor`
 * @example
 * ```ts
 * import { Nor } from '@symjs/symjs';
 * Nor(true, true); // => False
 * ```
 */
export function Nor(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Nor(xs, ev);
}

/**
 * Negates the exclusive disjunction of its operands.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns The negation of the exclusive disjunction.
 * @see SymPy `sympy.logic.boolalg.Xnor`
 * @example
 * ```ts
 * import { Xnor } from '@symjs/symjs';
 * Xnor(true, true); // => True
 * ```
 */
export function Xnor(...args: readonly (BoolLike | LogicEvalOptions)[]): Expr {
  const [xs, ev] = splitOptions(args);
  return GATES.Xnor(xs, ev);
}

/**
 * Forms a proposition that is true when at most one operand is true.
 *
 * @param args - The Boolean operands, optionally followed by evaluation settings.
 * @returns A proposition that is true when at most one operand is true.
 * @see SymPy `sympy.logic.boolalg.Exclusive`
 * @example
 * ```ts
 * import { Exclusive } from '@symjs/symjs';
 * Exclusive(false, true, true); // => False
 * ```
 */
export function Exclusive(...args: readonly BoolLike[]): Expr {
  const xs = args.map(toBool);
  const out: Expr[] = [];
  for (let i = 0; i < xs.length; i++) for (let j = i + 1; j < xs.length; j++) out.push(notFn(andFn(at(xs, i), at(xs, j))));
  return andFn(...out);
}

/**
 * Finds the set on which a Boolean expression holds, solving its relational subexpressions over
 * the reals.
 *
 * @see SymPy `sympy.logic.boolalg.Boolean.as_set`
 */
export function booleanAsSet<T extends Expr>(
  input: BoolLike,
  solveSet: (e: Expr) => T,
  periodOf: (r: Rel, x: Sym) => Expr | undefined,
  empty: T,
  reals: T,
): T {
  const e = toBool(input);
  const symbols = [...e.freeSymbols()].filter((arg) => arg instanceof Sym);
  if (symbols.length !== 1) return solveSet(e);
  const x = at(symbols, 0);
  const visit = (arg: Expr): Expr => {
    if (arg instanceof Sym) return S.true;
    if (arg instanceof Rel) {
      const period = periodOf(arg, x);
      if (!period || period === S.Zero) return arg;
      const result = solveSet(arg);
      if (result === empty) return S.false;
      if (result === reals) return S.true;
      throw new NotImplementedError('as_set is not implemented for relationals with periodic solutions');
    }
    if (isITE(arg)) {
      const branches = arg.args.map(visit);
      const c = at(branches, 0);
      return orFn(andFn(c, at(branches, 1)), andFn(notFn(c), at(branches, 2)));
    }
    if (isBooleanFunction(arg)) return rebuildBool(arg, arg.args.map(visit));
    return arg;
  };
  return solveSet(visit(e));
}

/**
 * The symbols used as booleans.
 *
 * @param e - The Boolean expression to examine.
 * @returns The symbols used in Boolean positions, indexed by structural key.
 * @see SymPy `sympy.logic.boolalg.Boolean.binary_symbols`
 */
export function binarySymbols(e: Expr): Map<string, Expr> {
  const out = new Map<string, Expr>();
  if (e instanceof Sym) out.set(e.key, e);
  else if (e instanceof Rel) {
    if ((e.op === 'Eq' || e.op === 'Ne') && e.args.some((a) => a instanceof BoolAtom)) {
      if (e.lhs instanceof Sym) out.set(e.lhs.key, e.lhs);
      else if (e.rhs instanceof Sym) out.set(e.rhs.key, e.rhs);
    }
  } else if (e instanceof AppliedPredicate && e.predicate === 'is_true') {
    return binarySymbols(e.arg);
  } else if (e instanceof AppliedPredicate && (e.predicate === 'eq' || e.predicate === 'ne')) {
    return binarySymbols(new Rel(e.predicate === 'eq' ? 'Eq' : 'Ne', at(e.args, 0), at(e.args, 1)));
  } else if (isBooleanFunction(e)) {
    for (const a of e.args) {
      if (isBooleanFunction(a) || a instanceof Sym || (a instanceof Rel && (a.op === 'Eq' || a.op === 'Ne'))) {
        for (const [k, v] of binarySymbols(a)) out.set(k, v);
      }
    }
  }
  return out;
}

booleanCalculus.derivative = (e, x) => {
  if (!isBooleanFunction(e) || !binarySymbols(e).has(x.key)) return undefined;
  const low = e.subs(x, S.false);
  const high = e.subs(x, S.true);
  const [a, b] = pair(ordered([low, high]));
  return piecewise([S.Zero, Eq(a, b)], [S.One, true]);
};

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
 * Chooses between two Boolean branches according to a Boolean condition.
 *
 * @param a0 - The Boolean condition.
 * @param b0 - The branch selected when the condition holds.
 * @param c0 - The branch selected when the condition is false.
 * @param opts - The logic eval settings.
 * @returns The second or third operand selected by the first, or a symbolic conditional.
 * @throws RangeError when the conditional has a different number of operands than three.
 * @see SymPy `sympy.logic.boolalg.ITE`
 * @example
 * ```ts
 * import { ITE } from '@symjs/symjs';
 * ITE(true, false, true); // => False
 * ```
 */
export function ITE(a0: BoolLike, b0: BoolLike, c0: BoolLike, opts: LogicEvalOptions = {}): Expr {
  if (arguments.length > 4 || opts instanceof Expr) throw new RangeError('ITE requires three operands');
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
 * A symbol or other atom, a negated literal, or a
 * non-boolean expression whose arguments are atoms (x + y).
 *
 * @param e - The Boolean expression to examine.
 * @returns Whether the expression is an atom or a negated atom.
 * @see SymPy `sympy.logic.boolalg.is_literal`
 * @example
 * ```ts
 * import { ex, isLiteral } from '@symjs/symjs';
 * isLiteral(ex`A`); // => True
 * ```
 */
export function isLiteral(e: Expr): boolean {
  if (isOp(e, 'Not')) return isLiteral(at(e.args, 0));
  if (e instanceof BoolAtom || e.args.length === 0) return true;
  return !isBooleanFunction(e) && e.args.every((a) => a.args.length === 0);
}

/**
 * Returns the arguments of an And, or the expression itself (ordered).
 *
 * @param expr - The Boolean expression to examine.
 * @returns The arguments of an And, or the expression itself (ordered).
 * @see SymPy `sympy.logic.boolalg.conjuncts`
 * @example
 * ```ts
 * import { conjuncts, ex } from '@symjs/symjs';
 * conjuncts(ex`A & B`); // => [A, B]
 * ```
 */
export function conjuncts(expr: BoolLike): Expr[] {
  const e = toBool(expr);
  return isOp(e, 'And') ? [...e.args] : [e];
}

/**
 * Returns the arguments of an Or, or the expression itself (ordered).
 *
 * @param expr - The Boolean expression to examine.
 * @returns The arguments of an Or, or the expression itself (ordered).
 * @see SymPy `sympy.logic.boolalg.disjuncts`
 * @example
 * ```ts
 * import { disjuncts, ex } from '@symjs/symjs';
 * disjuncts(ex`A | B`); // => [A, B]
 * ```
 */
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

/**
 * Replaces subexpressions by exact key match, including those nested inside Boolean functions.
 *
 * @see SymPy `sympy.core.basic.Basic.xreplace`
 */
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

/** Collects the distinct maximal subexpressions that are not Boolean functions. */
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

// SymPy's parse_expr knows these by name; the parser is in a lower layer, so they are registered here
parserHooks.constructors.set('Implies', (args) => Implies(...args));
parserHooks.constructors.set('Equivalent', (args) => Equivalent(...args));
parserHooks.constructors.set('Nand', (args) => Nand(...args));
parserHooks.constructors.set('Nor', (args) => Nor(...args));
parserHooks.constructors.set('ITE', (args) => {
  if (args.length < 3) throw new SyntaxError('ITE() takes at least 3 arguments');
  return ITE(at(args, 0), at(args, 1), at(args, 2));
});

// SymPy Boolean._eval_refine: a proposition or its complement may be assumed directly.
registerRefineHandler((expr, assumptions) => {
  if (!(expr instanceof Rel)) return expr;
  const facts = typeof assumptions === 'boolean' ? [] : assumptions instanceof Expr ? conjuncts(assumptions) : assumptions.flatMap(conjuncts);
  const key = relCanonical(expr).key;
  const negatedKey = relCanonical(relNegated(expr)).key;
  for (const fact of facts) {
    if (!(fact instanceof Rel)) continue;
    const canonical = relCanonical(fact).key;
    if (canonical === key) return S.true;
    if (canonical === negatedKey) return S.false;
  }
  return expr;
});
