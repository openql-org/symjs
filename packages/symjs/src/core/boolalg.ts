// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Boolean connectives And, Or and Not over relations (SymPy
 * logic.boolalg, the parts used by inequality solving).
 */

import type { ExprLike } from './nodes';
import { BoolAtom, Expr, Rational, Rel, S, Special, impl, isNum } from './nodes';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at } from './guard';

/** Boolean differentiation supplied by the logic module. */
export const booleanCalculus: { derivative?: (e: Expr, x: Expr) => Expr | undefined } = {};

export type BoolOpName = 'And' | 'Or' | 'Not' | 'Xor' | 'ITE';

/** And(...), Or(...) or Not(x). @internal ctor: use and/or/not. */
export class BoolOp extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'BoolOp' as const;
  /**
   * Creates a Boolean expression.
   *
   * @param op - The logical operator.
   * @param args - The operands in node order.
   */
  constructor(
    /** The logical operator applied to the arguments. */
    readonly op: BoolOpName,
    /** The operands of the expression in node order. */
    readonly args: readonly Expr[],
  ) {
    super();
  }
  /** The name of the logical operator. */
  get className(): string {
    return this.op;
  }
  protected computeKey(): string {
    return `${this.op}(${this.args.map((a) => a.key).join(',')})`;
  }
  /**
   * Tests whether a subexpression occurs in the Boolean expression.
   *
   * @param sub - The subexpression to find.
   * @returns Whether the queried expression occurs.
   */
  override has(sub: Expr): boolean {
    if ((this.op === 'And' || this.op === 'Or') && sub instanceof BoolOp && sub.op === this.op) {
      const keys = new Set(this.args.map((a) => a.key));
      if (sub.args.every((a) => keys.has(a.key))) return true;
    }
    return super.has(sub);
  }
  /**
   * Substitute inside associative gates, including subsets of their operands.
   *
   * @param old - The expression to replace.
   * @param replacement - The value to substitute.
   * @param recurse - The substitution callback for child expressions.
   * @returns The expression with the requested substitution applied.
   */
  subsSelf(old: Expr, replacement: Expr, recurse: (arg: Expr) => Expr): Expr | undefined {
    if (this.op !== 'And' && this.op !== 'Or' && this.op !== 'Xor') return undefined;
    const absorbing = this.op === 'And' ? S.false : this.op === 'Or' ? S.true : undefined;
    let invalid: TypeError | undefined;
    const terms: Expr[] = [];
    for (const arg of this.args) {
      try {
        const term = recurse(arg);
        if (term === absorbing) return term;
        terms.push(term);
      } catch (err) {
        if (!(err instanceof TypeError) || !absorbing) throw err;
        invalid = err;
      }
    }
    if (invalid) throw invalid;
    if (old instanceof BoolOp && old.op === this.op) {
      const keys = new Set(old.args.map((a) => a.key));
      if (old.args.every((a) => terms.some((t) => t.key === a.key))) {
        return this.withArgs([...terms.filter((t) => !keys.has(t.key)), replacement]);
      }
    }
    return terms.some((a, i) => a !== this.args[i]) ? this.withArgs(terms) : this;
  }
  /**
   * A node of the same class with new arguments (re-evaluated).
   *
   * @param args - The operands in node order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    switch (this.op) {
      case 'And':
        return and(...args);
      case 'Or':
        return or(...args);
      case 'Not':
        return not(at(args, 0));
      case 'Xor':
        return xor(...args);
      case 'ITE':
        return new BoolOp('ITE', args);
    }
  }
  /**
   * SymPy LatexPrinter: x \wedge y, x \vee y, x \veebar y, \neg x, \operatorname{ITE}(c, a, b).
   *
   * @param p - The expression printer for child nodes.
   * @returns The LaTeX representation.
   */
  printLatex(p: (e: Expr) => string): string {
    const paren = (a: Expr) => (a instanceof BoolOp && a.op !== 'Not' ? `\\left(${p(a)}\\right)` : p(a));
    if (this.op === 'Not') {
      const a = at(this.args, 0);
      // SymPy _print_Not: a negated Implies or Equivalent with a negated arrow
      const arrow = a instanceof BoolOp ? NEGATED_ARROWS[a.className] : undefined;
      if (arrow !== undefined) return a.args.map(paren).join(arrow);
      return a instanceof BoolOp ? `\\neg \\left(${p(a)}\\right)` : `\\neg ${p(a)}`;
    }
    if (this.op === 'ITE') return `\\operatorname{ITE}\\left(${this.args.map(p).join(', ')}\\right)`;
    const sep = this.op === 'And' ? ' \\wedge ' : this.op === 'Or' ? ' \\vee ' : ' \\veebar ';
    return this.args.map(paren).join(sep);
  }
  /**
   * SymPy StrPrinter: args sorted by default_sort_key, joined by & or |.
   *
   * @param p - The expression printer for child nodes.
   * @returns The formatted expression.
   */
  printStr(p: (e: Expr) => string): string {
    if (this.op === 'ITE') return `ITE(${this.args.map(p).join(', ')})`;
    if (this.op === 'Not') {
      const a = at(this.args, 0);
      return a instanceof Rel || a instanceof BoolOp ? `~(${p(a)})` : `~${p(a)}`;
    }
    const sep = this.op === 'And' ? ' & ' : this.op === 'Xor' ? ' ^ ' : ' | ';
    let args = [...this.args];
    if (this.op === 'And') {
      // SymPy _print_And: relations whose canonical rhs is -oo come first
      const front = args.filter((a) => a instanceof Rel && canonicalRhsIsNegOo(a));
      args = [...front, ...args.filter((a) => !front.includes(a))];
    }
    return args
      .map((a) => ((a instanceof Rel && a.op !== 'Eq' && a.op !== 'Ne') || (a instanceof BoolOp && a.op !== 'Not') ? `(${p(a)})` : p(a)))
      .join(sep);
  }
}

/** The negated arrows of Implies and Equivalent in LaTeX. */
const NEGATED_ARROWS: Partial<Record<string, string>> = { Implies: ' \\not\\Rightarrow ', Equivalent: ' \\not\\Leftrightarrow ' };

/** SymPy ordered(): node count, then default_sort_key. */
const sortArgs = (xs: readonly Expr[]): Expr[] =>
  impl.ordered ? impl.ordered(xs) : [...xs].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
/**
 * Rel.canonical puts a symbol-like side on the left; is the right side -oo?
 * (A relation between -oo and oo evaluates, so -oo on the left faces a finite side.)
 */
const canonicalRhsIsNegOo = (r: Rel): boolean => isNegOo(r.rhs) || isNegOo(r.lhs);
/**
 * A boolean argument: the integers 1 and 0 are true and false; any other number
 * is not a boolean (SymPy as_Boolean: TypeError).
 */
const boolArg = (x0: ExprLike | boolean): Expr => {
  const x = typeof x0 === 'boolean' ? (x0 ? S.true : S.false) : impl.sympify(x0);
  if (!isNum(x)) return x;
  if (x instanceof Rational && x.isInteger && (x.p === 1n || x.p === 0n)) return x.p === 1n ? S.true : S.false;
  throw new TypeError(`expecting bool or Boolean, not \`${impl.str(x)}\`.`);
};
const isTrue = (e: Expr) => e instanceof BoolAtom && e.value;
const isFalse = (e: Expr) => e instanceof BoolAtom && !e.value;

function lattice(op: 'And' | 'Or', xs: readonly (ExprLike | boolean)[]): Expr {
  const identity = op === 'And' ? S.true : S.false;
  const zero = op === 'And' ? S.false : S.true;
  const out = new Map<string, Expr>();
  const visit = (x: Expr) => {
    if (x instanceof BoolOp && x.op === op) x.args.forEach(visit);
    else out.set(x.key, x);
  };
  for (const x0 of xs) {
    const x = boolArg(x0);
    if (x.key === zero.key) return zero;
    if (x.key === identity.key) continue;
    visit(x);
  }
  if (out.size === 0) return identity;
  if (out.size === 1) return at([...out.values()], 0);
  return new BoolOp(op, sortArgs([...out.values()]));
}

/**
 * Forms the logical conjunction of the propositions.
 *
 * @param xs - The propositions to combine.
 * @returns The simplified Boolean expression.
 * @see SymPy `sympy.logic.boolalg.And`
 * @example
 * ```ts
 * import { And } from '@symjs/symjs';
 *
 * And(true, false); // => False
 * ```
 */
export const and = (...xs: (ExprLike | boolean)[]): Expr => lattice('And', xs);
/**
 * Forms the logical disjunction of the propositions.
 *
 * @param xs - The propositions to combine.
 * @returns The simplified Boolean expression.
 * @see SymPy `sympy.logic.boolalg.Or`
 * @example
 * ```ts
 * import { Or } from '@symjs/symjs';
 *
 * Or(true, false); // => True
 * ```
 */
export const or = (...xs: (ExprLike | boolean)[]): Expr => lattice('Or', xs);
export function not(x0: ExprLike | boolean): Expr {
  // SymPy Not(n) for a number n is the negation of its truth value (Not(2) is False)
  const x = typeof x0 === 'boolean' ? (x0 ? S.true : S.false) : impl.sympify(x0);
  if (isNum(x)) return x.isZero ? S.true : S.false;
  if (isTrue(x)) return S.false;
  if (isFalse(x)) return S.true;
  if (x instanceof BoolOp && x.op === 'Not') return at(x.args, 0);
  if (x instanceof Rel) {
    const neg = { Eq: 'Ne', Ne: 'Eq', Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt' } as const;
    return new Rel(neg[x.op], x.lhs, x.rhs);
  }
  return new BoolOp('Not', [x]);
}

/**
 * True when an odd number of the arguments is true.
 *
 * @param xs - The propositions to combine.
 * @returns The exclusive disjunction of the arguments.
 * @see SymPy `sympy.logic.boolalg.Xor`
 * @example
 * ```ts
 * import { Xor } from '@symjs/symjs';
 *
 * Xor(true, true); // => False
 * Xor(true, false); // => True
 * ```
 */
export function xor(...xs: (ExprLike | boolean)[]): Expr {
  return xorArgs(xs.map(boolArg), true);
}

/** Reduce nested parity gates, matching relations in a common orientation. */
export function xorArgs(args: readonly Expr[], removeTrue: boolean, canonical?: (r: Rel) => Rel): Expr {
  const terms = new Map<string, Expr>();
  let parity = 0;
  const toggle = (x: Expr): void => {
    if (x instanceof BoolOp && x.op === 'Xor') {
      x.args.forEach(toggle);
      return;
    }
    if (x instanceof BoolAtom) {
      if (x.value) parity ^= 1;
      return;
    }
    let key = x.key;
    if (x instanceof Rel) {
      const reversed = { Eq: 'Eq', Ne: 'Ne', Lt: 'Gt', Gt: 'Lt', Le: 'Ge', Ge: 'Le' } as const;
      const r = canonical ? canonical(x) : x.lhs.key > x.rhs.key ? new Rel(reversed[x.op], x.rhs, x.lhs) : x;
      key = r.key;
      if (terms.delete(not(r).key)) {
        parity ^= 1;
        return;
      }
    }
    if (!terms.delete(key)) terms.set(key, x);
  };
  args.forEach(toggle);
  if (!terms.size) return parity ? S.true : S.false;
  if (parity && !removeTrue) terms.set(S.true.key, S.true);
  const rest = [...terms.values()];
  const core = rest.length === 1 ? at(rest, 0) : new BoolOp('Xor', sortArgs(rest));
  return parity && removeTrue ? not(core) : core;
}
