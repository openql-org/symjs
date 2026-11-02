// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Boolean connectives And, Or and Not over relations (SymPy
 * logic.boolalg, the parts used by inequality solving).
 */

import type { ExprLike } from './nodes';
import { BoolAtom, Expr, Rational, Rel, S, Special, impl } from './nodes';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at } from './guard';

export type BoolOpName = 'And' | 'Or' | 'Not' | 'Xor' | 'ITE';

/** And(...), Or(...) or Not(x). @internal ctor: use and/or/not. */
export class BoolOp extends Expr {
  readonly kind = 'BoolOp' as const;
  constructor(
    readonly op: BoolOpName,
    readonly args: readonly Expr[],
  ) {
    super();
  }
  get className(): string {
    return this.op;
  }
  protected computeKey(): string {
    return `${this.op}(${this.args.map((a) => a.key).join(',')})`;
  }
  /** A node of the same class with new arguments (re-evaluated). */
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
  /** SymPy LatexPrinter: x \wedge y, x \vee y, x \veebar y, \neg x. */
  printLatex(p: (e: Expr) => string): string {
    const paren = (a: Expr) => (a instanceof BoolOp && a.op !== 'Not' ? `\\left(${p(a)}\\right)` : p(a));
    if (this.op === 'Not') {
      const a = at(this.args, 0);
      return a instanceof BoolOp ? `\\neg \\left(${p(a)}\\right)` : `\\neg ${p(a)}`;
    }
    if (this.op === 'ITE') return `\\left(${p(at(this.args, 1))} \\text{ if } ${p(at(this.args, 0))} \\text{ else } ${p(at(this.args, 2))}\\right)`;
    const sep = this.op === 'And' ? ' \\wedge ' : this.op === 'Or' ? ' \\vee ' : ' \\veebar ';
    return this.args.map(paren).join(sep);
  }
  /** SymPy StrPrinter: args sorted by default_sort_key, joined by & or |. */
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

/** SymPy ordered(): node count, then default_sort_key. */
const sortArgs = (xs: readonly Expr[]): Expr[] =>
  impl.ordered ? impl.ordered(xs) : [...xs].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
/** Rel.canonical puts a symbol-like side on the left; is the right side -oo? */
function canonicalRhsIsNegOo(r: Rel): boolean {
  if (isNegOo(r.rhs)) return true;
  if (isNegOo(r.lhs) && !isOo(r.rhs)) return true;
  return false;
}
/** A boolean argument: the integers 1 and 0 are true and false (SymPy's boolean context). */
const boolArg = (x0: ExprLike | boolean): Expr => {
  const x = typeof x0 === 'boolean' ? (x0 ? S.true : S.false) : impl.sympify(x0);
  if (x instanceof Rational && x.q === 1n && (x.p === 1n || x.p === 0n)) return x.p === 1n ? S.true : S.false;
  return x;
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

export const and = (...xs: (ExprLike | boolean)[]): Expr => lattice('And', xs);
export const or = (...xs: (ExprLike | boolean)[]): Expr => lattice('Or', xs);
export function not(x0: ExprLike | boolean): Expr {
  const x = boolArg(x0);
  if (isTrue(x)) return S.false;
  if (isFalse(x)) return S.true;
  if (x instanceof BoolOp && x.op === 'Not') return at(x.args, 0);
  if (x instanceof Rel) {
    const neg = { Eq: 'Ne', Ne: 'Eq', Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt' } as const;
    return new Rel(neg[x.op], x.lhs, x.rhs);
  }
  return new BoolOp('Not', [x]);
}

/** SymPy Xor(*args): true when an odd number of the arguments is true. */
export function xor(...xs: (ExprLike | boolean)[]): Expr {
  let parity = false;
  const counts = new Map<string, [Expr, number]>();
  for (const x0 of xs) {
    const x = boolArg(x0);
    if (isTrue(x)) parity = !parity;
    else if (!isFalse(x)) {
      const c = counts.get(x.key);
      counts.set(x.key, [x, (c?.[1] ?? 0) + 1]);
    }
  }
  // x ^ x = false
  const rest = [...counts.values()].filter(([, n]) => n % 2 === 1).map(([x]) => x);
  if (!rest.length) return parity ? S.true : S.false;
  const core = rest.length === 1 ? at(rest, 0) : new BoolOp('Xor', sortArgs(rest));
  return parity ? not(core) : core;
}
