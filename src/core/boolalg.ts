// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Boolean connectives And, Or and Not over relations (SymPy
 * logic.boolalg, the parts used by inequality solving).
 */

import { BoolAtom, Expr, ExprLike, Rel, S, Special, impl } from './nodes';
import { compareKeys, sortKey } from '../printing/sortkey';

export type BoolOpName = 'And' | 'Or' | 'Not';

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
  /** SymPy StrPrinter: args sorted by default_sort_key, joined by & or |. */
  printStr(p: (e: Expr) => string): string {
    if (this.op === 'Not') {
      const a = this.args[0]!;
      return a instanceof Rel || a instanceof BoolOp ? `~(${p(a)})` : `~${p(a)}`;
    }
    const sep = this.op === 'And' ? ' & ' : ' | ';
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
    const x = typeof x0 === 'boolean' ? (x0 ? S.true : S.false) : impl.sympify(x0);
    if (x.key === zero.key) return zero;
    if (x.key === identity.key) continue;
    visit(x);
  }
  if (out.size === 0) return identity;
  if (out.size === 1) return [...out.values()][0]!;
  return new BoolOp(op, sortArgs([...out.values()]));
}

export const and = (...xs: (ExprLike | boolean)[]): Expr => lattice('And', xs);
export const or = (...xs: (ExprLike | boolean)[]): Expr => lattice('Or', xs);
export function not(x0: ExprLike | boolean): Expr {
  const x = typeof x0 === 'boolean' ? (x0 ? S.true : S.false) : impl.sympify(x0);
  if (isTrue(x)) return S.false;
  if (isFalse(x)) return S.true;
  if (x instanceof BoolOp && x.op === 'Not') return x.args[0]!;
  if (x instanceof Rel) {
    const neg = { Eq: 'Ne', Ne: 'Eq', Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt' } as const;
    return new Rel(neg[x.op], x.lhs, x.rhs);
  }
  return new BoolOp('Not', [x]);
}
