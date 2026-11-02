// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's assumption predicates Q, ask and refine. A predicate about
 * a symbol is applied by rebuilding the expression with a symbol carrying
 * that assumption, so every simplification that uses assumptions applies.
 */

import { Assumptions, Expr, ExprLike, Sym } from './nodes';
import { sympify } from './ops';
import { xreplace } from './traverse';
import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from './assumptions';
import { str } from '../printing/str';

/** Predicate names of Q (SymPy Q.<name>). */
export type PredicateName =
  | 'real'
  | 'extended_real'
  | 'positive'
  | 'negative'
  | 'nonnegative'
  | 'nonpositive'
  | 'zero'
  | 'nonzero'
  | 'integer'
  | 'rational'
  | 'even'
  | 'odd'
  | 'prime'
  | 'composite'
  | 'complex'
  | 'imaginary'
  | 'finite'
  | 'commutative';

/** An assumption such as Q.positive(x) (SymPy AppliedPredicate), or a conjunction of them. */
export class AppliedPredicate {
  constructor(
    readonly name: PredicateName,
    readonly arg: Expr,
  ) {}
  /** Conjunction (SymPy &). */
  and(...others: Assumption[]): AppliedPredicate[] {
    return [this, ...others.flatMap((o): AppliedPredicate[] => (Array.isArray(o) ? [...(o as readonly AppliedPredicate[])] : [o as AppliedPredicate]))];
  }
  toString(): string {
    return `Q.${this.name}(${str(this.arg)})`;
  }
}

/** One predicate or a conjunction (array) of predicates. */
export type Assumption = AppliedPredicate | readonly AppliedPredicate[];

const pred = (name: PredicateName) => (x: ExprLike) => new AppliedPredicate(name, sympify(x));

/** SymPy Q: the assumption predicates. */
export const Q = {
  real: pred('real'),
  extended_real: pred('extended_real'),
  positive: pred('positive'),
  negative: pred('negative'),
  nonnegative: pred('nonnegative'),
  nonpositive: pred('nonpositive'),
  zero: pred('zero'),
  nonzero: pred('nonzero'),
  integer: pred('integer'),
  rational: pred('rational'),
  even: pred('even'),
  odd: pred('odd'),
  prime: pred('prime'),
  composite: pred('composite'),
  complex: pred('complex'),
  imaginary: pred('imaginary'),
  finite: pred('finite'),
  commutative: pred('commutative'),
} as const;

/** The symbol assumptions implied by a predicate (those the base module tracks). */
function implied(name: PredicateName): Assumptions {
  switch (name) {
    case 'real':
    case 'extended_real':
    case 'rational':
      return { real: true };
    case 'positive':
      return { positive: true, real: true };
    case 'negative':
      return { negative: true, real: true };
    case 'nonnegative':
      return { nonnegative: true, real: true };
    case 'nonpositive':
      return { nonpositive: true, real: true };
    case 'zero':
      return { zero: true, real: true, integer: true, nonnegative: true, nonpositive: true };
    case 'nonzero':
      return { zero: false };
    case 'integer':
    case 'even':
    case 'odd':
    case 'composite':
      return { integer: true, real: true };
    case 'prime':
      return { integer: true, positive: true, real: true };
    case 'commutative':
      return { commutative: true };
    default:
      return {};
  }
}

const flatten = (a: Assumption | boolean | undefined): AppliedPredicate[] => (a === undefined || typeof a === 'boolean' ? [] : Array.isArray(a) ? [...a] : [a as AppliedPredicate]);

/** Symbols with the assumptions added, and the substitutions back. */
function assume(assumptions: Assumption | boolean | undefined): [Map<string, Sym>, [Expr, Expr][]] {
  const added = new Map<string, { sym: Sym; extra: Assumptions }>();
  for (const p of flatten(assumptions)) {
    if (!(p.arg instanceof Sym)) continue;
    const cur = added.get(p.arg.key) ?? { sym: p.arg, extra: {} };
    cur.extra = { ...cur.extra, ...implied(p.name) };
    added.set(p.arg.key, cur);
  }
  const forward = new Map<string, Sym>();
  const back: [Expr, Expr][] = [];
  for (const [k, { sym, extra }] of added) {
    const s = new Sym(sym.name, { ...sym.assumptions, ...extra });
    forward.set(k, s);
    back.push([s, sym]);
  }
  return [forward, back];
}

/** Rebuild every node so that the assumptions take effect. */
function reevaluate(e: Expr, forward: Map<string, Sym>): Expr {
  return xreplace(
    e,
    [...forward].map(([k, s]) => [findByKey(e, k)!, s] as const).filter(([a]) => a !== undefined),
  );
}

function findByKey(e: Expr, key: string): Expr | undefined {
  if (e.key === key) return e;
  for (const a of e.args) {
    const r = findByKey(a, key);
    if (r) return r;
  }
  return undefined;
}

/**
 * SymPy refine(expr, assumptions): expr simplified under the assumptions,
 * e.g. refine(sqrt(x**2), Q.real(x)) = Abs(x),
 * refine(Abs(x), Q.positive(x)) = x.
 */
export function refine(expr: ExprLike, assumptions?: Assumption | boolean): Expr;
/** A matrix (any object with map) refined entry by entry (SymPy Matrix.refine). */
export function refine<M extends { map(f: (e: Expr) => ExprLike): M }>(expr: M, assumptions?: Assumption | boolean): M;
export function refine(expr: unknown, assumptions: Assumption | boolean = true): unknown {
  if (!(expr instanceof Expr) && typeof expr === 'object' && expr !== null && typeof (expr as { map?: unknown }).map === 'function') {
    return (expr as { map(f: (e: Expr) => ExprLike): unknown }).map((x) => refine(x, assumptions));
  }
  const e = sympify(expr as ExprLike);
  const [forward, back] = assume(assumptions);
  if (!forward.size) return e;
  return xreplace(reevaluate(e, forward), back);
}

/**
 * SymPy ask(proposition, assumptions): true, false, or undefined when it
 * cannot be decided.
 */
export function ask(proposition: AppliedPredicate, assumptions: Assumption | boolean = true): boolean | undefined {
  const [forward] = assume(assumptions);
  const x = forward.size ? reevaluate(proposition.arg, forward) : proposition.arg;
  const tri = (v: boolean | undefined | null): boolean | undefined => (v === null ? undefined : v);
  switch (proposition.name) {
    case 'real':
    case 'extended_real':
      return tri(isReal(x));
    case 'positive':
      return tri(isPositive(x));
    case 'negative':
      return tri(isNegative(x));
    case 'nonnegative':
      return tri(isNonNegative(x));
    case 'nonpositive': {
      const p = tri(isPositive(x));
      return p === undefined ? undefined : !p && tri(isReal(x)) === true ? true : p ? false : undefined;
    }
    case 'zero':
      return tri(isZero(x));
    case 'nonzero':
      return tri(isNonZero(x));
    case 'integer':
      return tri(isIntegerQ(x));
    case 'commutative':
      return x.isCommutative;
    default:
      return undefined;
  }
}
