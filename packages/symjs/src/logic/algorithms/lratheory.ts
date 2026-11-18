// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Exact feasibility for conjunctions of linear rational inequalities. */
import { Add, Mul, Rational, Sym, type Expr } from '../../core/nodes';
import { getOrThrow } from '../../core/guard';
import { NotImplementedError } from '../../core/errors';

/** Valid input outside linear real arithmetic. */
export class UnhandledInput extends NotImplementedError {
  constructor(message: string) {
    super(message);
    this.name = 'UnhandledInput';
  }
}

/** A linear form, including the constant at the empty key. */
export type LinearForm = Map<string, Rational>;
/** A linear form constrained to be nonpositive, or negative when strict. */
export interface LinearConstraint { readonly form: LinearForm; readonly strict: boolean }

const sum = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
const product = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.p, a.q * b.q);
const zero = Rational.of(0);

/** Add scaled linear forms without discarding rational precision. */
export function combineLinear(a: LinearForm, b: LinearForm, scale: Rational): LinearForm {
  const out = new Map(a);
  for (const [key, value] of b) {
    const c = sum(out.get(key) ?? zero, product(value, scale));
    if (c.p === 0n) out.delete(key);
    else out.set(key, c);
  }
  return out;
}

/** Parse a linear rational expression; nonlinear terms are rejected. */
export function linearForm(expr: Expr): LinearForm {
  if (expr instanceof Rational) return new Map([['', expr]]);
  if (expr instanceof Sym) return new Map([[expr.key, Rational.of(1)]]);
  if (expr instanceof Add) return expr.args.reduce((a, b) => combineLinear(a, linearForm(b), Rational.of(1)), new Map<string, Rational>());
  if (expr instanceof Mul) {
    let coefficient = Rational.of(1);
    let variable: LinearForm | undefined;
    for (const arg of expr.args) {
      if (arg instanceof Rational) coefficient = product(coefficient, arg);
      else if (variable === undefined) variable = linearForm(arg);
      else throw new UnhandledInput('Nonlinear expression');
    }
    return combineLinear(new Map(), variable ?? new Map([['', Rational.of(1)]]), coefficient);
  }
  throw new UnhandledInput('Unsupported linear expression');
}

/** Fourier–Motzkin elimination, preserving strict endpoints. */
export function linearFeasible(constraints: readonly LinearConstraint[]): boolean {
  let rows = [...constraints];
  const variables = new Set(rows.flatMap((r) => [...r.form.keys()].filter((k) => k !== '')));
  for (const key of variables) {
    const positive = rows.filter((r) => (r.form.get(key)?.p ?? 0n) > 0n);
    const negative = rows.filter((r) => (r.form.get(key)?.p ?? 0n) < 0n);
    const next = rows.filter((r) => !r.form.has(key));
    for (const p of positive) for (const n of negative) {
      const pc = getOrThrow(p.form, key), nc = getOrThrow(n.form, key);
      const factor = Rational.of(-nc.p * pc.q, nc.q * pc.p);
      const form = combineLinear(n.form, p.form, factor);
      next.push({ form, strict: p.strict || n.strict });
    }
    rows = next;
  }
  return rows.every(({ form, strict }) => {
    const c = form.get('') ?? zero;
    return strict ? c.p < 0n : c.p <= 0n;
  });
}
