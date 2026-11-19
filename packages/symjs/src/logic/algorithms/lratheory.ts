// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Exact feasibility for conjunctions of linear rational inequalities. */
import { Add, BoolAtom, Mul, Rational, Rel, S, Sym, type Expr } from '../../core/nodes';
import { BoolOp } from '../../core/boolalg';
import { AppliedPredicate } from '../../core/refine';
import { at, getOrThrow } from '../../core/guard';
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

const relationNames = { Eq: 'eq', Ne: 'ne', Lt: 'lt', Le: 'le', Gt: 'gt', Ge: 'ge' } as const;
const complement: Record<string, string> = { eq: 'ne', ne: 'eq', lt: 'ge', le: 'gt', gt: 'le', ge: 'lt' };
const signRelations: Record<string, string> = { positive: 'gt', negative: 'lt', nonpositive: 'le', nonnegative: 'ge', zero: 'eq', nonzero: 'ne', extended_positive: 'gt', extended_negative: 'lt', extended_nonpositive: 'le', extended_nonnegative: 'ge', extended_nonzero: 'ne' };

/** Translate the Boolean skeleton to conjunctions of theory constraints. */
function theoryBranches(e: Expr, negate = false): LinearConstraint[][] {
  if (e instanceof BoolAtom) return e.value !== negate ? [[]] : [];
  if (e instanceof BoolOp) {
    if (e.op === 'Not') return theoryBranches(at(e.args, 0), !negate);
    if (e.op !== 'And' && e.op !== 'Or') throw new UnhandledInput('Unsupported Boolean connective');
    const parts = e.args.map((arg) => theoryBranches(arg, negate));
    if ((e.op === 'And') === negate) return parts.flat();
    return parts.reduce<LinearConstraint[][]>((a, b) => a.flatMap((x) => b.map((y) => [...x, ...y])), [[]]);
  }
  let name: string, lhs: Expr, rhs: Expr;
  if (e instanceof Rel) {
    name = relationNames[e.op]; lhs = e.lhs; rhs = e.rhs;
  } else if (e instanceof AppliedPredicate) {
    name = e.predicate; lhs = e.arg; rhs = e.args[1] ?? S.Zero;
    if (['positive_infinite', 'negative_infinite', 'real', 'extended_real', 'finite'].includes(name)) linearForm(lhs);
    if (['positive_infinite', 'negative_infinite'].includes(name)) return negate ? [[]] : [];
    if (['real', 'extended_real', 'finite'].includes(name)) return negate ? [] : [[]];
    name = signRelations[name] ?? name;
  } else throw new UnhandledInput('Unsupported proposition');
  if (negate) name = complement[name] ?? '';
  if (!['eq', 'ne', 'lt', 'le', 'gt', 'ge'].includes(name)) throw new UnhandledInput('Unsupported predicate');
  const form = combineLinear(linearForm(lhs), linearForm(rhs), Rational.of(-1));
  const opposite = combineLinear(new Map(), form, Rational.of(-1));
  if (name === 'eq') return [[{ form, strict: false }, { form: opposite, strict: false }]];
  if (name === 'ne') return [[{ form, strict: true }], [{ form: opposite, strict: true }]];
  return [[{ form: name === 'gt' || name === 'ge' ? opposite : form, strict: name === 'gt' || name === 'lt' }]];
}

/** Check a Boolean combination of linear constraints over real variables. */
export const linearSatisfiable = (e: Expr): boolean => theoryBranches(e).some(linearFeasible);
