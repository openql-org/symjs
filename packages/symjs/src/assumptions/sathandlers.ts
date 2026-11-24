// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Facts about the arguments of an expression (SymPy
 * sympy.assumptions.sathandlers): a fact in a symbol applied to all, any or
 * exactly one of the arguments, and the registry of the facts that satask
 * knows about each class of expression (Abs, Add, Mul, MatMul, Pow and the
 * numbers).
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Pow, Sym, isAddLike, isMulLike } from '../core/nodes';
import { sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { and, not, or } from '../core/boolalg';
import { isInstance, isFunctionOf } from '../core/match';
import { isNegative, isPositive, isZero } from '../core/assumptions';
import type { Predicate } from '../core/refine';
import { Q, ask } from '../core/refine';
import { at, cast } from '../core/guard';
import { Equivalent, Implies } from '../logic/boolalg';

const applied = (symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr[] => {
  const [s, f] = [sympify(symbol), sympify(fact)];
  return sympify(expr).args.map((a) => subs(f, [[s, a]]));
};

/**
 * The fact (in symbol) holds for all the arguments of expr.
 *
 * @param symbol - Placeholder replaced by each argument of the expression.
 * @param fact - Boolean relation between the predicates.
 * @param expr - Expression to evaluate.
 * @returns The fact (in symbol) holds for all the arguments of expr.
 * @see SymPy `sympy.assumptions.sathandlers.allargs`
 * @example
 * ```ts
 * import { Q, allargs, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * allargs(x, Q.positive(x), ex`x*y`); // => Q.positive(x) & Q.positive(y)
 * ```
 */
export function allargs(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  return and(...applied(symbol, fact, expr));
}

/**
 * The fact (in symbol) holds for some argument of expr.
 *
 * @param symbol - Placeholder replaced by each argument of the expression.
 * @param fact - Boolean relation between the predicates.
 * @param expr - Expression to evaluate.
 * @returns The fact (in symbol) holds for some argument of expr.
 * @see SymPy `sympy.assumptions.sathandlers.anyarg`
 * @example
 * ```ts
 * import { Q, anyarg, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * anyarg(x, Q.positive(x), ex`x*y`); // => Q.positive(x) | Q.positive(y)
 * ```
 */
export function anyarg(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  return or(...applied(symbol, fact, expr));
}

/**
 * The fact (in symbol) holds for exactly one argument of expr.
 *
 * @param symbol - Placeholder replaced by each argument of the expression.
 * @param fact - Boolean relation between the predicates.
 * @param expr - Expression to evaluate.
 * @returns The fact (in symbol) holds for exactly one argument of expr.
 * @see SymPy `sympy.assumptions.sathandlers.exactlyonearg`
 * @example
 * ```ts
 * import { Q, ex, exactlyonearg, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * exactlyonearg(x, Q.positive(x), ex`x*y`); // => (Q.positive(x) & ~Q.positive(y)) | (Q.positive(y) & ~Q.positive(x))
 * ```
 */
export function exactlyonearg(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  const ps = applied(symbol, fact, expr);
  return or(...ps.map((p, i) => and(p, ...ps.filter((_q, j) => j !== i).map((q) => not(q)))));
}

/**
 * A callback supplying a fact about an expression.
 *
 * @param expr - Expression to evaluate.
 * @returns A boolean expression known to hold for the input.
 */
export type FactHandler = (expr: Expr) => Expr;
/**
 * A callback supplying several facts about an expression.
 *
 * @param expr - Expression to evaluate.
 * @returns Boolean expressions known to hold for the input.
 */
export type MultiFactHandler = (expr: Expr) => readonly Expr[];

/**
 * Tests whether an expression belongs to the named expression class.
 *
 * @param expr - Expression to evaluate.
 * @param cls - Name of the expression class to match.
 * @returns True if the expression belongs to the specified class.
 */
export function isClassInstance(expr: Expr, cls: string): boolean {
  if (cls === 'Add') return isAddLike(expr);
  if (cls === 'Mul') return isMulLike(expr);
  if (expr instanceof ExtensionExpr) return expr.name === cls;
  return isInstance(expr, cls) || isFunctionOf(expr, cls);
}

/**
 * A registry of facts about expression classes. A handler contributes one or more facts about an instance of its class.
 *
 * @see SymPy `sympy.assumptions.sathandlers.ClassFactRegistry`
 * @example
 * ```ts
 * import { ClassFactRegistry, Q, ex } from '@symjs/symjs';
 *
 * const registry = new ClassFactRegistry();
 * registry.register('Abs', e => Q.nonnegative(e));
 * registry.call(ex`Abs(x)`); // => [Q.nonnegative(Abs(x))]
 * ```
 */
export class ClassFactRegistry {
  private readonly singlefacts = new Map<string, Set<FactHandler>>();
  private readonly multifacts = new Map<string, Set<MultiFactHandler>>();
  /**
   * Registers a handler giving one fact about the expressions of a class.
   *
   * @param cls - Name of the expression class to match.
   * @param handler - Callback that supplies the facts for a matching expression.
   * @returns The registered handler.
   * @see SymPy `sympy.assumptions.sathandlers.ClassFactRegistry.register`
   */
  register(cls: string, handler: FactHandler): FactHandler {
    this.singlefacts.set(cls, new Set([...(this.singlefacts.get(cls) ?? []), handler]));
    return handler;
  }
  /**
   * Registers a handler giving several facts about the expressions of each class.
   *
   * @param classes - Expression class names to which the handler applies.
   * @param handler - Callback that supplies the facts for a matching expression.
   * @returns The registered handler.
   * @see SymPy `sympy.assumptions.sathandlers.ClassFactRegistry.multiregister`
   */
  multiregister(classes: string | readonly string[], handler: MultiFactHandler): MultiFactHandler {
    for (const cls of typeof classes === 'string' ? [classes] : classes) {
      this.multifacts.set(cls, new Set([...(this.multifacts.get(cls) ?? []), handler]));
    }
    return handler;
  }
  /**
   * The single-fact and multiple-fact handlers that apply to expr (SymPy registry[type(expr)]).
   *
   * @param expr - Expression to evaluate.
   * @returns The single-fact and multiple-fact handlers that apply to expr.
   */
  handlers(expr: Expr): [FactHandler[], MultiFactHandler[]] {
    const pick = <H>(m: ReadonlyMap<string, ReadonlySet<H>>): H[] => [
      ...new Set([...m].filter(([cls]) => isClassInstance(expr, cls)).flatMap(([, hs]) => [...hs])),
    ];
    return [pick(this.singlefacts), pick(this.multifacts)];
  }
  /**
   * Collects all registered facts about the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The distinct facts supplied by matching handlers.
   * @see SymPy `sympy.assumptions.sathandlers.ClassFactRegistry.__call__`
   */
  call(expr: ExprLike): Expr[] {
    const e = sympify(expr);
    const [single, multi] = this.handlers(e);
    const facts = [...single.map((h) => h(e)), ...multi.flatMap((h) => h(e))];
    return [...new Map(facts.map((f) => [f.key, f] as const)).values()];
  }
}

/**
 * The facts satask uses about Abs, Add, Mul, MatMul, Pow and the numbers.
 *
 * @see SymPy `sympy.assumptions.sathandlers.class_fact_registry`
 * @example
 * ```ts
 * import { Q, classFactRegistry, ex } from '@symjs/symjs';
 *
 * const facts = classFactRegistry.call(ex`Abs(x)`);
 * facts.some(fact => fact.equals(Q.nonnegative(ex`Abs(x)`))); // => True
 * ```
 */
export const classFactRegistry: ClassFactRegistry = new ClassFactRegistry();

const x = new Sym('x');

classFactRegistry.multiregister('Abs', (expr) => {
  const arg = at(expr.args, 0);
  return [
    Q.nonnegative(expr),
    Equivalent(not(Q.zero(arg)), not(Q.zero(expr))),
    Implies(Q.even(arg), Q.even(expr)),
    Implies(Q.odd(arg), Q.odd(expr)),
    Implies(Q.integer(arg), Q.integer(expr)),
  ];
});

classFactRegistry.multiregister('Add', (expr) => [
  Implies(allargs(x, Q.positive(x), expr), Q.positive(expr)),
  Implies(allargs(x, Q.negative(x), expr), Q.negative(expr)),
  Implies(allargs(x, Q.real(x), expr), Q.real(expr)),
  Implies(allargs(x, Q.rational(x), expr), Q.rational(expr)),
  Implies(allargs(x, Q.integer(x), expr), Q.integer(expr)),
  Implies(exactlyonearg(x, not(Q.integer(x)), expr), not(Q.integer(expr))),
]);

classFactRegistry.register('Add', (expr) =>
  Implies(allargs(x, Q.real(x), expr), Implies(exactlyonearg(x, Q.irrational(x), expr), Q.irrational(expr))),
);

classFactRegistry.multiregister('Mul', (expr) => [
  Equivalent(Q.zero(expr), anyarg(x, Q.zero(x), expr)),
  Implies(allargs(x, Q.positive(x), expr), Q.positive(expr)),
  Implies(allargs(x, Q.real(x), expr), Q.real(expr)),
  Implies(allargs(x, Q.rational(x), expr), Q.rational(expr)),
  Implies(allargs(x, Q.integer(x), expr), Q.integer(expr)),
  Implies(exactlyonearg(x, not(Q.rational(x)), expr), not(Q.integer(expr))),
  Implies(allargs(x, Q.commutative(x), expr), Q.commutative(expr)),
]);

// Would be allargs(x, Q.prime(x) | Q.composite(x)) except 1 is composite (assumes Mul has more than one arg)
classFactRegistry.register('Mul', (expr) => Implies(allargs(x, Q.prime(x), expr), not(Q.prime(expr))));

// General case: an odd number of imaginary args implies the product is imaginary (to be implemented)
classFactRegistry.register('Mul', (expr) =>
  Implies(allargs(x, or(Q.imaginary(x), Q.real(x)), expr), Implies(exactlyonearg(x, Q.imaginary(x), expr), Q.imaginary(expr))),
);

classFactRegistry.register('Mul', (expr) =>
  Implies(allargs(x, Q.real(x), expr), Implies(exactlyonearg(x, Q.irrational(x), expr), Q.irrational(expr))),
);

// With the integer qualification no facts are needed for odd: every integer is exactly one of even or odd
classFactRegistry.register('Mul', (expr) => Implies(allargs(x, Q.integer(x), expr), Equivalent(anyarg(x, Q.even(x), expr), Q.even(expr))));

classFactRegistry.register('MatMul', (expr) =>
  Implies(allargs(x, Q.square(x), expr), Equivalent(Q.invertible(expr), allargs(x, Q.invertible(x), expr))),
);

classFactRegistry.multiregister('Pow', (expr) => {
  const { base, exp } = cast(expr, Pow);
  return [
    Implies(and(Q.real(base), Q.even(exp), Q.nonnegative(exp)), Q.nonnegative(expr)),
    Implies(and(Q.nonnegative(base), Q.odd(exp), Q.nonnegative(exp)), Q.nonnegative(expr)),
    Implies(and(Q.nonpositive(base), Q.odd(exp), Q.nonnegative(exp)), Q.nonpositive(expr)),
    Equivalent(Q.zero(expr), and(Q.zero(base), Q.positive(exp))),
  ];
});

/** The old assumptions of a number: is_positive, is_zero, ... (true, false or undefined). */
const OLD_ASSUMP_GETTERS: readonly (readonly [Predicate, (o: Expr) => boolean | undefined])[] = [
  [Q.positive, isPositive],
  [Q.zero, isZero],
  [Q.negative, isNegative],
  ...(['rational', 'irrational', 'even', 'odd', 'imaginary', 'prime', 'composite'] as const).map(
    (n) => [Q[n], (o: Expr): boolean | undefined => {
      const t = ask(Q[n](o));
      return t === 'unknown' ? undefined : t;
    }] as const,
  ),
];

classFactRegistry.multiregister(['Number', 'NumberSymbol', 'ImaginaryUnit'], (expr) => {
  const ret: Expr[] = [];
  for (const [p, getter] of OLD_ASSUMP_GETTERS) {
    const prop = getter(expr);
    if (prop !== undefined) ret.push(Equivalent(p(expr), prop));
  }
  return ret;
});
