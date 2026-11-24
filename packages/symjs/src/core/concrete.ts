// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The unevaluated Sum / Product node.
 */

import type { ExprLike } from './nodes';
import { Derivative, Dummy, Expr, ExtensionExpr, Mul, Rel, Sym, UndefFn, impl, registerHeadResolver } from './nodes';
import { add, mul, pow, sub, sympify } from './ops';
import { at, getOrThrow } from './guard';
import { ReorderError } from './errors';
import type { Truth } from './truth';
import { isZero, isNegative, isPositive } from './assumptions';

/**
 * Sum or Product: args [f, k1, a1, b1, k2, a2, b2, ...]. @internal ctor
 *
 * @experimental May change in a minor release.
 */
export class Concrete extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Concrete' as const;
  /**
   * Creates a `Concrete`.
   *
   * @param kind2 - Whether the operation is a sum or a product.
   * @param args - The summand or factor followed by index and endpoint triples.
   */
  constructor(
    /** Whether the operation is a sum or a product. */
    readonly kind2: 'Sum' | 'Product',
    /** The node's arguments in canonical order. */
    readonly args: readonly Expr[]) {
    super();
  }
  /**
   * Identifies the expression evaluated at each index.
   *
   * @returns The summand or factor.
   */
  get function(): Expr {
    return at(this.args, 0);
  }
  /**
   * Indicates whether the expression represents a number.
   *
   * @returns The numeric flag.
   */
  override get isNumber(): boolean {
    return this.freeSymbols().size === 0;
  }
  /**
   * ExprWithLimits.free_symbols: each outer variable binds the preceding limits too.
   *
   * @returns The free symbols in the expression.
   */
  override freeSymbols(): Set<Expr> {
    const replacements = new Map<string, readonly [Expr, Expr]>();
    for (const [k] of this.limits) {
      const syms = impl.freeSymbols(k);
      replacements.set(k.key, [k, syms.size === 1 && [...syms].some((s) => s.key === k.key) ? k : new Dummy()]);
    }
    const f = impl.xreplace(this.function, [...replacements.values()]);
    const free = new Map([...impl.freeSymbols(f)].map((s) => [s.key, s]));
    for (const [k, a, b] of this.limits) {
      free.delete(getOrThrow(replacements, k.key)[1].key);
      for (const s of [...impl.freeSymbols(a), ...impl.freeSymbols(b)]) free.set(s.key, s);
    }
    return new Set(free.values());
  }
  /**
   * Lists the iterated bounds from the innermost limit outward.
   *
   * @returns Index and endpoint triples.
   */
  get limits(): [Expr, Expr, Expr][] {
    const out: [Expr, Expr, Expr][] = [];
    for (let i = 1; i < this.args.length; i += 3) out.push([at(this.args, i), at(this.args, i + 1), at(this.args, i + 2)]);
    return out;
  }
  protected computeKey(): string {
    return `${this.kind2}(${this.args.map((a) => a.key).join(',')})`;
  }
  /** A node of the same kind with new limits. */
  private withLimits(f: Expr, limits: readonly (readonly [Expr, Expr, Expr])[]): Concrete {
    return new Concrete(this.kind2, [f, ...limits.flat()]);
  }
  /**
   * Locates the unique limit bound to the given variable.
   *
   * @param x - The argument of the function.
   * @returns The limit index.
   * @throws RangeError when the variable does not occur in exactly one limit.
   * @see SymPy `sympy.concrete.expr_with_intlimits.ExprWithIntLimits.index`
   */
  index(x: ExprLike): number {
    const v = sympify(x);
    const vars = this.limits.map((l) => l[0].key);
    if (vars.filter((k) => k === v.key).length !== 1) throw new RangeError('Number of instances of variable not equal to one');
    return vars.indexOf(v.key);
  }
  /**
   * Swaps two limits whose bounds are independent of all index variables. Dependent bounds raise
   * `ReorderError`.
   *
   * @param x - A zero-based limit position to interchange.
   * @param y - A zero-based limit position to interchange.
   * @returns The reordered sum or product.
   * @throws ReorderError when the dependence of the limits prevents their interchange.
   * @see SymPy `sympy.concrete.expr_with_intlimits.ExprWithIntLimits.reorder_limit`
   */
  reorderLimit(x: number, y: number): Concrete {
    const vars = new Set(this.limits.map((l) => l[0].key));
    const limits = this.limits;
    const [lx, ly] = [at(limits, x), at(limits, y)];
    const independent = [lx[1], lx[2], ly[1], ly[2]].every((b) => ![...impl.freeSymbols(b)].some((s) => vars.has(s.key)));
    if (!independent) throw new ReorderError(impl.str(this), 'could not interchange the two limits specified');
    return this.withLimits(
      this.function,
      limits.map((l, i) => (i === x ? ly : i === y ? lx : l)),
    );
  }
  /**
   * Interchanges successive pairs of limits identified by position or variable.
   *
   * @param pairs - The pairs of limit positions or variables to interchange.
   * @returns The reordered sum or product.
   * @throws RangeError when a pair does not identify two limits.
   * @throws ReorderError when the limits cannot be interchanged.
   * @see SymPy `sympy.concrete.expr_with_intlimits.ExprWithIntLimits.reorder`
   */
  reorder(...pairs: readonly (readonly (number | ExprLike)[])[]): Concrete {
    let e: Concrete = this;
    for (const r of pairs) {
      if (r.length !== 2) throw new RangeError('Invalid number of arguments');
      const idx = r.map((v) => (typeof v === 'number' ? v : e.index(v)));
      e = e.reorderLimit(at(idx, 0), at(idx, 1));
    }
    return e;
  }
  /**
   * Changes the bound index by a linear transformation with coefficient 1, −1, or symbolic slope and
   * optionally renames the new variable.
   *
   * @param varIn - The index being changed.
   * @param trafoIn - The affine transformation of the index.
   * @param newvarIn - The replacement index symbol.
   * @returns The transformed sum or product.
   * @throws RangeError when the change of variable does not yield a supported linear index.
   * @see SymPy `sympy.concrete.expr_with_intlimits.ExprWithIntLimits.change_index`
   */
  changeIndex(varIn: ExprLike, trafoIn: ExprLike, newvarIn?: ExprLike): Concrete {
    const v = sympify(varIn);
    const trafo = sympify(trafoIn);
    const newvar = newvarIn === undefined ? v : sympify(newvarIn);
    const alpha = impl.expand(impl.diff(trafo, v, 1));
    const beta = impl.expand(sub(trafo, mul(alpha, v)));
    const linear = alpha.key !== '0' && ![...impl.freeSymbols(alpha), ...impl.freeSymbols(beta)].some((s) => s.key === v.key);
    if (!linear) throw new RangeError('Index transformation is not linear');
    const limits = this.limits.map(([k, a, b]): [Expr, Expr, Expr] => {
      if (k.key !== v.key) return [k, a, b];
      if (alpha.isNumber && alpha.key !== '1' && alpha.key !== '-1') throw new RangeError('Linear transformation results in non-linear summation stepsize');
      const lo = add(mul(alpha, a), beta);
      const hi = add(mul(alpha, b), beta);
      return alpha.key === '1' ? [newvar, lo, hi] : [newvar, hi, lo];
    });
    const f = impl.subs(impl.subs(this.function, [[v, mul(sub(v, beta), pow(alpha, -1))]]), [[v, newvar]]);
    return this.withLimits(f, limits);
  }
  /**
   * Tests whether any limit has an empty range with its lower endpoint one greater than its upper
   * endpoint.
   *
   * @returns The truth value, or `'unknown'` when it cannot be determined.
   */
  get hasEmptySequence(): Truth {
    let unknown = false;
    for (const [, a, b] of this.limits) {
      if (a.key === b.key) continue;
      const d = sub(sub(a, b), 1);
      const zero = isZero(d);
      if (zero === undefined) unknown = true;
      else if (zero) return true;
    }
    return unknown ? 'unknown' : false;
  }
}

/** SymPy AddWithLimits._eval_factor, applied from the innermost sum out. @internal */
export function factorConcreteSum(sum: Concrete, factor: (term: Expr) => Expr): Expr {
  const limits = sum.limits;
  const [k, a, b] = at(limits, limits.length - 1);
  const nested = limits.length > 1;
  const term = factor(nested ? new Concrete('Sum', sum.args.slice(0, -3)) : sum.function);
  if (nested && !term.has(k)) return mul(term, add(sub(b, a), 1));
  if (!(term instanceof Mul)) return sum;
  const outside: Expr[] = [], inside: Expr[] = [];
  for (const t of term.args) {
    const independent = t.isCommutative && ![...impl.freeSymbols(t)].some(s => s.equals(k));
    (independent ? outside : inside).push(t);
  }
  return mul(...outside, new Concrete('Sum', [mul(...inside), k, a, b]));
}

type ConcreteLimit = readonly [Expr, ExprLike, ExprLike] | readonly [Expr, Expr];

/** Set-valued limit processing supplied by concrete/exprwithlimits. @internal */
export const concreteHooks: { processLimit?: (f: Expr, k: Expr, domain: Expr) => readonly [Expr, Expr, Expr] } = {};

function withProcessedLimits(kind: 'Sum' | 'Product', fIn: ExprLike, limits: readonly ConcreteLimit[]): Expr {
  if (limits.length === 0) throw new RangeError(`${kind} requires a definite limit`);
  let f = sympify(fIn);
  if (f instanceof Rel && f.op === 'Eq') return impl.rebuild(f, [withProcessedLimits(kind, f.lhs, limits), withProcessedLimits(kind, f.rhs, limits)]);
  const args: Expr[] = [];
  for (const limit of limits) {
    const k = limit[0];
    if (!(k instanceof Sym || k instanceof UndefFn || k instanceof Derivative || (k instanceof ExtensionExpr && k.name === 'Indexed'))) throw new RangeError('Invalid limit variable');
    if (limit.length === 2) {
      if (concreteHooks.processLimit === undefined) throw new TypeError('Set limits require the calculus module');
      const [term, lower, upper] = concreteHooks.processLimit(f, k, limit[1]);
      f = term;
      args.push(k, lower, upper);
    } else {
      const lower = sympify(limit[1]), upper = sympify(limit[2]);
      if ('lower' in k && k.lower instanceof Expr && isNegative(sub(lower, k.lower)) === true) throw new RangeError('Lower limit is outside the index range');
      if ('upper' in k && k.upper instanceof Expr && isPositive(sub(upper, k.upper)) === true) throw new RangeError('Upper limit is outside the index range');
      args.push(k, lower, upper);
    }
  }
  return new Concrete(kind, [f, ...args]);
}

/**
 * Constructs an unevaluated sum over inclusive limits, processing the innermost limit first. Evaluate
 * it with `doit` or {@link summation}.
 *
 * @param f - The summand.
 * @param limits - The indices with their bounds.
 * @returns The sum.
 * @see SymPy `sympy.concrete.summations.Sum`
 * @example
 * ```ts
 * import { doit, ex, oo, Sum, symbols } from '@symjs/symjs';
 *
 * const [k, m] = symbols('k m');
 * Sum(k, [k, 1, m]); // => Sum(k, (k, 1, m))
 * doit(Sum(k, [k, 1, m])); // => m**2/2 + m/2
 * doit(Sum(k.pow(2), [k, 1, m])); // => m**3/3 + m**2/2 + m/6
 * doit(Sum(ex`x**k`, [k, 0, oo])); // => Piecewise((1/(1 - x), Abs(x) < 1), (Sum(x**k, (k, 0, oo)), True))
 * doit(Sum(ex`x**k/factorial(k)`, [k, 0, oo])); // => exp(x)
 * ```
 */
export function Sum(f: ExprLike, ...limits: ConcreteLimit[]): Expr {
  return withProcessedLimits('Sum', f, limits);
}

/**
 * Constructs an unevaluated product over inclusive limits, processing the innermost limit first.
 * Evaluate it with `doit` or {@link product}.
 *
 * @param f - The factor.
 * @param limits - The indices with their bounds.
 * @returns The product.
 * @see SymPy `sympy.concrete.products.Product`
 * @example
 * ```ts
 * import { doit, Product, symbols } from '@symjs/symjs';
 *
 * const [k, m] = symbols('k m');
 * Product(k, [k, 1, m]); // => Product(k, (k, 1, m))
 * doit(Product(k, [k, 1, m])); // => factorial(m)
 * doit(Product(k.pow(2), [k, 1, m])); // => factorial(m)**2
 * ```
 */
export function Product(f: ExprLike, ...limits: ConcreteLimit[]): Expr {
  return withProcessedLimits('Product', f, limits);
}

// func(Sum(...)) is Sum; the arguments of the node are flat (f, k, a, b, ...), so rebuild(e, args)
// rebuilds it rather than func(e)(...e.args)
registerHeadResolver(Concrete, (e) => (e.kind2 === 'Product' ? Product : Sum));
