// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The unevaluated Sum / Product node.
 */

import type { ExprLike } from './nodes';
import { Derivative, Dummy, Expr, ExtensionExpr, Sym, UndefFn, impl, registerHeadResolver } from './nodes';
import { add, mul, pow, sub, sympify } from './ops';
import { at, getOrThrow } from './guard';
import { ReorderError } from './errors';
import type { Truth } from './truth';
import { isZero } from './assumptions';

/**
 * Sum or Product: args [f, k1, a1, b1, k2, a2, b2, ...]. @internal ctor
 *
 * @experimental May change in a minor release.
 */
export class Concrete extends Expr {
  readonly kind = 'Concrete' as const;
  constructor(readonly kind2: 'Sum' | 'Product', readonly args: readonly Expr[]) {
    super();
  }
  get function(): Expr {
    return at(this.args, 0);
  }
  override get isNumber(): boolean {
    return this.freeSymbols().size === 0;
  }
  /** ExprWithLimits.free_symbols: each outer variable binds the preceding limits too. */
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
  /** SymPy ExprWithIntLimits.index: the position of the limit of variable x (which must occur once). */
  index(x: ExprLike): number {
    const v = sympify(x);
    const vars = this.limits.map((l) => l[0].key);
    if (vars.filter((k) => k === v.key).length !== 1) throw new RangeError('Number of instances of variable not equal to one');
    return vars.indexOf(v.key);
  }
  /**
   * SymPy ExprWithIntLimits.reorder_limit: the limits at positions x and y
   * interchanged, when neither depends on a summation variable (else a ReorderError).
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
   * SymPy ExprWithIntLimits.reorder: the limits interchanged pair by pair; a
   * pair names the limits by position or by variable.
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
   * SymPy ExprWithIntLimits.change_index: the variable var replaced by the
   * linear transformation trafo = alpha*var + beta (alpha = 1 or -1, or a
   * symbol), renamed newvar.
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
   * SymPy ExprWithIntLimits.has_empty_sequence: some limit (k, a, b) has
   * a - b = 1 (an empty range); 'unknown' when undecided.
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

type ConcreteLimit = readonly [Expr, ExprLike, ExprLike] | readonly [Expr, Expr];

/** Set-valued limit processing supplied by concrete/exprwithlimits. @internal */
export const concreteHooks: { processLimit?: (f: Expr, k: Expr, domain: Expr) => readonly [Expr, Expr, Expr] } = {};

function withProcessedLimits(kind: 'Sum' | 'Product', fIn: ExprLike, limits: readonly ConcreteLimit[]): Expr {
  if (limits.length === 0) throw new RangeError(`${kind} requires a definite limit`);
  let f = sympify(fIn);
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
      args.push(k, sympify(limit[1]), sympify(limit[2]));
    }
  }
  return new Concrete(kind, [f, ...args]);
}

/** Unevaluated Sum(f, (k, a, b), ...) or Sum(f, (k, Range)). */
export function Sum(f: ExprLike, ...limits: ConcreteLimit[]): Expr {
  return withProcessedLimits('Sum', f, limits);
}

/** Unevaluated Product(f, (k, a, b), ...) or Product(f, (k, Range)). */
export function Product(f: ExprLike, ...limits: ConcreteLimit[]): Expr {
  return withProcessedLimits('Product', f, limits);
}

// func(Sum(...)) is Sum; the arguments of the node are flat (f, k, a, b, ...), so rebuild(e, args)
// rebuilds it rather than func(e)(...e.args)
registerHeadResolver(Concrete, (e) => (e.kind2 === 'Product' ? Product : Sum));
