// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The unevaluated Sum / Product node.
 */

import type { ExprLike, Sym } from './nodes';
import { Expr, Rational, impl } from './nodes';
import { add, mul, pow, sub, sympify } from './ops';
import { at } from './guard';
import { ReorderError } from './errors';
import type { Truth } from './truth';

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
      // Eq(a - b, 1) decides only when a - b - 1 is a number
      const d = sub(sub(a, b), 1);
      if (!(d instanceof Rational)) unknown = true;
      else if (d.isZero) return true;
    }
    return unknown ? 'unknown' : false;
  }
}

/** Unevaluated Sum(f, (k, a, b), ...). */
export function Sum(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Sum', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** Unevaluated Product(f, (k, a, b), ...). */
export function Product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Product', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}
