// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Indexed roots of polynomials (SymPy ComplexRootOf / CRootOf).
 */

import { InvariantError, PolynomialError, NotImplementedError } from '../core/errors';
import { at, first, pair, defined } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Float, Rational, S, Sym } from '../core/nodes';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { callableClass } from '../core/callable';
import { toRational } from '../numeric/mpf';
import { nroots } from './nroots';
import { Poly, rootHooks } from './sympoly';

/**
 * The index-th root of a polynomial with rational coefficients (SymPy
 * CRootOf): real roots come first in increasing order, then the complex
 * roots by increasing real part, the one with negative imaginary part first.
 */
class CRootOfNode extends ExtensionExpr {
  readonly index: number;
  constructor(poly: Expr, index: number | Rational) {
    const i = typeof index === 'number' ? index : Number(index.p);
    super('CRootOf', [poly, Rational.of(i)]);
    this.index = i;
  }
  override freeSymbolsSelf(): ReadonlySet<Sym> {
    return new Set();
  }
  get poly(): Expr {
    return at(this.args, 0);
  }
  withArgs(args: readonly Expr[]): Expr {
    const [poly, index] = pair(args);
    if (!(index instanceof Rational)) throw new InvariantError('CRootOf index is not a Rational');
    return new CRootOf(poly, index);
  }
  override printStr(print: (e: Expr) => string): string {
    return `CRootOf(${print(this.poly)}, ${this.index})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{CRootOf} {\\left(${print(this.poly)}, ${this.index}\\right)}`;
  }
  /** The generator of the polynomial. */
  get gen(): Sym {
    return first([...freeSymbols(this.poly)]);
  }
  override subsSelf(old: Expr): Expr | undefined {
    // The polynomial generator is bound, not an unknown in the root's value.
    return old.key === this.gen.key ? this : undefined;
  }
  /**
   * The numerical roots of each polynomial, per precision: one nroots call serves all the indexed
   * roots of a polynomial (SymPy caches the isolating intervals of a polynomial at class level).
   */
  private static readonly rootValues = new Map<string, readonly Expr[]>();
  /** The number of root lists kept; the oldest is dropped beyond it. */
  static readonly rootValuesLimit = 256;
  override numericValue(dps: number): Expr | undefined {
    const key = `${dps}:${this.poly.key}`;
    let rs = CRootOfNode.rootValues.get(key);
    if (rs === undefined) {
      rs = nroots(Poly.from(this.poly, [this.gen]), dps);
      if (CRootOfNode.rootValues.size >= CRootOfNode.rootValuesLimit) CRootOfNode.rootValues.delete(first([...CRootOfNode.rootValues.keys()]));
      CRootOfNode.rootValues.set(key, rs);
    }
    return rs[this.index];
  }
  /** Clear cached numerical root lists (SymPy CRootOf.clear_cache). */
  static clearCache(): void {
    CRootOfNode.rootValues.clear();
    CRootOfNode.realIntervals.clear();
  }
  /** Numerical approximation at n decimal digits. */
  evalApprox(n: number | Rational): Expr {
    return defined(this.numericValue(n instanceof Rational ? n.toNumber() : n));
  }
  private static readonly realIntervals = new Map<string, [Rational, Rational]>();
  /** Certified rational approximation of a real root, by interval refinement. */
  evalRational(dx?: ExprLike, _dy?: ExprLike, opts: { n?: number | Rational } = {}): Expr {
    const p = Poly.from(this.poly, [this.gen]);
    const intervals = p.intervals();
    if (this.index >= intervals.length) throw new NotImplementedError('evalRational: complex root isolation is not implemented');
    let [a, b] = CRootOfNode.realIntervals.get(this.key) ?? at(intervals, this.index)[0];
    const midpoint = (): Rational => Rational.of(a.p * b.q + b.p * a.q, 2n * a.q * b.q);
    const abs = (r: Rational): Rational => Rational.of(r.p < 0n ? -r.p : r.p, r.q);
    const n = opts.n instanceof Rational ? opts.n.toNumber() : opts.n ?? 15;
    if (!Number.isInteger(n) || n < 0) throw new RangeError('precision must be a nonnegative integer');
    const value = dx === undefined ? undefined : sympify(dx);
    const tolerance = value instanceof Float ? Rational.of(...toRational(value.mpf)) : value;
    if (tolerance !== undefined && (!(tolerance instanceof Rational) || !tolerance.isPositive)) throw new RangeError('tolerance must be positive and rational');
    while (a.key !== b.key) {
      const c = midpoint();
      const eps = tolerance ?? Rational.of(abs(c).p, abs(c).q * 10n ** BigInt(n + 2));
      [a, b] = p.refineRoot(a, b, eps);
      const center = abs(midpoint());
      const width = Rational.of(b.p * a.q - a.p * b.q, a.q * b.q);
      if (tolerance !== undefined || width.p * center.q * 10n ** BigInt(n + 2) < center.p * width.q) break;
    }
    CRootOfNode.realIntervals.set(this.key, [a, b]);
    return midpoint();
  }
  private realRoot?: boolean;
  /** Is this root real? (nroots gives a Float, or 0, for each real root) */
  get isRealRoot(): boolean {
    if (this.realRoot === undefined) {
      const v = this.numericValue(15);
      this.realRoot = v instanceof Float || v === S.Zero;
    }
    return this.realRoot;
  }
  /** SymPy CRootOf.is_real: the real roots come first. */
  override isRealSelf(): boolean {
    return this.isRealRoot;
  }
}

/** Options of indexed roots (rootof uses radicals by default, CRootOf does not). */
export interface RootOfOptions { radicals?: boolean; }

/** Evaluated indexed root. Irreducible nontrivial factors remain CRootOf nodes. */
export function rootOf(f: ExprLike | Poly, index: number | Rational, opts: RootOfOptions = {}): Expr {
  let p = f instanceof Poly ? f : Poly.from(sympify(f));
  if (p.gens.length !== 1 || !(p.gens[0] instanceof Sym)) throw new PolynomialError('rootof requires one Symbol generator');
  if (p.domain === 'RR') p = p.toExact();
  const deg = p.degree(), i = index instanceof Rational ? index.toNumber() : index;
  if (deg <= 0) throw new PolynomialError('Cannot construct CRootOf for a constant polynomial');
  if (!Number.isInteger(i) || i < -deg || i >= deg) throw new RangeError(`rootof: index ${i} out of range`);
  const radicals = opts.radicals ?? true;
  const binomial = radicals && p.termList.length === 2 && !p.TC().equals(0);
  const roots = binomial ? p.roots().map((r) => ({ r, v: r.toComplex() })).sort((a, b) => {
    const ar = Math.abs(a.v.im) < 1e-12, br = Math.abs(b.v.im) < 1e-12;
    return Number(br) - Number(ar) || a.v.re - b.v.re || a.v.im - b.v.im;
  }).map(({ r }) => r) : p.allRoots({ radicals });
  return at(roots, i < 0 ? deg + i : i);
}

/** Call to evaluate; new CRootOf constructs the unevaluated node for AST work. */
export const CRootOf = callableClass(CRootOfNode, (f: ExprLike | Poly, index: number | Rational, opts: RootOfOptions = {}): Expr => rootOf(f, index, { radicals: false, ...opts }));
export type CRootOf = CRootOfNode;
/** SymPy's full spelling of CRootOf. */
export const ComplexRootOf = CRootOf;
export type ComplexRootOf = CRootOfNode;
/** SymPy RootOf evaluates the trivial radical cases by default. */
export const RootOf = callableClass(CRootOfNode, rootOf);
export type RootOf = CRootOfNode;

rootHooks.crootof = (e, i) => new CRootOf(e, i);
