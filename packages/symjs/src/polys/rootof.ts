// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Indexed roots of polynomials (SymPy ComplexRootOf / CRootOf).
 */

import { InvariantError, PolynomialError } from '../core/errors';
import { at, defined, expectType, first, getOrThrow, pair } from '../core/guard';
import { ordered } from '../core/match';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Float, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { callableClass } from '../core/callable';
import { asRealImag } from '../core/methods';
import { toRational } from '../numeric/mpf';
import { nroots } from './nroots';
import type { ComplexInterval } from './rootisolation';
import { isolateComplexRootsSqf, isolateRealRoots } from './rootisolation';
import { Poly, rootHooks } from './sympoly';

/**
 * The index-th root of a polynomial with rational coefficients (SymPy
 * CRootOf): real roots come first in increasing order, then the non-real
 * roots in the order of their isolating rectangles (by lower-left corner),
 * each conjugate pair with the negative imaginary part first.
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
    return first([...freeSymbols(this.poly)].filter((s) => s instanceof Sym));
  }
  override subsSelf(old: Expr): Expr | undefined {
    // The polynomial generator is bound, not an unknown in the root's value.
    return old.key === this.gen.key ? this : undefined;
  }
  /**
   * The numerical roots of each polynomial, per precision, computed from certified
   * isolating intervals and cached for all indices.
   */
  private static readonly rootValues = new Map<string, Map<number,Expr>>();
  /** The number of root lists kept; the oldest is dropped beyond it. */
  static readonly rootValuesLimit = 256;
  private static readonly approximations = new Map<string,readonly Expr[]>();
  override numericValue(dps: number): Expr | undefined {
    const key = `${dps}:${this.poly.key}`;
    let rs = CRootOfNode.rootValues.get(key);
    if (rs === undefined) {
      rs = new Map();
      if (CRootOfNode.rootValues.size >= CRootOfNode.rootValuesLimit) {
        const oldest=first([...CRootOfNode.rootValues.keys()]);
        CRootOfNode.rootValues.delete(oldest);CRootOfNode.approximations.delete(oldest);
      }
      CRootOfNode.rootValues.set(key, rs);
    }
    let value = rs.get(this.index);
    if(value === undefined){
      if(this.isRealRoot){
        const saved=CRootOfNode.realIntervals.get(this.key);
        value=this.evalRational(undefined,undefined,{n:dps}).evalf(dps);
        if(saved===undefined)CRootOfNode.realIntervals.delete(this.key);
        else CRootOfNode.realIntervals.set(this.key,saved);
      }
      else {
        const iv=this.getInterval();
        const q=(v:Expr):Rational=>v instanceof Float?Rational.of(...toRational(v.mpf)):expectType(v,(r):r is Rational=>r instanceof Rational,'numeric root component');
        const inside=(x:Rational,a:Rational,b:Rational):boolean=>a.p*x.q<=x.p*a.q&&x.p*b.q<=b.p*x.q;
        for(let precision=dps+5;value===undefined;precision*=2){
          const candidates=CRootOfNode.approximations.get(key)??nroots(Poly.from(this.poly,[this.gen]),precision);
          const matches=candidates.filter((z)=>{const [re,im]=asRealImag(z);return inside(q(re),iv.ax,iv.bx)&&inside(q(im),iv.ay,iv.by);});
          if(matches.length===1){value=first(matches).evalf(dps);CRootOfNode.approximations.set(key,candidates);}
          else CRootOfNode.approximations.delete(key);
        }
      }
      rs.set(this.index,defined(value));
    }
    return value;
  }
  /** Clear the cached root values and isolating intervals (SymPy CRootOf.clear_cache). */
  static clearCache(): void {
    CRootOfNode.rootValues.clear();
    CRootOfNode.approximations.clear();
    CRootOfNode.realIntervals.clear();
    complexesCache.clear();
  }
  /** Numerical approximation at n decimal digits. */
  evalApprox(n: number | Rational): Expr {
    return defined(this.numericValue(n instanceof Rational ? n.toNumber() : n));
  }
  /** The polynomial of the root, primitive over ZZ (SymPy's PurePoly). */
  private get factor(): Factor {
    return factorOf(this.poly, this.gen);
  }
  /** The number of real roots of the polynomial (SymPy len(_reals_cache[poly])). */
  private get realCount(): number {
    return realCountOf(this.factor);
  }
  /** The isolating rectangle of a non-real root (SymPy _get_interval). */
  private getInterval(): ComplexInterval {
    const f = this.factor;
    const ivs = complexesCache.get(f.key) ?? getComplexes([f]).map(([u]) => u);
    return at(ivs, this.index - this.realCount);
  }
  /** Store a refined rectangle (SymPy _set_interval). */
  private setInterval(iv: ComplexInterval): void {
    getOrThrow(complexesCache, this.factor.key)[this.index - this.realCount] = iv;
  }
  private static readonly realIntervals = new Map<string, [Rational, Rational]>();
  /**
   * Rational approximation within dx of the real part and dy (default dx) of the imaginary part,
   * or else to n digits (SymPy eval_rational); the refined isolating interval is kept for later calls.
   */
  evalRational(dx?: ExprLike, dy?: ExprLike, opts: { n?: number | Rational } = {}): Expr {
    const n = opts.n instanceof Rational ? opts.n.toNumber() : opts.n ?? 15;
    if (!Number.isInteger(n) || n < 0) throw new RangeError('precision must be a nonnegative integer');
    const tx = tolerance(dx);
    const ty = dy === undefined ? tx : tolerance(dy);
    if (!this.isRealRoot) return this.evalRationalComplex(tx, ty, n);
    const p = Poly.from(this.poly, [this.gen]);
    let [a, b] = CRootOfNode.realIntervals.get(this.key) ?? at(p.intervals(), this.index)[0];
    const midpoint = (): Rational => Rational.of(a.p * b.q + b.p * a.q, 2n * a.q * b.q);
    while (a.key !== b.key) {
      const c = midpoint();
      const eps = tx ?? Rational.of(qabs(c).p, qabs(c).q * 10n ** BigInt(n + 2));
      [a, b] = p.refineRoot(a, b, eps);
      const center = qabs(midpoint());
      const width = Rational.of(b.p * a.q - a.p * b.q, a.q * b.q);
      if (tx !== undefined || width.p * center.q * 10n ** BigInt(n + 2) < center.p * width.q) break;
    }
    CRootOfNode.realIntervals.set(this.key, [a, b]);
    return midpoint();
  }
  /** SymPy eval_rational for a non-real root: bisection of its isolating rectangle. */
  private evalRationalComplex(tx: Rational | undefined, ty: Rational | undefined, n: number): Expr {
    // the relative tolerance 10**-(n + 2) when no tolerance is given
    const rtol = (c: Rational): Rational => qabs(Rational.of(c.p, c.q * 10n ** BigInt(n + 2)));
    let interval = this.getInterval();
    const imaginary = interval.ax.p * interval.bx.p <= 0n;
    let re: Rational;
    let im: Rational;
    for (;;) {
      const [dx, dy] = tx === undefined ? [imaginary ? S.One : rtol(interval.center[0]), rtol(interval.center[1])] : [tx, defined(ty)];
      interval = interval.refineSize(dx, dy);
      [re, im] = interval.center;
      if (imaginary) re = S.Zero;
      if (tx !== undefined || ((imaginary || qlt(interval.dx, rtol(re))) && qlt(interval.dy, rtol(im)))) break;
    }
    this.setInterval(interval);
    return add(re, mul(S.I, im));
  }
  /** Is this root real? (the real roots come first) */
  get isRealRoot(): boolean {
    return this.index < this.realCount;
  }
  /** SymPy CRootOf.is_real: the real roots come first. */
  override isRealSelf(): boolean {
    return this.isRealRoot;
  }
}

/** An irreducible polynomial over ZZ, primitive with a positive leading coefficient (SymPy's PurePoly of a factor). */
interface Factor {
  dense: bigint[];
  key: string;
  expr: Expr;
}

const qabs = (r: Rational): Rational => (r.p < 0n ? Rational.of(-r.p, r.q) : r);
const qlt = (a: Rational, b: Rational): boolean => a.p * b.q < b.p * a.q;

/** A tolerance of eval_rational: a Rational, or a Float by its decimal digits (SymPy Rational(str(dx))). */
function tolerance(v: ExprLike | undefined): Rational | undefined {
  if (v === undefined) return undefined;
  const e = sympify(v);
  const t = e instanceof Float ? decimalRational(e.toString()) : e;
  if (!(t instanceof Rational) || !t.isPositive) throw new RangeError('tolerance must be positive and rational');
  return t;
}

/** The value of a decimal numeral such as 0.100000000000000 or 1.00000000000000e-8. */
function decimalRational(s: string): Rational {
  const [mantissa = '', exp = '0'] = s.split('e');
  const [int = '', frac = ''] = mantissa.split('.');
  const e = Number(exp) - frac.length;
  const digits = BigInt(`${int}${frac}`);
  return Rational.of(digits * 10n ** BigInt(Math.max(e, 0)), 10n ** BigInt(Math.max(-e, 0)));
}

function factorOf(poly: Expr, gen: Sym): Factor {
  const cs = Poly.from(poly, [gen]).allCoeffs().map((c) => expectType(c, (v): v is Rational => v instanceof Rational, 'coefficient'));
  const den = cs.reduce((l, c) => ilcm(l, c.q), 1n);
  const ints = cs.map((c) => (c.p * den) / c.q);
  const g = ints.reduce((a, c) => igcd(a, c), 0n) * (first(ints) < 0n ? -1n : 1n);
  const dense = ints.map((c) => c / g);
  const d = dense.length - 1;
  return { dense, key: dense.join(','), expr: add(...dense.map((c, i) => mul(Rational.of(c), pow(gen, d - i)))) };
}

/** SymPy _complexes_cache: the isolating rectangles of the non-real roots of irreducible polynomials. */
const complexesCache = new Map<string, ComplexInterval[]>();

const realCountOf = (f: Factor): number => isolateRealRoots([[f.dense, 1]]).length;

/** The number of imaginary roots of an irreducible polynomial (SymPy _imag_count_of_factor). */
function imagCount({ dense }: Factor): number {
  const d = dense.length - 1;
  if (dense.some((c, i) => c !== 0n && (d - i) % 2 === 1)) return 0;
  // the real roots of f(I*y)
  return isolateRealRoots([[dense.map((c, i) => ((d - i) % 4 === 2 ? -c : c)), 1]]).length;
}

/**
 * The isolating rectangles of the non-real roots of irreducible polynomials,
 * pairwise disjoint, off the imaginary axis unless the root is imaginary and
 * off the real axis, grouped by polynomial in SymPy's ordered() order (SymPy
 * _get_complexes, _complexes_sorted, _refine_complexes, _refine_imaginary);
 * updates the cache.
 */
function getComplexes(factors: Factor[]): [ComplexInterval, Factor][] {
  const byExpr = new Map(factors.map((f) => [f.expr.key, f]));
  const fs = ordered(factors.map((f) => f.expr)).map((e) => getOrThrow(byExpr, e.key));
  const complexes = fs.flatMap((f) => (complexesCache.get(f.key) ?? isolateComplexRootsSqf(f.dense)).map((u): [ComplexInterval, Factor] => [u, f]));
  for (let i = 0; i < complexes.length; i++) {
    let [u, f] = at(complexes, i);
    for (let j = i + 1; j < complexes.length; j++) {
      let [v, g] = at(complexes, j);
      [u, v] = u.refineDisjoint(v);
      complexes[j] = [v, g];
    }
    complexes[i] = [u, f];
  }
  // refine until the real parts are unambiguously positive or negative, except for imaginary roots
  const offImaginaryAxis = (u: ComplexInterval) => u.ax.p * u.bx.p > 0n;
  const out: [ComplexInterval, Factor][] = [];
  for (const f of fs) {
    const group = complexes.filter(([, g]) => g === f).map(([u]) => u);
    const nimag = imagCount(f);
    if (nimag === 0) {
      for (const [i, u] of group.entries()) {
        let v = u;
        while (!offImaginaryAxis(v)) v = v.refine();
        group[i] = v;
      }
    } else {
      // all but nimag rectangles leave the imaginary axis (at least one pass, as in SymPy)
      let potential = group.map((_, i) => i);
      do {
        potential = potential.filter((i) => {
          if (offImaginaryAxis(at(group, i))) return false;
          // SymPy also skips rectangles of zero width, which the bisection never makes
          group[i] = at(group, i).refine();
          return true;
        });
      } while (potential.length !== nimag);
    }
    for (const u of group) out.push([u, f]);
  }
  // the imaginary parts off the real axis
  for (const [i, [u0, f]] of out.entries()) {
    let u = u0;
    while (u.ay.p * u.by.p <= 0n) u = u.refine();
    out[i] = [u, f];
  }
  for (const f of fs) complexesCache.set(f.key, out.filter(([, g]) => g === f).map(([u]) => u));
  return out;
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
  const roots = p.allRoots({ radicals });
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
