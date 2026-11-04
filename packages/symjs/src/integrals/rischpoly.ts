// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Univariate polynomials and matrices over a field of rational
 * functions, the arithmetic the Risch algorithm (integrals/risch.ts,
 * rde.ts, prde.ts) does with SymPy's `Poly` and `PolyMatrix`.
 *
 * A {@link KPoly} is a polynomial in one generator whose coefficients are
 * expressions free of the generator, each kept in the normal form of
 * `cancel` (so a zero coefficient is the number 0). The algorithms follow
 * SymPy's dense polynomial routines (`dup_prem`, `dup_inner_subresultants`,
 * `dup_prs_resultant`, `dup_half_gcdex`, `dup_sqf_list`), with field
 * arithmetic in the coefficients.
 */

import { at, last } from '../core/guard';
import { NotInvertible, PolynomialError, ExactQuotientFailed } from '../core/errors';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { asNumerDenom, primitive } from '../core/methods';
import { diff } from '../calculus/diff';
import { polyCoefficients } from '../polys/poly';
import { Poly } from '../polys/sympoly';
import { cancel, fraction } from '../simplify/rational';

/** The normal form of a coefficient (SymPy's field elements of ZZ(x, ...)). */
export function kNorm(e: Expr): Expr {
  return e instanceof Rational ? e : cancel(e);
}

const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** A univariate polynomial over a field of rational functions (SymPy Poly(..., t, field=True)). */
export class KPoly {
  /** Coefficients, lowest degree first, without trailing zeros. */
  readonly cs: readonly Expr[];

  private constructor(
    readonly gen: Sym,
    cs: readonly Expr[],
  ) {
    let n = cs.length;
    while (n > 0 && isZeroE(at(cs, n - 1))) n--;
    this.cs = cs.slice(0, n);
  }

  /** The polynomial with the given coefficients (lowest degree first), normalized. */
  static fromCoeffs(cs: readonly ExprLike[], gen: Sym): KPoly {
    return new KPoly(
      gen,
      cs.map((c) => kNorm(sympify(c))),
    );
  }

  /** e as a polynomial in gen, or undefined when it is not one (SymPy as_poly). */
  static tryOf(eIn: ExprLike, gen: Sym): KPoly | undefined {
    const e = sympify(eIn);
    if (!e.has(gen)) return new KPoly(gen, [kNorm(e)]);
    const [n, d] = fraction(cancel(e));
    if (d.has(gen)) return undefined;
    const pc = polyCoefficients(n, gen);
    if (pc === undefined) return undefined;
    const deg = Math.max(0, ...pc.keys());
    const cs = Array.from({ length: deg + 1 }, (_, k) => kNorm(mul(pc.get(k) ?? S.Zero, pow(d, -1))));
    return new KPoly(gen, cs);
  }

  /** e as a polynomial in gen (SymPy Poly(e, gen)); PolynomialError when it is not one. */
  static of(e: ExprLike, gen: Sym): KPoly {
    const p = KPoly.tryOf(e, gen);
    if (p === undefined) throw new PolynomialError(`${String(sympify(e))} is not a polynomial in ${gen.name}`);
    return p;
  }

  static zero(gen: Sym): KPoly {
    return new KPoly(gen, []);
  }

  static one(gen: Sym): KPoly {
    return new KPoly(gen, [S.One]);
  }

  /** c*gen**k. */
  static monomial(c: ExprLike, k: number, gen: Sym): KPoly {
    const cs: Expr[] = Array.from({ length: k + 1 }, () => S.Zero);
    cs[k] = kNorm(sympify(c));
    return new KPoly(gen, cs);
  }

  get isZero(): boolean {
    return this.cs.length === 0;
  }

  /** The degree; -Infinity for the zero polynomial. */
  get degree(): number {
    return this.cs.length ? this.cs.length - 1 : -Infinity;
  }

  /** Constant (degree <= 0). */
  get isGround(): boolean {
    return this.cs.length <= 1;
  }

  get isOne(): boolean {
    return this.cs.length === 1 && at(this.cs, 0) instanceof Rational && at(this.cs, 0).key === S.One.key;
  }

  /** A single term c*gen**k. */
  get isMonomial(): boolean {
    return this.cs.filter((c) => !isZeroE(c)).length <= 1;
  }

  LC(): Expr {
    return this.cs.length ? at(this.cs, -1) : S.Zero;
  }

  TC(): Expr {
    return this.cs.length ? at(this.cs, 0) : S.Zero;
  }

  /** The coefficient of gen**k. */
  nth(k: number): Expr {
    return this.cs[k] ?? S.Zero;
  }

  asExpr(): Expr {
    return add(...this.cs.map((c, k) => mul(c, pow(this.gen, k))));
  }

  /** The same polynomial expression in another generator (SymPy Poly(p, gen)). */
  as(gen: Sym): KPoly {
    return gen.key === this.gen.key ? this : KPoly.of(this.asExpr(), gen);
  }

  /** Does the expression of the polynomial contain s (SymPy p.expr.has(s))? */
  has(s: Expr): boolean {
    return this.cs.some((c, k) => c.has(s) || (k > 0 && s.key === this.gen.key));
  }

  equals(o: KPoly): boolean {
    return this.sub(o).isZero;
  }

  private lift(o: KPoly | ExprLike): KPoly {
    return o instanceof KPoly ? o : KPoly.of(o, this.gen);
  }

  add(oIn: KPoly | ExprLike): KPoly {
    const o = this.lift(oIn);
    const n = Math.max(this.cs.length, o.cs.length);
    return KPoly.fromCoeffs(
      Array.from({ length: n }, (_, k) => add(this.nth(k), o.nth(k))),
      this.gen,
    );
  }

  sub(oIn: KPoly | ExprLike): KPoly {
    return this.add(this.lift(oIn).neg());
  }

  neg(): KPoly {
    return new KPoly(
      this.gen,
      this.cs.map((c) => kNorm(mul(-1, c))),
    );
  }

  mul(oIn: KPoly | ExprLike): KPoly {
    const o = this.lift(oIn);
    if (this.isZero || o.isZero) return KPoly.zero(this.gen);
    const out: Expr[][] = Array.from({ length: this.cs.length + o.cs.length - 1 }, () => []);
    this.cs.forEach((a, i) => {
      if (isZeroE(a)) return;
      o.cs.forEach((b, j) => {
        if (!isZeroE(b)) at(out, i + j).push(mul(a, b));
      });
    });
    return KPoly.fromCoeffs(
      out.map((ts) => add(...ts)),
      this.gen,
    );
  }

  mulGround(c: ExprLike): KPoly {
    const k = sympify(c);
    return new KPoly(
      this.gen,
      this.cs.map((a) => kNorm(mul(a, k))),
    );
  }

  /** Division of every coefficient by c (SymPy quo_ground / exquo_ground over a field). */
  quoGround(c: ExprLike): KPoly {
    return this.mulGround(pow(sympify(c), -1));
  }

  pow(n: number): KPoly {
    let r = KPoly.one(this.gen);
    for (let i = 0; i < n; i++) r = r.mul(this);
    return r;
  }

  /** Division with remainder over the field of coefficients. */
  div(o: KPoly): [KPoly, KPoly] {
    if (o.isZero) throw new RangeError('polynomial division by zero');
    const dg = o.degree;
    const lg = o.LC();
    let r: KPoly = this;
    const q: Expr[] = [];
    while (!r.isZero && r.degree >= dg) {
      const k = r.degree - dg;
      const c = kNorm(mul(r.LC(), pow(lg, -1)));
      q[k] = c;
      const t = KPoly.monomial(c, k, this.gen);
      // the leading term cancels exactly
      r = new KPoly(this.gen, r.sub(t.mul(o)).cs.slice(0, r.degree));
    }
    return [
      KPoly.fromCoeffs(
        Array.from({ length: q.length }, (_, k) => q[k] ?? S.Zero),
        this.gen,
      ),
      r,
    ];
  }

  quo(o: KPoly): KPoly {
    return this.div(o)[0];
  }

  rem(o: KPoly): KPoly {
    return this.div(o)[1];
  }

  /** Exact quotient (ExactQuotientFailed when o does not divide this polynomial). */
  exquo(o: KPoly): KPoly {
    const [q, r] = this.div(o);
    if (!r.isZero) throw new ExactQuotientFailed(`${String(o.asExpr())} does not divide ${String(this.asExpr())}`);
    return q;
  }

  monic(): KPoly {
    return this.isZero ? this : this.quoGround(this.LC());
  }

  /** The derivative in the generator. */
  diff(): KPoly {
    return KPoly.fromCoeffs(
      this.cs.slice(1).map((c, k) => mul(k + 1, c)),
      this.gen,
    );
  }

  /** The value at gen = a. */
  eval(a: ExprLike): Expr {
    const v = sympify(a);
    return kNorm(add(...this.cs.map((c, k) => mul(c, pow(v, k)))));
  }

  /** The monic greatest common divisor (Euclid over the field). */
  gcd(o: KPoly): KPoly {
    let f: KPoly = this;
    let g: KPoly = o;
    while (!g.isZero) [f, g] = [g, f.rem(g)];
    return f.monic();
  }

  lcm(o: KPoly): KPoly {
    if (this.isZero || o.isZero) return KPoly.zero(this.gen);
    return this.mul(o).quo(this.gcd(o)).monic();
  }

  /** SymPy half_gcdex: [s, h] with s*f = h (mod g), h the monic gcd. */
  halfGcdex(o: KPoly): [KPoly, KPoly] {
    let f: KPoly = this;
    let g: KPoly = o;
    let a = KPoly.one(this.gen);
    let b = KPoly.zero(this.gen);
    while (!g.isZero) {
      const [q, r] = f.div(g);
      [f, g] = [g, r];
      [a, b] = [b, a.sub(q.mul(b))];
    }
    return [a.quoGround(f.LC()), f.monic()];
  }

  /** The inverse modulo o (NotInvertible when the gcd is not 1). */
  invert(o: KPoly): KPoly {
    const [s, h] = this.halfGcdex(o);
    if (!h.isOne) throw new NotInvertible('zero divisor');
    return s.rem(o);
  }

  /** Pseudo-remainder (SymPy dup_prem). */
  prem(g: KPoly): KPoly {
    const dg = g.degree;
    let r: KPoly = this;
    let dr = r.degree;
    if (r.degree < dg) return r;
    let N = this.degree - dg + 1;
    const lcg = g.LC();
    for (;;) {
      const lcr = r.LC();
      const j = dr - dg;
      N--;
      r = new KPoly(this.gen, r.mulGround(lcg).sub(g.mul(KPoly.monomial(lcr, j, this.gen))).cs.slice(0, dr));
      dr = r.degree;
      if (dr < dg) break;
    }
    return r.mulGround(pow(lcg, N));
  }

  /** The subresultant PRS and the scalar subdeterminants (SymPy dup_inner_subresultants). */
  innerSubresultants(o: KPoly): [KPoly[], Expr[]] {
    let f: KPoly = this;
    let g: KPoly = o;
    let n = f.degree;
    let m = g.degree;
    if (n < m) {
      [f, g] = [g, f];
      [n, m] = [m, n];
    }
    // (resultantPRS passes nonzero polynomials)
    const R = [f, g];
    let d = n - m;
    let h = f.prem(g).mulGround(d % 2 === 0 ? -1 : 1);
    let lc = g.LC();
    let c = kNorm(pow(lc, d));
    const Ss: Expr[] = [S.One, c];
    c = kNorm(mul(-1, c));
    while (!h.isZero) {
      const k = h.degree;
      R.push(h);
      [f, g, m, d] = [g, h, k, m - k];
      const b = mul(-1, lc, pow(c, d));
      h = f.prem(g).quoGround(b);
      lc = g.LC();
      c = d > 1 ? kNorm(mul(pow(mul(-1, lc), d), pow(c, 1 - d))) : kNorm(mul(-1, lc));
      Ss.push(kNorm(mul(-1, c)));
    }
    return [R, Ss];
  }

  /** The resultant and the subresultant PRS (SymPy resultant(includePRS=True)). */
  resultantPRS(o: KPoly): [Expr, KPoly[]] {
    if (this.isZero || o.isZero) return [S.Zero, []];
    const [R, Ss] = this.innerSubresultants(o);
    if (last(R).degree > 0) return [S.Zero, R];
    return [last(Ss), R];
  }

  /** Square-free decomposition over the field (SymPy dup_sqf_list): [leading coefficient, monic factors]. */
  sqfList(all = false): [Expr, [KPoly, number][]] {
    if (this.isZero) return [S.Zero, []];
    const coeff = this.LC();
    const f = this.monic();
    if (f.degree <= 0) return [coeff, []];
    const result: [KPoly, number][] = [];
    let i = 1;
    let p: KPoly;
    let q: KPoly;
    {
      const h = f.diff();
      const g = f.gcd(h);
      p = f.quo(g);
      q = h.quo(g);
    }
    for (;;) {
      const d = p.diff();
      const h = q.sub(d);
      if (h.isZero) {
        result.push([p, i]);
        break;
      }
      const g = p.gcd(h);
      [p, q] = [p.quo(g), h.quo(g)];
      if (all || g.degree > 0) result.push([g, i]);
      i++;
    }
    return [coeff, result];
  }

  /** SymPy sqf_list_include: the leading coefficient is merged into the first factor. */
  sqfListInclude(all = false): [KPoly, number][] {
    const [coeff, factors] = this.sqfList(all);
    const f0 = factors[0];
    if (f0?.[1] === 1) return [[f0[0].mulGround(coeff), 1], ...factors.slice(1)];
    return [[KPoly.fromCoeffs([coeff], this.gen), 1], ...factors];
  }

  /** SymPy transform(p, q) with p = 1 and q = gen: the reversal q**n*f(1/q). */
  reverse(n: number): KPoly {
    const cs: Expr[] = Array.from({ length: n + 1 }, (_, k) => this.nth(n - k));
    return KPoly.fromCoeffs(cs, this.gen);
  }

  toString(): string {
    return `Poly(${String(this.asExpr())}, ${this.gen.name})`;
  }
}

/** f/g as a pair of polynomials without a common factor (SymPy f.cancel(g, include=True)). */
export function kCancel(f: KPoly, g: KPoly): [KPoly, KPoly] {
  const e = cancel(mul(f.asExpr(), pow(g.asExpr(), -1)));
  const [n0, d0] = fraction(e);
  // integer coefficients with the numeric content in front (SymPy clears the denominators over ZZ)
  const [cn, n] = primitive(n0);
  const [cd, d] = primitive(d0);
  const c = Rational.of(cn.p * cd.q, cn.q * cd.p);
  const num = KPoly.of(mul(c.p, n), f.gen);
  const den = KPoly.of(mul(c.q, d), f.gen);
  // the leading coefficient of the denominator positive (SymPy dmp_cancel over ZZ[...])
  return groundNegative(den.LC()) ? [num.neg(), den.neg()] : [num, den];
}

/** Is the lex-leading numeric coefficient of the polynomial e negative (SymPy K.is_negative over ZZ[...])? */
function groundNegative(e: Expr): boolean {
  const lc = e.freeSymbols().size ? Poly.from(e).LC() : e;
  return lc instanceof Rational && lc.isNegative;
}

/** The numerator and denominator of f as polynomials in t (SymPy frac_in). */
export function fracIn(f: Expr | readonly [KPoly, KPoly], t: Sym, opts: { cancel?: boolean } = {}): [KPoly, KPoly] {
  const e = f instanceof Array ? mul(f[0].asExpr(), pow(f[1].asExpr(), -1)) : f;
  const [n, d] = asNumerDenom(e);
  const fa = KPoly.tryOf(n, t);
  const fd = KPoly.tryOf(d, t);
  if (fa === undefined || fd === undefined) throw new PolynomialError(`Could not turn ${String(e)} into a fraction in ${t.name}.`);
  return opts.cancel === true ? kCancel(fa, fd) : [fa, fd];
}

/** The derivative of every coefficient as an expression (for derivation). */
export function exprDiff(e: Expr, v: Sym): Expr {
  return diff(e, v);
}

// ---- matrices over the field of rational functions (SymPy PolyMatrix) ----------------------------

/** A dense matrix of expressions, rows of equal length. */
export type KMatrix = Expr[][];

/** An m x n zero matrix. */
export function kZeros(m: number, n: number): KMatrix {
  return Array.from({ length: m }, () => Array.from({ length: n }, () => S.Zero));
}

/** The n x n identity matrix. */
export function kEye(n: number): KMatrix {
  return Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (i === j ? S.One : S.Zero)));
}

/** The number of columns (cols when the matrix has no rows). */
export function kCols(M: KMatrix, cols = 0): number {
  return M.length ? at(M, 0).length : cols;
}

/** [A | B] (B has the rows of A). */
export function kRowJoin(A: KMatrix, B: KMatrix): KMatrix {
  return A.map((r, i) => [...r, ...at(B, i)]);
}

/** A over B. */
export function kColJoin(A: KMatrix, B: KMatrix): KMatrix {
  return [...A.map((r) => [...r]), ...B.map((r) => [...r])];
}

/** The reduced row echelon form and the pivot columns. */
export function kRref(M0: KMatrix): [KMatrix, number[]] {
  const M = M0.map((r) => r.map(kNorm));
  const rows = M.length;
  const cols = kCols(M);
  const pivots: number[] = [];
  let r = 0;
  for (let c = 0; c < cols && r < rows; c++) {
    const p = M.findIndex((row, i) => i >= r && !isZeroE(at(row, c)));
    if (p < 0) continue;
    [M[r], M[p]] = [at(M, p), at(M, r)];
    const prow = at(M, r);
    const inv = pow(at(prow, c), -1);
    const scaled = prow.map((v) => kNorm(mul(v, inv)));
    M[r] = scaled;
    for (let i = 0; i < rows; i++) {
      const row = at(M, i);
      const k = at(row, c);
      if (i === r || isZeroE(k)) continue;
      M[i] = row.map((v, j) => kNorm(add(v, mul(-1, k, at(scaled, j)))));
    }
    pivots.push(c);
    r++;
  }
  return [M, pivots];
}

/** A basis of the right null space (one vector per free column, which is 1 in it). */
export function kNullspace(M: KMatrix, cols = kCols(M)): Expr[][] {
  const [R, pivots] = kRref(M);
  const out: Expr[][] = [];
  for (let j = 0; j < cols; j++) {
    if (pivots.includes(j)) continue;
    const v: Expr[] = Array.from({ length: cols }, () => S.Zero);
    v[j] = S.One;
    pivots.forEach((pc, i) => {
      v[pc] = kNorm(mul(-1, at(at(R, i), j)));
    });
    out.push(v);
  }
  return out;
}

