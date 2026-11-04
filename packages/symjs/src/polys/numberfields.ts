// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// The minimal polynomial is ported from SymPy 1.14.0
// (polys/numberfields/minpoly.py), Copyright (c) 2006-2023 SymPy Development
// Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Minimal polynomials of algebraic elements (SymPy minimal_polynomial
 * by composition of resultants, over QQ, QQ(symbols) or QQ<a>) and algebraic
 * numbers given as polynomials in a primitive element (a minimal port of
 * SymPy AlgebraicNumber).
 */

import { NotImplementedError, PolynomialError } from '../core/errors';
import { at, defined, expectType, first, pair } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Fn, Mul, Pow, Rational, S, Special, Sym } from '../core/nodes';
import { add, cbrt, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { evalf as evalfExpr } from '../numeric/evalf';
import { parse } from '../parsing/parser';
import { expand, expandMul } from '../simplify/expand';
import { collect } from '../simplify/radsimp';
import { divisors, factorint } from '../ntheory/factor';
import { cos } from '../functions/elementary';
import { chebyshevtCoeffs } from '../functions/polynomials';
import { CRootOf } from './rootof';
import { Poly, factor, factorListExpr, resultant } from './sympoly';

/** Options of minimalPolynomial. */
export interface MinimalPolynomialOptions {
  /** Compose the minimal polynomials of the parts by resultants (SymPy compose=True, the default). */
  compose?: boolean;
  /** Return a Poly instead of an expression. */
  polys?: boolean;
  /** The ground domain: 'QQ', or an algebraic field 'QQ<a, b, ...>' (SymPy QQ.algebraic_field(a, b, ...)). */
  domain?: string;
}

/** The ground domain: its symbols (QQ(y, ...)) and the generators of an algebraic field (QQ<a>). */
interface Ground {
  symbols: readonly Sym[];
  extension: readonly Expr[];
}

const notAlgebraic = (ex: Expr): NotImplementedError => new NotImplementedError(`${ex.toString()} does not seem to be an algebraic element`);
const same = (a: Expr, b: Expr): boolean => a.key === b.key;
const isQQ = (dom: Ground): boolean => !dom.symbols.length && !dom.extension.length;

/** The irreducible factors (over the ground domain) of a polynomial in x. */
function factorsIn(p: Expr, x: Sym, dom: Ground): Expr[] {
  if (dom.extension.length) {
    const f = factor(p, { extension: [...dom.extension] });
    const parts = f instanceof Mul ? f.args : [f];
    return parts.map((t) => (t instanceof Pow && t.exp instanceof Rational ? t.base : t)).filter((t) => t.has(x));
  }
  return factorListExpr(expand(p), [x])[1].map(([f]) => f);
}

/** The absolute value of e (a number) at `dps` digits, or undefined for nan and infinities. */
function absAt(e: Expr, dps: number): number | undefined {
  const v = evalfExpr(e, dps);
  if (v instanceof Special) return undefined;
  const z = v.toComplex();
  return Math.hypot(z.re, z.im);
}

/** The ways to assign values 0..bound-1 to k symbols, nondecreasing (Python subsets(range(bound), k, repetition=True)). */
function points(k: number, bound: number): number[][] {
  if (k === 0) return [[]];
  const out: number[][] = [];
  const rec = (start: number, acc: number[]): void => {
    if (acc.length === k) {
      out.push(acc);
      return;
    }
    for (let i = start; i < bound; i++) rec(i, [...acc, i]);
  };
  rec(0, []);
  return out;
}

/**
 * SymPy _choose_factor: the factor that vanishes at v, decided numerically
 * (at small integer values of the symbols of the domain). @internal
 */
export function chooseFactor(factors: readonly Expr[], x: Sym, v: Expr, dom: Ground): Expr {
  if (factors.length === 1) return first(factors);
  for (let prec = 10; prec <= 200; prec *= 2) {
    const fe = factors.map((f) => xreplace(f, [[x, v]]));
    for (const pt of points(dom.symbols.length, 5)) {
      const subs = dom.symbols.map((s, i): [Expr, Expr] => [s, Rational.of(at(pt, i))]);
      const vals = fe.map((f) => absAt(xreplace(f, subs), prec));
      const cands = vals.flatMap((a, i): [number, number][] => (a === undefined ? [] : [[a, i]]));
      if (cands.length < vals.length) continue;
      cands.sort((p, q) => p[0] - q[0]);
      const [[a, ix], [b]] = [at(cands, 0), at(cands, 1)];
      if (b > a * 1e6) return at(factors, ix);
    }
  }
  throw new NotImplementedError(`multiple candidates for the minimal polynomial of ${v.toString()}`);
}

/** The coefficients of p in x, highest power first, and its degree. */
function coeffsOf(p: Expr, x: Sym): Expr[] {
  return Poly.from(p, [x]).allCoeffs();
}

/** SymPy _invertx: x**n p(1/x). */
function invertx(p: Expr, x: Sym): Expr {
  const cs = coeffsOf(p, x);
  return add(...cs.map((c, i) => mul(c, pow(x, i))));
}

/** SymPy _muly: y**n p(x/y). */
function muly(p: Expr, x: Sym, y: Sym): Expr {
  const cs = coeffsOf(p, x);
  const n = cs.length - 1;
  return add(...cs.map((c, i) => mul(c, pow(x, n - i), pow(y, i))));
}

const degreeIn = (p: Expr, x: Sym): number => Poly.from(p, [x]).degree();

/** SymPy _minpoly_op_algebraic_element: the minimal polynomial of ex1 + ex2 or ex1*ex2. */
function opAlgebraic(op: 'add' | 'mul', ex1: Expr, ex2: Expr, x: Sym, dom: Ground, mp1In?: Expr, mp2In?: Expr): Expr {
  const y = new Dummy(x.name);
  const mp1 = mp1In ?? compose(ex1, x, dom);
  const mp2 = mp2In === undefined ? compose(ex2, y, dom) : xreplace(mp2In, [[x, y]]);
  const mp1a = op === 'add' ? expand(xreplace(mp1, [[x, add(x, mul(-1, y))]])) : muly(mp1, x, y);
  const r = resultant(mp1a, mp2, y);
  const deg1 = degreeIn(mp1, x);
  const deg2 = degreeIn(mp2, y);
  if ((op === 'mul' && deg1 === 1) || deg2 === 1) return r;
  return chooseFactor(factorsIn(r, x, dom), x, op === 'add' ? add(ex1, ex2) : mul(ex1, ex2), dom);
}

/** SymPy _minpoly_pow: the minimal polynomial of ex**pw for a rational pw. */
function minpolyPow(exIn: Expr, pwIn: Expr, x: Sym, dom: Ground): Expr {
  let ex = exIn;
  let mp = compose(ex, x, dom);
  if (!(pwIn instanceof Rational)) throw notAlgebraic(ex);
  let pw = pwIn;
  if (pw.isNegative) {
    if (same(mp, x)) throw new RangeError(`${ex.toString()} is zero`);
    mp = invertx(mp, x);
    if (same(pw, S.NegOne)) return mp;
    pw = Rational.of(-pw.p, pw.q);
    ex = pow(ex, -1);
  }
  const p = pw;
  const y = new Dummy(x.name);
  const res = resultant(xreplace(mp, [[x, y]]), add(pow(x, Rational.of(p.q)), mul(-1, pow(y, Rational.of(p.p)))), y);
  return chooseFactor(factorsIn(res, x, dom), x, pow(ex, p), dom);
}

/** The polynomial sum_i cs[i] x**i (cs lowest power first) as an expression. */
const polyIn = (cs: readonly Expr[], x: Expr): Expr => add(...cs.map((c, i) => mul(c, pow(x, i))));

/** The rational c with ex = c*pi (c != 1: cos(pi), ... evaluate), or undefined. */
function piMultiple(ex: Expr): Rational | undefined {
  if (!(ex instanceof Mul && ex.args.length === 2)) return undefined;
  const [c, p] = pair(ex.args);
  return c instanceof Rational && same(p, S.Pi) ? c : undefined;
}

/** SymPy _minpoly_sin. */
function minpolySin(ex: Expr, x: Sym, dom: Ground): Expr {
  const c = piMultiple(first(ex.args));
  if (!c) throw notAlgebraic(ex);
  const n = Number(c.q);
  const isPrime = divisors(n).length === 2;
  if (isPrime) {
    // sin(p*pi/q) for a prime q: x**(n-1) T_n's coefficients shifted (SymPy's formula)
    const a = [...chebyshevtCoeffs(n)].reverse();
    return add(...Array.from({ length: n }, (_, i) => mul(at(a, i), pow(x, n - i - 1))));
  }
  if (c.p === 1n && n === 9) return add(mul(64, pow(x, 6)), mul(-96, pow(x, 4)), mul(36, pow(x, 2)), -3);
  if (n % 2 === 1) return chooseFactor(factorsIn(polyIn(chebyshevtCoeffs(n), x), x, dom), x, ex, dom);
  return compose(sqrt(mul(S.Half, add(1, mul(-1, cos(mul(2, c, S.Pi)))))), x, dom);
}

/** SymPy _minpoly_cos. */
function minpolyCos(ex: Expr, x: Sym, dom: Ground): Expr {
  const c = piMultiple(first(ex.args));
  if (!c) throw notAlgebraic(ex);
  if (c.p === 1n && c.q === 7n) return add(mul(8, pow(x, 3)), mul(-4, pow(x, 2)), mul(-4, x), 1);
  if (c.p === 1n && c.q === 9n) return add(mul(8, pow(x, 3)), mul(-6, x), -1);
  if (c.p === 2n && divisors(c.q).length === 2) {
    const s = minpolySin(ex, x, dom);
    return expand(xreplace(s, [[x, sqrt(mul(S.Half, add(1, mul(-1, x))))]]));
  }
  const r = add(polyIn(chebyshevtCoeffs(Number(c.q)), x), mul(-1, pow(-1, Rational.of(c.p))));
  return chooseFactor(factorsIn(r, x, dom), x, ex, dom);
}

/** SymPy _minpoly_tan. */
function minpolyTan(ex: Expr, x: Sym, dom: Ground): Expr {
  const c0 = piMultiple(first(ex.args));
  if (!c0) throw notAlgebraic(ex);
  const c = Rational.of(2n * c0.p, c0.q);
  const n = Number(c.q);
  let a = c.p % 2n === 0n ? BigInt(n) : 1n;
  const terms: Expr[] = [];
  for (let k = Number((c.p + 1n) % 2n); k <= n; k += 2) {
    terms.push(mul(Rational.of(a), pow(x, k)));
    // an exact division (the coefficients of the multiple-angle formula)
    a = -(a * BigInt(n - k - 1) * BigInt(n - k)) / BigInt((k + 1) * (k + 2));
  }
  return chooseFactor(factorsIn(add(...terms), x, dom), x, ex, dom);
}

/** SymPy _minpoly_exp: exp(c*I*pi) for a rational c. */
function minpolyExp(ex: Pow, x: Sym, dom: Ground): Expr {
  const c = piMultiple(mul(ex.exp, pow(S.I, -1)));
  if (!c) throw notAlgebraic(ex);
  const q = Number(c.q);
  if (c.p === 1n || c.p === -1n) {
    if (q === 3) return add(pow(x, 2), mul(-1, x), 1);
    if (q === 4) return add(pow(x, 4), 1);
    if (q === 6) return add(pow(x, 4), mul(-1, pow(x, 2)), 1);
    if (q === 8) return add(pow(x, 8), 1);
    if (q === 9) return add(pow(x, 6), mul(-1, pow(x, 3)), 1);
    if (q === 10) return add(pow(x, 8), mul(-1, pow(x, 6)), pow(x, 4), mul(-1, pow(x, 2)), 1);
    if (divisors(q).length === 2) return add(...Array.from({ length: q }, (_, i) => pow(mul(-1, x), i)));
  }
  const factors = divisors(2 * q).map((d) => {
    const cs = cyclotomicCoeffs(Number(d));
    return add(...cs.map((v, i) => mul(Rational.of(v), pow(x, cs.length - 1 - i))));
  });
  return chooseFactor(factors, x, ex, dom);
}

/** p(x^k) for coefficients highest first (SymPy dup_inflate). */
const inflate = (p: readonly bigint[], k: number): bigint[] => p.flatMap((c, i) => (i === p.length - 1 ? [c] : [c, ...Array<bigint>(k - 1).fill(0n)]));

/** The exact quotient of p by a monic q, coefficients highest first (SymPy dup_quo over ZZ). */
function quo(p: readonly bigint[], q: readonly bigint[]): bigint[] {
  const r = [...p];
  const out: bigint[] = [];
  for (let i = 0; i + q.length <= r.length; i++) {
    const c = at(r, i);
    out.push(c);
    for (let j = 0; j < q.length; j++) r[i + j] = at(r, i + j) - c * at(q, j);
  }
  return out;
}

/** The coefficients of the n-th cyclotomic polynomial, highest first (SymPy dup_zz_cyclotomic_poly). */
export function cyclotomicCoeffs(n: number): bigint[] {
  let h = [1n, -1n];
  for (const [p, k] of factorint(n)) {
    h = quo(inflate(h, Number(p)), h);
    h = inflate(h, Number(p ** (k - 1n)));
  }
  return h;
}

/** SymPy _is_sum_surds: a sum of products of rationals and real square roots of rationals. */
function isSumSurds(p: Expr): boolean {
  const terms = p instanceof Add ? p.args : [p];
  return terms.every((t) =>
    (t instanceof Mul ? t.args : [t]).every(
      (f) => f instanceof Rational || (f instanceof Pow && f.base instanceof Rational && f.exp instanceof Rational && f.exp.q <= 2n && !f.base.isNegative),
    ),
  );
}

/**
 * The minimal polynomial of a sum of surds (or of a rational radical): the
 * irreducible factor of x**q - r**p, or of the norm of x - v, that vanishes at v.
 */
function sumOfSurds(v: Expr, x: Sym): Expr {
  const N = v instanceof Pow && v.base instanceof Rational && v.exp instanceof Rational
    ? Poly.from(add(pow(x, Rational.of(v.exp.q)), mul(-1, pow(v.base, Rational.of(v.exp.p)))), [x])
    : Poly.from(add(x, mul(-1, v)), [x]).norm();
  return chooseFactor(N.factorList()[1].map(([f]) => f.asExpr()), x, v, { symbols: [], extension: [] });
}

/** SymPy _minpoly_compose. */
function compose(ex: Expr, x: Sym, dom: Ground): Expr {
  if (ex instanceof Rational) return add(mul(ex.q, x), -ex.p);
  if (same(ex, S.I)) return factorsIn(add(pow(x, 2), 1), x, dom).length === 1 ? add(pow(x, 2), 1) : add(x, mul(-1, S.I));
  if (ex instanceof Constant && ex.name === 'GoldenRatio') {
    const fs = factorsIn(add(pow(x, 2), mul(-1, x), -1), x, dom);
    return fs.length === 1 ? add(pow(x, 2), mul(-1, x), -1) : chooseFactor(fs, x, mul(S.Half, add(1, sqrt(5))), dom);
  }
  if (ex instanceof Constant && ex.name === 'TribonacciConstant') {
    const fs = factorsIn(add(pow(x, 3), mul(-1, pow(x, 2)), mul(-1, x), -1), x, dom);
    const value = mul(Rational.of(1, 3), add(1, cbrt(add(19, mul(-3, sqrt(33)))), cbrt(add(19, mul(3, sqrt(33))))));
    return chooseFactor(fs, x, value, dom);
  }
  if (ex instanceof Sym && dom.symbols.some((s) => same(s, ex))) return add(x, mul(-1, ex));
  if (isQQ(dom) && isSumSurds(ex)) {
    try {
      return sumOfSurds(ex, x);
    } catch {
      // more than three square roots: composed by resultants below
    }
  }
  if (ex instanceof Add) {
    let mp = opAlgebraic('add', at(ex.args, 0), at(ex.args, 1), x, dom);
    let p = add(at(ex.args, 0), at(ex.args, 1));
    for (const px of ex.args.slice(2)) {
      mp = opAlgebraic('add', p, px, x, dom, mp);
      p = add(p, px);
    }
    return mp;
  }
  if (ex instanceof Mul) return minpolyMul(ex, x, dom);
  if (ex instanceof Pow) {
    if (ex.base instanceof Constant && ex.base.name === 'E') return minpolyExp(ex, x, dom);
    return minpolyPow(ex.base, ex.exp, x, dom);
  }
  if (ex instanceof Fn && ex.name === 'sin') return minpolySin(ex, x, dom);
  if (ex instanceof Fn && ex.name === 'cos') return minpolyCos(ex, x, dom);
  if (ex instanceof Fn && ex.name === 'tan') return minpolyTan(ex, x, dom);
  if (ex instanceof CRootOf) {
    const p = xreplace(ex.poly, [...freeSymbols(ex.poly)].map((s): [Expr, Expr] => [s, x]));
    return chooseFactor(factorsIn(p, x, dom), x, ex, dom);
  }
  throw notAlgebraic(ex);
}

/**
 * The minimal polynomial of a product: the rational powers of rationals are
 * gathered into one radical first (SymPy's Factors split), the other factors
 * are composed one at a time.
 */
function minpolyMul(ex: Mul, x: Sym, dom: Ground): Expr {
  const isRat = (f: Expr): boolean => f instanceof Rational || (f instanceof Pow && f.base instanceof Rational && f.exp instanceof Rational);
  const rat = ex.args.filter(isRat);
  const rest = ex.args.filter((f) => !isRat(f));
  if (rat.length && rest.length && isQQ(dom)) {
    const ex1 = mul(...rest);
    const ex2 = mul(...rat);
    // ex2**L is rational for L the lcm of the exponent denominators
    const L = rat.reduce((l, f) => (f instanceof Pow && f.exp instanceof Rational ? ilcm(l, f.exp.q) : l), 1n);
    const R = expectType(pow(ex2, Rational.of(L)), (v): v is Rational => v instanceof Rational, 'a rational power');
    const mp2 = add(mul(R.q, pow(x, Rational.of(L))), -R.p);
    return opAlgebraic('mul', ex1, ex2, x, dom, minimalPolynomialOf(ex1, x, dom), mp2);
  }
  let mp = opAlgebraic('mul', at(ex.args, 0), at(ex.args, 1), x, dom);
  let p = mul(at(ex.args, 0), at(ex.args, 1));
  for (const px of ex.args.slice(2)) {
    mp = opAlgebraic('mul', p, px, x, dom, mp);
    p = mul(p, px);
  }
  return mp;
}

/** The rational coefficient of a term (1 for a term without one). */
function numericCoeff(t: Expr): Rational {
  const c = t instanceof Mul ? at(t.args, 0) : t;
  return c instanceof Rational ? c : S.One;
}

/** The terms of p with their rational content removed and a positive leading coefficient (SymPy primitive and sign). */
function normalize(p: Expr, x: Sym): Expr {
  const e = expand(p);
  const terms = e instanceof Add ? e.args : [e];
  const coeffs = terms.map(numericCoeff);
  let num = 0n;
  let den = 1n;
  for (const c of coeffs) {
    num = igcd(num, c.p < 0n ? -c.p : c.p);
    den = ilcm(den, c.q);
  }
  let r = expandMul(mul(Rational.of(den, num), e));
  const lc = first(Poly.from(r, [x]).allCoeffs());
  // SymPy negates only a leading coefficient known to be negative (-y stays)
  if (lc instanceof Rational && lc.isNegative) r = expandMul(mul(-1, r));
  return r;
}

function minimalPolynomialOf(ex: Expr, x: Sym, dom: Ground): Expr {
  return normalize(compose(ex, x, dom), x);
}

/** The free symbols of ex outside CRootOf (whose polynomial variable is bound). */
function groundSymbols(ex: Expr): Set<Sym> {
  if (ex instanceof CRootOf) return new Set();
  if (ex instanceof Sym) return new Set([ex]);
  return new Set(ex.args.flatMap((a) => [...groundSymbols(a)]));
}

/** The ground domain of ex: QQ(free symbols), or the algebraic field given as 'QQ<a, b>'. */
function groundOf(ex: Expr, domain: string | undefined): Ground {
  const symbols = [...groundSymbols(ex)];
  if (domain === undefined || domain === 'QQ') return { symbols, extension: [] };
  const m = /^QQ<(.*)>$/.exec(domain);
  if (!m) throw new NotImplementedError(`minimal_polynomial over the domain ${domain}`);
  return { symbols, extension: topLevel(defined(m[1], 'domain generators')).map((g) => parse(g)) };
}

/** The comma-separated parts of s outside parentheses. */
function topLevel(s: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    else if (ch === ',' && depth === 0) {
      out.push(s.slice(start, i));
      start = i + 1;
    }
  }
  out.push(s.slice(start));
  return out;
}

/**
 * SymPy minimal_polynomial(ex, x): the minimal polynomial of the algebraic
 * element ex over QQ, over the field of the free symbols of ex
 * (QQ(y) for sqrt(y)), or over an algebraic field `{ domain: 'QQ<a>' }`;
 * primitive with a positive leading coefficient, collected in x.
 */
export function minimalPolynomial(ex: ExprLike, x?: Sym, opts?: MinimalPolynomialOptions & { polys?: false }): Expr;
export function minimalPolynomial(ex: ExprLike, x: Sym | undefined, opts: MinimalPolynomialOptions & { polys: true }): Poly;
export function minimalPolynomial(ex: ExprLike, x?: Sym, opts?: MinimalPolynomialOptions): Expr | Poly;
export function minimalPolynomial(exIn: ExprLike, xIn?: Sym, opts: MinimalPolynomialOptions = {}): Expr | Poly {
  let ex = sympify(exIn);
  if (!groundSymbols(ex).size) ex = expand(ex);
  const x = xIn ?? new Dummy('x');
  const dom = groundOf(ex, opts.domain);
  if (dom.symbols.some((s) => same(s, x))) throw new PolynomialError(`the variable ${x.toString()} is an element of the ground domain`);
  // compose=False (SymPy's Groebner basis method) gives the same polynomial
  const result = minimalPolynomialOf(ex, x, dom);
  return opts.polys ? Poly.from(result, [x], { pure: xIn === undefined }) : collect(result, x);
}


/** c[0]*t**(n-1) + ... + c[n-1] (Horner). */
const horner = (cs: readonly Expr[], t: Expr): Expr => cs.reduce<Expr>((acc, c) => add(mul(acc, t), c), S.Zero);

/**
 * An element of Q(theta) written as c[0]*theta**(n-1) + ... + c[n-1] for a
 * primitive element theta (SymPy AlgebraicNumber(theta, coeffs)). The
 * polynomial is reduced modulo the minimal polynomial of theta.
 */
export class AlgebraicNumber {
  readonly root: Expr;
  readonly coeffList: readonly Expr[];
  constructor(root: ExprLike | AlgebraicNumber, coeffs: readonly ExprLike[] = [1, 0]) {
    const t = new Dummy('t');
    const cs = coeffs.map((c) => sympify(c));
    // an element of an element: the polynomials composed in the inner primitive element
    const inner = root instanceof AlgebraicNumber ? horner(root.coeffList, t) : t;
    this.root = root instanceof AlgebraicNumber ? root.root : sympify(root);
    const p = Poly.from(expandMul(horner(cs, inner)), [t]);
    // SymPy raises when the minimal polynomial cannot be found (NotAlgebraic for a transcendental element)
    this.coeffList = p.rem(Poly.from(minimalPolynomial(this.root, t), [t])).allCoeffs();
  }

  /** c[0]*theta**(n-1) + ... + c[n-1] with theta kept symbolic. */
  private asPolyExpr(): Expr {
    const n = this.coeffList.length;
    return add(...this.coeffList.map((c, i) => mul(c, pow(this.root, n - 1 - i))));
  }

  /** The value as an expression (SymPy as_expr). */
  asExpr(): Expr {
    return expandMul(this.asPolyExpr());
  }

  /** The value as an explicit root expression (SymPy to_root). */
  toRoot(): Expr {
    return this.asExpr();
  }

  /** The primitive element theta. */
  primitiveElement(): Expr {
    return this.root;
  }

  /** Coefficients in the primitive element, highest power first. */
  coeffs(): Expr[] {
    return [...this.coeffList];
  }

  evalf(n = 15): Expr {
    return this.asExpr().evalf(n);
  }
}
