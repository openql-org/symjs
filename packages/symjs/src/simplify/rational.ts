// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rational-function manipulation: fraction, together, cancel.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Float, Fn, impl, Mul, Pow, Rational, S, Sym, isNum } from '../core/nodes';
import { fromRational } from '../numeric/mpf';
import { add, couldExtractMinusSign, mul, pow, splitCoeff, sympify } from '../core/ops';
import { rebuild, xreplace } from '../core/traverse';
import { str } from '../printing/str';
import { divExact, mgcd } from '../polys/mpoly';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { UPoly, polyHooks } from '../polys/poly';
import { expandMul as expand } from './expand';
import { isNegative, isPositive } from '../core/assumptions';
import { at, defined, first } from '../core/guard';
import { decomposePower } from './exprtools';
import { asNumerDenom } from '../core/methods';

const negExponent = (x: Expr): boolean => {
  // SymPy fraction: exponents known to be negative go to the denominator
  if (isNegative(x) === true) return true;
  if (isPositive(x) === true) return false;
  const [c] = splitCoeff(x);
  return c.isNegative;
};

/** Split e into [numerator, denominator]. */
export function fraction(ex: ExprLike, opts: { exact?: boolean } = {}): [Expr, Expr] {
  const e = sympify(ex);
  const factors = e instanceof Mul ? e.args : [e];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const f of factors) {
    if (f instanceof Rational) {
      num.push(Rational.of(f.p));
      den.push(Rational.of(f.q));
    } else if (opts.exact && f instanceof Pow) {
      // SymPy exact=True: only exponents known to be negative, symbolic ones stay in the numerator
      const ex = f.exp;
      const negative = ex instanceof Rational ? ex.isNegative : isNegative(ex) === true;
      if (negative && ex instanceof Rational && ex.p === -1n && ex.q === 1n) den.push(f.base);
      else if (negative && ex.freeSymbols().size === 0) den.push(pow(f.base, mul(-1, ex)));
      else num.push(f);
    } else if (f instanceof Pow && negExponent(f.exp)) {
      den.push(pow(f.base, mul(-1, f.exp)));
    } else {
      num.push(f);
    }
  }
  if (opts.exact) {
    // SymPy Mul(*numer, evaluate=not exact): the factors as they are (2*(x + 1) stays)
    const raw = (xs: Expr[]): Expr => {
      const ys = xs.filter((y) => !(y instanceof Rational && y.p === 1n && y.q === 1n));
      return ys.length === 0 ? Rational.of(1n) : ys.length === 1 ? first(ys) : new Mul(ys);
    };
    return [raw(num), raw(den)];
  }
  return [mul(...num), mul(...den)];
}

/** Combine a sum of fractions over a common denominator (recursively). */
export function together(ex: ExprLike, opts: { deep?: boolean } = {}): Expr {
  const deep = opts.deep ?? false;
  // SymPy _together: gcd_terms over the recursively combined terms of every sum
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const isExp = e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
    if ((e instanceof Fn || isExp) && !deep) return e;
    // (registered by simplify/exprtools, which every entry point that loads this module loads)
    if (e instanceof Add) return defined(impl.gcdTermsOf?.(e.args.map(go)), 'impl.gcdTermsOf (simplify/exprtools)');
    if (e instanceof Pow) return pow(go(e.base), deep ? go(e.exp) : e.exp);
    const args = e.args.map(go);
    return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
  };
  return go(sympify(ex));
}

/**
 * Put e into the form p/q with expanded p, q and cancel common factors.
 * Polynomial GCD cancellation is performed for univariate rational functions.
 */
/** sqrt(g) times a sum: the square root of the gcd of the integer radicands of every term. */
function radicalContent(e: Expr): [Expr, Expr] | undefined {
  if (!(e instanceof Add)) return undefined;
  let g = 0n;
  const gcd = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcd(b, a % b));
  for (const t of e.args) {
    let radicand: bigint | undefined;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Pow && f.base instanceof Rational && f.base.q === 1n && f.exp instanceof Rational && f.exp.p === 1n && f.exp.q === 2n) {
        radicand = f.base.p;
        break;
      }
    }
    if (radicand === undefined) return undefined;
    g = gcd(g, radicand);
  }
  if (g <= 1n) return undefined;
  const sg = pow(Rational.of(g), Rational.of(1n, 2n));
  return [sg, expand(mul(e, pow(sg, -1)))];
}

function radicalContentRatio(n: Expr, d: Expr): Expr | undefined {
  const a = radicalContent(n);
  const b = radicalContent(d);
  if (!a || !b || a[1].key !== b[1].key) return undefined;
  // (registered by simplify/sqrtdenest, which every entry point that loads this module loads)
  return defined(impl.radsimp?.(mul(a[0], pow(b[0], -1))), 'impl.radsimp (simplify/sqrtdenest)');
}

/**
 * SymPy cancel: p/q with expanded p and q, their gcd cancelled in the polynomial ring over the
 * generators of p and q (symbols, functions, radicals, ...), normalised as SymPy's
 * PolyElement.cancel does: denominators cleared, p and q with integer (Gaussian) coefficients and
 * the leading coefficient of q (lex order of the generators) canonical.
 */
export function cancel(ex: ExprLike): Expr {
  const e = together(sympify(ex));
  let [n, d] = fraction(e);
  // SymPy as_numer_denom of sums (also inside products): the terms' denominators, also those of exp(-x) = 1/exp(x)
  if (n instanceof Add || n instanceof Mul) {
    const [n1, d1] = asNumerDenom(n);
    [n, d] = [n1, mul(d, d1)];
  }
  n = expand(n);
  d = expand(d);
  // (with Float coefficients SymPy works over RR or CC: 1.0*x + 1 = 1.0*x + 1.0, (1.0*x + 1)/3 = 0.333333333333333*x + 0.333333333333333)
  const exact = !(d instanceof Float) && floatsToRationals(n)[1] === 0;
  if (d instanceof Rational && d.isOne && exact) return n;
  // a common square root content: (sqrt(3) + sqrt(15)*A)/(sqrt(2) + sqrt(10)*A) = sqrt(6)/2
  const rc = radicalContentRatio(n, d);
  if (rc) return rc;
  if (isNum(d) && exact) return expand(mul(n, pow(d, -1)));
  // the generators in SymPy's order; those that are not symbols are replaced by dummies
  const gens = ratsimpGens([n, d]);
  const vars = gens.map((x) => (x instanceof Sym ? x : new Dummy('g')));
  const back = gens.map((x, i): [Expr, Expr] => [at(vars, i), x]).filter(([v, x]) => x !== v);
  let p = inGens(n, gens, vars);
  let q = inGens(d, gens, vars);
  const tn = coeffTable(p, vars);
  const td = coeffTable(q, vars);
  // (p and q are polynomials in the generators: their coefficients are rational or Gaussian
  // rational, SymPy's domains ZZ, QQ, ZZ_I, QQ_I, unless there are Floats, SymPy's RR or CC)
  if (!tn || !td) {
    const [fp, fq] = floatCancel(p, q, vars);
    return mul(xreplace(fp, back), pow(xreplace(fq, back), -1));
  }
  const [n1, d1] = gcdCancel(p, q, vars);
  const s = cancelScale(tn, td, defined(coeffTable(d1, vars), 'the coefficients of d / gcd'));
  [p, q] = [expand(mul(s, n1)), expand(mul(s, d1))];
  // SymPy canonical_unit: the leading coefficient of the denominator positive, or for a Gaussian
  // coefficient in the first quadrant
  const u = leadingUnit(q, vars);
  if (u !== undefined) [p, q] = [expand(mul(u, p)), expand(mul(u, q))];
  // SymPy as_expr: each Gaussian coefficient times its monomial, (1 + I)*x unexpanded
  [p, q] = [fromTable(defined(coeffTable(p, vars), 'p'), vars), fromTable(defined(coeffTable(q, vars), 'q'), vars)];
  [p, q] = [xreplace(p, back), xreplace(q, back)];
  return q instanceof Rational && q.isOne ? p : mul(p, pow(q, -1));
}

/**
 * SymPy mpmath MPContext.to_rational(x, limit=True) for a Float of precision prec: its exact
 * value, or the best rational approximation with a denominator up to 1/tolerance (tolerance =
 * 100*2**(1 - prec)).
 */
function floatToRational(f: Float, prec: number): Rational {
  const { man, exp } = f.mpf;
  const [p, q] = exp >= 0n ? [man << exp, 1n] : [man, 1n << -exp];
  const maxDenom = 2n ** BigInt(prec - 1) / 100n;
  if (q <= maxDenom) return Rational.of(p, q);
  let [p0, q0, p1, q1] = [0n, 1n, 1n, 0n];
  let [nn, dd] = [p, q];
  for (;;) {
    // floor division (the convergents of the continued fraction)
    const a = nn >= 0n ? nn / dd : -((-nn + dd - 1n) / dd);
    const q2 = q0 + a * q1;
    if (q2 > maxDenom) break;
    [p0, q0, p1, q1] = [p1, q1, p0 + a * p1, q2];
    [nn, dd] = [dd, nn - a * dd];
  }
  const k = (maxDenom - q0) / q1;
  const x = Rational.of(p, q);
  const b1 = Rational.of(p0 + k * p1, q0 + k * q1);
  const b2 = Rational.of(p1, q1);
  const dist = (b: Rational): Rational => {
    const t = Rational.of(b.p * x.q - x.p * b.q, b.q * x.q);
    return t.isNegative ? Rational.of(-t.p, t.q) : t;
  };
  const [e1, e2] = [dist(b1), dist(b2)];
  return e2.p * e1.q <= e1.p * e2.q ? b2 : b1;
}

/** e with its Float factors replaced by rationals, and the largest Float precision (0 without a Float). */
function floatsToRationals(e: Expr): [Expr, number] {
  const terms = e instanceof Add ? e.args : [e];
  let prec = 0;
  for (const f of terms.flatMap((t) => (t instanceof Mul ? t.args : [t]))) if (f instanceof Float) prec = Math.max(prec, f.prec);
  const conv = (f: Expr): Expr => (f instanceof Float ? floatToRational(f, prec) : f);
  return [add(...terms.map((t) => (t instanceof Mul ? mul(...t.args.map(conv)) : conv(t)))), prec];
}

/**
 * SymPy cancel over RR and CC: the Floats are converted to rationals (RR.get_exact, CC.get_exact =
 * QQ_I), p and q are the cofactors of the monic gcd over QQ or QQ_I, and every coefficient becomes
 * a Float (a + b*I) again: (2.0*x + 1)/(4*x + 2.0) = 2.0/4.0 = 0.5. Over RR the leading coefficient
 * of q is made positive (RR.canonical_unit); CC has no canonical unit, and SymPy's signsimp before
 * cancel negates p and q when q could extract a minus sign.
 */
function floatCancel(n: Expr, d: Expr, vars: readonly Expr[]): [Expr, Expr] {
  const [nq, pn] = floatsToRationals(n);
  const [dq, pd] = floatsToRationals(d);
  // (the Floats are the only factors of the terms that are not generators or rationals)
  const tn = defined(coeffTable(nq, vars), 'the coefficients of n');
  const td = defined(coeffTable(dq, vars), 'the coefficients of d');
  const complex = [...tn.values(), ...td.values()].some(([, c]) => c[1] !== 0n);
  const prec = Math.max(pn, pd);
  let g = gcdOf(nq, dq, vars);
  let [p, q] = [nq, dq];
  if (g !== undefined) {
    const [a, b, den] = lexLeading(defined(coeffTable(g, vars), 'the coefficients of the gcd'));
    g = expand(mul(gqExpr([den * a, -den * b, a * a + b * b]), g));
    [p, q] = [defined(divExact(nq, g, vars), 'n / gcd'), defined(divExact(dq, g, vars), 'd / gcd')];
  }
  const flip = complex ? couldExtractMinusSign(d) : lexLeading(defined(coeffTable(q, vars), 'q'))[0] < 0n;
  if (flip) [p, q] = [expand(mul(-1, p)), expand(mul(-1, q))];
  const toFloat = (a: bigint, den: bigint): Float => new Float(fromRational(a, den, prec), prec);
  // SymPy CC.to_sympy: Float(re) + I*Float(im), the zero parts left out
  const coeff = ([a, b, den]: GQ): Expr => (b === 0n ? toFloat(a, den) : a === 0n ? mul(toFloat(b, den), S.I) : add(toFloat(a, den), mul(toFloat(b, den), S.I)));
  const asFloats = (e: Expr): Expr => add(...[...defined(coeffTable(e, vars), 'the coefficients').values()].map(([m, c]) => mul(coeff(c), ...m.map((k, i) => pow(at(vars, i), k)))));
  return [asFloats(p), asFloats(q)];
}

/** The gcd (up to a constant factor) of the polynomials n and d in vars over Q(i), undefined when it is constant. */
function gcdOf(n: Expr, d: Expr, vars: readonly Expr[]): Expr | undefined {
  if (vars.length === 1) {
    const x = first(vars);
    const pn = UPoly.fromExpr(n, x);
    const pd = UPoly.fromExpr(d, x);
    if (pn && pd) {
      const g = pn.gcd(pd);
      return g.degree > 0 ? g.toExpr(x) : undefined;
    }
  }
  const g = mgcd(n, d, vars);
  return vars.some((v) => g.has(v)) ? g : undefined;
}

/** n/g and d/g for the polynomial gcd g of the polynomials n and d in vars. */
function gcdCancel(n: Expr, d: Expr, vars: readonly Expr[]): [Expr, Expr] {
  let g = gcdOf(n, d, vars);
  if (g === undefined) return [n, d];
  // a rational leading coefficient, so that the exact division stays in Q(i)[vars]
  const [a, b] = lexLeading(defined(coeffTable(g, vars), 'the coefficients of the gcd'));
  if (b !== 0n) g = expand(mul(gqExpr([a, -b, 1n]), g));
  return [defined(divExact(n, g, vars), 'n / gcd'), defined(divExact(d, g, vars), 'd / gcd')];
}

/** A Gaussian rational (a + b*I)/den with den > 0. */
type GQ = readonly [bigint, bigint, bigint];
/** A Gaussian integer a + b*I. */
type GI = readonly [bigint, bigint];

const babs = (a: bigint): bigint => (a < 0n ? -a : a);
const gqExpr = ([a, b, den]: GQ): Expr => add(Rational.of(a, den), mul(Rational.of(b, den), S.I));
const giMul = ([a, b]: GI, [c, d]: GI): GI => [a * c - b * d, a * d + b * c];
/** round(n/d) for d > 0. */
const roundDiv = (n: bigint, d: bigint): bigint => {
  const q = (2n * n + d) / (2n * d);
  return 2n * n + d < 0n && (2n * n + d) % (2n * d) !== 0n ? q - 1n : q;
};
/** gcd of Gaussian integers, in the first quadrant (re > 0, im >= 0) unless it is 0. */
function giGcd(x: GI, y: GI): GI {
  const [a, b] = giGcdAny(x, y);
  if (a > 0n && b >= 0n) return [a, b];
  if (a <= 0n && b > 0n) return [b, -a];
  if (a < 0n && b <= 0n) return [-a, -b];
  return [-b, a];
}
function giGcdAny(x: GI, y: GI): GI {
  let [u, v] = [x, y];
  while (v[0] !== 0n || v[1] !== 0n) {
    const nv = v[0] * v[0] + v[1] * v[1];
    const [re, im] = giMul(u, [v[0], -v[1]]);
    const qv = giMul([roundDiv(re, nv), roundDiv(im, nv)], v);
    [u, v] = [v, [u[0] - qv[0], u[1] - qv[1]]];
  }
  return u;
}

/** The coefficients of the monomials of a polynomial in vars (undefined when e is not one over Q(i)). */
function coeffTable(e: Expr, vars: readonly Expr[]): Map<string, [number[], GQ]> | undefined {
  const out = new Map<string, [number[], GQ]>();
  for (const t of e instanceof Add ? e.args : [e]) {
    const m = vars.map(() => 0);
    let c: GQ = [1n, 0n, 1n];
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) c = [c[0] * f.p, c[1] * f.p, c[2] * f.q];
      else if (f instanceof Constant && f.name === 'I') c = [-c[1], c[0], c[2]];
      else {
        const [b, k] = decomposePower(f);
        const i = vars.findIndex((v) => v.key === b.key);
        if (i < 0 || k < 0) return undefined;
        m[i] = at(m, i) + k;
      }
    }
    const key = m.join(',');
    const cur = out.get(key)?.[1];
    out.set(key, [m, cur ? [cur[0] * c[2] + c[0] * cur[2], cur[1] * c[2] + c[1] * cur[2], cur[2] * c[2]] : c]);
  }
  return out;
}

/** The polynomial of a coefficient table. */
const fromTable = (t: Map<string, [number[], GQ]>, vars: readonly Expr[]): Expr =>
  add(...[...t.values()].map(([m, c]) => mul(gqExpr(c), ...m.map((k, i) => pow(at(vars, i), k)))));

/** The coefficient of the lex-leading monomial, as a Gaussian integer times a positive rational. */
function lexLeading(t: Map<string, [number[], GQ]>): GQ {
  let best: [number[], GQ] | undefined;
  for (const mc of t.values()) if (best === undefined || lexGreater(mc[0], best[0])) best = mc;
  return defined(best, 'a term of the polynomial')[1];
}

/** [lcm of the denominators, content of the cleared integer polynomial] of a nonzero polynomial. */
function clearDenoms(t: Map<string, [number[], GQ]>): [bigint, GI] {
  let den = 1n;
  for (const [, [a, b, q]] of t.values()) {
    const g = igcd(igcd(babs(a), babs(b)), q);
    den = ilcm(den, q / g);
  }
  let cont: GI = [0n, 0n];
  for (const [, [a, b, q]] of t.values()) cont = giGcd(cont, [(a * den) / q, (b * den) / q]);
  return [den, cont];
}

/**
 * The factor s that turns n1/d1 (n/d with their gcd cancelled) into SymPy's pair p/q: SymPy clears
 * the denominators (cq*n, cp*d), takes the cofactors of the integer polynomials (whose gcd holds the
 * gcd of their contents), and multiplies them by cp and cq without their common factor. So
 * q = cont(cp*d)/gcd(cont(cq*n), cont(cp*d)) * cq/gcd(cp, cq) * d1/cont(d1), up to a unit.
 */
function cancelScale(tn: Map<string, [number[], GQ]>, td: Map<string, [number[], GQ]>, t1: Map<string, [number[], GQ]>): Expr {
  const [cq, contN] = clearDenoms(tn);
  const [cp, contD] = clearDenoms(td);
  const [den1, cont1] = clearDenoms(t1);
  const k = (cq / igcd(cq, cp)) * den1;
  const num: GI = [contD[0] * k, contD[1] * k];
  const den = giMul(giGcd(contN, contD), cont1);
  const [re, im] = giMul(num, [den[0], -den[1]]);
  return gqExpr([re, im, den[0] * den[0] + den[1] * den[1]]);
}

/** The expanded polynomial e with each generator power gens[i]**k written as dummies[i]**k. */
function inGens(e: Expr, gens: readonly Expr[], dummies: readonly Expr[]): Expr {
  return add(
    ...(e instanceof Add ? e.args : [e]).map((t) =>
      mul(
        ...(t instanceof Mul ? t.args : [t]).map((f) => {
          const [b, k] = decomposePower(f);
          const i = gens.findIndex((g) => g.key === b.key);
          return i < 0 ? f : pow(at(dummies, i), k);
        }),
      ),
    ),
  );
}

/**
 * The unit (-1, I or -I) that moves the coefficient of the lex-leading term of the expanded
 * polynomial d into the first quadrant (re > 0, im >= 0); undefined when it is there already.
 */
function leadingUnit(d: Expr, gens: readonly Expr[]): Expr | undefined {
  // the coefficients of the monomials (terms that differ by I share one)
  const coeffs = new Map<string, [number[], Expr]>();
  for (const t of d instanceof Add ? d.args : [d]) {
    const m = gens.map(() => 0);
    let c: Expr = Rational.of(1n);
    for (const f of t instanceof Mul ? t.args : [t]) {
      const [b, k] = decomposePower(f);
      const i = gens.findIndex((g) => g.key === b.key);
      if (i < 0) c = mul(c, f);
      else m[i] = at(m, i) + k;
    }
    const cur = coeffs.get(m.join(','));
    coeffs.set(m.join(','), [m, cur ? add(cur[1], c) : c]);
  }
  let best: [number[], Expr] | undefined;
  for (const mc of coeffs.values()) if (best === undefined || lexGreater(mc[0], best[0])) best = mc;
  const { re, im } = defined(best, 'a term of the denominator')[1].toComplex();
  // (the coefficient is a nonzero number: a product of numbers and I)
  if (re > 0 && im >= 0) return undefined;
  if (re <= 0 && im > 0) return mul(-1, S.I);
  if (re < 0 && im <= 0) return S.NegOne;
  return S.I;
}

/** a > b in lex order (for distinct monomials a and b). */
const lexGreater = (a: readonly number[], b: readonly number[]): boolean =>
  a.reduce<boolean | undefined>((r, v, i) => r ?? (v !== at(b, i) ? v > at(b, i) : undefined), undefined) === true;

impl.fraction = (e) => fraction(e);

/** SymPy ratsimp: polynomial part plus a cancelled remainder over a single denominator. */
export function ratsimp(ex: ExprLike): Expr {
  const c = cancel(sympify(ex));
  const [f, g] = fraction(c);
  if (!g.freeSymbols().size) return c;
  // the generators of the polynomials in SymPy's order (symbols, functions, radicals, ...): those
  // that are not symbols are divided as dummies
  const [fe, ge] = [expand(f), expand(g)];
  const gens = ratsimpGens([fe, ge]);
  const dummies = gens.map((x) => (x instanceof Sym ? x : new Dummy('g')));
  const back = gens.map((x, i): [Expr, Expr] => [at(dummies, i), x]).filter(([d, x]) => x !== d);
  // multivariate division of f by g in lex order (registered by polys/groebner, which the
  // simplify entry point and the root entry point, the ones that export ratsimp, load)
  const [q, r] = defined(impl.polyReduce?.(inGens(fe, gens, dummies), inGens(ge, gens, dummies), dummies), 'impl.polyReduce (polys/groebner)').map((e) => xreplace(e, back));
  return add(defined(q), cancel(mul(defined(r), pow(g, -1))));
}

// SymPy _sort_gens: single letters in the order x, y, z, p..w, a..o, then everything else by name
const GENS_ORDER: Record<string, number> = {
  a: 301, b: 302, c: 303, d: 304, e: 305, f: 306, g: 307, h: 308, i: 309, j: 310, k: 311, l: 312, m: 313,
  n: 314, o: 315, p: 216, q: 217, r: 218, s: 219, t: 220, u: 221, v: 222, w: 223, x: 124, y: 125, z: 126,
};
const genKey = (g: Expr): [number, string, number] => {
  // (the pattern matches every string)
  const m = defined(/^(.*?)(\d*)$/.exec(str(g)), 'generator name');
  const name = at(m, 1);
  const digits = at(m, 2);
  return [GENS_ORDER[name] ?? 1000, name, digits ? Number(digits) : 0];
};

/** The generators of expanded polynomials (SymPy _dict_from_expr_no_gens), sorted as SymPy does. */
function ratsimpGens(es: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  for (const e of es) {
    for (const t of e instanceof Add ? e.args : [e]) {
      for (const f of t instanceof Mul ? t.args : [t]) {
        if (isNum(f) || (f instanceof Constant && f.name === 'I')) continue;
        const b = decomposePower(f)[0];
        gens.set(b.key, b);
      }
    }
  }
  return [...gens.values()].sort((a, b) => {
    const [a0, a1, a2] = genKey(a);
    const [b0, b1, b2] = genKey(b);
    return a0 !== b0 ? a0 - b0 : a1 !== b1 ? (a1 < b1 ? -1 : 1) : a2 - b2;
  });
}

polyHooks.cancel = (e) => cancel(e);
