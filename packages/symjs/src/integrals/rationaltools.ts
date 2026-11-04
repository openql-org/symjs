// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/rationaltools.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Integration of rational functions (SymPy ratint): Horowitz-Ostrogradsky
 * reduction for the rational part and the Lazard-Rioboo-Trager algorithm for
 * the logarithmic part, written with real logarithms and arctangents when the
 * integrand is real (SymPy log_to_real).
 */

import { isReal } from '../core/assumptions';
import { defined } from '../core/guard';
import { Lambda } from '../core/lambda';
import { asNumerDenom, atoms, primitive } from '../core/methods';
import type { Expr } from '../core/nodes';
import { Add, Dummy, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { add, mul, pow } from '../core/ops';
import { xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { atan, log } from '../functions/elementary/elementary';
import { linsolve } from '../matrices/linsys';
import { roots } from '../polys/poly';
import { RootSum } from '../polys/rootsum';
import { Poly, factorListExpr, resultant, sortGens } from '../polys/sympoly';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';

/** The largest degree of the denominator of the logarithmic part that is integrated. */
const MAX_LOG_DEGREE = 4;

/** Poly in one generator. */
const P = (e: Expr, x: Expr): Poly => Poly.from(e, [x]);

/** The coefficients are rational numbers. */
const rationalPoly = (p: Poly): boolean => p.coeffs().every((c) => c instanceof Rational);

/** The numeric coefficient of a leading coefficient is negative (SymPy EX is_negative). */
const negativeLC = (p: Poly): boolean => {
  const c = p.LC();
  const k = c instanceof Mul ? c.args[0] : c;
  return k instanceof Rational && k.isNegative;
};

/**
 * SymPy Poly.cancel(f, g): the common factor removed, as (coefficient, p, q)
 * with p/q*coefficient = f/g. Over the rationals the denominators are cleared
 * and the integer content goes into the coefficient.
 */
function polyCancel(f: Poly, g: Poly): [Expr, Poly, Poly] {
  const x = defined(f.gens[0], 'generator');
  let cp: Expr = S.One;
  let cq: Expr = S.One;
  let F = f;
  let G = g;
  if (rationalPoly(f) && rationalPoly(g)) {
    // the denominators are cleared and the gcd is taken over the integers, its content included
    const [dq, f1] = f.clearDenoms();
    const [dp, g1] = g.clearDenoms();
    const h = f1.gcd(g1);
    F = f1.exquo(h);
    G = g1.exquo(h);
    [cp, cq] = asNumerDenom(mul(dp, pow(dq, -1)));
  } else {
    // over a field of parameters the gcd is taken monic (constants are units)
    const h = f.gcd(g).monic();
    F = P(cancel(mul(f.asExpr(), pow(h.asExpr(), -1))), x);
    G = P(cancel(mul(g.asExpr(), pow(h.asExpr(), -1))), x);
  }
  const pNeg = negativeLC(F);
  const qNeg = negativeLC(G);
  if (pNeg && qNeg) {
    F = F.neg();
    G = G.neg();
  } else if (pNeg) {
    cp = mul(-1, cp);
    F = F.neg();
  } else if (qNeg) {
    cp = mul(-1, cp);
    G = G.neg();
  }
  return [mul(cp, pow(cq, -1)), F, G];
}

/**
 * The rational part of the integral of f/g (SymPy ratint_ratpart,
 * Horowitz-Ostrogradsky): [A/u, B/v] with g = u*v, u = gcd(g, g') and
 * integral(f/g) = A/u + integral(B/v).
 *
 * @example
 * ratintRatpart(Poly.from(1, [x]), Poly.from('x**2 + 2*x + 1', [x]), x)  // [-1/(x + 1), 0]
 */
export function ratintRatpart(f: Poly, g: Poly, x: Sym): [Expr, Expr] {
  // u = gcd(g, g') taken monic, v = g/u (by cancel: exact division of polynomials with parameters is slow here)
  const u = P(cancel(g.gcd(g.diff(x)).monic().asExpr()), x);
  const v = P(cancel(mul(g.asExpr(), pow(u.asExpr(), -1))), x);
  const n = u.degree();
  const m = v.degree();
  const As = Array.from({ length: n }, (_, i) => new Dummy(`a${n - i}`));
  const Bs = Array.from({ length: m }, (_, i) => new Dummy(`b${m - i}`));
  const A = add(...As.map((c, i) => mul(c, pow(x, n - 1 - i))));
  const B = add(...Bs.map((c, i) => mul(c, pow(x, m - 1 - i))));
  const ue = u.asExpr();
  const ve = v.asExpr();
  const uv = P(expand(mul(diff(ue, x), ve)), x).quo(u).asExpr();
  const H = expand(add(f.asExpr(), mul(-1, diff(A, x), ve), mul(A, uv), mul(-1, B, ue)));
  const unknowns = [...As, ...Bs];
  // the system has exactly one solution (Horowitz-Ostrogradsky)
  const sol = defined(linsolve(P(H, x).coeffs(), unknowns), 'ratint_ratpart solution');
  const rep = unknowns.map((c, i): [Expr, Expr] => [c, defined(sol[i], 'unknown')]);
  // SymPy cancel(A/u, x): numerator and denominator as polynomials in x
  const inX = (e: Expr): Expr => {
    const [n, d] = asNumerDenom(cancel(e));
    return mul(P(n, x).asExpr(), pow(P(d, x).asExpr(), -1));
  };
  return [inX(mul(xreplace(A, rep), pow(ue, -1))), inX(mul(xreplace(B, rep), pow(ve, -1)))];
}

/**
 * The logarithmic part of the integral of f/g for a square-free g with
 * deg f < deg g (SymPy ratint_logpart, Lazard-Rioboo-Trager): pairs [s, q]
 * with integral(f/g) = sum over the roots a of q(t) of a*log(s(x, a)).
 *
 * @example
 * ratintLogpart(Poly.from(1, [x]), Poly.from('x**2 - 2', [x]), x, t)  // [[x**2 - 2*t*x... ]]
 */
export function ratintLogpart(f: Poly, g: Poly, x: Sym, t: Sym): [Poly, Poly][] {
  // f = c*g': the resultant is a constant times (t - c)**deg(g), whose only factor gives c*log(g); the
  // subresultants are not needed (they are slow for coefficients in parameters)
  const dg = g.diff(x);
  if (f.degree() === dg.degree()) {
    const c = cancel(mul(f.LC(), pow(dg.LC(), -1)));
    if (P(expand(add(f.asExpr(), mul(-1, c, dg.asExpr()))), x).isZero) {
      // (SymPy's factor is primitive over the integers, and monic over the expressions of parameters)
      const q = P(add(t, mul(-1, c)), t);
      return [[g, rationalPoly(f) && rationalPoly(g) ? q.primitive()[1] : q]];
    }
  }
  const a = g;
  const b = P(expand(add(f.asExpr(), mul(-1, dg.asExpr(), t))), x);
  const res = P(resultant(a.asExpr(), b.asExpr(), x), t);
  const Rmap = new Map<number, Poly>();
  // (the coefficients of the sequence are polynomials in t: their quotients are cancelled)
  for (const r of a.subresultants(b)) Rmap.set(r.degree(), P(add(...r.terms().map(([[e = 0], c]) => mul(cancel(c), pow(x, e)))), x));
  const H: [Poly, Poly][] = [];
  for (const [q0, i] of res.sqfList()[1]) {
    const q = q0.primitive()[1];
    // (i = deg(g) means a single root c of multiplicity deg(g), so that f - c*g' vanishes at every root of g
    // and f = c*g', which was handled above)
    let h = defined(Rmap.get(i), 'subresultant of degree i');
    const hlc = P(h.LC(), t);
    for (const [s, j] of hlc.sqfListAll(true)[1]) {
      const d = pow(s.gcd(q).asExpr(), j);
      h = P(cancel(mul(h.asExpr(), pow(d, -1))), x);
    }
    const inv = hlc.toField().invert(q);
    // the leading coefficient becomes 1, the others are reduced modulo q
    const reduced = h.terms().map(([[e = 0], c], k) => mul(k === 0 ? S.One : P(expand(mul(inv.asExpr(), c)), t).rem(q).asExpr(), pow(x, e)));
    h = P(add(...reduced), x);
    H.push([h, q]);
  }
  return H;
}

/**
 * Convert a complex logarithm to real arctangents (SymPy log_to_atan):
 * i*log((f + i*g)/(f - i*g)) as a sum of 2*atan terms with polynomial
 * arguments.
 *
 * @example
 * logToAtan(Poly.from('x', [x]), Poly.from(1, [x]))  // 2*atan(x)
 */
export function logToAtan(f0: Poly, g0: Poly): Expr {
  let [f, g] = [f0, g0];
  if (f.degree() < g.degree()) [f, g] = [g.neg(), f];
  f = f.toField();
  g = g.toField();
  const [p, q] = f.div(g);
  if (q.isZero) return mul(2, atan(p.asExpr()));
  const [s, t, h] = g.gcdex(f.neg());
  const u = f.mul(s).add(g.mul(t)).quo(h);
  return add(mul(2, atan(u.asExpr())), logToAtan(s, t));
}

/**
 * The real roots of a polynomial (SymPy _get_real_roots); NotImplementedError
 * when some are not found (SymPy None).
 */
function realRoots(f: Poly, x: Sym): Expr[] {
  // the roots of irreducible factors of degree 3 or more other than binomials are not written in radicals here
  // (Cardano's formulas: their signs cannot be decided); roots raises for those of degree 5 or more
  for (const [g] of factorListExpr(f.asExpr())[1]) {
    const p = P(g, x);
    if (p.degree() > 2 && p.terms().length > 2) throw new NotImplementedError('real roots of an irreducible factor of degree 3 or more');
  }
  // the other factors have all their roots in radicals, whose realness is decided (SymPy compares their
  // number with count_roots)
  const rs: Expr[] = [];
  for (const r of roots(f.asExpr(), x)) if (isReal(r) === true && !rs.some((s) => s.key === r.key)) rs.push(r);
  return rs;
}

/** Real and imaginary parts of an expanded expression linear in I. */
function splitI(e: Expr): [Expr, Expr] {
  const re: Expr[] = [];
  const im: Expr[] = [];
  for (const term of e instanceof Add ? e.args : [e]) {
    const fs = term instanceof Mul ? term.args : [term];
    if (fs.some((f) => f.key === S.I.key)) im.push(mul(...fs.filter((f) => f.key !== S.I.key)));
    else re.push(term);
  }
  return [add(...re), add(...im)];
}

/**
 * The sum over the roots a of q of a*log(h(x, a)) with real functions
 * (SymPy log_to_real), or undefined when the real roots cannot be found.
 *
 * @example
 * logToReal(Poly.from('x - t', [x]), Poly.from('t**2 + 1', [t]), x, t)  // ...
 */
export function logToReal(h: Poly, q: Poly, x: Sym, t: Sym): Expr | undefined {
  try {
    return logToRealInner(h, q, x, t);
  } catch {
    // realRoots raises NotImplementedError when real roots are not found (SymPy None)
    return undefined;
  }
}

function logToRealInner(h: Poly, q: Poly, x: Sym, t: Sym): Expr {
  const u = new Dummy('u');
  const v = new Dummy('v');
  const tv = add(u, mul(S.I, v));
  const [a, b] = splitI(expand(xreplace(h.asExpr(), [[t, tv]])));
  const [c, d0] = splitI(expand(xreplace(q.asExpr(), [[t, tv]])));
  const result: Expr[] = [];
  for (const ru of realRoots(P(resultant(c, d0, v), u), u)) {
    let d = d0;
    let C = P(expand(xreplace(c, [[u, ru]])), v);
    if (C.isZero) {
      C = P(expand(xreplace(d, [[u, ru]])), v);
      d = S.Zero;
    }
    // the roots +-r_v once each, without 0
    const paired: Expr[] = [];
    for (const rv0 of realRoots(C, v)) {
      const rv = couldExtractMinusSign(rv0) ? mul(-1, rv0) : rv0;
      if (!(rv instanceof Rational && rv.isZero) && !paired.some((p) => p.key === rv.key)) paired.push(rv);
    }
    for (const rv of paired) {
      const D = expand(xreplace(d, [[u, ru], [v, rv]]));
      if (Math.abs(D.toNumber()) > 1e-12) continue;
      const A = P(expand(xreplace(a, [[u, ru], [v, rv]])), x);
      const B = P(expand(xreplace(b, [[u, ru], [v, rv]])), x);
      const AB = A.mul(A).add(B.mul(B)).asExpr();
      result.push(add(mul(ru, log(AB)), mul(rv, logToAtan(A, B))));
    }
  }
  for (const r of realRoots(q, t)) result.push(mul(r, log(expand(xreplace(h.asExpr(), [[t, r]])))));
  return add(...result);
}

/** A negative number or a product with a negative coefficient (SymPy is_negative or could_extract_minus_sign). */
function couldExtractMinusSign(e: Expr): boolean {
  if (isReal(e) === true && e.freeSymbols().size === 0 && e.toNumber() < 0) return true;
  const k = e instanceof Mul ? e.args[0] : e;
  return k instanceof Rational && k.isNegative;
}

/**
 * The integral of a rational function f in x (SymPy ratint), or undefined
 * when f is not a rational function of x or the roots of the logarithmic
 * part cannot be written.
 *
 * @example
 * ratint(parse('1/(x**2 + 2*a*x + a**2)'), x)  // -1/(a + x)
 */
export function ratint(f: Expr, x: Sym): Expr | undefined {
  const [pe, qe] = asNumerDenom(f);
  let p0: Poly;
  let q0: Poly;
  try {
    p0 = P(pe, x);
    q0 = P(qe, x);
  } catch {
    // not polynomials in x (Poly.from raises PolificationFailed)
    return undefined;
  }
  const [coeff, p1, q] = polyCancel(p0, q0);
  const [poly, p] = p1.div(q);
  let result = poly.integrate(x).asExpr();
  if (p.isZero) return mul(coeff, result);
  const [g, h] = ratintRatpart(p, q, x);
  const [Pe, Qe] = asNumerDenom(h);
  const Q = P(Qe, x);
  const [q2, r] = P(Pe, x).div(Q);
  result = add(result, g, q2.integrate(x).asExpr());
  if (!r.isZero) {
    // the resultant in t is computed by pseudo-remainders of polynomials in t, whose size explodes
    // for large denominators: those are left (SymPy computes them over QQ[t])
    if (Q.degree() > MAX_LOG_DEGREE) return undefined;
    const t = new Dummy('t');
    const L = ratintLogpart(r, Q, x, t);
    const real = atoms(f).every((e) => e.key === x.key || isReal(e) === true);
    const eps: Expr[] = [];
    for (const [h0, q1] of L) {
      // the content over the coefficients: a rational number, or 1 for coefficients in t or in parameters
      const hh = h0.asExpr().has(t) ? h0 : P(primitive(h0.asExpr())[1], x);
      const R = real ? logToReal(hh, q1, x, t) : rootSumQuadratic(q1, t, hh);
      eps.push(R ?? RootSum(q1.asExpr(), t, Lambda(t, mul(t, log(hh.asExpr())))));
    }
    result = add(result, ...eps);
  }
  return mul(coeff, result);
}

/**
 * SymPy preprocess_roots for coefficients that are monomials in parameters:
 * [c, q1] with the roots of q equal to c times the roots of q1, e.g.
 * 4*a**2*t**2 - 1 -> [1/a, 4*t**2 - 1].
 */
function preprocessRoots(q: Poly, t: Sym): [Expr, Poly] {
  let coeff: Expr = S.One;
  let poly = q;
  const isTerm = (c: Expr) => (c instanceof Mul ? c.args : [c]).every((f) => f instanceof Rational || f instanceof Sym || (f instanceof Pow && f.base instanceof Sym && f.exp instanceof Rational && f.exp.isInteger && f.exp.isPositive));
  if (!q.coeffs().every(isTerm)) return [coeff, poly];
  const gens = sortGens([...q.asExpr().freeSymbols()].filter((g) => g.key !== t.key));
  for (const gen of gens) {
    const inj = Poly.from(poly.asExpr(), [t, gen]);
    const base = inj.monoms().map((m) => defined(m[0], 'degree'));
    let strip = inj.monoms().map((m) => defined(m[1], 'degree'));
    let reverse = false;
    if (defined(strip[0], 'first') < defined(strip[strip.length - 1], 'last')) {
      strip = [...strip].reverse();
      reverse = true;
    }
    // the exponents of gen are ratio times those of t (pairs of zeros aside)
    const pairs = base.map((a, i): [number, number] => [a, defined(strip[i], 'exponent')]).filter(([a, b]) => a || b);
    const ratios = new Set(pairs.map(([a, b]) => (a && b && b % a === 0 ? b / a : NaN)));
    if (ratios.size !== 1 || ratios.has(NaN)) continue;
    let ratio = defined([...ratios][0], 'ratio');
    if (reverse) ratio = -ratio;
    poly = P(xreplace(poly.asExpr(), [[gen, S.One]]), t);
    coeff = mul(coeff, pow(gen, -ratio));
  }
  return [coeff, poly];
}

/**
 * SymPy RootSum(q, Lambda(t, t*log(h)), quadratic=True) for q with
 * linear and quadratic factors: the sum of r*log(h(r)) over the roots r of
 * q, with the scale of the roots taken out; undefined for factors of higher
 * degree.
 */
function rootSumQuadratic(q: Poly, t: Sym, h: Poly): Expr | undefined {
  const [scale, q1] = preprocessRoots(q, t);
  const he = h.asExpr();
  const terms: Expr[] = [];
  for (const [ge, k] of factorListExpr(q1.asExpr())[1]) {
    if (P(ge, t).degree() > 2) return undefined;
    terms.push(mul(k, add(...roots(ge, t).map((r) => mul(r, log(xreplace(he, [[t, mul(scale, r)]])))))));
  }
  return mul(scale, add(...terms));
}

/**
 * n/d with the common factor of the polynomials n and d in x removed (SymPy
 * Poly.cancel(include=True) as risch_integrate applies it), as
 * coefficient*p/q.
 */
export function cancelFraction(n: Expr, d: Expr, x: Sym): Expr {
  const [c, p, q] = polyCancel(P(n, x), P(d, x));
  return mul(c, p.asExpr(), pow(q.asExpr(), -1));
}

/** The rational function f of x is one (SymPy is_rational_function), as polynomials in x over its coefficients. */
export function isRationalIn(f: Expr, x: Sym): boolean {
  const [n, d] = asNumerDenom(f);
  try {
    P(n, x);
    P(d, x);
    return true;
  } catch {
    // (Poly.from raises PolificationFailed)
    return false;
  }
}

