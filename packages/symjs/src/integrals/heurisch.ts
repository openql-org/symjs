// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/heurisch.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file SymPy's heuristic Risch algorithm (heurisch, heurisch_wrapper,
 * components), and the case of heurisch for rational
 * functions of sin(u) and cos(u), u = a*x + b: heurisch rewrites them in
 * tan(u/2) (rewrite=True) and finds an antiderivative that is rational in x
 * and tan(u/2) plus logarithms and arctangents. Here the rational function of
 * t = tan(u/2) is integrated instead and written in heurisch's final form
 * (cancel(F).expand() without the terms free of x).
 */

import type { Expr, Sym } from '../core/nodes';
import { Add, Constant, Derivative, Dummy, Fn, Mul, Pow, Rational, S, UndefFn, impl } from '../core/nodes';
import { add, couldExtractMinusSign, mul, pow, sqrt } from '../core/ops';
import { mapBottomUp, some, subs, xreplace } from '../core/traverse';
import { and, or } from '../core/boolalg';
import { Eq, Ne, piecewise } from '../core/logic';
import { ordered } from '../core/match';
import { asIndependent, asNumerDenom, isPolynomial, isRationalFunction } from '../core/methods';
import { asin, atan, fn, log, tan, tanh } from '../functions/elementary/elementary';
import { isPositive, isNegative } from '../core/assumptions';
import { asinh } from '../functions/elementary/trigext';
import { erf, erfi } from '../functions/special/special';
import { at, defined } from '../core/guard';
import { polyCoefficients, roots } from '../polys/poly';
import { Poly, factorListExpr } from '../polys/sympoly';
import { itermonomials } from '../polys/monomial';
import { linsolve } from '../matrices/linsys';
import { diff } from '../calculus/diff';
import { compareKeys, sortKey } from '../printing/sortkey';
import { rewrite } from '../simplify/rewrite';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { solve } from '../solvers/solve';
import { permutations } from '../utilities/itertools';
import { isDiracDelta, isHeaviside } from './transforms/delta';

/**
 * The integral of a rational function f of sin(u) and cos(u) with u = a*x + b
 * (a a nonzero rational number, b free of x) by the substitution
 * t = tan(u/2); integrate integrates the rational function of t. Undefined
 * when f has another form or the rational function is not integrated.
 *
 * @example
 * heurischTrig(parse('1/(sin(y) + 1)'), y, integrate)  // -2/(tan(y/2) + 1)
 */
export function heurischTrig(f: Expr, x: Sym, integrate: (g: Expr, t: Sym) => Expr | undefined): Expr | undefined {
  // the arguments of sin and cos, and whether x appears elsewhere
  const args = new Map<string, Expr>();
  const scan = (e: Expr): boolean => {
    if (e instanceof Fn && (e.name === 'sin' || e.name === 'cos')) {
      args.set(at(e.args, 0).key, at(e.args, 0));
      return true;
    }
    return e.key !== x.key && e.args.every(scan);
  };
  if (!scan(f) || args.size !== 1) return undefined;
  const u = defined([...args.values()][0], 'argument');
  const pc = polyCoefficients(u, x);
  const a = pc?.get(1);
  if (pc === undefined || !(a instanceof Rational) || [...pc.keys()].some((k) => k > 1)) return undefined;
  const t = new Dummy('t');
  const den = add(1, pow(t, 2));
  const arg = u;
  const g = mapBottomUp(f, (e) => {
    if (!(e instanceof Fn) || e.args[0]?.key !== arg.key) return e;
    return e.name === 'sin' ? mul(2, t, pow(den, -1)) : mul(add(1, mul(-1, pow(t, 2))), pow(den, -1));
  });
  // dx = 2/(a*(1 + t**2)) dt
  const G = integrate(cancel(mul(g, 2, pow(mul(a, den), -1))), t);
  if (G === undefined) return undefined;
  // atan(tan(u/2)) is u/2 up to a constant: heurisch finds the polynomial a*x/2 instead
  const half = tan(expand(mul(S.Half, u)));
  const F = xreplace(
    mapBottomUp(G, (e) => (e.key === atan(t).key ? mul(a, x, S.Half) : e)),
    [[t, half]],
  );
  const r = expand(cancel(F));
  return r instanceof Add ? add(...r.args.filter((e) => e.has(x))) : r;
}

// ---- the heuristic Risch algorithm ------------------------------------------------------------

const isExpPow = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** The functional components of f (SymPy components) by key, added to `out`. */
function addComponents(f: Expr, x: Sym, out: Map<string, Expr>): void {
  if (!f.has(x)) return;
  if (f.key === x.key) {
    out.set(f.key, f);
  } else if (f instanceof Fn || f instanceof UndefFn || f instanceof Derivative) {
    for (const g of f.args) addComponents(g, x, out);
    out.set(f.key, f);
  } else if (f instanceof Pow) {
    addComponents(f.base, x, out);
    const e = f.exp;
    if (!(e instanceof Rational && e.isInteger)) {
      if (e instanceof Rational) {
        const r = pow(f.base, Rational.of(1n, e.q));
        out.set(r.key, r);
      } else {
        addComponents(e, x, out);
        out.set(f.key, f);
      }
    }
  } else for (const g of f.args) addComponents(g, x, out);
}

/**
 * SymPy components(f, x): the functional components of f, its symbols,
 * function applications and non-integer powers (a rational power with its
 * minimal positive exponent).
 *
 * @example
 * componentsOf(parse('sin(x)*cos(x)**2'), x)  // [x, sin(x), cos(x)] (in some order)
 */
export function componentsOf(f: Expr, x: Sym): Expr[] {
  const out = new Map<string, Expr>();
  addComponents(f, x, out);
  return [...out.values()];
}

// the variables of the algorithm (SymPy _symbols: the same Dummy for the same name and index)
const symbolsCache = new Map<string, Dummy[]>();
function symbols(name: string, n: number): Dummy[] {
  const l = symbolsCache.get(name) ?? [];
  symbolsCache.set(name, l);
  while (l.length < n) l.push(new Dummy(`${name}${l.length}`));
  return l.slice(0, n);
}

/** Options of heurisch: rewrite sin, cos, cot (sinh, cosh, coth) with tan (tanh); the number of retries; the degree offset. */
export interface HeurischOptions {
  rewrite?: boolean;
  retries?: number;
  degreeOffset?: number;
  /** Extra antiderivative components; an empty list enables automatic hints. */
  hints?: readonly Expr[];
}

type Pair = [Expr, Dummy];
const cmpExpr = (a: Expr, b: Expr): number => compareKeys(sortKey(a), sortKey(b));
// (the components are distinct: their order is that of the expressions)
const cmpPair = (p: Pair, q: Pair): number => cmpExpr(p[0], q[0]);
const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;
/** The functions heurisch does not handle. */
const excluded = (e: Expr): boolean => isHeaviside(e) || isDiracDelta(e) || (e instanceof Fn && ['abs', 're', 'im', 'sign', 'floor', 'ceiling', 'arg'].includes(e.name));

/** sin, cos, cot written with tan and sinh, cosh, coth with tanh (SymPy f.rewrite((sin, cos, cot), tan)). */
function rewriteTan(f: Expr): Expr {
  return mapBottomUp(f, (e) => {
    if (!(e instanceof Fn && e.args.length === 1)) return e;
    const a = at(e.args, 0);
    if (e.name === 'sin' || e.name === 'cos') return rewrite(e, 'tan');
    if (e.name === 'sinh' || e.name === 'cosh') return rewrite(e, 'tanh');
    if (e.name === 'cot') return pow(tan(a), -1);
    if (e.name === 'coth') return pow(tanh(a), -1);
    return e;
  });
}

/** The type of a component for the permutations of the mapping (SymPy type(e)). */
const typeOf = (e: Expr): string => (e instanceof Fn ? `Fn:${e.name}` : isExpPow(e) ? 'exp' : e.constructor.name);

/** The highest exponent of the algebraic parts of f (SymPy _exponent). */
function exponent(g: Expr): number {
  if (g instanceof Pow) {
    const e = g.exp;
    if (e instanceof Rational && !e.isInteger) {
      const p = Number(e.p);
      const q = Number(e.q);
      return p > 0 ? p + q - 1 : Math.abs(p + q);
    }
    return 1;
  }
  return g.args.length ? Math.max(...g.args.map(exponent)) : 1;
}

/** p as a polynomial in y (a Poly over the other symbols). */
const polyIn = (p: Expr, y: Expr): Poly => Poly.from(p, [y]);
const gcdIn = (p: Expr, q: Expr, y: Expr): Expr => polyIn(p, y).gcd(polyIn(q, y)).asExpr();

/**
 * The factors of poly over the roots of poly in z (SymPy root_factors(poly,
 * z)): the linear factors z - r and the factor of the roots not found.
 *
 * @internal
 */
export function rootFactors(poly: Expr, z: Sym): Expr[] {
  let rs: Expr[];
  try {
    rs = roots(poly, z);
  } catch {
    // (roots raises for the roots of degree 5 or more it does not find)
    rs = [];
  }
  const factors = ordered(rs).map((r) => add(z, mul(-1, r)));
  const F = polyIn(poly, z);
  if (factors.length < F.degree()) factors.push(F.quo(polyIn(mul(...factors), z)).asExpr());
  return factors;
}

/** The real and imaginary parts of an expanded polynomial linear in I (SymPy collect(poly, I, evaluate=False)). */
function splitI(e0: Expr): [Expr, Expr] {
  const e = expand(e0);
  const re: Expr[] = [];
  const im: Expr[] = [];
  for (const t of e instanceof Add ? e.args : [e]) {
    const fs = t instanceof Mul ? t.args : [t];
    if (fs.some((f) => f.key === S.I.key)) im.push(mul(...fs.filter((f) => f.key !== S.I.key)));
    else re.push(t);
  }
  return [add(...re), add(...im)];
}

/**
 * SymPy heurisch(f, x): an antiderivative of f by the heuristic (parallel)
 * Risch algorithm (Bronstein's "Poor Man's Integrator"), or undefined when it
 * is not found (which does not prove that none is elementary).
 *
 * Bessel derivatives use adjacent orders as an algebraically independent pair.
 *
 * @example
 * heurisch(parse('y*tan(x)'), x)  // y*log(tan(x)**2 + 1)/2
 */
export function heurisch(f: Expr, x: Sym, opts: HeurischOptions = {}): Expr | undefined {
  return heurisch0(f, x, opts.rewrite ?? false, opts.retries ?? 3, opts.degreeOffset ?? 0, undefined, [], opts.hints);
}

function heurisch0(f0: Expr, x: Sym, rewrite0: boolean, retries: number, degreeOffset: number, mappings0?: Iterator<Pair[]>, unnecessary0: Pair[] = [], hints?: readonly Expr[]): Expr | undefined {
  if (some(f0, excluded)) return undefined;
  if (!f0.has(x)) return mul(f0, x);
  let [indep, f] = f0 instanceof Add ? [S.One, f0] : asIndependent(f0, [x]);
  let rewrite = rewrite0;
  const hasTrig = some(f, (e) => e instanceof Fn && ['sin', 'cos', 'cot', 'sinh', 'cosh', 'coth'].includes(e.name));
  if (rewrite) f = rewriteTan(f);
  else if (!hasTrig) rewrite = true;
  const dcache = new Map<string, Expr>();
  const getDiff = (g: Expr): Expr => {
    const cached = dcache.get(g.key);
    if (cached !== undefined) return cached;
    if (g instanceof Fn && ['besselj', 'bessely', 'hankel1', 'hankel2', 'besseli', 'besselk', 'jn', 'yn'].includes(g.name)) {
      const n = at(g.args, 0), z = at(g.args, 1);
      const previous = fn(g.name, [add(n, -1), z]);
      const dz = getDiff(z);
      const order = ['jn', 'yn'].includes(g.name) ? add(n, 1) : n;
      const d0 = add(mul(g.name === 'besselk' ? -1 : 1, previous), mul(-1, order, g, pow(z, -1)));
      const d1 = add(mul(add(n, -1), previous, pow(z, -1)), mul(g.name === 'besseli' ? 1 : -1, g));
      dcache.set(g.key, mul(d0, dz));
      dcache.set(previous.key, mul(d1, dz));
    } else dcache.set(g.key, cancel(diff(g, x)));
    return defined(dcache.get(g.key), 'cached derivative');
  };
  const termMap = new Map<string, Expr>();
  addComponents(f, x, termMap);
  if (hints !== undefined) {
    if (hints.length) for (const g of hints) termMap.set(g.key, g);
    else for (const g of [...termMap.values()]) {
      const base = isExpPow(g) ? g.exp : g instanceof Pow && g.exp instanceof Rational && g.exp.q === 2n ? g.base : undefined;
      if (base === undefined) continue;
      const pc = polyCoefficients(base, x);
      if (pc === undefined || [...pc.keys()].some((k) => k > 2)) continue;
      const a = pc.get(2) ?? S.Zero;
      const b = pc.get(1) ?? S.Zero;
      const c = pc.get(0) ?? S.Zero;
      let hint: Expr | undefined;
      if (isExpPow(g)) {
        if (isPositive(a) === true) hint = erfi(add(mul(sqrt(a), x), mul(b, pow(mul(2, sqrt(a)), -1))));
        else if (isNegative(a) === true) hint = erf(add(mul(sqrt(mul(-1, a)), x), mul(-1, b, pow(mul(2, sqrt(mul(-1, a))), -1))));
      } else if (isZeroExpr(b) && isPositive(c) === true) {
        if (isPositive(a) === true) hint = asinh(mul(sqrt(mul(a, pow(c, -1))), x));
        else if (isNegative(a) === true) hint = asin(mul(sqrt(mul(-1, a, pow(c, -1))), x));
      } else if (isZeroExpr(b) && isNegative(c) === true && isPositive(a) === true) {
        hint = mul(log(add(mul(sqrt(a), sqrt(base)), mul(a, x))), pow(sqrt(a), -1));
        dcache.set(hint.key, pow(sqrt(base), -1));
      }
      if (hint !== undefined) termMap.set(hint.key, hint);
    }
  }
  for (const g of [...termMap.values()]) addComponents(getDiff(g), x, termMap);
  const terms = [...termMap.values()];
  const V = symbols('x', terms.length);
  // the mapping from the largest expressions to the smallest (the last is x)
  // (SymPy sorts by the part of each component that depends on x: the components are functions,
  // powers and symbols, which are that part themselves)
  const sorted = terms
    .map((t, i): Pair => [t, at(V, i)])
    .sort(cmpPair)
    .reverse();
  let mappings: Iterator<Pair[]>;
  let unnecessary: Pair[];
  if (mappings0 === undefined) {
    // only the order of the components of different types is permuted
    // (x is the last pair in SymPy's order; its place is taken here whatever the sort keys give)
    unnecessary = sorted.splice(sorted.findIndex(([t]) => t.key === x.key), 1);
    const types = new Map<string, Pair[]>();
    for (const pr of sorted) {
      const l = types.get(typeOf(pr[0])) ?? [];
      l.push(pr);
      types.set(typeOf(pr[0]), l);
    }
    mappings = (function* (): Generator<Pair[], void, undefined> {
      for (const perm of permutations([...types.values()])) yield perm.flatMap((g) => [...g].sort(cmpPair));
    })();
  } else {
    mappings = mappings0;
    unnecessary = unnecessary0;
  }
  let found: { sub: (e: Expr) => Expr; diffs: Expr[]; denom: Expr } | undefined;
  for (let it = mappings.next(); it.done !== true; it = mappings.next()) {
    const mapping = [...it.value, ...unnecessary];
    const sub = (e: Expr): Expr => subs(e, mapping);
    const diffs = terms.map((g) => sub(getDiff(g)));
    const denoms = diffs.map((g) => asNumerDenom(g)[1]);
    if (denoms.every((h) => isPolynomial(h, V)) && isRationalFunction(sub(f), V)) {
      const denom = denoms.reduce((p, q) => Poly.from(p, V).lcm(Poly.from(q, V)).asExpr());
      found = { sub, diffs, denom };
      break;
    }
  }
  // a result times the factor independent of x
  const scaled = (r: Expr | undefined): Expr | undefined => (r === undefined ? undefined : mul(indep, r));
  // no mapping gives rational functions: try again with tan and tanh
  if (found === undefined) return rewrite ? undefined : scaled(heurisch0(f, x, true, 3, 0, undefined, [], hints));
  const { sub, diffs, denom } = found;
  const numers = diffs.map((g) => cancel(mul(denom, g)));
  const derivation = (h: Expr): Expr => add(...numers.map((d, i) => mul(d, diff(h, at(V, i)))));
  const deflation = (p: Expr): Expr => {
    // (the first variable of p, unless the derivation of p vanishes)
    const y = V.find((v) => p.has(v));
    if (y === undefined || isZeroExpr(derivation(p))) return p;
    const [c, q] = polyIn(p, y).primitive();
    return mul(deflation(c), q.gcd(q.diff(y)).asExpr());
  };
  const splitter = (p: Expr): [Expr, Expr] => {
    for (const y of V) {
      // (the derivation of a variable, the derivative of its component, does not vanish)
      if (p.has(y)) {
        const [c, qp] = polyIn(p, y).primitive();
        const q = qp.asExpr();
        const h = gcdIn(q, derivation(q), y);
        const s = polyIn(h, y).quo(polyIn(gcdIn(q, diff(q, y), y), y)).asExpr();
        const cSplit = splitter(c);
        if (polyIn(s, y).degree() === 0) return [cSplit[0], mul(q, cSplit[1])];
        const qSplit = splitter(cancel(mul(q, pow(s, -1))));
        return [mul(cSplit[0], qSplit[0], s), mul(cSplit[1], qSplit[1])];
      }
    }
    return [S.One, p];
  };
  // the polynomials of tan and tanh that may appear in the logarithms, and LambertW, a factor of the denominator
  const special = new Map<string, [Expr, boolean]>();
  for (const term of terms) {
    const name = term instanceof Fn ? term.name : '';
    if (name === 'tan') {
      const k = add(1, pow(sub(term), 2));
      special.set(k.key, [k, false]);
    } else if (name === 'tanh') {
      for (const k of [add(1, sub(term)), add(1, mul(-1, sub(term)))]) special.set(k.key, [k, false]);
    } else if (name === 'LambertW') {
      const k = sub(term);
      special.set(k.key, [k, true]);
    }
  }
  const F = sub(f);
  const [P, Q] = asNumerDenom(F);
  const uSplit = splitter(denom);
  const vSplit = splitter(Q);
  const polys = new Map<string, Expr>();
  for (const p of [...vSplit, uSplit[0], ...[...special.values()].map(([k]) => k)]) polys.set(p.key, p);
  const s = mul(uSplit[0], ...[...special.values()].filter(([, v]) => v).map(([k]) => k));
  // (s, P and Q are polynomials: F is a rational function and s a product of polynomials)
  const [a, b, c] = [s, P, Q].map((p) => Poly.from(p, V).totalDegree());
  const polyDenom = mul(s, vSplit[0], deflation(vSplit[1]));
  const A = exponent(f);
  const B = defined(a) + Math.max(defined(b), defined(c));
  const monoms = [...itermonomials(V, A > 1 && B > 1 ? A + B - 1 + degreeOffset : A + B + degreeOffset)].sort(cmpExpr);
  const polyCoeffs0 = symbols('A', monoms.length);
  const polyPart = add(...monoms.map((m, i) => mul(at(polyCoeffs0, i), m)));
  const reducibles = new Map<string, Expr>();
  for (const poly of ordered([...polys.values()])) {
    const [coeff, factors] = factorListExpr(poly, V);
    reducibles.set(coeff.key, coeff);
    for (const [fact] of factors) reducibles.set(fact.key, fact);
  }
  const integrate = (field: 'Q' | undefined): Expr | undefined => {
    const polyCoeffs: Dummy[] = [...polyCoeffs0];
    const irreducibles = new Map<string, Expr>();
    if (field === 'Q') for (const [k, p] of reducibles) irreducibles.set(k, p);
    else {
      for (const poly of ordered([...reducibles.values()])) {
        const z = ordered(V.filter((v) => poly.has(v)))[0];
        if (!(z instanceof Dummy)) continue;
        for (const r of rootFactors(poly, z)) irreducibles.set(r.key, r);
      }
    }
    // pairs of complex conjugate factors x +- I*y as log(x**2 + y**2) and atan(x/y)
    const pairs: [Expr, Expr][] = [];
    for (const poly of ordered([...irreducibles.values()])) {
      const [re, im] = splitI(poly);
      if (isZeroExpr(im) || re.has(S.I) || im.has(S.I)) continue;
      pairs.push([re, im]);
      irreducibles.delete(poly.key);
    }
    const atans = new Map<string, Expr>();
    for (let pr = pairs.shift(); pr !== undefined; pr = pairs.shift()) {
      const [re, im0] = pr;
      const k = pairs.findIndex(([r2, i2]) => r2.key === re.key && i2.key === mul(-1, im0).key);
      if (k >= 0) {
        pairs.splice(k, 1);
        const im = couldExtractMinusSign(im0) ? mul(-1, im0) : im0;
        const q = add(mul(re, re), mul(im, im));
        irreducibles.set(q.key, q);
        const t = atan(mul(re, pow(im, -1)));
        atans.set(t.key, t);
      } else {
        const q = add(re, mul(S.I, im0));
        irreducibles.set(q.key, q);
      }
    }
    // the logarithms and arctangents of the variables, each with an unknown coefficient
    const hasV = (e: Expr): boolean => V.some((v) => e.has(v));
    const irr = ordered([...irreducibles.values()]).filter(hasV).reverse();
    const ats = ordered([...atans.values()]).filter(hasV).reverse();
    const Bs = symbols('B', irr.length);
    const Cs = symbols('C', ats.length);
    polyCoeffs.push(...Bs, ...Cs);
    const logPart = irr.map((poly, i) => mul(at(Bs, i), log(poly)));
    const atanPart = ats.map((t, i) => mul(at(Cs, i), t));
    const candidate = add(mul(polyPart, pow(polyDenom, -1)), ...logPart, ...atanPart);
    const h = add(F, mul(-1, derivation(candidate), pow(denom, -1)));
    const rawNumer = expand(asNumerDenom(h)[0]);
    // (the candidate is linear in its unknown coefficients; a numerator that is not a polynomial has no solution)
    const solution = isPolynomial(rawNumer, [...V, ...polyCoeffs]) ? linsolve(Poly.from(rawNumer, V, { domain: 'EX' }).coeffs(), polyCoeffs) : undefined;
    if (solution === undefined) return undefined;
    const rep = polyCoeffs.map((v, i): [Expr, Expr] => [v, at(solution, i)]);
    return xreplace(xreplace(candidate, rep), polyCoeffs.map((v): [Expr, Expr] => [v, S.Zero]));
  };
  const vKeys = new Set(V.map((v) => v.key));
  const moreFree = [...F.freeSymbols()].some((v) => !vKeys.has(v.key));
  const solution = moreFree ? integrate(undefined) : (integrate('Q') ?? integrate(undefined));
  if (solution !== undefined) {
    const back = terms.map((t, i): [Expr, Expr] => [at(V, i), t]);
    let antideriv = expand(cancel(subs(solution, back, { simultaneous: true })));
    if (antideriv instanceof Add) antideriv = asIndependent(antideriv, [x])[1];
    return mul(indep, antideriv);
  }
  // the next mappings
  return retries >= 0 ? scaled(heurisch0(f, x, rewrite, retries - 1, degreeOffset, mappings, unnecessary, hints)) : undefined;
}

/** The denominators of the subexpressions of e, each factor once (SymPy denoms). */
function denoms(e: Expr): Expr[] {
  const out = new Map<string, Expr>();
  const visit = (p: Expr): void => {
    const den = asNumerDenom(p)[1];
    if (den.key !== S.One.key) for (const d of den instanceof Mul ? den.args : [den]) out.set(d.key, d);
    for (const a of p.args) visit(a);
  };
  visit(e);
  return ordered([...out.values()]);
}

type Solution = [Expr, Expr][];
const solutionKey = (s: Solution): string => s.map(([k, v]) => `${k.key}=${v.key}`).join(';');

/**
 * The solutions of d = 0 for its first symbol other than x that gives some
 * (SymPy solve([d], dict=True, exclude=(x,))).
 */
function solveDenominator(d: Expr, x: Sym): Solution[] {
  for (const s of ordered([...d.freeSymbols()].filter((v) => v.key !== x.key))) {
    let sols: Expr[];
    try {
      sols = solve(d, s);
    } catch {
      // (SymPy: NotImplementedError)
      continue;
    }
    if (sols.length) return sols.map((v): Solution => [[s, v]]);
  }
  return [];
}

/**
 * SymPy heurisch_wrapper(f, x): heurisch with the cases where a symbolic
 * denominator of the result vanishes, as a Piecewise; undefined when
 * heurisch finds no antiderivative.
 *
 * @example
 * heurischWrapper(parse('cos(n*x)'), x)  // Piecewise((sin(n*x)/n, Ne(n, 0)), (x, True))
 */
export function heurischWrapper(f: Expr, x: Sym, opts: HeurischOptions = {}): Expr | undefined {
  if (!f.has(x)) return mul(f, x);
  const res = heurisch(f, x, opts);
  if (res === undefined) return undefined;
  const uniq = new Map<string, Solution>();
  for (const d of denoms(res)) for (const s of solveDenominator(d, x)) uniq.set(solutionKey(s), s);
  // the poles of the integrand are not special cases
  for (const d of denoms(f)) for (const s of solveDenominator(d, x)) uniq.delete(solutionKey(s));
  let slns = [...uniq.values()];
  if (!slns.length) return res;
  if (slns.length > 1) {
    // all the conditions together, when they are consistent
    const all = new Map<string, [Expr, Expr]>();
    let consistent = true;
    // (the solutions are distinct pairs: a symbol met again has another value)
    for (const [k, v] of slns.flat()) {
      if (all.has(k.key)) consistent = false;
      all.set(k.key, [k, v]);
    }
    if (consistent) slns = [[...all.values()], ...slns];
  }
  const pairs = slns.map((sub): [Expr, Expr] => {
    const g = subs(f, sub);
    return [heurisch(g, x, opts) ?? impl.integrate(g, x), and(...sub.map(([k, v]) => Eq(k, v)))];
  });
  const first = pairs[0];
  const firstSln = slns[0];
  if (pairs.length === 1 && first !== undefined && firstSln !== undefined) {
    const generic = or(...firstSln.map(([k, v]) => Ne(k, v)));
    return piecewise([res, generic], [first[0], S.true]);
  }
  return piecewise(...pairs, [res, S.true]);
}
