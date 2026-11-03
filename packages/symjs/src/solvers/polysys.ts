// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Factoring of polynomial systems (port of SymPy
 * solvers/polysys.py factor_system and factor_system_cond).
 */

import { NotImplementedError } from '../core/errors';
import type { ExprLike, Sym } from '../core/nodes';
import { Expr, Rational } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { at, cast, defined, expectType, first, getOrThrow } from '../core/guard';
import { groebner } from '../polys/groebner';
import { roots } from '../polys/poly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Poly, factorListExpr, sortGens } from '../polys/sympoly';
import { expand } from '../simplify/expand';
import { radsimp } from '../simplify/sqrtdenest';

type Factor = { expr: Expr; ground: boolean };

/**
 * Split each equation into irreducible factors and return the minimal
 * systems (one factor from every equation) whose common zeros give all
 * solutions of the original system, like SymPy factor_system_cond. Systems
 * may contain conditions that involve only the parameters.
 */
export function factorSystemCond(eqs: readonly ExprLike[], gens: readonly Expr[] = []): Expr[][] {
  return factorSystemRaw(eqs, gens).map((s) => s.map((f) => f.expr));
}

/**
 * SymPy factor_system: like factorSystemCond but generic systems only (those
 * that need a condition on the parameters alone are dropped).
 */
export function factorSystem(eqs: readonly ExprLike[], gens: readonly Expr[] = []): Expr[][] {
  return factorSystemRaw(eqs, gens)
    .filter((s) => !s.some((f) => f.ground))
    .map((s) => s.map((f) => f.expr));
}

function factorSystemRaw(eqsIn: readonly ExprLike[], gensIn: readonly Expr[]): Factor[][] {
  const eqs = eqsIn.map((e) => expand(sympify(e)));
  const all = new Map<string, Sym>();
  for (const e of eqs) for (const s of freeSymbols(e)) all.set(s.key, s);
  // sortGens returns the same Sym instances, looked up again by key to keep their type
  const sortSyms = (xs: Sym[]): Sym[] => sortGens(xs).map((g) => getOrThrow(all, g.key));
  const gens: readonly Expr[] = gensIn.length ? gensIn : sortSyms([...all.values()]);
  const genKeys = new Set(gens.map((g) => g.key));
  if (!gens.length) return eqs.every((e) => e instanceof Rational && e.isZero) ? [[]] : [];
  const vars = [...gens, ...sortSyms([...all.values()].filter((s) => !genKeys.has(s.key)))];
  const hasGen = (e: Expr) => [...freeSymbols(e)].some((s) => genKeys.has(s.key));

  const factorSets: Factor[][] = [];
  for (const e of eqs) {
    if (e instanceof Rational && e.isZero) continue;
    const [, fs] = factorListExpr(e, vars);
    const genFactors = fs.filter(([f]) => hasGen(f)).map(([f]) => ({ expr: f, ground: false }));
    const params = fs.filter(([f]) => !hasGen(f)).map(([f]) => f);
    if (!params.length) {
      if (!genFactors.length) return [];
      factorSets.push(genFactors);
    } else {
      factorSets.push([...genFactors, { expr: mul(...params), ground: true }]);
    }
  }
  if (!factorSets.length) return [[]];
  const systems = combineFactorSets(factorSets);
  // the coefficients are polynomials in the generators of the coefficient domain (SymPy ZZ[a, sqrt(a), ...])
  const coeffGens = new Map<string, Expr>();
  for (const f of systems.flat()) for (const c of Poly.from(f.expr, gens).coeffs()) for (const g of Poly.from(c).gens) coeffGens.set(g.key, g);
  const params = sortGens([...coeffGens.values()]);
  const sorted = systems.map((s) => [...s].sort((a, b) => -cmpKey(polyKey(a, gens), polyKey(b, gens), params)));
  return sorted.sort((a, b) => -cmpSysKey(a.map((f) => polyKey(f, gens)), b.map((f) => polyKey(f, gens)), params));
}

/** SymPy _factor_sets: minimal sets hitting every factor list. */
function combineFactorSets(sets: Factor[][]): Factor[][] {
  const result = new Map<string, Factor[]>();
  const has = (s: Factor[], f: Factor) => s.some((g) => g.expr.key === f.expr.key);
  const visit = (remaining: Factor[][], current: Factor[]) => {
    if (!remaining.length) {
      const sorted = [...current].sort((a, b) => (a.expr.key < b.expr.key ? -1 : 1));
      result.set(sorted.map((f) => f.expr.key).join('|'), sorted);
      return;
    }
    const next = remaining.reduce((m, s) => (s.length < m.length ? s : m));
    const rest = remaining.filter((s) => s !== next);
    // the sets containing a chosen factor are dropped, so f is never in current yet
    for (const f of next) visit(rest.filter((s) => !has(s, f)), [...current, f]);
  };
  visit(sets, []);
  const all = [...result.values()];
  const isProperSuperset = (a: Factor[], b: Factor[]) => a.length > b.length && b.every((f) => has(a, f));
  return all.filter((s1) => !all.some((s2) => isProperSuperset(s1, s2)));
}

/** A dense recursive representation (SymPy DMP.to_list): coefficients at the innermost level. */
type Dense = Expr | Dense[];
type Key = [number[], Dense];

/** SymPy dmp_zero(u): the zero polynomial at level u. */
const dmpZero = (u: number): Dense[] => (u === 0 ? [] : [dmpZero(u - 1)]);

/** The dense list of the terms at level u (u + 1 generators left), like SymPy's DMP rep. */
function dense(terms: [number[], Expr][], u: number): Dense[] {
  const d = Math.max(...terms.map(([m]) => first(m)));
  const out: Dense[] = [];
  for (let k = d; k >= 0; k--) {
    const sub = terms.filter(([m]) => first(m) === k).map(([m, c]): [number[], Expr] => [m.slice(1), c]);
    if (u === 0) out.push(sub.length ? at(sub, 0)[1] : Rational.of(0));
    else out.push(sub.length ? dense(sub, u - 1) : dmpZero(u - 1));
  }
  return out;
}

/** SymPy _poly_sort_key: (degree_list, dense representation). */
function polyKey(f: Factor, gens: readonly Expr[]): Key {
  const p = Poly.from(f.expr, gens);
  return [p.degreeList(), dense(p.terms(), gens.length - 1)];
}

/** Python ordering of sequences: elementwise, then by length. */
function cmpSeq<T>(a: readonly T[], b: readonly T[], cmp: (u: T, v: T) => number): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = cmp(at(a, i), at(b, i));
    if (c) return c;
  }
  return a.length - b.length;
}

const cmpNums = (a: readonly number[], b: readonly number[]): number => cmpSeq(a, b, (u, v) => u - v);

/** Python ordering of numbers (exact for rationals). */
function cmpNumber(a: Expr, b: Expr): number {
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    return d === 0n ? 0 : d < 0n ? -1 : 1;
  }
  return Math.sign(a.toComplex().re - b.toComplex().re);
}

/**
 * Python ordering of coefficients: numbers by value; with generators in the
 * coefficient domain, the coefficients are polynomials in them, ordered like
 * SymPy PolyElement.sort_key (the number of terms, then the terms in lex order).
 */
function cmpCoeff(a: Expr, b: Expr, params: readonly Expr[]): number {
  if (!params.length) return cmpNumber(a, b);
  const terms = (c: Expr) => {
    const p = Poly.from(c, params);
    return p.isZero ? [] : p.terms();
  };
  const [ta, tb] = [terms(a), terms(b)];
  return ta.length - tb.length || cmpSeq(ta, tb, ([ma, ca], [mb, cb]) => cmpNums(ma, mb) || cmpNumber(ca, cb));
}

const isDenseList = (v: unknown): v is Dense[] => Array.isArray(v);

/** Python ordering of (nested) lists. */
function cmpDense(a: Dense, b: Dense, params: readonly Expr[]): number {
  // the keys of one system share the generators, so both are lists or both are coefficients
  if (!Array.isArray(a)) return cmpCoeff(a, cast(b, Expr, 'coefficient'), params);
  return cmpSeq<Dense>(a, expectType(b, isDenseList, 'dense list'), (u, v) => cmpDense(u, v, params));
}

/** SymPy _poly_sort_key order. */
const cmpKey = (a: Key, b: Key, params: readonly Expr[]): number => cmpNums(a[0], b[0]) || cmpDense(a[1], b[1], params);

/** SymPy _sys_sort_key: the degree lists of all members first, then the representations. */
const cmpSysKey = (a: Key[], b: Key[], params: readonly Expr[]): number =>
  cmpSeq(a, b, (u, v) => cmpNums(u[0], v[0])) || cmpSeq(a, b, (u, v) => cmpDense(u[1], v[1], params));

/**
 * Solve a zero-dimensional polynomial system with a lexicographic Gröbner
 * basis (SymPy solve_poly_system / solve_generic). Solutions are tuples in
 * the order of `gens`, sorted like SymPy (default_sort_key). Throws for
 * systems that are not zero-dimensional.
 */
export function solvePolySystem(eqs: readonly ExprLike[], gens: readonly Sym[], opts: { rationalOnly?: boolean } = {}): Expr[][] {
  const system = eqs.map((e) => expand(sympify(e))).filter((e) => !(e instanceof Rational && e.isZero));
  const sols = solveReduced(system, gens, opts.rationalOnly ?? false);
  return sols.sort((a, b) => cmpSeq(a, b, (u, v) => compareKeys(sortKey(u), sortKey(v))));
}

function solveReduced(system: Expr[], gens: readonly Sym[], rationalOnly: boolean): Expr[][] {
  // no equation left to determine the generators: they are free
  if (!system.length) throw new NotImplementedError('solve_poly_system: only zero-dimensional systems are supported');
  const gen = at(gens, -1);
  const distinctRoots = (f: Expr): Expr[] => {
    const seen = new Map<string, Expr>();
    for (const r of roots(f, gen)) if (!rationalOnly || r instanceof Rational) seen.set(r.key, r);
    return [...seen.values()];
  };
  if (system.length === 1 && gens.length === 1) return distinctRoots(at(system, 0)).map((z) => [z]);
  if (gens.length === 1) {
    // common roots (works for algebraic coefficients, unlike the Gröbner basis over QQ)
    const [lowest, ...others] = [...system].sort((a, b) => Poly.from(a, [gen]).degree() - Poly.from(b, [gen]).degree());
    return distinctRoots(defined(lowest, 'equation'))
      .filter((z) => others.every((o) => expand(xreplace(o, [[gen, z]])).equals(Rational.of(0))))
      .map((z) => [z]);
  }
  // the Gröbner basis is computed over QQ: algebraic coefficients need a triangular system
  if (system.some(hasIrrational)) return backSubstitute(system, gens, rationalOnly);
  const basis = [...groebner(system, [...gens], 'lex').exprs];
  if (basis.length === 1 && basis[0] instanceof Rational) return [];
  const others = new Set(gens.slice(0, -1).map((g) => g.key));
  const univariate = basis.filter((b) => ![...freeSymbols(b)].some((s) => others.has(s.key)) && b.has(gen));
  if (univariate.length !== 1) throw new NotImplementedError('solve_poly_system: only zero-dimensional systems are supported');
  const f = at(univariate, 0);
  // a single polynomial in the last generator leaves the others free
  if (basis.length === 1) throw new NotImplementedError('solve_poly_system: only zero-dimensional systems are supported');
  const zeros = distinctRoots(f);
  const out: Expr[][] = [];
  const rest = basis.filter((b) => b !== f);
  for (const z of zeros) {
    // every root of the eliminant extends to a solution (the projection of a finite
    // variety is closed), so no basis element becomes a nonzero constant here
    const sub = rest.map((b) => expand(xreplace(b, [[gen, z]]))).filter((b) => !(b instanceof Rational && b.isZero));
    // irrational coefficients: the lex basis is triangular, so back-substitute instead of a new basis over QQ
    const rationalCoeffs = sub.every((b) => !hasIrrational(b));
    const partial = rationalCoeffs ? solveReduced(sub, gens.slice(0, -1), rationalOnly) : backSubstitute(sub, gens.slice(0, -1), rationalOnly);
    for (const s of partial) out.push([...s, z]);
  }
  return out;
}

/** Does a polynomial have a coefficient that is a number but not rational (sqrt(2), I, ...)? */
const hasIrrational = (e: Expr): boolean => {
  if (e.freeSymbols().size === 0) return !(e instanceof Rational);
  return e.args.some(hasIrrational);
};

/**
 * Solutions of a triangular system with algebraic coefficients: a generator
 * with an equation in it alone (the last such generator) is solved first and
 * substituted into the others.
 */
function backSubstitute(system: Expr[], gens: readonly Sym[], rationalOnly: boolean): Expr[][] {
  if (!gens.length) return system.every((b) => Math.abs(b.toComplex().re) + Math.abs(b.toComplex().im) < 1e-9) ? [[]] : [];
  const alone = (i: number) => {
    const others = new Set(gens.filter((_, j) => j !== i).map((g) => g.key));
    return system.filter((b) => b.has(at(gens, i)) && ![...freeSymbols(b)].some((s) => others.has(s.key)));
  };
  let idx = gens.length - 1;
  while (idx >= 0 && !alone(idx).length) idx--;
  if (idx < 0) throw new NotImplementedError('solve_poly_system: only zero-dimensional systems are supported');
  const gen = at(gens, idx);
  const uni = alone(idx);
  const [lowest, ...rest] = [...uni].sort((a, b) => Poly.from(a, [gen]).degree() - Poly.from(b, [gen]).degree());
  const vanishes = (e: Expr) => {
    const c = e.toComplex();
    return Math.hypot(c.re, c.im) < 1e-9;
  };
  const seen = new Map<string, Expr>();
  for (const r0 of roots(defined(lowest, 'equation'), gen)) {
    // roots of polynomials with algebraic coefficients come with radical denominators
    const r = expand(radsimp(r0));
    if (!rationalOnly || r instanceof Rational) seen.set(r.key, r);
  }
  const out: Expr[][] = [];
  const otherGens = gens.filter((_, j) => j !== idx);
  for (const z of seen.values()) {
    if (!rest.every((o) => vanishes(xreplace(o, [[gen, z]])))) continue;
    const sub = system.filter((b) => !uni.includes(b)).map((b) => expand(xreplace(b, [[gen, z]])));
    for (const s of backSubstitute(sub, otherGens, rationalOnly)) out.push([...s.slice(0, idx), z, ...s.slice(idx)]);
  }
  return out;
}
