// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Factoring of polynomial systems (port of SymPy
 * solvers/polysys.py factor_system and factor_system_cond).
 */

import { Expr, ExprLike, Rational, Sym } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
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
  const gens = (gensIn.length ? gensIn : sortGens([...all.values()])) as Sym[];
  const genKeys = new Set(gens.map((g) => g.key));
  if (!gens.length) return eqs.every((e) => e instanceof Rational && e.isZero) ? [[]] : [];
  const vars = [...gens, ...sortGens([...all.values()].filter((s) => !genKeys.has(s.key))) as Sym[]];
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
  const sorted = systems.map((s) => [...s].sort((a, b) => -cmpKey(polyKey(a, gens), polyKey(b, gens))));
  return sorted.sort((a, b) => -cmpSysKey(a.map((f) => polyKey(f, gens)), b.map((f) => polyKey(f, gens))));
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
    for (const f of next) visit(rest.filter((s) => !has(s, f)), has(current, f) ? current : [...current, f]);
  };
  visit(sets, []);
  const all = [...result.values()];
  const isProperSuperset = (a: Factor[], b: Factor[]) => a.length > b.length && b.every((f) => has(a, f));
  return all.filter((s1) => !all.some((s2) => isProperSuperset(s1, s2)));
}

type Key = (number | Expr)[][];

/** SymPy _poly_sort_key: (degree_list, dense representation). */
function polyKey(f: Factor, gens: readonly Sym[]): Key {
  const p = Poly.from(f.expr, gens);
  const rep: (number | Expr)[] = [];
  for (const [m, c] of p.terms()) rep.push(...m.map((k) => -k), c);
  return [p.degreeList().map((d) => (d === -Infinity ? -1 : d)), rep];
}

function cmpAtom(a: number | Expr, b: number | Expr): number {
  if (typeof a === 'number' && typeof b === 'number') return a - b;
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    return d === 0n ? 0 : d < 0n ? -1 : 1;
  }
  return 0;
}

function cmpList(a: (number | Expr)[], b: (number | Expr)[]): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = cmpAtom(a[i]!, b[i]!);
    if (c) return c;
  }
  return a.length - b.length;
}

function cmpKey(a: Key, b: Key): number {
  return cmpList(a[0]!, b[0]!) || cmpList(a[1]!, b[1]!);
}

/** SymPy _sys_sort_key: degree lists of all members first, then representations. */
function cmpSysKey(a: Key[], b: Key[]): number {
  for (let part = 0; part < 2; part++) {
    for (let i = 0; i < Math.min(a.length, b.length); i++) {
      const c = cmpList(a[i]![part]!, b[i]![part]!);
      if (c) return c;
    }
    if (a.length !== b.length) return a.length - b.length;
  }
  return 0;
}

/**
 * Solve a zero-dimensional polynomial system with a lexicographic Gröbner
 * basis (SymPy solve_poly_system / solve_generic). Solutions are tuples in
 * the order of `gens`, sorted like SymPy (default_sort_key). Throws for
 * systems that are not zero-dimensional.
 */
export function solvePolySystem(eqs: readonly ExprLike[], gens: readonly Sym[], opts: { rationalOnly?: boolean } = {}): Expr[][] {
  const system = eqs.map((e) => expand(sympify(e))).filter((e) => !(e instanceof Rational && e.isZero));
  const sols = solveReduced(system, gens, true, opts.rationalOnly ?? false);
  return sols.sort((a, b) => {
    for (let i = 0; i < a.length; i++) {
      const c = compareKeys(sortKey(a[i]!), sortKey(b[i]!));
      if (c) return c;
    }
    return 0;
  });
}

function solveReduced(system: Expr[], gens: readonly Sym[], entry: boolean, rationalOnly: boolean): Expr[][] {
  const gen = gens[gens.length - 1]!;
  const distinctRoots = (f: Expr): Expr[] => {
    const seen = new Map<string, Expr>();
    for (const r of roots(f, gen)) if (!rationalOnly || r instanceof Rational) seen.set(r.key, r);
    return [...seen.values()];
  };
  if (system.length === 1 && gens.length === 1) return distinctRoots(system[0]!).map((z) => [z]);
  if (gens.length === 1) {
    // common roots (works for algebraic coefficients, unlike the Gröbner basis over QQ)
    const [first, ...others] = [...system].sort((a, b) => Poly.from(a, [gen]).degree() - Poly.from(b, [gen]).degree());
    return distinctRoots(first!)
      .filter((z) => others.every((o) => expand(xreplace(o, [[gen, z]])).equals(Rational.of(0))))
      .map((z) => [z]);
  }
  const basis = [...groebner(system, [...gens], 'lex').exprs];
  if (basis.length === 1 && basis[0] instanceof Rational) return [];
  const others = new Set(gens.slice(0, -1).map((g) => g.key));
  const univariate = basis.filter((b) => ![...freeSymbols(b)].some((s) => others.has(s.key)) && b.has(gen));
  if (univariate.length !== 1) throw new Error('solve_poly_system: only zero-dimensional systems are supported');
  const f = univariate[0]!;
  const zeros = distinctRoots(f);
  if (basis.length === 1) return zeros.map((z) => [z]);
  const out: Expr[][] = [];
  const rest = basis.filter((b) => b !== f);
  for (const z of zeros) {
    const sub = rest.map((b) => expand(xreplace(b, [[gen, z]]))).filter((b) => !(b instanceof Rational && b.isZero));
    if (sub.some((b) => b.freeSymbols().size === 0)) continue;
    // irrational coefficients: the lex basis is triangular, so back-substitute instead of a new basis over QQ
    const rationalCoeffs = sub.every((b) => !hasIrrational(b));
    const partial = rationalCoeffs ? solveReduced(sub, gens.slice(0, -1), false, rationalOnly) : backSubstitute(sub, gens.slice(0, -1), rationalOnly);
    for (const s of partial) out.push([...s, z]);
  }
  if (entry && out.length && out[0]!.length !== gens.length) throw new Error('solve_poly_system: only zero-dimensional systems are supported');
  return out;
}

/** Does a polynomial have a coefficient that is a number but not rational (sqrt(2), I, ...)? */
const hasIrrational = (e: Expr): boolean => {
  if (e.freeSymbols().size === 0) return !(e instanceof Rational);
  return e.args.some(hasIrrational);
};

/** Solutions of a triangular system with algebraic coefficients, last generator first. */
function backSubstitute(system: Expr[], gens: readonly Sym[], rationalOnly: boolean): Expr[][] {
  if (!gens.length) return system.every((b) => Math.abs(b.toComplex().re) + Math.abs(b.toComplex().im) < 1e-9) ? [[]] : [];
  const gen = gens[gens.length - 1]!;
  const others = new Set(gens.slice(0, -1).map((g) => g.key));
  const uni = system.filter((b) => b.has(gen) && ![...freeSymbols(b)].some((s) => others.has(s.key)));
  if (!uni.length) throw new Error('solve_poly_system: only zero-dimensional systems are supported');
  const [first, ...rest] = [...uni].sort((a, b) => Poly.from(a, [gen]).degree() - Poly.from(b, [gen]).degree());
  const vanishes = (e: Expr) => {
    const c = e.toComplex();
    return Math.hypot(c.re, c.im) < 1e-9;
  };
  const seen = new Map<string, Expr>();
  for (const r0 of roots(first!, gen)) {
    // roots of polynomials with algebraic coefficients come with radical denominators
    const r = expand(radsimp(r0));
    if (!rationalOnly || r instanceof Rational) seen.set(r.key, r);
  }
  const out: Expr[][] = [];
  for (const z of seen.values()) {
    if (!rest.every((o) => vanishes(xreplace(o, [[gen, z]])))) continue;
    const sub = system.filter((b) => !uni.includes(b)).map((b) => expand(xreplace(b, [[gen, z]])));
    for (const s of backSubstitute(sub, gens.slice(0, -1), rationalOnly)) out.push([...s, z]);
  }
  return out;
}
