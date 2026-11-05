// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/constructor.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The smallest domain of a list of coefficients (SymPy
 * construct_domain): ZZ, QQ, ZZ_I, QQ_I, RR, CC, an algebraic field (with
 * `extension: true`), a polynomial ring or fraction field of the
 * generators (ZZ[x], QQ(x, y)), else EX; with the coefficients converted to
 * elements of that domain.
 */

import { Add, Constant, type Expr, Float, Mul, Pow, Rational, Sym } from '../core/nodes';
import { at, defined, first } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { ordered } from '../core/match';
import { expand } from '../simplify/expand';
import { fraction } from '../simplify/rational';
import { CC } from './domains/complexfield';
import { QQ_I, ZZ_I } from './domains/gaussiandomains';
import { AlgebraicField } from './domains/algebraicfield';
import { type Domain, EX, QQ, RR, ZZ } from './domains';
import { buildOptions, type Options } from './polyoptions';
import { sortGens } from './sympoly';

const isI = (e: Expr): boolean => e instanceof Constant && e.name === 'I';
const isInt = (e: Expr): boolean => e instanceof Rational && e.isInteger;

/** [a, b] for a coefficient a + b*I with numbers a and b, b nonzero (SymPy pure_complex); undefined otherwise. */
function pureComplex(e: Expr): [Expr, Expr] | undefined {
  const terms = e instanceof Add ? e.args : [e];
  let [re, im]: [Expr | undefined, Expr | undefined] = [undefined, undefined];
  for (const t of terms) {
    if (t instanceof Rational || t instanceof Float) re = t;
    else if (isI(t)) im = Rational.of(1n);
    else if (t instanceof Mul && t.args.length === 2 && (t.args[0] instanceof Rational || t.args[0] instanceof Float) && isI(at(t.args, 1))) im = at(t.args, 0);
    else return undefined;
  }
  return [re ?? Rational.of(0n), defined(im, 'imaginary part')];
}

/** A number built from rationals and I with +, * and rational powers (SymPy is_number and is_algebraic, for radicals). */
function isAlgebraicNumber(e: Expr): boolean {
  if (e instanceof Rational || isI(e)) return true;
  if (e instanceof Add || e instanceof Mul) return e.args.every(isAlgebraicNumber);
  if (e instanceof Pow) return e.exp instanceof Rational && isAlgebraicNumber(e.base);
  return false;
}

type Construction = [Domain, unknown[]];

/** The algebraic field of the algebraic coefficients (SymPy _construct_algebraic). */
function constructAlgebraic(coeffs: readonly Expr[]): Construction {
  const exts: Expr[] = [];
  const collect = (a: Expr): void => {
    if (a instanceof Rational) return;
    if (a instanceof Add || a instanceof Mul) a.args.forEach(collect);
    else if (!exts.some((x) => x.key === a.key)) exts.push(a);
  };
  coeffs.forEach(collect);
  const domain = new AlgebraicField(QQ, ...ordered(exts));
  return [domain, coeffs.map((c) => domain.convert(c))];
}

/** ZZ, QQ, ZZ_I, QQ_I, RR, CC or an algebraic field; null for a composite domain, false for EX (SymPy _construct_simple). */
function constructSimple(coeffs: readonly Expr[], opt: Options): Construction | null | false {
  let [rationals, floats, complexes, algebraics] = [false, false, false, false];
  const isAlgebraic = opt.extension === true ? isAlgebraicNumber : (): boolean => false;
  for (const coeff of coeffs) {
    if (coeff instanceof Rational) {
      if (!coeff.isInteger) rationals = true;
    } else if (coeff instanceof Float) {
      if (algebraics) return false;
      floats = true;
    } else {
      const c = pureComplex(coeff);
      if (c !== undefined) {
        complexes = true;
        const [x, y] = c;
        if (x instanceof Float || y instanceof Float) floats = true;
        else if (!isInt(x) || !isInt(y)) rationals = true;
      } else if (isAlgebraic(coeff)) {
        if (floats) return false;
        algebraics = true;
      } else return null;
    }
  }
  if (algebraics) return constructAlgebraic(coeffs);
  const domain = floats && complexes ? CC : floats ? RR : rationals || opt.field ? (complexes ? QQ_I : QQ) : complexes ? ZZ_I : ZZ;
  return [domain, coeffs.map((c) => domain.convert(c))];
}

/** The generators of expanded expressions: the factors that are not numbers (SymPy parallel_dict_from_basic). */
function generators(exprs: readonly Expr[]): Expr[] {
  const gens: Expr[] = [];
  const add = (g: Expr): void => {
    if (!gens.some((x) => x.key === g.key)) gens.push(g);
  };
  for (const e of exprs) {
    for (const t of e instanceof Add ? e.args : [e]) {
      for (const f of t instanceof Mul ? t.args : [t]) {
        if (isNumberFactor(f)) continue;
        add(f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.p > 0n ? f.base : f);
      }
    }
  }
  return sortGens(gens);
}

const isNumberFactor = (f: Expr): boolean => f instanceof Rational || f instanceof Float || isI(f);

/** The coefficients of the terms of an expanded polynomial in its generators (the products of their number factors). */
const coefficientsOf = (e: Expr): Expr[] => (e instanceof Add ? e.args : [e]).map((t) => mul(...(t instanceof Mul ? t.args : [t]).filter(isNumberFactor)));

/** A polynomial ring or fraction field of the generators; null when none applies (SymPy _construct_composite). */
function constructComposite(coeffs: readonly Expr[], opt: Options): Construction | null {
  const parts = coeffs.map((c) => fraction(c)).map(([n, d]) => [expand(n), expand(d)] as const);
  const gens = generators(parts.flat());
  if (opt.composite === null) {
    if (gens.some((g) => freeSymbols(g).size === 0)) return null;
    const seen = new Set<string>();
    for (const g of gens) {
      const syms = [...freeSymbols(g)].map((s) => s.key);
      if (syms.some((s) => seen.has(s))) return null;
      syms.forEach((s) => seen.add(s));
    }
  }
  const fractions = opt.field || parts.some(([, d]) => !(d instanceof Rational));
  const numbers = fractions ? parts.flatMap(([n, d]) => [...coefficientsOf(n), ...coefficientsOf(d)]) : parts.flatMap(([n, d]) => coefficientsOf(n).map((c) => mul(c, pow(d, -1))));
  let [rationals, floats] = [false, false];
  for (const c of numbers) {
    if (c instanceof Float) floats = true;
    else if (!(c instanceof Rational)) return null;
    else if (!c.isInteger) rationals = true;
  }
  // symjs polynomial rings are over ZZ, QQ and RR (SymPy also makes ZZ_I[x], QQ_I[x] and CC[x]; symjs uses EX there)
  const ground = floats ? RR : rationals ? QQ : ZZ;
  // the polynomial rings of symjs have symbols as generators (SymPy also allows ZZ[sin(x)]; symjs uses EX there)
  const syms = gens.filter((g): g is Sym => g instanceof Sym);
  if (syms.length !== gens.length) return null;
  const domain = fractions ? ground.fracField(...syms) : ground.polyRing(...syms);
  return [domain, coeffs.map((c) => domain.convert(c))];
}

/** Options of constructDomain (SymPy construct_domain keywords). */
export interface ConstructDomainOptions {
  /** Prefer a field: QQ over ZZ, K(x) over K[x]. */
  field?: boolean;
  /** Make algebraic coefficients elements of an algebraic field. */
  extension?: boolean | readonly ExprLike[];
  /** Allow (true) or forbid (false) polynomial rings and fraction fields; by default allowed for independent symbols. */
  composite?: boolean;
}

const isList = (o: unknown): o is readonly ExprLike[] => Array.isArray(o);

/**
 * The smallest domain of coefficients and the coefficients as its elements
 * (SymPy construct_domain): a list gives a list, a single coefficient one
 * element.
 */
export function constructDomain(obj: ExprLike | readonly ExprLike[], options: ConstructDomainOptions = {}): [Domain, unknown] {
  const opt = buildOptions([], new Map(Object.entries(options)));
  const coeffs = (isList(obj) ? obj : [obj]).map((c) => sympify(c));
  let result = constructSimple(coeffs, opt);
  if (result === null && opt.composite !== false) result = constructComposite(coeffs, opt);
  const [domain, elements] = result === null || result === false ? [EX, coeffs.map((c) => EX.convert(c))] : result;
  return [domain, isList(obj) ? elements : first(elements)];
}
