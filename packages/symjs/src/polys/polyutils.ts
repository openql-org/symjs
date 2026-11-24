// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/polyutils.py), BSD 3-Clause License.

/** Multinomial dictionaries with explicit or jointly inferred generators. */
import { PolynomialError } from '../core/errors';
import { first } from '../core/guard';
import { fact } from '../core/exprfacts';
import { Add, BoolAtom, Float, Mul, Pow, Rational, Rel, S, type Expr, type ExprLike } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { expand } from '../simplify/expand';
import type { Domain } from './domains';
import { Poly, sortGens } from './sympoly';

/** Options controlling generator discovery, as in SymPy dict_from_expr. */
export interface DictFromExprOptions {
  /** The ordered generators. */
  gens?: readonly Expr[];
  /** The coefficient domain. */
  domain?: Domain;
  /** Whether to treat additional expressions as generators. */
  greedy?: boolean;
  /** The algebraic extensions to include in the coefficient domain. */
  extension?: boolean | null;
  /** Whether to expand expressions before collecting their terms. */
  expand?: boolean;
}

/**
 * Convert expressions to dictionaries over one common sequence of generators.
 *
 * @param inputs - Expressions to expand over a shared generator list.
 * @param options - Choose the generator order, coefficient domain, algebraic extensions and whether to expand the input.
 * @returns The term dictionaries and their shared ordered generators.
 * @throws PolynomialError when the expression is not a commutative polynomial.
 * @see SymPy `sympy.polys.polyutils.parallel_dict_from_expr`
 */
export function parallelDictFromExpr(inputs: readonly ExprLike[], options: DictFromExprOptions = {}): [Map<number[], Expr>[], Expr[]] {
  const exprs = inputs.map((input) => {
    const e = sympify(input);
    if (!e.isCommutative || e instanceof BoolAtom || e instanceof Rel && e.op !== 'Eq') throw new PolynomialError('expression must be a commutative polynomial');
    const value = e instanceof Rel ? add(e.lhs, mul(-1, e.rhs)) : e;
    return options.expand === false ? value : expand(value);
  });
  if (options.gens?.length) return [exprs.map((e) => new Map(Poly.from(e, options.gens).asDict())), [...options.gens]];
  const isCoefficient = (e: Expr): boolean => {
    if (e instanceof Rational || e instanceof Float) return true;
    if (options.domain) return options.domain.contains(e);
    if (options.extension === true) return fact(e, 'algebraic') === true;
    return options.greedy === false ? freeSymbols(e).size === 0 : e.key === S.I.key;
  };
  const generators = new Map<string, Expr>();
  const reprs = exprs.map((e) => (e instanceof Add ? e.args : [e]).map((term) => {
    const coefficients: Expr[] = [];
    const powers = new Map<string, number>();
    for (const factor of term instanceof Mul ? term.args : [term]) {
      if (isCoefficient(factor)) coefficients.push(factor);
      else {
        let base = factor, exponent = 1;
        if (factor instanceof Pow && factor.exp instanceof Rational && factor.exp.isInteger) {
          exponent = Math.abs(Number(factor.exp.p));
          base = factor.exp.isNegative ? pow(factor.base, -1) : factor.base;
        }
        generators.set(base.key, base);
        powers.set(base.key, (powers.get(base.key) ?? 0) + exponent);
      }
    }
    return { coefficient: mul(...coefficients), powers };
  }));
  const gens = sortGens([...generators.values()]);
  const polys = reprs.map((terms) => {
    const combined = new Map<string, [number[], Expr]>();
    for (const { coefficient, powers } of terms) {
      const monom = gens.map((g) => powers.get(g.key) ?? 0);
      const key = monom.join(',');
      const previous = combined.get(key);
      combined.set(key, [monom, previous ? add(previous[1], coefficient) : coefficient]);
    }
    return new Map([...combined.values()].map(([m, c]) => [m, c]));
  });
  return [polys, gens];
}

/**
 * Convert one expression to its multinomial dictionary and generators.
 *
 * @param input - Expression to collect as a polynomial.
 * @param options - Choose the generator order, coefficient domain, algebraic extensions and whether to expand the input.
 * @returns The term dictionary and ordered generators.
 * @see SymPy `sympy.polys.polyutils.dict_from_expr`
 */
export function dictFromExpr(input: ExprLike, options: DictFromExprOptions = {}): [Map<number[], Expr>, Expr[]] {
  const [polys, gens] = parallelDictFromExpr([input], options);
  return [first(polys), gens];
}
