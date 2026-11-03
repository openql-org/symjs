// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file separatevars: write an expression as a product of factors that
 * each depend on fewer symbols (SymPy simplify.separatevars).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Constant, Mul, Pow } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { factor } from '../polys/sympoly';
import { expand } from './expand';
import { posify } from './powsimp';
import { first, getOrThrow } from '../core/guard';

function sep(e0: Expr, force: boolean): Expr {
  let e = e0;
  if (e.freeSymbols().size < 2) return e;
  if (e instanceof Mul) {
    const args = e.args.map((a) => sep(a, force));
    return args.some((a, i) => a.key !== e.args[i]?.key) ? mul(...args) : e;
  }
  if (e instanceof Pow && !(e.base instanceof Constant && e.base.name === 'E')) e = pow(sep(e.base, force), e.exp);
  e = expand(e, { mul: false, multinomial: false, force });
  const [pe, reps] = force ? posify(e) : [e, new Map<Expr, Expr>()];
  e = xreplace(factor(pe), [...reps]);
  // SymPy then pulls out the factors common to the terms of a sum and factors the rest again; factor
  // has already extracted them (the content and the common powers of the generators, also for
  // non-commutative terms), so a sum that factor leaves has none and is returned as it is
  return e;
}

/**
 * Separate the variables of an expression (SymPy separatevars). With
 * `dict`, returns {symbol: factor, coeff: rest} or undefined.
 */
export function separatevars(
  exIn: ExprLike,
  opts: { symbols?: readonly Sym[]; dict?: boolean; force?: boolean } = {},
): Expr | Map<Sym | 'coeff', Expr> | undefined {
  const e = sep(sympify(exIn), opts.force ?? false);
  if (!opts.dict) return e;
  const symbols = opts.symbols?.length ? [...opts.symbols] : ([...e.freeSymbols()] as Sym[]);
  const ret = new Map<Sym | 'coeff', Expr[]>([...symbols.map((s) => [s, []] as [Sym, Expr[]]), ['coeff', []]]);
  for (const f of e instanceof Mul ? e.args : [e]) {
    const inter = symbols.filter((s) => f.has(s));
    if (inter.length > 1) return undefined;
    getOrThrow(ret, inter.length === 0 ? 'coeff' : first(inter)).push(f);
  }
  return new Map([...ret].map(([k, v]) => [k, mul(...v)] as [Sym | 'coeff', Expr]));
}
