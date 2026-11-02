// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file separatevars: write an expression as a product of factors that
 * each depend on fewer symbols (SymPy simplify.separatevars).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Constant, Mul, Pow } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import { splitCoeff } from '../core/ops';
import { xreplace } from '../core/traverse';
import { factor } from '../polys/sympoly';
import { expand } from './expand';
import { posify } from './powsimp';

function sep(e0: Expr, force: boolean): Expr {
  let e = e0;
  if (e.freeSymbols().size < 2) return e;
  if (e instanceof Mul) {
    const args = e.args.map((a) => separatevars(a, { force }) as Expr);
    return args.some((a, i) => a.key !== e.args[i]!.key) ? mul(...args) : e;
  }
  if (e instanceof Pow && !(e.base instanceof Constant && e.base.name === 'E')) e = pow(separatevars(e.base, { force }) as Expr, e.exp);
  e = expand(e, { mul: false, multinomial: false, force });
  const [pe, reps] = force ? posify(e) : [e, new Map<Expr, Expr>()];
  e = xreplace(factor(pe), [...reps]);
  if (!(e instanceof Add)) return e;
  const cSets = e.args.map((a) => new Map((a instanceof Mul ? a.args : [a]).map((f) => [f.key, f] as const)));
  let common = [...cSets[0]!.values()].filter((f) => cSets.every((s) => s.has(f.key)));
  let commonc = splitCoeff(mul(...common))[1];
  common = commonc instanceof Mul ? [...commonc.args] : [commonc];
  const commonKeys = new Set(common.map((f) => f.key));
  let nonsepar: Expr = e.args.map((a) => mul(...(a instanceof Mul ? a.args : [a]).filter((f) => !commonKeys.has(f.key))))
    .reduce((acc, t) => acc.add(t));
  if (nonsepar.freeSymbols().size > 1) {
    const [pn, r2] = force ? posify(nonsepar) : [nonsepar, new Map<Expr, Expr>()];
    const fx = xreplace(factor(pn), [...r2]);
    if (!(fx instanceof Add)) nonsepar = fx;
  }
  commonc = mul(...common);
  return mul(commonc, nonsepar);
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
    if (inter.length === 0) ret.get('coeff')!.push(f);
    else ret.get(inter[0]!)!.push(f);
  }
  return new Map([...ret].map(([k, v]) => [k, mul(...v)] as [Sym | 'coeff', Expr]));
}
