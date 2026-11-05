// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file General functional decomposition and composition (SymPy
 * sympy.solvers.decompogen): f = f_1(f_2(... f_n)) as [f_1, ..., f_n].
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Constant, Fn, Pow, Rel, UndefFn } from '../core/nodes';
import { sympify } from '../core/ops';
import { freeSymbols, subs } from '../core/traverse';
import { at } from '../core/guard';
import { Poly } from '../polys/sympoly';
import { BoolOp } from '../core/boolalg';

const REL_NAMES = { Eq: 'Equality', Ne: 'Unequality', Lt: 'StrictLessThan', Le: 'LessThan', Gt: 'StrictGreaterThan', Ge: 'GreaterThan' } as const;
const isE = (e: Expr): boolean => e instanceof Constant && e.name === 'E';
const hasFree = (e: Expr, x: Expr): boolean => [...freeSymbols(e)].some((s) => s.key === x.key);

/**
 * SymPy decompogen: the general functional decomposition [f_1, ..., f_n] of
 * f in symbol, f = f_1(f_2(... f_n(symbol))); polynomials are decomposed
 * like SymPy decompose.
 */
export function decompogen(fIn: ExprLike, symbolIn: ExprLike): Expr[] {
  const f = sympify(fIn);
  const symbol = sympify(symbolIn);
  if (f instanceof Rel) throw new TypeError(`expecting Expr but got: \`${REL_NAMES[f.op]}\``);
  if (f instanceof BoolOp) throw new TypeError(`expecting Expr but got: \`${f.op}\``);
  if (!hasFree(f, symbol)) return [f];
  // Min/Max: every argument depending on symbol must decompose alike
  if (f instanceof Fn && (f.name === 'Min' || f.name === 'Max')) {
    const args = [...f.args];
    let inner: Expr[] = [];
    let seen = false;
    let last: Expr = symbol;
    for (let i = 0; i < args.length; i++) {
      const a = at(args, i);
      if (!hasFree(a, symbol)) continue;
      let d = decompogen(a, symbol);
      if (d.length === 1) d = [symbol, ...d];
      const rest = d.slice(1);
      if (!seen) {
        inner = rest;
        seen = true;
      }
      // a different decomposition of another argument: no decomposition
      else if (rest.length !== inner.length || rest.some((r, j) => r.key !== at(inner, j).key)) return [f];
      args[i] = at(d, 0);
      last = at(d, 0);
    }
    // (SymPy looks at the outer function of the last argument)
    if (last.key === symbol.key) return [f];
    return [rebuildFn(f, args), ...inner];
  }
  if (f instanceof Fn || f instanceof UndefFn || f instanceof Pow) {
    const arg = f instanceof Pow && isE(f.base) ? f.exp : at(f.args, 0);
    if (arg.key === symbol.key) return [f];
    return [subs(f, [[arg, symbol]]), ...decompogen(arg, symbol)];
  }
  const gens = Poly.from(f).gens.filter((g) => hasFree(g, symbol));
  const g = gens[0];
  if (gens.length === 1 && g !== undefined && g.key !== symbol.key) return [subs(f, [[g, symbol]]), ...decompogen(g, symbol)];
  try {
    return Poly.from(f)
      .decompose()
      .map((p) => p.asExpr());
  } catch {
    // not a univariate polynomial: no decomposition
    return [f];
  }
}

function rebuildFn(f: Fn, args: readonly Expr[]): Expr {
  return subs(f, f.args.map((a, i) => [a, at(args, i)] as const), { simultaneous: true });
}

/**
 * SymPy compogen: the composition g_1(g_2(... g_n)) of the functions g_s of
 * symbol.
 */
export function compogen(gs: readonly ExprLike[], symbolIn: ExprLike): Expr {
  const symbol = sympify(symbolIn);
  const fs = gs.map(sympify);
  let acc = at(fs, fs.length - 1);
  for (let i = fs.length - 2; i >= 0; i--) acc = subs(at(fs, i), [[symbol, acc]]);
  return acc;
}
