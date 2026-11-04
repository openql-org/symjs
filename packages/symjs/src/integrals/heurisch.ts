// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/heurisch.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The case of SymPy's heuristic Risch algorithm (heurisch) for rational
 * functions of sin(u) and cos(u), u = a*x + b: heurisch rewrites them in
 * tan(u/2) (rewrite=True) and finds an antiderivative that is rational in x
 * and tan(u/2) plus logarithms and arctangents. Here the rational function of
 * t = tan(u/2) is integrated instead and written in heurisch's final form
 * (cancel(F).expand() without the terms free of x).
 */

import type { Expr, Sym } from '../core/nodes';
import { Add, Dummy, Fn, Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { mapBottomUp, xreplace } from '../core/traverse';
import { atan, tan } from '../functions/elementary/elementary';
import { at, defined } from '../core/guard';
import { polyCoefficients } from '../polys/poly';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';

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
