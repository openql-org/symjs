// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Ordinary differential equations: the dsolve entry point (single
 * equations through SymPy's hints in solvers/dsolve.ts, systems through
 * solvers/odesystem.ts) and initial conditions.
 */

import { NotImplementedError } from '../core/errors';
import { dsolveSystem, registerSingleOdeSolver } from './odesystem';
import { SubsNode } from '../core/subsnode';
import type { Expr, ExprLike } from '../core/nodes';
import { Derivative, Rel, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { at, cast, first } from '../core/guard';
import { add, mul, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { asEquation, linsolve } from './solve';
import { dsolveRaw } from './dsolve';

/** Order of the highest derivative of f in e. */
export function odeOrder(e: Expr, f: UndefFn): number {
  let n = 0;
  const go = (x: Expr) => {
    if (x instanceof Derivative && x.expr.key === f.key) n = Math.max(n, x.variableCount.reduce((s, [, k]) => s + k, 0));
    x.args.forEach(go);
  };
  go(e);
  return n;
}

const isExprList = <T>(v: T | readonly T[] | undefined): v is readonly T[] => Array.isArray(v);

/**
 * Solve an ordinary differential equation for f(x) with SymPy's hints
 * (solvers/dsolve.ts). Returns Eq(f(x), solution); like SymPy, a list of
 * equations is returned when the general solution has several branches.
 * A system gives [Eq(f(t), ...), Eq(g(t), ...)], or a list of such lists when
 * it has several solution families.
 * ics lists initial conditions, e.g. [[f(0), 1], [Subs(Derivative(f(x), x), x, 0), 0]].
 */
export function dsolve(eqIn: ExprLike | readonly ExprLike[], fx?: Expr | readonly Expr[], opts: { ics?: [Expr, ExprLike][]; hint?: string } = {}): Expr | Expr[] | Expr[][] {
  // a system of equations: a list of solutions, or a list of solution lists (SymPy)
  if (isExprList(eqIn)) return dsolveSystem(eqIn, isExprList(fx) ? fx.map((f) => cast(f, UndefFn, 'unknown function')) : undefined);
  if (isExprList(fx) || fx === undefined) throw new TypeError('dsolve: the unknown function f(x) is required');
  return dsolveSingle(eqIn, fx, opts);
}

/** dsolve of a single equation. */
function dsolveSingle(eqIn: ExprLike, fx: Expr, opts: { ics?: [Expr, ExprLike][]; hint?: string }): Expr | Expr[] {
  if (!(fx instanceof UndefFn) || fx.args.length !== 1 || !(fx.args[0] instanceof Sym)) {
    throw new TypeError('dsolve: f(x) with a single symbol argument expected');
  }
  const x = fx.args[0];
  const eq = asEquation(eqIn);
  const n = odeOrder(eq, fx);
  if (n === 0) throw new TypeError('dsolve: not a differential equation');
  const viaHints = dsolveRaw(eq, fx, opts.hint);
  // SymPy raises NotImplementedError when no hint matches
  if (!viaHints?.length) throw new NotImplementedError('dsolve: unsupported equation');
  const ics = opts.ics;
  const out = ics?.length ? viaHints.map((s) => Eq(fx, applyIcs(cast(s, Rel, 'dsolve solution').rhs, fx, x, ics))) : viaHints;
  return out.length === 1 ? first(out) : out;
}

/**
 * SymPy solve_ics, with the checks of classify_ode: the conditions are
 * f(x0) = value and f(x).diff(x, k).subs(x, x0) = value (a Subs, or the
 * Derivative that substituting a symbol gives; Derivative(f(x0), (x, k)) is
 * also accepted), with x0 and the value free of x; the constants are found by
 * a linear solve.
 */
function applyIcs(sol: Expr, fx: UndefFn, x: Sym, ics: [Expr, ExprLike][]): Expr {
  const cs = [...sol.freeSymbols()].filter((s) => /^C\d+$/.test(s.name));
  const eqs: Expr[] = [];
  for (const [cond, v] of ics) {
    const val = sympify(v);
    if (cond instanceof SubsNode || cond instanceof Derivative) {
      const deriv = cond instanceof SubsNode ? cond.expr : cond;
      const old = cond instanceof SubsNode ? first(cond.variables) : x;
      // Derivative(f(y), y) is f(x).diff(x).subs(x, y); Derivative(f(a), (x, k)) with a free of x also stands for f^(k)(a)
      const at0 = cond instanceof Derivative && cond.expr instanceof UndefFn && cond.expr.args.length === 1 && !first(cond.expr.args).has(x) && first(cond.variableCount)[0].key === x.key;
      const point = cond instanceof SubsNode ? first(cond.point) : at0 ? first(cond.expr.args) : first(cond.variableCount)[0];
      if (
        !(deriv instanceof Derivative) || !(deriv.expr instanceof UndefFn) || deriv.expr.name !== fx.name || deriv.expr.args.length !== 1 ||
        deriv.variableCount.length !== 1 || old.key !== x.key || point.has(x) || val.has(x)
      ) {
        throw new RangeError('dsolve: invalid boundary conditions for Derivatives');
      }
      const k = first(deriv.variableCount)[1];
      eqs.push(add(xreplace(diff(sol, x, k), [[x, point]]), mul(-1, val)));
    } else if (cond instanceof UndefFn) {
      if (cond.name !== fx.name || cond.args.length !== 1 || first(cond.args).has(x) || val.has(x)) {
        throw new RangeError('dsolve: invalid boundary conditions for Function');
      }
      eqs.push(add(xreplace(sol, [[x, first(cond.args)]]), mul(-1, val)));
    } else {
      throw new RangeError('dsolve: enter boundary conditions of the form [[f(point), value], [Subs(Derivative(f(x), (x, order)), x, point), value]]');
    }
  }
  const s = linsolve(eqs, cs);
  if (!s) throw new RangeError("dsolve: couldn't solve for initial conditions");
  return xreplace(sol, cs.map((c, i) => [c, at(s, i)] as const));
}

export { homogeneousOrder } from './homogeneous';

registerSingleOdeSolver((eq, fx) => dsolveSingle(eq, fx, {}));
