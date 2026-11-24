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
import { Derivative, Dummy, Mul, Pow, S, Sym, UndefFn } from '../core/nodes';
import { NoMatch } from '../core/truth';
import { coeff } from '../core/methods';
import { cancel } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { expand } from '../simplify/expand';
import { solveIcs } from './odesimp';
import { at, cast, first } from '../core/guard';
import { mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';

import { asEquation, linearEqToMatrix } from './solve';
import { allOdeHints, classifyOde as classifyOdeHints, dsolveRaw } from './dsolve';

/** Order of the highest derivative of f in e. */
export function odeOrder(e: Expr, f: UndefFn): number {
  if (!e.has(f)) return 0;
  if (e instanceof Derivative) {
    const count = e.variableCount.reduce((n, [, k]) => n + k, 0);
    return e.expr.equals(f) ? count : count + Math.max(0, ...e.expr.args.map((arg) => odeOrder(arg, f)));
  }
  return Math.max(0, ...e.args.map((arg) => odeOrder(arg, f)));
}

/** Classify two canonical first-order velocities, with u and v standing for the functions. */
function nonlinearType(F: Expr, G: Expr, u: Sym, v: Sym, t: Expr): string | typeof NoMatch {
  if (!F.has(t) && !G.has(t)) {
    const factors = F instanceof Mul ? F.args : [F];
    const commonRatio = cancel(mul(G, pow(F, -1)));
    const power = factors.find((e) => e.equals(u) || (e instanceof Pow && e.base.equals(u) && !e.exp.has(u) && !e.exp.has(v))) ?? S.One;
    if (!cancel(mul(power, commonRatio)).has(u)) return 'type1';
    const exponential = factors.find((e) => e instanceof Pow && e.base.equals(S.E) && !mul(e.exp, pow(u, -1)).has(u) && !e.exp.has(v));
    if (exponential && !cancel(mul(exponential, commonRatio)).has(u)) return 'type2';
    return 'type3';
  }
  const ratio = cancel(mul(F, pow(G, -1)));
  if (!ratio.has(t) && separatevars(ratio, { symbols: [u, v], dict: true }) instanceof Map) return 'type4';
  return NoMatch;
}

/** Classify a system by its derivative orders, coefficients and linearity. */
export function classifySysode(eqs: readonly ExprLike[], funcs?: readonly UndefFn[]): Map<string, unknown> {
  const equations = eqs.map((e) => expand(asEquation(e)));
  const found = new Map<string, UndefFn>();
  const visit = (e: Expr): void => {
    if (e instanceof Derivative && e.expr instanceof UndefFn) found.set(e.expr.key, e.expr);
    e.args.forEach(visit);
  };
  equations.forEach(visit);
  const functions = funcs ?? [...found.values()];
  if (!functions.length) throw new TypeError('classifySysode: no dependent functions');
  const orders = new Map(functions.map((f) => [f, Math.max(...equations.map((e) => odeOrder(e, f)))]));
  const jets = [...orders].flatMap(([f, order]) => Array.from({ length: order + 1 }, (_, k) => ({ f, k, jet: k === 0 ? f : new Derivative([f, first(f.args), sympify(k)]) })));
  const variables = jets.map((_, i) => new Dummy(`jet${i}`));
  const replacements = jets.map(({ jet }, i): [Expr, Expr] => [jet, at(variables, i)]);
  const substituted = equations.map((e) => xreplace(e, replacements));
  const coefficients = new Map<readonly [number, UndefFn, number], Expr>();
  const back = replacements.map(([jet, v]): [Expr, Expr] => [v, jet]);
  for (const [i, equation] of substituted.entries()) for (const [j, { f, k }] of jets.entries()) coefficients.set([i, f, k], xreplace(coeff(equation, at(variables, j)), back));
  const linear = linearEqToMatrix(substituted, variables) !== undefined;
  let type: string | typeof NoMatch = NoMatch;
  if (!linear && functions.length === 2 && equations.length === 2 && [...orders.values()].every((k) => k === 1)) {
    const system = linearEqToMatrix(substituted, [at(variables, 1), at(variables, 3)]);
    if (system && !system[0].det().equals(0)) {
      const rhs = system[0].inv().mul(system[1]);
      type = nonlinearType(rhs.get(0, 0), rhs.get(1, 0), first(variables), at(variables, 2), first(first(functions).args));
    }
  }
  return new Map<string, unknown>([
    ['no_of_equation', equations.length], ['eq', equations], ['func', functions], ['order', orders],
    ['func_coeff', coefficients], ['is_linear', linear], ['type_of_equation', type],
  ]);
}

/**
 * Options of dsolve: initial conditions, the hint, and for the lie_group
 * hint the infinitesimals xi(x, f(x)) and eta(x, f(x)) of a known symmetry.
 */
export interface DsolveOptions {
  ics?: [Expr, ExprLike][];
  hint?: string;
  xi?: ExprLike;
  eta?: ExprLike;
  n?: number;
  x0?: ExprLike;
}

const isExprList = <T>(v: T | readonly T[] | undefined): v is readonly T[] => Array.isArray(v);

/**
 * Solves an ordinary differential equation, or a system of them, for the
 * unknown functions with SymPy's classification hints. The result is
 * `Eq(f(x), solution)`; an array of equations when the general solution has
 * several branches. A system gives `[Eq(f(t), ...), Eq(g(t), ...)]`, or an array
 * of such arrays when it has several families of solutions.
 *
 * @param eqIn - The equation (an expression equal to zero, or an `Eq`), or the
 *   equations of a system.
 * @param fx - The unknown function applied to its variable (`f(x)`), or the
 *   functions of a system; found from the equation when omitted.
 * @param opts - `ics` gives initial conditions as pairs, such as
 *   `[[f(0), 1], [Subs(Derivative(f(x), x), x, 0), 0]]`; `hint` selects a
 *   method (`'all'` returns the solution of every applicable hint); `n` and
 *   `x0` set the order and the point of a power series solution.
 * @returns The solution.
 * @see SymPy `sympy.solvers.ode.ode.dsolve`
 * @example
 * ```ts
 * import { dsolve, ex, SymFunction, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const f = SymFunction('f');
 * dsolve(ex`Derivative(f(x), x, 2) + 9*f(x)`, f(x)); // => Eq(f(x), C1*sin(3*x) + C2*cos(3*x))
 * dsolve(ex`Derivative(f(x), x) - f(x)`, f(x), { ics: [[f(0), 2]] }); // => Eq(f(x), 2*exp(x))
 * ```
 */
export function dsolve(eqIn: ExprLike, fx: Expr | undefined, opts: DsolveOptions & { hint: 'all' }): ReturnType<typeof allOdeHints>;
export function dsolve(eqIn: ExprLike | readonly ExprLike[], fx?: Expr | readonly Expr[], opts?: DsolveOptions): Expr | Expr[] | Expr[][];
export function dsolve(eqIn: ExprLike | readonly ExprLike[], fx?: Expr | readonly Expr[], opts: DsolveOptions = {}): Expr | Expr[] | Expr[][] | ReturnType<typeof allOdeHints> {
  // a system of equations: a list of solutions, or a list of solution lists (SymPy)
  if (isExprList(eqIn)) {
    const solutions = dsolveSystem(eqIn, isExprList(fx) ? fx.map((f) => cast(f, UndefFn, 'unknown function')) : undefined, undefined, opts.ics === undefined ? undefined : new Map(opts.ics));
    return solutions.length === 1 ? first(solutions) : solutions;
  }
  if (isExprList(fx)) throw new TypeError('dsolve: the unknown function f(x) is required');
  const dependent = fx ?? unknownFunction(asEquation(eqIn));
  if (opts.hint === 'all') return allOdeHints(asEquation(eqIn), cast(dependent, UndefFn));
  return dsolveSingle(eqIn, dependent, opts);
}

/** SymPy _preprocess: the one function whose derivatives the equation contains. */
function unknownFunction(eq: Expr): Expr {
  const fs = new Map<string, Expr>();
  const go = (e: Expr): void => {
    if (e instanceof Derivative && e.expr instanceof UndefFn) fs.set(e.expr.key, e.expr);
    e.args.forEach(go);
  };
  go(eq);
  if (fs.size !== 1) throw new TypeError('dsolve: the unknown function f(x) is required');
  return first([...fs.values()]);
}

/** dsolve of a single equation. */
function dsolveSingle(eqIn: ExprLike, fx: Expr, opts: DsolveOptions): Expr | Expr[] {
  if (!(fx instanceof UndefFn) || fx.args.length !== 1 || !(fx.args[0] instanceof Sym)) {
    throw new TypeError('dsolve: f(x) with a single symbol argument expected');
  }
  const x = fx.args[0];
  const eq = asEquation(eqIn);
  const n = odeOrder(eq, fx);
  if (n === 0) throw new TypeError('dsolve: not a differential equation');
  if (opts.hint === '1st_power_series') {
    const ics = opts.ics ?? [];
    const terms = opts.n ?? 6;
    if (!Number.isSafeInteger(terms) || terms < 1) throw new RangeError('a positive Taylor series length is required');
    const condition = ics[0];
    const point = condition ? initialCondition(fx, x, ...condition)[0] : sympify(opts.x0 ?? 0);
    if (ics.length > 1 || (condition && !(condition[0] instanceof UndefFn))) throw new RangeError('expected one function value at the expansion point');
    const value = condition ? sympify(condition[1]) : new Sym('C1');
    const solutions = dsolveRaw(eq, fx, opts.hint, undefined, { point, value, terms });
    if (!solutions.length) throw new NotImplementedError('no Taylor series solution at the expansion point');
    return first(solutions);
  }
  const viaHints = dsolveRaw(eq, fx, opts.hint, opts.xi !== undefined && opts.eta !== undefined ? { xi: opts.xi, eta: opts.eta } : undefined);
  // SymPy raises NotImplementedError when no hint matches
  if (!viaHints.length) throw new NotImplementedError('dsolve: unsupported equation');
  const ics = opts.ics;
  if (!ics?.length) return viaHints.length === 1 ? first(viaHints) : viaHints;
  for (const [condition, v] of ics) initialCondition(fx, x, condition, v);
  const out: Expr[] = [];
  for (const sol of viaHints) {
    const constants = [...sol.freeSymbols()].filter((s): s is Sym => s instanceof Sym && /^C\d+$/.test(s.name) && !eq.has(s));
    try {
      out.push(xreplace(sol, [...solveIcs([sol], [fx], constants, new Map(ics))]));
    } catch (error) {
      if (!(error instanceof RangeError) || viaHints.length === 1) throw error;
    }
  }
  if (!out.length) throw new RangeError('no solution satisfies the initial conditions');
  return out.length === 1 ? first(out) : out;
}

/** Validate a function or derivative initial condition and return its point and order. */
function initialCondition(fx: UndefFn, x: Sym, cond: Expr, v: ExprLike): [Expr, number] {
  const val = sympify(v);
  if (cond instanceof SubsNode || cond instanceof Derivative) {
    const deriv = cond instanceof SubsNode ? cond.expr : cond;
    const old = cond instanceof SubsNode ? first(cond.variables) : x;
    // Derivative(f(y), y) is f(x).diff(x).subs(x, y); Derivative(f(a), (x, k)) with a free of x also stands for f^(k)(a)
    const at0 = cond instanceof Derivative && cond.expr instanceof UndefFn && cond.expr.args.length === 1 && !first(cond.expr.args).has(x) && first(cond.variableCount)[0].key === x.key;
    const point = cond instanceof SubsNode ? first(cond.point) : at0 ? first(cond.expr.args) : first(cond.variableCount)[0];
    if (
      !(deriv instanceof Derivative) || !(deriv.expr instanceof UndefFn) || deriv.expr.name !== fx.name || deriv.expr.args.length !== 1 ||
      deriv.variableCount.length !== 1 || old.key !== x.key || point.has(x) || [...val.freeSymbols()].some((s) => s.equals(x))
    ) {
      throw new RangeError('dsolve: invalid boundary conditions for Derivatives');
    }
    return [point, first(deriv.variableCount)[1]];
  } else if (cond instanceof UndefFn) {
    if (cond.name !== fx.name || cond.args.length !== 1 || first(cond.args).has(x) || [...val.freeSymbols()].some((s) => s.equals(x))) {
      throw new RangeError('dsolve: invalid boundary conditions for Function');
    }
    return [first(cond.args), 0];
  } else {
    throw new RangeError('dsolve: enter boundary conditions of the form [[f(point), value], [Subs(Derivative(f(x), (x, order)), x, point), value]]');
  }
}

/** Classify an ODE after validating any supplied initial conditions. */
export function classifyOde(eq: ExprLike, fx: UndefFn, opts: Pick<DsolveOptions, 'ics'> = {}): string[] {
  if (fx.args.length !== 1) throw new RangeError('expected a function of one independent variable');
  const x = cast(first(fx.args), Sym, 'independent variable');
  for (const [condition, value] of opts.ics ?? []) initialCondition(fx, x, condition, value);
  return classifyOdeHints(eq, fx);
}

export { homogeneousOrder } from './homogeneous';

registerSingleOdeSolver((eq, fx) => dsolveSingle(eq, fx, {}));
