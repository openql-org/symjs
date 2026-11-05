// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 solvers/ode/single.py, BSD-3-Clause; see LICENSE.

/**
 * @file The ODE problem and solver objects of SymPy's
 * `sympy.solvers.ode.single`: SingleODEProblem (the properties of one ODE
 * that the solvers share), the SingleODESolver base class and the
 * NthAlgebraic solver. The other hints of that module are the solver
 * functions of `solvers/dsolve.ts`, which `dsolve` runs.
 */

import type { Expr } from '../../core/nodes';
import { Derivative, Dummy, Integral, Mul, Pow, Rational, S, Sym, UndefFn } from '../../core/nodes';
import { at, cast, first } from '../../core/guard';
import { add } from '../../core/ops';
import { Eq } from '../../core/logic';
import { NotImplementedError } from '../../core/errors';
import { xreplace } from '../../core/traverse';
import { ordered } from '../../core/match';
import { derivative } from '../../core/undef';
import { NoMatch, type NoMatchResult } from '../../core/truth';
import { diff } from '../../calculus/diff';
import { doit } from '../../calculus/doit';
import { expand } from '../../simplify/expand';
import { simplify } from '../../simplify/simplify';
import { numberedSymbols } from '../../utilities/iterables';
import { solve } from '../solve';

/** SymPy ODEMatchError: the solver does not match the equation. */
export class ODEMatchError extends NotImplementedError {
  constructor(message: string) {
    super(message);
    this.name = 'ODEMatchError';
  }
}

/** The order of the highest derivative of f in e (SymPy ode_order). */
function orderIn(e: Expr, f: UndefFn): number {
  if (e instanceof Derivative && e.expr.key === f.key) return e.variableCount.reduce((s, [, k]) => s + k, 0);
  return Math.max(0, ...e.args.map((a) => orderIn(a, f)));
}

/** The k-th derivative of f(x) in x (f(x) itself for k = 0). */
const nthDerivative = (f: UndefFn, x: Sym, k: number): Expr => (k === 0 ? f : derivative(f, [[x, k]]));

/**
 * SymPy SingleODEProblem: an ODE eq in the unknown function func of the
 * independent variable sym, with the properties the solvers share.
 */
export class SingleODEProblem {
  constructor(
    readonly eq: Expr,
    readonly func: UndefFn,
    readonly sym: Sym,
  ) {}

  /** SymPy order: the order of the highest derivative of func. */
  get order(): number {
    return orderIn(this.eq, this.func);
  }

  /** SymPy eq_expanded: the expanded equation. */
  get eqExpanded(): Expr {
    return expand(this.eq);
  }

  /** SymPy is_autonomous: the equation does not depend on sym except through func. */
  get isAutonomous(): boolean {
    // (func and its derivatives replaced by a symbol u)
    const dependsOnSym = (e: Expr): boolean =>
      !(e.key === this.func.key || (e instanceof Derivative && e.expr.key === this.func.key)) && (e.key === this.sym.key || e.args.some(dependsOnSym));
    return !dependsOnSym(this.eq);
  }

  /** SymPy iter_numbered_constants: C1, C2, ... skipping the symbols and function names of the equation. */
  iterNumberedConstants(start = 1, prefix = 'C'): Generator<Sym, never, undefined> {
    const exclude: Expr[] = [...this.eq.freeSymbols()];
    const names = new Set<string>();
    const visit = (e: Expr): void => {
      if (e instanceof UndefFn) names.add(e.name);
      e.args.forEach(visit);
    };
    visit(this.eq);
    return numberedSymbols(prefix, { start, exclude: [...exclude, ...[...names].map((n) => new Sym(n))] });
  }

  /** SymPy get_numbered_constants: the first num constants of iterNumberedConstants. */
  getNumberedConstants(num = 1, start = 1, prefix = 'C'): Sym[] {
    const it = this.iterNumberedConstants(start, prefix);
    return Array.from({ length: num }, () => it.next().value);
  }

  /**
   * SymPy get_linear_coefficients: the coefficients a_k(x) of
   * a_n(x) y^(n) + ... + a_0(x) y + B(x) = 0 by order k, with B(x) at -1,
   * or NoMatch when eq is not linear in func and its derivatives.
   */
  getLinearCoefficients(eq: Expr, func: UndefFn, order: number): Map<number, Expr> | NoMatchResult {
    const x = cast(first(func.args), Sym, 'independent variable');
    const ts = Array.from({ length: order + 1 }, () => new Dummy('t'));
    // the highest derivatives first, so that f(x) inside them is not replaced
    const reps = ts.map((t, k) => [nthDerivative(func, x, k), t] as const).reverse();
    const e = reps.reduce((acc, [d, t]) => xreplace(acc, [[d, t]]), eq);
    const coeffs = ts.map((t) => diff(e, t));
    const rhs = xreplace(e, ts.map((t) => [t, S.Zero] as const));
    const linear = [...coeffs, rhs].every((c) => !c.has(func) && !ts.some((t) => c.has(t)));
    if (!linear) return NoMatch;
    const out = new Map<number, Expr>(coeffs.map((c, k) => [k, c]));
    out.set(-1, rhs);
    return out;
  }
}

/** SymPy SingleODESolver: the base class of the solvers of one ODE. */
export abstract class SingleODESolver {
  /** The hint name (the argument of dsolve). */
  abstract readonly hint: string;
  /** Whether the solver has an _Integral hint. */
  abstract readonly hasIntegral: boolean;
  #matched: boolean | undefined;

  constructor(readonly odeProblem: SingleODEProblem) {}

  /** SymPy matches: whether the solver applies to the equation. */
  matches(): boolean {
    this.#matched ??= this.matchesImpl();
    return this.#matched;
  }

  /** SymPy get_general_solution: the general solutions; throws ODEMatchError when the solver does not match. */
  getGeneralSolution(opts: { simplify?: boolean } = {}): Expr[] {
    if (!this.matches()) throw new ODEMatchError(`${this.hint} solver cannot solve:\n${String(this.odeProblem.eq)}`);
    return this.generalSolution(opts.simplify ?? true);
  }

  protected abstract matchesImpl(): boolean;
  protected abstract generalSolution(simplifyFlag: boolean): Expr[];
}

/**
 * The solutions for func of an equation in func and its derivatives with
 * respect to x, treating differentiation as an invertible function: each
 * factor is solved for the one derivative D^k(func) it contains, and the
 * value is integrated k times, adding a constant Dummy('C') each time
 * (SymPy NthAlgebraic with its diffx class). Throws NotImplementedError
 * when a factor cannot be solved so.
 */
function solveDifferentiationAlgebraically(eq: Expr, func: UndefFn, x: Sym): Expr[] {
  const factors = eq instanceof Mul ? eq.args : [eq];
  const out: Expr[] = [];
  for (const m0 of factors) {
    // a power is zero where its base is (SymPy _solve of a Pow)
    const m = m0 instanceof Pow && m0.exp instanceof Rational && m0.exp.isPositive ? m0.base : m0;
    if (!m.has(func)) continue;
    const gens = new Map<string, number>();
    const visit = (e: Expr): void => {
      if (e.key === func.key) gens.set(e.key, 0);
      else if (e instanceof Derivative && e.expr.key === func.key) gens.set(e.key, orderIn(e, func));
      else e.args.forEach(visit);
    };
    visit(m);
    if (gens.size !== 1) throw new NotImplementedError('nth_algebraic: the equation is not algebraic in one derivative');
    const k = first([...gens.values()]);
    const t = new Dummy('t');
    for (const r of solve(xreplace(m, [[nthDerivative(func, x, k), t]]), t)) {
      let v = r;
      for (let i = 0; i < k; i++) v = add(new Integral([v, x]), new Dummy('C'));
      out.push(v);
    }
  }
  // (SymPy's solve returns the solutions of the factors as one ordered list)
  return ordered(out);
}

/**
 * SymPy NthAlgebraic: an equation that can be solved algebraically for
 * func when differentiation is treated as an invertible function, such as
 * f(x)*(f'(x)**2 - 1) = 0 (f = 0 or f' = 1 or f' = -1). The constants of
 * the general solution are Dummy('C') symbols.
 */
export class NthAlgebraic extends SingleODESolver {
  readonly hint = 'nth_algebraic';
  readonly hasIntegral = true;
  #solutions: Expr[] = [];

  protected matchesImpl(): boolean {
    const { eq, func, sym } = this.odeProblem;
    let solns: Expr[];
    try {
      solns = solveDifferentiationAlgebraically(eq, func, sym);
    } catch {
      // (SymPy catches the NotImplementedError of solve)
      solns = [];
    }
    this.#solutions = solns.map((s) => Eq(func, simplify(doit(s))));
    return this.#solutions.length > 0;
  }

  protected generalSolution(): Expr[] {
    return this.#solutions;
  }
}

/**
 * The nth_algebraic solutions of dsolve, with the constants of each
 * solution as symbols C1, C2, ... for odesimp to renumber; undefined when
 * the hint does not match.
 */
export function nthAlgebraicSolutions(eq: Expr, func: UndefFn, x: Sym): Expr[] | undefined {
  const solver = new NthAlgebraic(new SingleODEProblem(eq, func, x));
  if (!solver.matches()) return undefined;
  return solver.getGeneralSolution().map((s) => {
    const cs = [...s.freeSymbols()].filter((c): c is Dummy => c instanceof Dummy && c.name === 'C');
    const fresh = new SingleODEProblem(eq, func, x).getNumberedConstants(cs.length);
    return xreplace(s, cs.map((c, i) => [c, at(fresh, i)] as const));
  });
}
