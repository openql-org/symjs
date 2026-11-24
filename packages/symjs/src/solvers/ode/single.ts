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

import { Expr } from '../../core/nodes';
import { Derivative, Dummy, Integral, Mul, Pow, Rational, S, Sym, UndefFn } from '../../core/nodes';
import { at, cast, expectType, first, getOrThrow } from '../../core/guard';
import { add, exp, mul, pow } from '../../core/ops';
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

/**
 * The solver does not match the equation.
 *
 * @see SymPy `sympy.solvers.ode.single.ODEMatchError`
 */
export class ODEMatchError extends NotImplementedError {
  /**
   * Creates an ODEMatchError instance.
   *
   * @param message - The reason for the error.
   */
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

function iterNumberedConstants(equations: readonly Expr[], start: number, prefix: string): Generator<Sym, never, undefined> {
  const exclude = equations.flatMap((eq) => [...eq.freeSymbols()]);
  const names = new Set<string>();
  const visit = (e: Expr): void => {
    if (e instanceof UndefFn) names.add(e.name);
    e.args.forEach(visit);
  };
  equations.forEach(visit);
  return numberedSymbols(prefix, { start, exclude: [...exclude, ...[...names].map((n) => new Sym(n))] });
}

/**
 * Allocates integration constants distinct from symbols and functions in the input.
 *
 * @param eq - The equation, or an expression equal to zero.
 * @param num - The number of fresh constants.
 * @param start - The first subscript to try.
 * @param prefix - The base name for the constants.
 * @returns Fresh integration constants that do not collide with names in the equation.
 * @throws RangeError when the input is neither an expression nor a sequence of expressions.
 * @see SymPy `sympy.solvers.ode.ode.get_numbered_constants`
 */
export function getNumberedConstants(eq: Expr | readonly Expr[], num = 1, start = 1, prefix = 'C'): Sym[] {
  const equations = eq instanceof Expr ? [eq] : eq;
  if (!Array.isArray(equations)) throw new RangeError('expected an expression or sequence');
  const it = iterNumberedConstants(equations, start, prefix);
  return Array.from({ length: num }, () => it.next().value);
}

/**
 * An ODE eq in the unknown function func of the
 * independent variable sym, with the properties the solvers share.
 *
 * @see SymPy `sympy.solvers.ode.single.SingleODEProblem`
 * @example
 * ```ts
 * import { AppliedUndef, SingleODEProblem, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * new SingleODEProblem(ex`Derivative(f(x), x) - f(x)`, new AppliedUndef('f', [x]), x).order; // => 1
 * ```
 */
export class SingleODEProblem {
  /**
   * Creates a SingleODEProblem instance.
   *
   * @param eq - The equation, or an expression equal to zero.
   * @param func - The dependent function applied to its arguments.
   * @param sym - The independent variable.
   */
  constructor(
    /** The differential equation expressed with zero right-hand side. */
    readonly eq: Expr,
    /** The unknown function applied to its independent variable. */
    readonly func: UndefFn,
    /** The independent variable of the equation. */
    readonly sym: Sym,
  ) {}

  /**
   * Represents the order of the highest derivative of func.
   *
   * @returns The order of the highest derivative of func.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.order`
   */
  get order(): number {
    return orderIn(this.eq, this.func);
  }

  /**
   * Represents the expanded equation.
   *
   * @returns The expanded equation.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.eq_expanded`
   */
  get eqExpanded(): Expr {
    return expand(this.eq);
  }

  /**
   * The equation does not depend on sym except through func.
   *
   * @returns Whether the equation is independent of the variable except through the unknown function.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.is_autonomous`
   */
  get isAutonomous(): boolean {
    // (func and its derivatives replaced by a symbol u)
    const dependsOnSym = (e: Expr): boolean =>
      !(e.key === this.func.key || (e instanceof Derivative && e.expr.key === this.func.key)) && (e.key === this.sym.key || e.args.some(dependsOnSym));
    return !dependsOnSym(this.eq);
  }

  /**
   * C1, C2, ... skipping the symbols and function names of the equation.
   *
   * @param start - The first subscript to try.
   * @param prefix - The base name for the constants.
   * @returns An iterator over fresh integration constants.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.iter_numbered_constants`
   */
  iterNumberedConstants(start = 1, prefix = 'C'): Generator<Sym, never, undefined> {
    return iterNumberedConstants([this.eq], start, prefix);
  }

  /**
   * The first num constants of iterNumberedConstants.
   *
   * @param num - The number of fresh constants.
   * @param start - The first subscript to try.
   * @param prefix - The base name for the constants.
   * @returns Fresh integration constants that do not collide with names in the equation.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.get_numbered_constants`
   */
  getNumberedConstants(num = 1, start = 1, prefix = 'C'): Sym[] {
    const it = this.iterNumberedConstants(start, prefix);
    return Array.from({ length: num }, () => it.next().value);
  }

  /**
   * The coefficients a_k(x) of
   * a_n(x) y^(n) + ... + a_0(x) y + B(x) = 0 by order k, with B(x) at -1,
   * or NoMatch when eq is not linear in func and its derivatives.
   *
   * @param eq - The equation, or an expression equal to zero.
   * @param func - The dependent function applied to its arguments.
   * @param order - The highest derivative order to include.
   * @returns The coefficients by derivative order, with the constant term at −1, or `NoMatch`.
   * @see SymPy `sympy.solvers.ode.single.SingleODEProblem.get_linear_coefficients`
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

/**
 * The base class of the solvers of one ODE.
 *
 * @see SymPy `sympy.solvers.ode.single.SingleODESolver`
 * @example
 * ```ts
 * import { AppliedUndef, FirstLinear, SingleODEProblem, SingleODESolver, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const problem = new SingleODEProblem(ex`Derivative(f(x), x) - f(x)`, new AppliedUndef('f', [x]), x);
 * new FirstLinear(problem) instanceof SingleODESolver; // => True
 * ```
 */
export class SingleODESolver {
  /** The hint name (the argument of dsolve). */
  readonly hint: string = '';
  /** Determines whether the solver has an _Integral hint. */
  readonly hasIntegral: boolean = false;
  #matched: boolean | undefined;

  /**
   * Creates a SingleODESolver instance.
   *
   * @param odeProblem - The differential equation and dependent function to solve for.
   */
  constructor(
    /** The differential equation and its dependent and independent variables. */
    readonly odeProblem: SingleODEProblem) {}

  /**
   * Determines whether the solver applies to the equation.
   *
   * @returns Whether the equation belongs to this class.
   * @see SymPy `sympy.solvers.ode.single.SingleODESolver.matches`
   */
  matches(): boolean {
    this.#matched ??= this.matchesImpl();
    return this.#matched;
  }

  /**
   * The general solutions; throws ODEMatchError when the solver does not match.
   *
   * @param opts - `simplify` simplifies the result.
   * @returns The general solutions.
   * @throws ODEMatchError when the equation does not match the solver.
   * @see SymPy `sympy.solvers.ode.single.SingleODESolver.get_general_solution`
   */
  getGeneralSolution(opts: { simplify?: boolean } = {}): Expr[] {
    if (!this.matches()) throw new ODEMatchError(`${this.hint} solver cannot solve:\n${String(this.odeProblem.eq)}`);
    return this.generalSolution(opts.simplify ?? true);
  }

  protected matchesImpl(): boolean { throw new NotImplementedError('solver matching is not implemented'); }
  protected generalSolution(_simplifyFlag: boolean): Expr[] { throw new NotImplementedError('general solution is not implemented'); }
}

/**
 * The integrating-factor solution of y' + P(x)*y = Q(x).
 *
 * @see SymPy `sympy.solvers.ode.single.FirstLinear`
 * @example
 * ```ts
 * import { AppliedUndef, FirstLinear, SingleODEProblem, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const problem = new SingleODEProblem(ex`Derivative(f(x), x) - f(x)`, new AppliedUndef('f', [x]), x);
 * new FirstLinear(problem).matches(); // => True
 * ```
 */
export class FirstLinear extends SingleODESolver {
  /**
   * The classification hint selecting this solver.
   *
   * @see SymPy `sympy.solvers.ode.single.FirstLinear.hint`
   */
  override readonly hint = '1st_linear';
  /**
   * Indicates whether an unevaluated integral hint is available.
   *
   * @see SymPy `sympy.solvers.ode.single.FirstLinear.has_integral`
   */
  override readonly hasIntegral = true;
  protected override matchesImpl(): boolean {
    const { eqExpanded, func, order } = this.odeProblem;
    return order === 1 && this.odeProblem.getLinearCoefficients(eqExpanded, func, order) instanceof Map;
  }
  protected override generalSolution(): Expr[] {
    const { eqExpanded, func, sym } = this.odeProblem;
    const cs = this.odeProblem.getLinearCoefficients(eqExpanded, func, 1);
    const coefficients = expectType(cs, (v): v is Map<number, Expr> => v instanceof Map, 'linear coefficients');
    const inv = pow(getOrThrow(coefficients, 1), -1);
    const factor = exp(new Integral([mul(getOrThrow(coefficients, 0), inv), sym]));
    const integral = new Integral([mul(-1, getOrThrow(coefficients, -1), inv, factor), sym]);
    return [Eq(func, mul(add(first(this.odeProblem.getNumberedConstants()), integral), pow(factor, -1)))];
  }
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
 * An equation that can be solved algebraically for
 * func when differentiation is treated as an invertible function, such as
 * f(x)*(f'(x)**2 - 1) = 0 (f = 0 or f' = 1 or f' = -1). The constants of
 * the general solution are Dummy('C') symbols.
 *
 * @see SymPy `sympy.solvers.ode.single.NthAlgebraic`
 * @example
 * ```ts
 * import { AppliedUndef, NthAlgebraic, SingleODEProblem, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const problem = new SingleODEProblem(ex`Derivative(f(x), (x, 2))`, new AppliedUndef('f', [x]), x);
 * new NthAlgebraic(problem).matches(); // => True
 * ```
 */
export class NthAlgebraic extends SingleODESolver {
  /**
   * The classification hint selecting this solver.
   *
   * @see SymPy `sympy.solvers.ode.single.NthAlgebraic.hint`
   */
  override readonly hint = 'nth_algebraic';
  /**
   * Indicates whether an unevaluated integral hint is available.
   *
   * @see SymPy `sympy.solvers.ode.single.NthAlgebraic.has_integral`
   */
  override readonly hasIntegral = true;
  #solutions: Expr[] = [];

  protected override matchesImpl(): boolean {
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

  protected override generalSolution(): Expr[] {
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
