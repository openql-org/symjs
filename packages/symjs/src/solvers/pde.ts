// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 solvers/pde.py, BSD-3-Clause; see LICENSE.
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Derivative, Dummy, Integral, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { at, cast, first } from '../core/guard';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { Eq } from '../core/logic';
import { SymFunction } from '../core/undef';
import { SubsNode } from '../core/subsnode';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { NotImplementedError } from '../core/errors';
import { freeSymbols, rebuild, some, subs, xreplace } from '../core/traverse';
import { coeff } from '../core/methods';
import { numAdd, numCmp } from '../core/num';
import { linearEqToMatrix } from '../matrices/linsys';
import { diff } from '../calculus/diff';
import { doit } from '../calculus/doit';
import { integrate } from '../integrals/integrate';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { asEquation, solve } from './solve';
import { dsolve } from './ode';

function dependent(eq: Expr, func?: Expr): UndefFn {
  if (func !== undefined) return cast(func, UndefFn, 'dependent function');
  const functions = new Map<string, UndefFn>();
  const visit = (e: Expr): void => { if (e instanceof UndefFn) functions.set(e.key, e); e.args.forEach(visit); };
  visit(eq);
  if (functions.size !== 1) throw new TypeError('Specify the dependent function of the PDE.');
  return first([...functions.values()]);
}
interface LinearPde { f: UndefFn; x: Sym; y: Sym; a: Expr; b: Expr; c: Expr; forcing: Expr; constant: boolean; }
/** f**n of a coefficient a*f**n (SymPy coeff.match(a*f(x,y)**n)), or undefined. */
function fPower(coefficient: Expr, f: UndefFn): Rational | undefined {
  let n: Rational = S.Zero;
  let a: Expr = S.One;
  for (const factor of coefficient instanceof Mul ? coefficient.args : [coefficient]) {
    if (factor.equals(f)) n = numAdd(n, S.One);
    else if (factor instanceof Pow && factor.base.equals(f) && factor.exp instanceof Rational) n = numAdd(n, factor.exp);
    else a = mul(a, factor);
  }
  return a.equals(0) || a.has(f) ? undefined : n;
}
/**
 * SymPy classify_pde: divide the terms of the expanded equation by the
 * smallest power of f(x,y) in the coefficients of its first derivatives.
 */
function reduced(eq: Expr, f: UndefFn, x: Sym, y: Sym): Expr {
  if (!(eq instanceof Add)) return eq;
  let power: Rational | undefined;
  for (const v of [x, y]) {
    const k = coeff(eq, diff(f, v));
    if (k.equals(1)) continue;
    const n = fPower(k, f);
    if (n !== undefined && (power === undefined || numCmp(n, power) < 0)) power = n;
  }
  if (power === undefined || power.isZero) return eq;
  const den = pow(f, power);
  return add(...eq.args.map((t) => mul(t, pow(den, -1))));
}
function linearPde(eqIn: Expr, f: UndefFn): LinearPde | undefined {
  if (f.args.length !== 2 || !f.args.every((v) => v instanceof Sym)) return undefined;
  const x = cast(at(f.args, 0), Sym), y = cast(at(f.args, 1), Sym);
  const eq = reduced(expand(eqIn), f, x, y);
  const ux = new Dummy('ux'), uy = new Dummy('uy'), u = new Dummy('u');
  const replaced = xreplace(eq, [[diff(f, x), ux], [diff(f, y), uy], [f, u]]);
  if (some(replaced, (e) => e instanceof Derivative)) return undefined;
  const system = linearEqToMatrix([replaced], [ux, uy, u]);
  if (!system) return undefined;
  const a = system[0].get(0, 0), b = system[0].get(0, 1), c = system[0].get(0, 2), forcing = system[1].get(0, 0);
  if (a.equals(0) && b.equals(0)) return undefined;
  return { f, x, y, a, b, c, forcing, constant: [a, b, c].every((v) => !v.has(x) && !v.has(y)) };
}
/** Supported SymPy hints of a first-order linear PDE, in SymPy's order. */
export function classifyPde(equation: ExprLike, func?: Expr): string[] {
  const eq = asEquation(equation), f = dependent(eq, func), m = linearPde(eq, f);
  if (!m) return [];
  if (!m.constant) return ['1st_linear_variable_coeff'];
  return m.forcing.equals(0) ? ['1st_linear_constant_coeff_homogeneous'] : ['1st_linear_constant_coeff', '1st_linear_constant_coeff_Integral'];
}
/**
 * Solve a*x-derivative(f) + b*y-derivative(f) + c*f = forcing(x,y).
 * With constant coefficients the arbitrary function is F(b*x-a*y); with
 * variable coefficients the characteristic is found by dsolve (SymPy
 * pde_1st_linear_variable_coeff). Higher orders are explicitly unsupported,
 * rather than assigned a partial solution.
 */
export function pdsolve(equation: ExprLike, func?: Expr, hint = 'default'): Expr {
  const eq = asEquation(equation), f = dependent(eq, func), m = linearPde(eq, f);
  if (!m) throw new NotImplementedError('pdsolve: only first-order linear PDEs are implemented');
  if (hint !== 'default' && !classifyPde(eq, f).includes(hint)) throw new RangeError(`PDE does not match hint ${hint}`);
  if (!m.constant) return variableCoeff(m);
  const { x, y, a, b, c, forcing } = m;
  const norm = simplify(add(pow(a, 2), pow(b, 2)));
  const eta = add(mul(b, x), mul(-1, a, y));
  const eta0 = new Dummy('eta'), t = new Dummy('xi');
  // The usual orthogonal characteristic chart degenerates for complex
  // coefficients a^2+b^2=0. In that case use x/a as the characteristic time.
  const singularChart = norm.equals(0);
  const coordinate = singularChart ? mul(x, pow(a, -1)) : add(mul(a, x), mul(b, y));
  const scale = singularChart ? S.One : norm;
  const rate = mul(c, pow(scale, -1));
  const inverse: [Expr, Expr][] = singularChart
    ? [[x, mul(a, t)], [y, add(mul(b, t), mul(-1, eta0, pow(a, -1)))]]
    : [[x, mul(add(mul(a, t), mul(b, eta0)), pow(norm, -1))], [y, mul(add(mul(b, t), mul(-1, a, eta0)), pow(norm, -1))]];
  let solution = SymFunction('F')(eta);
  if (!forcing.equals(0)) {
    const integrand = mul(exp(mul(rate, t)), xreplace(forcing, inverse), pow(scale, -1));
    const primitive = hint.endsWith('_Integral')
      ? new SubsNode([new Integral([xreplace(integrand, [[eta0, eta]]), t]), t, coordinate])
      : xreplace(integrate(integrand, t), [[eta0, eta], [t, coordinate]]);
    solution = add(solution, primitive);
  }
  return Eq(f, simplify(mul(exp(mul(-1, rate, coordinate)), solution)));
}
/** The one solution of a first-order ODE (the first branch of several, as SymPy takes). */
function odeSolution(eq: Expr, fx: UndefFn, hint?: string): Rel {
  const sol: unknown = dsolve(eq, fx, hint === undefined ? {} : { hint });
  return cast(Array.isArray(sol) ? sol[0] : sol, Rel, 'dsolve solution');
}
/** Symbols of a that are not symbols of any of the others. */
function newSymbols(a: Expr, ...others: Expr[]): Sym[] {
  const old = new Set(others.flatMap((e) => [...freeSymbols(e)]));
  return [...freeSymbols(a)].filter((s) => !old.has(s));
}
/** SymPy _simplify_variable_coeff: the integration constant becomes F(funcarg). */
function simplifyVariableCoeff(sol: Expr, constants: readonly Sym[], funcarg: Expr, eta: Sym): Expr {
  return simplify(subs(subs(sol, [[first(constants), SymFunction('F')(funcarg)]]), [[eta, funcarg]]));
}
/**
 * SymPy pde_1st_linear_variable_coeff: a(x,y)*fx + b(x,y)*fy + c(x,y)*f = G(x,y).
 * With xi = x and eta the constant of the characteristic dy/dx = b/a, the
 * PDE becomes the linear ODE a*du/dxi + c*u = G, solved by dsolve.
 */
function variableCoeff(m: LinearPde): Expr {
  const { f, x, y, a: b, b: c, c: d, forcing: e } = m;
  const F = SymFunction('F'), eta = new Sym('eta');
  if (d.equals(0) && (b.equals(0) || c.equals(0))) {
    // b*fx = e or c*fy = e
    return b.equals(0) ? Eq(f, add(F(x), integrate(mul(e, pow(c, -1)), y))) : Eq(f, add(F(y), integrate(mul(e, pow(b, -1)), x)));
  }
  // one derivative only: a linear ODE in the other variable, y or x a parameter
  if (c.equals(0) || b.equals(0)) {
    const [k, v, w] = c.equals(0) ? [b, x, y] : [c, y, x];
    const gv = new UndefFn(f.name, [v]);
    const plode = add(mul(diff(gv, v), k), mul(d, gv), mul(-1, e));
    const sol = odeSolution(plode, gv).rhs;
    return Eq(f, simplifyVariableCoeff(sol, newSymbols(sol, plode, x, y), w, eta));
  }
  const dx = new UndefFn('d', [x]);
  const h = subs(mul(c, pow(b, -1)), [[y, dx]]);
  const sol = odeSolution(add(diff(dx, x), mul(-1, h)), dx);
  // (a first-order ODE solution has one integration constant)
  const etat = subs(first(solve(sol, first(newSymbols(sol, h, x, y)))), [[dx, y]]);
  const ysub = first(solve(add(eta, mul(-1, etat)), y));
  const fx = new UndefFn(f.name, [x]);
  const deq = subs(add(mul(b, diff(fx, x)), mul(d, fx), mul(-1, e)), [[y, ysub]]);
  const final = odeSolution(deq, fx, '1st_linear').rhs;
  return Eq(f, simplifyVariableCoeff(final, newSymbols(final, deq, x, y), etat, eta));
}
/** Verify an explicit PDE solution by substituting and differentiating it. */
export function checkpdesol(equation: ExprLike, solutionIn: ExprLike, func?: Expr): [boolean, Expr] {
  const eq = asEquation(equation), f = dependent(eq, func), solution = sympify(solutionIn);
  const rhs = solution instanceof Rel && solution.op === 'Eq'
    ? solution.lhs.equals(f) ? solution.rhs : solution.rhs.equals(f) ? solution.lhs : undefined
    : solution;
  if (rhs === undefined || rhs.has(f)) throw new NotImplementedError('checkpdesol: supply an explicit solution for the dependent function');
  // Differentiating F(a*x+b*y) introduces a fresh bound dummy on each
  // differentiation. Alpha-normalize those binders before cancelling terms.
  const scopes = new Map<number, Dummy[]>();
  const normalize = (e: Expr, depth: number): Expr => {
    if (e instanceof SubsNode && e.variables.every((v) => v instanceof Sym)) {
      const scope = scopes.get(depth) ?? []; scopes.set(depth, scope);
      while (scope.length < e.variables.length) scope.push(new Dummy(`xi_${scope.length + 1}`));
      const vs = scope.slice(0, e.variables.length);
      const body = xreplace(e.expr, e.variables.map((v, i): [Expr, Expr] => [v, at(vs, i)]));
      return new SubsNode([normalize(body, depth + 1), ...vs, ...e.point.map((p) => normalize(p, depth))]);
    }
    return e.args.length ? rebuild(e, e.args.map((a) => normalize(a, depth))) : e;
  };
  const residual = simplify(normalize(doit(subs(eq, [[f, rhs]])), 0));
  return [residual.equals(0), residual];
}

/** Separate independent variables by an additive or multiplicative ansatz. */
export function pdeSeparate(equation: ExprLike, func: Expr, separated: readonly Expr[], strategy: 'add' | 'mul' = 'mul'): [Expr, Expr] | NoMatchResult {
  if (!['add', 'mul'].includes(strategy)) throw new RangeError('Unknown separation strategy');
  const f = cast(func, UndefFn), variables = separated.flatMap((s) => s.args);
  if (variables.length !== f.args.length) throw new RangeError('Variable counts do not match');
  if (new Set(variables.map((v) => v.key)).size !== variables.length) throw new RangeError('Duplicate substitution arguments');
  if (variables.some((v) => !f.args.some((x) => x.equals(v)))) throw new RangeError('Arguments do not match');
  if (separated.length < 2) throw new RangeError('At least two separated functions are required');
  const ansatz = strategy === 'add' ? add(...separated) : mul(...separated);
  let value = expand(doit(subs(asEquation(equation), [[f, ansatz]])));
  if (strategy === 'mul') value = expand(simplify(mul(value, pow(ansatz, -1))));
  const dep = first(separated).args, others = separated.slice(1).flatMap((s) => s.args);
  const has = (e: Expr, vs: readonly Expr[]): boolean => vs.some((v) => e.has(v));
  const terms = (e: Expr): readonly Expr[] => e instanceof Add ? e.args : [e];
  const split = (e: Expr): [Expr, Expr] => { const factors = e instanceof Mul ? e.args : [e]; return [mul(...factors.filter((v) => !has(v, dep))), mul(...factors.filter((v) => has(v, dep)))]; };
  const divisors = new Map<string, Expr>();
  for (const term of terms(value)) {
    if (some(term, (e) => e instanceof Derivative && !has(e, others))) {
      const [independent, rest] = split(term);
      if (has(rest, others)) return NoMatch;
      divisors.set(independent.key, independent);
    }
  }
  if (divisors.size) value = add(...terms(value).map((term) => simplify(add(...[...divisors.values()].map((d) => mul(term, pow(d, -1)))))));
  let lhs: Expr = S.Zero, rhs: Expr = S.Zero;
  const denominators = new Map<string, Expr>();
  for (const term of terms(value)) {
    if (!has(term, others)) { lhs = add(lhs, term); continue; }
    const [, rest] = split(expand(term));
    if (has(rest, others)) return NoMatch;
    denominators.set(rest.key, rest); rhs = add(rhs, mul(-1, term));
  }
  if (!denominators.size) return NoMatch;
  const divisor = add(...denominators.values());
  lhs = expand(simplify(mul(lhs, pow(divisor, -1)))); rhs = expand(simplify(mul(rhs, pow(divisor, -1))));
  return has(lhs, others) || has(rhs, dep) ? NoMatch : [lhs, rhs];
}
export const pdeSeparateAdd = (eq: ExprLike, f: Expr, separated: readonly Expr[]): [Expr, Expr] | NoMatchResult => pdeSeparate(eq, f, separated, 'add');
export const pdeSeparateMul = (eq: ExprLike, f: Expr, separated: readonly Expr[]): [Expr, Expr] | NoMatchResult => pdeSeparate(eq, f, separated, 'mul');
