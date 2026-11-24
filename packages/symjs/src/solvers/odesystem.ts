// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Systems of linear first-order ODEs with constant coefficients
 * (SymPy dsolve for systems, the linear constant-coefficient case):
 * x' = A*x + b(t). The homogeneous solutions come from the Jordan form of A
 * (real solutions Re/Im for complex eigenvalue pairs), the particular
 * solution from variation of parameters.
 */

import { NotImplementedError } from '../core/errors';
import type { Expr, ExprLike } from '../core/nodes';
import { Derivative, Dummy, I, Integral, Order, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { asNumerDenom, getO, removeO } from '../core/methods';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { isIntegerQ, isReal } from '../core/assumptions';
import { SymFunction } from '../core/undef';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { doit } from '../calculus/doit';
import { Eq } from '../core/logic';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { cos, im, log, re, sin, sinh, fn } from '../functions/elementary/elementary';
import { factor } from '../polys/sympoly';
import { cancel } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { powsimp } from '../simplify/powsimp';
import { expand, expandMul, expandMulOnly } from '../simplify/expand';
import { collect } from '../simplify/radsimp';
import { sqrtdenest } from '../simplify/sqrtdenest';
import { simplify } from '../simplify/simplify';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { analyticFunc, jordanForm, stronglyConnectedComponents } from '../matrices/linalg';
import { asEquation, linearEqToMatrix, nonlinsolve, solve } from './solve';
import { solveIcs } from './odesimp';

/** The single-equation dsolve, registered by solvers/ode.ts (which imports this module). */
let dsolveOne: (eq: Expr, f: Expr) => Expr | Expr[] = () => {
  throw new NotImplementedError('dsolve: single equations are not loaded');
};
/** @internal */
export function registerSingleOdeSolver(f: (eq: Expr, fx: Expr) => Expr | Expr[]): void {
  dsolveOne = f;
}

const isZero = (e: Expr) => e instanceof Rational && e.isZero;
const isOne = (e: Expr) => e instanceof Rational && e.p === 1n && e.q === 1n;

/**
 * A list of solutions
 * [Eq(f(t), ...), Eq(g(t), ...)], or, like SymPy, a list of such lists when the
 * system has several solution families (a nonlinear triangular system).
 *
 * @param eqsIn - System of ODEs to be solved.
 * @param funcsIn - List of dependent variables that make up the system of ODEs.
 * @param t - Independent variable in the system of ODEs.
 * @param ics - Set of initial boundary/conditions for the system of ODEs.
 * @param options - `simplify` simplifies the result, `doit` evaluates integrals.
 * @returns Families of solution equations, one equation per dependent function.
 * @throws RangeError when the dependent functions use different independent variables.
 * @see SymPy `sympy.solvers.ode.systems.dsolve_system`
 * @example
 * ```ts
 * import { dsolveSystem, ex } from '@symjs/symjs';
 * dsolveSystem([ex`Eq(Derivative(f(x), x), g(x))`, ex`Eq(Derivative(g(x), x), f(x))`]); // => [[Eq(f(x), -C1*exp(-x) + C2*exp(x)), Eq(g(x), C1*exp(-x) + C2*exp(x))]]
 * ```
 */
export function dsolveSystem(eqsIn: readonly ExprLike[], funcsIn?: readonly UndefFn[], t?: Sym, ics?: ReadonlyMap<Expr, ExprLike>, options: { simplify?: boolean; doit?: boolean } = {}): Expr[][] {
  const sols = dsolveSystemAll(eqsIn, funcsIn, options);
  const funcs = funcsIn ?? findFunctions(eqsIn.map(sympify));
  if (t !== undefined && funcs.some((f) => !first(f.args).equals(t))) throw new RangeError('dsolveSystem: inconsistent independent variable');
  if (ics === undefined) return sols;
  const parameters = new Set(eqsIn.flatMap((e) => [...sympify(e).freeSymbols()].map((s) => s.key)));
  return sols.map((family) => {
    const constants = [...new Map(family.flatMap((e) => [...e.freeSymbols()].filter((s) => s instanceof Sym)).filter((s) => !parameters.has(s.key)).map((s) => [s.key, s])).values()];
    const values = solveIcs(family, funcs, constants, ics);
    return family.map((e) => xreplace(e, [...values]));
  });
}

/**
 * Solves an ODE system for each function's highest derivative.
 *
 * @param eqs - List of the ODEs.
 * @param funcs - List of dependent variables.
 * @param t - Independent variable.
 * @returns Equivalent systems solved for their highest derivatives.
 * @throws RangeError when a dependent function has no derivative in the system.
 * @see SymPy `sympy.solvers.ode.systems.canonical_odes`
 * @example
 * ```ts
 * import { AppliedUndef, canonicalOdes, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * canonicalOdes([ex`Eq(-7*f(x) + Derivative(f(x), x), 12*g(x))`, ex`Eq(g(x) + Derivative(g(x), x), 20*f(x))`], [new AppliedUndef('f', [x]), new AppliedUndef('g', [x])], x); // => [[Eq(Derivative(f(x), x), 7*f(x) + 12*g(x)), Eq(Derivative(g(x), x), 20*f(x) - g(x))]]
 * ```
 */
export function canonicalOdes(eqs: readonly ExprLike[], funcs: readonly UndefFn[], t: Sym): Expr[][] {
  const equations = eqs.map(asEquation);
  const derivatives = funcs.map((f) => {
    let order = 0;
    const visit = (e: Expr): void => {
      if (e instanceof Derivative && e.expr.equals(f)) order = Math.max(order, e.variableCount.reduce((n, [v, k]) => n + (v.equals(t) ? k : 0), 0));
      e.args.forEach(visit);
    };
    equations.forEach(visit);
    if (order === 0) throw new RangeError('canonicalOdes: a derivative is required for every function');
    return new Derivative([f, t, Rational.of(order)]);
  });
  const unknowns = funcs.map((_, i) => new Dummy(`d${i}`));
  const replacement = derivatives.map((d, i): [Expr, Expr] => [d, at(unknowns, i)]);
  return nonlinsolve(equations.map((e) => xreplace(e, replacement)), unknowns)
    .map((row) => derivatives.map((d, i) => Eq(d, at(row, i))));
}

/**
 * Exp(A*t) for a constant square coefficient matrix.
 *
 * @param A - The square coefficient matrix.
 * @param t - The independent variable.
 * @returns The matrix exponential of the coefficient matrix times the independent variable.
 * @throws RangeError when the matrix is not square or depends on the time variable.
 * @see SymPy `sympy.solvers.ode.systems.matrix_exp`
 * @example
 * ```ts
 * import { Matrix, odeMatrixExp, symbols } from '@symjs/symjs';
 *
 * const [t] = symbols('t');
 * odeMatrixExp(Matrix.of([[1, 0], [0, 1]]), t); // => Matrix([
 * //   [exp(t),      0],
 * //   [     0, exp(t)]])
 * ```
 */
export function matrixExp(A: Matrix, t: Sym): Matrix {
  if (A.rows !== A.cols || A.data.some((e) => e.has(t))) throw new RangeError('expected a square matrix independent of t');
  const z = new Dummy('lambda');
  return analyticFunc(A, exp(mul(t, z)), z);
}

/**
 * Classifies a first-order linear system by forcing and commutativity with its antiderivative.
 *
 * @param A - The square coefficient matrix.
 * @param t - The independent variable.
 * @param b - The inhomogeneous forcing column.
 * @returns The equation type and the coefficient antiderivative when applicable.
 * @throws RangeError when the system dimensions disagree.
 * @throws NotImplementedError when the coefficient matrix does not commute with its antiderivative.
 * @see SymPy `sympy.solvers.ode.systems.linodesolve_type`
 * @example
 * ```ts
 * import { Matrix, linodesolveType, symbols } from '@symjs/symjs';
 *
 * const [t] = symbols('t');
 * linodesolveType(Matrix.of([[1, 0], [0, 1]]), t).get('type_of_equation'); // => type1
 * ```
 */
export function linodesolveType(A: Matrix, t: Sym, b?: Matrix): Map<string, string | Matrix | NoMatchResult> {
  if (A.rows !== A.cols || (b !== undefined && (b.rows !== A.rows || b.cols !== 1))) throw new RangeError('linodesolveType: incompatible system dimensions');
  const variable = A.data.some((e) => e.has(t));
  const forced = b?.data.some((e) => !isZero(e)) ?? false;
  const antiderivative = variable ? A.map((e) => integrate(e, t)) : NoMatch;
  if (antiderivative instanceof Matrix && A.mul(antiderivative).sub(antiderivative.mul(A)).data.some((e) => !isZero(simplify(e)))) throw new NotImplementedError('linodesolveType: matrix does not commute with its antiderivative');
  return new Map<string, string | Matrix | NoMatchResult>([['type_of_equation', `type${1 + (variable ? 2 : 0) + (forced ? 1 : 0)}`], ['antiderivative', antiderivative]]);
}

const derivativeOf = (f: UndefFn, t: Sym, k: number) => new Derivative([f, t, Rational.of(k)]);

/** Every solution list of the system. */
function dsolveSystemAll(eqsIn: readonly ExprLike[], funcsIn: readonly UndefFn[] | undefined, options: { simplify?: boolean; doit?: boolean }): Expr[][] {
  const eqs = eqsIn.map((e) => {
    const x = sympify(e);
    return x instanceof Rel && x.op === 'Eq' ? add(x.lhs, mul(-1, x.rhs)) : x;
  });
  const funcs = funcsIn ?? findFunctions(eqs);
  const n = funcs.length;
  if (n === 0 || eqs.length !== n) throw new TypeError('dsolve: as many equations as functions are needed');
  const t = cast(first(first(funcs).args), Sym);
  if (funcs.some((f) => f.args.length !== 1 || !first(f.args).equals(t))) throw new RangeError('system functions must depend on one common variable');
  const primitive = (e: Expr): Expr => options.doit === false && !isZero(e) ? new Integral([e,t]) : integrate(e,t);
  const finish = (e: Expr): Expr => options.simplify === false ? e : expand(e);
  // Introduce a state for each lower derivative in a coupled linear system.
  const derivatives = eqs.flatMap((eq) => subexprs(eq, (e) => e instanceof Derivative)).map((d) => cast(d, Derivative));
  if (derivatives.some((d) => funcs.some((f) => d.expr.equals(f)) && d.variableCount.some(([v]) => !v.equals(t)))) throw new RangeError('inconsistent differentiation variable');
  const orders = funcs.map((f) => Math.max(0, ...derivatives.filter((d) => d.expr.equals(f)).map((d) => d.variableCount.reduce((a, [, k]) => a + k, 0))));
  // If X = q(t)*Y eliminates Y, solve the smaller subsystem for Y'
  // before introducing the constants of the final antiderivatives.
  if (orders.every((k) => k === 2)) {
    const system = systemMatrices(eqs, funcs, t, 2);
    if (system && !system[1].data.some((e) => !isZero(e))) {
      const [matrices] = system, lead = first(matrices), firstOrder = at(matrices, 1), zeroOrder = at(matrices, 2);
      if (firstOrder.data.every(isZero) && !isZero(lead.det())) {
        const acceleration = lead.inv().mul(zeroOrder);
        const modes = secondOrderModes(acceleration, funcs, t);
        if (modes) return [funcs.map((f, i) => Eq(f, finish(modes.get(i, 0))))];
      }
      for (const q of [S.One, t]) {
        const dq = diff(q, t);
        if (!zeroOrder.scale(q).add(firstOrder.scale(dq)).data.every((e) => isZero(simplify(e)))) continue;
        const velocity = Matrix.col(...funcs);
        const equations = lead.mul(velocity.map((f) => diff(f, t))).sub(firstOrder.sub(lead.scale(mul(2, dq, pow(q, -1)))).mul(velocity));
        const solutions = dsolveSystemAll(equations.data, funcs, options);
        const used = new Set([...eqs, ...solutions.flat()].flatMap((e) => [...e.freeSymbols()].map((v) => v.key)));
        let index = 1;
        const cs = funcs.map(() => { while (used.has(C(index).key)) index++; return C(index++); });
        return solutions.map((family) => family.map((sol, i) => Eq(at(funcs, i), mul(q, add(at(cs, i), primitive(cast(sol, Rel).rhs))))));
      }
    }
  }

  if (orders.some((k) => k > 1) && eqs.every((eq) => funcs.filter((f) => eq.has(f)).length > 1)) {
    const states = [...funcs];
    const links: Expr[] = [];
    const jets: [Expr, Expr][] = [];
    for (const [i, f] of funcs.entries()) {
      let state = f;
      for (let k = 1; k <= at(orders, i); k++) {
        const jet = derivativeOf(f, t, k);
        const ds = derivativeOf(state, t, 1);
        if (k === at(orders, i)) jets.push([jet, ds]);
        else {
          let name = `${f.name}_${k}`;
          while (eqs.some((eq) => eq.has(new UndefFn(name, [t]))) || states.some((v) => v.name === name)) name += '_';
          state = new UndefFn(name, [t]);
          states.push(state);
          links.push(add(ds, mul(-1, state)));
          jets.push([jet, state]);
        }
      }
    }
    const reduced = [...eqs.map((e) => xreplace(e, jets)), ...links];
    return dsolveSystemAll(reduced, states, options).map((family) => family.slice(0, n));
  }
  // replace derivatives and functions by symbols, then read the coefficients
  const ds = funcs.map((_, i) => new Dummy(`d${i}`));
  const us = funcs.map((_, i) => new Dummy(`u${i}`));
  const reps: [Expr, Expr][] = [
    ...funcs.map((f, i): [Expr, Expr] => [new Derivative([f, t, S.One]), at(ds, i)]),
    ...funcs.map((f, i): [Expr, Expr] => [f, at(us, i)]),
  ];
  const sub = eqs.map((e) => xreplace(e, reps));
  const lin = linearEqToMatrix(sub, [...ds, ...us]);
  if (!lin) {
    // Protect parameters named C1, C2, ... while a nonlinear solver allocates integration constants.
    const parameters = [...new Map(eqs.flatMap((e) => [...e.freeSymbols()].filter((s) => s instanceof Sym)).filter((s) => s.key !== t.key && /^C\d+$/.test(s.name)).map((s) => [s.key, s])).values()];
    const protect = parameters.map((s): [Expr, Expr] => [s, new Dummy(s.name)]);
    const protectedEqs = eqs.map((e) => xreplace(e, protect));
    let nl = n === 2 ? nonlinear2(protectedEqs, [first(funcs), at(funcs, 1)], t) : n === 3 ? nonlinear3(protectedEqs, funcs, t) : undefined;
    if (nl !== undefined && parameters.length) {
      const used = new Set(parameters.map((s) => s.name));
      const constants = [...new Map(nl.flat().flatMap((e) => [...e.freeSymbols()].filter((s) => s instanceof Sym)).filter((s) => !(s instanceof Dummy) && /^C\d+$/.test(s.name)).map((s) => [s.key, s])).values()].sort((a, b) => a.name.localeCompare(b.name));
      let next = 1;
      const rename = constants.map((s): [Expr, Expr] => {
        while (used.has(`C${next}`)) next++;
        return [s, C(next++)];
      });
      nl = nl.map((family) => family.map((e) => xreplace(xreplace(e, rename), protect.map(([s, d]) => [d, s]))));
    }
    return nl ?? triangularSystem(eqs, funcs, options);
  }
  const [M, rhs] = lin;
  const Md = Matrix.fromFunction(n, n, (i, j) => M.get(i, j));
  const Mu = Matrix.fromFunction(n, n, (i, j) => M.get(i, n + j));
  if (Md.det().key === S.Zero.key) throw new NotImplementedError('dsolve: the system is not of first order in every function');
  // d = A*u + b
  const MdInv = Md.inv();
  const A = MdInv.mul(Mu).scale(-1).map((e) => simplify(e));
  const b = MdInv.mul(rhs).map((e) => simplify(e));
  if (A.data.some((e) => e.has(t))) {
    // A(t) = alpha(t)*I + phi(t)*M. The two summands commute.
    const direct = constantTimesFunction(A, t);
    const alpha = direct ? S.Zero : A.get(0, 0);
    const shifted = A.sub(Matrix.eye(n).scale(alpha));
    const scaled = direct ?? constantTimesFunction(shifted, t);
    if (scaled) {
      const [phi, M] = scaled;
      const tau = integrate(phi, t);
      const s = new Dummy('s');
      const basis = fundamentalSolutions(M, s, options.simplify !== false).reduce((acc, c) => acc.hstack(c));
      if (options.simplify === false) {
        // exp(B) and exp(-B) for B = integral(alpha)*I + tau*M.
        const unscaled = basis.mul(basis.map((e) => xreplace(e, [[s, S.Zero]])).inv());
        const shift = integrate(alpha, t);
        const atTime = (sign: number) => unscaled.map((e) => expandMul(mul(exp(mul(sign, shift)), xreplace(e, [[s, mul(sign,tau)]])))).map((e) => powsimp(e));
        const phi = atTime(1);
        const constants = Matrix.col(...funcs.map((_, i) => C(i + 1)));
        const forcing = atTime(-1).mul(b).map((e) => primitive(expandMul(e)));
        const sol = phi.mul(constants.add(forcing)).map(expandMul);
        return [funcs.map((f,i) => {
          const e = sol.get(i,0);
          const gens = subexprs(e, (v) => v instanceof Pow && v.base.equals(S.E));
          return Eq(f, collect(e, gens, { exact: true }));
        })];
      }
      const Phi = basis.map((e) => mul(exp(integrate(alpha, t)), xreplace(e, [[s, tau]])));
      let constants = Matrix.col(...Array.from({ length: n }, (_, i) => C(i + 1)));
      if (b.data.some((e) => !isZero(e))) constants = constants.add(Phi.inv().mul(b).map((e) => primitive(simplify(e))));
      const sol = Phi.mul(constants);
      return [funcs.map((f, i) => Eq(f, finish(sol.get(i, 0))))];
    }
    if (n === 2 && b.data.every((e) => isZero(e))) return [linear2VariableCoefficients(A, funcs, t)];
    return triangularSystem(eqs, funcs, options);
  }
  const fundamental = fundamentalSolutions(A, t);
  const Phi = fundamental.reduce((acc, c) => acc.hstack(c));
  const Cs = Array.from({ length: n }, (_, i) => new Sym(`C${i + 1}`));
  let sol = Phi.mul(Matrix.col(...Cs));
  if (b.data.some((e) => !isZero(e))) {
    // A constant forcing admits the equilibrium particular solution -A^-1*b.
    if (b.data.every((e) => !e.has(t)) && !isZero(A.det())) {
      const stationary = A.inv().mul(b);
      return [funcs.map((f, i) => Eq(f, add(sol.get(i, 0), mul(-1, stationary.get(i, 0)))))];
    }
    // variation of parameters: Phi * Integral(Phi**-1 * b)
    const g = Phi.inv().mul(b).map((e) => simplify(e));
    const part = Phi.mul(g.map(primitive)).map((e) => options.simplify === false ? e : simplify(expand(e)));
    sol = sol.add(part);
  }
  return [funcs.map((f, i) => Eq(f, finish(sol.get(i, 0))))];
}

/**
 * A = phi(t)*M with M constant, phi the (common) factor of one nonzero entry
 * that has t, or undefined.
 */
function constantTimesFunction(A: Matrix, t: Sym): [Expr, Matrix] | undefined {
  const ref = A.data.find((e) => e.has(t));
  if (ref === undefined) return [S.One, A];
  const M = A.map((e) => simplify(mul(e, pow(ref, -1))));
  return M.data.some((e) => e.has(t)) ? undefined : [ref, M];
}

const diagonal = (m: Matrix) => m.data.every((v, i) => i % (m.rows + 1) === 0 || isZero(v));

/** Decouple X'' = phi(t)*M*X into Airy equations or constant-coefficient equations in 1/t. */
function secondOrderModes(acceleration: Matrix, funcs: readonly UndefFn[], t: Sym): Matrix | undefined {
  if (!acceleration.data.some((e) => e.has(t))) return undefined;
  const scaled = constantTimesFunction(acceleration, t);
  if (!scaled) return undefined;
  const [phi, matrix] = scaled;
  const reciprocal = simplify(mul(pow(t, 4), phi));
  const inverted = !reciprocal.has(t);
  if (!inverted && diff(phi, t).has(t)) return undefined;
  const [basis, jordan] = diagonal(matrix) ? [Matrix.eye(matrix.rows), matrix] : jordanForm(matrix);
  if (!diagonal(jordan)) return undefined;
  const modes = funcs.map((f, i) => {
    const rate = mul(inverted ? reciprocal : phi, jordan.get(i, i));
    const solution = cast(dsolveOne(add(diff(f, t, 2), mul(-1, rate, f)), f), Rel);
    const mode = xreplace(solution.rhs, [[C(1), C(2*i + 1)], [C(2), C(2*i + 2)]]);
    // X=t*V(1/t) changes X''=M*X/t^4 into V''=M*V.
    return inverted ? mul(t, xreplace(mode, [[t, pow(t, -1)]])) : mode;
  });
  return basis.mul(Matrix.col(...modes));
}

/** n real fundamental solutions (columns) of x' = A*x. */
function fundamentalSolutions(A: Matrix, t: Sym, realForm = true): Matrix[] {
  const n = A.rows;
  const symbolic = A.data.find((e) => e.freeSymbols().size > 0);
  if (symbolic && n > 2) {
    const normalized = A.map((e) => cancel(mul(e, pow(symbolic, -1))));
    if (normalized.data.every((e) => e.freeSymbols().size === 0)) {
      const tau = new Dummy('tau');
      return fundamentalSolutions(normalized, tau, realForm).map((v) => v.map((e) => xreplace(e, [[tau, mul(symbolic, t)]])));
    }
  }
  if (symbolic && diagonal(A)) return Array.from({ length: n }, (_, i) => Matrix.eye(n).col(i).scale(exp(mul(A.get(i, i), t))));
  if (n === 2 && symbolic) {
    // Solve the quadratic characteristic equation symbolically. The columns
    // (b, lambda-a) are eigenvectors whenever b is nonzero.
    const a = A.get(0, 0), b = A.get(0, 1), c = A.get(1, 0), d = A.get(1, 1);
    const mean = mul(S.Half, add(a, d));
    const delta = pow(simplify(add(pow(mul(S.Half, add(a, mul(-1, d))), 2), mul(b, c))), S.Half);
    if (isZero(delta)) {
      const phi = Matrix.eye(2).add(A.sub(Matrix.eye(2).scale(mean)).scale(t)).scale(exp(mul(mean, t)));
      return [phi.col(0), phi.col(1)];
    }
    return [-1, 1].map((sign) => {
      const root = add(mean, mul(sign, delta));
      const v = isZero(b) ? Matrix.col(add(root, mul(-1, d)), c) : Matrix.col(b, add(root, mul(-1, a)));
      return v.scale(exp(mul(root, t)));
    });
  }
  const [P, J] = jordanForm(A);
  // a real A has its complex eigenvalues in conjugate pairs with the same Jordan
  // structure, each pair giving two real solutions; a complex A keeps exp(lam*t)
  const realA = realForm && A.data.every((e) => isReal(e) === true);
  const out: Matrix[] = [];
  let i = 0;
  while (i < n) {
    const lam = J.get(i, i);
    // block size
    let k = 1;
    while (i + k < n && J.get(i + k - 1, i + k).key === S.One.key && J.get(i + k, i + k).key === lam.key) k++;
    const imaginary = realA && lam.freeSymbols().size === 0 ? lam.toComplex().im : 0;
    const complexPair = Math.abs(imaginary) > 1e-14;
    for (let j = 0; j < k; j++) {
      // the j-th chain solution: e^(lam*t) * sum_{m<=j} t**(j-m)/(j-m)! * P_col(i+m)
      let v = Matrix.zeros(n, 1);
      for (let m = 0; m <= j; m++) {
        let fact = 1n;
        for (let q = 2n; q <= BigInt(j - m); q++) fact *= q;
        v = v.add(P.col(i + m).scale(mul(pow(t, j - m), Rational.of(1n, fact))));
      }
      if (!complexPair) out.push(v.scale(exp(mul(lam, t))).map((e) => simplify(e)));
      else if (imaginary < 0) {
        // the pair is represented by the eigenvalue with negative imaginary part:
        // e^(lam*t) = e^(a*t)*(cos(b*t) + I*sin(b*t)), real solutions Re and Im (t real)
        const a = simplify(re(lam));
        const bb = simplify(im(lam));
        const tr = new Dummy('t', { real: true });
        const w = v.map((e) => xreplace(e, [[t, tr]])).scale(mul(exp(mul(a, tr)), add(cos(mul(bb, tr)), mul(I, sin(mul(bb, tr))))));
        const ex = w.map((e) => expand(e, { complex: true }));
        const back = (e: Expr) => simplify(xreplace(expand(e, { complex: true }), [[tr, t]]));
        out.push(ex.map((e) => back(re(e))), ex.map((e) => back(im(e))));
      }
    }
    i += k;
  }
  return out;
}

/** The unknown functions, in the order of the derivatives in the equations. */
function findFunctions(eqs: readonly Expr[]): UndefFn[] {
  const seen = new Map<string, UndefFn>();
  for (const e of eqs) {
    const ds: UndefFn[] = [];
    const walk = (x: Expr) => {
      if (x instanceof Derivative && x.expr instanceof UndefFn) ds.push(x.expr);
      x.args.forEach(walk);
    };
    walk(e);
    const f = ds.find((d) => !seen.has(d.key));
    if (f) seen.set(f.key, f);
  }
  return [...seen.values()];
}


/**
 * x' = f*x + g*y, y' = h*x + p*y with variable coefficients (SymPy's form in
 * terms of a particular solution x0(t), y0(t)):
 * x = C1*x0 + C2*x0*Integral(g*F/x0**2), y = C1*y0 + C2*(y0*Integral(g*F/x0**2) + F/x0),
 * F = exp(Integral(f))*exp(Integral(p)).
 */
function linear2VariableCoefficients(A: Matrix, funcs: readonly UndefFn[], t: Sym): Expr[] {
  const [f, g, , p] = [A.get(0, 0), A.get(0, 1), A.get(1, 0), A.get(1, 1)];
  const x0 = SymFunction('x0')(t);
  const y0 = SymFunction('y0')(t);
  // keep exp(Integral(f))*exp(Integral(p)) as two factors (no automatic combination of the exponents)
  const Fraw = new Mul([exp(new Integral([p, t])), exp(new Integral([f, t]))]);
  const Ig = new Integral([mul(g, Fraw, pow(x0, -2)), t]);
  const [C1, C2] = [new Sym('C1'), new Sym('C2')];
  return [
    Eq(at(funcs, 0), add(mul(C1, x0), mul(C2, x0, Ig))),
    Eq(at(funcs, 1), add(mul(C1, y0), mul(C2, add(mul(y0, Ig), mul(Fraw, pow(x0, -1)))))),
  ];
}

// ---------------------------------------------------------------------------
// nonlinear systems of two first-order equations (port of SymPy
// solvers/ode/ode.py check_nonlinear_2eq_order1 and _nonlinear_2eq_order1_type1..5)
// ---------------------------------------------------------------------------

const C = (i: number): Sym => new Sym(`C${i}`);

/** The factor x**n of a product (n free of x and y): [n, the other factors]. */
function powerFactor(r: Expr, x: Expr, y: Expr, isPow: (g: Expr) => Expr | undefined): [Expr, Expr] {
  const fs = r instanceof Mul ? r.args : [r];
  let n: Expr = S.Zero;
  const rest: Expr[] = [];
  for (const g of fs) {
    const k = isPow(g);
    if (k !== undefined && !k.has(x) && !k.has(y)) n = add(n, k);
    else rest.push(g);
  }
  return [n, mul(...rest)];
}

/** dsolve of eq for f, the solution's own constant named C2 (C1 is the first integral's). */
function solveWithC1(eq: Expr, f: UndefFn): Expr {
  const d = new Dummy('C1');
  const r = dsolveOne(xreplace(eq, [[C(1), d]]), f);
  const solution = cast(first([r].flat()), Rel, 'solution');
  if (solution.lhs.key !== f.key || solution.rhs.has(f)) throw new NotImplementedError('the time equation has only an implicit solution');
  const rhs = solution.rhs;
  return xreplace(xreplace(rhs, [[C(1), C(2)]]), [[d, C(1)]]);
}

/**
 * SymPy's types of x' = f(x, y, t), y' = g(x, y, t) and the Clairaut type 5;
 * undefined when none matches or the type's integrals or equations are not solved.
 */
function nonlinear2(eqs: readonly Expr[], [X, Y]: [UndefFn, UndefFn], t: Sym): Expr[][] | undefined {
  const dX = new Derivative([X, t, S.One]);
  const dY = new Derivative([Y, t, S.One]);
  const u = new Dummy('u');
  const v = new Dummy('v');
  const uv = (e: Expr): Expr => xreplace(e, [[X, u], [Y, v]]);
  const free = (e: Expr): boolean => !e.has(t) && !e.has(X) && !e.has(Y);
  try {
    // type 5 (Clairaut): x = t*x' + F(x', y'), y = t*y' + G(x', y')
    const e0 = expand(at(eqs, 0));
    const e1 = expand(at(eqs, 1));
    for (const sign of [1, -1]) {
      const F = add(mul(sign, e0), mul(-1, t, dX), X);
      const G = add(mul(sign, e1), mul(-1, t, dY), Y);
      const c = [C(1), C(2)];
      const at0 = (e: Expr): Expr => xreplace(e, [[dX, at(c, 0)], [dY, at(c, 1)]]);
      if (free(at0(F)) && free(at0(G))) return [[Eq(X, add(mul(at(c, 0), t), at0(F))), Eq(Y, add(mul(at(c, 1), t), at0(G)))]];
    }
    // x' = R0, y' = R1
    const rhs = (e: Expr, d: Expr, other: Expr): Expr | undefined => {
      const c = diff(e, d);
      if (c.has(d) || isZero(c)) return undefined;
      const r = expand(mul(-1, add(e, mul(-1, c, d)), pow(c, -1)));
      return r.has(other) ? undefined : r;
    };
    const R0 = rhs(e0, dX, dY);
    const R1 = rhs(e1, dY, dX);
    if (!R0 || !R1) return undefined;
    const C1 = C(1);
    const C2 = C(2);
    // the solutions for y (an invariant error, caught below, when solve finds none)
    const pairs = (xs: Expr[], phi: (s: Expr) => Expr): Expr[][] => [[defined(xs[0], 'solution'), ...xs.slice(1)].flatMap((s0) => [Eq(X, phi(s0)), Eq(Y, s0)])];
    // type 1: x' = x**n*f, y' = g*f with g free of x
    const [n1, f1] = powerFactor(factor(R0), X, Y, (g) => (g.key === X.key ? S.One : g instanceof Pow && g.base.key === X.key ? g.exp : undefined));
    const g1 = mul(R1, pow(f1, -1));
    if (!g1.has(X) && !uv(g1).has(t) && !uv(f1).has(t)) {
      const gv = uv(g1);
      const ig = integrate(pow(gv, -1), v);
      const phi = isOne(n1) ? mul(C1, exp(ig)) : pow(add(C1, mul(add(1, mul(-1, n1)), ig)), pow(add(1, mul(-1, n1)), -1));
      const sols = solve(add(integrate(pow(mul(gv, xreplace(uv(f1), [[u, phi]])), -1), v), mul(-1, t), mul(-1, C2)), v);
      return pairs(sols, (s0) => xreplace(phi, [[v, s0]]));
    }
    // type 2: x' = exp(n*x)*f, y' = g*f with g free of x
    const [n2, f2] = powerFactor(factor(R0), X, Y, (g) => (g instanceof Pow && g.base.key === S.E.key && g.exp.has(X) ? cancel(mul(g.exp, pow(X, -1))) : undefined));
    const g2 = mul(R1, pow(f2, -1));
    // (SymPy's matcher needs the factor exp(n*x), n != 0; without it the system is of type 3)
    if (!isZero(n2) && !g2.has(X) && !uv(g2).has(t) && !uv(f2).has(t)) {
      const gv = uv(g2);
      const ig = integrate(pow(gv, -1), v);
      const phi = mul(-1, pow(n2, -1), log(add(C1, mul(-1, n2, ig))));
      const sols = solve(add(integrate(pow(mul(gv, xreplace(uv(f2), [[u, phi]])), -1), v), mul(-1, t), mul(-1, C2)), v);
      return pairs(sols, (s0) => xreplace(phi, [[v, s0]]));
    }
    const F = uv(R0);
    const G = uv(R1);
    // x'=a*x*y, y'=b*x^m: y^2 - 2*b*x^m/(a*m) is constant.
    // The time equation for y is Riccati; keep its zero-invariant family too.
    const a = cancel(mul(F, pow(mul(u, v), -1)));
    const [m, b] = powerFactor(factor(G), u, v, (g) => g.key === u.key ? S.One : g instanceof Pow && g.base.key === u.key ? g.exp : undefined);
    // For an integer m, taking the m-th power of the chosen radical recovers
    // its radicand. Other exponents use the orbit quadrature below, preserving branches.
    if (![a, b, m].some((g) => g.has(u) || g.has(v) || g.has(t)) && isIntegerQ(m) === true && !isZero(m) && !isZero(a) && !isZero(b)) {
      const tau = add(t, C2);
      const am = mul(a, m);
      const r = pow(C1, S.Half);
      const angle = mul(S.Half, am, r, tau);
      return [
        [Eq(X, pow(mul(am, C1, pow(mul(2, b, pow(sinh(angle), 2)), -1)), pow(m, -1))), Eq(Y, mul(-1, r, fn('coth', [angle])))],
        [Eq(X, pow(mul(2, pow(mul(a, b, m, pow(tau, 2)), -1)), pow(m, -1))), Eq(Y, mul(-2, pow(mul(am, tau), -1)))],
      ];
    }
    // type 3: solve an orbit dv/du = G/F, then the scalar time equation on that orbit.
    // Either coordinate can be used as u; the second often turns an algebraic quadrature into a Riccati equation.
    if (!F.has(t) && !G.has(t)) {
      let quadratures: Expr[][] | undefined;
      for (const [A, H, K] of [[X, F, G], [Y, xreplace(G, [[u, v], [v, u]]), xreplace(F, [[u, v], [v, u]])]] as const) {
        try {
          const orbit = SymFunction('v')(u);
          const orbitEquation = add(diff(orbit, u), mul(-1, xreplace(cancel(mul(K, pow(H, -1))), [[v, orbit]])));
          const curves = [dsolveOne(orbitEquation, orbit)].flat();
          const solutions: Expr[][] = [];
          const implicit: Expr[][] = [];
          for (const curve of curves) {
            const relation = cast(curve, Rel, 'orbit');
            if (relation.lhs.key !== orbit.key || relation.rhs.has(orbit)) throw new NotImplementedError('the orbit is implicit');
            const phi = relation.rhs;
            const velocity = simplify(xreplace(H, [[v, phi]]));
            const q = Eq(new Integral([pow(velocity, -1), u, A]), add(t, C2));
            // subs preserves the integration variable of an unevaluated orbit
            // integral and records the dependent coordinate as its upper limit.
            const dependent = Eq(A === X ? Y : X, phi.subs([[u, A]]));
            implicit.push(A === X ? [q, dependent] : [dependent, q]);
            try {
              const timed = solveWithC1(add(diff(A, t), mul(-1, velocity.subs([[u, A]]))), A);
              const other = simplify(phi.subs([[u, timed]]));
              const solution = A === X ? [Eq(X, timed), Eq(Y, other)] : [Eq(X, other), Eq(Y, timed)];
              if (checkodesol(eqs, solution)[0]) solutions.push(solution);
            } catch {
              // A valid orbit still supplies a quadrature when time cannot be inverted.
            }
          }
          if (solutions.length) return solutions;
          quadratures ??= implicit;
        } catch {
          // The other coordinate may have a solvable orbit or time equation.
        }
      }
      if (quadratures?.length) return quadratures;
    }
    // type 4: F/G = f1(u)*g1(v)/(f2(u)*g2(v)), for t-dependent equations
    const [num, den] = asNumerDenom(cancel(mul(F, pow(G, -1))));
    const sn = separatevars(num, { dict: true, symbols: [u, v] });
    const sd = separatevars(den, { dict: true, symbols: [u, v] });
    if (F.has(t) && sn instanceof Map && sd instanceof Map && ![num, den].some((e) => e.has(t))) {
      const F1 = mul(getOrThrow(sn, u), getOrThrow(sn, 'coeff'));
      const G1 = getOrThrow(sn, v);
      const F2 = mul(getOrThrow(sd, u), getOrThrow(sd, 'coeff'));
      const G2 = getOrThrow(sd, v);
      const phi = mul(F, pow(num, -1));
      const first0 = add(integrate(mul(F2, pow(F1, -1)), u), mul(-1, integrate(mul(G1, pow(G2, -1)), v)), mul(-1, C1));
      // y from y' = f2(u)*g2(y)*phi with u from the first integral, and x from the first integral at that y
      // (SymPy solves for x by its own equation too, with a constant of its own, which does not satisfy the
      // system: x/y is not constant then)
      const us = solve(first0, u);
      return [defined(us[0], 'solution'), ...us.slice(1)].map((s0) => {
        const ysol = solveWithC1(add(diff(Y, t), mul(-1, xreplace(xreplace(mul(F2, G2, phi), [[u, s0]]), [[v, Y]]))), Y);
        return [Eq(X, xreplace(s0, [[v, ysol]])), Eq(Y, ysol)];
      });
    }
  } catch {
    // an integral or an equation the type needs is not solved
  }
  return undefined;
}

/** Euler systems X'=a*Y*Z*h, Y'=b*Z*X*h, Z'=c*X*Y*h, with a common separable time factor. */
function nonlinear3(eqs: readonly Expr[], funcs: readonly UndefFn[], t: Sym): Expr[][] | undefined {
  const derivatives = funcs.map((f) => new Derivative([f, t, S.One]));
  const ds = derivatives.map((_, i) => new Dummy(`d${i}`));
  const linear = linearEqToMatrix(eqs.map((e) => xreplace(e, derivatives.map((d, i) => [d, at(ds, i)]))), ds);
  if (!linear) return undefined;
  const [M, r] = linear;
  if (isZero(M.det())) return undefined;
  const rhs = M.inv().mul(r).data;
  const [X, Y, Z] = [at(funcs, 0), at(funcs, 1), at(funcs, 2)];
  const products = [mul(Y, Z), mul(Z, X), mul(X, Y)];
  const coefficients = rhs.map((g, i) => cancel(mul(g, pow(at(products, i), -1))));
  if (coefficients.some((g) => funcs.some((f) => g.has(f)) || isZero(g))) return undefined;
  const b = cancel(mul(at(coefficients, 1), pow(first(coefficients), -1)));
  const c = cancel(mul(at(coefficients, 2), pow(first(coefficients), -1)));
  if ([b, c].some((g) => g.has(t))) return undefined;
  const used = new Set(eqs.flatMap((e) => [...e.freeSymbols()].filter((s) => s instanceof Sym).map((s) => s.name)));
  const constants: Sym[] = [];
  for (let i = 1; constants.length < 3; i++) if (!used.has(`C${i}`)) constants.push(C(i));
  const [C1, C2, C3] = [at(constants, 0), at(constants, 1), at(constants, 2)];
  const u = new Dummy('u');
  const time = add(integrate(first(coefficients), t), C3);
  const solutions: Expr[][] = [];
  for (const sy of [-1, 1]) for (const sz of [-1, 1]) {
    const y = mul(sy, pow(add(mul(b, pow(u, 2)), C1), S.Half));
    const z = mul(sz, pow(add(mul(c, pow(u, 2)), C2), S.Half));
    // One quadrature and two algebraic relations share the same constants and signs.
    // Independent quadratures for X,Y,Z would introduce inconsistent phase constants.
    const quadrature = new Integral([pow(mul(y, z), -1), u, X]);
    solutions.push([Eq(quadrature, time), Eq(Y, xreplace(y, [[u, X]])), Eq(Z, xreplace(z, [[u, X]]))]);
  }
  return solutions;
}

/**
 * A triangular (possibly nonlinear) system: an equation in one unknown
 * function is solved first, its solution substituted into the others, and so
 * on; the constants are numbered in that order. An equation with several
 * solutions gives a solution list for each (SymPy's list of solution lists).
 */
function triangularSystem(eqs: readonly Expr[], funcs: readonly UndefFn[], options: { simplify?: boolean; doit?: boolean }): Expr[][] {
  const out: Expr[][] = [];
  const step = (remaining: readonly Expr[], solved: ReadonlyMap<string, Expr>, nextC: number): void => {
    if (!remaining.length) {
      out.push(funcs.map((f) => Eq(f, getOrThrow(solved, f.key))));
      return;
    }
    const idx = remaining.findIndex((e) => funcs.filter((f) => !solved.has(f.key) && e.has(f)).length === 1);
    const pending = funcs.filter((f) => !solved.has(f.key));
    let block: UndefFn[];
    let rows: readonly Expr[];
    if (idx >= 0 && (options.simplify !== false || idx === 0)) {
      rows = [at(remaining, idx)];
      block = [defined(pending.find((f) => first(rows).has(f)), 'unknown function')];
    } else {
      // Edges point from each differentiated function to its dependencies.
      // Tarjan returns a closed component first.
      const owners = findFunctions(remaining);
      if (owners.length !== remaining.length) throw new NotImplementedError('dsolve: cannot isolate a differential component');
      const edges = remaining.flatMap((eq, i) => pending.filter((f) => eq.has(f)).map((f) => [at(owners,i), f] as const));
      block = first(stronglyConnectedComponents([pending, edges]));
      if (block.length >= funcs.length) throw new NotImplementedError('dsolve: only linear or triangular systems are supported');
      rows = block.map((f) => at(remaining, owners.findIndex((g) => g.equals(f))));
    }
    const rest = remaining.filter((e) => !rows.includes(e));
    const known = [...solved.values()].flatMap((v) => [...v.freeSymbols()].filter((s) => s instanceof Sym).filter((c) => /^C\d+$/.test(c.name)));
    const protect = [...new Map(known.map((c) => [c.key, c])).values()].map((c) => [c, new Dummy(c.name)] as [Expr, Expr]);
    const substituteKnown = (eq: Expr): Expr => {
      let e = eq;
      for (const f of funcs) if (solved.has(f.key)) e = subFuncDoit(e, f, getOrThrow(solved, f.key));
      return xreplace(e, protect);
    };
    let families: Expr[][];
    if (block.length === 1) {
      const f = first(block), row = first(rows), t = cast(first(f.args), Sym);
      const df = derivativeOf(f, t, 1);
      const higher = subexprs(row, (e) => e instanceof Derivative && e.expr.equals(f) && !e.equals(df));
      const linear = !higher.length ? systemMatrices(rows, block, t, 1) : undefined;
      if (linear && !isZero(first(linear[0]).get(0, 0))) {
        // Extract the forcing before substituting solved functions. This keeps
        // powers of earlier quadratures intact in the integrating-factor formula.
        const lead = pow(substituteKnown(first(linear[0]).get(0, 0)), -1);
        const basis = exp(integrate(mul(lead, substituteKnown(at(linear[0], 1).get(0, 0))), t));
        const forcing = substituteKnown(linear[1].get(0, 0));
        const kernel = expandMulOnly(mul(lead, forcing, pow(basis, -1)));
        const particular = isZero(kernel) ? S.Zero : mul(basis, options.doit === false ? new Integral([kernel, t]) : integrate(kernel, t));
        families = [[Eq(f, add(mul(C(1), basis), particular))]];
      } else {
        families = [dsolveOne(substituteKnown(row), f)].flat().map((sol) => [sol]);
      }
    } else {
      families = dsolveSystemAll(rows.map(substituteKnown), block, options);
    }
    for (const family of families) {
      const constants = family.flatMap((sol) => [...sol.freeSymbols()].filter((c): c is Sym => c instanceof Sym && !(c instanceof Dummy) && /^C\d+$/.test(c.name)));
      const cs = [...new Map(constants.map((c) => [c.key,c])).values()].sort((a,b) => Number(a.name.slice(1)) - Number(b.name.slice(1)));
      const rename = cs.map((c,i): [Expr,Expr] => [c,C(nextC+i)]);
      const next = new Map(solved);
      for (const sol of family) {
        const rel = cast(sol, Rel, 'solution');
        next.set(rel.lhs.key, xreplace(xreplace(rel.rhs, rename), protect.map(([c,d]) => [d,c])));
      }
      step(rest, next, nextC + cs.length);
    }
  };
  step(eqs, new Map(), 1);
  return out;
}

// ---------------------------------------------------------------------------
// checkodesol (port of SymPy sympy.solvers.ode.subscheck, BSD 3-Clause,
// Copyright (c) SymPy Development Team): substitution of explicit solutions
// ---------------------------------------------------------------------------

const isList = (v: unknown): v is readonly ExprLike[] => Array.isArray(v);

/** The subexpressions of e that satisfy pred. */
function subexprs(e: Expr, pred: (x: Expr) => boolean): Expr[] {
  const out = new Map<string, Expr>();
  const go = (x: Expr) => {
    if (pred(x)) out.set(x.key, x);
    x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/**
 * Func replaced by value in eq, with the derivatives of func evaluated.
 *
 * @param eqIn - The equation, or an expression equal to zero.
 * @param funcIn - The dependent function applied to its arguments.
 * @param valueIn - The expression to substitute for the unknown function.
 * @returns The equation after substitution and differentiation.
 * @see SymPy `sympy.solvers.ode.subscheck.sub_func_doit`
 * @example
 * ```ts
 * import { ex, subFuncDoit } from '@symjs/symjs';
 * subFuncDoit(ex`3*Derivative(y(x), x) - 1`, ex`y(x)`, ex`x`); // => 2
 * ```
 */
export function subFuncDoit(eqIn: ExprLike, funcIn: ExprLike, valueIn: ExprLike): Expr {
  const [eq, func, value] = [sympify(eqIn), sympify(funcIn), sympify(valueIn)];
  const reps: [Expr, Expr][] = [[func, value]];
  for (const d of subexprs(eq, (x) => x instanceof Derivative)) {
    const dv = cast(d, Derivative, 'derivative');
    let r: Expr;
    if (dv.expr.key === func.key) {
      r = value;
      for (const [v, n] of dv.variableCount) r = diff(r, v, n);
    } else r = doit(xreplace(dv, [[func, value]]));
    reps.push([d, r]);
  }
  return xreplace(eq, reps);
}

/** The residual eq made zero when possible (SymPy checksysodesol; sqrtdenest is not applied). */
function reduceResidual(eq: Expr): Expr {
  const ss = simplify(eq);
  return isZero(ss) ? S.Zero : simplify(expand(ss, { force: true }));
}

/** The solution solved for its function: [func, rhs]. */
function solvedFor(solIn: Expr, func?: Expr): [Expr, Expr] {
  const fs = func ? [func] : subexprs(solIn, (x) => x instanceof UndefFn);
  if (fs.length !== 1) throw new RangeError('solutions should have one function only');
  const f = first(fs);
  const [l, r] = solIn instanceof Rel && solIn.op === 'Eq' ? [solIn.lhs, solIn.rhs] : [f, solIn];
  const [lhs, rhs] = r.key === f.key ? [r, l] : [l, r];
  if (lhs.key !== f.key || rhs.has(f)) throw new NotImplementedError('checkodesol: only solutions solved for the function are supported');
  return [f, rhs];
}

/**
 * Substitutes the solution into the ODE and
 * checks that the result is 0. For a system (arrays of equations and of
 * solutions, one per function) the result is `[true, [0, 0, ...]]` when every
 * equation vanishes, else `[false, residuals]`; for one equation
 * `[true, 0]` or `[false, residual]`. Solutions must be explicit (solved for
 * the function); SymPy's further methods for implicit solutions are not
 * ported.
 *
 * @remarks SymPy returns `(False, 2)`.
 *
 * @param ode - The differential equation to check.
 * @param sol - The proposed solution.
 * @returns The verification flag and the residual after substitution.
 * @see SymPy `sympy.solvers.ode.subscheck.checkodesol`
 * @example
 * ```ts
 * import { checkodesol, ex } from '@symjs/symjs';
 * checkodesol(ex`Derivative(f(x), (x, 2))`, ex`x**2`); // => [False, 2]
 * ```
 */
export function checkodesol(ode: readonly ExprLike[], sol: ExprLike | readonly ExprLike[]): [boolean, Expr[]];
/**
 * Substitutes the solution into the ODE and
 * checks that the result is 0. For a system (arrays of equations and of
 * solutions, one per function) the result is `[true, [0, 0, ...]]` when every
 * equation vanishes, else `[false, residuals]`; for one equation
 * `[true, 0]` or `[false, residual]`. Solutions must be explicit (solved for
 * the function); SymPy's further methods for implicit solutions are not
 * ported.
 *
 * @param ode - The differential equation to check.
 * @param sol - The proposed solution.
 * @param func - The dependent function applied to its arguments.
 * @returns The verification flag and the residual after substitution.
 * @see SymPy `sympy.solvers.ode.subscheck.checkodesol`
 */
export function checkodesol(ode: ExprLike, sol: readonly ExprLike[], func?: Expr): [boolean, Expr][];
/**
 * Substitutes the solution into the ODE and
 * checks that the result is 0. For a system (arrays of equations and of
 * solutions, one per function) the result is `[true, [0, 0, ...]]` when every
 * equation vanishes, else `[false, residuals]`; for one equation
 * `[true, 0]` or `[false, residual]`. Solutions must be explicit (solved for
 * the function); SymPy's further methods for implicit solutions are not
 * ported.
 *
 * @param ode - The differential equation to check.
 * @param sol - The proposed solution.
 * @param func - The dependent function applied to its arguments.
 * @returns The verification flag and the residual after substitution.
 * @see SymPy `sympy.solvers.ode.subscheck.checkodesol`
 */
export function checkodesol(ode: ExprLike, sol: ExprLike, func?: Expr): [boolean, Expr];
/**
 * Substitutes the solution into the ODE and
 * checks that the result is 0. For a system (arrays of equations and of
 * solutions, one per function) the result is `[true, [0, 0, ...]]` when every
 * equation vanishes, else `[false, residuals]`; for one equation
 * `[true, 0]` or `[false, residual]`. Solutions must be explicit (solved for
 * the function); SymPy's further methods for implicit solutions are not
 * ported.
 *
 * @param ode - The differential equation to check.
 * @param sol - The proposed solution.
 * @param func - The dependent function applied to its arguments.
 * @returns The verification flag and the residual after substitution.
 * @throws RangeError when number of solutions provided does not match the number of equations.
 * @see SymPy `sympy.solvers.ode.subscheck.checkodesol`
 */
export function checkodesol(ode: ExprLike | readonly ExprLike[], sol: ExprLike | readonly ExprLike[], func?: Expr): [boolean, Expr] | [boolean, Expr[]] | [boolean, Expr][] {
  const residual = (e: Expr): Expr => (e instanceof Rel && e.op === 'Eq' ? add(e.lhs, mul(-1, e.rhs)) : e);
  if (isList(ode)) {
    const eqs = ode.map((e) => residual(sympify(e)));
    const sols = (isList(sol) ? sol : [sol]).map((s) => solvedFor(sympify(s)));
    const funcs = new Map<string, Expr>();
    for (const e of eqs) for (const d of subexprs(e, (x) => x instanceof Derivative)) for (const f of subexprs(d, (x) => x instanceof UndefFn)) funcs.set(f.key, f);
    if (funcs.size !== new Set(sols.map(([f]) => f.key)).size) throw new RangeError('number of solutions provided does not match the number of equations');
    const dict = new Map(sols.map(([f, r]) => [f.key, r]));
    const checks = eqs.map((e) => {
      let r = e;
      for (const f of funcs.values()) r = subFuncDoit(r, f, getOrThrow(dict, f.key));
      // Collect the coefficient of each independent trigonometric term
      // before denesting. This avoids expanding its phase at every step.
      const terms = subexprs(r, (e) => e.kind === 'Fn' && ('name' in e && (e.name === 'sin' || e.name === 'cos')));
      if (terms.length) r = collect(expand(r), terms, { func: (c) => simplify(sqrtdenest(c)) });
      return reduceResidual(r);
    });
    return [checks.every(isZero), checks];
  }
  if (isList(sol)) return sol.map((s) => checkodesol(ode, s, func));
  const eq = residual(sympify(ode));
  const s0 = sympify(sol);
  // the function: the one differentiated in the equation, else the one in the solution
  const inEq = new Map<string, Expr>();
  for (const d of subexprs(eq, (e) => e instanceof Derivative)) for (const g of subexprs(d, (e) => e instanceof UndefFn)) inEq.set(g.key, g);
  const dependent = func ?? (inEq.size === 1 ? first([...inEq.values()]) : undefined);
  if (dependent instanceof UndefFn && s0 instanceof Rel && s0.lhs instanceof Integral && s0.lhs.args.length === 3 && at(s0.lhs.args, 2).equals(dependent) && !s0.rhs.has(dependent)) {
    const x = cast(first(dependent.args), Sym);
    const kernel = s0.lhs.integrand;
    if (!kernel.has(x)) {
      const velocity = mul(diff(s0.rhs, x), pow(xreplace(kernel, [[s0.lhs.variable, dependent]]), -1));
      const jets: [Expr, Expr][] = [];
      let v = velocity;
      const order = Math.max(0, ...subexprs(eq, (e) => e instanceof Derivative && e.expr.equals(dependent)).map((e) => cast(e, Derivative).variableCount.reduce((a, [, k]) => a + k, 0)));
      for (let k = 1; k <= order; k++) {
        jets.push([derivativeOf(dependent, x, k), v]);
        v = xreplace(diff(v, x), [[derivativeOf(dependent, x, 1), velocity]]);
      }
      const r = reduceResidual(xreplace(eq, jets));
      return [isZero(r), r];
    }
  }
  const [f, rhs] = solvedFor(s0, dependent);
  const order = getO(rhs);
  if (order instanceof Order && f instanceof UndefFn && f.args.length === 1) {
    const x = first(f.args);
    if (order.expr instanceof Pow && order.expr.base.equals(x) && (order.args.length === 1 || at(order.args, -1).equals(S.Zero))) {
      const degree = Math.max(0, ...subexprs(eq, (e) => e instanceof Derivative && e.expr.equals(f)).map((e) => cast(e, Derivative).variableCount.reduce((a, [, k]) => a + k, 0)));
      const truncated = expand(subFuncDoit(eq, f, removeO(rhs)));
      const remainder = new Order([pow(x, add(order.expr.exp, -degree)), x, S.Zero]);
      const r = reduceResidual(removeO(add(truncated, remainder)));
      return [isZero(r), r];
    }
  }
  const r = reduceResidual(subFuncDoit(eq, f, rhs));
  return [isZero(r), r];
}

/**
 * Checkodesol of a system of ODEs (one equation and
 * one solution per function): [true, [0, 0, ...]] when the solutions satisfy
 * the equations, else [false, residuals].
 *
 * @param eqs - The equations to solve simultaneously.
 * @param sols - The candidate solutions.
 * @returns The verification flag and the residual after substitution.
 * @see SymPy `sympy.solvers.ode.subscheck.checksysodesol`
 * @example
 * ```ts
 * import { checksysodesol, ex } from '@symjs/symjs';
 * checksysodesol([ex`Derivative(f(x), x) - f(x)`], [ex`Eq(f(x), exp(x))`]); // => [True, [0]]
 * ```
 */
export function checksysodesol(eqs: readonly ExprLike[], sols: readonly ExprLike[]): [boolean, Expr[]] {
  return checkodesol(eqs, sols);
}

/**
 * A derivative exceeds the requested order of the matrix equation.
 *
 * @see SymPy `sympy.solvers.ode.systems.ODEOrderError`
 */
export class ODEOrderError extends RangeError {}
/**
 * An ODE system is nonlinear in the dependent functions or their derivatives.
 *
 * @see SymPy `sympy.solvers.ode.systems.ODENonlinearError`
 */
export class ODENonlinearError extends RangeError {}

/**
 * Express A_n X^(n) = A_(n-1) X^(n-1) + ... + A_0 X + b.
 *
 * @param equations - The equations to solve simultaneously.
 * @param funcs - The dependent variables of the system of ODEs.
 * @param t - The independent variable.
 * @param order - The order of the system of ODEs.
 * @returns The coefficient matrices by derivative order and the forcing column.
 * @throws RangeError when the order is negative or nonintegral.
 * @throws ODENonlinearError when the system of ODEs is nonlinear.
 * @see SymPy `sympy.solvers.ode.systems.linear_ode_to_matrix`
 * @example
 * ```ts
 * import { AppliedUndef, ex, linearOdeToMatrix, symbols } from '@symjs/symjs';
 *
 * const [t] = symbols('t');
 * linearOdeToMatrix([ex`Derivative(f(t), t) - f(t)`], [new AppliedUndef('f', [t])], t, 1); // => [[Matrix([[1]]), Matrix([[1]])], Matrix([[0]])]
 * ```
 */
export function linearOdeToMatrix(equations: readonly Expr[], funcs: readonly UndefFn[], t: Sym, order: number): [Matrix[], Matrix] {
  if (!Number.isInteger(order) || order < 0) throw new RangeError('order must be a nonnegative integer');
  const check = (e: Expr): void => {
    if (e instanceof Derivative && funcs.some((f) => f.equals(e.expr)) && e.variableCount.reduce((n, [, k]) => n + k, 0) > order) {
      throw new ODEOrderError(`Cannot represent system in ${order}-order form`);
    }
    e.args.forEach(check);
  };
  equations.forEach(check);
  const system = systemMatrices(equations, funcs, t, order);
  if (!system) throw new ODENonlinearError('The system of ODEs is nonlinear.');
  return system;
}

function systemMatrices(equations: readonly Expr[], funcs: readonly UndefFn[], t: Sym, order: number): [Matrix[], Matrix] | undefined {
  const jets: Expr[] = [];
  for (let k = order; k >= 0; k--) for (const f of funcs) jets.push(k === 0 ? f : new Derivative([f, t, mul(S.One, k)]));
  const variables = jets.map((_, i) => new Dummy(`jet${i}`));
  const substitutions = jets.map((jet, i): [Expr, Expr] => [jet, at(variables, i)]);
  const eqs = equations.map((e) => expand(xreplace(asEquation(e), substitutions)));
  const result = linearEqToMatrix(eqs, variables);
  if (result === undefined) return undefined;
  const [matrix, rhs] = result;
  const matrices = Array.from({ length: order + 1 }, (_, i) => Matrix.of(Array.from({ length: equations.length }, (_, row) => funcs.map((_, col) => mul(i === 0 ? 1 : -1, matrix.get(row, i * funcs.length + col))))));
  return [matrices, rhs.map((e) => add(e))];
}
