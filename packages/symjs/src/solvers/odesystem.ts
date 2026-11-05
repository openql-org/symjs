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
import { Derivative, Dummy, I, Integral, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { asNumerDenom } from '../core/methods';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { isReal } from '../core/assumptions';
import { SymFunction } from '../core/undef';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { doit } from '../calculus/doit';
import { Eq } from '../core/logic';
import { cos, im, log, re, sin } from '../functions/elementary/elementary';
import { factor } from '../polys/sympoly';
import { cancel } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { jordanForm } from '../matrices/linalg';
import { linearEqToMatrix, solve } from './solve';

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
 * SymPy dsolve([eq1, eq2, ...], [f(t), g(t), ...]): a list of solutions
 * [Eq(f(t), ...), Eq(g(t), ...)], or, like SymPy, a list of such lists when the
 * system has several solution families (a nonlinear triangular system).
 */
export function dsolveSystem(eqsIn: readonly ExprLike[], funcsIn?: readonly UndefFn[]): Expr[] | Expr[][] {
  const sols = dsolveSystemAll(eqsIn, funcsIn);
  return sols.length === 1 ? first(sols) : sols;
}

/** Every solution list of the system. */
function dsolveSystemAll(eqsIn: readonly ExprLike[], funcsIn?: readonly UndefFn[]): Expr[][] {
  const eqs = eqsIn.map((e) => {
    const x = sympify(e);
    return x instanceof Rel && x.op === 'Eq' ? add(x.lhs, mul(-1, x.rhs)) : x;
  });
  const funcs = funcsIn ?? findFunctions(eqs);
  const n = funcs.length;
  if (n === 0 || eqs.length !== n) throw new TypeError('dsolve: as many equations as functions are needed');
  const t = cast(first(first(funcs).args), Sym);
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
    const nl = n === 2 ? nonlinear2(eqs, [first(funcs), at(funcs, 1)], t) : undefined;
    return nl ?? triangularSystem(eqs, funcs);
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
    const scaled = constantTimesFunction(A, t);
    if (scaled && b.data.every((e) => isZero(e))) {
      // A = phi(t)*M with M constant: the solution of x' = M*x at tau = Integral(phi)
      const [phi, M] = scaled;
      const tau = integrate(phi, t);
      const s = new Dummy('s');
      const Phi = fundamentalSolutions(M, s).reduce((acc, c) => acc.hstack(c));
      const Cs = Array.from({ length: n }, (_, i) => new Sym(`C${i + 1}`));
      const sol = Phi.mul(Matrix.col(...Cs));
      return [funcs.map((f, i) => Eq(f, expand(xreplace(sol.get(i, 0), [[s, tau]]))))];
    }
    if (n === 2 && b.data.every((e) => isZero(e))) return [linear2VariableCoefficients(A, funcs, t)];
    return triangularSystem(eqs, funcs);
  }
  const fundamental = fundamentalSolutions(A, t);
  const Phi = fundamental.reduce((acc, c) => acc.hstack(c));
  const Cs = Array.from({ length: n }, (_, i) => new Sym(`C${i + 1}`));
  let sol = Phi.mul(Matrix.col(...Cs));
  if (b.data.some((e) => !isZero(e))) {
    // variation of parameters: Phi * Integral(Phi**-1 * b)
    const g = Phi.inv().mul(b).map((e) => simplify(e));
    const part = Phi.mul(g.map((e) => integrate(e, t))).map((e) => simplify(expand(e)));
    sol = sol.add(part);
  }
  return [funcs.map((f, i) => Eq(f, expand(sol.get(i, 0))))];
}

/**
 * A = phi(t)*M with M constant, phi the (common) factor of one nonzero entry
 * that has t, or undefined.
 */
function constantTimesFunction(A: Matrix, t: Sym): [Expr, Matrix] | undefined {
  const ref = defined(A.data.find((e) => e.has(t)), 'entry with t');
  const M = A.map((e) => simplify(mul(e, pow(ref, -1))));
  return M.data.some((e) => e.has(t)) ? undefined : [ref, M];
}

/** n real fundamental solutions (columns) of x' = A*x. */
function fundamentalSolutions(A: Matrix, t: Sym): Matrix[] {
  const n = A.rows;
  const [P, J] = jordanForm(A);
  // a real A has its complex eigenvalues in conjugate pairs with the same Jordan
  // structure, each pair giving two real solutions; a complex A keeps exp(lam*t)
  const realA = A.data.every((e) => isReal(e) === true);
  const out: Matrix[] = [];
  let i = 0;
  while (i < n) {
    const lam = J.get(i, i);
    // block size
    let k = 1;
    while (i + k < n && J.get(i + k - 1, i + k).key === S.One.key && J.get(i + k, i + k).key === lam.key) k++;
    const c = lam.toComplex();
    const complexPair = realA && Math.abs(c.im) > 1e-14;
    for (let j = 0; j < k; j++) {
      // the j-th chain solution: e^(lam*t) * sum_{m<=j} t**(j-m)/(j-m)! * P_col(i+m)
      let v = Matrix.zeros(n, 1);
      for (let m = 0; m <= j; m++) {
        let fact = 1n;
        for (let q = 2n; q <= BigInt(j - m); q++) fact *= q;
        v = v.add(P.col(i + m).scale(mul(pow(t, j - m), Rational.of(1n, fact))));
      }
      if (!complexPair) out.push(v.scale(exp(mul(lam, t))).map((e) => simplify(e)));
      else if (c.im < 0) {
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
  const rhs = cast(first([r].flat()), Rel, 'solution').rhs;
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

/**
 * A triangular (possibly nonlinear) system: an equation in one unknown
 * function is solved first, its solution substituted into the others, and so
 * on; the constants are numbered in that order. An equation with several
 * solutions gives a solution list for each (SymPy's list of solution lists).
 */
function triangularSystem(eqs: readonly Expr[], funcs: readonly UndefFn[]): Expr[][] {
  const out: Expr[][] = [];
  const step = (remaining: readonly Expr[], solved: ReadonlyMap<string, Expr>, nextC: number): void => {
    if (!remaining.length) {
      out.push(funcs.map((f) => Eq(f, getOrThrow(solved, f.key))));
      return;
    }
    const idx = remaining.findIndex((e) => funcs.filter((f) => !solved.has(f.key) && e.has(f)).length === 1);
    if (idx < 0) throw new NotImplementedError('dsolve: only linear or triangular systems are supported');
    const e = at(remaining, idx);
    const rest = remaining.filter((_, i) => i !== idx);
    const f = defined(funcs.find((g) => !solved.has(g.key) && e.has(g)), 'unknown function');
    // constants of the solutions already substituted are protected while solving
    const known = [...solved.values()].flatMap((v) => [...v.freeSymbols()].filter((c) => /^C\d+$/.test(c.name)));
    const protect = [...new Map(known.map((c) => [c.key, c])).values()].map((c) => [c, new Dummy(c.name)] as [Expr, Expr]);
    const sub = xreplace(xreplace(e, [...solved.entries()].map(([k, v]) => [defined(funcs.find((g) => g.key === k), 'solved function'), v] as [Expr, Expr])), protect);
    const r = dsolveOne(sub, f);
    for (const sol of Array.isArray(r) ? r : [r]) {
      let rhs = cast(sol, Rel, 'solution').rhs;
      // the new constants continue the numbering
      const cs = [...rhs.freeSymbols()].filter((c) => /^C\d+$/.test(c.name) && !(c instanceof Dummy)).sort((a, b) => Number(a.name.slice(1)) - Number(b.name.slice(1)));
      rhs = xreplace(rhs, cs.map((c, i) => [c, new Sym(`C${nextC + i}`)] as [Expr, Expr]));
      rhs = xreplace(rhs, protect.map(([c, d]) => [d, c] as [Expr, Expr]));
      step(rest, new Map([...solved, [f.key, rhs]]), nextC + cs.length);
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

/** SymPy sub_func_doit: func replaced by value in eq, with the derivatives of func evaluated. */
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
 * SymPy `checkodesol(ode, sol)`: substitutes the solution into the ODE and
 * checks that the result is 0. For a system (arrays of equations and of
 * solutions, one per function) the result is `[true, [0, 0, ...]]` when every
 * equation vanishes, else `[false, residuals]`; for one equation
 * `[true, 0]` or `[false, residual]`. Solutions must be explicit (solved for
 * the function); SymPy's further methods for implicit solutions are not
 * ported.
 */
export function checkodesol(ode: readonly ExprLike[], sol: ExprLike | readonly ExprLike[]): [boolean, Expr[]];
export function checkodesol(ode: ExprLike, sol: ExprLike, func?: Expr): [boolean, Expr];
export function checkodesol(ode: ExprLike | readonly ExprLike[], sol: ExprLike | readonly ExprLike[], func?: Expr): [boolean, Expr] | [boolean, Expr[]] {
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
      return reduceResidual(r);
    });
    return [checks.every(isZero), checks];
  }
  if (isList(sol)) throw new TypeError('checkodesol: one solution is expected for one equation');
  const eq = residual(sympify(ode));
  const s0 = sympify(sol);
  // the function: the one differentiated in the equation, else the one in the solution
  const inEq = new Map<string, Expr>();
  for (const d of subexprs(eq, (e) => e instanceof Derivative)) for (const g of subexprs(d, (e) => e instanceof UndefFn)) inEq.set(g.key, g);
  const [f, rhs] = solvedFor(s0, func ?? (inEq.size === 1 ? first([...inEq.values()]) : undefined));
  const r = reduceResidual(subFuncDoit(eq, f, rhs));
  return [isZero(r), r];
}

/**
 * SymPy checksysodesol: checkodesol of a system of ODEs (one equation and
 * one solution per function): [true, [0, 0, ...]] when the solutions satisfy
 * the equations, else [false, residuals].
 */
export function checksysodesol(eqs: readonly ExprLike[], sols: readonly ExprLike[]): [boolean, Expr[]] {
  return checkodesol(eqs, sols);
}
