// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The lie_group hint of dsolve (port of SymPy solvers/ode/lie_group.py,
 * with checkinfsol from solvers/ode/ode.py and the first-order linear PDE
 * solvers of solvers/pde.py that it needs): the infinitesimals xi, eta of a
 * symmetry of y' = h(x, y) are found by heuristics, the canonical coordinates
 * r, s by solving xi*r_x + eta*r_y = 0 and xi*s_x + eta*s_y = 1, and the
 * equation, separable in r and s, by quadrature.
 *
 * References: E.S. Cheb-Terrab, L.G.S. Duarte and L.A.C.P. da Mota, Computer
 * Algebra Solving of First Order ODEs Using Symmetry Methods; E.S. Cheb-Terrab,
 * A.D. Roche, Symmetries and First Order ODE Patterns; Lie Groups and
 * Differential Equations, pp. 327-329.
 */

import { NotImplementedError } from '../core/errors';
import type { ExprLike } from '../core/nodes';
import { Add, Derivative, Dummy, Expr, Integral, Mul, Pow, Rational, Rel, S, Sym, UndefFn, Wild } from '../core/nodes';
import { Eq } from '../core/logic';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { match as matchPattern } from '../core/match';
import { asNumerDenom, isPolynomial, isRationalFunction } from '../core/methods';
import { countOps, freeSymbols, mapBottomUp, some, subs, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { SubsNode } from '../core/subsnode';
import { doit } from '../calculus/doit';
import { log } from '../functions/elementary/elementary';
import { integrate } from '../integrals/integrate';
import { reduced } from '../polys/groebner';
import { Poly } from '../polys/sympoly';
import { expand } from '../simplify/expand';
import { factorTerms } from '../simplify/exprtools';
import { powsimp } from '../simplify/powsimp';
import { cancel, together } from '../simplify/rational';
import { separatevars } from '../simplify/separatevars';
import { simplify } from '../simplify/simplify';
import { linsolve, solve } from './solve';

/** SymPy lie_heuristics, in the order the default hint tries them. */
export const LIE_HEURISTICS = [
  'abaco1_simple', 'abaco1_product', 'abaco2_similar', 'abaco2_unique_unknown', 'abaco2_unique_general', 'linear', 'function_sum', 'bivariate',
  'chi',
] as const;
export type LieHeuristic = (typeof LIE_HEURISTICS)[number];

/** A pair of infinitesimals; etaFirst keeps the key order of SymPy's dict. */
interface Inf {
  xi: Expr;
  eta: Expr;
  etaFirst: boolean;
}

/** The data of y' = h(x, y) the heuristics use (SymPy's match dict). */
interface LieMatch {
  h: Expr;
  hx: Expr;
  hy: Expr;
  /** h with x and y exchanged, inverted: the equation dx/dy = 1/h. */
  hinv: Expr;
  x: Sym;
  y: Dummy;
  func: UndefFn;
}

/** Bound variables shared by every Subs that diff creates here (one per position). */
const SUBS_VARS: Dummy[] = [];
/**
 * diff, with the bound variables of the Subs it creates (the derivatives of
 * an unknown function at a point) made the same, so that equal derivatives
 * cancel (SymPy compares Subs up to their bound variables).
 */
function d(e: Expr, v: Expr, n = 1): Expr {
  return mapBottomUp(diff(e, v, n), (u) => {
    if (!(u instanceof SubsNode) || !u.variables.every((w) => w instanceof Dummy)) return u;
    const reps = u.variables.map((w, i): [Expr, Expr] => {
      while (SUBS_VARS.length <= i) SUBS_VARS.push(new Dummy(`xi_${SUBS_VARS.length + 1}`));
      return [w, at(SUBS_VARS, i)];
    });
    return new SubsNode([xreplace(u.expr, reps), ...reps.map(([, c]) => c), ...u.point]);
  });
}

const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const inf = (xi: Expr, eta: Expr, etaFirst = false): Inf => ({ xi, eta, etaFirst });
const sameInf = (a: Inf, b: Inf): boolean => a.xi.key === b.xi.key && a.eta.key === b.eta.key;

/** The dict {xi(x, f(x)): xi, eta(x, f(x)): eta} SymPy returns. */
function infMap(i: Inf, x: Sym, func: UndefFn): Map<Expr, Expr> {
  const xiKey = new UndefFn('xi', [x, func]);
  const etaKey = new UndefFn('eta', [x, func]);
  return new Map<Expr, Expr>(i.etaFirst ? [[etaKey, i.eta], [xiKey, i.xi]] : [[xiKey, i.xi], [etaKey, i.eta]]);
}

/** The value of separatevars(e, dict=True, symbols=[x, y]) for a key ('coeff', x or y). */
type Sep = Map<Sym | 'coeff', Expr>;
function sepDict(e: Expr, x: Sym, y: Sym): Sep | undefined {
  const r = separatevars(e, { dict: true, symbols: [x, y] });
  return r instanceof Map ? r : undefined;
}

/** Exchange x and y. */
const swapXY = (e: Expr, x: Sym, y: Sym): Expr => xreplace(e, [[x, y], [y, x]]);

// ---------------------------------------------------------------------------
// heuristics
// ---------------------------------------------------------------------------

/** xi = 0, eta = f(x); xi = 0, eta = f(y); xi = f(x), eta = 0; xi = f(y), eta = 0. */
function abaco1Simple(m: LieMatch, comp: boolean): Inf[] {
  const { y, h, x, hx, hy, func } = m;
  const back = (e: Expr): Expr => xreplace(e, [[y, func]]);
  // [the test, the infinitesimals], tried in SymPy's order
  const tries: [() => boolean, () => Inf][] = [
    [() => !hy.has(y), () => inf(S.Zero, exp(integrate(hy, x)))],
    [() => !mul(hy, pow(h, -1)).has(x), () => inf(S.Zero, back(exp(integrate(mul(hy, pow(h, -1)), y))))],
    [() => !mul(hx, pow(h, -1)).has(y), () => inf(exp(integrate(mul(-1, hx, pow(h, -1)), x)), S.Zero)],
    [() => !mul(hx, pow(h, -2)).has(x), () => inf(back(exp(integrate(mul(-1, hx, pow(h, -2)), y))), S.Zero)],
  ];
  const out: Inf[] = [];
  for (const [test, make] of tries) {
    if (comp ? !test() : out.length > 0 || !test()) continue;
    const i = make();
    if (!out.some((o) => sameInf(o, i))) out.push(i);
  }
  return out;
}

/** eta = 0, xi = f(x)*g(y), or eta = f(x)*g(y), xi = 0 (the equation inverted). */
function abaco1Product(m: LieMatch, comp: boolean): Inf[] {
  const { y, h, hinv, x, func } = m;
  const out: Inf[] = [];
  for (const [fac, inverted] of [[h, false], [hinv, true]] as const) {
    const sep = sepDict(mul(d(d(log(fac), y), x), pow(fac, -2)), x, y);
    if (!sep || isZero(getOrThrow(sep, 'coeff'))) continue;
    const fx = getOrThrow(sep, x);
    const gy0 = simplify(mul(fx, d(pow(mul(fx, fac), -1), x)));
    if (gy0.has(x)) continue;
    const val = mul(fx, exp(integrate(gy0, y)));
    out.push(inverted ? inf(S.Zero, xreplace(swapXY(val, x, y), [[y, func]]), true) : inf(xreplace(val, [[y, func]]), S.Zero, true));
  }
  return comp ? out : out.slice(0, 1);
}

/** The coefficients of a polynomial in x and y (the equations for its vanishing identically). */
function polyCoeffEqs(e: Expr, x: Sym, y: Sym): Expr[] {
  return Poly.from(e, [x, y]).asDict().map(([, c]) => c);
}

/**
 * Solve the homogeneous linear equations for the unknowns (SymPy solve
 * returning a dict): the values with the free unknowns set to 1, or undefined
 * when the only solution is zero (SymPy also gives up when the solved
 * unknowns are zero and only free ones are not, a nonzero solution as well).
 */
function nontrivialSolution(eqs: readonly Expr[], unknowns: readonly Sym[]): [Sym, Expr][] | undefined {
  const vals = linsolve(eqs, unknowns);
  if (!vals?.some((v, i) => v.key === at(unknowns, i).key)) return undefined;
  const ones = unknowns.map((u): [Sym, Expr] => [u, S.One]);
  return unknowns.map((u, i) => [u, xreplace(at(vals, i), ones)]);
}

/** The monomials x**p*y**(i - p) of total degree i with fresh coefficients name_p_(i-p) (added to unknowns). */
function homogeneousTerms(name: string, i: number, x: Sym, y: Sym, unknowns: Sym[]): Expr {
  return add(
    ...Array.from({ length: i + 1 }, (_, p) => {
      const c = new Dummy(`${name}_${p}_${i - p}`);
      unknowns.push(c);
      return mul(c, pow(x, p), pow(y, i - p));
    }),
  );
}

/** xi and eta bivariate polynomials in x and y (h a rational function). */
function bivariate(m: LieMatch): Inf[] {
  const { h, hx, hy, x, y, func } = m;
  if (!isRationalFunction(h)) return [];
  const xi0 = new Dummy('xi0');
  const eta0 = new Dummy('eta0');
  const xiSyms: Sym[] = [xi0];
  const etaSyms: Sym[] = [eta0];
  let xieq: Expr = xi0;
  let etaeq: Expr = eta0;
  const attempt = (i: number): Inf[] | undefined => {
    if (i) {
      xieq = add(xieq, homogeneousTerms('xi', i, x, y, xiSyms));
      etaeq = add(etaeq, homogeneousTerms('eta', i, x, y, etaSyms));
    }
    const ipde = add(d(etaeq, x), mul(add(d(etaeq, y), mul(-1, d(xieq, x))), h), mul(-1, d(xieq, y), pow(h, 2)), mul(-1, xieq, hx), mul(-1, etaeq, hy));
    const [pden] = asNumerDenom(ipde);
    const sol = nontrivialSolution(polyCoeffEqs(expand(pden), x, y), [...xiSyms, ...etaSyms]);
    return sol && [inf(xreplace(xreplace(xieq, sol), [[y, func]]), xreplace(xreplace(etaeq, sol), [[y, func]]), true)];
  };
  // the degree of h = P/Q: xi = Q, eta = P satisfy the PDE (the trivial symmetry along the solutions), so that
  // SymPy's search up to the degree of the PDE ends there
  const [P, Q] = asNumerDenom(together(h));
  const top = Math.max(Poly.from(P, [x, y]).totalDegree(), Poly.from(Q, [x, y]).totalDegree());
  for (let i = 0; i < top; i++) {
    const r = attempt(i);
    if (r) return r;
  }
  return defined(attempt(top), 'bivariate infinitesimals');
}

/**
 * Quotient and remainder of the division of p by q (SymPy div): polynomials in
 * x, y, 1/x and 1/y, in that generator order, divided in lex order; undefined
 * when they are not such polynomials.
 */
function divide(p: Expr, q: Expr, x: Sym, y: Sym): [Expr, Expr] | undefined {
  const ix = new Dummy('ix');
  const iy = new Dummy('iy');
  const invOf = (e: Expr, g: Sym, ig: Dummy): Expr => mapBottomUp(e, (u) => (u instanceof Pow && u.base.key === g.key && u.exp instanceof Rational && u.exp.isNegative ? pow(ig, mul(-1, u.exp)) : u));
  const inv = (e: Expr): Expr => invOf(invOf(e, x, ix), y, iy);
  const P = inv(expand(p));
  const Q = inv(expand(q));
  const gens = [x, y, ix, iy].filter((g) => P.has(g) || Q.has(g));
  if (!isPolynomial(P, gens) || !isPolynomial(Q, gens)) return undefined;
  const [[quo], rem] = reduced(P, [Q], gens);
  const back = (e: Expr): Expr => xreplace(e, [[ix, pow(x, -1)], [iy, pow(y, -1)]]);
  return [back(cast(quo, Expr, 'quotient')), back(rem)];
}

/** chi = eta - xi*h a bivariate polynomial solving chi_x + h*chi_y - h_y*chi = 0. */
function chi(m: LieMatch): Inf[] {
  const { h, hy, x, y, func } = m;
  if (!isRationalFunction(h)) return [];
  const [schi, schix, schiy] = [new Dummy('schi'), new Dummy('schix'), new Dummy('schiy')];
  const [num] = asNumerDenom(together(add(schix, mul(h, schiy), mul(-1, hy, schi))));
  const deg = Poly.from(num, [x, y]).totalDegree();
  const chi0 = new Dummy('chi');
  const chiSyms: Sym[] = [chi0];
  let chieq: Expr = chi0;
  for (let i = 1; i <= deg; i++) {
    chieq = add(chieq, homogeneousTerms('chi', i, x, y, chiSyms));
    // the numerator over a common denominator: a factor it shares with the denominator does not change which
    // coefficients vanish (SymPy cancels first, which is slow with the unknown coefficients here)
    const [cnum] = asNumerDenom(together(add(d(chieq, x), mul(h, d(chieq, y)), mul(-1, hy, chieq))));
    const sol = nontrivialSolution(polyCoeffEqs(expand(cnum), x, y), chiSyms);
    if (!sol) continue;
    const qr = divide(xreplace(chieq, sol), h, x, y);
    if (!qr) return [];
    const [xic, etac] = qr;
    return [inf(mul(-1, xreplace(xic, [[y, func]])), xreplace(etac, [[y, func]]), true)];
  }
  return [];
}

/** eta = 0, xi = f(x) + g(y), or eta = f(x) + g(y), xi = 0 (the equation inverted). */
function functionSum(m: LieMatch): Inf[] {
  const { h, hinv, x, y, func } = m;
  for (const [odefac, inverted] of [[h, false], [hinv, true]] as const) {
    const factor = mul(odefac, d(pow(odefac, -1), x, 2));
    const sep = sepDict(d(pow(factor, -1), y), x, y);
    if (!sep || isZero(getOrThrow(sep, 'coeff')) || !getOrThrow(sep, x).has(x) || !getOrThrow(sep, y).has(y)) continue;
    const k = new Dummy('k');
    let gy = mul(k, integrate(getOrThrow(sep, y), y));
    const fdd = pow(mul(k, getOrThrow(sep, x), getOrThrow(sep, 'coeff')), -1);
    let fx = simplify(add(mul(fdd, pow(factor, -1)), mul(-1, gy)));
    const check = simplify(add(d(fx, x, 2), mul(-1, fdd)));
    // k from the condition f'' = fdd when it does not hold identically (SymPy; with fx = 0 the sum is g alone)
    const kk = (isZero(check) ? [S.One] : solve(check, k))[0];
    if (!kk) continue;
    fx = xreplace(fx, [[k, kk]]);
    gy = mul(gy, pow(k, -1), kk);
    if (inverted) {
      fx = xreplace(fx, [[x, y]]);
      gy = xreplace(gy, [[y, x]]);
    }
    let etaval = factorTerms(add(fx, gy));
    if (etaval instanceof Mul) etaval = mul(...etaval.args.filter((a) => a.has(x) || a.has(y)));
    // the conditions above do not ensure a symmetry: SymPy returns, e.g., xi = x**3 + f(x)**3 for
    // f' = 1/(x**3 + f(x)**3), which its checkinfsol rejects; such infinitesimals are not returned here
    const [xi, eta] = inverted ? [S.Zero, etaval] : [etaval, S.Zero];
    if (!isZero(simplify(determiningPde(xi, eta, h, x, y)))) continue;
    // SymPy returns the infinitesimals of the first form that gives some
    return [inf(xreplace(xi, [[y, func]]), xreplace(eta, [[y, func]]), inverted)];
  }
  return [];
}

/** The size of h_y/h_yy above which abaco2_similar gives up (cancel of it is too slow). */
const MAX_SIMILAR_OPS = 120;

/** xi = f(x), eta = g(x), or xi = g(y), eta = f(y) (the equation inverted). */
function abaco2Similar(m: LieMatch): Inf[] {
  const { h, hx, hy, hinv, x, y, func } = m;
  for (const [fac, facx, facy, inverted] of [[h, hx, hy, false], [hinv, d(hinv, x), d(hinv, y), true]] as const) {
    // h linear in y: h_y/h_yy is undefined (SymPy goes on with zoo and returns invalid infinitesimals)
    const fyy = d(fac, y, 2);
    if (isZero(fyy)) continue;
    const quotient = mul(d(fac, y), pow(fyy, -1));
    // cancel of a large quotient with transcendental generators does not finish here (SymPy computes it)
    if (countOps(quotient) > MAX_SIMILAR_OPS) continue;
    const factor = cancel(quotient);
    const result = (tau: Expr, gx: Expr): Inf[] =>
      inverted ? [inf(xreplace(gx, [[x, func]]), xreplace(tau, [[x, func]]), true)] : [inf(tau, gx)];
    if (!factor.has(x) && !factor.has(y)) {
      // fac = A(x) + B(x)*exp(y/C): tau = exp(-Integral(A/C, x))/B (SymPy writes exp(..., x), which raises)
      const A = new Wild('A', { exclude: [y] });
      const B = new Wild('B', { exclude: [y] });
      const C = new Wild('C', { exclude: [x, y] });
      const r = matchPattern(fac, add(A, mul(B, exp(mul(y, pow(C, -1))))));
      const [a, b, c] = [A, B, C].map((w) => r?.get(w));
      if (!a || !b || !c) continue;
      const tau = mul(exp(mul(-1, integrate(mul(a, pow(c, -1)), x))), pow(b, -1));
      return result(tau, mul(a, tau));
    }
    const gamma = cancel(mul(d(factor, x), pow(d(factor, y), -1)));
    if (gamma.has(y)) continue;
    const tauint = cancel(mul(add(mul(gamma, facy), mul(-1, d(gamma, x)), mul(-1, facx)), pow(add(fac, gamma), -1)));
    if (tauint.has(y)) continue;
    const tau = exp(integrate(tauint, x));
    return result(tau, mul(-1, tau, gamma));
  }
  return [];
}

/** Infinitesimals from the unknown functions or non-integer powers of h. */
function abaco2UniqueUnknown(m: LieMatch): Inf[] {
  const { h, x, y, func } = m;
  const funcs: Expr[] = [];
  const walk = (e: Expr): void => {
    if (e instanceof Pow && e.base.has(x) && e.base.has(y) && !(e.exp instanceof Rational && e.exp.isInteger)) funcs.push(e);
    else if (e instanceof UndefFn && e.has(x) && e.has(y)) funcs.push(e);
    e.args.forEach(walk);
  };
  walk(h);
  const unique = [...new Map(funcs.map((f) => [f.key, f])).values()];
  for (const f of unique) {
    const frac = cancel(mul(d(f, y), pow(d(f, x), -1)));
    const sep = sepDict(frac, x, y);
    // [xi, eta, expand before simplify] in SymPy's order: xi = X(x), eta = Y(y) when frac = R(y)/X(x) separates,
    // else eta/xi = -1/frac
    let tries: [Expr, Expr, boolean][];
    if (sep && !isZero(getOrThrow(sep, 'coeff'))) {
      const xitry1 = getOrThrow(sep, x);
      const etatry1 = mul(-1, pow(mul(getOrThrow(sep, y), getOrThrow(sep, 'coeff')), -1));
      tries = [[xitry1, etatry1, false], [pow(etatry1, -1), pow(xitry1, -1), true]];
    } else tries = [[S.One, mul(-1, pow(frac, -1)), false], [mul(-1, frac), S.One, true]];
    for (const [xi, eta, ex] of tries) {
      const pde = determiningPde(xi, eta, h, x, y);
      if (isZero(simplify(ex ? expand(pde) : pde))) return [inf(xreplace(xi, [[y, func]]), xreplace(eta, [[y, func]]))];
    }
  }
  return [];
}

/**
 * SymPy lie_heuristic_abaco2_unique_general (xi = f(x), eta = g(y) by the
 * conditions of Cheb-Terrab and Roche): SymPy's implementation tests
 * `x not in etaval`, which raises a TypeError whenever the conditions hold,
 * and gives no infinitesimals otherwise; it gives none here.
 */
function abaco2UniqueGeneral(): Inf[] {
  return [];
}

/** xi = c0*x + c1*y + c2, eta = c3*x + c4*y + c5, the coefficients from the grouped terms of the PDE. */
function linear(m: LieMatch): Inf[] {
  const { h, hx, hy, x, y, func } = m;
  const [C0, C1, C2, C3, C4, C5] = [new Dummy('c0'), new Dummy('c1'), new Dummy('c2'), new Dummy('c3'), new Dummy('c4'), new Dummy('c5')];
  const cs = [C0, C1, C2, C3, C4, C5];
  const pde0 = add(C3, mul(add(C4, mul(-1, C0)), h), mul(-1, add(mul(C0, x), mul(C1, y), C2), hx), mul(-1, add(mul(C3, x), mul(C4, y), C5), hy), mul(-1, C1, pow(h, 2)));
  const [num] = asNumerDenom(pde0);
  const pde = powsimp(expand(num));
  const coeffs = new Map<string, [Expr, Expr]>();
  // SymPy takes the coefficient of a term that is not a product to be 1 (C3 = 0 becomes 1 = 0): its own factors
  // free of x and y are its coefficient here
  for (const term of pde instanceof Add ? pde.args : [pde]) {
    const rem = mul(...(term instanceof Mul ? term.args : [term]).filter((a) => !a.has(x) && !a.has(y)));
    // the monomial with expanded exponents, so that x**(n*(m + 1)) and x**(m*n + n) are the same
    const xypart = mapBottomUp(mul(term, pow(rem, -1)), (u) => (u instanceof Pow ? pow(u.base, expand(u.exp)) : u));
    const old = coeffs.get(xypart.key);
    coeffs.set(xypart.key, [xypart, old ? add(old[1], rem) : rem]);
  }
  const sol = nontrivialSolution([...coeffs.values()].map(([, c]) => c), cs);
  if (!sol) return [];
  const xival = xreplace(add(mul(C0, x), mul(C1, func), C2), sol);
  const etaval = xreplace(add(mul(C3, x), mul(C4, func), C5), sol);
  return [inf(xival, etaval)];
}

const HEURISTICS: Record<LieHeuristic, (m: LieMatch, comp: boolean) => Inf[]> = {
  abaco1_simple: abaco1Simple,
  abaco1_product: abaco1Product,
  abaco2_similar: abaco2Similar,
  abaco2_unique_unknown: abaco2UniqueUnknown,
  abaco2_unique_general: abaco2UniqueGeneral,
  linear,
  function_sum: functionSum,
  bivariate,
  chi,
};

// ---------------------------------------------------------------------------
// infinitesimals and checkinfsol
// ---------------------------------------------------------------------------

/** The first-order ODE as y' = h(x, y): [h, y] (SymPy infinitesimals and checkinfsol). */
function odeRhs(eqIn: ExprLike, func: UndefFn): [Expr, Dummy] {
  const eq = sympify(eqIn);
  const x = cast(first(func.args), Sym, 'independent variable');
  const df = new Derivative([func, x, S.One]);
  const ex = expand(eq);
  const terms = ex instanceof Add ? ex.args : [ex];
  const withDf = terms.filter((t) => t.has(df));
  const coeff = add(...withDf.map((t) => mul(t, pow(df, -1))));
  let h: Expr;
  if (withDf.length && !coeff.has(df)) h = simplify(mul(-1, add(...terms.filter((t) => !t.has(df))), pow(coeff, -1)));
  else {
    const sols = solve(eq, df);
    if (!sols.length) throw new NotImplementedError('Infinitesimals for the first order ODE could not be found');
    h = first(sols);
  }
  const y = new Dummy('y');
  return [xreplace(h, [[func, y]]), y];
}

function lieMatch(h: Expr, y: Dummy, func: UndefFn): LieMatch {
  const x = cast(first(func.args), Sym, 'independent variable');
  const u = new Dummy('u');
  const hinv = xreplace(xreplace(pow(h, -1), [[x, u], [y, x]]), [[u, y]]);
  return { h, hx: d(h, x), hy: d(h, y), hinv, x, y, func };
}

/** The ODE's function f(x): the one differentiated in the equation. */
function odeFunction(eq: Expr): UndefFn {
  const found: UndefFn[] = [];
  const walk = (e: Expr): void => {
    if (e instanceof Derivative && e.expr instanceof UndefFn) found.push(e.expr);
    e.args.forEach(walk);
  };
  walk(eq);
  if (!found.length) throw new TypeError('infinitesimals: the equation has no derivative of an unknown function');
  return first(found);
}

/** Order of the derivatives of func in e. */
function orderIn(e: Expr, func: UndefFn): number {
  let n = 0;
  const walk = (t: Expr): void => {
    if (t instanceof Derivative && t.expr.key === func.key) n = Math.max(n, t.variableCount.reduce((s, [, k]) => s + k, 0));
    t.args.forEach(walk);
  };
  walk(e);
  return n;
}

function prepare(eqIn: ExprLike, funcIn?: Expr): [Expr, UndefFn, Sym] {
  const e0 = sympify(eqIn);
  const eq = e0 instanceof Rel && e0.op === 'Eq' ? add(e0.lhs, mul(-1, e0.rhs)) : e0;
  const func = funcIn === undefined ? odeFunction(eq) : cast(funcIn, UndefFn, 'unknown function');
  if (func.args.length !== 1) throw new RangeError("ODE's have only one independent variable");
  if (orderIn(eq, func) !== 1) throw new NotImplementedError("Infinitesimals for only first order ODE's have been implemented");
  return [eq, func, cast(first(func.args), Sym, 'independent variable')];
}

/** The infinitesimals of y' = h by one heuristic, or by the first that finds some ('default'), or by all ('all'). */
function infinitesimalsOf(m: LieMatch, hint: LieHeuristic | 'default' | 'all'): Inf[] {
  if (hint === 'all') {
    const out: Inf[] = [];
    for (const name of LIE_HEURISTICS) for (const i of HEURISTICS[name](m, true)) if (!out.some((o) => sameInf(o, i))) out.push(i);
    if (!out.length) throw new NotImplementedError('Infinitesimals could not be found for the given ODE');
    return out;
  }
  if (hint === 'default') {
    for (const name of LIE_HEURISTICS) {
      const r = HEURISTICS[name](m, false);
      if (r.length) return r;
    }
    throw new NotImplementedError('Infinitesimals could not be found for the given ODE');
  }
  const r = HEURISTICS[hint](m, true);
  if (!r.length) throw new RangeError('Infinitesimals could not be found using the given heuristic');
  return r;
}

/**
 * SymPy infinitesimals(eq, func, order, hint): the infinitesimals
 * {xi(x, f(x)): ..., eta(x, f(x)): ...} of the Lie point symmetries of a
 * first-order ODE, found by the heuristics (hint: one of LIE_HEURISTICS,
 * 'default' for the first heuristic that succeeds, or 'all').
 */
export function infinitesimals(eq: ExprLike, opts: { func?: Expr; hint?: string } = {}): Map<Expr, Expr>[] {
  const [e, func, x] = prepare(eq, opts.func);
  const hint = opts.hint ?? 'default';
  if (hint !== 'default' && hint !== 'all' && !LIE_HEURISTICS.some((h) => h === hint)) throw new RangeError(`Heuristic not recognized: ${hint}`);
  const [h, y] = odeRhs(e, func);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the hint was checked against LIE_HEURISTICS above
  return infinitesimalsOf(lieMatch(h, y, func), hint as LieHeuristic).map((i) => infMap(i, x, func));
}

/**
 * SymPy checkinfsol(eq, infinitesimals, func, order): for each pair of
 * infinitesimals, [true, 0] when it satisfies the determining PDE, otherwise
 * [false, the PDE's residual].
 */
export function checkinfsol(eq: ExprLike, infs: readonly ReadonlyMap<Expr, Expr>[], opts: { func?: Expr } = {}): [boolean, Expr][] {
  const [e, func, x] = prepare(eq, opts.func);
  const [h, y] = odeRhs(e, func);
  const xiKey = new UndefFn('xi', [x, func]).key;
  const etaKey = new UndefFn('eta', [x, func]).key;
  return infs.map((i) => {
    const get = (k: string): Expr => xreplace(cast([...i].find(([kk]) => kk.key === k)?.[1], Expr, 'infinitesimal'), [[func, y]]);
    const residual = simplify(doit(determiningPde(get(xiKey), get(etaKey), h, x, y)));
    return isZero(residual) ? [true, S.Zero] : [false, xreplace(residual, [[y, func]])];
  });
}

/** eta_x + (eta_y - xi_x)*h - xi_y*h**2 - xi*h_x - eta*h_y. */
function determiningPde(xi: Expr, eta: Expr, h: Expr, x: Sym, y: Sym): Expr {
  return add(d(eta, x), mul(add(d(eta, y), mul(-1, d(xi, x))), h), mul(-1, d(xi, y), pow(h, 2)), mul(-1, xi, d(h, x)), mul(-1, eta, d(h, y)));
}

// ---------------------------------------------------------------------------
// canonical coordinates: b*F_x + c*F_y = e (SymPy pdsolve, first-order linear hints)
// ---------------------------------------------------------------------------

/** Solves one first-order ODE with a hint (dsolve, given by the caller to avoid an import cycle). */
export type OdeSolver = (eq: Expr, fx: UndefFn) => Expr[];

const F = (arg: Expr): Expr => new UndefFn('F', [arg]);

/**
 * The general solution F(x, y) of b*F_x + c*F_y = e (b, c not both zero),
 * with an arbitrary function F(...) (SymPy pde_1st_linear_constant_coeff[_homogeneous]
 * and pde_1st_linear_variable_coeff without the F term).
 */
function pdsolveLinear(b: Expr, c: Expr, e: Expr, x: Sym, y: Sym, dsolveFn: OdeSolver): Expr {
  const isConst = (v: Expr): boolean => !v.has(x) && !v.has(y);
  if (isConst(b) && isConst(c)) {
    // F(c*x - b*y) + e*(b*x + c*y)/(b**2 + c**2)
    const particular = isZero(e) ? S.Zero : mul(e, add(mul(b, x), mul(c, y)), pow(add(pow(b, 2), pow(c, 2)), -1));
    return simplify(add(F(add(mul(c, x), mul(-1, b, y))), particular));
  }
  if (isZero(b)) return add(F(x), integrate(mul(e, pow(c, -1)), y));
  if (isZero(c)) return add(F(y), integrate(mul(e, pow(b, -1)), x));
  // the characteristics dy/dx = c/b
  const d = new UndefFn('d', [x]);
  const hc = xreplace(mul(c, pow(b, -1)), [[y, d]]);
  const sol = cast(first(dsolveFn(add(new Derivative([d, x, S.One]), mul(-1, hc)), d)), Rel, 'characteristic');
  // the constant of the characteristics (SymPy raises NotImplementedError unless there is one)
  const c0 = first([...freeSymbols(sol)].filter((c) => !hc.has(c) && c.key !== x.key && c.key !== y.key));
  const etat = xreplace(first(solve(add(sol.lhs, mul(-1, sol.rhs)), c0)), [[d, y]]);
  const eta = new Dummy('eta');
  const ysub = first(solve(add(eta, mul(-1, etat)), y));
  // b*f'(x) = e along a characteristic (SymPy dsolve(..., hint='1st_linear')): f = F(eta) + Integral(e/b, x)
  const fin = add(F(etat), integrate(xreplace(mul(e, pow(b, -1)), [[y, ysub]]), x));
  return simplify(xreplace(fin, [[eta, etat]]));
}

/** SymPy _lie_group_remove: drop the arbitrary functions of pdsolve's solution. */
export function lieGroupRemove(coords: Expr): Expr {
  if (coords instanceof UndefFn) return first(coords.args);
  if (coords instanceof Add) {
    const fs: Expr[] = [];
    const walk = (e: Expr): void => {
      if (e instanceof UndefFn) fs.push(e);
      else e.args.forEach(walk);
    };
    walk(coords);
    return xreplace(coords, fs.map((f): [Expr, Expr] => [f, S.Zero]));
  }
  if (coords instanceof Pow) return pow(lieGroupRemove(coords.base), lieGroupRemove(coords.exp));
  if (coords instanceof Mul) return mul(...coords.args.map(lieGroupRemove));
  return coords;
}

/** Solve [r - rcoord, s - scoord] for x and y: the first solution, or undefined. */
function solveCoords(eqs: [Expr, Expr], x: Sym, y: Sym): [Expr, Expr] {
  const orders: [Expr, Expr][] = [eqs, [eqs[1], eqs[0]]];
  const vars: [Sym, Sym][] = [[y, x], [x, y]];
  for (const [e1, e2] of orders) {
    for (const [v1, v2] of vars) {
      try {
        for (const a of solve(e1, v1)) {
          for (const b of solve(xreplace(e2, [[v1, a]]), v2)) {
            const vals = new Map([[v1.key, xreplace(a, [[v2, b]])], [v2.key, b]]);
            return [getOrThrow(vals, x.key), getOrThrow(vals, y.key)];
          }
        }
      } catch {
        // not solved for this unknown: the next one
      }
    }
  }
  throw new NotImplementedError('lie_group: the canonical coordinates are not inverted');
}

/** SymPy _ode_lie_group_try_heuristic: the solutions from the infinitesimals, or undefined. */
function tryInfinitesimals(infs: readonly Inf[], m: LieMatch, dsolveFn: OdeSolver): Expr[] {
  const { h, y, func } = m;
  const tempsol: Expr[] = [];
  for (const i of infs) {
    const xiinf = xreplace(i.xi, [[func, y]]);
    const etainf = xreplace(i.eta, [[func, y]]);
    // the trivial symmetry along the solutions gives no coordinates
    if ((isZero(xiinf) && isZero(etainf)) || simplify(mul(etainf, pow(xiinf, -1))).key === h.key) continue;
    let r: { explicit: Expr[] } | { implicit: Expr };
    try {
      r = solveByCoordinates(xiinf, etainf, m, dsolveFn);
    } catch {
      // SymPy: NotImplementedError, the next infinitesimals
      continue;
    }
    if ('implicit' in r) tempsol.push(r.implicit);
    else return r.explicit;
  }
  return tempsol.map((t) => Eq(xreplace(t, [[y, func]]), S.Zero));
}

/**
 * The solutions from the canonical coordinates r, s of xi, eta: explicit, or
 * the implicit equation when it cannot be solved for f(x).
 */
function solveByCoordinates(xiinf: Expr, etainf: Expr, m: LieMatch, dsolveFn: OdeSolver): { explicit: Expr[] } | { implicit: Expr } {
  const { h, x, y, func } = m;
  const C1 = new Sym('C1');
  const rcoord = lieGroupRemove(pdsolveLinear(xiinf, etainf, S.Zero, x, y, dsolveFn));
  const scoord = lieGroupRemove(pdsolveLinear(xiinf, etainf, S.One, x, y, dsolveFn));
  const r = new Dummy('r');
  const s = new Dummy('s');
  const [xsub, ysub] = solveCoords([add(r, mul(-1, rcoord)), add(s, mul(-1, scoord))], x, y);
  const num = simplify(add(d(scoord, x), mul(d(scoord, y), h)));
  // s is constant along the solutions (r is not: the symmetry is not the trivial one)
  if (isZero(num)) return { explicit: solve(add(scoord, mul(-1, C1)), y).map((v) => Eq(func, v)) };
  const denom = simplify(add(d(rcoord, x), mul(d(rcoord, y), h)));
  const diffeq = simplify(xreplace(mul(num, pow(denom, -1)), [[x, xsub], [y, ysub]]));
  // separable in r and s (an invariant error, caught by the caller, when simplification does not show it)
  const sep = defined(sepDict(diffeq, r, s), 'separable equation in the canonical coordinates');
  const deq0 = add(integrate(pow(getOrThrow(sep, s), -1), s), C1, mul(-1, integrate(mul(getOrThrow(sep, 'coeff'), getOrThrow(sep, r)), r)));
  const deq = subs(subs(deq0, [[r, rcoord]]), [[s, scoord]]);
  // an integral whose limit depends on y: the solution stays implicit (SymPy's solve treats the integral as
  // independent of y and gives a wrong explicit solution)
  if (some(deq, (u) => u instanceof Integral && u.args.slice(2).some((l) => l.has(y)))) return { implicit: deq };
  try {
    return { explicit: solve(deq, y).map((v) => Eq(func, v)) };
  } catch {
    return { implicit: deq };
  }
}

/**
 * SymPy LieGroup._get_general_solution and _ode_lie_group: the solutions of
 * the first-order ODE eq for f(x) by the Lie group method, with user-given
 * infinitesimals xi, eta (tried alone, like SymPy) or those of the heuristics.
 */
export function odeLieGroup(eq: Expr, func: UndefFn, dsolveFn: OdeSolver, user?: { xi: ExprLike; eta: ExprLike }): Expr[] | undefined {
  const x = cast(first(func.args), Sym, 'independent variable');
  const df = new Derivative([func, x, S.One]);
  let hs: Expr[];
  const ex = expand(eq);
  const terms = ex instanceof Add ? ex.args : [ex];
  const coeff = add(...terms.filter((t) => t.has(df)).map((t) => mul(t, pow(df, -1))));
  if (!isZero(coeff) && !coeff.has(df)) hs = [simplify(mul(-1, add(...terms.filter((t) => !t.has(df))), pow(coeff, -1)))];
  else {
    try {
      hs = solve(eq, df);
    } catch {
      hs = [];
    }
  }
  const y = new Dummy('y');
  const out: Expr[] = [];
  for (const h0 of hs) {
    const m = lieMatch(xreplace(h0, [[func, y]]), y, func);
    const sols = solveWithHeuristics(m, dsolveFn, user);
    if (sols) out.push(...sols);
  }
  return out.length ? out : undefined;
}

function solveWithHeuristics(m: LieMatch, dsolveFn: OdeSolver, user?: { xi: ExprLike; eta: ExprLike }): Expr[] | undefined {
  if (user) return tryInfinitesimals([inf(sympify(user.xi), sympify(user.eta))], m, dsolveFn);
  for (const name of LIE_HEURISTICS) {
    const infs = HEURISTICS[name](m, true);
    if (!infs.length) continue;
    const sol = tryInfinitesimals(infs, m, dsolveFn);
    if (sol.length) return sol;
  }
  return undefined;
}

