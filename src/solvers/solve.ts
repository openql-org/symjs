// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Equation solving (SymPy-compatible results): single equations,
 * linear and polynomial systems, undetermined coefficients and nsolve.
 */

import { isNegative, isNonNegative, isPositive, isReal } from '../core/assumptions';
import { Add, Constant, Dummy, Expr, ExprLike, Fn, Mul, Pow, Rational, Rel, S, Special, Sym, impl } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace, xreplace as xreplaceS } from '../core/traverse';
import { diff } from '../calculus/diff';
import { acos, asin, atan, log } from '../functions/elementary';
import { Matrix } from '../matrices/matrix';
import { rref } from '../matrices/linalg';
import { polyCoefficients, roots } from '../polys/poly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { radsimp } from '../simplify/radsimp';
import { simplify } from '../simplify/simplify';

const isZeroE = (e: Expr): boolean => {
  if (e instanceof Rational) return e.isZero;
  const s = simplify(e);
  return s instanceof Rational && s.isZero;
};

/** lhs - rhs for an equation given as Eq(lhs, rhs) or an expression (= 0). */
export function asEquation(e: ExprLike): Expr {
  const x = sympify(e);
  if (x instanceof Rel && x.op === 'Eq') return add(x.lhs, mul(-1, x.rhs));
  return x;
}

const sortExprs = (xs: Expr[]): Expr[] =>
  [...new Map(xs.map((x) => [x.key, x])).values()].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

/** Denominators of an expression (factors with negative exponents). */
function denominators(e: Expr): Expr[] {
  const out: Expr[] = [];
  const go = (x: Expr) => {
    if (x instanceof Pow && x.exp instanceof Rational && x.exp.isNegative) out.push(x.base);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

/** Does the candidate solution satisfy the assumptions of x and keep denominators nonzero? */
function checkSolution(f: Expr, x: Sym, v: Expr): boolean {
  const a = x.assumptions;
  if (a.positive && isPositive(v) === false) return false;
  if (a.positive && isNonNegative(v) === false) return false;
  if (a.nonnegative && isNegative(v) === true) return false;
  if (a.real && isReal(v) === false) return false;
  if (a.integer && v instanceof Rational && !v.isInteger) return false;
  for (const d of denominators(f)) {
    const dv = xreplace(d, [[x, v]]);
    if (isZeroE(dv)) return false;
  }
  // the original expression must not be undefined there
  const fv = xreplace(f, [[x, v]]);
  if (fv instanceof Special) return false;
  return true;
}

/** Inverse images of y under a function application f(u) (principal branches like SymPy). */
function invertFn(f: Fn | Pow, y: Expr): [Expr, Expr[]] | undefined {
  if (f instanceof Pow) {
    const [b, n] = f.args;
    if (b instanceof Constant && b.name === 'E') return [n, [log(y)]];
    if (!(n instanceof Rational)) return undefined;
    if (n.isInteger) return undefined; // handled as a polynomial
    return [b, [pow(y, Rational.of(n.q, n.p))]];
  }
  const u = f.args[0]!;
  switch (f.name) {
    case 'log':
      return [u, [exp(y)]];
    case 'sin':
      return [u, [asin(y), add(S.Pi, mul(-1, asin(y)))]];
    case 'cos':
      return [u, [acos(y), add(mul(2, S.Pi), mul(-1, acos(y)))]];
    case 'tan':
      return [u, [atan(y)]];
    default:
      return undefined;
  }
}

/** Solutions of f = 0 for x (without the final check). */
function solveRaw(f0: Expr, x: Sym, depth = 0): Expr[] {
  if (depth > 12) throw new Error('solve: recursion too deep');
  const f = f0;
  if (!f.has(x)) return [];
  // rational function: solve the numerator
  const [num] = fraction(together(f));
  const n = expandMul(num);
  const pc = polyCoefficients(n, x);
  if (pc) return roots(n, x);
  // products: union of the factors
  if (num instanceof Mul) {
    const sols: Expr[] = [];
    for (const g of num.args) if (g.has(x)) sols.push(...solveRaw(g, x, depth + 1));
    return sols;
  }
  if (num instanceof Pow && num.exp instanceof Rational && num.exp.isPositive) return solveRaw(num.base, x, depth + 1);
  // isolate a single function application: a*F(u) + b = 0
  const terms = num instanceof Add ? num.args : [num];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length === 1) {
    const b = add(...terms.filter((t) => !t.has(x)));
    const t = dep[0]!;
    const factors = t instanceof Mul ? t.args : [t];
    const fdep = factors.filter((g) => g.has(x));
    if (fdep.length === 1) {
      const a = mul(...factors.filter((g) => !g.has(x)));
      const F = fdep[0]!;
      const y = mul(-1, b, pow(a, -1));
      if (F instanceof Fn || F instanceof Pow) {
        const inv = invertFn(F, y);
        if (inv) {
          const [u, ys] = inv;
          return ys.flatMap((yy) => solveRaw(add(u, mul(-1, yy)), x, depth + 1));
        }
      }
    }
  }
  throw new Error(`solve: cannot solve ${f.toString()} for ${x.name}`);
}

/**
 * Solutions of the equation e = 0 (or Eq(lhs, rhs)) for x, sorted like
 * SymPy. Solutions violating the assumptions on x or making a denominator
 * vanish are removed unless check is false.
 */
export function solve(e: ExprLike, x?: Sym | Expr, opts: { check?: boolean } = {}): Expr[] {
  if (x !== undefined && !(x instanceof Sym)) {
    // solve for an expression such as f(x), Derivative(f(x), x) or x + 2: treat it as a symbol
    const t = new Dummy('t');
    const target = x;
    const g = replaceTarget(asEquation(e), target, t);
    if (!g.has(t)) return [];
    return solve(g, t, opts).map((r) => xreplaceS(r, [[t, target]]));
  }
  const f = asEquation(e);
  const syms = [...freeSymbols(f)];
  const v = x ?? (syms.length === 1 ? syms[0] : undefined);
  if (v === undefined) {
    if (syms.length === 0) return [];
    throw new Error('solve: specify the symbol to solve for');
  }
  const raw0 = solveRaw(f, v);
  // SymPy: high-order root lists (more than two roots) are not simplified
  const raw = raw0.length > 2 ? raw0 : raw0.map((r) => simplifySolution(r));
  const checked = opts.check === false ? raw : raw.filter((r) => checkSolution(f, v, r));
  return sortExprs(checked);
}

/** Replace free occurrences of target (not inside derivatives); a sum target may match part of a sum. */
function replaceTarget(e: Expr, target: Expr, t: Expr): Expr {
  const go = (x: Expr): Expr => {
    if (x.key === target.key) return t;
    if (x.kind === 'Derivative') return x;
    if (target instanceof Add && x instanceof Add && target.args.every((a) => x.args.some((b) => b.key === a.key))) {
      const rest = x.args.filter((b) => !target.args.some((a) => a.key === b.key));
      return add(t, ...rest.map(go));
    }
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    return args.every((a, i) => a === x.args[i]) ? x : xreplaceS(x, x.args.map((a, i) => [a, args[i]!] as [Expr, Expr]).filter(([a, b]) => a !== b));
  };
  return go(e);
}

function simplifySolution(r: Expr): Expr {
  if (r.freeSymbols().size === 0 && !(r instanceof Rational)) {
    const s = simplify(r);
    return s;
  }
  return r;
}

// ---------------------------------------------------------------------------
// systems
// ---------------------------------------------------------------------------

/** Coefficient matrix and right-hand side of a linear system; undefined if nonlinear. */
export function linearEqToMatrix(eqs: readonly ExprLike[], syms: readonly Sym[]): [Matrix, Matrix] | undefined {
  const rows: Expr[][] = [];
  const rhs: Expr[] = [];
  for (const e0 of eqs) {
    const e = expandMul(asEquation(e0));
    const row: Expr[] = [];
    let rest = e;
    for (const s of syms) {
      const pc = polyCoefficients(e, s);
      if (!pc || [...pc.keys()].some((k) => k > 1)) return undefined;
      const c = pc.get(1) ?? S.Zero;
      if (syms.some((t) => t !== s && c.has(t))) return undefined;
      row.push(c);
      rest = add(rest, mul(-1, c, s));
    }
    rest = expandMul(rest);
    if (syms.some((s) => rest.has(s))) return undefined;
    rows.push(row);
    rhs.push(mul(-1, rest));
  }
  return [Matrix.of(rows), Matrix.col(...rhs)];
}

/**
 * Solve a linear system. Returns the solution tuple (free unknowns appear as
 * themselves), or undefined when inconsistent.
 */
export function linsolve(eqs: readonly ExprLike[], syms: readonly Sym[]): Expr[] | undefined {
  const lin = linearEqToMatrix(eqs, syms);
  if (!lin) throw new Error('linsolve: nonlinear system');
  const [A, b] = lin;
  return solveAugmented(A.hstack(b), syms);
}

/** Solve [A | b] for syms. */
export function solveAugmented(aug: Matrix, syms: readonly Sym[]): Expr[] | undefined {
  const n = syms.length;
  const [R, pivots] = rref(aug);
  if (pivots.includes(n)) return undefined; // inconsistent
  const sol: Expr[] = syms.map((s) => s);
  pivots.forEach((pc, i) => {
    let v: Expr = R.get(i, n);
    for (let j = 0; j < n; j++) {
      if (j === pc || pivots.includes(j)) continue;
      v = add(v, mul(-1, R.get(i, j), syms[j]!));
    }
    sol[pc] = cancel(v);
  });
  return sol;
}

/**
 * Solve a polynomial system by successive elimination: equations that are
 * univariate (after substitution) are solved and their solutions substituted.
 * Returns the list of solution tuples.
 */
export function nonlinsolve(eqs: readonly ExprLike[], syms: readonly Sym[]): Expr[][] {
  const lin = linearEqToMatrix(eqs, syms);
  if (lin) {
    const s = solveAugmented(lin[0].hstack(lin[1]), syms);
    return s ? [s] : [];
  }
  const results: Expr[][] = [];
  const go = (system: Expr[], assigned: Map<string, Expr>) => {
    const pending = system.map((e) => expandMul(e)).filter((e) => !isZeroE(e));
    const unknowns = syms.filter((s) => !assigned.has(s.key));
    if (pending.length === 0) {
      // remaining unknowns are free parameters
      results.push(syms.map((s) => assigned.get(s.key) ?? s));
      return;
    }
    if (unknowns.length === 0) return;
    if (pending.some((e) => freeSymbols(e).size === 0 || !unknowns.some((u) => e.has(u)))) return;
    // prefer an equation that is linear in some unknown with a nonzero constant coefficient
    for (const e of pending) {
      for (const u of unknowns) {
        const pc = polyCoefficients(numerOf(e), u);
        if (pc && Math.max(...pc.keys()) === 1) {
          const c1 = pc.get(1)!;
          const c0 = pc.get(0) ?? S.Zero;
          const val = cancel(mul(-1, c0, pow(c1, -1)));
          if (val.has(u)) continue;
          const next = new Map(assigned);
          next.set(u.key, val);
          for (const [k, w] of next) next.set(k, cancel(xreplace(w, [[u, val]])));
          go(
            pending.filter((p) => p !== e).map((p) => xreplace(p, [[u, val]])),
            next,
          );
          return;
        }
      }
    }
    // a univariate equation
    for (const e of pending) {
      const vars = unknowns.filter((u) => e.has(u));
      if (vars.length !== 1) continue;
      const u = vars[0]!;
      let sols: Expr[];
      try {
        sols = solve(e, u, { check: false }).filter((v) =>
          denominators(e).every((dd) => !isZeroE(xreplace(dd, [[u, v]]))),
        );
      } catch {
        continue;
      }
      for (const s of sols) {
        const next = new Map(assigned);
        next.set(u.key, s);
        for (const [k, w] of next) next.set(k, simplifyBack(xreplace(w, [[u, s]])));
        go(
          pending.filter((p) => p !== e).map((p) => xreplace(p, [[u, s]])),
          next,
        );
      }
      return;
    }
    throw new Error('nonlinsolve: unsupported system');
  };
  go(eqs.map(asEquation), new Map());
  return results;
}

const numerOf = (e: Expr): Expr => expandMul(fraction(together(e))[0]);
const simplifyBack = (e: Expr): Expr => {
  const c = cancel(e);
  if (c.freeSymbols().size > 0) return c;
  const r = expandMul(radsimp(c));
  return r.freeSymbols().size === 0 ? simplify(r) : r;
};

/** SymPy solve_linear: (symbol, value) for an equation linear in one symbol, else (numer, denom). */
export function solveLinear(e: ExprLike, opts: { symbols?: Sym[]; exclude?: Sym[] } = {}): [Expr, Expr] {
  const f = asEquation(e);
  const [n, d] = fraction(together(f));
  const num = expandMul(n);
  if (num instanceof Rational && num.isZero) return [S.Zero, S.One];
  const cands = [...freeSymbols(num)]
    .filter((s) => !opts.symbols || opts.symbols.some((t) => t.key === s.key))
    .filter((s) => !opts.exclude || !opts.exclude.some((t) => t.key === s.key))
    .sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  for (const s of cands) {
    const pc = polyCoefficients(num, s);
    if (!pc || Math.max(...pc.keys()) !== 1) continue;
    const c1 = pc.get(1)!;
    if (c1.has(s)) continue;
    const val = cancel(mul(-1, pc.get(0) ?? S.Zero, pow(c1, -1)));
    if (denominators(f).some((dd) => isZeroE(xreplace(dd, [[s, val]])))) continue;
    return [s, val];
  }
  return [num, expandMul(d)];
}

/** Solve for the undetermined coefficients so that eq vanishes identically in the given symbols. */
export function solveUndeterminedCoeffs(e: ExprLike, coeffs: readonly Sym[], syms: readonly Sym[]): Expr[][] {
  const f = expandMul(numerOf(asEquation(e)));
  // collect coefficients of each monomial in syms
  const eqs: Expr[] = [];
  const collect = (expr: Expr, vars: readonly Sym[]) => {
    if (vars.length === 0) {
      eqs.push(expr);
      return;
    }
    const pc = polyCoefficients(expr, vars[0]!);
    if (!pc) throw new Error('solve_undetermined_coeffs: not polynomial in the symbols');
    for (const c of pc.values()) collect(c, vars.slice(1));
  };
  collect(f, syms);
  return nonlinsolve(eqs, coeffs);
}

/** Numeric root of f near x0 by Newton's method (complex arithmetic). */
export function nsolve(e: ExprLike, x: Sym, x0: ExprLike): Expr {
  const f = asEquation(e);
  const df = diff(f, x);
  const z0 = sympify(x0).toComplex();
  let z = z0;
  for (let i = 0; i < 100; i++) {
    const fv = xreplace(f, [[x, cplx(z)]]).toComplex();
    const dv = xreplace(df, [[x, cplx(z)]]).toComplex();
    const den = dv.re * dv.re + dv.im * dv.im;
    if (den === 0) break;
    const step = { re: (fv.re * dv.re + fv.im * dv.im) / den, im: (fv.im * dv.re - fv.re * dv.im) / den };
    z = { re: z.re - step.re, im: z.im - step.im };
    if (Math.hypot(step.re, step.im) < 1e-15 * Math.max(1, Math.hypot(z.re, z.im))) break;
  }
  return impl.evalf(cplx(z));
}

const cplx = (z: { re: number; im: number }): Expr =>
  z.im === 0 ? sympify(z.re) : add(sympify(z.re), mul(sympify(z.im), S.I));

