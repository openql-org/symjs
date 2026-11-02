// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Equation solving (SymPy-compatible results): single equations,
 * linear and polynomial systems, undetermined coefficients and nsolve.
 */

import { isNegative, isNonNegative, isPositive, isReal } from '../core/assumptions';
import { Add, Constant, Dummy, Expr, ExprLike, Fn, Mul, Pow, Rational, Rel, S, Special, Sym, impl } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, some, xreplace, xreplace as xreplaceS } from '../core/traverse';
import { evalf } from '../numeric/evalf';
import { diff } from '../calculus/diff';
import { acos, asin, atan, log } from '../functions/elementary';
import { Matrix } from '../matrices/matrix';
import { rref } from '../matrices/linalg';
import { polyCoefficients, roots } from '../polys/poly';
import { Poly } from '../polys/sympoly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { radsimp } from '../simplify/radsimp';
import { simplify } from '../simplify/simplify';
import { asNumerDenom } from '../core/methods';

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
  // a numeric residual must vanish (SymPy checksol), e.g. sqrt(x) + 1 at x = 1
  if (freeSymbols(fv).size === 0 && !hasExtension(fv)) {
    try {
      const c = evalf(fv, 30).toComplex();
      if (Number.isFinite(c.re) && Number.isFinite(c.im) && Math.hypot(c.re, c.im) > 1e-12) return false;
    } catch {
      // not evaluable: keep the candidate
    }
  }
  return true;
}

const hasExtension = (e: Expr): boolean => e.kind === 'Extension' || e.args.some(hasExtension);

/** Inverse images of y under a function application f(u) (principal branches like SymPy). */
function invertFn(f: Fn | Pow, y: Expr): [Expr, Expr[]] | undefined {
  if (f instanceof Pow) {
    const [b, n] = f.args;
    if (b instanceof Constant && b.name === 'E') {
      // exp(-u) = y  ->  u = log(1/y), with 1/(-a - b) written as -1/(a + b) like SymPy
      if (couldExtractMinusSign(n)) {
        const iy = pow(y, -1);
        const inv = iy instanceof Pow && iy.base instanceof Add && couldExtractMinusSign(iy.base) ? mul(-1, pow(mul(-1, iy.base), -1)) : iy;
        return [mul(-1, n), [log(inv)]];
      }
      return [n, [log(y)]];
    }
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
  // a single exponential term or 1/x: isolate it before clearing denominators
  if (f instanceof Add) {
    const dep = f.args.filter((t) => t.has(x));
    if (dep.length === 1) {
      const t = dep[0]!;
      const fs = t instanceof Mul ? t.args : [t];
      const F = fs.filter((g) => g.has(x));
      if (F.length === 1 && F[0] instanceof Pow && F[0].base.key === x.key && F[0].exp instanceof Rational && F[0].exp.p === -1n && F[0].exp.q === 1n) {
        // a/x + b = 0  ->  x = 1/(-b/a)
        const a = mul(...fs.filter((g) => !g.has(x)));
        const y = mul(-1, add(...f.args.filter((u) => !u.has(x))), pow(a, -1));
        return isZeroE(y) ? [] : [pow(y, -1)];
      }
      if (F.length === 1 && F[0] instanceof Pow && F[0].base instanceof Constant && F[0].base.name === 'E') {
        const a = mul(...fs.filter((g) => !g.has(x)));
        const y = mul(-1, add(...f.args.filter((u) => !u.has(x))), pow(a, -1));
        const inv = invertFn(F[0], y)!;
        return inv[1].flatMap((yy) => solveRaw(add(inv[0], mul(-1, yy)), x, depth + 1));
      }
    }
  }
  // rational function: solve the numerator
  const [num] = fraction(together(f));
  const n = expandMul(num);
  const pc = polyCoefficients(n, x);
  if (pc) {
    const degree = Math.max(...pc.keys());
    const rational = [...pc.values()].every((c) => c instanceof Rational);
    if (noCubics && degree >= 3) {
      // SymPy cubics=False: CRootOf instead of the general formulas
      return rational ? uniqueKeys(Poly.from(n, [x]).allRoots()) : [];
    }
    let rs: Expr[];
    try {
      rs = roots(n, x);
    } catch (err) {
      if (!rational) throw err;
      rs = [];
    }
    if (rational && rs.length < degree) return uniqueKeys(Poly.from(n, [x]).allRoots());
    return rs;
  }
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
  const rad = singleRadical(num, x, depth);
  if (rad) return rad;
  const lw = lambertSolve(num, x);
  if (lw) return lw;
  // a*sin(u) + b*cos(u) = 0  ->  tan(u) = -b/a
  const sc = sinCosLinear(num, x);
  if (sc) return sc;
  throw new Error(`solve: cannot solve ${f.toString()} for ${x.name}`);
}

/**
 * One radical R = g**(p/q) in a*R + b = 0 (a, b free of radicals in x):
 * a**q*g**p = (-b)**q, a polynomial-type equation (SymPy unrad). Spurious
 * candidates are removed by the final check.
 */
function singleRadical(num: Expr, x: Sym, depth: number): Expr[] | undefined {
  const rads = new Map<string, Pow>();
  const find = (e: Expr) => {
    if (e instanceof Pow && e.exp instanceof Rational && !e.exp.isInteger && e.base.has(x)) rads.set(e.key, e);
    e.args.forEach(find);
  };
  find(num);
  if (rads.size !== 1) return undefined;
  const R = [...rads.values()][0]!;
  const terms = num instanceof Add ? num.args : [num];
  const as: Expr[] = [];
  const bs: Expr[] = [];
  for (const t of terms) {
    if (!t.has(R)) {
      bs.push(t);
      continue;
    }
    const c = mul(t, pow(R, -1));
    if (c.has(R) || some(c, (u) => u instanceof Pow && u.exp instanceof Rational && !u.exp.isInteger && u.base.has(x))) return undefined;
    as.push(c);
  }
  const a = add(...as);
  const b = add(...bs);
  const p = (R.exp as Rational).p;
  const q = (R.exp as Rational).q;
  if (p < 0n || q > 6n) return undefined;
  const eq = add(mul(pow(a, Rational.of(q)), pow(R.base, Rational.of(p))), mul(-1, pow(mul(-1, b), Rational.of(q))));
  return solveRaw(expandMul(eq), x, depth + 1);
}

function sinCosLinear(e: Expr, x: Sym): Expr[] | undefined {
  const terms = e instanceof Add ? e.args : [e];
  let a: Expr = S.Zero;
  let b: Expr = S.Zero;
  let u: Expr | undefined;
  for (const t of terms) {
    const fs = t instanceof Mul ? t.args : [t];
    const trig = fs.filter((g) => g instanceof Fn && (g.name === 'sin' || g.name === 'cos') && g.has(x)) as Fn[];
    if (trig.length !== 1) return undefined;
    const g = trig[0]!;
    if (u && u.key !== g.args[0]!.key) return undefined;
    u = g.args[0]!;
    const c = mul(...fs.filter((h) => h !== g));
    if (c.has(x)) return undefined;
    if (g.name === 'sin') a = add(a, c);
    else b = add(b, c);
  }
  if (!u || a instanceof Rational && a.isZero || b instanceof Rational && b.isZero) return undefined;
  return solveRaw(add(u, mul(-1, atan(mul(-1, b, pow(a, -1))))), x);
}

/**
 * Lambert W forms (a, b, c, d, e free of x):
 *   a*x + b + c*exp(d*x + e) = 0   ->  x = -W(c*d/a*exp(e - b*d/a))/d - b/a
 *   (a*x + b)*exp(d*x + e) + c = 0 ->  x = W(-c*d/a*exp(b*d/a - e))/d - b/a
 */
function lambertSolve(num: Expr, x: Sym): Expr[] | undefined {
  const terms = num instanceof Add ? num.args : [num];
  const isExp = (g: Expr): g is Pow => g instanceof Pow && g.base instanceof Constant && g.base.name === 'E';
  let u: Expr | undefined;
  const withExp: Expr[] = [];
  const without: Expr[] = [];
  for (const t of terms) {
    const factors = t instanceof Mul ? t.args : [t];
    const ex = factors.filter((g) => isExp(g) && g.has(x));
    if (ex.length > 1) return undefined;
    if (ex.length === 0) {
      without.push(t);
      continue;
    }
    const ue = (ex[0] as Pow).exp;
    if (u && u.key !== ue.key) return undefined;
    u = ue;
    withExp.push(mul(...factors.filter((g) => g !== ex[0])));
  }
  if (!u) return undefined;
  const P = polyCoefficients(add(...withExp), x);
  const Q = polyCoefficients(add(...without), x);
  const U = polyCoefficients(u, x);
  if (!P || !Q || !U) return undefined;
  const deg = (m: Map<number, Expr>) => Math.max(-1, ...[...m.entries()].filter(([, v]) => !(v instanceof Rational && v.isZero)).map(([k]) => k));
  if (deg(U) !== 1) return undefined;
  const d = U.get(1)!;
  const e = U.get(0) ?? S.Zero;
  const W = (arg: Expr, k?: number) => (k === undefined ? impl.lambertW!(arg) : impl.lambertW!(arg, k));
  const branches = (arg: Expr, sol: (k?: number) => Expr): Expr[] => {
    const out = [sol()];
    if (arg.freeSymbols().size === 0) {
      const v = arg.toComplex();
      if (Math.abs(v.im) < 1e-300 && v.re < 0 && v.re > -Math.exp(-1)) out.push(sol(-1));
    }
    return out;
  };
  if (deg(P) === 0 && deg(Q) === 1) {
    const c = P.get(0)!;
    const a = Q.get(1)!;
    const ba = mul(Q.get(0) ?? S.Zero, pow(a, -1));
    const arg = mul(c, d, pow(a, -1), exp(add(e, mul(-1, d, ba))));
    return branches(arg, (k) => add(mul(-1, W(arg, k), pow(d, -1)), mul(-1, ba)));
  }
  if (deg(P) === 1 && deg(Q) <= 0) {
    const a = P.get(1)!;
    const ba = mul(P.get(0) ?? S.Zero, pow(a, -1));
    const c = Q.get(0) ?? S.Zero;
    if (c instanceof Rational && c.isZero) return undefined;
    const arg = mul(-1, c, d, pow(a, -1), exp(add(mul(d, ba), mul(-1, e))));
    return branches(arg, (k) => add(mul(W(arg, k), pow(d, -1)), mul(-1, ba)));
  }
  return undefined;
}

/**
 * Solutions of the equation e = 0 (or Eq(lhs, rhs)) for x, sorted like
 * SymPy. Solutions violating the assumptions on x or making a denominator
 * vanish are removed unless check is false.
 */
let noCubics = false;
const uniqueKeys = (xs: Expr[]): Expr[] => [...new Map(xs.map((r) => [r.key, r])).values()];

export function solve(e: ExprLike, x?: Sym | Expr, opts: { check?: boolean; cubics?: boolean } = {}): Expr[] {
  if (opts.cubics === false && !noCubics) {
    noCubics = true;
    try {
      return solve(e, x, { ...opts, cubics: undefined });
    } finally {
      noCubics = false;
    }
  }
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
  const checked = opts.check === false || raw.some((r) => r.kind === 'Extension') ? raw : raw.filter((r) => checkSolution(f, v, r));
  // indexed roots (CRootOf) keep their order
  return raw.some((r) => r.kind === 'Extension') ? checked : sortExprs(checked);
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
  // port of SymPy solve_linear
  const eq = asEquation(e);
  const [n, d] = asNumerDenom(eq);
  if (isZeroE(n)) return [S.Zero, S.One];
  let symbols = [...freeSymbols(n)];
  if (opts.symbols) symbols = symbols.filter((s) => opts.symbols!.some((t) => t.key === s.key));
  if (opts.exclude) symbols = symbols.filter((s) => !opts.exclude!.some((t) => t.key === s.key));
  if (!symbols.length) return [S.Zero, S.One];
  symbols.sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  // denominators of eq that depend on the symbols (SymPy _simple_dens)
  const dens: Expr[] = [];
  const visit = (t: Expr) => {
    t.args.forEach(visit);
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && symbols.some((s) => t.base.has(s))) dens.push(t.base);
  };
  visit(eq);
  const symKeys = new Set(symbols.map((s) => s.key));
  let allZero = true;
  for (const xi of symbols) {
    const dn = diff(n, xi);
    if (isZeroE(dn)) continue;
    const free = [...freeSymbols(dn)];
    const ok = !free.length || free.some((s) => !isZeroE(diff(dn, s))) || (free.length === symKeys.size && free.every((s) => symKeys.has(s.key)));
    if (!ok) continue;
    allZero = false;
    if (dn.has(xi)) continue;
    const vi = mul(-1, pow(dn, -1), xreplace(n, [[xi, S.Zero]]));
    const bad = dens.some((di) => {
      const v = xreplace(di, [[xi, vi]]);
      return isZeroE(v) || isZeroE(cancel(v));
    });
    if (!bad) return [xi, expandMul(vi)];
  }
  if (allZero) return [S.Zero, S.One];
  if (n instanceof Sym) return [S.Zero, S.Zero];
  return [n, d];
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
export function nsolve(e: ExprLike, x: Sym, x0: ExprLike, opts: { prec?: number } = {}): Expr {
  const r = nsolveDouble(e, x, x0);
  const dps = opts.prec;
  if (dps === undefined || dps <= 15) return r;
  // refine with Newton steps in arbitrary precision (SymPy nsolve(..., prec=n))
  const f = asEquation(e);
  const df = diff(f, x);
  const wp = dps + 10;
  let z = impl.evalf(r, wp);
  let last = '';
  for (let i = 0; i < 60; i++) {
    const fv = impl.evalf(xreplace(f, [[x, z]]), wp);
    const dv = impl.evalf(xreplace(df, [[x, z]]), wp);
    z = impl.evalf(add(z, mul(-1, fv, pow(dv, -1))), wp);
    const cur = impl.evalf(z, dps).toString();
    if (cur === last) break;
    last = cur;
  }
  return impl.evalf(z, dps);
}

function nsolveDouble(e: ExprLike, x: Sym, x0: ExprLike): Expr {
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


/**
 * SymPy solvers._invert: reduce eq = 0 to lhs = rhs with lhs containing the
 * symbols in its simplest form. Returns [rhs, lhs].
 */
export function invertEquation(eqIn: ExprLike, symbols: readonly Sym[] = [], opts: { integerPower?: boolean } = {}): [Expr, Expr] {
  const eq = sympify(eqIn);
  const syms = symbols.length ? [...symbols] : [...freeSymbols(eq)];
  if (!syms.some((s) => eq.has(s))) return [eq, S.Zero];
  const dep = (e: Expr) => syms.some((s) => e.has(s));
  let lhs = eq;
  let rhs: Expr = S.Zero;
  for (let guard = 0; guard < 50; guard++) {
    const was = lhs;
    for (let g2 = 0; g2 < 50; g2++) {
      if (lhs instanceof Add) {
        const indep = add(...lhs.args.filter((a) => !dep(a)));
        if (indep instanceof Rational && indep.isZero) break;
        lhs = add(...lhs.args.filter(dep));
        rhs = add(rhs, mul(-1, indep));
      } else if (lhs instanceof Mul) {
        const indep = mul(...lhs.args.filter((a) => !dep(a)));
        if (indep instanceof Rational && indep.isOne) break;
        lhs = mul(...lhs.args.filter(dep));
        rhs = mul(rhs, pow(indep, -1));
      } else break;
    }
    if (lhs instanceof Fn && lhs.name === 'log' && lhs.args.length === 1) {
      rhs = exp(rhs);
      lhs = lhs.args[0]!;
    } else if (lhs instanceof Pow && lhs.base instanceof Constant && lhs.base.name === 'E') {
      rhs = log(rhs);
      lhs = lhs.exp;
    }
    if (!(rhs instanceof Rational && rhs.isZero) && lhs instanceof Pow && lhs.exp instanceof Rational && lhs.exp.isInteger && lhs.exp.isNegative) {
      lhs = pow(lhs, -1);
      rhs = pow(rhs, -1);
    }
    if (lhs instanceof Pow && !(lhs.base instanceof Constant)) {
      const intExp = lhs.exp instanceof Rational && lhs.exp.isInteger;
      const multi = syms.length > 1 && syms.filter((s) => (lhs as Pow).base.has(s)).length > 1;
      if ((intExp && opts.integerPower) || (!intExp && multi)) {
        rhs = pow(rhs, pow(lhs.exp, -1));
        lhs = lhs.base;
      }
    }
    if (lhs.key === was.key) break;
  }
  return [rhs, lhs];
}
