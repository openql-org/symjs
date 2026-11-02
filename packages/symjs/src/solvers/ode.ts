// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Ordinary differential equations (dsolve), SymPy-compatible forms:
 * first-order linear and separable equations, linear equations with
 * constant coefficients of any order (homogeneous solution with SymPy's
 * grouping) and particular solutions by undetermined coefficients.
 */

import { NotImplementedError } from '../core/errors';
import { dsolveSystem } from './odesystem';
import { SubsNode } from '../core/subsnode';
import { Add, Derivative, Dummy, Expr, ExprLike, Fn, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { add, couldExtractMinusSign, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { powsimp } from '../simplify/powsimp';
import { diff } from '../calculus/diff';
import { cos, im, re, sin } from '../functions/elementary';
import { integrate } from '../integrals/integrate';
import { polyCoefficients, roots } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { asEquation, linsolve, solve } from './solve';
import { dsolveRaw } from './dsolve';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;

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

/** Replace f and its derivatives by symbols y0, y1, ... */
function toSymbols(e: Expr, f: UndefFn, n: number): [Expr, Sym[]] {
  const ys = Array.from({ length: n + 1 }, (_, i) => new Sym(`_y${i}`));
  const go = (x: Expr): Expr => {
    if (x.key === f.key) return ys[0]!;
    if (x instanceof Derivative && x.expr.key === f.key) {
      const k = x.variableCount.reduce((s, [, m]) => s + m, 0);
      return ys[k]!;
    }
    if (x.args.length === 0) return x;
    return rebuildWith(x, go);
  };
  return [go(e), ys];
}

function rebuildWith(x: Expr, go: (e: Expr) => Expr): Expr {
  const args = x.args.map(go);
  if (args.every((a, i) => a === x.args[i])) return x;
  if (x instanceof Add) return add(...args);
  if (x instanceof Mul) return mul(...args);
  if (x instanceof Pow) return pow(args[0]!, args[1]!);
  if (x instanceof Fn) return xreplace(x, x.args.map((a, i) => [a, args[i]!] as const));
  return x;
}

const constants = (n: number, start = 1) => Array.from({ length: n }, (_, i) => new Sym(`C${start + i}`));

/** Homogeneous solution of sum_k a_k y^(k) = 0 with constant coefficients. */
function constantCoeffHomogeneous(coeffs: Expr[], x: Sym): [Expr, number] {
  const n = coeffs.length - 1;
  const r = new Sym('_r');
  const chareq = add(...coeffs.map((c, k) => mul(c, pow(r, k))));
  const rs = roots(chareq, r);
  // group roots with multiplicities
  const groups = new Map<string, { root: Expr; mult: number }>();
  for (const v of rs) {
    const g = groups.get(v.key);
    if (g) g.mult++;
    else groups.set(v.key, { root: v, mult: 1 });
  }
  const num = (e: Expr): number | undefined => {
    if (e.freeSymbols().size > 0) return undefined;
    try {
      return e.toComplex().re;
    } catch {
      return undefined;
    }
  };
  const reals: { root: Expr; mult: number }[] = [];
  const complexes: { a: Expr; b: Expr; mult: number }[] = [];
  for (const g of groups.values()) {
    const b = im(g.root);
    if (isZeroE(simplify(b)) || g.root.freeSymbols().size > 0) reals.push(g);
    else if ((num(simplify(b)) ?? 0) > 0) complexes.push({ a: re(g.root), b: simplify(b), mult: g.mult });
  }
  const absval = (e: Expr) => Math.abs(num(e) ?? 0);
  type Part = { key: number; tie: number; build: (cs: Sym[]) => Expr; count: number; root?: Expr };
  const parts: Part[] = [];
  for (const g of reals) {
    parts.push({
      key: absval(g.root),
      tie: num(g.root) ?? 0,
      count: g.mult,
      root: g.root,
      build: (cs) => {
        const poly = add(...cs.map((c, i) => mul(c, pow(x, i))));
        return isZeroE(g.root) ? poly : mul(poly, exp(mul(g.root, x)));
      },
    });
  }
  for (const c of complexes) {
    parts.push({
      key: Math.hypot(num(c.a) ?? 0, num(c.b) ?? 0),
      tie: (num(c.a) ?? 0) - 0.5,
      count: 2 * c.mult,
      build: (cs) => {
        const terms: Expr[] = [];
        for (let i = 0; i < c.mult; i++) {
          terms.push(mul(cs[2 * i]!, pow(x, i), sin(mul(c.b, x))), mul(cs[2 * i + 1]!, pow(x, i), cos(mul(c.b, x))));
        }
        const s = add(...terms);
        return isZeroE(c.a) ? s : mul(s, exp(mul(c.a, x)));
      },
    });
  }
  parts.sort((p, q) => p.key - q.key || p.tie - q.tie);
  // SymPy factors out the smallest exponential when all roots are real, simple and of one sign
  const simple = complexes.length === 0 && reals.every((g) => g.mult === 1) && reals.length > 1;
  const signs = reals.map((g) => Math.sign(num(g.root) ?? NaN));
  if (simple && (signs.every((s) => s > 0) || signs.every((s) => s < 0))) {
    const r0 = parts[0]!.root!;
    const cs = constants(n);
    const inner = add(...parts.map((p, i) => mul(cs[i]!, exp(mul(add(p.root!, mul(-1, r0)), x)))));
    return [mul(inner, exp(mul(r0, x))), n];
  }
  let k = 1;
  const terms = parts.map((p) => {
    const cs = constants(p.count, k);
    k += p.count;
    return p.build(cs);
  });
  return [add(...terms), n];
}

/** Particular solution by undetermined coefficients for constant-coefficient equations. */
function particular(coeffs: Expr[], rhs: Expr, x: Sym): Expr | undefined {
  if (isZeroE(rhs)) return S.Zero;
  const r = new Sym('_r');
  const chareq = add(...coeffs.map((c, k) => mul(c, pow(r, k))));
  const multiplicity = (z: Expr) => roots(chareq, r).filter((v) => isZeroE(simplify(add(v, mul(-1, z))))).length;
  const terms = expand(rhs) instanceof Add ? (expand(rhs) as Add).args : [expand(rhs)];
  // group terms by (exponent a, frequency b) of exp(a x) * {poly, sin(bx), cos(bx)}
  const trial: Expr[] = [];
  const unknowns: Sym[] = [];
  let u = 0;
  const fresh = () => {
    const s = new Sym(`_A${u++}`);
    unknowns.push(s);
    return s;
  };
  const seen = new Set<string>();
  for (const t of terms) {
    let a: Expr = S.Zero;
    let b: Expr = S.Zero;
    let deg = 0;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (!f.has(x)) continue;
      if (f.key === x.key) deg += 1;
      else if (f instanceof Pow && f.base.key === x.key && f.exp instanceof Rational && f.exp.isInteger) deg += Number(f.exp.p);
      else if (f instanceof Pow && f.base.key === S.E.key) {
        const pc = polyCoefficients(f.exp, x);
        if (!pc || Math.max(...pc.keys()) > 1) return undefined;
        a = add(a, pc.get(1) ?? S.Zero);
      } else if (f instanceof Fn && (f.name === 'sin' || f.name === 'cos')) {
        const pc = polyCoefficients(f.args[0]!, x);
        if (!pc || Math.max(...pc.keys()) > 1 || pc.has(0)) return undefined;
        b = pc.get(1)!;
      } else return undefined;
    }
    const key = `${a.key}|${b.key}`;
    const z = add(a, mul(S.I, b));
    const s = multiplicity(z);
    const sig = `${key}|${deg}`;
    if (seen.has(sig)) continue;
    seen.add(sig);
    const polyTerms = (): Expr => add(...Array.from({ length: deg + 1 }, (_, i) => mul(fresh(), pow(x, i + s))));
    const ex = isZeroE(a) ? S.One : exp(mul(a, x));
    if (isZeroE(b)) trial.push(mul(ex, polyTerms()));
    else trial.push(mul(ex, add(mul(polyTerms(), sin(mul(b, x))), mul(polyTerms(), cos(mul(b, x))))));
  }
  const yp = add(...trial);
  const L = add(...coeffs.map((c, k) => mul(c, diff(yp, x, k))));
  const residual = expand(add(L, mul(-1, rhs)));
  // collect coefficients of the independent functions of x
  const eqs: Expr[] = [];
  const basis = new Map<string, Expr[]>();
  for (const t of residual instanceof Add ? residual.args : [residual]) {
    const factors = t instanceof Mul ? t.args : [t];
    const fx = mul(...factors.filter((f) => f.has(x)));
    const c = mul(...factors.filter((f) => !f.has(x)));
    const arr = basis.get(fx.key) ?? [];
    arr.push(c);
    basis.set(fx.key, arr);
  }
  for (const cs of basis.values()) eqs.push(add(...cs));
  const sol = linsolve(eqs, unknowns);
  if (!sol) return undefined;
  return expand(xreplace(yp, unknowns.map((s, i) => [s, sol[i]!] as const)));
}

/**
 * Solve an ordinary differential equation for f(x). Returns Eq(f(x), solution).
 * ics maps initial conditions, e.g. new Map([[f(0), 1], [Derivative(f(x), x).subs(x, 0), 0]]).
 */
/**
 * Solve an ordinary differential equation for f(x). Like SymPy, a list of
 * equations is returned when the general solution has several branches.
 */
export function dsolve(eqIn: ExprLike | readonly ExprLike[], fx?: Expr | readonly Expr[], opts: { ics?: [Expr, ExprLike][]; hint?: string } = {}): Expr | Expr[] {
  // a system of equations: linear first-order with constant coefficients
  if (Array.isArray(eqIn)) return dsolveSystem(eqIn, Array.isArray(fx) ? (fx as UndefFn[]) : undefined);
  if (Array.isArray(fx) || fx === undefined) throw new Error('dsolve: the unknown function f(x) is required');
  if (!(fx instanceof UndefFn) || fx.args.length !== 1 || !(fx.args[0] instanceof Sym)) {
    throw new Error('dsolve: f(x) with a single symbol argument expected');
  }
  const x = fx.args[0];
  const eq = asEquation(eqIn as ExprLike);
  const n = odeOrder(eq, fx);
  if (n === 0) throw new Error('dsolve: not a differential equation');
  // SymPy's hints in order (solvers/dsolve.ts); the older direct solvers below are a fallback
  const viaHints = dsolveRaw(eq, fx, opts.hint);
  if (viaHints && viaHints.length) {
    const out = opts.ics && opts.ics.length ? viaHints.map((s) => Eq(fx, applyIcs((s as Rel).rhs, fx, x, opts.ics!))) : viaHints;
    return out.length === 1 ? out[0]! : out;
  }
  const [E, ys] = toSymbols(eq, fx, n);
  const e = expand(E);
  let sol: Expr | undefined;

  // linear in y0..yn?
  const coeffs: Expr[] = [];
  let rest = e;
  let linear = true;
  for (const y of ys) {
    const pc = polyCoefficients(e, y);
    if (!pc || Math.max(...pc.keys()) > 1) {
      linear = false;
      break;
    }
    const c = pc.get(1) ?? S.Zero;
    if (ys.some((z) => c.has(z))) {
      linear = false;
      break;
    }
    coeffs.push(c);
    rest = add(rest, mul(-1, c, y));
  }
  rest = expand(rest);
  if (linear && ys.some((z) => rest.has(z))) linear = false;

  if (linear) {
    const lead = coeffs[n]!;
    const norm = coeffs.map((c) => cancel(mul(c, pow(lead, -1))));
    const rhs = cancel(mul(-1, rest, pow(lead, -1)));
    const constCoeff = norm.every((c) => !c.has(x));
    if (constCoeff) {
      const [yh] = constantCoeffHomogeneous(norm, x);
      const yp = particular(norm, rhs, x);
      if (yp !== undefined) sol = add(yh, yp);
    }
    if (sol === undefined && n === 1) {
      // y' + p y = q
      const p = norm[0]!;
      const q = rhs;
      const C1 = new Sym('C1');
      if (isZeroE(p)) sol = add(C1, integrate(q, x));
      else {
        const P = integrate(p, x);
        const mu = exp(P);
        if (isZeroE(q)) sol = mul(C1, exp(mul(-1, P)));
        else sol = expand(mul(exp(mul(-1, P)), add(C1, integrate(expand(mul(q, mu)), x))));
      }
    }
  }
  if (sol === undefined && n === 1) {
    // separable: y' = g(x) h(y)
    const pc = polyCoefficients(e, ys[1]!);
    if (pc && Math.max(...pc.keys()) === 1) {
      const rhs = cancel(mul(-1, pc.get(0) ?? S.Zero, pow(pc.get(1)!, -1)));
      const factors = rhs instanceof Mul ? rhs.args : [rhs];
      const g = mul(...factors.filter((f) => !f.has(ys[0]!)));
      const h = mul(...factors.filter((f) => f.has(ys[0]!)));
      if (!g.has(ys[0]!) && !h.has(x)) {
        const C1 = new Sym('C1');
        const lhs = integrate(pow(h, -1), ys[0]!);
        const r = add(integrate(g, x), C1);
        const sols = solve(add(lhs, mul(-1, r)), ys[0]!, { check: false });
        if (sols.length === 1) sol = pullMinus(sols[0]!);
      }
    }
  }
  if (sol === undefined && n === 1) {
    // 1st_exact: M(x, y) + N(x, y)*y' = 0 with dM/dy = dN/dx
    const sols = firstExact(e, x, ys[0]!, ys[1]!);
    if (sols) {
      const out = sols.map((s0) => Eq(fx, xreplace(s0, [[ys[0]!, fx]])));
      return out.length === 1 ? out[0]! : out;
    }
  }
  if (sol === undefined) throw new NotImplementedError('dsolve: unsupported equation');
  let result = sol;
  if (opts.ics && opts.ics.length) result = applyIcs(result, fx, x, opts.ics);
  return Eq(fx, result);
}

/** 1/(-a - b) -> -1/(a + b), like SymPy's normalized output. */
function pullMinus(e: Expr): Expr {
  if (e instanceof Pow && e.exp instanceof Rational && e.exp.isNegative && e.base instanceof Add && couldExtractMinusSign(e.base)) {
    return mul(e.exp.isInteger && e.exp.p % 2n === 0n ? 1 : -1, pow(mul(-1, e.base), e.exp));
  }
  return e;
}

function applyIcs(sol: Expr, fx: UndefFn, x: Sym, ics: [Expr, ExprLike][]): Expr {
  const cs = [...sol.freeSymbols()].filter((s) => /^C\d+$/.test(s.name));
  const eqs: Expr[] = [];
  for (const [cond, val] of ics) {
    // cond is f(a) or Derivative(f(x), x) evaluated at a (Subs) -- we accept f(a) and (Derivative, a) pairs
    if (cond instanceof UndefFn && cond.name === fx.name) {
      eqs.push(add(xreplace(sol, [[x, cond.args[0]!]]), mul(-1, sympify(val))));
    } else if (cond instanceof SubsNode && cond.expr instanceof Derivative && cond.expr.expr instanceof UndefFn && cond.variables.length === 1) {
      // f(x).diff(x, k).subs(x, a): Subs(Derivative(f(x), (x, k)), x, a)
      const k = cond.expr.variableCount.reduce((s, [, m]) => s + m, 0);
      eqs.push(add(xreplace(diff(sol, x, k), [[x, cond.point[0]!]]), mul(-1, sympify(val))));
    } else if (cond instanceof Derivative && cond.expr instanceof UndefFn) {
      const k = cond.variableCount.reduce((s, [, m]) => s + m, 0);
      const at = (cond.expr.args[0] as Expr) ?? x;
      eqs.push(add(xreplace(diff(sol, x, k), [[x, at]]), mul(-1, sympify(val))));
    }
  }
  const s = linsolve(eqs, cs);
  if (!s) throw new Error('dsolve: initial conditions are inconsistent');
  return simplify(xreplace(sol, cs.map((c, i) => [c, s[i]!] as const)));
}

/**
 * SymPy homogeneous_order(eq, *symbols): n such that eq(t*x, t*y, ...) = t**n * eq(x, y, ...),
 * or undefined when eq is not homogeneous in the symbols.
 */
export function homogeneousOrder(eqIn: ExprLike, ...symbols: Expr[]): Expr | undefined {
  let eq = sympify(eqIn);
  const hasDeriv = (e: Expr): boolean => e instanceof Derivative || e.args.some(hasDeriv);
  if (hasDeriv(eq)) return undefined;
  if (freeSymbols(eq).size === 0) return S.Zero;
  // replace applied functions of the symbols by dummies
  const syms: Expr[] = [];
  for (const s of symbols) {
    if (s instanceof UndefFn) {
      if (s.args.some((a) => !symbols.some((t) => t.key === a.key))) return undefined;
      const d = new Dummy('d');
      eq = xreplace(eq, [[s, d]]);
      syms.push(d);
    } else syms.push(s);
  }
  if (![...freeSymbols(eq)].some((s) => syms.some((t) => t.key === s.key))) return undefined;
  if (eq instanceof Fn) return homogeneousOrder(eq.args[0]!, ...syms)?.key === S.Zero.key ? S.Zero : undefined;
  const t = new Dummy('t', { positive: true });
  const scaled = xreplace(eq, syms.map((s) => [s, mul(t, s)] as const));
  const ratio = simplify(powsimp(mul(scaled, pow(eq, -1)), { force: false }));
  if (ratio instanceof Rational && ratio.isOne) return S.Zero;
  if (ratio.key === t.key) return S.One;
  if (ratio instanceof Pow && ratio.base.key === t.key && !ratio.exp.has(t)) return ratio.exp;
  return undefined;
}


/**
 * SymPy 1st_exact: for M + N*y' = 0 with dM/dy = dN/dx the potential
 * F = Integral(M, x) + Integral(N - d/dy Integral(M, x), y) is constant.
 * Returns the explicit solutions for y, or undefined.
 */
function firstExact(e: Expr, x: Sym, y: Sym, yp: Sym): Expr[] | undefined {
  const pc = polyCoefficients(e, yp);
  if (!pc || Math.max(...pc.keys()) !== 1) return undefined;
  const N = pc.get(1)!;
  const M = pc.get(0) ?? S.Zero;
  if (N.has(yp) || M.has(yp) || !N.has(y) && !M.has(y)) return undefined;
  const yy = y as unknown as Sym;
  const diffMN = simplify(add(diff(M, yy), mul(-1, diff(N, x))));
  if (!isZeroE(diffMN)) return undefined;
  const Fx = integrate(M, x);
  const rest = simplify(add(N, mul(-1, diff(Fx, yy))));
  const F = add(Fx, integrate(rest, yy));
  if (F.has(S.NaN) || containsIntegral(F)) return undefined;
  const C1 = new Sym('C1');
  let sols: Expr[];
  try {
    sols = solve(add(F, mul(-1, C1)), yy, { check: false });
  } catch {
    return undefined;
  }
  if (!sols.length) return undefined;
  // absorb a sign into the constant like SymPy constantsimp (-C1 -> C1) when that is simpler
  const flipped = sols.map((s0) => xreplace(s0, [[C1, mul(-1, C1)]]));
  const minus = (xs: Expr[]) => xs.reduce((n, t) => n + (t.toString().match(/-/g)?.length ?? 0), 0);
  return minus(flipped) < minus(sols) ? flipped : sols;
}

function containsIntegral(e: Expr): boolean {
  return e.kind === 'Integral' || e.args.some(containsIntegral);
}
