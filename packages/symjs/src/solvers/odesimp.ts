// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Post-processing of ODE solutions (port of SymPy solvers/ode/ode.py
 * odesimp, constantsimp and constant_renumber).
 */

import type { Expr } from '../core/nodes';
import { Add, Constant, Fn, Integral, Mul, Pow, Rational, Rel, Sym, UndefFn } from '../core/nodes';
import { Eq } from '../core/logic';
import { add, couldExtractMinusSign, mul, pow } from '../core/ops';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { asNumerDenom } from '../core/methods';
import { doit } from '../calculus/doit';
import { termsGcd } from '../polys/sympoly';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand } from '../simplify/expand';
import { logcombine, powsimp } from '../simplify/powsimp';
import { simplify } from '../simplify/simplify';
import { solve } from './solve';

const isExpPow = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** Number of occurrences of the symbol c in e (SymPy Basic.count). */
function count(e: Expr, c: Expr): number {
  if (e.key === c.key) return 1;
  return e.args.reduce((n, a) => n + count(a, c), 0);
}

const subset = (e: Expr, Cs: readonly Sym[]) => [...freeSymbols(e)].every((s) => Cs.some((c) => c.key === s.key));

/** SymPy _get_constant_subexpressions. */
function constantSubexpressions(expr: Expr, Cs: readonly Sym[]): Expr[] {
  const out: Expr[] = [];
  const walk = (e0: Expr) => {
    let e = e0;
    const fs = freeSymbols(e);
    if (fs.size && subset(e, Cs)) {
      out.push(e);
      return;
    }
    if (isExpPow(e)) e = expand(e);
    if (e instanceof Add || e instanceof Mul) {
      const consts = e.args.filter((a) => subset(a, Cs));
      if (consts.length > 1) {
        const x = e instanceof Add ? add(...consts) : mul(...consts);
        if (freeSymbols(x).size) out.push(x);
      }
    } else if (e instanceof Integral) {
      if (subset(e, Cs) && e.limits) out.push(e);
    }
    e.args.forEach(walk);
  };
  walk(expr);
  return out;
}

/** SymPy __remove_linear_redundancies (the Equality normalization). */
function removeLinearRedundancies(expr: Expr, CsIn: readonly Sym[]): Expr {
  const cnts = new Map(CsIn.map((c) => [c.key, count(expr, c)]));
  const Cs = CsIn.filter((c) => (cnts.get(c.key) ?? 0) > 0);
  const isC = (e: Expr) => Cs.some((c) => c.key === e.key);
  if (!(expr instanceof Rel && expr.op === 'Eq')) return expr;
  let lhs = expr.lhs;
  let rhs = expr.rhs;
  const f = (i: Expr) => i instanceof Rational || isC(i);
  if (lhs instanceof Sym && isC(lhs)) [lhs, rhs] = [rhs, lhs];
  const atomic = (e: Expr) => e.args.length === 0;
  if ((lhs instanceof Add || lhs instanceof Sym) && (rhs instanceof Add || rhs instanceof Sym)) {
    const l = atomic(lhs) ? [lhs] : [...lhs.args];
    const r = atomic(rhs) ? [rhs] : [...rhs.args];
    lhs = add(...l.filter((i) => !f(i)), mul(-1, add(...r.filter((i) => !f(i)))));
    rhs = add(...r.filter(f), mul(-1, add(...l.filter(f))));
  } else if ((lhs instanceof Mul || lhs instanceof Sym) && (rhs instanceof Mul || rhs instanceof Sym)) {
    const l = atomic(lhs) ? [lhs] : [...lhs.args];
    const t = l.filter(f);
    if (t.length) {
      lhs = mul(...l.filter((i) => !f(i)));
      rhs = mul(rhs, ...t.map((i) => i.pow(-1)));
    }
  }
  return Eq(lhs, rhs);
}

/** terms_gcd unless it would put exp both outside and inside a sum (SymPy _conditional_term_factoring). */
function conditionalTermFactoring(expr: Expr): Expr {
  const apply = (e: Expr): Expr => {
    try {
      return termsGcd(e, { clear: false, deep: true, expand: false });
    } catch {
      return e;
    }
  };
  // SymPy applies terms_gcd to the whole Equality, so the exp check below never fires for equations
  if (expr instanceof Rel) return Eq(apply(expr.lhs), apply(expr.rhs));
  const ne = apply(expr);
  if (ne instanceof Mul) {
    let asfac = false;
    let infac = false;
    for (const m of ne.args) {
      if (isExpPow(m)) asfac = true;
      else if (m instanceof Add) infac = m.args.some((t) => (t instanceof Mul ? t.args : [t]).some(isExpPow));
      if (asfac && infac) return expr;
    }
  }
  return ne;
}

/** Absorb constant subexpressions into the constants (SymPy constantsimp). */
export function constantsimp(exprIn: Expr, Cs: readonly Sym[]): Expr {
  let expr = exprIn;
  for (let round = 0; round < 10; round++) {
    const orig = expr;
    for (const xe of constantSubexpressions(expr, Cs)) {
      const xes = [...freeSymbols(xe)].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
      if (!xes.length) continue;
      if (xes.every((c) => count(expr, c) === count(xe, c))) expr = subs(expr, [[xe, xes[0]!]]);
    }
    expr = removeLinearRedundancies(expr, Cs);
    expr = conditionalTermFactoring(expr);
    if (expr.key === orig.key) return expr;
  }
  return expr;
}

/** Renumber the constants C1, C2, ... in order of appearance (SymPy constant_renumber). */
export function constantRenumber(expr: Expr, variables: readonly Expr[]): Expr {
  const vars = new Set(variables.map((v) => v.key));
  const consts = [...freeSymbols(expr)].filter((s) => !vars.has(s.key) && /^C\d+$/.test(s.name));
  const isConst = (e: Expr) => consts.some((c) => c.key === e.key);
  const found: Sym[] = [];
  const one = consts.map((c) => [c, Rational.of(1)] as [Expr, Expr]);
  const key = (e: Expr) => sortKey(xreplace(e, one));
  const walk = (e: Expr) => {
    if (e instanceof Rel) {
      walk(e.lhs);
      walk(e.rhs);
      return;
    }
    const hasC = consts.some((c) => e.has(c));
    if (!(e instanceof Mul || e instanceof Add || e instanceof Pow) && !(e instanceof Fn || e instanceof UndefFn) && !hasC) return;
    if (isConst(e)) {
      if (!found.some((c) => c.key === e.key)) found.push(e as Sym);
      return;
    }
    if (e instanceof Fn || e instanceof UndefFn || e instanceof Pow) {
      e.args.forEach(walk);
      return;
    }
    [...e.args].sort((a, b) => compareKeys(key(a), key(b))).forEach(walk);
  };
  walk(expr);
  const fresh = found.map((_, i) => new Sym(`C${i + 1}`));
  const tmp = found.map((_, i) => new Sym(`_Ctmp${i}`));
  let r = xreplace(expr, found.map((c, i) => [c, tmp[i]!] as [Expr, Expr]));
  r = xreplace(r, tmp.map((t, i) => [t, fresh[i]!] as [Expr, Expr]));
  return r;
}

/**
 * SymPy odesimp: evaluate integrals, simplify constants, solve for f(x) when
 * possible and renumber the constants.
 */
export function odesimp(ode: Expr, solIn: Expr, fx: UndefFn, hint: string): Expr[] {
  const x = fx.args[0] as Sym;
  const odeSyms = [...freeSymbols(ode)];
  let sol = hint === 'nth_linear_constant_coeff_homogeneous' ? solIn : doit(solIn);
  if (hint.startsWith('nth_linear_euler_eq_nonhomogeneous') && sol instanceof Rel) sol = Eq(simplify(sol.lhs), simplify(sol.rhs));
  if (!(sol instanceof Rel)) throw new TypeError('odesimp: an equation is expected');
  const constants = [...freeSymbols(sol)].filter((s) => !odeSyms.some((o) => o.key === s.key));
  sol = constantsimp(sol, constants);
  let eqs: Expr[];
  const s = sol as Rel;
  if (s.rhs.key === fx.key && !s.lhs.has(fx)) eqs = [Eq(s.rhs, s.lhs)];
  else if (s.lhs.key === fx.key && !s.rhs.has(fx)) eqs = [s];
  else {
    let sols: Expr[] = [];
    try {
      sols = solve(add(s.lhs, mul(-1, s.rhs)), fx, { check: false });
    } catch {
      sols = [];
    }
    if (!sols.length) eqs = [s];
    else {
      const expandSol = (t0: Expr): Expr => {
        // 1/(-a - b) -> -1/(a + b) like SymPy's solve output
        let t = t0;
        if (t instanceof Pow && t.base instanceof Add && t.exp instanceof Rational && t.exp.isInteger && t.exp.isNegative && t.base.args.every((a) => couldExtractMinusSign(a))) {
          t = mul(t.exp.p % 2n === 0n ? 1 : -1, pow(mul(-1, t.base), t.exp));
        }
        const [, den] = asNumerDenom(t);
        return den instanceof Add ? t : powsimp(expand(t), { combine: 'exp', deep: true });
      };
      eqs = sols.map((t) => Eq(fx, expandSol(t)));
    }
    if (hint.startsWith('1st_homogeneous_coeff')) {
      const C1 = constants.find((c) => c.name === 'C1') ?? new Sym('C1');
      eqs = eqs.map((e) => {
        let ni = logcombine(e, { force: true }) as Rel;
        if (ni.lhs instanceof Fn && ni.lhs.name === 'log' && ni.rhs instanceof Rational && ni.rhs.isZero) ni = Eq(mul(ni.lhs.args[0]!, C1.pow(-1)), C1) as Rel;
        return ni;
      });
    }
  }
  return eqs.map((e) => constantRenumber(constantsimp(e, constants), [...odeSyms, x]));
}

