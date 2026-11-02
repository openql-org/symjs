// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy ratsimpmodprime: simplification of a rational function
 * modulo a prime ideal given by a Groebner basis G (the algorithm of Monagan
 * and Pearce, "Rational Simplification Modulo a Polynomial Ideal"),
 * including SymPy's quick particular solution of the linear systems
 * (minsolve_linear_system with quick=True).
 */

import { Dummy, Expr, ExprLike, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { ordered } from '../core/match';
import { xreplace } from '../core/traverse';
import { leadingMonomial, reduced, type MonomialOrder } from '../polys/groebner';
import { Poly } from '../polys/sympoly';
import { linsolve } from '../solvers/solve';
import { cancel, fraction } from './rational';
import { compareKeys, sortKey } from '../printing/sortkey';

const isZero = (e: Expr) => e instanceof Rational && e.isZero;

/** SymPy minsolve_linear_system(system, *symbols, quick=True) for linear equations. */
function particularSolution(eqs: readonly Expr[], vars: readonly Sym[]): Map<string, Expr> | undefined {
  const sol0 = linsolve(eqs as Expr[], vars as Sym[]);
  if (!sol0) return undefined;
  // pivot variables only (free variables are solved as themselves)
  const s = new Map<string, [Sym, Expr]>();
  vars.forEach((v, i) => {
    if (sol0[i]!.key !== v.key) s.set(v.key, [v, sol0[i]!]);
  });
  if ([...s.values()].every(([, v]) => isZero(v)) && s.size === vars.length) return new Map([...s].map(([k, [, v]]) => [k, v]));
  const determined = new Map<string, Expr>();
  const update = () => {
    for (const [k, [v, e]] of [...s]) {
      const e2 = xreplace(e, [...determined].map(([dk, dv]) => [vars.find((u) => u.key === dk)!, dv] as [Expr, Expr]));
      if (e2.freeSymbols().size === 0 || ![...e2.freeSymbols()].some((f) => vars.some((u) => u.key === f.key))) {
        determined.set(k, e2);
        s.delete(k);
      } else s.set(k, [v, e2]);
    }
  };
  update();
  while (s.size) {
    // the value with the most free symbols (ties by sort key)
    const vals = [...s.values()].map(([, e]) => e);
    const k = vals.reduce((m, e) => {
      const a = e.freeSymbols().size;
      const b = m.freeSymbols().size;
      return a > b || (a === b && compareKeys(sortKey(e), sortKey(m)) > 0) ? e : m;
    });
    const kfree = ordered([...k.freeSymbols()]) as Sym[];
    const x = kfree[kfree.length - 1]!;
    if (kfree.length !== 1) determined.set(x.key, S.Zero);
    else {
      // k is linear in x: its root
      const c1 = cancel(xreplace(k, [[x, S.One]]));
      const c0 = cancel(xreplace(k, [[x, S.Zero]]));
      const val = cancel(mul(-1, c0, pow(add(c1, mul(-1, c0)), -1)));
      if (isZero(val) && ![...s.values()].some(([, e]) => !isZero(cancel(xreplace(e, [[x, val]]))))) determined.set(x.key, S.One);
      else determined.set(x.key, val);
    }
    update();
  }
  return determined;
}

/** SymPy ratsimpmodprime(expr, G, *gens, order=...): a simpler fraction equal to expr modulo the ideal of G (G a Groebner basis of a prime ideal). */
export function ratsimpmodprime(exprIn: ExprLike, G: readonly ExprLike[], gens: readonly Sym[], opts: { order?: MonomialOrder; quick?: boolean } = {}): Expr {
  const order = opts.order ?? 'grevlex';
  const quick = opts.quick ?? true;
  const Gs = G.map(sympify);
  let [num, denom] = fraction(cancel(sympify(exprIn)));
  const lms = Gs.map((g) => leadingMonomial(g, gens, order));
  const tested = new Set<string>();
  const divides = (m: number[], l: number[]) => l.every((k, i) => m[i]! >= k);
  const staircase = (n: number): Expr[] => {
    if (n === 0) return [S.One];
    const out: Expr[] = [];
    const rec = (start: number, left: number, m: number[]) => {
      if (left === 0) {
        if (lms.every((l) => !divides(m, l))) out.push(mul(...m.map((k, i) => pow(gens[i]!, k))));
        return;
      }
      for (let i = start; i < gens.length; i++) {
        const m2 = [...m];
        m2[i]!++;
        rec(i, left - 1, m2);
      }
    };
    rec(0, n, gens.map(() => 0));
    return [...out, ...staircase(n - 1)];
  };
  const totalDegree = (e: Expr) => Poly.from(e, gens).totalDegree();
  const step = (a: Expr, b: Expr, N: number, D: number): [Expr, Expr] => {
    let [c, d] = [a, b];
    let steps = 0;
    const maxdeg = totalDegree(a) + totalDegree(b);
    const bound = quick ? maxdeg - 1 : maxdeg;
    while (N + D <= bound) {
      if (tested.has(`${N},${D}`)) break;
      tested.add(`${N},${D}`);
      const M1 = staircase(N);
      const M2 = staircase(D);
      const Cs = M1.map((_, i) => new Dummy(`c${i}`));
      const Ds = M2.map((_, i) => new Dummy(`d${i}`));
      const cHat = add(...Cs.map((ci, i) => mul(ci, M1[i]!)));
      const dHat = add(...Ds.map((di, i) => mul(di, M2[i]!)));
      const ng = [...Cs, ...Ds];
      const r = reduced(add(mul(a, dHat), mul(-1, b, cHat)), Gs, [...gens, ...ng], order)[1];
      const Seqs = Poly.from(r, gens).coeffs();
      const sol = particularSolution(Seqs, ng);
      if (sol && ![...sol.values()].every(isZero)) {
        const reps = [...sol].map(([k, v]) => [ng.find((u) => u.key === k)!, v] as [Expr, Expr]);
        const ones = ng.map((u) => [u, S.One] as [Expr, Expr]);
        c = xreplace(xreplace(cHat, reps), ones);
        d = xreplace(xreplace(dHat, reps), ones);
        if (isZero(d)) throw new Error('ratsimpmodprime: ideal not prime?');
        break;
      }
      steps++;
      N++;
      D++;
    }
    if (steps > 0) {
      [c, d] = step(c, d, N, D - steps);
      [c, d] = step(c, d, N - steps, D);
    }
    return [c, d];
  };
  num = reduced(num, Gs, [...gens], order)[1];
  denom = reduced(denom, Gs, [...gens], order)[1];
  const [c, d] = step(num, denom, 0, 0);
  return mul(c, pow(d, -1));
}
