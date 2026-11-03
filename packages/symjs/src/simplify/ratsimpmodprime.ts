// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy ratsimpmodprime: simplification of a rational function
 * modulo a prime ideal given by a Groebner basis G (the algorithm of Monagan
 * and Pearce, "Rational Simplification Modulo a Polynomial Ideal"),
 * including SymPy's quick particular solution of the linear systems
 * (minsolve_linear_system with quick=True).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Dummy, Rational, S } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { ordered } from '../core/match';
import { xreplace } from '../core/traverse';
import { leadingMonomial, reduced, type MonomialOrder } from '../polys/groebner';
import { Poly } from '../polys/sympoly';
import { linsolve } from '../matrices/linsys';
import { cancel, fraction } from './rational';
import { at, defined, expectType, last } from '../core/guard';
import { lcm as ilcm } from '../core/numbers';
import { compareKeys, sortKey } from '../printing/sortkey';

const isZero = (e: Expr) => e instanceof Rational && e.isZero;

/** The pivot variables of the solution of a linear system, with their values (SymPy solve_linear_system). */
function pivotSolution(eqs: readonly Expr[], vars: readonly Sym[]): Map<string, Expr> {
  // (the system is homogeneous, so it always has a solution)
  const sol0 = defined(linsolve(eqs, vars), 'a solution of the homogeneous system');
  const s = new Map<string, Expr>();
  vars.forEach((v, i) => {
    const si = at(sol0, i);
    if (si.key !== v.key) s.set(v.key, si);
  });
  return s;
}

const allZero = (s: ReadonlyMap<string, Expr>) => [...s.values()].every(isZero);

/** SymPy minsolve_linear_system(system, *symbols, quick=...) for homogeneous linear equations (internal). */
export function particularSolution(eqs: readonly Expr[], vars: readonly Sym[], quick: boolean): Map<string, Expr> {
  const s0 = pivotSolution(eqs, vars);
  // only the trivial solution of the pivots: SymPy returns it as it is
  if (allZero(s0)) return s0;
  if (!quick) return minimalSolution(eqs, vars);
  const s = new Map<string, [Sym, Expr]>();
  for (const [k, e] of s0) s.set(k, [defined(vars.find((u) => u.key === k)), e]);
  const determined = new Map<string, Expr>();
  const update = () => {
    for (const [k, [v, e]] of [...s]) {
      const e2 = xreplace(e, [...determined].map(([dk, dv]): [Expr, Expr] => [defined(vars.find((u) => u.key === dk)), dv]));
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
    const kfree = ordered([...k.freeSymbols()]);
    const x = last(kfree);
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

/** The index sets of size n of 0..N-1 in lexicographic order (Python itertools.combinations). */
function combinations(N: number, n: number): number[][] {
  const out: number[][] = [];
  const rec = (start: number, cur: number[]) => {
    if (cur.length === n) {
      out.push(cur);
      return;
    }
    for (let i = start; i < N; i++) rec(i + 1, [...cur, i]);
  };
  rec(0, []);
  return out;
}

const PRIME = 1000003;
const modp = (a: bigint): number => Number(((a % BigInt(PRIME)) + BigInt(PRIME)) % BigInt(PRIME));
const invp = (a: number): number => {
  // a**(p - 2) mod p
  let r = 1;
  let b = a;
  for (let e = PRIME - 2; e > 0; e >>= 1) {
    if (e & 1) r = (r * b) % PRIME;
    b = (b * b) % PRIME;
  }
  return r;
};

/**
 * A fast filter for the subset search: fullRank(cols) is true when the columns cols of the
 * coefficient matrix (its rows scaled to integers) are independent modulo a prime, so that the
 * subsystem has only the zero solution (a rank modulo p never exceeds the rank over Q).
 */
function fullRankTest(eqs: readonly Expr[], vars: readonly Sym[]): (cols: readonly number[]) => boolean {
  const zeros: [Expr, Expr][] = vars.map((v) => [v, S.Zero]);
  const rows: number[][] = eqs.map((e) => {
    // (the coefficients are rational: groebner works over QQ) the row scaled to integers
    const cs = vars.map((v) => expectType(xreplace(e, zeros.map(([u, z]): [Expr, Expr] => [u, u === v ? S.One : z])), (c): c is Rational => c instanceof Rational, 'a rational coefficient'));
    const l = cs.reduce((m, c) => ilcm(m, c.q), 1n);
    return cs.map((c) => modp((c.p * l) / c.q));
  });
  return (cols) => {
    const m = rows.map((r) => cols.map((j) => at(r, j)));
    let rank = 0;
    for (let j = 0; j < cols.length && rank < m.length; j++) {
      const piv = m.findIndex((r, i) => i >= rank && at(r, j) !== 0);
      if (piv < 0) continue;
      [m[rank], m[piv]] = [at(m, piv), at(m, rank)];
      const pr = at(m, rank);
      const inv = invp(at(pr, j));
      for (let i = rank + 1; i < m.length; i++) {
        const ri = at(m, i);
        const f = (at(ri, j) * inv) % PRIME;
        if (f) for (let k = j; k < cols.length; k++) ri[k] = (((at(ri, k) - f * at(pr, k)) % PRIME) + PRIME) % PRIME;
      }
      rank++;
    }
    return rank === cols.length;
  };
}

/**
 * SymPy minsolve_linear_system with quick=False: a solution with as few nonzero variables as
 * possible, found by trying the subsets of n variables for decreasing n.
 */
function minimalSolution(eqs: readonly Expr[], vars: readonly Sym[]): Map<string, Expr> {
  let bestsol = particularSolution(eqs, vars, true);
  const n0 = [...bestsol.values()].filter((v) => !isZero(v)).length;
  const fullRank = fullRankTest(eqs, vars);
  for (let n = n0 - 1; n > 1; n--) {
    let thissol: Map<string, Expr> | undefined;
    for (const nonzeros of combinations(vars.length, n)) {
      // a subsystem of full rank has only the zero solution
      if (fullRank(nonzeros)) continue;
      const nz = nonzeros.map((i) => at(vars, i));
      const zeros: [Expr, Expr][] = vars.filter((_, i) => !nonzeros.includes(i)).map((v) => [v, S.Zero]);
      const s = pivotSolution(eqs.map((e) => xreplace(e, zeros)), nz);
      if (s.size && !allZero(s)) {
        const ones: [Expr, Expr][] = nz.map((v) => [v, S.One]);
        const sol = new Map<string, Expr>();
        for (const v of vars) {
          const e = s.get(v.key);
          sol.set(v.key, e !== undefined ? xreplace(e, ones) : nz.includes(v) ? S.One : S.Zero);
        }
        thissol = sol;
        break;
      }
    }
    if (thissol === undefined) break;
    bestsol = thissol;
  }
  return bestsol;
}

/** SymPy ratsimpmodprime(expr, G, *gens, order=...): a simpler fraction equal to expr modulo the ideal of G (G a Groebner basis of a prime ideal). */
export function ratsimpmodprime(exprIn: ExprLike, G: readonly ExprLike[], gens: readonly Sym[], opts: { order?: MonomialOrder; quick?: boolean } = {}): Expr {
  const order = opts.order ?? 'grevlex';
  const quick = opts.quick ?? true;
  const Gs = G.map(sympify);
  let [num, denom] = fraction(cancel(sympify(exprIn)));
  const lms = Gs.map((g) => leadingMonomial(g, gens, order));
  const tested = new Set<string>();
  const divides = (m: number[], l: number[]) => l.every((k, i) => at(m, i) >= k);
  const staircase = (n: number): Expr[] => {
    if (n === 0) return [S.One];
    const out: Expr[] = [];
    const rec = (start: number, left: number, m: number[]) => {
      if (left === 0) {
        if (lms.every((l) => !divides(m, l))) out.push(mul(...m.map((k, i) => pow(at(gens, i), k))));
        return;
      }
      for (let i = start; i < gens.length; i++) {
        const m2 = [...m];
        m2[i] = at(m2, i) + 1;
        rec(i, left - 1, m2);
      }
    };
    rec(0, n, gens.map(() => 0));
    return [...out, ...staircase(n - 1)];
  };
  const totalDegree = (e: Expr) => Poly.from(e, gens).totalDegree();
  /** c_hat and d_hat at the solution, the variables it leaves free set to 1. */
  const substitute = (cHat: Expr, dHat: Expr, sol: ReadonlyMap<string, Expr>, ng: readonly Sym[]): [Expr, Expr] => {
    const reps = [...sol].map(([k, v]): [Expr, Expr] => [defined(ng.find((u) => u.key === k)), v]);
    const ones = ng.map((u) => [u, S.One] as [Expr, Expr]);
    return [xreplace(xreplace(cHat, reps), ones), xreplace(xreplace(dHat, reps), ones)];
  };
  type Sol = { cHat: Expr; dHat: Expr; S: Expr[]; ng: Sym[] };
  const step = (a: Expr, b: Expr, allsolIn: Sol[], NIn: number, DIn: number): [Expr, Expr, Sol[]] => {
    let N = NIn;
    let D = DIn;
    let [c, d] = [a, b];
    let allsol = allsolIn;
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
      const cHat = add(...Cs.map((ci, i) => mul(ci, at(M1, i))));
      const dHat = add(...Ds.map((di, i) => mul(di, at(M2, i))));
      const ng = [...Cs, ...Ds];
      const r = reduced(add(mul(a, dHat), mul(-1, b, cHat)), Gs, [...gens, ...ng], order)[1];
      const Seqs = Poly.from(r, gens).coeffs();
      const sol = particularSolution(Seqs, ng, true);
      if (!allZero(sol)) {
        [c, d] = substitute(cHat, dHat, sol, ng);
        if (isZero(d)) throw new RangeError('ratsimpmodprime: ideal not prime?');
        allsol.push({ cHat, dHat, S: Seqs, ng });
        if (N + D !== maxdeg) allsol = [last(allsol)];
        break;
      }
      steps++;
      N++;
      D++;
    }
    if (steps > 0) {
      [c, d, allsol] = step(c, d, allsol, N, D - steps);
      [c, d, allsol] = step(c, d, allsol, N - steps, D);
    }
    return [c, d, allsol];
  };
  // over ZZ (integer coefficients in the input) the result is normalized like SymPy's clear_denoms
  const overZZ = [num, denom, ...Gs].every((p) => Poly.from(p, gens).coeffs().every((k) => k instanceof Rational && k.isInteger));
  num = reduced(num, Gs, [...gens], order)[1];
  denom = reduced(denom, Gs, [...gens], order)[1];
  let [c, d, allsol] = step(num, denom, [], 0, 0);
  if (!quick && allsol.length) {
    // the solution with the fewest terms among the minimal solutions of the systems met
    const newsol = allsol.map(({ cHat, dHat, S: Seqs, ng }) => substitute(cHat, dHat, particularSolution(Seqs, ng, false), ng));
    // (the first of the smallest, as Python's min)
    const sizes = newsol.map(([cs, ds]) => Poly.from(cs, gens).terms().length + Poly.from(ds, gens).terms().length);
    [c, d] = at(newsol, sizes.indexOf(Math.min(...sizes)));
  }
  if (!overZZ) return mul(c, pow(d, -1));
  const [cn, cp] = Poly.from(c, gens).clearDenoms(true);
  const [dn, dp] = Poly.from(d, gens).clearDenoms(true);
  const r = expectType(mul(cn, pow(dn, -1)), (v): v is Rational => v instanceof Rational, 'the ratio of the denominators');
  return mul(cp.asExpr(), Rational.of(r.q), pow(mul(dp.asExpr(), Rational.of(r.p)), -1));
}
