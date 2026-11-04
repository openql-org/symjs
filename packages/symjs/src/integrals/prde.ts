// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The parametric Risch differential equation, the limited
 * integration problem and the structure theorems, ported from SymPy's
 * `sympy/integrals/prde.py` (Bronstein, "Symbolic Integration I", chapters
 * 7 and 9): param_rischDE, limited_integrate, parametric_log_deriv,
 * is_deriv_k, is_log_deriv_k_t_radical and
 * is_log_deriv_k_t_radical_in_field, with the constant system they solve.
 */

import { at, expectType, first } from '../core/guard';
import { xreplace } from '../core/traverse';
import { NotImplementedError } from '../core/errors';
import type { Expr } from '../core/nodes';
import { Dummy, Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { asNumerDenom } from '../core/methods';
import { lcm as ilcm } from '../core/numbers';
import { roots } from '../polys/poly';
import { factorListExpr } from '../polys/sympoly';
import { cancel } from '../simplify/rational';
import { boundDegree, num, orderAt, orderAtOo, rdeHooks, recover, weakNormalizer } from './rde';
import type { DiffExtension } from './rischbase';
import { decrementLevel, derivation, derivationBasic, exprGcd, gcdexDiophantine, residueReduce, residueReduceDerivation, splitfactor } from './rischbase';
import type { KMatrix } from './rischpoly';
import { KPoly, fracIn, kCancel, kColJoin, kCols, kEye, kNorm, kNullspace, kRowJoin, kRref, kZeros } from './rischpoly';

const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isRational = (v: unknown): v is Rational => v instanceof Rational;

/** The normal part of the denominator for a list of right-hand sides (SymPy prde_normal_denom). */
export function prdeNormalDenom(fa: KPoly, fd: KPoly, G: readonly [KPoly, KPoly][], DE: DiffExtension): [KPoly, [KPoly, KPoly], [KPoly, KPoly][], KPoly] {
  const [dn] = splitfactor(fd, DE);
  const gd = G.reduce((acc, [, d]) => acc.lcm(d), KPoly.one(DE.t));
  const [en] = splitfactor(gd, DE);
  const p = dn.gcd(en);
  const h = en.gcd(en.diff()).quo(p.gcd(p.diff()));
  const a = dn.mul(h);
  const c = a.mul(h);
  const ba = kCancel(a.mul(fa).sub(dn.mul(derivation(h, DE)).mul(fd)), fd);
  return [a, ba, G.map(([A, D]) => kCancel(c.mul(A), D)), h];
}

/** The special part of the denominator for a list of right-hand sides (SymPy prde_special_denom). */
export function prdeSpecialDenom(a: KPoly, ba: KPoly, bd: KPoly, G: readonly [KPoly, KPoly][], DE: DiffExtension, caseIn = 'auto'): [KPoly, KPoly, [KPoly, KPoly][], KPoly] {
  const t = DE.t;
  const kase = caseIn === 'auto' ? DE.case : caseIn;
  let p: KPoly;
  if (kase === 'exp') p = KPoly.monomial(1, 1, t);
  else if (kase === 'primitive' || kase === 'base') return [a, ba.quo(bd), [...G], KPoly.one(t)];
  else if (kase === 'tan') throw new NotImplementedError('prde_special_denom: the hypertangent case is not implemented');
  else throw new RangeError(`case must be one of {'exp', 'tan', 'primitive', 'base'}, not ${kase}.`);
  const nb = orderAt(ba, p, t) - orderAt(bd, p, t);
  const nc = Math.min(...G.map(([Ga, Gd]) => orderAt(Ga, p, t) - orderAt(Gd, p, t)));
  let n = Math.min(0, nc - Math.min(0, nb));
  if (nb === 0) {
    const dcoeff = DE.d.quo(p);
    const A = decrementLevel(DE, () => {
      const [alphaa, alphad] = fracIn(mul(-1, ba.eval(0), pow(bd.eval(0), -1), pow(a.eval(0), -1)), DE.t);
      const [etaa, etad] = fracIn(dcoeff.asExpr(), DE.t);
      return parametricLogDeriv(alphaa, alphad, etaa, etad, DE);
    });
    if (A !== undefined && A[0].key === S.One.key) n = Math.min(n, num(A[1]));
  }
  const N = Math.max(0, -nb);
  const pN = p.pow(N);
  const pn = p.pow(-n);
  const A = a.mul(pN);
  const B = ba.mul(pN.quo(bd)).add(a.mulGround(n).mul(derivation(p, DE).quo(p)).mul(pN));
  return [A, B, G.map(([Ga, Gd]) => kCancel(Ga.mul(pN).mul(pn), Gd)), pn];
}

/** The matrix of the coefficients of the polynomials p, rows by degree (SymPy Matrix(N + 1, m, lambda i, j: p[j].nth(i))). */
function coeffMatrix(p: readonly KPoly[], rows: number): KMatrix {
  return Array.from({ length: rows }, (_, i) => p.map((pj) => pj.nth(i)));
}

/** Linear constraints on the constants for a list of fractions (SymPy prde_linear_constraints). */
export function prdeLinearConstraints(_a: KPoly, _b: KPoly, G: readonly [KPoly, KPoly][], DE: DiffExtension): [KPoly[], KMatrix] {
  const d = G.reduce((acc, [, gd]) => acc.lcm(gd), first(G)[1]);
  const Q = G.map(([ga, gd]) => ga.mul(d.quo(gd)).div(d));
  const rs = Q.map(([, r]) => r);
  const M = rs.every((r) => r.isZero) ? [] : coeffMatrix(rs, Math.max(...rs.map((r) => r.degree)) + 1);
  void DE;
  return [Q.map(([q]) => q), M];
}

/** Linear constraints for polynomial right-hand sides (SymPy poly_linear_constraints). */
export function polyLinearConstraints(p: readonly KPoly[], d: KPoly): [KPoly[], KMatrix] {
  const qr = p.map((pi) => pi.div(d));
  const rs = qr.map(([, r]) => r);
  const M = rs.every((r) => r.isZero) ? [] : coeffMatrix(rs, Math.max(...rs.map((r) => r.degree)) + 1);
  return [qr.map(([q]) => q), M];
}

/**
 * The system for constant solutions of A*c = u (SymPy constant_system): the
 * rows with nonconstant entries are replaced by their derivatives.
 */
export function constantSystem(A0: KMatrix, u0: Expr[], DE: DiffExtension, cols = kCols(A0)): [KMatrix, Expr[]] {
  if (A0.length === 0 || cols === 0) return [A0, u0];
  const [Au] = kRref(kRowJoin(A0, u0.map((v) => [v])));
  let A = Au.map((r) => r.slice(0, -1));
  let u = Au.map((r) => at(r, -1));
  const rows = A.length;
  for (let j = 0; j < cols; j++) {
    for (let i = 0; i < rows; i++) {
      const Aij = at(at(A, i), j);
      if (!DE.T.some((s) => Aij.has(s))) continue;
      const Ri = at(A, i);
      const DAij = derivationBasic(Aij, DE);
      const Rm1 = Ri.map((v) => kNorm(mul(derivationBasic(v, DE), pow(DAij, -1))));
      const um1 = kNorm(mul(derivationBasic(at(u, i), DE), pow(DAij, -1)));
      const Aj = A.map((r) => at(r, j));
      A = A.map((r, k) => r.map((v, l) => kNorm(add(v, mul(-1, at(Aj, k), at(Rm1, l))))));
      u = u.map((v, k) => kNorm(add(v, mul(-1, at(Aj, k), um1))));
      A = [...A, Rm1];
      u = [...u, um1];
    }
  }
  return [A, u];
}

/** The SPDE reduction for a list of right-hand sides (SymPy prde_spde). */
export function prdeSpde(a: KPoly, b: KPoly, Q: readonly KPoly[], n: number, DE: DiffExtension): [KPoly, KPoly, KPoly[], KPoly[], number] {
  const RZ = Q.map((qi) => gcdexDiophantine(b, a, qi));
  const B = b.add(derivation(a, DE));
  const Qq = RZ.map(([ri, zi]) => zi.sub(derivation(ri, DE)));
  return [a, B, Qq, RZ.map(([r]) => r), n - a.degree];
}

/** [A | 0; I | -I] closing a parametric solution (shared by the no-cancellation cases). */
function closeSystem(A: KMatrix, m: number): KMatrix {
  const c = kEye(m);
  return kColJoin(
    kRowJoin(A, kZeros(A.length, m)),
    kRowJoin(
      c,
      c.map((r) => r.map((v) => mul(-1, v))),
    ),
  );
}

/** The parametric problem with deg b large enough (SymPy prde_no_cancel_b_large). */
export function prdeNoCancelBLarge(b: KPoly, Q0: readonly KPoly[], n: number, DE: DiffExtension): [KPoly[], KMatrix] {
  const db = b.degree;
  const m = Q0.length;
  const Q = [...Q0];
  const H = Q.map(() => KPoly.zero(DE.t));
  for (let N = n; N >= 0; N--) {
    for (let i = 0; i < m; i++) {
      const si = mul(at(Q, i).nth(N + db), pow(b.LC(), -1));
      const sitn = KPoly.monomial(si, N, DE.t);
      H[i] = at(H, i).add(sitn);
      Q[i] = at(Q, i).sub(derivation(sitn, DE)).sub(b.mul(sitn));
    }
  }
  const dc = Q.every((q) => q.isZero) ? -1 : Math.max(...Q.map((q) => q.degree));
  const M = coeffMatrix(Q, dc + 1);
  const [A] = constantSystem(M, M.map(() => S.Zero), DE, m);
  return [H, closeSystem(A, m)];
}

/** The parametric problem with deg b small enough (SymPy prde_no_cancel_b_small). */
export function prdeNoCancelBSmall(b: KPoly, Q0: readonly KPoly[], n: number, DE: DiffExtension): [KPoly[], KMatrix] {
  const m = Q0.length;
  const Q = [...Q0];
  const H = Q.map(() => KPoly.zero(DE.t));
  for (let N = n; N > 0; N--) {
    for (let i = 0; i < m; i++) {
      const si = mul(at(Q, i).nth(N + DE.d.degree - 1), pow(mul(N, DE.d.LC()), -1));
      const sitn = KPoly.monomial(si, N, DE.t);
      H[i] = at(H, i).add(sitn);
      Q[i] = at(Q, i).sub(derivation(sitn, DE)).sub(b.mul(sitn));
    }
  }
  if (b.degree > 0) {
    for (let i = 0; i < m; i++) {
      const si = KPoly.monomial(mul(at(Q, i).nth(b.degree), pow(b.LC(), -1)), 0, DE.t);
      H[i] = at(H, i).add(si);
      Q[i] = at(Q, i).sub(derivation(si, DE)).sub(b.mul(si));
    }
    const dc = Q.every((q) => q.isZero) ? -1 : Math.max(...Q.map((q) => q.degree));
    const M = coeffMatrix(Q, dc + 1);
    const [A] = constantSystem(M, M.map(() => S.Zero), DE, m);
    return [H, closeSystem(A, m)];
  }
  const t = DE.t;
  let f: KPoly[];
  let B: KMatrix;
  if (DE.case !== 'base') {
    const [f0, B0] = decrementLevel(DE, () => {
      const [ba, bd] = fracIn(b.asExpr(), DE.t);
      const Q1 = Q.map((qi) => fracIn(qi.TC(), DE.t));
      return paramRischDE(ba, bd, Q1, DE);
    });
    f = f0.map(([fa, fd]) => KPoly.of(mul(fa.asExpr(), pow(fd.asExpr(), -1)), t));
    B = B0;
  } else {
    f = [KPoly.one(t)];
    B = [[...Q.map((qi) => qi.TC()), S.Zero]];
  }
  const d = Math.max(...Q.map((q) => q.degree));
  let A: KMatrix;
  if (d > 0) {
    const M = Array.from({ length: d }, (_, i) => Q.map((qj) => qj.nth(i + 1)));
    [A] = constantSystem(M, M.map(() => S.Zero), DE, m);
  } else A = [];
  const r = f.length;
  const I = kEye(m);
  const A2 = A.map((row) => [...row, ...Array.from({ length: r + m }, () => S.Zero)]);
  const B2 = B.map((row) => [...row, ...Array.from({ length: m }, () => S.Zero)]);
  const C = kRowJoin(
    kRowJoin(I, kZeros(m, r)),
    I.map((row) => row.map((v) => mul(-1, v))),
  );
  return [[...f, ...H], kColJoin(kColJoin(A2, B2), C)];
}

/** The parametric cancellation case of Liouvillian monomials (SymPy prde_cancel_liouvillian). */
export function prdeCancelLiouvillian(b: KPoly, Q0: readonly KPoly[], n: number, DE: DiffExtension): [KPoly[], KMatrix] {
  const H: KPoly[] = [];
  let Q = [...Q0];
  let M: KMatrix = [];
  let ba: KPoly | undefined;
  let bd: KPoly | undefined;
  if (DE.case === 'primitive') [ba, bd] = decrementLevel(DE, () => fracIn(b.asExpr(), DE.t));
  for (let i = n; i >= 0; i--) {
    if (DE.case === 'exp') {
      const e = add(b.asExpr(), mul(i, derivation(DE.t, DE).asExpr(), pow(DE.t, -1)));
      [ba, bd] = decrementLevel(DE, () => fracIn(cancel(e), DE.t));
    }
    const [fi0, Ai] = decrementLevel(DE, () => {
      const Qy = Q.map((q) => fracIn(q.nth(i), DE.t));
      return paramRischDE(kpOf(ba), kpOf(bd), Qy, DE);
    });
    const fi = fi0.map(([fa, fd]) => KPoly.of(mul(fa.asExpr(), pow(fd.asExpr(), -1)), DE.t));
    const ri = fi.length;
    M = i === n ? Ai : kColJoin(Ai, M.map((row) => [...row, ...Array.from({ length: ri }, () => S.Zero)]));
    const hi = fi.map((f) => f.mul(KPoly.monomial(1, i, DE.t)));
    const Fi = hi.map((h) => derivation(h, DE).sub(b.mul(h)).neg());
    H.push(...hi);
    Q = [...Q, ...Fi];
  }
  return [H, M];
}

const kpOf = (p: KPoly | undefined): KPoly => {
  if (p === undefined) throw new NotImplementedError('prde_cancel_liouvillian: only primitive and exp cases');
  return p;
};

/** Polynomial solutions of the parametric problem a*Dq + b*q = sum c_i q_i (SymPy param_poly_rischDE). */
export function paramPolyRischDE(a0: KPoly, b0: KPoly, q0: readonly KPoly[], n0: number, DE: DiffExtension): [KPoly[], KMatrix] {
  const m = q0.length;
  if (n0 < 0) {
    if (q0.every((qi) => qi.isZero)) return [[], kZeros(1, m)];
    const N = Math.max(...q0.map((qi) => qi.degree));
    const M = coeffMatrix(q0, N + 1);
    const [A] = constantSystem(M, M.map(() => S.Zero), DE, m);
    return [[], A];
  }
  if (a0.isGround) {
    const ac = a0.LC();
    const b = b0.quoGround(ac);
    const q = q0.map((qi) => qi.quoGround(ac));
    const dd = DE.d.degree;
    if (!b.isZero && (DE.case === 'base' || b.degree > Math.max(0, dd - 1))) return prdeNoCancelBLarge(b, q, n0, DE);
    if ((b.isZero || b.degree < dd - 1) && (DE.case === 'base' || dd >= 2)) return prdeNoCancelBSmall(b, q, n0, DE);
    if (dd >= 2 && b.degree === dd - 1) throw new NotImplementedError('prde_no_cancel_b_equal() is not yet implemented.');
    if (DE.case === 'primitive' || DE.case === 'exp') return prdeCancelLiouvillian(b, q, n0, DE);
    throw new NotImplementedError('non-linear and hypertangent cases have not yet been implemented');
  }
  let [a, b, q, n] = [a0, b0, [...q0], n0];
  let alpha = KPoly.one(DE.t);
  let beta = q.map(() => KPoly.zero(DE.t));
  let d = KPoly.one(DE.t);
  while (n >= 0) {
    let r: KPoly[];
    [a, b, q, r, n] = prdeSpde(a, b, q, n, DE);
    const al = alpha;
    beta = beta.map((bi, i) => bi.add(al.mul(at(r, i))));
    alpha = alpha.mul(a);
    d = a.gcd(b);
    if (!d.isGround) break;
  }
  const [qq, M] = polyLinearConstraints(q, d);
  const [A] = constantSystem(M, M.map(() => S.Zero), DE, m);
  const V = kNullspace(A, m);
  if (!V.length) return [[], kEye(m)];
  const r = V.map((vj) => sumPolys(qq, vj, DE));
  const f = V.map((vj) => sumPolys(beta, vj, DE));
  const [g, B] = paramPolyRischDE(a.quo(d), b.quo(d), r, n, DE);
  const h = [...f, ...g.map((gk) => alpha.mul(gk))];
  return [h, assemble(m, V, g.length, B)];
}

/** sum v_j*p_j. */
function sumPolys(p: readonly KPoly[], v: readonly Expr[], DE: DiffExtension): KPoly {
  return p.reduce((acc, pj, j) => acc.add(pj.as(DE.t).mulGround(at(v, j))), KPoly.zero(DE.t));
}

/** [-I | V | 0; 0 | B] (the system of param_rischDE and param_poly_rischDE). */
function assemble(m: number, V: readonly Expr[][], nh: number, B: KMatrix): KMatrix {
  const top = kEye(m).map((row, i) => [...row.map((v) => mul(-1, v)), ...V.map((vj) => at(vj, i)), ...Array.from({ length: nh }, () => S.Zero)]);
  const bottom = B.map((row) => [...Array.from({ length: m }, () => S.Zero), ...row]);
  return [...top, ...bottom];
}

/**
 * Solutions of Dy + f*y = sum c_i g_i: [h, A] with every solution
 * y = sum d_j h_j where (c, d) satisfies A*(c, d) = 0 (SymPy param_rischDE).
 */
export function paramRischDE(fa0: KPoly, fd0: KPoly, G0: readonly [KPoly, KPoly][], DE: DiffExtension): [[KPoly, KPoly][], KMatrix] {
  const m = G0.length;
  const [q, [fa, fd]] = weakNormalizer(fa0, fd0, DE);
  let gamma = q;
  const G1 = G0.map(([ga, gd]) => kCancel(q.mul(ga), gd));
  const [a0, [ba, bd], G2, hn] = prdeNormalDenom(fa, fd, G1, DE);
  gamma = gamma.mul(hn);
  const [A0, B0, G3, hs] = prdeSpecialDenom(a0, ba, bd, G2, DE);
  gamma = gamma.mul(hs);
  const g0 = A0.gcd(B0);
  const a = A0.quo(g0);
  const b = B0.quo(g0);
  const g = G3.map(([gia, gid]) => kCancel(gia, gid.mul(g0)));
  const [qs, M0] = prdeLinearConstraints(a, b, g, DE);
  const [M] = constantSystem(M0, M0.map(() => S.Zero), DE, m);
  const V = kNullspace(M, m);
  if (!V.length) return [[], kEye(m)];
  const r = V.map((vj) => sumPolys(qs, vj, DE));
  const n = recover(() => boundDegree(a, b, r, DE), NotImplementedError, 5);
  const [h, B] = paramPolyRischDE(a, b, r, n, DE);
  const A = assemble(m, V, h.length, B);
  const v = h.length;
  const W = kNullspace(A, m + V.length + v);
  const elements = W.map((wl) => [...wl.slice(0, m), ...wl.slice(m + V.length)]);
  const N = kNullspace(elements, m + v);
  return [h.map((hk) => kCancel(hk, gamma)), N];
}

/** The reduction of the limited integration problem to a parametric one (SymPy limited_integrate_reduce). */
export function limitedIntegrateReduce(fa: KPoly, fd: KPoly, G: readonly [KPoly, KPoly][], DE: DiffExtension): [KPoly, KPoly, KPoly, number, [KPoly, KPoly], [KPoly, KPoly][]] {
  const [dn, ds] = splitfactor(fd, DE);
  const E = G.map(([, gd]) => splitfactor(gd, DE));
  const c = E.reduce((acc, [en]) => acc.lcm(en), dn);
  const hn = c.gcd(c.diff());
  if (!['base', 'primitive', 'exp', 'tan'].includes(DE.case)) throw new NotImplementedError('limited_integrate_reduce: nonlinear monomials');
  const hs = E.reduce((acc, [, es]) => acc.lcm(es), ds);
  const a = hn.mul(hs);
  const b = derivation(hn, DE).neg().sub(hn.mul(derivation(hs, DE)).quo(hs));
  const mu = Math.min(orderAtOo(fa, fd), ...G.map(([ga, gd]) => orderAtOo(ga, gd)));
  const N = hn.degree + hs.degree + Math.max(0, 1 - DE.d.degree - mu);
  const V = G.map(([ga, gd]) => kCancel(a.mul(hn).mul(ga).neg(), gd));
  return [a, b, a, N, kCancel(a.mul(hn).mul(fa), fd), V];
}

/**
 * Limited integration: f = Dv + sum c_i w_i with constants c_i
 * (SymPy limited_integrate); [v, c] or undefined.
 */
export function limitedIntegrate(fa0: KPoly, fd0: KPoly, G: readonly [KPoly, KPoly][], DE: DiffExtension): [[KPoly, KPoly], Expr[]] | undefined {
  const fa = fa0.quoGround(fd0.LC());
  const fd = fd0.monic();
  const [h, A] = paramRischDE(KPoly.zero(DE.t), KPoly.one(DE.t), [[fa, fd], ...G], DE);
  // (SymPy builds C from no rows as a 0 x 0 matrix, whose null space is empty; with no constraints
  // every vector is a solution)
  const V = kNullspace(A, 1 + G.length + h.length).filter((v) => !isZeroE(first(v)));
  if (!V.length) return undefined;
  const v0 = first(V);
  const c0 = first(v0);
  const v = v0.map((e) => kNorm(mul(e, pow(mul(-1, c0), -1))));
  const r = h.length;
  const mm = v.length - r - 1;
  const C = v.slice(1, mm + 1);
  const y = mul(-1, add(...h.map(([ha, hd], i) => mul(at(v, mm + 1 + i), ha.asExpr(), pow(hd.asExpr(), -1)))));
  const [yn, yd] = asNumerDenom(y);
  const Ya = KPoly.of(yn, DE.t);
  const Yd = KPoly.of(yd, DE.t);
  return [[Ya.quoGround(Yd.LC()), Yd.monic()], C];
}

/** The constant c1 solving the linear equations e_i - c1*w_i = 0, if there is exactly one. */
function solveC1(eqs: readonly [Expr, Expr][]): Expr | undefined {
  let c: Expr | undefined;
  const nontrivial = eqs.filter(([e, w]) => !isZeroE(kNorm(e)) || !isZeroE(kNorm(w)));
  for (const [e, w] of nontrivial) {
    if (isZeroE(kNorm(w))) return undefined;
    const v = kNorm(mul(e, pow(w, -1)));
    if (c === undefined) c = v;
    else if (!isZeroE(kNorm(add(c, mul(-1, v))))) return undefined;
  }
  return c;
}

/** Heuristic parametric logarithmic derivative (SymPy parametric_log_deriv_heu): [n, m, v] or undefined. */
export function parametricLogDerivHeu(fa: KPoly, fd: KPoly, wa: KPoly, wd: KPoly, DE: DiffExtension): [Expr, Expr, Expr] | undefined {
  const [p] = fa.div(fd);
  const [q] = wa.div(wd);
  const B = Math.max(0, derivation(DE.t, DE).degree - 1);
  const C = Math.max(p.degree, q.degree);
  const finish = (s: Expr | undefined): [Expr, Expr, Expr] | undefined => {
    if (!(s instanceof Rational)) return undefined;
    const [M, N] = [Rational.of(s.p), Rational.of(s.q)];
    const nfmwa = fa.mul(wd).mulGround(N).sub(wa.mul(fd).mulGround(M));
    const nfmwd = fd.mul(wd);
    const Qv = isLogDerivKTRadicalInField(nfmwa, nfmwd, DE, 'auto');
    if (Qv === undefined) return undefined;
    // (SymPy also returns None for Q = 0 or v = 0; is_log_deriv_k_t_radical_in_field returns neither)
    const [Q, v] = Qv;
    return [mul(Q, N), mul(Q, M), v];
  };
  if (q.degree > B) {
    const eqs: [Expr, Expr][] = [];
    for (let i = B + 1; i <= C; i++) eqs.push([p.nth(i), q.nth(i)]);
    return finish(solveC1(eqs));
  }
  if (p.degree > B) return undefined;
  const lf = fd.LC();
  const lw = wd.LC();
  const c = cancel(mul(lf, lw, pow(exprGcd(lf, lw), -1)));
  const l = fd.monic().lcm(wd.monic()).mulGround(c);
  const [ln, ls] = splitfactor(l, DE);
  const z = ls.mul(ln.gcd(ln.diff()));
  if (!z.has(DE.t)) return undefined;
  const r1 = fa.mul(l.quo(fd)).div(z)[1];
  const r2 = wa.mul(l.quo(wd)).div(z)[1];
  const eqs: [Expr, Expr][] = [];
  for (let i = 0; i < z.degree; i++) eqs.push([r1.nth(i), r2.nth(i)]);
  return finish(solveC1(eqs));
}

/** Parametric logarithmic derivative (SymPy parametric_log_deriv, the heuristic). */
export function parametricLogDeriv(fa: KPoly, fd: KPoly, wa: KPoly, wd: KPoly, DE: DiffExtension): [Expr, Expr, Expr] | undefined {
  return parametricLogDerivHeu(fa, fd, wa, wd, DE);
}

/** The exp and log parts of the structure-theorem system and its constant solution u. */
function structureSystem(dfa: KPoly, dfd: KPoly, DE: DiffExtension): Expr[] | undefined {
  if (DE.exts.length !== DE.D.length) {
    if (DE.cases.includes('tan') || DE.cases.some((c, i) => c === 'primitive' && !DE.indices('log').includes(i))) {
      throw new NotImplementedError('Real version of the structure theorems with hypertangent support is not yet implemented.');
    }
    throw new NotImplementedError('Nonelementary extensions not supported in the structure theorems.');
  }
  const E = DE.indices('exp').map((i) => at(DE.D, i).quo(KPoly.monomial(1, 1, at(DE.T, i))).asExpr());
  const L = DE.indices('log').map((i) => at(DE.D, i).asExpr());
  const lhs = [[...E, ...L]];
  const rhs = [kNorm(mul(dfa.asExpr(), pow(dfd.asExpr(), -1)))];
  const [A, u] = constantSystem(lhs, rhs, DE);
  if (A.length === 0 || kCols(A) === 0 || !u.every((i) => isZeroE(derivationBasic(i, DE)))) return undefined;
  if (!u.every((i) => i instanceof Rational)) throw new NotImplementedError('Cannot work with non-rational coefficients in this case.');
  return u;
}

/**
 * Is f = Df/f... the derivative of an element of k(t)? (SymPy is_deriv_k):
 * [ans, result, const] with f = D(result + log(const))-style data, or undefined.
 */
export function isDerivK(fa: KPoly, fd: KPoly, DE: DiffExtension): [[Expr, Expr][], Expr, Expr] | undefined {
  const [dfa, dfd] = kCancel(fd.mul(derivation(fa, DE)).sub(fa.mul(derivation(fd, DE))), fd.mul(fa));
  const u = structureSystem(dfa, dfd, DE);
  if (u === undefined) return undefined;
  const terms = [...DE.indices('exp').map((i) => at(DE.extargs, i)), ...DE.indices('log').map((i) => at(DE.T, i))];
  const ans: [Expr, Expr][] = terms.map((tm, k) => [tm, at(u, k)]);
  const result = add(...ans.map(([i, j]) => mul(i, j)));
  const argterms = [...DE.indices('exp').map((i) => at(DE.T, i)), ...DE.indices('log').map((i) => at(DE.extargs, i))];
  const l: Expr[] = [];
  const ld: Expr[] = [];
  argterms.forEach((i, k) => {
    const j = at(u, k);
    const [n, d] = asNumerDenom(i);
    l.push(sqfPow(n, j));
    ld.push(sqfPow(d, j));
  });
  const cst = cancel(mul(fa.asExpr(), pow(fd.asExpr(), -1), pow(mul(...l), -1), ...ld));
  return [ans, result, cst];
}

/** e**j as the product of the powers of its factors (SymPy is_deriv_k with sqf_list): (x**2)**(1/2) = x. */
function sqfPow(e: Expr, j: Expr): Expr {
  const [c, fs] = factorListExpr(e);
  return mul(pow(c, j), ...fs.map(([b, k]) => pow(b, mul(k, j))));
}

/**
 * Is f the logarithmic derivative of a k(t)-radical? (SymPy
 * is_log_deriv_k_t_radical): [ans, result, n, const] or undefined.
 */
export function isLogDerivKTRadical(fa: KPoly, fd: KPoly, DE: DiffExtension, Df = true): [[Expr, Expr][], Expr, Expr, Expr] | undefined {
  const [dfa, dfd] = Df ? kCancel(fd.mul(derivation(fa, DE)).sub(fa.mul(derivation(fd, DE))), fd.mul(fd)) : [fa, fd];
  const u0 = structureSystem(dfa, dfd, DE);
  if (u0 === undefined) return undefined;
  let nn = 1n;
  for (const i of u0) nn = ilcm(nn, expectType(i, isRational, 'rational coefficient').q);
  const n = Rational.of(nn);
  const u = u0.map((i) => mul(i, n));
  const terms = [...DE.indices('exp').map((i) => at(DE.T, i)), ...DE.indices('log').map((i) => at(DE.extargs, i))];
  const ans: [Expr, Expr][] = terms.map((tm, k) => [tm, at(u, k)]);
  const result = mul(...ans.map(([i, j]) => pow(i, j)));
  const argterms = [...DE.indices('exp').map((i) => at(DE.extargs, i)), ...DE.indices('log').map((i) => at(DE.T, i))];
  const cst = cancel(add(mul(fa.asExpr(), pow(fd.asExpr(), -1)), mul(-1, add(...argterms.map((i, k) => mul(i, at(u, k), pow(n, -1)))))));
  return [ans, result, n, cst];
}

/** The roots of a polynomial with rational coefficients when they are all rational. */
function rationalRoots(p: KPoly): Rational[] | undefined {
  // (SymPy: NotImplementedError, real roots over a domain with parameters)
  if (!p.cs.every((c) => c instanceof Rational)) throw new NotImplementedError(`real roots of ${String(p.asExpr())}`);
  const rs = roots(p.asExpr(), p.gen);
  return rs.length === p.degree && rs.every((r) => r instanceof Rational) ? rs.filter((r): r is Rational => r instanceof Rational) : undefined;
}

/**
 * Is f the logarithmic derivative of a k(t)-radical, with the radical in
 * k(t)? (SymPy is_log_deriv_k_t_radical_in_field): [n, u] with n*f = Du/u.
 */
export function isLogDerivKTRadicalInField(fa0: KPoly, fd0: KPoly, DE: DiffExtension, caseIn = 'auto', z: Dummy = new Dummy('z')): [Expr, Expr] | undefined {
  const [fa, fd] = kCancel(fa0, fd0);
  const [H, b] = residueReduce(fa, fd, DE, z);
  if (!b) return undefined;
  const rootLists: Rational[][] = [];
  for (const [i] of H) {
    const rs = rationalRoots(i);
    if (rs === undefined) return undefined;
    rootLists.push(rs);
  }
  const residueterms: [Expr, Rational][] = H.flatMap(([, h], j) => at(rootLists, j).map((i): [Expr, Rational] => [xreplace(h.asExpr(), [[z, i]]), i]));
  const pe = cancel(add(mul(fa.asExpr(), pow(fd.asExpr(), -1)), mul(-1, residueReduceDerivation(H, DE, z))));
  const p = KPoly.tryOf(pe, DE.t);
  if (p === undefined) return undefined;
  if (p.degree >= Math.max(1, DE.d.degree)) return undefined;
  const kase = caseIn === 'auto' ? DE.case : caseIn;
  let n: Expr;
  let u: Expr;
  if (kase === 'exp') {
    const [wa0, wd0] = kCancel(derivation(DE.t, DE), KPoly.monomial(1, 1, DE.t));
    const A = decrementLevel(DE, () => {
      const [pa, pd] = fracIn(p.asExpr(), DE.t, { cancel: true });
      const [wa, wd] = fracIn([wa0, wd0], DE.t);
      return parametricLogDeriv(pa, pd, wa, wd, DE);
    });
    if (A === undefined) return undefined;
    n = A[0];
    u = mul(A[2], pow(DE.t, A[1]));
  } else if (kase === 'primitive') {
    const A = decrementLevel(DE, () => {
      const [pa, pd] = fracIn(p.asExpr(), DE.t);
      return isLogDerivKTRadicalInField(pa, pd, DE, 'auto');
    });
    if (A === undefined) return undefined;
    [n, u] = A;
  } else if (kase === 'base') {
    if (!fd.gcd(fd.diff()).isGround || fa.degree >= fd.degree) return undefined;
    let nb = 1n;
    for (const [, i] of residueterms) nb = ilcm(nb, i.q);
    return [Rational.of(nb), mul(...residueterms.map(([i, j]) => pow(i, mul(j, nb))))];
  } else if (kase === 'tan') {
    throw new NotImplementedError('The hypertangent case is not yet implemented for is_log_deriv_k_t_radical_in_field()');
  } else {
    throw new RangeError(`The ${kase} case is not supported in this function.`);
  }
  let common = 1n;
  for (const [, j] of residueterms) common = ilcm(common, j.q);
  // (n is a positive integer: a common denominator)
  const nq = expectType(n, isRational, 'the integer n');
  common = ilcm(common, nq.p);
  const m = common / nq.p;
  const terms = residueterms.map(([i, j]) => pow(i, mul(j, Rational.of(common))));
  return [Rational.of(common), cancel(mul(pow(u, Rational.of(m)), ...terms))];
}

rdeHooks.parametricLogDeriv = parametricLogDeriv;
rdeHooks.limitedIntegrate = limitedIntegrate;
rdeHooks.isLogDerivKTRadicalInField = (fa, fd, DE) => isLogDerivKTRadicalInField(fa, fd, DE);
