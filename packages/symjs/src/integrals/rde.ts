// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Risch differential equation Dy + f*y = g, ported from SymPy's
 * `sympy/integrals/rde.py` (Bronstein, "Symbolic Integration I", chapter
 * 6): the weak normalization, the normal and special parts of the
 * denominator, the degree bound, the SPDE reduction and the polynomial
 * cases without cancellation, and the cancellation cases of primitive and
 * hyperexponential monomials.
 *
 * The parametric problems of `prde.ts` and this module need each other;
 * `prde.ts` fills in {@link rdeHooks} when it is loaded (risch.ts loads
 * both).
 */

import { at, defined } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import type { Expr, Sym } from '../core/nodes';
import { Dummy, Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { rootsDict } from '../polys/poly';
import { cancel } from '../simplify/rational';
import type { DiffExtension } from './rischbase';
import { NonElementaryIntegralException, decrementLevel, derivation, derivationBasic, gcdexDiophantine, splitfactor } from './rischbase';
import { KPoly, fracIn, kCancel } from './rischpoly';

/** The parametric functions of prde.ts used here (set by prde.ts). */
export const rdeHooks: {
  parametricLogDeriv?: (fa: KPoly, fd: KPoly, wa: KPoly, wd: KPoly, DE: DiffExtension) => [Expr, Expr, Expr] | undefined;
  limitedIntegrate?: (fa: KPoly, fd: KPoly, G: [KPoly, KPoly][], DE: DiffExtension) => [[KPoly, KPoly], Expr[]] | undefined;
  isLogDerivKTRadicalInField?: (fa: KPoly, fd: KPoly, DE: DiffExtension) => [Expr, Expr] | undefined;
} = {};

const hooks = {
  parametricLogDeriv: (fa: KPoly, fd: KPoly, wa: KPoly, wd: KPoly, DE: DiffExtension): [Expr, Expr, Expr] | undefined => defined(rdeHooks.parametricLogDeriv, 'rdeHooks (integrals/prde)')(fa, fd, wa, wd, DE),
  limitedIntegrate: (fa: KPoly, fd: KPoly, G: [KPoly, KPoly][], DE: DiffExtension): [[KPoly, KPoly], Expr[]] | undefined => defined(rdeHooks.limitedIntegrate, 'rdeHooks (integrals/prde)')(fa, fd, G, DE),
  isLogDerivKTRadicalInField: (fa: KPoly, fd: KPoly, DE: DiffExtension): [Expr, Expr] | undefined => defined(rdeHooks.isLogDerivKTRadicalInField, 'rdeHooks (integrals/prde)')(fa, fd, DE),
};
const hook = <K extends keyof typeof hooks>(k: K): (typeof hooks)[K] => hooks[k];

/** A numeric value of an integer or rational expression (degree bounds). */
export function num(e: Expr | number): number {
  if (typeof e === 'number') return e;
  if (e instanceof Rational) return e.toNumber();
  throw new NotImplementedError(`a symbolic degree bound ${String(e)}`);
}

const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** The order of a at the irreducible p: the largest n with p**n | a (SymPy order_at). */
export function orderAt(a: KPoly, p: KPoly, t: Sym): number {
  if (a.isZero) return Infinity;
  const aa = a.as(t);
  if (p.degree === 1 && isZeroE(p.TC())) return aa.cs.findIndex((c) => !(c instanceof Rational && c.isZero));
  const powerList: [KPoly, number][] = [];
  let p1 = p;
  let tracks = 1;
  while (aa.rem(p1).isZero) {
    powerList.push([p1, tracks]);
    p1 = p1.mul(p1);
    tracks *= 2;
  }
  let n = 0;
  let product = KPoly.one(t);
  for (const [f, k] of powerList.reverse()) {
    const productf = product.mul(f);
    if (aa.rem(productf).isZero) {
      n += k;
      product = productf;
    }
  }
  return n;
}

/** The order at infinity of a/d (SymPy order_at_oo). */
export function orderAtOo(a: KPoly, d: KPoly): number {
  if (a.isZero) return Infinity;
  return d.degree - a.degree;
}

/** The positive integer roots of a polynomial, with multiplicity (SymPy real_roots filtered by ZZ). */
function positiveIntegerRoots(r: KPoly): number[] {
  return rootsDict(r.asExpr(), r.gen, { multiple: true }).flatMap((v) => (v instanceof Rational && v.isInteger && v.p > 0n ? [Number(v.p)] : []));
}

/** A weak normalizer q of f = a/d and f - Dq/q (SymPy weak_normalizer). */
export function weakNormalizer(a: KPoly, d: KPoly, DE: DiffExtension, z: Sym = new Dummy('z')): [KPoly, [KPoly, KPoly]] {
  const t = DE.t;
  const [dn] = splitfactor(d, DE);
  const g = dn.gcd(dn.diff());
  const dSqf = dn.quo(g);
  const d1 = dSqf.quo(dSqf.gcd(g));
  const Dd1 = derivation(d1, DE);
  const r = KPoly.of(a.sub(KPoly.of(z, t).mul(Dd1)).resultantPRS(d1)[0], z);
  if (!r.has(z)) return [KPoly.one(t), [a, d]];
  const N = positiveIntegerRoots(r);
  let q = KPoly.one(t);
  for (const n of N) q = q.mul(a.sub(Dd1.mulGround(n)).gcd(d1));
  const dq = derivation(q, DE);
  const sn = q.mul(a).sub(d.mul(dq));
  const sd = q.mul(d);
  return [q, kCancel(sn, sd)];
}

/** The normal part of the denominator (SymPy normal_denom): [a, (ba, bd), (ca, cd), h]. */
export function normalDenom(fa: KPoly, fd: KPoly, ga: KPoly, gd: KPoly, DE: DiffExtension): [KPoly, [KPoly, KPoly], [KPoly, KPoly], KPoly] {
  const [dn] = splitfactor(fd, DE);
  const [en] = splitfactor(gd, DE);
  const p = dn.gcd(en);
  const h = en.gcd(en.diff()).quo(p.gcd(p.diff()));
  const a = dn.mul(h);
  const c = a.mul(h);
  if (!c.div(en)[1].isZero) throw new NonElementaryIntegralException('normal_denom: no solution');
  const ca = kCancel(c.mul(ga), gd);
  const ba = kCancel(a.mul(fa).sub(dn.mul(derivation(h, DE)).mul(fd)), fd);
  return [a, ba, ca, h];
}

/** The special part of the denominator (SymPy special_denom): [A, B, C, h]. */
export function specialDenom(a: KPoly, ba: KPoly, bd: KPoly, ca: KPoly, cd: KPoly, DE: DiffExtension, caseIn = 'auto'): [KPoly, KPoly, KPoly, KPoly] {
  const t = DE.t;
  const kase = caseIn === 'auto' ? DE.case : caseIn;
  let p: KPoly;
  if (kase === 'exp') p = KPoly.monomial(1, 1, t);
  else if (kase === 'primitive' || kase === 'base') return [a, ba.quo(bd), ca.quo(cd), KPoly.one(t)];
  else if (kase === 'tan') throw new NotImplementedError('special_denom: the hypertangent case is not implemented');
  else throw new RangeError(`case must be one of {'exp', 'tan', 'primitive', 'base'}, not ${kase}.`);
  const nb = orderAt(ba, p, t) - orderAt(bd, p, t);
  const nc = orderAt(ca, p, t) - orderAt(cd, p, t);
  let n = Math.min(0, nc - Math.min(0, nb));
  if (nb === 0) {
    const dcoeff = DE.d.quo(p);
    const A = decrementLevel(DE, () => {
      const [alphaa, alphad] = fracIn(mul(-1, ba.eval(0), pow(bd.eval(0), -1), pow(a.eval(0), -1)), DE.t);
      const [etaa, etad] = fracIn(dcoeff.asExpr(), DE.t);
      return hook('parametricLogDeriv')(alphaa, alphad, etaa, etad, DE);
    });
    if (A !== undefined && A[0].key === S.One.key) n = Math.min(n, num(A[1]));
  }
  const N = Math.max(0, -nb, n - nc);
  const pN = p.pow(N);
  const pn = p.pow(-n);
  const A = a.mul(pN);
  const B = ba.mul(pN.quo(bd)).add(a.mulGround(n).mul(derivation(p, DE).quo(p)).mul(pN));
  const C = ca.mul(pN).mul(pn).quo(cd);
  return [A, B, C, pn];
}

/** A bound on the degree of a polynomial solution of a*Dq + b*q = c (SymPy bound_degree). */
export function boundDegree(a: KPoly, b: KPoly, cQ: KPoly | readonly KPoly[], DE: DiffExtension, caseIn = 'auto'): number {
  const kase = caseIn === 'auto' ? DE.case : caseIn;
  const da = a.degree;
  const db = b.degree;
  const dc = cQ instanceof KPoly ? cQ.degree : Math.max(...cQ.map((c) => c.degree));
  const alpha = cancel(mul(-1, b.LC(), pow(a.LC(), -1)));
  let n: number;
  if (kase === 'base') {
    n = Math.max(0, dc - Math.max(db, da - 1));
    if (db === da - 1 && alpha instanceof Rational && alpha.isInteger) n = Math.max(0, alpha.toNumber(), dc - db);
  } else if (kase === 'primitive') {
    n = db > da ? Math.max(0, dc - db) : Math.max(0, dc - da + 1);
    const [etaa, etad] = fracIn(DE.d.asExpr(), at(DE.T, DE.T.length + DE.level - 1));
    const t1 = DE.t;
    n = decrementLevel(DE, () => {
      const [alphaa, alphad] = fracIn(alpha, DE.t);
      if (db === da - 1) {
        // (SymPy catches NonElementaryIntegralException, which limited_integrate does not raise)
        const r = hook('limitedIntegrate')(alphaa, alphad, [[etaa, etad]], DE);
        if (r !== undefined) return intMax(n, at(r[1], 0));
      } else if (db === da) {
        const A = hook('isLogDerivKTRadicalInField')(alphaa, alphad, DE);
        if (A !== undefined && A[0].key === S.One.key) {
          const zz = A[1];
          // (SymPy takes derivation(z) as a polynomial in the lower monomial, which fails for z = 1/x:
          // the derivative is an element of the lower field)
          const beta = mul(-1, a.mul(KPoly.of(derivationBasic(zz, DE), t1)).add(b.mul(KPoly.of(zz, t1))).LC(), pow(mul(zz, a.LC()), -1));
          const [betaa, betad] = fracIn(beta, DE.t);
          const r = hook('limitedIntegrate')(betaa, betad, [[etaa, etad]], DE);
          if (r !== undefined) return intMax(n, at(r[1], 0));
        }
      }
      return n;
    });
  } else if (kase === 'exp') {
    n = Math.max(0, dc - Math.max(db, da));
    if (da === db) {
      const [etaa, etad] = fracIn(DE.d.quo(KPoly.monomial(1, 1, DE.t)).asExpr(), at(DE.T, DE.T.length + DE.level - 1));
      const A = decrementLevel(DE, () => {
        const [alphaa, alphad] = fracIn(alpha, DE.t);
        return hook('parametricLogDeriv')(alphaa, alphad, etaa, etad, DE);
      });
      if (A !== undefined && A[0].key === S.One.key) n = Math.max(n, num(A[1]));
    }
  } else if (kase === 'tan' || kase === 'other_nonlinear') {
    const delta = DE.d.degree;
    const alpha2 = cancel(mul(alpha, pow(DE.d.LC(), -1)));
    n = Math.max(0, dc - Math.max(da + delta - 1, db));
    if (db === da + delta - 1 && alpha2 instanceof Rational && alpha2.isInteger) n = Math.max(0, alpha2.toNumber(), dc - db);
  } else {
    throw new RangeError(`case must be one of {'exp', 'tan', 'primitive', 'other_nonlinear', 'base'}, not ${kase}.`);
  }
  return n;
}

/**
 * max(n, c) for an integer constant c of the limited integration problem
 * alpha = Dz + c*eta; another constant does not bound the degree (SymPy takes
 * max(n, c) for any c, which fails for a symbolic one, and Bronstein's bound
 * only uses integers).
 */
function intMax(n: number, c: Expr): number {
  return c instanceof Rational && c.isInteger ? Math.max(n, c.toNumber()) : n;
}

/** Rothstein's SPDE reduction (SymPy spde): [B, C, m, alpha, beta]. */
export function spde(a0: KPoly, b0: KPoly, c0: KPoly, n0: number, DE: DiffExtension): [KPoly, KPoly, number, KPoly, KPoly] {
  const zero = KPoly.zero(DE.t);
  let alpha = KPoly.one(DE.t);
  let beta = KPoly.zero(DE.t);
  let [a, b, c, n] = [a0, b0, c0, n0];
  for (;;) {
    if (c.isZero) return [zero, zero, 0, zero, beta];
    if (n < 0) throw new NonElementaryIntegralException('spde: negative degree bound');
    const g = a.gcd(b);
    if (!c.rem(g).isZero) throw new NonElementaryIntegralException('spde: gcd(a, b) does not divide c');
    [a, b, c] = [a.quo(g), b.quo(g), c.quo(g)];
    if (a.degree === 0) return [b.quo(a), c.quo(a), n, alpha, beta];
    const [r, z] = gcdexDiophantine(b, a, c);
    b = b.add(derivation(a, DE));
    c = z.sub(derivation(r, DE));
    n -= a.degree;
    beta = beta.add(alpha.mul(r));
    alpha = alpha.mul(a);
  }
}

/** Dq + b*q = c with deg b large enough (SymPy no_cancel_b_large). */
export function noCancelBLarge(b: KPoly, c0: KPoly, n0: number, DE: DiffExtension): KPoly {
  let q = KPoly.zero(DE.t);
  let [c, n] = [c0, n0];
  while (!c.isZero) {
    const m = c.degree - b.degree;
    if (!(m >= 0 && m <= n)) throw new NonElementaryIntegralException('no_cancel_b_large: no solution');
    const p = KPoly.monomial(mul(c.LC(), pow(b.LC(), -1)), m, DE.t);
    q = q.add(p);
    n = m - 1;
    c = c.sub(derivation(p, DE)).sub(b.mul(p));
  }
  return q;
}

/**
 * Dq + b*q = c with deg b small enough (SymPy no_cancel_b_small); in the
 * case b in k it returns [h, b0, c0] for the problem one level down.
 */
export function noCancelBSmall(b: KPoly, c0: KPoly, n0: number, DE: DiffExtension): KPoly | [KPoly, Expr, Expr] {
  let q = KPoly.zero(DE.t);
  let [c, n] = [c0, n0];
  while (!c.isZero) {
    const m = n === 0 ? 0 : c.degree - DE.d.degree + 1;
    if (!(m >= 0 && m <= n)) throw new NonElementaryIntegralException('no_cancel_b_small: no solution');
    let p: KPoly;
    if (m > 0) p = KPoly.monomial(mul(c.LC(), pow(mul(m, DE.d.LC()), -1)), m, DE.t);
    else {
      if (b.degree !== c.degree) throw new NonElementaryIntegralException('no_cancel_b_small: no solution');
      if (b.degree === 0) return [q, b.asExpr(), c.asExpr()];
      p = KPoly.monomial(mul(c.LC(), pow(b.LC(), -1)), 0, DE.t);
    }
    q = q.add(p);
    n = m - 1;
    c = c.sub(derivation(p, DE)).sub(b.mul(p));
  }
  return q;
}

/** Dq + b*q = c with deg b = deg Dt - 1 (SymPy no_cancel_equal). */
export function noCancelEqual(b: KPoly, c0: KPoly, n0: number, DE: DiffExtension): KPoly | [KPoly, number, KPoly] {
  let q = KPoly.zero(DE.t);
  let [c, n] = [c0, n0];
  const lc = cancel(mul(-1, b.LC(), pow(DE.d.LC(), -1)));
  const M = lc instanceof Rational && lc.isInteger && lc.isPositive ? lc.toNumber() : -1;
  while (!c.isZero) {
    const m = Math.max(M, c.degree - DE.d.degree + 1);
    if (!(m >= 0 && m <= n)) throw new NonElementaryIntegralException('no_cancel_equal: no solution');
    const uu = cancel(add(mul(m, DE.d.LC()), b.LC()));
    if (uu instanceof Rational && uu.isZero) return [q, m, c];
    // (m = 0 only when deg c = deg Dt - 1, which SymPy checks again)
    const p = m > 0 ? KPoly.monomial(mul(c.LC(), pow(uu, -1)), m, DE.t) : KPoly.monomial(mul(c.LC(), pow(b.LC(), -1)), 0, DE.t);
    q = q.add(p);
    n = m - 1;
    c = c.sub(derivation(p, DE)).sub(b.mul(p));
  }
  return q;
}

/** Dq + b*q = c in the primitive cancellation case (SymPy cancel_primitive). */
export function cancelPrimitive(b: KPoly, c0: KPoly, n0: number, DE: DiffExtension): KPoly {
  const [ba, bd] = decrementLevel(DE, () => {
    const [ba1, bd1] = fracIn(b.asExpr(), DE.t);
    const A = hook('isLogDerivKTRadicalInField')(ba1, bd1, DE);
    if (A !== undefined && A[0].key === S.One.key) throw new NotImplementedError('is_deriv_in_field() is required to  solve this problem.');
    return [ba1, bd1];
  });
  let [c, n] = [c0, n0];
  if (c.isZero) return c;
  if (n < c.degree) throw new NonElementaryIntegralException('cancel_primitive: no solution');
  let q = KPoly.zero(DE.t);
  while (!c.isZero) {
    // (deg c decreases: n = m - 1 bounds it, as SymPy checks again)
    const m = c.degree;
    const [sa, sd] = decrementLevel(DE, () => {
      const [a2a, a2d] = fracIn(c.LC(), DE.t);
      return rischDE(ba, bd, a2a, a2d, DE);
    });
    const stm = KPoly.monomial(mul(sa.asExpr(), pow(sd.asExpr(), -1)), m, DE.t);
    q = q.add(stm);
    n = m - 1;
    c = c.sub(b.mul(stm).add(derivation(stm, DE)));
  }
  return q;
}

/** Dq + b*q = c in the hyperexponential cancellation case (SymPy cancel_exp). */
export function cancelExp(b: KPoly, c0: KPoly, n0: number, DE: DiffExtension): KPoly {
  const eta = DE.d.quo(KPoly.monomial(1, 1, DE.t)).asExpr();
  const [etaa, etad] = decrementLevel(DE, () => {
    const [ea, ed] = fracIn(eta, DE.t);
    const [ba, bd] = fracIn(b.asExpr(), DE.t);
    const A = hook('parametricLogDeriv')(ba, bd, ea, ed, DE);
    if (A !== undefined && A[0].key === S.One.key) throw new NotImplementedError('is_deriv_in_field() is required to solve this problem.');
    return [ea, ed];
  });
  let [c, n] = [c0, n0];
  if (c.isZero) return c;
  if (n < c.degree) throw new NonElementaryIntegralException('cancel_exp: no solution');
  let q = KPoly.zero(DE.t);
  while (!c.isZero) {
    // (deg c decreases: n = m - 1 bounds it, as SymPy checks again)
    const m = c.degree;
    const [sa, sd] = decrementLevel(DE, () => {
      const [a1a0, a1d0] = fracIn(b.asExpr(), DE.t);
      const a1a = a1a0.mul(etad).add(etaa.mul(a1d0).mulGround(m));
      const a1d = a1d0.mul(etad);
      const [a2a, a2d] = fracIn(c.LC(), DE.t);
      return rischDE(a1a, a1d, a2a, a2d, DE);
    });
    const stm = KPoly.monomial(mul(sa.asExpr(), pow(sd.asExpr(), -1)), m, DE.t);
    q = q.add(stm);
    n = m - 1;
    c = c.sub(b.mul(stm).add(derivation(stm, DE)));
  }
  return q;
}

/** A polynomial solution of Dq + b*q = c of degree at most n (SymPy solve_poly_rde). */
export function solvePolyRde(b: KPoly, cQ: KPoly, n: number, DE: DiffExtension): KPoly {
  const dd = DE.d.degree;
  if (!b.isZero && (DE.case === 'base' || b.degree > Math.max(0, dd - 1))) return noCancelBLarge(b, cQ, n, DE);
  if ((b.isZero || b.degree < dd - 1) && (DE.case === 'base' || dd >= 2)) {
    const R = noCancelBSmall(b, cQ, n, DE);
    if (R instanceof KPoly) return R;
    const [h, b0, c0] = R;
    const y = decrementLevel(DE, () => solvePolyRde(KPoly.of(b0, DE.t), KPoly.of(c0, DE.t), n, DE).asExpr());
    return h.add(KPoly.of(y, DE.t));
  }
  if (dd >= 2 && b.degree === dd - 1 && n > num(cancel(mul(-1, b.LC(), pow(DE.d.LC(), -1))))) {
    const R = noCancelEqual(b, cQ, n, DE);
    if (R instanceof KPoly) return R;
    const [h, m, C] = R;
    return h.add(solvePolyRde(b, C, m, DE));
  }
  if (b.isZero) throw new NotImplementedError('Remaining cases for Poly (P)RDE are not yet implemented (is_deriv_in_field() required).');
  if (DE.case === 'exp') return cancelExp(b, cQ, n, DE);
  if (DE.case === 'primitive') return cancelPrimitive(b, cQ, n, DE);
  throw new NotImplementedError(`Other Poly (P)RDE cancellation cases are not yet implemented (${DE.case}).`);
}

/** rischDE, with undefined when there is no solution (NonElementaryIntegralException). */
export function rischDEOrNone(fa: KPoly, fd: KPoly, ga: KPoly, gd: KPoly, DE: DiffExtension): [KPoly, KPoly] | undefined {
  return recover((): [KPoly, KPoly] | undefined => rischDE(fa, fd, ga, gd, DE), NonElementaryIntegralException, undefined);
}

/** fn(), or the fallback when it raises an error of the class E (other errors are raised). */
export function recover<T>(fn: () => T, E: abstract new (...args: never[]) => Error, fallback: T): T {
  try {
    return fn();
  } catch (e) {
    if (!(e instanceof E)) throw e;
    return fallback;
  }
}

/** A solution y = ya/yd in K of Dy + f*y = g (SymPy rischDE); NonElementaryIntegralException if none. */
export function rischDE(fa0: KPoly, fd0: KPoly, ga: KPoly, gd: KPoly, DE: DiffExtension): [KPoly, KPoly] {
  const [, [fa, fd]] = weakNormalizer(fa0, fd0, DE);
  const [a, [ba, bd], [ca, cd], hn] = normalDenom(fa, fd, ga, gd, DE);
  const [A, B0, C0, hs] = specialDenom(a, ba, bd, ca, cd, DE);
  const n = recover(() => boundDegree(A, B0, C0, DE), NotImplementedError, Infinity);
  const [B, C, m, alpha, beta] = spde(A, B0, C0, n, DE);
  const y = C.isZero ? C : solvePolyRde(B, C, m, DE);
  return [alpha.mul(y).add(beta), hn.mul(hs)];
}
