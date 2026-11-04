// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The differential-algebra layer of the Risch algorithm, ported from
 * SymPy's `sympy/integrals/risch.py` (Aaron Meurer's implementation of
 * Bronstein, "Symbolic Integration I: Transcendental Functions"): the
 * differential extension state, the derivation, the splitting
 * factorization, the canonical representation, Hermite reduction,
 * polynomial reduction and the Lazard-Rioboo-Rothstein-Trager resultant
 * reduction.
 *
 * The construction of a differential extension from an integrand and the
 * integration drivers are in `risch.ts`, which builds on this module and on
 * `rde.ts` / `prde.ts` (they need the functions here, and the construction
 * needs theirs).
 */

import { at, first, getOrThrow } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import type { Expr, Sym } from '../core/nodes';
import { Dummy, Integral, Rational, S } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import type { LambdaNode } from '../core/lambda';
import { Lambda } from '../core/lambda';
import { log } from '../functions/elementary';
import { mgcd } from '../polys/mpoly';
import { RootSum } from '../polys/rootsum';
import { cancel, fraction } from '../simplify/rational';
import { KPoly, exprDiff, kCancel, kNorm } from './rischpoly';

/** The kind of a monomial of a differential extension: x itself (SymPy None), exp or log. */
export type ExtensionKind = 'none' | 'exp' | 'log';

/** The case of a monomial (SymPy get_case). */
export type RischCase = 'base' | 'primitive' | 'exp' | 'tan' | 'other_nonlinear' | 'other_linear';

/** A manually given differential extension (SymPy DifferentialExtension(extension={...})). */
export interface ExtensionSpec {
  /** The derivations Dt of the monomials, each a polynomial in its monomial. */
  D: readonly KPoly[];
  /** The monomials (by default the generators of D). */
  T?: readonly Sym[];
  /** The integration variable (by default T[0]). */
  x?: Sym;
  exts?: readonly ExtensionKind[];
  extargs?: readonly Expr[];
  Tfuncs?: readonly LambdaNode[];
}

/**
 * The state of a differential extension of K(x): the tower of monomials T
 * with their derivations D, and the current level (SymPy
 * DifferentialExtension; the construction from an integrand is
 * `DifferentialExtension` in risch.ts).
 */
export class DiffExtension {
  f: Expr = S.Zero;
  x: Sym;
  T: Sym[];
  D: KPoly[];
  fa: KPoly;
  fd: KPoly;
  Tfuncs: LambdaNode[];
  backsubs: [Expr, Expr][] = [];
  exts: ExtensionKind[];
  /** The argument of each exp/log monomial (S.Zero for x). */
  extargs: Expr[];
  cases: RischCase[] = [];
  case: RischCase = 'base';
  t: Sym;
  d: KPoly;
  newf: Expr = S.Zero;
  level = -1;

  constructor(extension: ExtensionSpec) {
    this.D = [...extension.D];
    this.T = extension.T ? [...extension.T] : this.D.map((d) => d.gen);
    this.x = extension.x ?? first(this.T);
    this.exts = extension.exts ? [...extension.exts] : [];
    this.extargs = extension.extargs ? [...extension.extargs] : [];
    this.Tfuncs = extension.Tfuncs ? [...extension.Tfuncs] : [];
    this.t = this.x;
    this.d = first(this.D);
    this.fa = KPoly.zero(this.x);
    this.fd = KPoly.one(this.x);
    this.autoAttrs();
  }

  /** The cases and the top level (SymPy _auto_attrs). */
  protected autoAttrs(): void {
    this.cases = this.D.map((d, i) => getCase(d, at(this.T, i)));
    this.level = -1;
    this.t = at(this.T, -1);
    this.d = at(this.D, -1);
    this.case = at(this.cases, -1);
  }

  /** The indices of the monomials of the given kind. */
  indices(extension: ExtensionKind): number[] {
    return this.exts.flatMap((e, i) => (e === extension ? [i] : []));
  }

  private setLevel(level: number): void {
    this.level = level;
    this.t = at(this.T, level);
    this.d = at(this.D, level);
    this.case = at(this.cases, level);
  }

  incrementLevel(): void {
    if (this.level >= -1) throw new RangeError('The level of the differential extension cannot be incremented any further.');
    this.setLevel(this.level + 1);
  }

  decrementLevel(): void {
    if (this.level <= -this.T.length) throw new RangeError('The level of the differential extension cannot be decremented any further.');
    this.setLevel(this.level - 1);
  }

  /** The monomials below the current one (SymPy DE.T[:DE.level]). */
  get lower(): Sym[] {
    return this.T.slice(0, this.T.length + this.level);
  }

  /** The pairs (t_i, f_i(x)) that substitute the monomials back, top first. */
  backSubstitution(): [Expr, Expr][] {
    const n = this.Tfuncs.length;
    return this.Tfuncs.map((f, i) => [at(this.T, this.T.length - n + i), f.call(this.x)] as [Expr, Expr]).reverse();
  }
}

/** Run fn one level down (SymPy `with DecrementLevel(DE)`). */
export function decrementLevel<T>(DE: DiffExtension, fn: () => T): T {
  DE.decrementLevel();
  try {
    return fn();
  } finally {
    DE.incrementLevel();
  }
}

/** Raised when an integral is proven nonelementary (SymPy NonElementaryIntegralException). */
export class NonElementaryIntegralException extends RangeError {}

/** An integral proven to be nonelementary by the Risch algorithm (printed as Integral). */
export class NonElementaryIntegral extends Integral {}

/** The case of the monomial t with derivation d (SymPy get_case). */
export function getCase(d: KPoly, t: Sym): RischCase {
  if (!d.has(t)) return d.isOne ? 'base' : 'primitive';
  const p = d.as(t);
  if (p.rem(KPoly.monomial(1, 1, t)).isZero) return 'exp';
  if (p.rem(KPoly.fromCoeffs([1, 0, 1], t)).isZero) return 'tan';
  if (p.degree > 1) return 'other_nonlinear';
  return 'other_linear';
}

/** The sum of D(v)*dp/dv over the monomials up to the current level. */
function derivSum(p: Expr, DE: DiffExtension): Expr {
  const n = DE.T.length + DE.level + 1;
  return add(...DE.T.slice(0, n).map((v, i) => mul(at(DE.D, i).asExpr(), exprDiff(p, v))));
}

/**
 * The derivation of p (a polynomial or an expression) as a polynomial in the
 * current monomial; with coefficientD only the coefficient derivation
 * kappa_D, which leaves the current monomial constant (SymPy derivation).
 */
export function derivation(p: KPoly | Expr, DE: DiffExtension, coefficientD = false): KPoly {
  const t = DE.t;
  if (coefficientD) {
    if (DE.level <= -DE.T.length) return KPoly.zero(t);
    return decrementLevel(DE, () => KPoly.of(derivSum(p instanceof KPoly ? p.asExpr() : p, DE), t));
  }
  return KPoly.of(derivSum(p instanceof KPoly ? p.asExpr() : p, DE), t);
}

/** The derivation of an expression, cancelled (SymPy derivation(basic=True)). */
export function derivationBasic(p: KPoly | Expr, DE: DiffExtension, coefficientD = false): Expr {
  if (coefficientD) {
    if (DE.level <= -DE.T.length) return S.Zero;
    return decrementLevel(DE, () => cancel(derivSum(p instanceof KPoly ? p.asExpr() : p, DE)));
  }
  return cancel(derivSum(p instanceof KPoly ? p.asExpr() : p, DE));
}

/** [s, t] with s*a + t*b = c and deg s < deg b (SymPy gcdex_diophantine). */
export function gcdexDiophantine(a: KPoly, b: KPoly, c: KPoly): [KPoly, KPoly] {
  const [s0, g] = a.halfGcdex(b);
  let s = s0.mul(c.exquo(g));
  if (!s.isZero && s.degree >= b.degree) s = s.div(b)[1];
  const t = c.sub(s.mul(a)).exquo(b);
  return [s, t];
}

/** The greatest common divisor of two expressions as polynomials in all their symbols (numerators). */
export function exprGcd(a: Expr, b: Expr): Expr {
  const na = fraction(cancel(a))[0];
  const nb = fraction(cancel(b))[0];
  const vars = [...new Map([...na.freeSymbols(), ...nb.freeSymbols()].map((s) => [s.key, s])).values()];
  return mgcd(na, nb, vars);
}

/**
 * The splitting factorization p = pn*ps: ps special (it divides D(ps)) and
 * pn normal (SymPy splitfactor).
 */
export function splitfactor(p: KPoly, DE: DiffExtension, coefficientD = false): [KPoly, KPoly] {
  const One = KPoly.one(DE.t);
  if (p.isZero) return [p, One];
  const Dp = derivation(p, DE, coefficientD);
  if (!p.has(DE.t)) {
    const s = KPoly.of(exprGcd(p.asExpr(), Dp.asExpr()), DE.t);
    return [p.exquo(s), s];
  }
  if (Dp.isZero) return [p, One];
  const h = p.gcd(Dp);
  const g = p.gcd(p.diff());
  const s = h.exquo(g);
  if (s.degree === 0) return [p, One];
  const [qn, qs] = splitfactor(p.exquo(s), DE, coefficientD);
  return [qn, qs.mul(s)];
}

/**
 * The splitting factorization of the square-free factors of p:
 * [normal parts, special parts], each with its multiplicity (SymPy
 * splitfactor_sqf). With z the polynomial is in z over the field of the
 * monomials.
 */
export function splitfactorSqf(p: KPoly, DE: DiffExtension, coefficientD = false, z?: Sym): [[KPoly, number][], [KPoly, number][]] {
  if (p.isZero) return [[[p, 1]], []];
  const N: [KPoly, number][] = [];
  const Sp: [KPoly, number][] = [];
  for (const [pi, i] of p.sqfListInclude()) {
    const Dpi = derivation(pi, DE, coefficientD);
    const Si = z ? pi.as(z).gcd(Dpi.as(z)) : KPoly.of(exprGcd(pi.asExpr(), Dpi.asExpr()), pi.gen);
    const Ni = pi.exquo(Si.as(pi.gen));
    if (!Si.isOne) Sp.push([Si.as(DE.t), i]);
    if (!Ni.isOne) N.push([Ni.as(DE.t), i]);
  }
  return [N, Sp];
}

/** f = a/d as q + bs/ds + cn/dn: polynomial, special and normal parts (SymPy canonical_representation). */
export function canonicalRepresentation(a0: KPoly, d0: KPoly, DE: DiffExtension): [KPoly, [KPoly, KPoly], [KPoly, KPoly]] {
  const l = pow(d0.LC(), -1);
  const a = a0.mulGround(l);
  const d = d0.mulGround(l);
  const [q, r] = a.div(d);
  const [dn, ds] = splitfactor(d, DE);
  const [b, c] = gcdexDiophantine(dn, ds, r);
  return [q, [b, ds], [c, dn]];
}

/**
 * Hermite reduction: f = Dg + h + r with h simple and r reduced
 * (SymPy hermite_reduce); returns [g, h, r] as numerator/denominator pairs.
 */
export function hermiteReduce(a0: KPoly, d0: KPoly, DE: DiffExtension): [[KPoly, KPoly], [KPoly, KPoly], [KPoly, KPoly]] {
  const l0 = pow(d0.LC(), -1);
  const [fp, fs, fn] = canonicalRepresentation(a0.mulGround(l0), d0.mulGround(l0), DE);
  const l = pow(fn[1].LC(), -1);
  let a = fn[0].mulGround(l);
  const d = fn[1].mulGround(l);
  let ga = KPoly.zero(DE.t);
  let gd = KPoly.one(DE.t);
  const dd = derivation(d, DE);
  let dm = d.gcd(dd);
  const ds = d.div(dm)[0];
  while (dm.degree > 0) {
    const ddm = derivation(dm, DE);
    const dm2 = dm.gcd(ddm);
    const dms = dm.div(dm2)[0];
    const dsDdmDm = ds.mul(ddm).div(dm)[0];
    const [b, c] = gcdexDiophantine(dsDdmDm.neg(), dms, a);
    const db = derivation(b, DE);
    const dsDms = ds.div(dms)[0];
    a = c.sub(db.mul(dsDms));
    ga = ga.mul(dm).add(b.mul(gd));
    gd = gd.mul(dm);
    [ga, gd] = kCancel(ga, gd);
    dm = dm2;
  }
  const [q, r0] = a.div(ds);
  [ga, gd] = kCancel(ga, gd);
  const [r, dr] = kCancel(r0, ds);
  const [rra, rrd] = kCancel(q.mul(fs[1]).add(fp.mul(fs[1])).add(fs[0]), fs[1]);
  return [
    [ga, gd],
    [r, dr],
    [rra, rrd],
  ];
}

/** p = Dq + r with deg r < deg Dt (SymPy polynomial_reduce, nonlinear case). */
export function polynomialReduce(p0: KPoly, DE: DiffExtension): [KPoly, KPoly] {
  let q = KPoly.zero(DE.t);
  let p = p0;
  while (p.degree >= DE.d.degree) {
    const m = p.degree - DE.d.degree + 1;
    const q0 = KPoly.monomial(mul(p.LC(), pow(mul(m, DE.d.LC()), -1)), m, DE.t);
    q = q.add(q0);
    p = p.sub(derivation(q0, DE));
  }
  return [q, p];
}

/** p in K[t, 1/t] as a polynomial in t and z = 1/t: [part in t, part in z] (SymPy as_poly_1t). */
export function asPoly1t(p: Expr, t: Sym, z: Sym): [KPoly, KPoly] {
  const [pa0, pd0] = fracInCancel(p, t);
  if (!pd0.isMonomial) throw new NotImplementedError(`${String(p)} is not an element of K[${t.name}, 1/${t.name}].`);
  const [tPart, remainder] = pa0.div(pd0);
  if (remainder.isZero) return [tPart, KPoly.zero(z)];
  const r = pd0.degree - remainder.degree;
  // remainder.transform(1, t)*t**r with t -> z: the reversed coefficients
  const zPart = KPoly.fromCoeffs(remainder.reverse(remainder.degree).cs, z).mul(KPoly.monomial(1, r, z)).quoGround(pd0.LC());
  return [tPart, zPart];
}

function fracInCancel(p: Expr, t: Sym): [KPoly, KPoly] {
  const [n, d] = fraction(cancel(p));
  return [KPoly.of(n, t), KPoly.of(d, t)];
}

/**
 * Lazard-Rioboo-Rothstein-Trager resultant reduction (SymPy
 * residue_reduce): [H, b] with H the pairs (s(z), S(z, t)) of the
 * logarithmic part sum_{s(alpha)=0} alpha*log(S(alpha, t)), and b false
 * when f - Dg is not in K[t] for any elementary g (then f has no
 * elementary integral).
 */
export function residueReduce(a0: KPoly, d0: KPoly, DE: DiffExtension, z: Sym = new Dummy('z'), invert = true): [[KPoly, KPoly][], boolean] {
  const t = DE.t;
  const [ac, dc] = kCancel(a0, d0);
  const lc = pow(dc.LC(), -1);
  let a = ac.mulGround(lc);
  const d = dc.mulGround(lc);
  if (a.isZero) return [[], true];
  a = a.div(d)[1];
  const pz = KPoly.of(z, t);
  const Dd = derivation(d, DE);
  const q = a.sub(pz.mul(Dd));
  const [r, R] = Dd.degree <= d.degree ? d.resultantPRS(q) : q.resultantPRS(d);
  const Rmap = new Map<number, KPoly>();
  for (const i of R) Rmap.set(i.degree, i);
  const [Np, Sp] = splitfactorSqf(KPoly.of(r, z), DE, true, z);
  const H: [KPoly, KPoly][] = [];
  for (const [s0, i] of Sp) {
    if (i === d.degree) {
      H.push([s0.as(z).monic(), d]);
      continue;
    }
    // (SymPy skips a missing subresultant; the subresultant of degree i is in the PRS when i is the
    // multiplicity of a factor of the resultant, Lazard-Rioboo-Trager)
    let h = getOrThrow(Rmap, i);
    for (const [a1, j] of KPoly.of(h.LC(), t).sqfListInclude(true)) {
      h = h.quoGround(exprGcd(a1.asExpr(), pow(s0.asExpr(), j)));
    }
    const s = s0.as(z).monic();
    if (invert) {
      const inv = KPoly.of(h.LC(), z).invert(s);
      const hh = h;
      h = KPoly.fromCoeffs(
        hh.cs.map((c, k) => (k === hh.degree ? S.One : c instanceof Rational && c.isZero ? c : KPoly.of(c, z).mul(inv).rem(s).asExpr())),
        t,
      );
    }
    H.push([s, h]);
  }
  const b = !Np.some(([i]) => {
    const e = cancel(i.asExpr());
    return e.has(t) || e.has(z);
  });
  return [H, b];
}

/** The logarithmic part as RootSums of i*log(S(i, t)) back in terms of x (SymPy residue_reduce_to_basic). */
export function residueReduceToBasic(H: readonly [KPoly, KPoly][], DE: DiffExtension, z: Sym): Expr {
  const i = new Dummy('i');
  const s = DE.backSubstitution();
  return add(
    ...H.map(([sz, h]) => {
      let body = mul(i, log(xreplace(h.asExpr(), [[z, i]])));
      for (const pr of s) body = xreplace(body, [pr]);
      return RootSum(sz.as(z).asExpr(), z, Lambda(i, body));
    }),
  );
}

/**
 * The sum of R(alpha) over the roots alpha of the square-free polynomial
 * s(z), for R = num/den rational in z (SymPy RootSum with a rational
 * function, _rational_case): the trace of R mod s via Newton's identities.
 */
export function rootSumRational(s0: KPoly, num: KPoly, den: KPoly): Expr {
  const s = s0.monic();
  const n = s.degree;
  // power sums p_k of the roots
  // the elementary symmetric functions e_k, k < n
  const e = (k: number): Expr => mul(k % 2 === 0 ? 1 : -1, s.nth(n - k));
  const p: Expr[] = [S.Zero];
  for (let k = 1; k < n; k++) {
    const terms: Expr[] = [mul(k % 2 === 0 ? -1 : 1, k, e(k))];
    for (let j = 1; j < k; j++) terms.push(mul(j % 2 === 0 ? -1 : 1, e(j), at(p, k - j)));
    p.push(kNorm(add(...terms)));
  }
  p[0] = sympify(n);
  const P = num.mul(den.invert(s)).rem(s);
  return kNorm(add(...P.cs.map((c, k) => mul(c, at(p, k)))));
}

/** The derivation of the logarithmic part (SymPy residue_reduce_derivation). */
export function residueReduceDerivation(H: readonly [KPoly, KPoly][], DE: DiffExtension, z: Sym): Expr {
  return add(
    ...H.map(([sz, h]) => {
      const Dh = derivation(h, DE);
      return rootSumRational(sz.as(z), KPoly.of(mul(z, Dh.asExpr()), z), KPoly.of(h.asExpr(), z));
    }),
  );
}
