// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, ntheory/elliptic_curve.py, BSD-3-Clause; see LICENSE.

/**
 * @file Elliptic curves `y**2 + a1*x*y + a3*y = x**3 + a2*x**2 + a4*x + a6` over the rationals or a prime
 * field GF(p) (SymPy EllipticCurve, EllipticCurvePoint): points, the group law, point orders, torsion
 * points, the discriminant, the j-invariant and the minimal Weierstrass equation.
 *
 * Deviations from SymPy, where SymPy's result is wrong: `pointsX` over the rationals returns the
 * rational points with that x-coordinate (SymPy returns the raw `solve` output of the homogeneous
 * polynomial), and torsion points are listed in increasing order of the divisors of the discriminant
 * (SymPy iterates them in the unspecified order of `divisors(generator=True)`).
 */

import type { Expr } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { TupleNode } from '../core/containers';
import { divisors } from './factor';
import { polynomialCongruence } from './residue';
import { add, mul, pow } from '../core/ops';
import { at, first, last } from '../core/guard';

/** An element of Q (den > 0, in lowest terms) or of GF(p) (den 1, 0 <= num < p). */
interface Elt {
  readonly n: bigint;
  readonly d: bigint;
}

const absB = (a: bigint): bigint => (a < 0n ? -a : a);
const gcdB = (a: bigint, b: bigint): bigint => {
  let [x, y] = [absB(a), absB(b)];
  while (y) [x, y] = [y, x % y];
  return x;
};
const modB = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;

/** The ring Q (p = 0) or GF(p) with SymPy's conversions (FF elements print in the symmetric range). */
class Domain {
  constructor(readonly p: bigint) {}
  of(n: bigint, d = 1n): Elt {
    if (this.p) return { n: modB(n * this.inv(modB(d, this.p)), this.p), d: 1n };
    const g = gcdB(n, d) * (d < 0n ? -1n : 1n);
    return { n: n / g, d: d / g };
  }
  /** The inverse of a nonzero residue (SymPy raises NotInvertible on a zero divisor). */
  private inv(a: bigint): bigint {
    let [r0, r1, s0, s1] = [a, this.p, 1n, 0n];
    while (r1) {
      const q = r0 / r1;
      [r0, r1, s0, s1] = [r1, r0 - q * r1, s1, s0 - q * s1];
    }
    if (r0 !== 1n) throw new RangeError('zero divisor');
    return modB(s0, this.p);
  }
  conv(v: ElementLike): Elt {
    if (typeof v === 'number') {
      if (!Number.isInteger(v)) throw new TypeError(`${v} is not an integer`);
      return this.of(BigInt(v));
    }
    if (typeof v === 'bigint') return this.of(v);
    return this.of(v.p, v.q);
  }
  add(a: Elt, b: Elt): Elt {
    return this.of(a.n * b.d + b.n * a.d, a.d * b.d);
  }
  sub(a: Elt, b: Elt): Elt {
    return this.of(a.n * b.d - b.n * a.d, a.d * b.d);
  }
  mul(a: Elt, b: Elt): Elt {
    return this.of(a.n * b.n, a.d * b.d);
  }
  div(a: Elt, b: Elt): Elt {
    if (b.n === 0n) throw new RangeError('zero divisor');
    return this.of(a.n * b.d, a.d * b.n);
  }
  neg(a: Elt): Elt {
    return this.of(-a.n, a.d);
  }
  /** a * k for a small integer k. */
  k(k: bigint, a: Elt): Elt {
    return this.of(k * a.n, a.d);
  }
  pow(a: Elt, e: number): Elt {
    let r = this.of(1n);
    for (let i = 0; i < e; i++) r = this.mul(r, a);
    return r;
  }
  eq(a: Elt, b: Elt): boolean {
    return a.n === b.n && a.d === b.d;
  }
  isZero(a: Elt): boolean {
    return a.n === 0n;
  }
  /** SymPy domain.to_sympy: a Rational; an element of GF(p) in the symmetric range. */
  toSympy(a: Elt): Rational {
    const n = this.p && a.n > this.p / 2n ? a.n - this.p : a.n;
    return Rational.of(n, a.d);
  }
}

/** A coordinate or coefficient: an integer or a rational number. */
export type ElementLike = number | bigint | Rational;

/** The terms of SymPy's Poly printer: `-x**3 - 1/2*x*z**2 + y**2*z`. */
function polyString(terms: readonly (readonly [Rational, readonly [number, number, number]])[], domain: string): string {
  const sorted = terms.filter(([c]) => !c.isZero).sort(([, a], [, b]) => b[0] - a[0] || b[1] - a[1]);
  const monom = (m: readonly [number, number, number]): string =>
    ['x', 'y', 'z']
      .map((v, i) => (m[i] === 0 ? '' : m[i] === 1 ? v : `${v}**${m[i]}`))
      .filter(Boolean)
      .join('*');
  const parts = sorted.map(([c, m], i) => {
    const neg = c.p < 0n;
    const a = Rational.of(neg ? -c.p : c.p, c.q);
    const mon = monom(m);
    const body = a.isOne ? mon : `${a.toString()}*${mon}`;
    return i === 0 ? (neg ? `-${body}` : body) : `${neg ? ' - ' : ' + '}${body}`;
  });
  return `Poly(${parts.join('')}, x, y, z, ${domain})`;
}

/**
 * The elliptic curve `y**2 + a1*x*y + a3*y = x**3 + a2*x**2 + a4*x + a6` over Q (modulus 0, the
 * default) or GF(modulus) (SymPy EllipticCurve(a4, a6, a1=0, a2=0, a3=0, modulus=0)).
 */
export class EllipticCurve {
  /** @internal */ readonly dom: Domain;
  /** @internal */ readonly a1: Elt;
  /** @internal */ readonly a2: Elt;
  /** @internal */ readonly a3: Elt;
  /** @internal */ readonly a4: Elt;
  /** @internal */ readonly a6: Elt;
  private readonly b2: Elt;
  private readonly b4: Elt;
  private readonly b6: Elt;
  private readonly discrim: Elt;
  readonly modulus: bigint;

  constructor(a4: ElementLike, a6: ElementLike, a1: ElementLike = 0, a2: ElementLike = 0, a3: ElementLike = 0, modulus: number | bigint = 0) {
    this.modulus = BigInt(modulus);
    const D = (this.dom = new Domain(this.modulus));
    [this.a1, this.a2, this.a3, this.a4, this.a6] = [D.conv(a1), D.conv(a2), D.conv(a3), D.conv(a4), D.conv(a6)];
    const { a1: A1, a2: A2, a3: A3, a4: A4, a6: A6 } = this;
    this.b2 = D.add(D.pow(A1, 2), D.k(4n, A2));
    this.b4 = D.add(D.k(2n, A4), D.mul(A1, A3));
    this.b6 = D.add(D.pow(A3, 2), D.k(4n, A6));
    const b8 = [D.mul(D.pow(A1, 2), A6), D.k(4n, D.mul(A2, A6)), D.neg(D.mul(D.mul(A1, A3), A4)), D.mul(A2, D.pow(A3, 2)), D.neg(D.pow(A4, 2))].reduce((s, t) => D.add(s, t));
    const { b2, b4, b6 } = this;
    this.discrim = [D.neg(D.mul(D.pow(b2, 2), b8)), D.k(-8n, D.pow(b4, 3)), D.k(-27n, D.pow(b6, 2)), D.k(9n, D.mul(D.mul(b2, b4), b6))].reduce((s, t) => D.add(s, t));
  }

  /** SymPy `curve(x, y, z=1)`: the point (x : y : z) of the curve. */
  call(x: ElementLike, y: ElementLike, z: ElementLike = 1): EllipticCurvePoint {
    return new EllipticCurvePoint(x, y, z, this);
  }

  /** The value of the homogeneous equation at (x : y : z) (zero on the curve). */
  private value(x: Elt, y: Elt, z: Elt): Elt {
    const D = this.dom;
    const t = [D.mul(D.pow(y, 2), z), D.mul(D.mul(D.mul(this.a1, x), y), z), D.mul(D.mul(this.a3, y), D.pow(z, 2))];
    const u = [D.pow(x, 3), D.mul(D.mul(this.a2, D.pow(x, 2)), z), D.mul(D.mul(this.a4, x), D.pow(z, 2)), D.mul(this.a6, D.pow(z, 3))];
    return D.sub(t.reduce((s, v) => D.add(s, v)), u.reduce((s, v) => D.add(s, v)));
  }

  /** SymPy `point in curve`: a point, or the coordinates [x, y] or [x, y, z]. */
  has(point: EllipticCurvePoint | readonly ElementLike[]): boolean {
    if (point instanceof EllipticCurvePoint) return this.hasElts(point.ex, point.ey, point.ez);
    if (point.length < 2) throw new RangeError('Invalid point.');
    const D = this.dom;
    return this.hasElts(D.conv(at(point, 0)), D.conv(at(point, 1)), D.conv(point[2] ?? 1));
  }

  /** @internal */
  hasElts(x: Elt, y: Elt, z: Elt): boolean {
    if (this.characteristic === 0n && this.dom.isZero(z)) return true;
    return this.dom.isZero(this.value(x, y, z));
  }

  /** SymPy's repr: the homogeneous polynomial `y**2*z + a1*x*y*z + a3*y*z**2 - x**3 - ...` as a Poly. */
  toString(): string {
    const D = this.dom;
    const c = (e: Elt, sign: bigint): Rational => D.toSympy(D.k(sign, e));
    const terms: [Rational, [number, number, number]][] = [
      [Rational.of(1n), [0, 2, 1]],
      [c(this.a1, 1n), [1, 1, 1]],
      [c(this.a3, 1n), [0, 1, 2]],
      [D.toSympy(D.of(-1n)), [3, 0, 0]],
      [c(this.a2, -1n), [2, 0, 1]],
      [c(this.a4, -1n), [1, 0, 2]],
      [c(this.a6, -1n), [0, 0, 3]],
    ];
    return polyString(terms, this.modulus ? `modulus=${this.modulus}` : "domain='QQ'");
  }

  /** SymPy minimal(): the minimal Weierstrass equation. */
  minimal(): EllipticCurve {
    const D = this.dom;
    const char = this.characteristic;
    const R = (e: Elt): Rational => Rational.of(e.n, e.d);
    if (char === 2n) return this;
    if (char === 3n) return new EllipticCurve(R(D.div(this.b4, D.of(2n))), R(D.div(this.b6, D.of(4n))), 0, R(D.div(this.b2, D.of(4n))), 0, this.modulus);
    const c4 = D.sub(D.pow(this.b2, 2), D.k(24n, this.b4));
    const c6 = D.add(D.add(D.neg(D.pow(this.b2, 3)), D.k(36n, D.mul(this.b2, this.b4))), D.k(-216n, this.b6));
    return new EllipticCurve(R(D.k(-27n, c4)), R(D.k(-54n, c6)), 0, 0, 0, this.modulus);
  }

  /** The solutions y in GF(p) of the curve equation at x (SymPy polynomial_congruence). */
  private congruence(x: Elt): bigint[] {
    const D = this.dom;
    const y = new Sym('y');
    const lin = D.toSympy(D.add(D.mul(this.a1, x), this.a3));
    const cst = D.toSympy(D.neg([D.pow(x, 3), D.mul(this.a2, D.pow(x, 2)), D.mul(this.a4, x), this.a6].reduce((s, v) => D.add(s, v))));
    return polynomialCongruence(add(pow(y, 2), mul(lin, y), cst), this.modulus);
  }

  /** SymPy points(): the affine points of a curve over GF(p), as (x, y) tuples. */
  points(): Set<TupleNode> {
    const char = this.characteristic;
    if (char < 1n) throw new RangeError('Infinitely many points');
    const all = new Set<TupleNode>();
    for (let i = 0n; i < char; i++) {
      for (const n of this.congruence(this.dom.of(i))) all.add(new TupleNode([Rational.of(i), Rational.of(n)]));
    }
    return all;
  }

  /**
   * SymPy points_x(x): the affine points with this x-coordinate. Over Q, the rational points (SymPy
   * returns the raw solutions of its polynomial in y and z there).
   */
  pointsX(x: ElementLike): TupleNode[] {
    const D = this.dom;
    const ex = D.conv(x);
    const X = D.toSympy(ex);
    if (this.modulus) return this.congruence(ex).map((y) => new TupleNode([X, Rational.of(y)]));
    // y**2 + b*y - c = 0 with b = a1*x + a3, c = x**3 + a2*x**2 + a4*x + a6: y = (-b +- sqrt(b**2 + 4*c))/2
    const b = D.add(D.mul(this.a1, ex), this.a3);
    const c = [D.pow(ex, 3), D.mul(this.a2, D.pow(ex, 2)), D.mul(this.a4, ex), this.a6].reduce((s, v) => D.add(s, v));
    const disc = D.add(D.pow(b, 2), D.k(4n, c));
    const r = rationalSqrt(disc);
    if (r === undefined) return [];
    const ys = D.isZero(r) ? [r] : [D.neg(r), r];
    return ys.map((s) => new TupleNode([X, D.toSympy(D.div(D.sub(s, b), D.of(2n)))]));
  }

  /**
   * SymPy torsion_points(): the points of finite order of a curve over Q (Nagell-Lutz: y = 0 or y**2
   * divides the discriminant), the point at infinity first.
   */
  torsionPoints(): EllipticCurvePoint[] {
    if (this.characteristic > 0n) throw new RangeError('No torsion point for Finite Field.');
    const D = this.dom;
    const l = [EllipticCurvePoint.pointAtInfinity(this)];
    // the rational roots x of x**3 + a2*x**2 + (a4 - a1*j)*x + (a6 - j**2 - a3*j)
    const roots = (j: Elt): Elt[] =>
      rationalRoots([D.of(1n), this.a2, D.sub(this.a4, D.mul(this.a1, j)), D.sub(D.sub(this.a6, D.pow(j, 2)), D.mul(this.a3, j))]);
    for (const xx of roots(D.of(0n))) l.push(this.call(D.toSympy(xx), 0));
    for (const i of divisors(this.discriminant)) {
      const j = isqrt(i);
      if (j * j !== i) continue;
      for (const xx of roots(D.of(j))) {
        const p = this.call(D.toSympy(xx), j);
        if (p.order() !== S.Infinity) l.push(p, p.neg());
      }
    }
    return l;
  }

  /** SymPy characteristic: 0 over Q, p over GF(p). */
  get characteristic(): bigint {
    return this.modulus;
  }

  /** SymPy discriminant (over GF(p), its residue in [0, p)). */
  get discriminant(): bigint {
    return this.discrim.n / this.discrim.d;
  }

  /** SymPy is_singular: the discriminant is zero. */
  get isSingular(): boolean {
    return this.discriminant === 0n;
  }

  /** SymPy j_invariant: c4**3/discriminant. */
  get jInvariant(): Rational {
    const D = this.dom;
    const c4 = D.sub(D.pow(this.b2, 2), D.k(24n, this.b4));
    return D.toSympy(D.div(D.pow(c4, 3), this.discrim));
  }

  /** SymPy order: the number of affine points of a curve over GF(p). */
  get order(): number {
    if (this.characteristic === 0n) throw new NotImplementedError('Still not implemented');
    return this.points().size;
  }

  /** SymPy rank: 0 over a finite field (not implemented over Q). */
  get rank(): number {
    if (this.modulus) return 0;
    throw new NotImplementedError('Still not implemented');
  }
}

const isqrt = (n: bigint): bigint => {
  if (n < 2n) return n;
  // Newton's iteration from above
  let x = n;
  let y = (x + 1n) / 2n;
  while (y < x) [x, y] = [y, (y + n / y) / 2n];
  return x;
};

/** The square root of a nonnegative rational square, or undefined. */
function rationalSqrt(a: Elt): Elt | undefined {
  if (a.n < 0n) return undefined;
  const [p, q] = [isqrt(a.n), isqrt(a.d)];
  return p * p === a.n && q * q === a.d ? { n: p, d: q } : undefined;
}

/** The distinct rational roots, increasing, of the monic cubic with rational coefficients [1, b, c, d]. */
function rationalRoots(cs: readonly Elt[]): Elt[] {
  const Q = new Domain(0n);
  // clear denominators: an integer polynomial whose rational roots p/q have p | a0 and q | lead
  const l = cs.reduce((m, c) => (m * c.d) / gcdB(m, c.d), 1n);
  const ints = cs.map((c) => (c.n * l) / c.d);
  const evalAt = (r: Elt): Elt => cs.reduce((s, c) => Q.add(Q.mul(s, r), c), Q.of(0n));
  const out: Elt[] = [];
  const lead = first(ints);
  let a0 = last(ints);
  let k = 0;
  // zero roots
  if (a0 === 0n) {
    out.push(Q.of(0n));
    for (k = ints.length - 1; k > 0 && ints[k] === 0n; k--);
    a0 = at(ints, k);
  }
  for (const p of divisors(absB(a0))) {
    for (const q of divisors(absB(lead))) {
      for (const s of [-1n, 1n]) {
        const r = Q.of(s * p, q);
        if (Q.isZero(evalAt(r)) && !out.some((o) => Q.eq(o, r))) out.push(r);
      }
    }
  }
  return out.sort((a, b) => (a.n * b.d < b.n * a.d ? -1 : 1));
}

/** A point (x : y : z) of an elliptic curve; z = 0 is the point at infinity O (SymPy EllipticCurvePoint). */
export class EllipticCurvePoint {
  /** @internal */ readonly ex: Elt;
  /** @internal */ readonly ey: Elt;
  /** @internal */ readonly ez: Elt;

  /** SymPy point_at_infinity(curve): O = (0 : 1 : 0). */
  static pointAtInfinity(curve: EllipticCurve): EllipticCurvePoint {
    return new EllipticCurvePoint(0, 1, 0, curve);
  }

  constructor(
    x: ElementLike,
    y: ElementLike,
    z: ElementLike,
    readonly curve: EllipticCurve,
  ) {
    const D = curve.dom;
    [this.ex, this.ey, this.ez] = [D.conv(x), D.conv(y), D.conv(z)];
    if (!curve.hasElts(this.ex, this.ey, this.ez)) throw new RangeError('The curve does not contain this point');
  }

  private static of(x: Elt, y: Elt, z: Elt, curve: EllipticCurve): EllipticCurvePoint {
    const r = (e: Elt): Rational => Rational.of(e.n, e.d);
    return new EllipticCurvePoint(r(x), r(y), r(z), curve);
  }

  /** The affine coordinates as SymPy numbers (x, y). */
  get x(): Rational {
    return this.curve.dom.toSympy(this.ex);
  }
  get y(): Rational {
    return this.curve.dom.toSympy(this.ey);
  }
  get z(): Rational {
    return this.curve.dom.toSympy(this.ez);
  }

  /** The group law (SymPy `self + p`). */
  add(p: EllipticCurvePoint): EllipticCurvePoint {
    const c = this.curve;
    const D = c.dom;
    if (D.isZero(this.ez)) return p;
    if (D.isZero(p.ez)) return this;
    const [x1, y1] = [D.div(this.ex, this.ez), D.div(this.ey, this.ez)];
    const [x2, y2] = [D.div(p.ex, p.ez), D.div(p.ey, p.ez)];
    const { a1, a2, a3, a4, a6 } = c;
    let slope: Elt;
    let yint: Elt;
    if (!D.eq(x1, x2)) {
      slope = D.div(D.sub(y1, y2), D.sub(x1, x2));
      yint = D.div(D.sub(D.mul(y1, x2), D.mul(y2, x1)), D.sub(x2, x1));
    } else {
      if (D.isZero(D.add(y1, y2))) return EllipticCurvePoint.pointAtInfinity(c);
      const den = D.add(D.add(D.mul(a1, x1), a3), D.k(2n, y1));
      slope = D.div([D.k(3n, D.pow(x1, 2)), D.k(2n, D.mul(a2, x1)), a4, D.neg(D.mul(a1, y1))].reduce((s, v) => D.add(s, v)), den);
      yint = D.div([D.neg(D.pow(x1, 3)), D.mul(a4, x1), D.k(2n, a6), D.neg(D.mul(a3, y1))].reduce((s, v) => D.add(s, v)), den);
    }
    const x3 = [D.pow(slope, 2), D.mul(a1, slope), D.neg(a2), D.neg(x1), D.neg(x2)].reduce((s, v) => D.add(s, v));
    const y3 = D.sub(D.sub(D.neg(D.mul(D.add(slope, a1), x3)), yint), a3);
    return EllipticCurvePoint.of(x3, y3, D.of(1n), c);
  }

  /** SymPy `-self`. */
  neg(): EllipticCurvePoint {
    const D = this.curve.dom;
    return EllipticCurvePoint.of(this.ex, D.sub(D.sub(D.neg(this.ey), D.mul(this.curve.a1, this.ex)), this.curve.a3), this.ez, this.curve);
  }

  /** SymPy `self - other`. */
  sub(other: EllipticCurvePoint): EllipticCurvePoint {
    return this.add(other.neg());
  }

  /** SymPy `self * n` (and `n * self`): the n-th multiple by double-and-add. */
  mul(nIn: number | bigint): EllipticCurvePoint {
    let n = BigInt(nIn);
    let r = EllipticCurvePoint.pointAtInfinity(this.curve);
    if (n === 0n) return r;
    if (n < 0n) return this.neg().mul(-n);
    let p: EllipticCurvePoint = this;
    while (n) {
      if (n & 1n) r = r.add(p);
      n >>= 1n;
      p = p.add(p);
    }
    return r;
  }

  /** Whether the two points have the same projective coordinates (SymPy compares the coordinate tuples). */
  equals(other: EllipticCurvePoint): boolean {
    const D = this.curve.dom;
    return D.eq(this.ex, other.ex) && D.eq(this.ey, other.ey) && D.eq(this.ez, other.ez);
  }

  /** SymPy order(): the least n with n*P = O, or oo (over Q, oo once the multiples stop being integral). */
  order(): Expr {
    const D = this.curve.dom;
    if (D.isZero(this.ez)) return S.One;
    if (D.isZero(this.ey)) return Rational.of(2n);
    let p = this.mul(2);
    if (D.eq(p.ey, D.neg(this.ey))) return Rational.of(3n);
    let i = 2;
    const integral = (q: EllipticCurvePoint): boolean => q.ex.d === 1n && q.ey.d === 1n;
    // over Q a point of finite order has order at most 12 (Mazur)
    while (integral(p) && (this.curve.modulus !== 0n || i <= 12)) {
      p = this.add(p);
      i++;
      if (D.isZero(p.ez)) return Rational.of(BigInt(i));
    }
    return S.Infinity;
  }

  /** SymPy's repr: `(x, y)`, or `O` for the point at infinity. */
  toString(): string {
    if (this.curve.dom.isZero(this.ez)) return 'O';
    return `(${this.x.toString()}, ${this.y.toString()})`;
  }
}
