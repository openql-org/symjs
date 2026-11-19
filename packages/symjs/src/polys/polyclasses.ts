// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/polyclasses.py: ANP, DMP_Python),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Dense recursive polynomials and elements of algebraic number fields.
 * SymPy ANP is a polynomial in
 * the primitive element theta with rational coefficients, reduced modulo the
 * minimal polynomial of theta. An element prints as
 * `ANP([MPQ(1,1), MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)`.
 */

import { DomainError, NotInvertible } from '../core/errors';
import { at, defined, first } from '../core/guard';
import { CoercionFailed, QQ, groundRational, domainArith, domainNeg } from './domains';
import type { Domain } from './domains';
import { UnificationFailed } from './polyerrors';
import { PythonMPQ } from './domains/pythonrational';

import { dmpFromDict, dmpValidate, dmpNormal, dmpConvert, dmpGround, dmpCopy, dmpToDict, dmpZeroP, dmpOneP, dmpDegreeIn, dmpDegreeList, dmpGroundLC, dmpGroundTC, dmpGroundNth, dmpZero, dmpExclude, groundEquals } from './densebasic';
import type { DensePoly } from './densebasic';
import { dmpAbs, dmpNeg, dmpAdd, dmpSub, dmpMul, dmpSqr, dmpPow, dmpMulGround, dmpQuoGround, dmpExquoGround, dmpDiv, dmpExquo, dmpPdiv, dmpPexquo, dmpMaxNorm, dmpL1Norm } from './densearith';
import type * as DenseTools from './densetools';

/** Advanced dense operations registered by the densetools module. */
export const dmpTools: Partial<Pick<typeof DenseTools, 'dmpDiffIn' | 'dmpEvalIn' | 'dmpGroundMonic' | 'dmpGroundContent' | 'dmpGroundPrimitive' | 'dmpGroundTrunc' | 'dmpCompose' | 'dupDecompose' | 'dmpClearDenoms'>> = {};

import { heuGcd } from './euclidtools';

type QP = PythonMPQ[];
const ZERO = new PythonMPQ(0n);
const ONE = new PythonMPQ(1n);

const strip = (f: readonly PythonMPQ[]): QP => {
  let i = 0;
  while (i < f.length && at(f, i).isZero) i++;
  return f.slice(i);
};
function polyAdd(f: QP, g: QP): QP {
  const n = Math.max(f.length, g.length);
  const pad = (h: QP): QP => [...Array.from({ length: n - h.length }, () => ZERO), ...h];
  const [F, G] = [pad(f), pad(g)];
  return strip(F.map((c, i) => c.add(at(G, i))));
}
function polyMul(f: QP, g: QP): QP {
  if (!f.length || !g.length) return [];
  const out: QP = Array.from({ length: f.length + g.length - 1 }, () => ZERO);
  f.forEach((a, i) => g.forEach((b, j) => (out[i + j] = at(out, i + j).add(a.mul(b)))));
  return strip(out);
}
/** [quotient, remainder] of f by a nonzero g. */
function polyDivmod(f: QP, g: QP): [QP, QP] {
  const r = [...f];
  const dg = g.length - 1;
  if (r.length - 1 < dg) return [[], strip(r)];
  const qq: QP = [];
  const lc = first(g);
  for (let i = 0; i <= f.length - 1 - dg; i++) {
    const c = at(r, i).div(lc);
    qq.push(c);
    for (let j = 0; j <= dg; j++) r[i + j] = at(r, i + j).sub(c.mul(at(g, j)));
  }
  return [strip(qq), strip(r.slice(f.length - dg))];
}
/** The inverse of f modulo m (SymPy dup_invert); throws NotInvertible. */
function polyInvert(f: QP, m: QP): QP {
  let [r0, r1, s0, s1]: [QP, QP, QP, QP] = [m, polyDivmod(f, m)[1], [], [ONE]];
  while (r1.length) {
    const [qq, r] = polyDivmod(r0, r1);
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, polyAdd(s0, polyMul(qq, s1).map((c) => c.neg()))];
  }
  if (r0.length !== 1) throw new NotInvertible('zero divisor');
  const c = first(r0);
  return s0.map((a) => a.div(c));
}

/** An element of an algebraic number field: a polynomial in the primitive element modulo its minimal polynomial (SymPy ANP). */
export class ANP {
  readonly rep: QP;
  readonly mod: QP;
  constructor(
    rep: unknown,
    mod: readonly unknown[],
    readonly dom: Domain = QQ,
  ) {
    const conv = (a: unknown): PythonMPQ => QQ.convert(a);
    this.rep = strip(Array.isArray(rep) ? (rep as unknown[]).map(conv) : [conv(rep)]);
    this.mod = strip(mod.map(conv));
  }
  private per(rep: QP): ANP {
    return new ANP(polyDivmod(rep, this.mod)[1], this.mod, this.dom);
  }
  private repOf(o: unknown): QP {
    if (o instanceof ANP) {
      if (o.mod.length !== this.mod.length || o.mod.some((c, i) => !c.equals(this.mod[i]))) throw new CoercionFailed('cannot unify algebraic numbers of different fields');
      return o.rep;
    }
    return strip([QQ.convert(o)]);
  }
  get isOne(): boolean {
    return this.rep.length === 1 && this.LC().equals(1);
  }
  get isZero(): boolean {
    return this.rep.length === 0;
  }
  /** The coefficients, highest first (SymPy to_list). */
  toList(): PythonMPQ[] {
    return [...this.rep];
  }
  /** The defining polynomial coefficients (SymPy mod_to_list). */
  modToList(): PythonMPQ[] {
    return [...this.mod];
  }
  /** Representations over a common ground domain (SymPy unify). */
  unify(o: ANP): [Domain, (rep: QP) => ANP, QP, QP, QP] {
    if (this.mod.length !== o.mod.length || this.mod.some((c, i) => !c.equals(o.mod[i]))) throw new UnificationFailed('cannot unify algebraic numbers of different fields');
    const dom = this.dom.unify(o.dom);
    return [dom, (rep) => new ANP(rep, this.mod, dom), [...this.rep], [...o.rep], [...this.mod]];
  }
  /** The leading coefficient (SymPy LC). */
  LC(): PythonMPQ {
    return this.rep[0] ?? ZERO;
  }
  add(o: unknown): ANP {
    return this.per(polyAdd(this.rep, this.repOf(o)));
  }
  sub(o: unknown): ANP {
    return this.per(polyAdd(this.rep, this.repOf(o).map((c) => c.neg())));
  }
  mul(o: unknown): ANP {
    return this.per(polyMul(this.rep, this.repOf(o)));
  }
  neg(): ANP {
    return this.per(this.rep.map((c) => c.neg()));
  }
  /** this/o; throws NotInvertible for o = 0. */
  div(o: unknown): ANP {
    return this.per(polyMul(this.rep, polyInvert(this.repOf(o), this.mod)));
  }
  /** The field quotient (SymPy quo). */
  quo(o: unknown): ANP {
    return this.div(o);
  }
  /** The field remainder; division by a zero divisor is undefined. */
  rem(o: unknown): ANP {
    this.div(o);
    return this.per([]);
  }
  /** The field quotient and zero remainder (SymPy div). */
  divmod(o: unknown): [ANP, ANP] {
    return [this.div(o), this.per([])];
  }
  /** this**n (a negative n inverts). */
  pow(n: number): ANP {
    let [r, b] = [this.per([ONE]), n < 0 ? this.per(polyInvert(this.rep, this.mod)) : this];
    for (let k = Math.abs(n); k; k >>= 1) {
      if (k & 1) r = r.mul(b);
      b = b.mul(b);
    }
    return r;
  }
  equals(o: unknown): boolean {
    if (!(o instanceof ANP)) return this.rep.length <= 1 && groundRational(o) !== undefined && this.LC().equals(QQ.convert(o));
    return o.rep.length === this.rep.length && o.rep.every((c, i) => c.equals(this.rep[i])) && o.mod.length === this.mod.length && o.mod.every((c, i) => c.equals(this.mod[i]));
  }
  /** SymPy repr(a), which is also its str. */
  toString(): string {
    const list = (f: QP): string => `[${f.map((c) => c.repr()).join(', ')}]`;
    return `ANP(${list(this.rep)}, ${list(this.mod)}, ${this.dom.toString()})`;
  }
  repr(): string {
    return this.toString();
  }
}

/** Dense recursive polynomials over a ground domain (SymPy DMP_Python). */
export class DMPJs {
  readonly rep: unknown[];
  readonly lev: number;
  constructor(rep: DensePoly, readonly dom: Domain, lev?: number) {
    const [normal, level] = dmpValidate(rep);
    this.lev = lev ?? level;
    if (this.lev !== level) throw new RangeError('inconsistent polynomial level');
    this.rep = dmpNormal(normal, this.lev, dom);
  }
  private per(rep: DensePoly): DMPJs { return new DMPJs(rep, this.dom, this.lev); }
  private operand(other: unknown): DMPJs {
    if (other instanceof DMPJs) {
      if (other.lev !== this.lev) throw new UnificationFailed('cannot unify different polynomial levels');
      return new DMPJs(dmpConvert(other.rep, this.lev, other.dom, this.dom), this.dom, this.lev);
    }
    return this.per(denseList(dmpGround(this.dom.convert(other), this.lev)));
  }
  toList(): unknown[] { return dmpCopy(this.rep, this.lev); }
  toDict(): Map<number[], unknown> { return dmpToDict(this.rep, this.lev); }
  toSympyDict(): Map<number[], unknown> { return new Map([...this.toDict()].map(([m, c]) => [m, this.dom.toSympy(c)])); }
  get isZero(): boolean { return dmpZeroP(this.rep, this.lev); }
  get isOne(): boolean { return dmpOneP(this.rep, this.lev, this.dom); }
  get isGround(): boolean { return this.toDict().size === 0 || [...this.toDict().keys()].every((m) => m.every((e) => e === 0)); }
  get isMonic(): boolean { return this.dom.isOne(this.LC()); }
  get isPrimitive(): boolean { return this.dom.isOne(this.content()); }
  get isSqf(): boolean {
    let g: DMPJs = this;
    for (let j = 0; j <= this.lev; j++) g = g.gcd(this.diff(1, j));
    return !this.isZero && g.isGround;
  }
  degree(j = 0): number { return dmpDegreeIn(this.rep, j, this.lev); }
  degreeList(): number[] { return dmpDegreeList(this.rep, this.lev); }
  totalDegree(): number { return Math.max(0, ...[...this.toDict().keys()].map((m) => m.reduce((a, b) => a + b, 0))); }
  LC(): unknown { return dmpGroundLC(this.rep, this.lev, this.dom); }
  TC(): unknown { return dmpGroundTC(this.rep, this.lev, this.dom); }
  nth(...N: number[]): unknown { return dmpGroundNth(this.rep, N, this.lev, this.dom); }
  maxNorm(): unknown { return dmpMaxNorm(this.rep, this.lev, this.dom); }
  l1Norm(): unknown { return dmpL1Norm(this.rep, this.lev, this.dom); }
  abs(): DMPJs { return this.per(dmpAbs(this.rep, this.lev, this.dom)); }
  neg(): DMPJs { return this.per(dmpNeg(this.rep, this.lev, this.dom)); }
  add(other: unknown): DMPJs { return this.per(dmpAdd(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  sub(other: unknown): DMPJs { return this.per(dmpSub(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  mul(other: unknown): DMPJs { return this.per(dmpMul(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  sqr(): DMPJs { return this.per(dmpSqr(this.rep, this.lev, this.dom)); }
  pow(n: number): DMPJs {
    if (!Number.isInteger(n)) throw new TypeError('polynomial exponent must be an integer');
    return this.per(dmpPow(this.rep, n, this.lev, this.dom));
  }
  mulGround(c: unknown): DMPJs { return this.per(dmpMulGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  quoGround(c: unknown): DMPJs { return this.per(dmpQuoGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  exquoGround(c: unknown): DMPJs { return this.per(dmpExquoGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  div(other: unknown): [DMPJs, DMPJs] { const [q, r] = dmpDiv(this.rep, this.operand(other).rep, this.lev, this.dom); return [this.per(q), this.per(r)]; }
  quo(other: unknown): DMPJs { return this.div(other)[0]; }
  rem(other: unknown): DMPJs { return this.div(other)[1]; }
  exquo(other: unknown): DMPJs { return this.per(dmpExquo(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  pdiv(other: unknown): [DMPJs, DMPJs] { const [q, r] = dmpPdiv(this.rep, this.operand(other).rep, this.lev, this.dom); return [this.per(q), this.per(r)]; }
  pquo(other: unknown): DMPJs { return this.pdiv(other)[0]; }
  prem(other: unknown): DMPJs { return this.pdiv(other)[1]; }
  pexquo(other: unknown): DMPJs { return this.per(dmpPexquo(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  diff(m = 1, j = 0): DMPJs {
    if (!Number.isInteger(m) || !Number.isInteger(j)) throw new TypeError('derivative order and generator index must be integers');
    return this.per(defined(dmpTools.dmpDiffIn, 'dense polynomial tools')(this.rep, m, j, this.lev, this.dom));
  }
  eval(a: unknown, j = 0): unknown {
    const r = defined(dmpTools.dmpEvalIn, 'dense polynomial tools')(this.rep, this.dom.convert(a), j, this.lev, this.dom);
    return this.lev === 0 ? r : new DMPJs(denseList(r), this.dom, this.lev - 1);
  }
  monic(): DMPJs { return this.per(defined(dmpTools.dmpGroundMonic, 'dense polynomial tools')(this.rep, this.lev, this.dom)); }
  content(): unknown { return defined(dmpTools.dmpGroundContent, 'dense polynomial tools')(this.rep, this.lev, this.dom); }
  primitive(): [unknown, DMPJs] { const [c, p] = defined(dmpTools.dmpGroundPrimitive, 'dense polynomial tools')(this.rep, this.lev, this.dom); return [c, this.per(p)]; }
  trunc(p: unknown): DMPJs { return this.per(defined(dmpTools.dmpGroundTrunc, 'dense polynomial tools')(this.rep, this.dom.convert(p), this.lev, this.dom)); }
  compose(g: DMPJs): DMPJs { return this.per(defined(dmpTools.dmpCompose, 'dense polynomial tools')(this.rep, this.operand(g).rep, this.lev, this.dom)); }
  decompose(): DMPJs[] { this.univariate(); return defined(dmpTools.dupDecompose, 'dense polynomial tools')(this.rep, this.dom).map((p) => this.per(p)); }
  private univariate(): void { if (this.lev !== 0) throw new RangeError('univariate polynomial expected'); }
  /** Primitive polynomial remainder sequence over recursively polynomial coefficients. */
  gcd(other: unknown): DMPJs {
    let [a, b]: [DMPJs, DMPJs] = [this, this.operand(other)];
    if (a.isZero) return b.normalized();
    if (b.isZero) return a.normalized();
    if (this.dom.toString() === 'ZZ') {
      const terms = (p: DMPJs): Map<string, { e: readonly number[]; c: bigint }> => new Map([...p.toDict()].map(([e, c]) => [e.join(','), { e, c: BigInt(String(c)) }]));
      const candidate = heuGcd(terms(a), terms(b), this.lev + 1);
      if (candidate !== undefined) return this.per(dmpFromDict(new Map([...candidate[0].values()].map(({ e, c }) => [e, c])), this.lev, this.dom));
    }
    if (this.lev === 0) {
      const c = this.dom.isField ? this.dom.one : this.dom.gcd(a.content(), b.content());
      [a, b] = [a.primitive()[1], b.primitive()[1]];
      while (!b.isZero) [a, b] = [b, a.prem(b).primitive()[1]];
      return (this.dom.isField ? a.monic() : a.normalized()).mulGround(c);
    }
    const coefficientContent = (p: DMPJs): DMPJs => p.rep.map((c) => new DMPJs(denseList(c), p.dom, p.lev - 1)).reduce((g, c) => g.gcd(c));
    const primitive = (p: DMPJs): DMPJs => {
      if (p.isZero) return p;
      const c = coefficientContent(p);
      return p.per(p.rep.map((a) => new DMPJs(denseList(a), p.dom, p.lev - 1).exquo(c).rep));
    };
    const c = coefficientContent(a).gcd(coefficientContent(b));
    [a, b] = [primitive(a), primitive(b)];
    while (!b.isZero) [a, b] = [b, primitive(a.prem(b))];
    const h = primitive(a).mul(this.per([c.rep]));
    return this.dom.isField ? h.monic() : h.normalized();
  }
  private normalized(): DMPJs { return this.dom.isNegative(this.LC()) ? this.neg() : this; }
  lcm(other: unknown): DMPJs {
    const b = this.operand(other);
    if (this.isZero || b.isZero) return this.per(dmpZero(this.lev));
    const h = this.mul(b).exquo(this.gcd(b));
    return this.dom.isField ? h.monic() : h.normalized();
  }
  cofactors(other: unknown): [DMPJs, DMPJs, DMPJs] {
    const b = this.operand(other), h = this.gcd(b);
    return h.isZero ? [h, h, h] : [h, this.exquo(h), b.exquo(h)];
  }
  gcdex(other: unknown, auto = true): [DMPJs, DMPJs, DMPJs] {
    this.univariate();
    if (!auto && !this.dom.isField) throw new DomainError('Cannot compute extended GCD over a ring');
    const K = this.dom.getField();
    let a = new DMPJs(dmpConvert(this.rep, 0, this.dom, K), K);
    let b = new DMPJs(dmpConvert(this.operand(other).rep, 0, this.dom, K), K);
    let [s0, s1, t0, t1] = [a.operand(1), a.operand(0), a.operand(0), a.operand(1)];
    while (!b.isZero) {
      const [q, r] = a.div(b);
      [a, b, s0, s1, t0, t1] = [b, r, s1, s0.sub(q.mul(s1)), t1, t0.sub(q.mul(t1))];
    }
    const c = a.LC();
    return [s0.quoGround(c), t0.quoGround(c), a.monic()];
  }
  halfGcdex(other: unknown, auto = true): [DMPJs, DMPJs] { const [s, , h] = this.gcdex(other, auto); return [s, h]; }
  invert(other: unknown, auto = true): DMPJs {
    const [s, h] = this.halfGcdex(other, auto);
    if (!h.isOne) throw new NotInvertible('zero divisor');
    return s.rem(other);
  }
  sturm(): DMPJs[] {
    this.univariate();
    const K = this.dom.getField();
    const f = new DMPJs(dmpConvert(this.sqfPart().rep, 0, this.dom, K), K);
    const out = [f, f.diff()];
    while (!at(out, out.length - 1).isZero) out.push(at(out, out.length - 2).rem(at(out, out.length - 1)).neg());
    return out.slice(0, -1);
  }
  sqfPart(): DMPJs {
    if (this.isZero) return this;
    let h: DMPJs = this;
    for (let j = 0; j <= this.lev; j++) h = h.gcd(this.diff(1, j));
    const p = this.exquo(h);
    return this.dom.isField ? p.monic() : p.normalized().primitive()[1];
  }
  sqfList(): [unknown, [DMPJs, number][]] {
    if (this.isZero) return [this.dom.zero, []];
    const c = this.dom.isField ? this.LC() : this.dom.isNegative(this.LC()) ? domainNeg(this.dom, this.content()) : this.content();
    const f = this.exquoGround(c);
    let g: DMPJs = f;
    for (let j = 0; j <= this.lev; j++) g = g.gcd(f.diff(1, j));
    let w = f.exquo(g), i = 1;
    const factors: [DMPJs, number][] = [];
    while (!w.isOne) {
      const y = w.gcd(g), z = w.exquo(y);
      if (!z.isOne) factors.push([z, i]);
      [w, g] = [y, g.exquo(y)];
      i++;
    }
    return [c, factors];
  }
  /** Subresultant PRS with recursive coefficient arithmetic (SymPy dmp_inner_subresultants). */
  private innerSubresultants(other: unknown): [DMPJs[], DMPJs[]] {
    let [f, g]: [DMPJs, DMPJs] = [this, this.operand(other)];
    if (f.degree() < g.degree()) [f, g] = [g, f];
    const coefficient = (p: DMPJs): DMPJs => new DMPJs(p.lev === 0 ? [p.LC()] : denseList(first(p.rep)), p.dom, Math.max(0, p.lev - 1));
    const one = coefficient(g).operand(1);
    if (f.isZero) return [[], []];
    if (g.isZero) return [[f], [one]];
    const times = (p: DMPJs, c: DMPJs): DMPJs => p.lev === 0 ? p.mulGround(c.LC()) : p.mul(p.per([c.rep]));
    const quotient = (p: DMPJs, c: DMPJs): DMPJs => p.lev === 0 ? p.exquoGround(c.LC()) : p.per(p.rep.map((a) => new DMPJs(denseList(a), p.dom, p.lev - 1).exquo(c).rep));
    const R = [f, g];
    let m = g.degree(), d = f.degree() - m;
    let h = times(f.prem(g), one.neg().pow(d + 1));
    let lc = coefficient(g), c = lc.pow(d);
    const S = [one, c];
    c = c.neg();
    while (!h.isZero) {
      const k = h.degree();
      R.push(h);
      [f, g, m, d] = [g, h, k, m - k];
      const b = lc.neg().mul(c.pow(d));
      h = quotient(f.prem(g), b);
      lc = coefficient(g);
      c = d > 1 ? lc.neg().pow(d).exquo(c.pow(d - 1)) : lc.neg();
      S.push(c.neg());
    }
    return [R, S];
  }
  subresultants(other: unknown): DMPJs[] { return this.innerSubresultants(other)[0]; }
  resultant(other: unknown): unknown {
    const [R, S] = this.innerSubresultants(other);
    const r = R.length === 0 || at(R, R.length - 1).degree() > 0 ? new DMPJs(dmpZero(Math.max(0, this.lev - 1)), this.dom) : at(S, S.length - 1);
    const sign = this.degree() < this.operand(other).degree() && this.degree() * this.operand(other).degree() % 2 !== 0 ? -1 : 1;
    const value = r.mulGround(sign);
    return this.lev === 0 ? value.LC() : value;
  }
  discriminant(): unknown {
    const n = this.degree();
    if (n <= 0) return this.lev === 0 ? this.dom.zero : new DMPJs(dmpZero(this.lev - 1), this.dom);
    const r = this.resultant(this.diff());
    const sign = (-1) ** (n * (n - 1) / 2);
    return r instanceof DMPJs ? r.mulGround(sign).exquo(new DMPJs(denseList(first(this.rep)), this.dom)) : domainArith(this.dom, 'quo', domainArith(this.dom, 'mul', r, this.dom.convert(sign)), this.LC());
  }
  cancelFraction(other: unknown): [unknown, DMPJs, DMPJs] {
    const [a, b, p, q] = this.cancel(other, false);
    return [domainArith(this.dom.getField(), 'quo', a, b), p, q];
  }
  cancel(other: unknown, include: false): [unknown, unknown, DMPJs, DMPJs];
  cancel(other: unknown, include?: true): [DMPJs, DMPJs];
  cancel(other: unknown, include = true): [DMPJs, DMPJs] | [unknown, unknown, DMPJs, DMPJs] {
    const b = this.operand(other);
    const [cp, fp] = defined(dmpTools.dmpClearDenoms, 'dense polynomial tools')(this.rep, this.lev, this.dom);
    const [cq, gp] = defined(dmpTools.dmpClearDenoms, 'dense polynomial tools')(b.rep, this.lev, this.dom);
    const K = this.dom.getRing();
    const [h, f0, g0] = new DMPJs(fp, K).cofactors(new DMPJs(gp, K));
    const f = this.per(dmpConvert(f0.rep, this.lev, K, this.dom));
    const g = this.per(dmpConvert(g0.rep, this.lev, K, this.dom));
    if (h.isZero) return include ? [f, g] : [this.dom.one, this.dom.one, f, g];
    const common = this.dom.gcd(this.dom.convert(cp), this.dom.convert(cq));
    let a = domainArith(this.dom, 'quo', this.dom.convert(cq), common);
    const c = domainArith(this.dom, 'quo', this.dom.convert(cp), common);
    let [p, q] = [f, g];
    if (this.dom.isNegative(p.LC())) { p = p.neg(); a = domainNeg(this.dom, a); }
    if (this.dom.isNegative(q.LC())) { q = q.neg(); a = domainNeg(this.dom, a); }
    return include ? [p.mulGround(a), q.mulGround(c)] : [a, c, p, q];
  }
  exclude(): [number[], DMPJs] { const [J, f, u] = dmpExclude(this.rep, this.lev, this.dom); return [J, new DMPJs(f, this.dom, u)]; }
  equals(other: unknown): boolean {
    if (!(other instanceof DMPJs) || this.lev !== other.lev) return false;
    const same = (a: unknown, b: unknown): boolean => Array.isArray(a) && Array.isArray(b) ? a.length === b.length && a.every((c, i) => same(c, b[i])) : groundEquals(a, b);
    return same(this.rep, other.rep);
  }
  toString(): string {
    const format = (c: unknown): string => Array.isArray(c) ? `[${c.map(format).join(', ')}]` : c instanceof PythonMPQ ? c.repr() : String(c);
    return `DMP_Python(${format(this.rep)}, ${String(this.dom)})`;
  }
}

function denseList(value: unknown): unknown[] {
  if (!Array.isArray(value)) throw new TypeError('dense polynomial coefficient must be a list');
  return value;
}
