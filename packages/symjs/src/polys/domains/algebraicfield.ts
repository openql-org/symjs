// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/algebraicfield.py, polys/polyclasses.py: ANP),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Algebraic number fields QQ<a> (SymPy AlgebraicField) and their
 * elements (SymPy ANP): a polynomial in the primitive element theta with
 * rational coefficients, reduced modulo the minimal polynomial of theta.
 * An element prints as `ANP([MPQ(1,1), MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)`.
 */

import { DomainError, NotInvertible } from '../../core/errors';
import { at, first } from '../../core/guard';
import type { ExprLike } from '../../core/nodes';
import { Dummy, Expr, Rational } from '../../core/nodes';
import { add, mul, pow, sympify } from '../../core/ops';
import { str } from '../../printing/str';
import { expand } from '../../simplify/expand';
import { CoercionFailed, Domain, QQ, domainHooks, groundRational } from '../domains';
import { AlgebraicNumber, minimalPolynomial } from '../numberfields';
import { toNumberField } from '../numberfields/subfield';
import { PythonMPQ } from './pythonrational';

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
  get isZero(): boolean {
    return this.rep.length === 0;
  }
  /** The coefficients, highest first (SymPy to_list). */
  toList(): PythonMPQ[] {
    return [...this.rep];
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
    return o.rep.length === this.rep.length && o.rep.every((c, i) => c.equals(this.rep[i])) && o.mod.length === this.mod.length;
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

/** An algebraic number field QQ<a, ...> (SymPy AlgebraicField). */
export class AlgebraicField extends Domain {
  readonly ground = 'EX' as const;
  readonly isField = true;
  /** The primitive element theta as an algebraic number (SymPy ext). */
  readonly ext: AlgebraicNumber;
  /** The extensions the field was made from (SymPy orig_ext). */
  readonly origExt: readonly Expr[];
  /** The minimal polynomial of theta, highest coefficient first (SymPy mod). */
  readonly mod: QP;
  private readonly baseDomain: Domain;
  constructor(dom: Domain, ...ext: (ExprLike | AlgebraicNumber)[]) {
    super();
    if (!dom.equals(QQ)) throw new DomainError('ground domain must be a rational field');
    this.baseDomain = dom;
    this.origExt = ext.map((e) => (e instanceof AlgebraicNumber ? e.asExpr() : sympify(e)));
    this.ext = toNumberField(ext.length === 1 ? first(ext) : ext);
    const t = new Dummy('t');
    this.mod = minimalPolynomial(this.ext.asExpr(), t, { polys: true })
      .allCoeffs()
      .map((c) => QQ.convert(c));
  }
  override get dom(): Domain {
    return this.baseDomain;
  }
  /** The ground domain QQ (SymPy domain). */
  get domain(): Domain {
    return this.baseDomain;
  }
  toString(): string {
    return `${this.baseDomain.toString()}<${str(this.ext.asExpr())}>`;
  }
  override equals(o: Domain): boolean {
    return o instanceof AlgebraicField && o.toString() === this.toString();
  }
  /** SymPy K(a) or K([c_n, ..., c_0]): the element with these coefficients in theta. */
  override new(...args: unknown[]): ANP {
    return new ANP(first(args), this.mod, this.baseDomain);
  }
  /** An element from a rational, an expression in the field or another element (SymPy convert); throws CoercionFailed. */
  override convert(a: unknown, base?: Domain): ANP {
    if (a instanceof ANP) return a;
    const v = base !== undefined && !base.equals(this) ? base.toSympy(a) : a;
    if (groundRational(v) !== undefined) return this.new([v]);
    if (!(v instanceof Expr)) throw new CoercionFailed(`cannot convert ${String(a)} to ${this.toString()}`);
    try {
      return this.new(toNumberField(v, this.ext).coeffs());
    } catch {
      throw new CoercionFailed(`${str(v)} is not a valid algebraic number in ${this.toString()}`);
    }
  }
  override ofType(a: unknown): boolean {
    return a instanceof ANP;
  }
  /** The element as an expression in the extension (SymPy to_sympy). */
  override toSympy(a: unknown): Expr {
    if (!(a instanceof ANP)) return super.toSympy(a);
    const theta = this.ext.asExpr();
    const n = a.rep.length - 1;
    return expand(add(...a.rep.map((c, i) => mul(Rational.of(c.numerator, c.denominator), pow(theta, n - i)))));
  }
  canon(e: Expr): Expr {
    return this.toSympy(this.convert(e));
  }
  fromSympy(e: ExprLike): Expr {
    return this.canon(sympify(e));
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    throw new DomainError(`there is no ring associated with ${this.toString()}`);
  }
  override isZero(a: unknown): boolean {
    return a instanceof ANP ? a.isZero : super.isZero(a);
  }
  /** The sign of the leading coefficient (SymPy is_positive). */
  override isPositive(a: unknown): boolean {
    return this.convert(a).LC().sign > 0;
  }
  override isNegative(a: unknown): boolean {
    return a instanceof ANP ? a.LC().sign < 0 : super.isNegative(a);
  }
  override div(a: unknown, b: unknown): [ANP, ANP] {
    return [this.exquo(a, b), this.new(0n)];
  }
  override exquo(a: unknown, b: unknown): ANP {
    return this.convert(a).div(this.convert(b));
  }
  override rem(_a: unknown, _b: unknown): ANP {
    return this.new(0n);
  }
  override gcd(a: unknown, b: unknown): ANP {
    return this.new(this.convert(a).isZero && this.convert(b).isZero ? 0n : 1n);
  }
  override lcm(a: unknown, b: unknown): ANP {
    return this.convert(a).mul(this.convert(b));
  }
  /** The field with more extensions (SymPy algebraic_field). */
  override algebraicField(...exts: ExprLike[]): Domain {
    return new AlgebraicField(this.baseDomain, ...this.origExt, ...exts);
  }
  /** The element as an algebraic number (SymPy to_alg_num). */
  toAlgNum(a: ANP): AlgebraicNumber {
    return new AlgebraicNumber(this.ext.asExpr(), a.rep.map((c) => Rational.of(c.numerator, c.denominator)));
  }
  /** The characteristic 0. */
  characteristic(): bigint {
    return 0n;
  }
}

domainHooks.algebraicField = (K, exts) => new AlgebraicField(K.getField(), ...exts);
