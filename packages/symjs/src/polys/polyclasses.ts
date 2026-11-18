// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/polyclasses.py: ANP),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Elements of algebraic number fields (SymPy ANP): a polynomial in
 * the primitive element theta with rational coefficients, reduced modulo the
 * minimal polynomial of theta. An element prints as
 * `ANP([MPQ(1,1), MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)`.
 */

import { NotInvertible } from '../core/errors';
import { at, first } from '../core/guard';
import { CoercionFailed, QQ, groundRational } from './domains';
import type { Domain } from './domains';
import { UnificationFailed } from './polyerrors';
import { PythonMPQ } from './domains/pythonrational';

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
