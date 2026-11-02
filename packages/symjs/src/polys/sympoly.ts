// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Poly: SymPy-compatible polynomial objects (generators, domain,
 * printing and the main polynomial API), plus top-level polynomial
 * functions (degree, LC/LM/LT, gcd, lcm, div, factor_list, ...).
 */

import { factorModP } from './zassenhaus';
import { Add, Constant, Expr, ExprLike, Float, Fn, Mul, Pow, Rational, S, Sym, impl, isNum } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, rebuild, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { integrate } from '../integrals/integrate';
import { str } from '../printing/str';
import { expandMul as expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { decomposePower, keepCoeff } from '../simplify/exprtools';
import { divExact, mfactorList, mgcd, mlcm, prem as mprem } from './mpoly';
import { CRootOf } from './rootof';
import { isolateRealRoots, refineRealRoot } from './rootisolation';
import { nroots } from './nroots';
import { UPoly, polyCoefficients, roots as rootsOf } from './poly';

export class PolificationFailed extends Error {}

// ---------------------------------------------------------------------------
// generators
// ---------------------------------------------------------------------------

const GENS_ORDER: Record<string, number> = {
  a: 301, b: 302, c: 303, d: 304, e: 305, f: 306, g: 307, h: 308, i: 309, j: 310, k: 311, l: 312, m: 313,
  n: 314, o: 315, p: 216, q: 217, r: 218, s: 219, t: 220, u: 221, v: 222, w: 223, x: 124, y: 125, z: 126,
};

/** SymPy `_sort_gens` order key. */
function genKey(g: Expr): [number, string, number] {
  const s = str(g);
  const m = /^(.*?)(\d*)$/.exec(s)!;
  const name = m[1]!;
  const index = m[2] ? Number(m[2]) : 0;
  return [GENS_ORDER[name] ?? 1000, name, index];
}

export function sortGens(gens: Expr[]): Expr[] {
  return [...gens].sort((a, b) => {
    const ka = genKey(a);
    const kb = genKey(b);
    for (let i = 0; i < 3; i++) {
      if (ka[i]! < kb[i]!) return -1;
      if (ka[i]! > kb[i]!) return 1;
    }
    return 0;
  });
}

const isCoeffAtom = (f: Expr) => isNum(f) || (f instanceof Constant && f.name === 'I');

/** Generators of an expanded expression (SymPy _dict_from_expr_no_gens). */
function detectGens(e: Expr): Expr[] {
  const gens = new Map<string, Expr>();
  for (const t of e instanceof Add ? e.args : [e]) {
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (isCoeffAtom(f)) continue;
      const g = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.isPositive ? f.base : f;
      gens.set(g.key, g);
    }
  }
  return sortGens([...gens.values()]);
}

// ---------------------------------------------------------------------------
// domains
// ---------------------------------------------------------------------------

function numberDomain(cs: Expr[]): string | undefined {
  let rational = false;
  let complex = false;
  let real = false;
  for (const c of cs) {
    if (c instanceof Rational) {
      if (!c.isInteger) rational = true;
      continue;
    }
    if (c instanceof Float) {
      real = true;
      continue;
    }
    // a + b*I with rational a, b
    const parts = c instanceof Add ? c.args : [c];
    let ok = true;
    for (const p of parts) {
      const [k, r] = p instanceof Mul && p.args[0] instanceof Rational ? [p.args[0], p.args.length === 2 ? p.args[1]! : new Mul(p.args.slice(1))] : [S.One, p];
      if (r instanceof Constant && r.name === 'I') {
        complex = true;
        if (!(k as Rational).isInteger) rational = true;
      } else if (p instanceof Rational) {
        if (!p.isInteger) rational = true;
      } else ok = false;
    }
    if (!ok) return undefined;
  }
  if (real) return 'RR';
  if (complex) return rational ? 'QQ_I' : 'ZZ_I';
  return rational ? 'QQ' : 'ZZ';
}

function inferDomain(cs: Expr[]): string {
  const nd = numberDomain(cs);
  if (nd) return nd;
  const syms = new Map<string, Sym>();
  for (const c of cs) for (const s of freeSymbols(c)) syms.set(s.key, s);
  if (syms.size === 0) return 'EX';
  const gens = sortGens([...syms.values()]) as Sym[];
  // polynomial ring?
  let rational = false;
  const polyOk = cs.every((c) => {
    const e = expand(c);
    return (e instanceof Add ? e.args : [e]).every((t) => {
      const fs = t instanceof Mul ? t.args : [t];
      return fs.every((f) => {
        if (f instanceof Rational) {
          if (!f.isInteger) rational = true;
          return true;
        }
        const b = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.isPositive ? f.base : f;
        return b instanceof Sym;
      });
    });
  });
  const names = gens.map((g) => str(g)).join(',');
  if (polyOk) return `${rational ? 'QQ' : 'ZZ'}[${names}]`;
  const fracOk = cs.every((c) =>
    (c instanceof Mul ? c.args : [c]).every((f) => {
      if (f instanceof Rational) {
        if (!f.isInteger) rational = true;
        return true;
      }
      const b = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger ? f.base : f;
      return b instanceof Sym || (b instanceof Add && b.args.every((a) => a instanceof Sym || a instanceof Rational));
    }),
  );
  if (fracOk) return `${rational ? 'QQ' : 'ZZ'}(${names})`;
  return 'EX';
}

// ---------------------------------------------------------------------------
// Poly
// ---------------------------------------------------------------------------

type Term = { monom: number[]; coeff: Expr };

const monomCmp = (a: number[], b: number[]): number => {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i]! - b[i]!;
  return 0;
};

export class Poly {
  readonly gens: readonly Expr[];
  /** terms in lex order, highest first; coefficients are nonzero */
  readonly termList: readonly Term[];
  readonly domain: string;
  readonly pure: boolean;

  private constructor(gens: readonly Expr[], terms: Term[], domain: string, pure = false) {
    this.gens = gens;
    this.termList = terms.sort((a, b) => monomCmp(b.monom, a.monom));
    this.domain = domain;
    this.pure = pure;
  }

  /** Build a polynomial; generators are detected unless given. */
  static from(ex: ExprLike, gens?: readonly Expr[], opts: { domain?: string; pure?: boolean } = {}): Poly {
    const e = expand(sympify(ex));
    const gs = gens && gens.length ? [...gens] : detectGens(e);
    const terms = new Map<string, Term>();
    for (const t of e instanceof Add ? e.args : [e]) {
      const monom = gs.map(() => 0);
      const rest: Expr[] = [];
      for (const f of t instanceof Mul ? t.args : [t]) {
        const i = gs.findIndex((g) => g.key === f.key);
        if (i >= 0) {
          monom[i]! += 1;
          continue;
        }
        if (f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.isPositive) {
          const j = gs.findIndex((g) => g.key === f.base.key);
          if (j >= 0) {
            monom[j]! += Number(f.exp.p);
            continue;
          }
        }
        if (gs.some((g) => f.has(g))) throw new PolificationFailed(`${str(e)} is not a polynomial in ${gs.map(str).join(', ')}`);
        rest.push(f);
      }
      const k = monom.join(',');
      const c = mul(...rest);
      const cur = terms.get(k);
      if (cur) cur.coeff = add(cur.coeff, c);
      else terms.set(k, { monom, coeff: c });
    }
    const list = [...terms.values()]
      .map((t) => ({ monom: t.monom, coeff: gs.length && !t.coeff.isNumber ? expand(t.coeff) : t.coeff }))
      .filter((t) => !(t.coeff instanceof Rational && t.coeff.isZero));
    const domain = opts.domain ?? inferDomain(list.length ? list.map((t) => t.coeff) : [S.Zero]);
    return new Poly(gs, list, domain, opts.pure ?? false);
  }

  private termExpr(t: Term): Expr {
    return mul(t.coeff, ...t.monom.map((k, i) => pow(this.gens[i]!, k)));
  }

  asExpr(): Expr {
    return add(...this.termList.map((t) => this.termExpr(t)));
  }

  get isZero(): boolean {
    return this.termList.length === 0;
  }

  /** [(monomial, coefficient)] in lex order. */
  terms(): [number[], Expr][] {
    if (this.isZero) return [[this.gens.map(() => 0), S.Zero]];
    return this.termList.map((t) => [t.monom, t.coeff]);
  }
  coeffs(): Expr[] {
    return this.isZero ? [S.Zero] : this.termList.map((t) => t.coeff);
  }
  monoms(): number[][] {
    return this.isZero ? [this.gens.map(() => 0)] : this.termList.map((t) => t.monom);
  }
  /** Dense coefficient list of a univariate polynomial, highest degree first. */
  allCoeffs(): Expr[] {
    if (this.gens.length !== 1) throw new Error('all_coeffs: multivariate polynomial');
    const d = this.degree();
    if (d < 0) return [S.Zero];
    return Array.from({ length: d + 1 }, (_, i) => this.coeffMonomial([d - i]));
  }
  coeffMonomial(monom: number[]): Expr {
    return this.termList.find((t) => monomCmp(t.monom, monom) === 0)?.coeff ?? S.Zero;
  }
  LC(): Expr {
    return this.termList[0]?.coeff ?? S.Zero;
  }
  LM(): Expr {
    const t = this.termList[0];
    return t ? mul(...t.monom.map((k, i) => pow(this.gens[i]!, k))) : S.One;
  }
  LT(): [number[], Expr] {
    const t = this.termList[0];
    return t ? [t.monom, t.coeff] : [this.gens.map(() => 0), S.Zero];
  }
  /** Degree in the given generator (first generator by default); -oo for zero. */
  degree(gen?: Expr | number): number {
    const i = gen === undefined ? 0 : typeof gen === 'number' ? gen : this.gens.findIndex((g) => g.key === gen.key);
    if (this.isZero) return -Infinity;
    if (i < 0) return 0;
    return Math.max(...this.termList.map((t) => t.monom[i]!));
  }
  degreeList(): number[] {
    return this.gens.map((_, i) => this.degree(i));
  }
  totalDegree(): number {
    if (this.isZero) return -Infinity;
    return Math.max(...this.termList.map((t) => t.monom.reduce((a, b) => a + b, 0)));
  }

  add(o: Poly | ExprLike): Poly {
    return Poly.from(add(this.asExpr(), o instanceof Poly ? o.asExpr() : o), this.gens);
  }
  sub(o: Poly | ExprLike): Poly {
    return Poly.from(add(this.asExpr(), mul(-1, o instanceof Poly ? o.asExpr() : o)), this.gens);
  }
  mul(o: Poly | ExprLike): Poly {
    return Poly.from(mul(this.asExpr(), o instanceof Poly ? o.asExpr() : o), this.gens);
  }
  pow(n: number): Poly {
    return Poly.from(pow(this.asExpr(), n), this.gens);
  }
  neg(): Poly {
    return Poly.from(mul(-1, this.asExpr()), this.gens);
  }

  private univariate(): Sym {
    const g = this.gens[0];
    if (this.gens.length !== 1 || !(g instanceof Sym)) throw new Error('univariate polynomial in a symbol expected');
    return g;
  }

  /** Division with remainder (univariate over the field of fractions). */
  div(o: Poly): [Poly, Poly] {
    const x = this.univariate();
    let r = this.asExpr();
    const g = o.asExpr();
    const dg = o.degree();
    const lg = o.LC();
    const q: Expr[] = [];
    for (let guard = 0; guard < 1000; guard++) {
      const pr = Poly.from(r, [x]);
      if (pr.isZero || pr.degree() < dg) break;
      const t = mul(pr.LC(), pow(lg, -1), pow(x, pr.degree() - dg));
      q.push(t);
      r = expand(add(r, mul(-1, t, g)));
    }
    const field = (d: string) => (d === 'ZZ' ? 'QQ' : d);
    const qp = Poly.from(add(...q), [x]);
    const rp = Poly.from(r, [x]);
    const dom = field(this.domain === o.domain ? this.domain : 'QQ');
    return [Poly.from(qp.asExpr(), [x], { domain: dom }), Poly.from(rp.asExpr(), [x], { domain: dom })];
  }
  /** SymPy div with auto=True: computed over the field, converted back to the ring when exact. */
  private toRingIfExact(p: Poly, ring: boolean): Poly {
    if (ring && p.domain === 'QQ' && p.termList.every((t) => t.coeff instanceof Rational && t.coeff.isInteger)) {
      return Poly.from(p.asExpr(), this.gens, { domain: 'ZZ' });
    }
    return p;
  }
  divAuto(o: Poly, auto = true): [Poly, Poly] {
    const ring = this.domain === 'ZZ' && o.domain === 'ZZ';
    if (!auto && ring) {
      const [q, r] = this.div(o);
      const ok = q.termList.every((t) => t.coeff instanceof Rational && t.coeff.isInteger);
      return ok ? [this.toRingIfExact(q, true), this.toRingIfExact(r, true)] : [Poly.from(0, this.gens, { domain: 'ZZ' }), this];
    }
    const [q, r] = this.div(o);
    const Q = this.toRingIfExact(q, ring);
    const R = this.toRingIfExact(r, ring);
    if (ring && (Q.domain !== 'ZZ' || R.domain !== 'ZZ')) return [q, r];
    return [Q, R];
  }
  rem(o: Poly, auto = true): Poly {
    if (!auto && this.domain === 'ZZ') return this.divAuto(o, false)[1];
    return this.toRingIfExact(this.div(o)[1], this.domain === 'ZZ' && o.domain === 'ZZ');
  }
  quo(o: Poly, auto = true): Poly {
    if (!auto && this.domain === 'ZZ') return this.divAuto(o, false)[0];
    return this.toRingIfExact(this.div(o)[0], this.domain === 'ZZ' && o.domain === 'ZZ');
  }
  /** Pseudo-remainder. */
  prem(o: Poly): Poly {
    return Poly.from(mprem(this.asExpr(), o.asExpr(), this.univariate()), this.gens);
  }
  /** Subresultant PRS (SymPy dup_inner_subresultants), univariate. */
  subresultants(o: Poly): Poly[] {
    let f: Poly = this;
    let g: Poly = o;
    let n = f.degree();
    let m = g.degree();
    if (n < m) {
      [f, g] = [g, f];
      [n, m] = [m, n];
    }
    if (f.isZero) return [];
    if (g.isZero) return [f];
    const R = [f, g];
    let d = n - m;
    let h = f.prem(g).mulGround(Rational.of(d % 2 === 0 ? -1 : 1));
    let lc = g.LC();
    let c: Expr = pow(lc, d);
    c = mul(-1, c);
    while (!h.isZero) {
      const k = h.degree();
      R.push(h);
      [f, g, d, m] = [g, h, m - k, k];
      const b = mul(-1, lc, pow(c, d));
      h = f.prem(g).exquoGround(b);
      lc = g.LC();
      if (d > 1) c = cancel(mul(pow(mul(-1, lc), d), pow(pow(c, d - 1), -1)));
      else c = mul(-1, lc);
    }
    return R;
  }
  /** Pseudo-quotient. */
  pquo(o: Poly): Poly {
    const x = this.univariate();
    const k = this.degree() - o.degree() + 1;
    const scaled = mul(pow(o.LC(), Math.max(0, k)), this.asExpr());
    return Poly.from(divExact(expand(add(scaled, mul(-1, mprem(this.asExpr(), o.asExpr(), x)))), o.asExpr(), [x])!, this.gens);
  }
  exquo(o: Poly): Poly {
    const q = divExact(this.asExpr(), o.asExpr(), this.gens as Sym[]);
    if (q === undefined) throw new Error('exquo: inexact division');
    return Poly.from(q, this.gens);
  }

  gcd(o: Poly): Poly {
    return Poly.from(mgcd(this.asExpr(), o.asExpr(), this.gens as Sym[]), this.gens);
  }
  lcm(o: Poly): Poly {
    return Poly.from(mlcm(this.asExpr(), o.asExpr(), this.gens as Sym[]), this.gens);
  }
  monic(): Poly {
    const lc = this.LC();
    const dom = this.domain === 'ZZ' ? 'QQ' : this.domain;
    return Poly.from(mul(this.asExpr(), pow(lc, -1)), this.gens, { domain: dom });
  }
  /** [content, primitive part] over the integers. */
  primitive(): [Expr, Poly] {
    const c = this.content();
    return [c, Poly.from(mul(this.asExpr(), pow(c, -1)), this.gens)];
  }
  content(): Expr {
    let g: Expr = S.Zero;
    for (const t of this.termList) g = mgcd(g, t.coeff, []);
    return g;
  }

  diff(x?: Expr): Poly {
    return Poly.from(diff(this.asExpr(), (x ?? this.gens[0]) as Sym), this.gens);
  }
  integrate(x?: Expr): Poly {
    const v = (x ?? this.gens[0]) as Sym;
    return Poly.from(integrate(this.asExpr(), v), this.gens, { domain: this.domain === 'ZZ' ? 'QQ' : this.domain });
  }
  /** Evaluate at gen = a (first generator by default). */
  eval(a: ExprLike, gen?: Expr): Expr | Poly {
    const g = gen ?? this.gens[0]!;
    const v = xreplace(this.asExpr(), [[g, sympify(a)]]);
    const rest = this.gens.filter((h) => h.key !== g.key);
    return rest.length ? Poly.from(v, rest) : expand(v);
  }

  /** (content, [(factor, multiplicity)]) with primitive integer factors. */
  factorList(): [Rational, [Poly, number][]] {
    const [c, fs] = factorListExpr(this.asExpr(), this.gens as Sym[]);
    return [c, fs.map(([f, k]) => [Poly.from(f, this.gens), k] as [Poly, number])];
  }
  sqfList(): [Rational, [Poly, number][]] {
    const x = this.univariate();
    const up = UPoly.fromExpr(this.asExpr(), x);
    if (!up) throw new Error('sqf_list: rational coefficients expected');
    const content = up.lc;
    const out: [Poly, number][] = up.squareFree().map(([f, k]) => [primitiveIntPoly(f.toExpr(x), x), k]);
    return [content, out];
  }

  /** Dense integer coefficients (highest degree first) of a primitive integer polynomial. */
  private denseInts(): bigint[] {
    const x = this.univariate();
    const n = this.degree();
    const cs = Array.from({ length: n + 1 }, (_, i) => this.coeffMonomial([n - i]) as Rational);
    void x;
    const den = cs.reduce((l, c) => (l * c.q) / bigGcd(l, c.q), 1n);
    return cs.map((c) => (c.p * den) / c.q);
  }
  /** Isolating intervals of the real roots with multiplicities (SymPy Poly.intervals). */
  intervals(eps?: Rational): [[Rational, Rational], number][] {
    const [, fs] = this.sqfList();
    return isolateRealRoots(fs.map(([f, k]) => [f.denseInts(), k] as [bigint[], number]), eps);
  }
  /** Refine the isolating interval (s, t) of a real root (SymPy Poly.refine_root). */
  refineRoot(s: Rational, t: Rational, eps?: Rational, steps?: number): [Rational, Rational] {
    const [, fs] = this.sqfList();
    const sqf = fs.reduce((acc, [f]) => acc.mul(f), Poly.from(S.One, this.gens));
    return refineRealRoot(sqf.denseInts(), s, t, eps, steps);
  }

  roots(): Expr[] {
    return rootsOf(this.asExpr(), this.univariate());
  }


  // ---- further SymPy Poly methods --------------------------------------------

  private like(e: ExprLike, gens: readonly Expr[] = this.gens, domain?: string): Poly {
    const p = Poly.from(e, gens);
    const d = domain ?? (this.domain === 'QQ' && p.domain === 'ZZ' ? 'QQ' : p.domain);
    return d === p.domain ? p : Poly.from(e, gens, { domain: d });
  }
  private mapCoeffs(f: (c: Expr) => Expr, domain?: string): Poly {
    return this.like(add(...this.termList.map((t) => this.termExpr({ monom: t.monom, coeff: f(t.coeff) }))), this.gens, domain);
  }
  abs(): Poly {
    return this.mapCoeffs((c) => (c instanceof Rational && c.isNegative ? mul(-1, c) : c));
  }
  sqr(): Poly {
    return this.pow(2);
  }
  addGround(c: ExprLike): Poly {
    return this.like(add(this.asExpr(), c));
  }
  subGround(c: ExprLike): Poly {
    return this.like(add(this.asExpr(), mul(-1, c)));
  }
  mulGround(c: ExprLike): Poly {
    return this.like(mul(this.asExpr(), c));
  }
  /** Coefficient-wise quotient (floor division over ZZ). */
  quoGround(c: ExprLike): Poly {
    const k = sympify(c);
    if (this.domain === 'ZZ' && k instanceof Rational && k.isInteger) {
      return this.mapCoeffs((x) => {
        const v = (x as Rational).p;
        const q = v / k.p;
        return Rational.of(v % k.p !== 0n && (v < 0n) !== (k.p < 0n) ? q - 1n : q);
      }, 'ZZ');
    }
    return this.mapCoeffs((x) => mul(x, pow(k, -1)));
  }
  exquoGround(c: ExprLike): Poly {
    const k = sympify(c);
    const r = this.mapCoeffs((x) => mul(x, pow(k, -1)));
    if (this.domain === 'ZZ' && r.domain !== 'ZZ') throw new Error('exquo_ground: inexact division');
    return r;
  }
  allMonoms(): number[][] {
    const d = this.degree();
    return Array.from({ length: Math.max(d, 0) + 1 }, (_, i) => [Math.max(d, 0) - i]);
  }
  allTerms(): [number[], Expr][] {
    return this.allMonoms().map((m) => [m, this.coeffMonomial(m)]);
  }
  asDict(): [number[], Expr][] {
    return this.termList.map((t) => [t.monom, t.coeff]);
  }
  /** Evaluate at the given generator values (positional) or a substitution list. */
  asExprAt(values: readonly ExprLike[] | readonly (readonly [Expr, ExprLike])[]): Expr {
    const reps: [Expr, Expr][] =
      values.length && Array.isArray(values[0])
        ? (values as readonly (readonly [Expr, ExprLike])[]).map(([g, v]) => [g, sympify(v)])
        : (values as readonly ExprLike[]).map((v, i) => [this.gens[i]!, sympify(v)]);
    return expand(xreplace(this.asExpr(), reps));
  }
  /** (gcd, f/gcd, g/gcd). */
  cofactors(o: Poly): [Poly, Poly, Poly] {
    const h = this.gcd(o);
    return [h, this.exquo(h), o.exquo(h)];
  }
  compose(o: Poly): Poly {
    return this.like(expand(xreplace(this.asExpr(), [[this.gens[0]!, o.asExpr()]])));
  }
  discriminant(): Expr {
    return discriminant(this.asExpr(), this.univariate());
  }
  resultant(o: Poly): Expr {
    return resultant(this.asExpr(), o.asExpr(), this.univariate());
  }
  /** Last coefficient in term order. */
  EC(): Expr {
    return this.termList[this.termList.length - 1]?.coeff ?? S.Zero;
  }
  /** Constant term. */
  TC(): Expr {
    return this.coeffMonomial(this.gens.map(() => 0));
  }
  /** Coefficient of gens**N. */
  nth(...N: number[]): Expr {
    return this.coeffMonomial(N);
  }
  length(): number {
    return this.termList.length;
  }
  l1Norm(): Expr {
    return add(...this.termList.map((t) => (t.coeff instanceof Rational && t.coeff.isNegative ? mul(-1, t.coeff) : t.coeff)));
  }
  maxNorm(): Expr {
    let m: Expr = S.Zero;
    for (const t of this.termList) {
      const a = t.coeff instanceof Rational && t.coeff.isNegative ? mul(-1, t.coeff) : t.coeff;
      if (a instanceof Rational && m instanceof Rational && (a.p * m.q > m.p * a.q)) m = a;
    }
    return m;
  }
  /** Evaluate several generators at once (dict or tuple of leading values). */
  evalMany(values: readonly (readonly [Expr, ExprLike])[]): Expr | Poly {
    const rest = this.gens.filter((g) => !values.some(([h]) => h.key === g.key));
    const v = expand(xreplace(this.asExpr(), values.map(([g, a]) => [g, sympify(a)] as [Expr, Expr])));
    return rest.length ? Poly.from(v, rest, { domain: this.domain }) : v;
  }
  /** Remove generators that do not occur. */
  exclude(): Poly {
    const keep = this.gens.filter((_, i) => this.termList.some((t) => t.monom[i]! > 0));
    return Poly.from(this.asExpr(), keep.length ? keep : [this.gens[0]!], { domain: this.domain });
  }
  hasOnlyGens(...gens: Expr[]): boolean {
    return this.gens.every((g, i) => gens.some((h) => h.key === g.key) || this.termList.every((t) => t.monom[i] === 0));
  }
  /** Total degree when homogeneous, else undefined. */
  homogeneousOrder(): number | undefined {
    if (this.isZero) return -Infinity;
    const ds = this.termList.map((t) => t.monom.reduce((a, b) => a + b, 0));
    return ds.every((d) => d === ds[0]) ? ds[0] : undefined;
  }
  homogenize(s: Expr): Poly {
    const d = this.totalDegree();
    const gens = this.gens.some((g) => g.key === s.key) ? this.gens : [...this.gens, s];
    const e = add(...this.termList.map((t) => mul(this.termExpr(t), pow(s, d - t.monom.reduce((a, b) => a + b, 0)))));
    return Poly.from(e, gens, { domain: this.domain });
  }
  /** Drop the generators to the left of gen. */
  ltrim(gen: Expr | number): Poly {
    let i = typeof gen === 'number' ? gen : this.gens.findIndex((g) => g.key === gen.key);
    if (i < 0) i += this.gens.length;
    return Poly.from(this.asExpr(), this.gens.slice(i), { domain: this.domain });
  }
  reorder(...gens: Expr[]): Poly {
    return Poly.from(this.asExpr(), gens, { domain: this.domain });
  }
  replace(x: Expr, y: Expr): Poly {
    return Poly.from(xreplace(this.asExpr(), [[x, y]]), this.gens.map((g) => (g.key === x.key ? y : g)), { domain: this.domain });
  }
  /** Pseudo-division: (pquo, prem). */
  pdiv(o: Poly): [Poly, Poly] {
    return [this.pquo(o), this.prem(o)];
  }
  pexquo(o: Poly): Poly {
    const [q, r] = this.pdiv(o);
    if (!r.isZero) throw new Error('pexquo: inexact division');
    return q;
  }
  /** f(x + a). */
  /** Greatest factorial factorization (SymPy gff_list, dup_gff_list). */
  gffList(): [Poly, number][] {
    if (this.isZero) throw new Error('gff_list: zero polynomial');
    const f = this.monic();
    if (f.degree() <= 0) return [];
    const g0 = f.gcd(f.shift(1));
    const H = g0.gffList();
    let g = g0;
    const out: [Poly, number][] = H.map(([h, k]) => {
      g = g.mul(h.shift(-k));
      return [h, k + 1];
    });
    const q = f.quo(g);
    return q.degree() <= 0 ? out : [[q, 1], ...out];
  }

  shift(a: ExprLike): Poly {
    const x = this.gens[0]!;
    return this.like(expand(xreplace(this.asExpr(), [[x, add(x, a)]])));
  }
  /** Square-free part. */
  sqfPart(): Poly {
    const x = this.univariate();
    const g = mgcd(this.asExpr(), diff(this.asExpr(), x), [x]);
    const q = divExact(this.asExpr(), g, [x])!;
    const p = Poly.from(q, this.gens);
    const [, prim] = p.primitive();
    return prim.LC() instanceof Rational && (prim.LC() as Rational).isNegative ? prim.neg() : prim;
  }
  /** (gcd of the monomials, quotient). */
  termsGcd(): [number[], Poly] {
    const m = this.gens.map((_, i) => Math.min(...this.termList.map((t) => t.monom[i]!)));
    const e = add(...this.termList.map((t) => this.termExpr({ monom: t.monom.map((k, i) => k - m[i]!), coeff: t.coeff })));
    return [m, Poly.from(e, this.gens, { domain: this.domain })];
  }
  /** (gcd of the exponents per generator, deflated polynomial). */
  deflate(): [number[], Poly] {
    const g = (a: number, b: number): number => (b === 0 ? a : g(b, a % b));
    const J = this.gens.map((_, i) => this.termList.reduce((acc, t) => g(acc, t.monom[i]!), 0) || 1);
    const e = add(...this.termList.map((t) => this.termExpr({ monom: t.monom.map((k, i) => k / J[i]!), coeff: t.coeff })));
    return [J, Poly.from(e, this.gens, { domain: this.domain })];
  }
  toField(): Poly {
    return Poly.from(this.asExpr(), this.gens, { domain: this.domain === 'ZZ' ? 'QQ' : this.domain });
  }
  toRing(): Poly {
    return Poly.from(this.asExpr(), this.gens, { domain: this.domain === 'QQ' ? 'ZZ' : this.domain });
  }
  toExact(): Poly {
    const e = xreplace(
      this.asExpr(),
      this.termList.filter((t) => t.coeff instanceof Float).map((t) => [t.coeff, rationalOfFloat(t.coeff as Float)] as [Expr, Expr]),
    );
    return Poly.from(e, this.gens, { domain: 'QQ' });
  }
  /** q**n * f(p/q). */
  transform(p: Poly, q: Poly): Poly {
    const n = this.degree();
    const x = this.gens[0]!;
    const e = add(
      ...this.termList.map((t) => mul(t.coeff, pow(p.asExpr(), t.monom[0]!), pow(q.asExpr(), n - t.monom[0]!))),
    );
    void x;
    return this.like(expand(e));
  }
  /** Reduce the coefficients modulo p into the symmetric range. */
  trunc(pIn: ExprLike): Poly {
    const p = (sympify(pIn) as Rational).p;
    return this.mapCoeffs((c) => {
      let v = ((c as Rational).p % p + p) % p;
      if (v > p / 2n) v -= p;
      return Rational.of(v);
    });
  }
  /** (lcm of denominators, polynomial times it). */
  clearDenoms(convert = false): [Expr, Poly] {
    let l = 1n;
    const gcdB = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcdB(b, a % b));
    for (const t of this.termList) if (t.coeff instanceof Rational) l = (l / gcdB(l, t.coeff.q)) * t.coeff.q;
    const e = expand(mul(Rational.of(l), this.asExpr()));
    return [Rational.of(l), Poly.from(e, this.gens, { domain: convert ? 'ZZ' : this.domain })];
  }
  /** Extended Euclid: (s, t, h) with s*f + t*g = h = gcd(f, g) (monic, over QQ). */
  gcdex(o: Poly): [Poly, Poly, Poly] {
    const x = this.univariate();
    let [r0, r1] = [this.toField(), o.toField()];
    let [s0, s1] = [Poly.from(1, [x], { domain: 'QQ' }), Poly.from(0, [x], { domain: 'QQ' })];
    let [t0, t1] = [Poly.from(0, [x], { domain: 'QQ' }), Poly.from(1, [x], { domain: 'QQ' })];
    while (!r1.isZero) {
      const [q, r] = r0.div(r1);
      [r0, r1] = [r1, r];
      [s0, s1] = [s1, s0.sub(q.mul(s1)).toField()];
      [t0, t1] = [t1, t0.sub(q.mul(t1)).toField()];
    }
    const lc = r0.LC();
    const inv = pow(lc, -1);
    const f = (p: Poly) => Poly.from(expand(mul(inv, p.asExpr())), [x], { domain: 'QQ' });
    return [f(s0), f(t0), f(r0)];
  }
  halfGcdex(o: Poly): [Poly, Poly] {
    const [s, , h] = this.gcdex(o);
    return [s, h];
  }
  /** Inverse of f modulo g. */
  invert(o: Poly): Poly {
    const [s, , h] = this.gcdex(o);
    if (h.degree() !== 0) throw new Error('invert: zero divisor');
    return s;
  }
  /** Sturm sequence over QQ. */
  sturm(): Poly[] {
    const x = this.univariate();
    const seq: Poly[] = [this.toField(), Poly.from(diff(this.asExpr(), x), [x], { domain: 'QQ' })];
    for (;;) {
      const r = seq[seq.length - 2]!.div(seq[seq.length - 1]!)[1];
      if (r.isZero) break;
      seq.push(Poly.from(mul(-1, r.asExpr()), [x], { domain: 'QQ' }));
    }
    return seq;
  }
  /** Number of real roots in [a, b] (Sturm's theorem). */
  countRoots(a?: ExprLike, b?: ExprLike): number {
    const x = this.univariate();
    const seq = this.sqfPartQQ().sturm();
    const signChanges = (v: Expr | 'inf' | '-inf'): number => {
      const vals = seq.map((p) => {
        if (v === 'inf' || v === '-inf') {
          const lc = (p.LC() as Rational).value;
          const d = p.degree();
          return v === 'inf' ? Math.sign(lc) : Math.sign(lc) * (d % 2 === 0 ? 1 : -1);
        }
        const r = xreplace(p.asExpr(), [[x, v]]);
        return Math.sign((r as Rational).value);
      }).filter((s) => s !== 0);
      let n = 0;
      for (let i = 1; i < vals.length; i++) if (vals[i] !== vals[i - 1]) n++;
      return n;
    };
    const lo = a === undefined ? '-inf' : sympify(a);
    const hi = b === undefined ? 'inf' : sympify(b);
    let n = signChanges(lo) - signChanges(hi);
    if (lo !== '-inf' && (xreplace(this.asExpr(), [[x, lo]]) as Rational).isZero) n += 1;
    return n;
  }
  private sqfPartQQ(): Poly {
    return this.sqfPart();
  }
  /** Rational roots with multiplicities (SymPy ground_roots). */
  groundRoots(): [Expr, number][] {
    const x = this.gens[0]!;
    const full = Poly.from(this.asExpr());
    if (this.gens.length === 1 && full.gens.length > 1 && full.gens.every((g) => g instanceof Sym)) {
      // symbolic coefficients: factor over all generators, keep factors linear in x
      const [, ffs] = full.factorList();
      const out: [Expr, number][] = [];
      for (const [f, k] of ffs) {
        const fx = Poly.from(f.asExpr(), [x]);
        if (fx.degree() === 1) out.push([cancel(mul(-1, fx.TC(), pow(fx.LC(), -1))), k]);
      }
      return out;
    }
    const [, fs] = this.factorList();
    const out: [Expr, number][] = [];
    for (const [f, k] of fs) {
      if (f.degree() === 1) out.push([mul(-1, f.TC(), pow(f.LC(), -1)), k]);
    }
    const [m] = this.termsGcd();
    if (m[0]! > 0 && !out.some(([r]) => r instanceof Rational && r.isZero)) out.push([S.Zero, m[0]!]);
    return out;
  }
  /** Series reversion: g with f*g = 1 mod x**n. */
  revert(n: number): Poly {
    const x = this.univariate();
    const c0 = this.TC();
    let g: Expr = pow(c0, -1);
    for (let k = 1; k < n; k++) {
      const prod = expand(mul(this.asExpr(), g));
      const ck = Poly.from(prod, [x]).coeffMonomial([k]);
      g = add(g, mul(-1, ck, pow(c0, -1), pow(x, k)));
    }
    return this.like(expand(g));
  }
  /** Polynomial whose roots are the n-th powers of the roots of f. */
  nthPowerRootsPoly(n: number): Poly {
    const x = this.univariate();
    const y = new Sym('_y_npr');
    const r = resultant(xreplace(this.asExpr(), [[x, y]]), add(x, mul(-1, pow(y, n))), y);
    const p = Poly.from(expand(r), [x]);
    const lc = p.LC();
    const sign = this.degree() % 2 === 1 && n % 2 === 0 ? -1 : 1;
    void sign;
    return this.like(expand(mul(r, pow(lc, -1), this.LC())));
  }
  /** Real roots (rational and quadratic surds), sorted, with multiplicity. */
  realRoots(): Expr[] {
    return this.rootsWhere(true);
  }
  allRoots(): Expr[] {
    return this.rootsWhere(false);
  }
  private rootsWhere(realOnly: boolean): Expr[] {
    const x = this.univariate();
    const [, fs] = this.factorList();
    type R = [Expr, { re: number; im: number }];
    const real: R[] = [];
    const cplx: R[] = [];
    for (const [f, k] of fs) {
      if (f.degree() > 2) {
        // irreducible factors of degree >= 3: CRootOf(f, i) like SymPy
        const vals = nroots(f, 15).map((v) => v.toComplex());
        vals.forEach((v, i) => {
          const r = new CRootOf(f.asExpr(), i);
          for (let j = 0; j < k; j++) (v.im === 0 ? real : cplx).push([r, v]);
        });
        continue;
      }
      for (const r of rootsOf(f.asExpr(), x)) {
        const v = impl.toComplex(r) as { re: number; im: number };
        for (let i = 0; i < k; i++) (isRealConst(r) ? real : cplx).push([r, v]);
      }
    }
    real.sort((a, b) => a[1].re - b[1].re);
    cplx.sort((a, b) => a[1].re - b[1].re || a[1].im - b[1].im);
    return realOnly ? real.map(([r]) => r) : [...real, ...cplx].map(([r]) => r);
  }
  root(i: number): Expr {
    return this.allRoots()[i]!;
  }
  whichRealRoots(cands: readonly Expr[]): Expr[] {
    return this.whichRoots(cands, true);
  }
  whichAllRoots(cands: readonly Expr[]): Expr[] {
    return this.whichRoots(cands, false);
  }
  private whichRoots(cands: readonly Expr[], realOnly: boolean): Expr[] {
    const x = this.univariate();
    const out: Expr[] = [];
    for (const c of cands) {
      if (out.some((o) => o.key === c.key)) continue;
      if (realOnly && !isRealConst(c)) continue;
      const v = expand(xreplace(this.asExpr(), [[x, c]]));
      if (v instanceof Rational && v.isZero) out.push(c);
    }
    return out;
  }
  /** [(f, k)] with the content folded into the first factor. */
  factorListInclude(): [Poly, number][] {
    const [c, fs] = this.factorList();
    if (!fs.length) return [[Poly.from(c, this.gens), 1]];
    if (!(c instanceof Rational && c.isOne)) fs[0] = [Poly.from(mul(c, fs[0]![0].asExpr()), this.gens), fs[0]![1]];
    return fs;
  }
  sqfListInclude(all = false): [Poly, number][] {
    const [c, fs] = this.sqfListAll(all);
    const out: [Poly, number][] = [[Poly.from(c, this.gens, { domain: this.domain }), 1], ...fs];
    if (fs.length && fs[0]![1] === 1) {
      out.shift();
      out[0] = [Poly.from(mul(c, fs[0]![0].asExpr()), this.gens), 1];
    }
    return out;
  }
  sqfListAll(all = false): [Rational, [Poly, number][]] {
    const [c, fs] = this.sqfList();
    if (!all) return [c, fs];
    const max = Math.max(0, ...fs.map(([, k]) => k));
    const full: [Poly, number][] = [];
    for (let k = 1; k <= max; k++) full.push(fs.find(([, j]) => j === k) ?? [Poly.from(1, this.gens, { domain: this.domain }), k]);
    return [c, full];
  }

  /** Smallest domain containing the coefficients (SymPy retract). */
  retract(field = false): Poly {
    const p = Poly.from(this.asExpr(), this.gens);
    if (field && p.domain === 'ZZ') return Poly.from(this.asExpr(), this.gens, { domain: 'QQ' });
    return p;
  }
  /** Functional decomposition f = g1(g2(...)) of a univariate polynomial (SymPy decompose). */
  decompose(): Poly[] {
    const x = this.univariate();
    const out: Poly[] = [];
    let f: Poly = this;
    for (;;) {
      const r = decomposeOnce(f, x);
      if (!r) break;
      out.unshift(r[1]);
      f = r[0];
    }
    return [f, ...out];
  }

  toString(): string {
    return polyStr(this);
  }
}

/** One step of the right decomposition f = g(h) with h(0) = 0, deg h > 1 (smallest such degree). */
function decomposeOnce(f: Poly, x: Sym): [Poly, Poly] | undefined {
  const n = f.degree();
  const lc = f.LC();
  for (let sDeg = 2; sDeg < n; sDeg++) {
    if (n % sDeg !== 0) continue;
    const r = n / sDeg;
    // h = x^s + h_{s-1} x^{s-1} + ... + h_1 x from the top coefficients of f/lc
    let h: Expr = pow(x, sDeg);
    for (let k = 1; k < sDeg; k++) {
      const hr = Poly.from(expand(pow(h, r)), [x]);
      const fk = mul(f.coeffMonomial([n - k]), pow(lc, -1));
      const ck = mul(add(fk, mul(-1, hr.coeffMonomial([n - k]))), Rational.of(1n, BigInt(r)));
      h = add(h, mul(ck, pow(x, sDeg - k)));
    }
    // express f in powers of h
    const hp = Poly.from(h, [x]);
    const gCoeffs: Expr[] = [];
    let cur: Poly = f;
    let ok = true;
    while (!cur.isZero) {
      const [q, rem] = cur.div(hp);
      if (rem.degree() > 0) {
        ok = false;
        break;
      }
      gCoeffs.push(rem.isZero ? S.Zero : rem.TC());
      cur = q;
    }
    if (!ok) continue;
    const g = add(...gCoeffs.map((c, i) => mul(c, pow(x, i))));
    const dom = f.domain === 'ZZ' && [g, h].every((e) => Poly.from(e, [x]).domain === 'ZZ') ? 'ZZ' : undefined;
    return [Poly.from(g, [x], dom ? { domain: dom } : {}), Poly.from(h, [x], dom ? { domain: dom } : {})];
  }
  return undefined;
}

function isRealConst(e: Expr): boolean {
  return !e.has(S.I);
}

function rationalOfFloat(f: Float): Rational {
  return impl.rationalFromFloat ? impl.rationalFromFloat(f) : Rational.of(BigInt(Math.round(f.value)));
}

/** Make a univariate rational polynomial primitive with integer coefficients and positive leading coefficient. */
function primitiveIntPoly(e: Expr, x: Sym): Poly {
  const p = Poly.from(e, [x]);
  const [, prim] = p.primitive();
  return prim.LC() instanceof Rational && (prim.LC() as Rational).isNegative ? prim.neg() : prim;
}

function bigGcd(a: bigint, b: bigint): bigint {
  let [x, y] = [a < 0n ? -a : a, b < 0n ? -b : b];
  while (y) [x, y] = [y, x % y];
  return x;
}

/** factor_list on expressions: (content, [(factor, multiplicity)]). */
export function factorListExpr(e: Expr, gens?: readonly Sym[]): [Rational, [Expr, number][]] {
  const vars = gens ?? (sortGens([...freeSymbols(e)]) as Sym[]);
  const [c, fs] = factorListRaw(e, vars);
  return [c, sortFactors(fs, vars)];
}

/** SymPy _sort_factors(multiple=True): by dense length in the main generator, multiplicity, then coefficients. */
function sortFactors(fs: [Expr, number][], vars: readonly Sym[]): [Expr, number][] {
  if (!vars.length) return fs;
  const key = (f: Expr): [number, Expr[]] => {
    const p = Poly.from(f, vars);
    if (vars.length === 1) return [p.degree() + 1, p.allCoeffs()];
    return [p.degree(0) + 1, []];
  };
  const cmpCoeffs = (a: Expr[], b: Expr[]): number => {
    for (let i = 0; i < Math.min(a.length, b.length); i++) {
      const x = a[i]!;
      const y = b[i]!;
      if (x instanceof Rational && y instanceof Rational) {
        const d = x.p * y.q - y.p * x.q;
        if (d !== 0n) return d < 0n ? -1 : 1;
      }
    }
    return a.length - b.length;
  };
  return [...fs].sort(([f, n], [g, m]) => {
    const [lf, cf] = key(f);
    const [lg, cg] = key(g);
    return lf - lg || n - m || cmpCoeffs(cf, cg);
  });
}

function factorListRaw(e: Expr, vars: readonly Sym[]): [Rational, [Expr, number][]] {
  return mfactorList(e, vars, (p, x) => {
    const up = UPoly.fromExpr(p, x);
    if (!up) return [S.One, [[p, 1]]];
    const { content, factors } = up.factor();
    let c: Rational = content;
    const out: [Expr, number][] = [];
    for (const [f, k] of factors) {
      const prim = primitiveIntPoly(f.toExpr(x), x);
      // f = s * prim  => c *= s^k
      const s = mul(f.toExpr(x), pow(prim.asExpr(), -1));
      const sc = cancel(s);
      if (sc instanceof Rational) c = mulR(c, powR(sc, k));
      out.push([prim.asExpr(), k]);
    }
    return [c, out];
  });
}

const mulR = (a: Rational, b: Rational): Rational => mul(a, b) as Rational;
const powR = (a: Rational, k: number): Rational => pow(a, k) as Rational;

// ---------------------------------------------------------------------------
// printing (SymPy StrPrinter._print_Poly)
// ---------------------------------------------------------------------------

function coeffStr(c: Expr): string {
  if (c instanceof Float) {
    const v = c.value;
    return Number.isInteger(v) ? `${v}.0` : `${v}`;
  }
  return str(c);
}

export function polyStr(p: Poly): string {
  const gens = p.gens.map((g) => {
    const s = str(g);
    return g instanceof Sym || isNum(g) ? s : `(${s})`;
  });
  const terms: string[] = [];
  for (const [monom, coeff] of p.terms()) {
    const sm: string[] = [];
    monom.forEach((e, i) => {
      if (e > 0) sm.push(e === 1 ? gens[i]! : `${gens[i]}**${e}`);
    });
    const sMonom = sm.join('*');
    let sCoeff: string;
    if (coeff instanceof Add) {
      sCoeff = sMonom ? `(${str(coeff)})` : str(coeff);
    } else {
      if (sMonom) {
        if (coeff instanceof Rational && coeff.isOne) {
          terms.push('+', sMonom);
          continue;
        }
        if (coeff instanceof Rational && coeff.p === -1n && coeff.q === 1n) {
          terms.push('-', sMonom);
          continue;
        }
      }
      sCoeff = coeffStr(coeff);
    }
    const sTerm = sMonom ? `${sCoeff}*${sMonom}` : sCoeff;
    if (sTerm.startsWith('-')) terms.push('-', sTerm.slice(1));
    else terms.push('+', sTerm);
  }
  const mod = terms.shift();
  if (mod === '-') terms[0] = `-${terms[0]}`;
  const gensOut = gens.map((g) => (g.length > 2 && g.startsWith('(') && g.endsWith(')') ? g.slice(1, -1) : g));
  return `${p.pure ? 'PurePoly' : 'Poly'}(${terms.join(' ')}, ${gensOut.join(', ')}, domain='${p.domain}')`;
}

// ---------------------------------------------------------------------------
// top-level functions on expressions
// ---------------------------------------------------------------------------

const toExpr = (f: Poly | ExprLike): Expr => (f instanceof Poly ? f.asExpr() : sympify(f));
const varsFor = (...fs: Expr[]): Sym[] => {
  const m = new Map<string, Sym>();
  for (const f of fs) for (const s of freeSymbols(f)) m.set(s.key, s);
  return sortGens([...m.values()]) as Sym[];
};

/** gcd of polynomials (expressions). */
export function polyGcd(f: Poly | ExprLike, g: Poly | ExprLike): Expr {
  const a = toExpr(f);
  const b = toExpr(g);
  return mgcd(a, b, varsFor(a, b));
}
export function polyLcm(f: Poly | ExprLike, g: Poly | ExprLike): Expr {
  const a = toExpr(f);
  const b = toExpr(g);
  return mlcm(a, b, varsFor(a, b));
}

/** Degree of f in gen (default: the only/first generator). */
export function degree(f: Poly | ExprLike, gen?: Expr): number {
  const p = f instanceof Poly ? f : Poly.from(f);
  if (gen === undefined) return p.degree();
  const e = p.asExpr();
  if (!e.has(gen)) return e instanceof Rational && e.isZero ? -Infinity : 0;
  return Poly.from(e, [gen]).degree();
}

/** Univariate division q, r with f = q*g + r. */
export function polyDiv(f: Poly | ExprLike, g: Poly | ExprLike): [Expr, Expr] {
  const a = toExpr(f);
  const b = toExpr(g);
  const v = varsFor(a, b);
  if (v.length !== 1) throw new Error('div: univariate polynomials expected');
  const [q, r] = Poly.from(a, v).div(Poly.from(b, v));
  return [q.asExpr(), r.asExpr()];
}

/** terms_gcd: pull out the gcd of all terms (numeric content and common monomial). */
export function termsGcd(f: ExprLike, ...rest: (Sym | TermsGcdOptions)[]): Expr {
  const opts: TermsGcdOptions = rest.length && !(rest[rest.length - 1] instanceof Expr) ? (rest.pop() as TermsGcdOptions) : {};
  const gens = rest as Sym[];
  const orig = sympify(f);
  if (orig.args.length === 0 || orig.isNumber) return orig;
  if (opts.deep) {
    const inner = rebuild(orig, orig.args.map((a) => termsGcd(a, ...gens, { ...opts })));
    return termsGcd(inner, ...gens, { ...opts, deep: false, expand: false });
  }
  const e = opts.expand === false ? orig : expand(orig);
  // terms as (rational coefficient, generator -> exponent)
  const terms: [Rational, Map<string, [Expr, number]>][] = [];
  for (const t of e instanceof Add ? e.args : [e]) {
    const fs = t instanceof Mul ? t.args : [t];
    let c = S.One as Rational;
    const m = new Map<string, [Expr, number]>();
    for (const g of fs) {
      if (g instanceof Rational) {
        c = mul(c, g) as Rational;
        continue;
      }
      if (g.isNumber && !(g instanceof Pow) && !(g instanceof Constant)) return orig;
      let [b, k] = decomposePower(g);
      if (k < 0) {
        b = pow(b, -1);
        k = -k;
      }
      const cur = m.get(b.key);
      m.set(b.key, [b, (cur ? cur[1] : 0) + k]);
    }
    terms.push([c, m]);
  }
  if (terms.length === 1 && terms[0]![0].isZero) return S.Zero;
  // exponents common to all terms
  const J = new Map<string, [Expr, number]>();
  for (const [k, v] of terms[0]![1]) J.set(k, [...v]);
  for (const [, m] of terms.slice(1)) {
    for (const [k, v] of [...J]) {
      const o = m.get(k);
      if (!o) J.delete(k);
      else v[1] = Math.min(v[1], o[1]);
    }
  }
  let num = 0n;
  let den = 1n;
  const g2 = (a: bigint, b: bigint): bigint => (b === 0n ? (a < 0n ? -a : a) : g2(b, a % b));
  for (const [c] of terms) {
    num = g2(num, c.p);
    den = (den / g2(den, c.q)) * c.q;
  }
  const coeff = num === 0n ? S.One : Rational.of(num, den);
  const term = mul(...[...J.values()].map(([b, k]) => pow(b, k)));
  if (coeff.isOne && isOneExpr(term)) return orig;
  const fExpr = add(
    ...terms.map(([c, m]) =>
      mul(
        mul(c, pow(coeff, -1)),
        ...[...m].map(([k, [b, n]]) => pow(b, n - (J.get(k)?.[1] ?? 0))),
      ),
    ),
  );
  if (opts.clear !== false) return keepCoeff(coeff, mul(term, fExpr));
  const kc = keepCoeff(coeff, fExpr, false);
  const [c2, f2] = kc instanceof Mul && kc.args[0] instanceof Rational ? [kc.args[0], kc.args.length === 2 ? kc.args[1]! : new Mul(kc.args.slice(1))] : [S.One, kc];
  return keepCoeff(c2, mul(term, f2), false);
}

/** Options of terms_gcd. */
export interface TermsGcdOptions {
  expand?: boolean;
  deep?: boolean;
  clear?: boolean;
}

const isOneExpr = (e: Expr) => e instanceof Rational && e.isOne;

/** Horner form (SymPy horner): multivariate polynomials recurse on the coefficients. */
export function horner(f: ExprLike, x?: Sym): Expr {
  const e = sympify(f);
  if (e.isNumber) return e;
  let gens = Poly.from(e).gens;
  if (x) gens = [x, ...gens.filter((g) => g.key !== x.key)];
  const v = gens[0];
  if (!v) return e;
  const p = Poly.from(e, [v]);
  const multi = gens.length > 1;
  let acc: Expr = S.Zero;
  for (const c of p.allCoeffs()) acc = add(mul(acc, v), multi ? horner(c) : c);
  return acc;
}

/** Lagrange interpolating polynomial through points (x_i, y_i) or y-values at 1..n. */
export function interpolate(data: readonly (readonly [ExprLike, ExprLike])[] | readonly ExprLike[], x: Sym): Expr {
  const pts: [Expr, Expr][] = (data as unknown[]).map((d, i) =>
    Array.isArray(d) ? [sympify(d[0] as ExprLike), sympify(d[1] as ExprLike)] : [Rational.of(i + 1), sympify(d as ExprLike)],
  );
  const terms = pts.map(([xi, yi], i) =>
    mul(yi, ...pts.filter((_, j) => j !== i).map(([xj]) => mul(add(x, mul(-1, xj)), pow(add(xi, mul(-1, xj)), -1)))),
  );
  return expand(add(...terms));
}

/** Resultant of two univariate polynomials (Sylvester determinant via Euclid). */
export function resultant(f: ExprLike, g: ExprLike, x: Sym): Expr {
  // res(f, g) by recursion on pseudo-remainders over the field of fractions
  let a = Poly.from(f, [x]);
  let b = Poly.from(g, [x]);
  let res: Expr = S.One;
  for (let guard = 0; guard < 100; guard++) {
    if (b.isZero) return S.Zero;
    const db = b.degree();
    if (db === 0) return expand(mul(res, pow(b.LC(), a.degree())));
    const da = a.degree();
    const r = a.rem(b);
    if (r.isZero) return S.Zero;
    const dr = r.degree();
    res = mul(res, pow(b.LC(), da - dr), (da * db) % 2 === 1 ? -1 : 1);
    a = b;
    b = r;
  }
  return res;
}

export function discriminant(f: ExprLike, x: Sym): Expr {
  const p = Poly.from(f, [x]);
  const n = p.degree();
  const r = resultant(p.asExpr(), diff(p.asExpr(), x), x);
  const sign = ((n * (n - 1)) / 2) % 2 === 0 ? 1 : -1;
  return expand(mul(sign, r, pow(p.LC(), -1)));
}

/**
 * Factor an expression over the rationals (multivariate), SymPy style:
 * an unevaluated product of the content and primitive factors.
 */
/**
 * Factorization of a univariate integer polynomial over GF(p) (SymPy
 * factor(f, modulus=p)), with coefficients in the symmetric range.
 */
function factorModulus(e: Expr, p: bigint): Expr {
  const vars = [...freeSymbols(e)];
  if (vars.length !== 1) throw new Error('factor: modulus requires a univariate polynomial');
  const x = vars[0]!;
  const cs = polyCoefficients(e, x);
  if (!cs || [...cs.values()].some((c) => !(c instanceof Rational && c.q === 1n))) throw new Error('factor: modulus requires integer coefficients');
  const n = Math.max(...cs.keys());
  const f = Array.from({ length: n + 1 }, (_, i) => (cs.get(i) as Rational | undefined)?.p ?? 0n);
  const sym = (c: bigint) => (c > p / 2n ? c - p : c);
  const [lc, fs] = factorModP(f, p);
  const toExpr = (g: bigint[]) => add(...g.map((c, i) => mul(Rational.of(sym(c)), pow(x, i))));
  return keepCoeff(Rational.of(sym(lc)), mul(...fs.map(([g, m]) => pow(toExpr(g), m))));
}

export function factor(ex: ExprLike, opts: { deep?: boolean; extension?: readonly Expr[]; gaussian?: boolean; modulus?: number | bigint } = {}): Expr {
  if (opts.modulus !== undefined) return factorModulus(sympify(ex), BigInt(opts.modulus));
  if (opts.gaussian || opts.extension?.length) {
    const r = factorOverExtension(sympify(ex), opts.gaussian ? [S.I] : opts.extension!);
    if (r) return r;
  }
  if (opts.deep) {
    // factor the arguments of functions and powers first (SymPy deep=True)
    const inner = mapBottomUp(sympify(ex), (t) => (t instanceof Fn || (t instanceof Pow && !(t.exp instanceof Rational)) ? rebuild(t, t.args.map((a) => factor(a))) : t));
    return factor(inner);
  }
  const e = sympify(ex);
  const vars = sortGens([...freeSymbols(e)]) as Sym[];
  if (vars.length === 0) return e;
  // rational functions: factor numerator and denominator
  const n = e instanceof Mul ? e.args.filter((f) => !(f instanceof Pow && f.exp instanceof Rational && f.exp.isNegative)) : [e];
  const d = e instanceof Mul ? e.args.filter((f) => f instanceof Pow && f.exp instanceof Rational && f.exp.isNegative) : [];
  if (d.length) {
    const fn_ = factor(mul(...n));
    const fd = factor(mul(...d.map((f) => pow((f as Pow).base, mul(-1, (f as Pow).exp)))));
    return mul(fn_, pow(fd, -1));
  }
  // powers of sums are factored base-wise (SymPy _symbolic_factor_list), which
  // also avoids expanding large powers
  const isSumPow = (f: Expr) => f instanceof Pow && f.base instanceof Add && f.exp instanceof Rational && f.exp.isInteger && f.exp.p > 1n;
  if (isSumPow(e)) return pow(factor((e as Pow).base), (e as Pow).exp);
  if (e instanceof Pow && e.base instanceof Add && e.exp instanceof Rational && !e.exp.isInteger) return pow(factor(e.base), e.exp);
  if (e instanceof Mul && e.args.some(isSumPow)) return mul(...e.args.map((f) => factor(f)));
  let poly: Expr;
  try {
    poly = expand(e);
    Poly.from(poly, vars);
  } catch {
    // treat non-polynomial subexpressions (sin(y), exp(x), sqrt(x), ...) as generators
    const reps: [Expr, Expr][] = [];
    const back: [Expr, Expr][] = [];
    const gen = (x: Expr): Expr => {
      if (x instanceof Sym || x instanceof Rational || x.freeSymbols().size === 0) return x;
      const polyLike = x instanceof Add || x instanceof Mul || (x instanceof Pow && x.exp instanceof Rational && x.exp.isInteger);
      if (polyLike) {
        const args = x.args.map(gen);
        return args.every((a, i) => a === x.args[i]) ? x : rebuild(x, args);
      }
      const found = reps.find(([k]) => k.key === x.key);
      if (found) return found[1];
      const d = new Sym(`_fg${reps.length}`);
      reps.push([x, d]);
      back.push([d, x]);
      return d;
    };
    const g = gen(e);
    if (!reps.length || g.key === e.key) return e;
    try {
      Poly.from(expand(g), sortGens([...freeSymbols(g)]) as Sym[]);
    } catch {
      return e;
    }
    return xreplace(factor(g), back);
  }
  const [c, fs] = factorListExpr(poly, vars);
  const parts = fs.map(([f, k]) => pow(f, k));
  if (parts.length === 0) return c;
  if (parts.length === 1 && c.isOne) return parts[0]!;
  // SymPy _keep_coeff: -1 times a single factor is evaluated (-(x + 1) -> -x - 1)
  if (parts.length === 1 && c.p === -1n && c.q === 1n) return mul(-1, parts[0]!);
  const sorted = [...parts].sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
  return c.isOne ? new Mul(sorted) : new Mul([c, ...sorted]);
}


/**
 * Factor a univariate polynomial with rational coefficients over Q(ext):
 * linear factors x - r for the roots r that lie in the extension (their
 * irrational parts are built from the generators only), the rest stays
 * as a factor over QQ.
 */
function factorOverExtension(e: Expr, ext: readonly Expr[]): Expr | undefined {
  const vars = [...freeSymbols(e)] as Sym[];
  if (vars.length !== 1) return undefined;
  const x = vars[0]!;
  let p: Poly;
  try {
    p = Poly.from(expand(e), [x]);
  } catch {
    return undefined;
  }
  if (p.domain !== 'ZZ' && p.domain !== 'QQ') return undefined;
  const gens = new Set(ext.map((g) => g.key));
  const inField = (r: Expr): boolean => {
    let ok = true;
    const visit = (t: Expr) => {
      if (!ok) return;
      if (t instanceof Rational) return;
      if (gens.has(t.key)) return;
      if (t instanceof Constant && t.name === 'I') {
        ok = false;
        return;
      }
      if (t instanceof Pow && t.exp instanceof Rational && !t.exp.isInteger) {
        // sqrt(8) = 2*sqrt(2) is canonical already; anything else must be a generator
        ok = false;
        return;
      }
      t.args.forEach(visit);
    };
    visit(r);
    return ok;
  };
  const rs = rootsOf(p.asExpr(), x);
  const lin: Expr[] = [];
  let rest = p;
  for (const r of rs) {
    if (!inField(r)) continue;
    lin.push(add(x, mul(-1, r)));
  }
  if (!lin.length) return undefined;
  // the product of the linear factors is rational when the extension is closed under conjugation
  let prod: Poly;
  try {
    prod = Poly.from(expand(mul(...lin)), [x]);
  } catch {
    return undefined;
  }
  if (prod.domain !== 'ZZ' && prod.domain !== 'QQ') return undefined;
  rest = p.exquo(prod);
  const lc = rest.LC();
  const remaining = rest.degree() > 0 ? factor(mul(rest.asExpr(), pow(lc, -1))) : S.One;
  return mul(lc, remaining, ...lin);
}

/**
 * Factor an expression with non-commutative symbols (a light SymPy
 * factor_nc): the non-commutative symbols are replaced by commutative
 * dummies, the result is factored and accepted when expanding it with the
 * original symbols gives back the input.
 */
export function factorNc(ex: ExprLike): Expr {
  const e = sympify(ex);
  if (e.isCommutative) return factor(e);
  const nc = [...freeSymbols(e)].filter((s) => !s.isCommutative);
  const reps = nc.map((s) => [s, new Sym(`_nc_${s.name}`)] as [Expr, Expr]);
  const f = factor(xreplace(e, reps));
  const back = xreplace(f, reps.map(([a, b]) => [b, a] as [Expr, Expr]));
  return expand(back).key === expand(e).key ? back : e;
}
