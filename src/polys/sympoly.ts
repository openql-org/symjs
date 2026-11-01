// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Poly: SymPy-compatible polynomial objects (generators, domain,
 * printing and the main polynomial API), plus top-level polynomial
 * functions (degree, LC/LM/LT, gcd, lcm, div, factor_list, ...).
 */

import { Add, Constant, Expr, ExprLike, Float, Mul, Pow, Rational, S, Sym, isNum } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { integrate } from '../integrals/integrate';
import { str } from '../printing/str';
import { expandMul as expand } from '../simplify/expand';
import { divExact, mfactorList, mgcd, mlcm, prem as mprem } from './mpoly';
import { UPoly, roots as rootsOf } from './poly';

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
  rem(o: Poly): Poly {
    return this.div(o)[1];
  }
  quo(o: Poly): Poly {
    return this.div(o)[0];
  }
  /** Pseudo-remainder. */
  prem(o: Poly): Poly {
    return Poly.from(mprem(this.asExpr(), o.asExpr(), this.univariate()), this.gens);
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
    const p = Poly.from(mul(this.asExpr(), pow(lc, -1)), this.gens);
    return p;
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

  roots(): Expr[] {
    return rootsOf(this.asExpr(), this.univariate());
  }

  toString(): string {
    return polyStr(this);
  }
}

/** Make a univariate rational polynomial primitive with integer coefficients and positive leading coefficient. */
function primitiveIntPoly(e: Expr, x: Sym): Poly {
  const p = Poly.from(e, [x]);
  const [, prim] = p.primitive();
  return prim.LC() instanceof Rational && (prim.LC() as Rational).isNegative ? prim.neg() : prim;
}

/** factor_list on expressions: (content, [(factor, multiplicity)]). */
export function factorListExpr(e: Expr, gens?: readonly Sym[]): [Rational, [Expr, number][]] {
  const vars = gens ?? (sortGens([...freeSymbols(e)]) as Sym[]);
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
      const sc = expand(s);
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
export function termsGcd(f: ExprLike): Expr {
  const e = expand(sympify(f));
  const vars = varsFor(e);
  const p = Poly.from(e, vars);
  if (p.isZero) return S.Zero;
  const mins = vars.map((_, i) => Math.min(...p.termList.map((t) => t.monom[i]!)));
  const [c] = p.primitive();
  const mono = mul(c, ...mins.map((k, i) => pow(vars[i]!, k)));
  const rest = expand(mul(e, pow(mono, -1)));
  if (rest instanceof Add) return new Mul([...(mono instanceof Mul ? mono.args : [mono]), rest].filter((x) => !(x instanceof Rational && x.isOne)));
  return mul(mono, rest);
}

/** Horner form of a univariate polynomial. */
export function horner(f: ExprLike, x?: Sym): Expr {
  const e = sympify(f);
  const v = x ?? varsFor(e)[0];
  if (!v) return e;
  const p = Poly.from(e, [v]);
  const cs = p.allCoeffs();
  let acc: Expr = cs[0]!;
  for (const c of cs.slice(1)) acc = add(mul(acc, v), c);
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
export function factor(ex: ExprLike): Expr {
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
  let poly: Expr;
  try {
    poly = expand(e);
    Poly.from(poly, vars);
  } catch {
    return e;
  }
  const [c, fs] = factorListExpr(poly, vars);
  const parts = fs.map(([f, k]) => pow(f, k));
  if (parts.length === 0) return c;
  if (parts.length === 1 && c.isOne) return parts[0]!;
  const sorted = [...parts].sort((a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
  return c.isOne ? new Mul(sorted) : new Mul([c, ...sorted]);
}
