// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Poly: SymPy-compatible polynomial objects (generators, domain,
 * printing and the main polynomial API), plus top-level polynomial
 * functions (degree, LC/LM/LT, gcd, lcm, div, factor_list, ...).
 */

import { DomainError, ExactQuotientFailed, NotImplementedError, NotInvertible, PolynomialError, SympifyError } from '../core/errors';
import { parse } from '../parsing/parser';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { isPolynomial } from '../core/methods';
import { at, defined, expectType, first, getOrThrow } from '../core/guard';
import { isIntegerQ, isPositive } from '../core/assumptions';
import { factorModP } from './zassenhaus';
import type { ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Expr, Float, Mul, Pow, Rational, S, Sym, compareExpr, impl, isNum } from '../core/nodes';
import { evalf as evalfExpr } from '../numeric/evalf';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, rebuild, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { str } from '../printing/str';
import { expand as expandFull, expandMul as expand } from '../simplify/expand';
import { sqrtdenest } from '../simplify/sqrtdenest';
import { cancel, fraction, together } from '../simplify/rational';
import { decomposePower, keepCoeff } from '../simplify/exprtools';
import { modInverse, rationalFromFloat } from '../core/numberutils';
import { lcm as ilcm } from '../core/numbers';
import { divExact, ffDiv, mfactorList, mgcd, mlcm } from './mpoly';
import { isolateRealRoots, refineRealRoot } from './rootisolation';
import { UPoly, polyCoefficients, polyHooks, roots as rootsOf } from './poly';

const isRational = (x: unknown): x is Rational => x instanceof Rational;
/** x as a Rational; throws InvariantError when the algorithm's guarantee that it is one fails. */
const asRational = (x: Expr, what: string): Rational => expectType(x, isRational, what);

/** The expression cannot be written as a polynomial in the generators (SymPy PolificationFailed). */
/** Numeric roots and CRootOf, registered by polys/nroots and polys/rootof (which import this module). @internal */
export const rootHooks: { nroots?: (f: Poly, n: number) => Expr[]; crootof?: (e: Expr, i: number) => Expr } = {};
const nroots = (f: Poly, n: number): Expr[] => defined(rootHooks.nroots, 'nroots hook')(f, n);

export class PolificationFailed extends PolynomialError {}

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
  // the pattern matches every string
  const m = defined(/^(.*?)(\d*)$/.exec(s), 'generator name');
  const name = at(m, 1);
  const digits = at(m, 2);
  const index = digits ? Number(digits) : 0;
  return [GENS_ORDER[name] ?? 1000, name, index];
}

export function sortGens<T extends Expr>(gens: readonly T[]): T[] {
  return [...gens].sort((a, b) => {
    const [a0, a1, a2] = genKey(a);
    const [b0, b1, b2] = genKey(b);
    if (a0 !== b0) return a0 < b0 ? -1 : 1;
    if (a1 !== b1) return a1 < b1 ? -1 : 1;
    if (a2 !== b2) return a2 < b2 ? -1 : 1;
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
  let rational = false as boolean; // set inside the callbacks below
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
      const [k, r] = p instanceof Mul && p.args[0] instanceof Rational ? [p.args[0], p.args.length === 2 ? at(p.args, 1) : new Mul(p.args.slice(1))] : [S.One, p];
      if (r instanceof Constant && r.name === 'I') {
        complex = true;
        if (!(k).isInteger) rational = true;
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

/** The ground domain of the coefficients (SymPy construct_domain): ZZ, QQ, RR, ZZ_I, ZZ[x], ZZ(x), EX. */
export function inferDomain(cs: Expr[]): string {
  const nd = numberDomain(cs);
  if (nd) return nd;
  const syms = new Map<string, Sym>();
  for (const c of cs) for (const s of freeSymbols(c)) syms.set(s.key, s);
  if (syms.size === 0) return 'EX';
  const gens = sortGens([...syms.values()]);
  // polynomial ring?
  let rational = false as boolean; // set inside the callbacks below
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

/** Lex comparison of two monomials of the same length. */
const monomCmp = (a: readonly number[], b: readonly number[]): number => {
  for (let i = 0; i < a.length; i++) {
    const x = at(a, i);
    const y = at(b, i);
    if (x !== y) return x - y;
  }
  return 0;
};

/** A [monomial, coefficient] result of a termwise callback. */
/** The double value of a Rational (values of the rational Sturm sequence at rational points). */
const numValue = (e: Expr): number => asRational(e, 'value').value;

/** A [generator, value] entry of a substitution list. */
const isGenValue = (v: ExprLike | readonly [Expr, ExprLike]): v is readonly [Expr, ExprLike] => Array.isArray(v);

const isTermPair = (r: ExprLike | readonly [readonly number[], ExprLike]): r is readonly [readonly number[], ExprLike] => Array.isArray(r);

/** A dense-representation leaf converted like sympify (SympifyError for other values). */
function sympifyLeaf(x: unknown): Expr {
  if (x instanceof Expr || typeof x === 'number' || typeof x === 'bigint') return sympify(x);
  throw new SympifyError(`Cannot convert ${String(x)} to an expression`, x);
}

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
    // over RR the generators are the symbols (numbers such as sqrt(3) become coefficients)
    const real = opts.domain === 'R' || opts.domain === 'RR';
    const gs = gens?.length ? [...gens] : real ? (sortGens([...freeSymbols(e)])) : detectGens(e);
    const terms = new Map<string, Term>();
    for (const t of e instanceof Add ? e.args : [e]) {
      const monom = gs.map(() => 0);
      const rest: Expr[] = [];
      for (const f of t instanceof Mul ? t.args : [t]) {
        const i = gs.findIndex((g) => g.key === f.key);
        if (i >= 0) {
          monom[i] = at(monom, i) + 1;
          continue;
        }
        if (f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.isPositive) {
          const j = gs.findIndex((g) => g.key === f.base.key);
          if (j >= 0) {
            monom[j] = at(monom, j) + Number(f.exp.p);
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
    if (opts.domain === 'R' || opts.domain === 'RR') {
      // real floating-point coefficients
      const real = list.map((t) => ({ monom: t.monom, coeff: impl.evalf(t.coeff, 15) }));
      return new Poly(gs, real, 'RR', opts.pure ?? false);
    }
    const domain = opts.domain ?? inferDomain(list.length ? list.map((t) => t.coeff) : [S.Zero]);
    return new Poly(gs, list, domain, opts.pure ?? false);
  }

  private termExpr(t: Term): Expr {
    return mul(t.coeff, ...t.monom.map((k, i) => pow(at(this.gens, i), k)));
  }

  asExpr(): Expr {
    return add(...this.termList.map((t) => this.termExpr(t)));
  }

  /**
   * SymPy ==: the same terms over the same generators (an expression is
   * converted to a polynomial in them first). The generators of a PurePoly
   * are placeholders: only their number has to agree.
   */
  equals(other: Poly | ExprLike): boolean {
    const g = other instanceof Poly ? other : asPoly(other, ...this.gens);
    if (isNoMatch(g)) return false;
    if (this.pure ? this.gens.length !== g.gens.length : this.gens.length !== g.gens.length || this.gens.some((x, i) => x.key !== at(g.gens, i).key)) return false;
    if (this.termList.length !== g.termList.length) return false;
    return this.termList.every((t, i) => {
      const u = at(g.termList, i);
      return monomCmp(t.monom, u.monom) === 0 && t.coeff.key === u.coeff.key;
    });
  }

  get isZero(): boolean {
    return this.termList.length === 0;
  }

  /**
   * Apply func to every term (SymPy termwise): it returns the new
   * coefficient, or a [monomial, coefficient] pair; zero coefficients drop.
   */
  termwise(func: (monom: number[], coeff: Expr) => ExprLike | readonly [readonly number[], ExprLike], gens: readonly Expr[] = this.gens): Poly {
    const out = new Map<string, Term>();
    for (const t of this.termList) {
      const r = func([...t.monom], t.coeff);
      const [monom, c] = isTermPair(r) ? [[...r[0]], sympify(r[1])] : [[...t.monom], sympify(r)];
      if (c instanceof Rational && c.isZero) continue;
      const k = monom.join(',');
      if (out.has(k)) throw new PolynomialError(`termwise: monomial ${k} was generated twice`);
      out.set(k, { monom, coeff: c });
    }
    return new Poly([...gens], [...out.values()], inferDomain(out.size ? [...out.values()].map((t) => t.coeff) : [S.Zero]), this.pure);
  }

  /**
   * A polynomial with this domain from a dense representation (SymPy per):
   * nested coefficient lists, highest degree first, one level per
   * generator. `remove` drops the generator at that index.
   */
  per(rep: readonly unknown[], opts: { gens?: readonly Expr[]; remove?: number } = {}): Poly | Expr {
    let gens = [...(opts.gens ?? this.gens)];
    if (opts.remove !== undefined) gens = gens.filter((_, i) => i !== opts.remove);
    const terms: Term[] = [];
    const walk = (r: unknown, level: number, prefix: number[]): void => {
      if (level === gens.length) {
        const c = sympifyLeaf(r);
        if (!(c instanceof Rational && c.isZero)) terms.push({ monom: prefix, coeff: c });
        return;
      }
      if (!Array.isArray(r)) throw new PolynomialError('per: dense representation nested less deeply than the generators');
      const list: readonly unknown[] = r;
      list.forEach((x, i) => walk(x, level + 1, [...prefix, list.length - 1 - i]));
    };
    if (!gens.length) return sympifyLeaf(rep.length ? rep[0] : 0);
    walk(rep, 0, []);
    return new Poly(gens, terms, this.domain, this.pure);
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
    if (this.gens.length !== 1) throw new PolynomialError('all_coeffs: multivariate polynomial');
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
    return t ? mul(...t.monom.map((k, i) => pow(at(this.gens, i), k))) : S.One;
  }
  LT(): [number[], Expr] {
    const t = this.termList[0];
    return t ? [t.monom, t.coeff] : [this.gens.map(() => 0), S.Zero];
  }
  /** The index of a generator (SymPy _gen_to_level): PolynomialError for an expression that is not one. */
  private genIndex(gen: Expr): number {
    const i = this.gens.findIndex((g) => g.key === gen.key);
    if (i < 0) throw new PolynomialError(`a valid generator expected, got ${gen.toString()}`);
    return i;
  }
  /** Degree in the given generator (first generator by default); -oo for zero. */
  degree(gen?: Expr | number): number {
    const i = gen === undefined ? 0 : typeof gen === 'number' ? gen : this.genIndex(gen);
    if (this.isZero) return -Infinity;
    return Math.max(...this.termList.map((t) => at(t.monom, i)));
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
    if (this.gens.length !== 1 || !(g instanceof Sym)) throw new PolynomialError('univariate polynomial in a symbol expected');
    return g;
  }

  /** Division with remainder (univariate over the field of fractions). */
  div(o: Poly): [Poly, Poly] {
    if (this.gens.length > 1) return this.divMulti(o);
    const x = this.univariate();
    let r = this.asExpr();
    const g = o.asExpr();
    const dg = o.degree();
    const lg = o.LC();
    const q: Expr[] = [];
    // symbolic coefficients are kept as cancelled fractions, so that the leading term cancels
    const canc = (c: Expr): Expr => (c instanceof Rational ? c : cancel(c));
    for (let guard = 0; guard < 1000; guard++) {
      const pr = Poly.from(r, [x]);
      if (pr.isZero || pr.degree() < dg) break;
      const t = mul(canc(mul(pr.LC(), pow(lg, -1))), pow(x, pr.degree() - dg));
      q.push(t);
      r = add(...Poly.from(expand(add(r, mul(-1, t, g))), [x]).termList.map((u) => mul(canc(u.coeff), pow(x, first(u.monom)))));
    }
    const field = (d: string) => (d === 'ZZ' ? 'QQ' : d);
    const qp = Poly.from(add(...q), [x]);
    const rp = Poly.from(r, [x]);
    const dom = field(this.domain === o.domain ? this.domain : 'QQ');
    return [Poly.from(qp.asExpr(), [x], { domain: dom }), Poly.from(rp.asExpr(), [x], { domain: dom })];
  }
  /** Multivariate division over the field of fractions (SymPy dmp_ff_div). */
  private divMulti(o: Poly): [Poly, Poly] {
    const [q, r] = ffDiv(this.asExpr(), o.asExpr(), this.gens);
    const dom = this.domain === o.domain && this.domain !== 'ZZ' ? this.domain : 'QQ';
    return [Poly.from(q, this.gens, { domain: dom }), Poly.from(r, this.gens, { domain: dom })];
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
  /** Pseudo-remainder: the remainder of LC(g)**(deg f - deg g + 1)*f (SymPy dup_prem). */
  prem(o: Poly): Poly {
    const x = this.univariate();
    if (o.isZero) throw new RangeError('prem: division by zero polynomial');
    const dg = o.degree();
    let N = this.degree() - dg + 1;
    if (N <= 0) return this;
    const lg = o.LC();
    const g = o.asExpr();
    let r: Poly = this;
    // each reduction step multiplies by LC(g); the remaining powers are applied at the end
    while (!r.isZero && r.degree() >= dg) {
      N--;
      r = Poly.from(expand(add(mul(lg, r.asExpr()), mul(-1, r.LC(), pow(x, r.degree() - dg), g))), this.gens);
    }
    return Poly.from(expand(mul(pow(lg, N), r.asExpr())), this.gens);
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
    // the scaled dividend minus the pseudo-remainder is an exact multiple of o
    return Poly.from(defined(divExact(expand(add(scaled, mul(-1, this.prem(o).asExpr()))), o.asExpr(), [x]), 'pseudo-quotient'), this.gens);
  }
  exquo(o: Poly): Poly {
    const q = divExact(this.asExpr(), o.asExpr(), this.gens);
    if (q === undefined) throw new ExactQuotientFailed('exquo: inexact division');
    return Poly.from(q, this.gens);
  }

  gcd(o: Poly): Poly {
    return Poly.from(mgcd(this.asExpr(), o.asExpr(), this.gens), this.gens);
  }
  lcm(o: Poly): Poly {
    return Poly.from(mlcm(this.asExpr(), o.asExpr(), this.gens), this.gens);
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
    return Poly.from(diff(this.asExpr(), x ?? first(this.gens)), this.gens);
  }
  /** The antiderivative in a generator (SymPy Poly.integrate), term by term. */
  integrate(x?: Expr): Poly {
    const i = x === undefined ? 0 : this.genIndex(x);
    const domain = this.domain === 'ZZ' ? 'QQ' : this.domain;
    const terms = this.termList.map((t) => {
      const k = at(t.monom, i) + 1;
      return mul(t.coeff, Rational.of(1n, BigInt(k)), ...t.monom.map((e, j) => pow(at(this.gens, j), j === i ? k : e)));
    });
    return Poly.from(add(...terms), this.gens, { domain });
  }
  /** Evaluate at gen = a (first generator by default). */
  eval(a: ExprLike, gen?: Expr): Expr | Poly {
    const g = gen ?? first(this.gens);
    const v = xreplace(this.asExpr(), [[g, sympify(a)]]);
    const rest = this.gens.filter((h) => h.key !== g.key);
    return rest.length ? Poly.from(v, rest) : expand(v);
  }

  /** (content, [(factor, multiplicity)]) with primitive integer factors. */
  factorList(): [Expr, [Poly, number][]] {
    const [c, fs] = factorListInt(this.asExpr(), this.gens);
    return [c, fs.map(([f, k]) => [Poly.from(f, this.gens), k] as [Poly, number])];
  }
  sqfList(): [Rational, [Poly, number][]] {
    const x = this.univariate();
    const up = UPoly.fromExpr(this.asExpr(), x);
    if (!up) return this.sqfListSymbolic(x);
    const content = up.lc;
    const out: [Poly, number][] = up.squareFree().map(([f, k]) => [primitiveIntPoly(f.toExpr(x), x), k]);
    return [content, out];
  }

  /**
   * Yun's square-free decomposition over ZZ[x, parameters] (symbolic
   * coefficients). A content free of x that is not a number is listed first
   * as a factor of degree 0 (SymPy returns it as the content).
   */
  private sqfListSymbolic(x: Expr): [Rational, [Poly, number][]] {
    const e = this.asExpr();
    const vars = [x, ...sortGens([...freeSymbols(e)].filter((s) => s.key !== x.key))];
    const dx = (p: Expr) => expand(diff(p, x));
    const quo = (p: Expr, q: Expr) => defined(divExact(p, q, vars), 'exact quotient');
    const sub = (p: Expr, q: Expr) => expand(add(p, mul(-1, q)));
    const g = mgcd(e, dx(e), vars);
    let b = quo(e, g);
    let d = sub(quo(dx(e), g), dx(b));
    const fs: [Expr, number][] = [];
    for (let i = 1; b.has(x); i++) {
      const a = mgcd(b, d, vars);
      if (a.has(x)) fs.push([a, i]);
      b = quo(b, a);
      d = sub(quo(d, a), dx(b));
    }
    const rest = quo(e, expand(mul(...fs.map(([f, k]) => pow(f, k)))));
    const opts = { domain: this.domain };
    const out: [Poly, number][] = fs.map(([f, k]) => [Poly.from(f, [x], opts), k]);
    if (rest instanceof Rational) return [rest, out];
    return [S.One, [[Poly.from(rest, [x], opts), 1], ...out]];
  }

  /** Dense integer coefficients (highest degree first) of the polynomial with its denominators cleared. */
  private denseInts(): bigint[] {
    this.univariate();
    const n = this.degree();
    const cs = Array.from({ length: n + 1 }, (_, i) => {
      const c = this.coeffMonomial([n - i]);
      if (!(c instanceof Rational)) throw new DomainError(`real root refinement not supported over ${this.domain}`);
      return c;
    });
    const den = cs.reduce((l, c) => ilcm(l, c.q), 1n);
    return cs.map((c) => (c.p * den) / c.q);
  }
  /** Isolating intervals of the real roots with multiplicities (SymPy Poly.intervals). */
  intervals(eps?: Rational): [[Rational, Rational], number][] {
    const [, fs] = this.sqfList();
    return isolateRealRoots(fs.map(([f, k]) => [f.denseInts(), k] as [bigint[], number]), eps);
  }
  /** Refine the isolating interval (s, t) of a real root (SymPy Poly.refine_root). */
  refineRoot(s: Rational, t: Rational, eps?: Rational, steps?: number): [Rational, Rational] {
    if (eps !== undefined && !eps.isPositive) throw new RangeError("'eps' must be a positive rational");
    // SymPy refines the polynomial itself (check_sqf=False), one step when neither eps nor steps is given
    return refineRealRoot(this.denseInts(), s, t, eps, steps ?? (eps === undefined ? 1 : undefined));
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
        const v = asRational(x, 'ZZ coefficient').p;
        const q = v / k.p;
        return Rational.of(v % k.p !== 0n && (v < 0n) !== (k.p < 0n) ? q - 1n : q);
      }, 'ZZ');
    }
    return this.mapCoeffs((x) => mul(x, pow(k, -1)));
  }
  exquoGround(c: ExprLike): Poly {
    const k = sympify(c);
    const r = this.mapCoeffs((x) => mul(x, pow(k, -1)));
    if (this.domain === 'ZZ' && r.domain !== 'ZZ') throw new ExactQuotientFailed('exquo_ground: inexact division');
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
    const vs: readonly (ExprLike | readonly [Expr, ExprLike])[] = values;
    const reps = vs.map((v, i): [Expr, Expr] => (isGenValue(v) ? [v[0], sympify(v[1])] : [at(this.gens, i), sympify(v)]));
    return expand(xreplace(this.asExpr(), reps));
  }
  /** (gcd, f/gcd, g/gcd). */
  cofactors(o: Poly): [Poly, Poly, Poly] {
    const h = this.gcd(o);
    return [h, this.exquo(h), o.exquo(h)];
  }
  compose(o: Poly): Poly {
    return this.like(expand(xreplace(this.asExpr(), [[first(this.gens), o.asExpr()]])));
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
    const keep = this.gens.filter((_, i) => this.termList.some((t) => at(t.monom, i) > 0));
    return Poly.from(this.asExpr(), keep.length ? keep : this.gens, { domain: this.domain });
  }
  hasOnlyGens(...gens: Expr[]): boolean {
    return this.gens.every((g, i) => gens.some((h) => h.key === g.key) || this.termList.every((t) => t.monom[i] === 0));
  }
  /** Total degree when homogeneous (SymPy homogeneous_order), else NoMatch. */
  homogeneousOrder(): number | NoMatchResult {
    if (this.isZero) return -Infinity;
    const ds = this.termList.map((t) => t.monom.reduce((a, b) => a + b, 0));
    const [d0] = ds;
    return d0 !== undefined && ds.every((d) => d === d0) ? d0 : NoMatch;
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
    if (!r.isZero) throw new ExactQuotientFailed('pexquo: inexact division');
    return q;
  }
  /** f(x + a). */
  /** Greatest factorial factorization (SymPy gff_list, dup_gff_list). */
  gffList(): [Poly, number][] {
    if (this.isZero) throw new PolynomialError('gff_list: zero polynomial');
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
    const all: [Poly, number][] = q.degree() <= 0 ? out : [[q, 1], ...out];
    // over ZZ the (monic) factors are integer polynomials
    return all.map(([h, k]) => [this.domain === 'ZZ' ? h.retract() : h.toField(), k]);
  }

  shift(a: ExprLike): Poly {
    const x = first(this.gens);
    return this.like(expand(xreplace(this.asExpr(), [[x, add(x, a)]])));
  }
  /** Square-free part. */
  sqfPart(): Poly {
    const x = this.univariate();
    const g = mgcd(this.asExpr(), diff(this.asExpr(), x), [x]);
    const q = defined(divExact(this.asExpr(), g, [x]), 'quotient by gcd(f, f\')');
    const p = Poly.from(q, this.gens);
    const [, prim] = p.primitive();
    const lc = prim.LC();
    return lc instanceof Rational && lc.isNegative ? prim.neg() : prim;
  }
  /** (gcd of the monomials, quotient). */
  termsGcd(): [number[], Poly] {
    const m = this.gens.map((_, i) => Math.min(...this.termList.map((t) => at(t.monom, i))));
    const e = add(...this.termList.map((t) => this.termExpr({ monom: t.monom.map((k, i) => k - at(m, i)), coeff: t.coeff })));
    return [m, Poly.from(e, this.gens, { domain: this.domain })];
  }
  /** (gcd of the exponents per generator, deflated polynomial). */
  deflate(): [number[], Poly] {
    const g = (a: number, b: number): number => (b === 0 ? a : g(b, a % b));
    const J = this.gens.map((_, i) => this.termList.reduce((acc, t) => g(acc, at(t.monom, i)), 0) || 1);
    const e = add(...this.termList.map((t) => this.termExpr({ monom: t.monom.map((k, i) => k / at(J, i)), coeff: t.coeff })));
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
      this.termList.flatMap((t): [Expr, Expr][] => (t.coeff instanceof Float ? [[t.coeff, rationalOfFloat(t.coeff)]] : [])),
    );
    // SymPy get_exact: RR -> QQ, exact domains unchanged
    return Poly.from(e, this.gens, { domain: this.domain === 'RR' ? 'QQ' : this.domain });
  }
  /** q**n * f(p/q). */
  transform(p: Poly, q: Poly): Poly {
    const n = this.degree();
    const e = add(
      ...this.termList.map((t) => {
        const k = first(t.monom);
        return mul(t.coeff, pow(p.asExpr(), k), pow(q.asExpr(), n - k));
      }),
    );
    return this.like(expand(e));
  }
  /** Reduce the coefficients modulo p into the symmetric range. */
  trunc(pIn: ExprLike): Poly {
    const p = asRational(sympify(pIn), 'modulus').p;
    return this.mapCoeffs((c) => {
      let v = (asRational(c, 'coefficient').p % p + p) % p;
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
    if (h.degree() !== 0) throw new NotInvertible('invert: zero divisor');
    return s;
  }
  /** Sturm sequence over QQ. */
  sturm(): Poly[] {
    const x = this.univariate();
    const seq: Poly[] = [this.toField(), Poly.from(diff(this.asExpr(), x), [x], { domain: 'QQ' })];
    for (;;) {
      const r = at(seq, -2).div(at(seq, -1))[1];
      if (r.isZero) break;
      seq.push(Poly.from(mul(-1, r.asExpr()), [x], { domain: 'QQ' }));
    }
    return seq;
  }
  /** Number of real roots in [a, b] (Sturm's theorem). */
  countRoots(a?: ExprLike, b?: ExprLike): number {
    // over RR the roots of the exact polynomial are counted (SymPy count_roots() over RR gives 2 for x**2 - 2.0)
    if (this.domain === 'RR') return this.toExact().countRoots(a, b);
    const x = this.univariate();
    const seq = this.sqfPartQQ().sturm();
    const signChanges = (v: Expr | 'inf' | '-inf'): number => {
      const vals = seq.map((p) => {
        if (v === 'inf' || v === '-inf') {
          const lc = numValue(p.LC());
          const d = p.degree();
          return v === 'inf' ? Math.sign(lc) : Math.sign(lc) * (d % 2 === 0 ? 1 : -1);
        }
        const r = xreplace(p.asExpr(), [[x, v]]);
        return Math.sign(numValue(r));
      }).filter((s) => s !== 0);
      let n = 0;
      for (let i = 1; i < vals.length; i++) if (vals[i] !== vals[i - 1]) n++;
      return n;
    };
    // SymPy converts the bounds to QQ (CoercionFailed for other numbers)
    const bound = (v: ExprLike): Rational => {
      const e = sympify(v);
      if (e instanceof Float) return rationalOfFloat(e);
      if (e instanceof Rational) return e;
      throw new DomainError(`expected a Rational, got ${str(e)}`);
    };
    const lo = a === undefined ? '-inf' : bound(a);
    const hi = b === undefined ? 'inf' : bound(b);
    let n = signChanges(lo) - signChanges(hi);
    if (lo !== '-inf') {
      if (numValue(xreplace(this.asExpr(), [[x, lo]])) === 0) n += 1;
    }
    return n;
  }
  private sqfPartQQ(): Poly {
    return this.sqfPart();
  }
  /** Rational roots with multiplicities (SymPy ground_roots). */
  groundRoots(opts: { extension?: boolean } = {}): [Expr, number][] {
    const x = first(this.gens);
    if (opts.extension) {
      const out = new Map<string, [Expr, number]>();
      for (const r of this.radicalRoots(false)) {
        const cur = out.get(r.key);
        if (cur) cur[1]++;
        else out.set(r.key, [r, 1]);
      }
      return [...out.values()];
    }
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
    // SymPy: the resultant in y of f(y) and y**n - x, (-1)**deg(f)*LC(f)**n*prod(x - r_i**n)
    return this.like(expand(resultant(xreplace(this.asExpr(), [[x, y]]), add(pow(y, n), mul(-1, x)), y)));
  }
  /**
   * Roots of a polynomial with algebraic coefficients (I, square roots of
   * integers), like SymPy: the roots of the norm polynomial over QQ (the
   * product of the conjugates) that are roots of this polynomial.
   */
  private liftedRoots(realOnly: boolean): Expr[] | undefined {
    const N = this.normPoly();
    if (!N) return undefined;
    const f = this.asExpr();
    const x = this.univariate();
    const scale = this.allCoeffs().reduce((m, c) => Math.max(m, Math.hypot(c.toComplex().re, c.toComplex().im)), 1);
    // the roots of the rational norm and the coefficients of f are numbers, so f evaluates at them
    return N.rootsWhere(realOnly).filter((r) => {
      const v = evalfExpr(xreplace(f, [[x, evalfExpr(r, 30)]]), 30).toComplex();
      return Math.hypot(v.re, v.im) < 1e-12 * scale;
    });
  }
  /**
   * The norm of a univariate polynomial with algebraic coefficients (I and
   * square roots of integers): the product of its conjugates, a polynomial
   * over QQ. Undefined when the coefficients are rational.
   */
  private normPoly(): Poly | undefined {
    const cs = this.allCoeffs();
    if (cs.every((c) => c instanceof Rational) && !/^(?:QQ|ZZ)<.*>$/.test(this.domain)) return undefined;
    return this.algebraicNorm();
  }
  /**
   * SymPy Poly.norm: the product of the conjugates of a polynomial over an
   * algebraic field QQ<a>, a polynomial over QQ. Like SymPy, other ground
   * domains (ZZ, QQ, ZZ_I, EX) raise DomainError.
   */
  norm(): Poly {
    if (!/^(?:QQ|ZZ)<.*>$/.test(this.domain)) throw new DomainError('ground domain must be algebraic');
    const N = this.algebraicNorm();
    if (!N) throw new NotImplementedError('norm: unsupported coefficient field');
    return N;
  }
  /** The product of the conjugates over I and square roots of integers; undefined when they do not give a rational polynomial. */
  private algebraicNorm(): Poly | undefined {
    const cs = this.allCoeffs();
    const gens = new Map<string, Expr>();
    const findGens = (e: Expr) => {
      if (e instanceof Constant && e.name === 'I') gens.set(e.key, e);
      else if (e instanceof Pow && e.base instanceof Rational && e.base.isInteger && e.exp instanceof Rational && e.exp.key === S.Half.key) gens.set(e.key, e);
      else e.args.forEach(findGens);
    };
    cs.forEach(findGens);
    // the generators of an algebraic field domain QQ<a> count too (QQ<sqrt(2) + sqrt(3)> has degree 4)
    const dm = /^(?:QQ|ZZ)<(.*)>$/.exec(this.domain);
    if (dm) {
      try {
        findGens(parse(defined(dm[1], 'domain generator')));
      } catch {
        // not an expression we can read
      }
    }
    const gl = [...gens.values()];
    if (!gl.length || gl.length > 3) return undefined;
    const f = this.asExpr();
    let norm: Expr = S.One;
    for (let mask = 0; mask < 1 << gl.length; mask++) {
      norm = mul(norm, xreplace(f, gl.map((g, i) => [g, mask & (1 << i) ? mul(-1, g) : g] as [Expr, Expr])));
    }
    const N = Poly.from(expand(norm), [this.univariate()], { domain: 'QQ' });
    return N.allCoeffs().every((c) => c instanceof Rational) ? N : undefined;
  }
  /** SymPy Poly.make_monic_over_integers_by_scaling_roots: [monic integer polynomial g, s] with g(x) = f(x/s)*s**n/LC(f). */
  makeMonicOverIntegersByScalingRoots(): [Poly, Expr] {
    const x = this.univariate();
    const n = this.degree();
    const lc = this.LC();
    const cs = this.allCoeffs().map((c) => impl.mul(c, impl.pow(lc, -1)));
    let s = 1n;
    const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
    for (const c of cs) {
      if (!(c instanceof Rational)) throw new DomainError('make_monic_over_integers_by_scaling_roots: rational coefficients expected');
      s = (s * c.q) / g(s, c.q);
    }
    const S_ = Rational.of(s);
    const e = impl.add(...cs.map((c, i) => impl.mul(c, impl.pow(S_, i), impl.pow(x, n - i))));
    return [Poly.from(e, [x], { domain: 'ZZ' }), S_];
  }
  /** SymPy Poly.get_modulus: p of a polynomial over GF(p). */
  getModulus(): bigint {
    const m = /^GF\((\d+)\)$/.exec(this.domain);
    if (!m) throw new DomainError('get_modulus: not a polynomial over a finite field');
    return BigInt(defined(m[1], 'modulus'));
  }
  /** SymPy Poly.set_modulus: the polynomial over GF(p), coefficients in the symmetric range. */
  setModulus(p: number | bigint): Poly {
    const P = BigInt(p);
    const red = (c: Expr): Expr => {
      if (!(c instanceof Rational && c.q === 1n)) throw new DomainError('set_modulus: integer coefficients expected');
      let r = ((c.p % P) + P) % P;
      if (r > P / 2n) r -= P;
      return Rational.of(r);
    };
    const e = add(...this.termList.map((t) => mul(red(t.coeff), ...t.monom.map((k, i) => pow(at(this.gens, i), k)))));
    return Poly.from(e, this.gens, { domain: `GF(${P})` });
  }
  /** SymPy Poly.eject(*gens): move generators into the ground domain (ZZ -> ZZ[x]). */
  eject(...gens: Expr[]): Poly {
    // SymPy ejects over a numerical domain only
    if (this.domain.includes('[')) throw new DomainError(`Cannot eject generators over ${this.domain}`);
    const keys = new Set(gens.map((g) => g.key));
    const rest = this.gens.filter((g) => !keys.has(g.key));
    if (gens.length === 0) return this;
    // SymPy ejects the leading or the trailing generators, in their order
    const k = gens.length;
    const same = (part: readonly Expr[]) => part.length === k && part.every((g, j) => g.key === at(gens, j).key);
    if (!same(this.gens.slice(0, k)) && !same(this.gens.slice(-k))) throw new NotImplementedError('can only eject front or back generators');
    const names = this.gens.filter((g) => keys.has(g.key)).map((g) => str(g)).join(',');
    return Poly.from(this.asExpr(), rest, { domain: `${this.domain}[${names}]` });
  }
  /** SymPy Poly.inject(front=False): move the generators of a polynomial ground domain (ZZ[y]) into the generators. */
  inject(opts: { front?: boolean } = {}): Poly {
    const m = this.domain.match(/^(ZZ|QQ)\[(.*)\]$/);
    if (!m) return this;
    const [, ground = '', inner = ''] = m;
    const names = inner.split(',');
    const syms = new Map([...freeSymbols(this.asExpr())].map((s) => [str(s), s] as [string, Expr]));
    const dg = names.map((n) => syms.get(n)).filter((s): s is Expr => s !== undefined);
    const gens = opts.front ? [...dg, ...this.gens] : [...this.gens, ...dg];
    return Poly.from(this.asExpr(), gens, { domain: ground });
  }
  /** SymPy Poly.lift: the norm over the ground field of an algebraic extension (ZZ_I -> ZZ, QQ<a> -> QQ). */
  lift(): Poly {
    // SymPy lifts over ZZ_I, QQ_I and QQ<a> only
    if (!/^(?:ZZ_I|QQ_I|(?:QQ|ZZ)<.*>)$/.test(this.domain)) throw new DomainError('computation can be done only in an algebraic domain');
    const N = defined(this.normPoly(), 'lift');
    return Poly.from(N.asExpr(), this.gens, { domain: this.domain.startsWith('ZZ') ? 'ZZ' : 'QQ' });
  }
  /** Real roots (rational and quadratic surds), sorted, with multiplicity. */
  realRoots(opts: { extension?: boolean } = {}): Expr[] {
    return opts.extension ? this.radicalRoots(true) : this.rootsWhere(true);
  }
  allRoots(opts: { extension?: boolean } = {}): Expr[] {
    return opts.extension ? this.radicalRoots(false) : this.rootsWhere(false);
  }
  /** Roots in radicals (SymPy extension=True for algebraic coefficients), real ones first, sorted. */
  private radicalRoots(realOnly: boolean): Expr[] {
    // algebraic numbers detected as generators (sqrt(2)*x + ...): the polynomial in its symbol
    const syms = this.gens.filter((g) => g instanceof Sym);
    if (this.gens.length > 1 && syms.length === 1) return Poly.from(this.asExpr(), syms).radicalRoots(realOnly);
    if (this.allCoeffs().every((c) => c instanceof Rational)) return this.rootsWhere(realOnly);
    // like SymPy's roots over the algebraic field: nested square roots denested
    // (sqrt(5 - 2*sqrt(6)) = sqrt(3) - sqrt(2)) and square roots of complex numbers expanded
    const tidy = (r0: Expr): Expr => {
      let r = expandFull(sqrtdenest(r0));
      const complexRadical = (e: Expr): boolean => (e instanceof Pow && !(e.exp instanceof Rational && e.exp.isInteger) && freeSymbols(e.base).size === 0 && e.base.has(S.I)) || e.args.some(complexRadical);
      if (complexRadical(r)) r = expandFull(r, { complex: true });
      return r;
    };
    const rs = rootsOf(this.asExpr(), this.univariate()).map((r) => tidy(r)).map((r) => [r, impl.toComplex(r)] as const);
    const isReal = (v: { im: number; re: number }) => Math.abs(v.im) <= 1e-12 * Math.max(1, Math.abs(v.re));
    const real = rs.filter(([, v]) => isReal(v)).sort((a, b) => a[1].re - b[1].re);
    const cplx = rs.filter(([, v]) => !isReal(v)).sort((a, b) => a[1].re - b[1].re || a[1].im - b[1].im);
    return (realOnly ? real : [...real, ...cplx]).map(([r]) => r);
  }
  private rootsWhere(realOnly: boolean): Expr[] {
    const lifted = this.liftedRoots(realOnly);
    if (lifted) return lifted;
    const x = this.univariate();
    const [, fs] = this.factorList();
    type R = [Expr, { re: number; im: number }];
    const real: R[] = [];
    const cplx: R[] = [];
    for (const [f, k] of fs) {
      if (f.degree() > 2) {
        // irreducible factors of degree >= 3: CRootOf(f, i) like SymPy
        const vals = nroots(f, 15).map((v) => v.toComplex());
        const crootof = defined(rootHooks.crootof, 'crootof hook');
        vals.forEach((v, i) => {
          const r = crootof(f.asExpr(), i);
          for (let j = 0; j < k; j++) (v.im === 0 ? real : cplx).push([r, v]);
        });
        continue;
      }
      for (const r of rootsOf(f.asExpr(), x)) {
        const v = impl.toComplex(r);
        for (let i = 0; i < k; i++) (isRealConst(r) ? real : cplx).push([r, v]);
      }
    }
    real.sort((a, b) => a[1].re - b[1].re);
    cplx.sort((a, b) => a[1].re - b[1].re || a[1].im - b[1].im);
    return realOnly ? real.map(([r]) => r) : [...real, ...cplx].map(([r]) => r);
  }
  root(i: number): Expr {
    return at(this.allRoots(), i);
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
      else if (!(v instanceof Rational)) {
        // implicit candidates (CRootOf): decided numerically
        try {
          const z = evalfExpr(v, 30).toComplex();
          if (Math.hypot(z.re, z.im) < 1e-12) out.push(c);
        } catch {
          // not evaluable
        }
      }
    }
    return out;
  }
  /** [(f, k)] with the content folded into the first factor. */
  factorListInclude(): [Poly, number][] {
    const [c, fs] = this.factorList();
    const [f0, ...rest] = fs;
    if (f0 === undefined) return [[Poly.from(c, this.gens), 1]];
    if (!(c instanceof Rational && c.isOne)) return [[Poly.from(mul(c, f0[0].asExpr()), this.gens), f0[1]], ...rest];
    return fs;
  }
  sqfListInclude(all = false): [Poly, number][] {
    const [c, fs] = this.sqfListAll(all);
    const out: [Poly, number][] = [[Poly.from(c, this.gens, { domain: this.domain }), 1], ...fs];
    const f0 = fs[0];
    if (f0?.[1] === 1) {
      out.shift();
      out[0] = [Poly.from(mul(c, f0[0].asExpr()), this.gens), 1];
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
    // both components over the domain of f (QQ when a component has fractions)
    const dom = f.domain === 'ZZ' && [g, h].every((e) => Poly.from(e, [x]).domain === 'ZZ') ? 'ZZ' : f.domain === 'ZZ' || f.domain === 'QQ' ? 'QQ' : f.domain;
    return [Poly.from(g, [x], { domain: dom }), Poly.from(h, [x], { domain: dom })];
  }
  return undefined;
}

function isRealConst(e: Expr): boolean {
  return !e.has(S.I);
}

function rationalOfFloat(f: Float): Rational {
  return rationalFromFloat(f.value);
}

/** The primitive integer polynomial of a monic univariate rational polynomial (positive leading coefficient). */
const primitiveIntPoly = (e: Expr, x: Expr): Poly => Poly.from(e, [x]).primitive()[1];

/** SymPy factor_list(expr) without `frac`: (content, [(factor, multiplicity)]). */
export type FactorList = [Expr, [Expr, Expr][]];
/** SymPy factor_list(expr, frac=True): (content, numerator factors, denominator factors). */
export type FactorListFrac = [Expr, [Expr, Expr][], [Expr, Expr][]];
/** Options of factorList (SymPy factor_list flags). */
export interface FactorListOptions {
  /** Factor the denominator too and return its factors as a third element (SymPy frac=True). */
  frac?: boolean;
}

/**
 * SymPy factor_list(f, *gens) on expressions: (content, [(factor, multiplicity)]).
 * The multiplicities are expressions: a power with a symbolic or fractional
 * exponent keeps it ((x + 1)**y -> (1, [(x + 1, y)])). Without gens every
 * non-rational part is a generator (sqrt(2), f(1), exp(y), ...); with gens the
 * factors are polynomials in them over the ring of the other parts, and the
 * parts free of the gens with an integer exponent make up the content. A
 * denominator is an error unless `frac` is set, which returns its factors as
 * a third element.
 */
export function factorListExpr(e: Expr, gens?: readonly Expr[], opts?: FactorListOptions & { frac?: false }): FactorList;
export function factorListExpr(e: Expr, gens: readonly Expr[] | undefined, opts: FactorListOptions & { frac: true }): FactorListFrac;
export function factorListExpr(e: Expr, gens?: readonly Expr[], opts?: FactorListOptions): FactorList | FactorListFrac;
export function factorListExpr(e: Expr, gens: readonly Expr[] = [], opts: FactorListOptions = {}): FactorList | FactorListFrac {
  const [numer, denom] = fraction(together(e));
  const [cp, fp] = symbolicFactorList(numer, gens);
  const [cq, fq] = symbolicFactorList(denom, gens);
  const frac = opts.frac === true;
  if (fq.length && !frac) throw new PolynomialError(`a polynomial expected, got ${str(e)}`);
  const content = mul(cp, pow(cq, -1));
  const numerFactors = sortedFactors(fp, gens);
  return frac ? [content, numerFactors, sortedFactors(fq, gens)] : [content, numerFactors];
}

/**
 * factorListExpr with integer multiplicities, for callers that factor
 * polynomials: a factor with another exponent is kept as the power.
 */
export function factorListInt(e: Expr, gens?: readonly Expr[]): [Expr, [Expr, number][]] {
  const [c, fs] = factorListExpr(e, gens);
  return [c, fs.map(([f, k]): [Expr, number] => (k instanceof Rational && k.isInteger ? [f, Number(k.p)] : [pow(f, k), 1]))];
}

/**
 * SymPy _generic_factor_list after _symbolic_factor_list: equal factors are
 * collected, each factor becomes a polynomial (expanded, in the gens when
 * given) and the list is sorted by _sorted_factors.
 */
function sortedFactors(fs: readonly SymbolicFactor[], fixed: readonly Expr[]): [Expr, Expr][] {
  const merged = new Map<string, SymbolicFactor>();
  for (const [f, k, key] of fs) {
    // (factors of different polynomial rings are different in SymPy)
    const id = `${key ? key[1] : 0}|${f.key}`;
    const cur = merged.get(id);
    if (cur) cur[1] = add(cur[1], k);
    else merged.set(id, [f, k, key]);
  }
  const keyed = [...merged.values()].map(([f, k, key]): [Expr, Expr, FactorKey] => {
    if (key) return [fixed.length ? Poly.from(f, fixed).asExpr() : f, k, [key[0], key[1], k, key[3], key[4]]];
    const pf = polify(f, fixed);
    if (!pf) {
      // SymPy _poly_from_expr(f, gens) fails on a part with a generator inside
      if (fixed.length) throw new PolynomialError(`${str(genPart(f, fixed) ?? f)} contains an element of the set of generators.`);
      return [f, k, ownKey(k)];
    }
    const pe = fixed.length ? Poly.from(f, fixed).asExpr() : xreplace(pf.expr, pf.back);
    const rep = denseRep(pf.expr, pf.gens);
    if (!Array.isArray(rep)) return [pe, k, [1, fixed.length, k, pf.domain, [rep]]];
    return [pe, k, [rep.length, fixed.length || pf.gens.length, k, pf.domain, rep]];
  });
  keyed.sort((a, b) => compareFactorKeys(a[2], b[2]));
  return keyed.map(([f, k]): [Expr, Expr] => [f, k]);
}

/** SymPy _sorted_factors key (method='factor'): (len(rep), len(gens), exp, str(domain), rep). */
type FactorKey = [number, number, Expr, string, DenseRep];
type DenseRep = Rational | DenseRep[];

/** The key of a factor that is not a polynomial (SymPy makes it a polynomial in itself). */
const ownKey = (k: Expr): FactorKey => [2, 1, k, 'ZZ', [S.One, S.Zero]];

function denseRep(e: Expr, gens: readonly Expr[]): DenseRep {
  const [g, ...rest] = gens;
  if (g === undefined) return asRational(e, 'polynomial coefficient');
  const cs = defined(polyCoefficients(e, g), 'polynomial in its generators');
  const n = Math.max(0, ...cs.keys());
  return Array.from({ length: n + 1 }, (_, i) => denseRep(cs.get(n - i) ?? S.Zero, rest));
}

function compareRep(a: DenseRep, b: DenseRep): number {
  if (!Array.isArray(a) || !Array.isArray(b)) {
    const d = asRational(sub(expectType(a, isRational, 'dense coefficient'), expectType(b, isRational, 'dense coefficient')), 'difference');
    return d.p < 0n ? -1 : d.p > 0n ? 1 : 0;
  }
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = compareRep(at(a, i), at(b, i));
    if (c) return c;
  }
  return a.length - b.length;
}

function compareFactorKeys(a: FactorKey, b: FactorKey): number {
  if (a[0] !== b[0]) return a[0] - b[0];
  if (a[1] !== b[1]) return a[1] - b[1];
  const e = compareExponents(a[2], b[2]);
  if (e) return e;
  if (a[3] !== b[3]) return a[3] < b[3] ? -1 : 1;
  return compareRep(a[4], b[4]);
}

/**
 * Multiplicities in numeric order. SymPy raises TypeError comparing a symbolic
 * exponent with another one (y < 2); symjs orders such pairs canonically.
 */
function compareExponents(a: Expr, b: Expr): number {
  if (a.key === b.key) return 0;
  const d = sub(a, b);
  if (d instanceof Rational) return d.p < 0n ? -1 : 1;
  return compareExpr(a, b);
}

const sub = (a: Expr, b: Expr): Expr => add(a, mul(-1, b));

/**
 * An expression as a polynomial (SymPy _poly_from_expr with greedy generators):
 * the expression in generator symbols, the generators (the given ones first,
 * then the others in SymPy's order), the map back to the original parts and
 * the domain name.
 */
interface Polified {
  expr: Expr;
  gens: Expr[];
  back: [Expr, Expr][];
  domain: string;
}

function polify(e: Expr, fixed: readonly Expr[]): Polified | undefined {
  const ex = expandFull(e);
  const found = new Map<string, [Expr, Expr]>(); // key of the original -> [original, generator]
  const fixedKeys = new Set(fixed.map((g) => g.key));
  const genOf = (b: Expr): Expr | undefined => {
    if (fixedKeys.has(b.key)) return b;
    // a coefficient cannot contain a generator (SymPy PolynomialError)
    if (fixed.some((g) => b.has(g))) return undefined;
    const cur = found.get(b.key);
    if (cur) return cur[1];
    const g = b instanceof Sym ? b : new Dummy('g');
    found.set(b.key, [b, g]);
    return g;
  };
  const terms: Expr[] = [];
  for (const t of ex instanceof Add ? ex.args : [ex]) {
    const fs: Expr[] = [];
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) {
        fs.push(f);
        continue;
      }
      if (f instanceof Float || !f.isCommutative) return undefined;
      let [b, k] = decomposePower(f);
      // a negative power is a generator of its own (1/x), not one of the gens (after together() only in exponents)
      if (k < 0) [b, k] = [pow(b, -1), -k];
      const g = genOf(b);
      if (g === undefined) return undefined;
      fs.push(pow(g, k));
    }
    terms.push(mul(...fs));
  }
  const others = sortGens([...found.values()].map(([o]) => o));
  const gens = [...fixed, ...others.map((o) => getOrThrow(found, o.key)[1])];
  const back = [...found.values()].filter(([o, g]) => o !== g).map(([o, g]): [Expr, Expr] => [g, o]);
  // the numerators of together() have integer coefficients
  const domain = fixed.length && others.length ? `ZZ[${others.map(str).join(',')}]` : 'ZZ';
  return { expr: add(...terms), gens, back, domain };
}

/** The first part of f that is not one of the gens but contains one (sin(x) in x + sin(x)). */
function genPart(f: Expr, fixed: readonly Expr[]): Expr | undefined {
  const keys = new Set(fixed.map((g) => g.key));
  const ex = expandFull(f);
  for (const t of ex instanceof Add ? ex.args : [ex]) {
    for (const u of t instanceof Mul ? t.args : [t]) {
      const [b] = decomposePower(u);
      if (!keys.has(b.key) && fixed.some((g) => b.has(g))) return b;
    }
  }
  return undefined;
}

/** A [factor, exponent] pair of symbolicFactorList with the sort key of polynomial factors. */
type SymbolicFactor = [Expr, Expr, FactorKey | undefined];

/** The polynomial factor f**k of a base raised to exp. */
function powered(f: Expr, k: Expr, exp: Expr, key: FactorKey): SymbolicFactor {
  const m = mul(k, exp);
  return [f, m, [key[0], key[1], m, key[3], key[4]]];
}

/**
 * SymPy _symbolic_factor_list: the numeric content and the [factor, exponent]
 * pairs of a product, each base factored as a polynomial in its generators.
 */
function symbolicFactorList(expr: Expr, fixed: readonly Expr[]): [Expr, SymbolicFactor[]] {
  let coeff: Expr = S.One;
  const factors: SymbolicFactor[] = [];
  for (const arg of expr instanceof Mul ? expr.args : [expr]) {
    if (isNum(arg) || isPureComplex(arg)) {
      coeff = mul(coeff, arg);
      continue;
    }
    let base: Expr = arg;
    let exp: Expr = S.One;
    if (arg instanceof Pow && !isE(arg.base)) {
      if (isNum(arg.base) && isNum(arg.exp)) {
        coeff = mul(coeff, arg);
        continue;
      }
      if (isNum(arg.base)) {
        factors.push([arg.base, arg.exp, undefined]);
        continue;
      }
      [base, exp] = [arg.base, arg.exp];
    }
    const pf = polify(base, fixed);
    if (!pf) {
      factors.push([base, exp, undefined]);
      continue;
    }
    const [r0, fs0] = factorListRaw(pf.expr, pf.gens);
    const ngens = fixed.length || pf.gens.length;
    // with gens, the factors free of them are elements of the ground domain (part of SymPy's _coeff)
    let c0: Expr = r0;
    const fs: [Expr, Expr, FactorKey][] = [];
    for (const [f0, k] of fs0) {
      const f = xreplace(f0, pf.back);
      if (fixed.length && !fixed.some((g) => f.has(g))) {
        c0 = mul(c0, pow(f, k));
        continue;
      }
      const rep = expectType(denseRep(f0, pf.gens), (r): r is DenseRep[] => Array.isArray(r), 'dense polynomial');
      fs.push([f, Rational.of(k), [rep.length, ngens, Rational.of(k), pf.domain, rep]]);
    }
    if (exp instanceof Rational && exp.isInteger) {
      coeff = mul(coeff, pow(c0, exp));
      for (const [f, k, key] of fs) factors.push(powered(f, k, exp, key));
      continue;
    }
    const c0Positive = isPositive(c0) === true;
    if (c0Positive && !(c0 instanceof Rational && c0.isOne)) factors.push([c0, exp, undefined]);
    if (isIntegerQ(exp) === true) {
      // an integer exponent goes to every factor (SymPy exp.is_integer)
      for (const [f, k, key] of fs) factors.push(powered(f, k, exp, key));
      if (!c0Positive) factors.push([c0, exp, undefined]);
      continue;
    }
    // a fractional or symbolic exponent: the positive factors get it one by one
    const other: Expr[] = c0Positive ? [] : [c0];
    for (const [f, k, key] of fs) {
      if (isPositive(f) === true) factors.push(powered(f, k, exp, key));
      else other.push(pow(f, k));
    }
    // (SymPy appends (1, exp) when every factor is positive, and then fails to make it a polynomial)
    if (other.length) factors.push([mul(...other), exp, undefined]);
  }
  return [coeff, factors];
}

const isE = (b: Expr): boolean => b instanceof Constant && b.name === 'E';
const isI = (e: Expr): boolean => e instanceof Constant && e.name === 'I';
const isGaussTerm = (e: Expr): boolean => isI(e) || (e instanceof Mul && e.args.length === 2 && isNum(at(e.args, 0)) && isI(at(e.args, 1)));
/** SymPy pure_complex: a + b*I with numbers a, b (I, 2*I, 1 + I, ...). */
const isPureComplex = (e: Expr): boolean => isGaussTerm(e) || (e instanceof Add && e.args.length === 2 && isNum(at(e.args, 0)) && isGaussTerm(at(e.args, 1)));

/** SymPy together(e, fraction=False): exp with a negative exponent is not a denominator. */
function togetherNoFraction(e: Expr): Expr {
  const reps: [Expr, Expr][] = [];
  const hidden = mapBottomUp(e, (t) => {
    if (!(t instanceof Pow && isE(t.base) && couldExtractMinusSign(t.exp))) return t;
    const d = new Dummy('e');
    reps.push([d, t]);
    return d;
  });
  return xreplace(together(hidden), reps);
}

/** SymPy factor on expressions (_symbolic_factor): the factors of the numerator and the denominator of together(e). */
function symbolicFactor(e: Expr, frac: boolean): Expr {
  const [c, fs] = symbolicFactorList(frac ? together(e) : togetherNoFraction(e), []);
  return keepCoeff(c, mul(...fs.map(([f, k]) => pow(f, k))));
}

function factorListRaw(e: Expr, vars: readonly Expr[]): [Rational, [Expr, number][]] {
  return mfactorList(e, vars, (p, x) => {
    // (polynomials in generator symbols with integer coefficients)
    const { content, factors } = defined(UPoly.fromExpr(p, x), 'univariate polynomial').factor();
    let c: Rational = content;
    const out: [Expr, number][] = [];
    for (const [f, k] of factors) {
      const prim = primitiveIntPoly(f.toExpr(x), x);
      // f = s * prim  => c *= s^k
      const s = mul(f.toExpr(x), pow(prim.asExpr(), -1));
      c = mulR(c, powR(asRational(cancel(s), 'factor scale'), k));
      out.push([prim.asExpr(), k]);
    }
    return [c, out];
  });
}

const mulR = (a: Rational, b: Rational): Rational => asRational(mul(a, b), 'product of rationals');
const powR = (a: Rational, k: number): Rational => asRational(pow(a, k), 'power of a rational');

// ---------------------------------------------------------------------------
// printing (SymPy StrPrinter._print_Poly)
// ---------------------------------------------------------------------------

function coeffStr(c: Expr): string {
  if (c instanceof Float) {
    const v = c.value;
    return Number.isInteger(v) ? `${v}.0` : `${Number(v.toPrecision(15))}`;
  }
  return str(c);
}

export function polyStr(p: Poly): string {
  const gens = p.gens.map((g) => {
    const s = str(g);
    return g instanceof Sym || g instanceof Constant || isNum(g) ? s : `(${s})`;
  });
  const terms: string[] = [];
  for (const [monom, coeff] of p.terms()) {
    const sm: string[] = [];
    monom.forEach((e, i) => {
      if (e > 0) sm.push(e === 1 ? at(gens, i) : `${at(gens, i)}**${e}`);
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
  const gf = /^GF\((\d+)\)$/.exec(p.domain);
  const dom = gf ? `modulus=${gf[1]}` : `domain='${p.domain}'`;
  return `${p.pure ? 'PurePoly' : 'Poly'}(${terms.join(' ')}, ${gensOut.join(', ')}, ${dom})`;
}

// ---------------------------------------------------------------------------
// top-level functions on expressions
// ---------------------------------------------------------------------------

const toExpr = (f: Poly | ExprLike): Expr => (f instanceof Poly ? f.asExpr() : sympify(f));
const varsFor = (...fs: Expr[]): Sym[] => {
  const m = new Map<string, Sym>();
  for (const f of fs) for (const s of freeSymbols(f)) m.set(s.key, s);
  return sortGens([...m.values()]);
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

/**
 * Division q, r with f = q*g + r (SymPy div), in the given generators or the free symbols;
 * multivariate polynomials are divided recursively in the first generator (SymPy dmp_div).
 */
export function polyDiv(f: Poly | ExprLike, g: Poly | ExprLike, gens?: readonly Expr[]): [Expr, Expr] {
  const a = toExpr(f);
  const b = toExpr(g);
  const v = gens ?? varsFor(a, b);
  if (v.length === 0) throw new PolynomialError('div: polynomials in some generator expected');
  const [q, r] = Poly.from(a, v).div(Poly.from(b, v));
  return [q.asExpr(), r.asExpr()];
}

/** terms_gcd: pull out the gcd of all terms (numeric content and common monomial). */
export function termsGcd(f: ExprLike, ...rest: (Sym | TermsGcdOptions)[]): Expr {
  const lastArg = rest[rest.length - 1];
  const opts: TermsGcdOptions = lastArg !== undefined && !(lastArg instanceof Expr) ? lastArg : {};
  const gens = rest.filter((g): g is Sym => g instanceof Expr);
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
    let c = S.One;
    const m = new Map<string, [Expr, number]>();
    for (const g of fs) {
      if (g instanceof Rational) {
        c = asRational(mul(c, g), 'product of rational coefficients');
        continue;
      }
      if (g.isNumber && !(g instanceof Pow) && !(g instanceof Constant)) return orig;
      let [b, k] = decomposePower(g);
      if (k < 0) {
        b = pow(b, -1);
        k = -k;
      }
      // distinct factors of a canonical product have distinct bases
      m.set(b.key, [b, k]);
    }
    terms.push([c, m]);
  }
  const t0 = first(terms);
  if (terms.length === 1 && t0[0].isZero) return S.Zero;
  // exponents common to all terms
  const J = new Map<string, [Expr, number]>();
  for (const [k, v] of t0[1]) J.set(k, [...v]);
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
  // num is nonzero: a single zero term was handled above
  const coeff = Rational.of(num, den);
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
  const [c2, f2] = kc instanceof Mul && kc.args[0] instanceof Rational ? [kc.args[0], mul(...kc.args.slice(1))] : [S.One, kc];
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
  const v = first(gens);
  const p = Poly.from(e, [v]);
  const multi = gens.length > 1;
  let acc: Expr = S.Zero;
  for (const c of p.allCoeffs()) acc = add(mul(acc, v), multi ? horner(c) : c);
  return acc;
}

const isPoint = (d: readonly [ExprLike, ExprLike] | ExprLike): d is readonly [ExprLike, ExprLike] => Array.isArray(d);

/** Lagrange interpolating polynomial through points (x_i, y_i) or y-values at 1..n. */
export function interpolate(data: readonly (readonly [ExprLike, ExprLike])[] | readonly ExprLike[], x: Sym): Expr {
  const items: readonly (readonly [ExprLike, ExprLike] | ExprLike)[] = data;
  const pts = items.map((d, i): [Expr, Expr] => (isPoint(d) ? [sympify(d[0]), sympify(d[1])] : [Rational.of(i + 1), sympify(d)]));
  const terms = pts.map(([xi, yi], i) =>
    mul(yi, ...pts.filter((_, j) => j !== i).map(([xj]) => mul(add(x, mul(-1, xj)), pow(add(xi, mul(-1, xj)), -1)))),
  );
  return expand(add(...terms));
}

/**
 * Resultant of two univariate polynomials by pseudo-remainder sequences:
 * Res(a, b) = (-1)**(da*db) * LC(b)**(da - dr) * Res(b, a mod b), with the
 * powers of LC(b) introduced by the pseudo-division divided out at the end
 * (no division by symbolic coefficients during the sequence).
 */
export function resultant(f: ExprLike, g: ExprLike, x: Sym): Expr {
  let a = Poly.from(f, [x]);
  let b = Poly.from(g, [x]);
  if (a.isZero || b.isZero) return S.Zero;
  let num: Expr = S.One;
  let den: Expr = S.One;
  for (;;) {
    const da = a.degree();
    const db = b.degree();
    if (db === 0) {
      num = mul(num, pow(b.LC(), da));
      break;
    }
    if (da < db) {
      if ((da * db) % 2 === 1) num = mul(-1, num);
      [a, b] = [b, a];
      continue;
    }
    // r = LC(b)**(da - db + 1) * (a mod b)
    const r = a.prem(b);
    if (r.isZero) return S.Zero;
    num = mul(num, pow(b.LC(), da - r.degree()), (da * db) % 2 === 1 ? -1 : 1);
    den = mul(den, pow(b.LC(), (da - db + 1) * db));
    a = b;
    b = r;
  }
  return expand(cancel(mul(num, pow(den, -1))));
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
  const [x] = vars;
  if (x === undefined || vars.length !== 1) throw new PolynomialError('factor: modulus requires a univariate polynomial');
  const cs = polyCoefficients(e, x);
  if (!cs) throw new DomainError('factor: modulus requires integer coefficients');
  const ints = new Map<number, bigint>();
  for (const [k, c] of cs) {
    if (!(c instanceof Rational && c.q === 1n)) throw new DomainError('factor: modulus requires integer coefficients');
    ints.set(k, c.p);
  }
  const n = Math.max(...cs.keys());
  const f = Array.from({ length: n + 1 }, (_, i) => ints.get(i) ?? 0n);
  const sym = (c: bigint) => (c > p / 2n ? c - p : c);
  const [lc, fs] = factorModP(f, p);
  const toExpr = (g: bigint[]) => add(...g.map((c, i) => mul(Rational.of(sym(c)), pow(x, i))));
  return keepCoeff(Rational.of(sym(lc)), mul(...fs.map(([g, m]) => pow(toExpr(g), m))));
}

export function factor(ex: ExprLike, opts: { deep?: boolean; extension?: readonly Expr[]; gaussian?: boolean; modulus?: number | bigint; fraction?: boolean } = {}): Expr {
  if (opts.modulus !== undefined) return factorModulus(sympify(ex), BigInt(opts.modulus));
  if (opts.gaussian || opts.extension?.length) {
    const r = factorOverExtension(sympify(ex), opts.gaussian ? [S.I] : defined(opts.extension, 'extension'));
    if (r) return r;
  }
  if (opts.deep) {
    // SymPy deep=True: factor bottom up (keeping the products and powers), then the sums and products inside
    const sub = { ...opts, deep: false };
    const tryFactor = (t: Expr): Expr => {
      if (t.args.length === 0) return t;
      const fac = factor(t, sub);
      return fac instanceof Mul || fac instanceof Pow ? fac : t;
    };
    // (SymPy's second pass over the sums and products finds nothing the bottom-up pass has not tried)
    return mapBottomUp(sympify(ex), tryFactor);
  }
  const e = sympify(ex);
  // SymPy: a PolynomialError for non-commutative expressions leads to factor_nc
  if (!e.isCommutative) return factorNc(e);
  return symbolicFactor(e, opts.fraction !== false);
}

/**
 * Factor a univariate polynomial with rational coefficients over Q(ext):
 * linear factors x - r for the roots r that lie in the extension (their
 * irrational parts are built from the generators only), the rest stays
 * as a factor over QQ.
 */
function factorOverExtension(e: Expr, ext: readonly Expr[]): Expr | undefined {
  const vars = [...freeSymbols(e)];
  const [x] = vars;
  if (x === undefined || vars.length !== 1) return undefined;
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
  for (const r of rs) {
    if (!inField(r)) continue;
    lin.push(add(x, mul(-1, r)));
  }
  if (!lin.length) return undefined;
  // the product of the linear factors is rational when the extension is closed under
  // conjugation; otherwise the cofactor has coefficients in the extension and is kept
  // (it has no roots there): factor(x**3 - 2, extension=2**(1/3)) = (x - 2**(1/3))*(x**2 + 2**(1/3)*x + 2**(2/3))
  const prod = Poly.from(expand(mul(...lin)), [x]);
  const rational = prod.domain === 'ZZ' || prod.domain === 'QQ';
  const rest = rational ? p.exquo(prod) : p.div(prod)[0];
  const lc = rest.LC();
  const monicRest = mul(rest.asExpr(), pow(lc, -1));
  const remaining = rest.degree() > 0 ? (rational ? factor(monicRest) : monicRest) : S.One;
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
  // a non-commutative node without non-commutative symbols (a Quaternion): its arguments are factored (SymPy factor_nc)
  if (!nc.length) return rebuild(e, e.args.map(factorNc));
  const reps = nc.map((s) => [s, new Sym(`_nc_${s.name}`)] as [Expr, Expr]);
  const f = factor(xreplace(e, reps));
  const back = xreplace(f, reps.map(([a, b]) => [b, a] as [Expr, Expr]));
  return expand(back).key === expand(e).key ? back : e;
}

/**
 * SymPy sqf_norm(f, extension): [s, g, r] with g(x) = f(x - s*a) for the
 * primitive element a (the sum of the extension generators) and r = norm(g)
 * square-free over QQ.
 */
export function sqfNorm(fIn: ExprLike, x: Sym, extension: readonly Expr[]): [number[], Expr, Expr] {
  const f = sympify(fIn);
  const a = add(...extension);
  const domain = `QQ<${str(a)}>`;
  for (let s = 0; s < 50; s++) {
    const g = expand(xreplace(f, [[x, add(x, mul(-s, a))]]));
    const r = Poly.from(g, [x], { domain }).norm();
    if (r.gcd(r.diff(x)).degree() <= 0) return [extension.map(() => s), g, r.asExpr()];
  }
  throw new NotImplementedError('sqf_norm: no square-free norm found');
}

impl.factor = (e) => factor(e);
polyHooks.factorList = (e) => factorListInt(e);

/**
 * SymPy PurePoly(expr, *gens): a polynomial whose generators are only
 * placeholders, so that polynomials over different generators compare equal
 * (PurePoly(x**2 + 1).equals(PurePoly(y**2 + 1))).
 */
export function PurePoly(ex: Poly | ExprLike, ...gens: Expr[]): Poly {
  return Poly.from(toExpr(ex), gens.length ? gens : ex instanceof Poly ? ex.gens : undefined, { pure: true });
}

/** e, or the PolynomialError of SymPy's Poly for a non-commutative expression. */
function commutativeOnly(e: Expr): Expr {
  if (!e.isCommutative) throw new PolynomialError('non-commutative expressions are not supported');
  return e;
}

/**
 * SymPy Expr.as_poly(*gens): e as a polynomial in gens (detected when not
 * given), or NoMatch when it is not one.
 */
export function asPoly(ex: ExprLike, ...gens: Expr[]): Poly | NoMatchResult {
  const e = sympify(ex);
  // SymPy's Poly raises PolynomialError for these (a non-commutative expression, or not a polynomial in gens)
  if (!e.isCommutative || (gens.length > 0 && !isPolynomial(e, gens))) return NoMatch;
  return Poly.from(e, gens.length ? gens : undefined);
}

/**
 * SymPy invert(f, g, *gens): the inverse of f modulo g (an integer modulo an
 * integer, or a polynomial modulo a polynomial); NotInvertible when f and g
 * have a common factor.
 */
export function invert(fIn: Poly | ExprLike, gIn: Poly | ExprLike, ...gens: Expr[]): Expr {
  const f = commutativeOnly(toExpr(fIn));
  const g = commutativeOnly(toExpr(gIn));
  if (f instanceof Rational && g instanceof Rational && f.isInteger && g.isInteger) return modInverse(f, g);
  const vars = gens.length ? gens : varsFor(f, g);
  if (vars.length !== 1) throw new PolynomialError(`invert: univariate polynomials expected, got ${str(f)} and ${str(g)}`);
  const gp = Poly.from(g, vars, { domain: 'QQ' });
  return Poly.from(f, vars, { domain: 'QQ' }).invert(gp).rem(gp).asExpr();
}

/** SymPy gcd_list(seq, *gens): the greatest common divisor of the items of seq (0 for none). */
export function gcdList(seq: readonly (Poly | ExprLike)[]): Expr {
  return seq.map(toExpr).reduce<Expr>((acc, f) => polyGcd(acc, f), S.Zero);
}

/** SymPy lcm_list(seq, *gens): the least common multiple of the items of seq (1 for none). */
export function lcmList(seq: readonly (Poly | ExprLike)[]): Expr {
  return seq.map(toExpr).reduce<Expr>((acc, f) => polyLcm(acc, f), S.One);
}

/**
 * SymPy sqf(f, *gens): the square-free factorization of f, the numerator and
 * the denominator of a rational function separately
 * (2*x**5 + 16*x**4 + ... -> 2*(x + 1)**2*(x + 2)**3).
 */
export function sqf(ex: Poly, ...gens: Expr[]): Poly;
export function sqf(ex: ExprLike, ...gens: Expr[]): Expr;
export function sqf(ex: Poly | ExprLike, ...gens: Expr[]): Expr | Poly {
  const [content, numer, denom] = factorListExpr(toExpr(ex), gens, { frac: true });
  const r = mul(content, sqfProduct(numer), pow(sqfProduct(denom), -1));
  // a polynomial gives a polynomial, as in SymPy
  return ex instanceof Poly ? Poly.from(r, ex.gens) : r;
}

/** The product of the square-free factors: the irreducible factors of each multiplicity multiplied out. */
function sqfProduct(factors: readonly [Expr, Expr][]): Expr {
  const groups = new Map<string, [Expr, Expr[]]>();
  for (const [f, k] of factors) {
    const g = groups.get(k.key);
    if (g) g[1].push(f);
    else groups.set(k.key, [k, [f]]);
  }
  return mul(...[...groups.values()].map(([k, fs]) => pow(fs.length === 1 ? first(fs) : expand(mul(...fs)), k)));
}
