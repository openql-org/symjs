// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Finite-domain polynomial operations ported from SymPy 1.14.0
// (polys/polytools.py, polys/densearith.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Poly: SymPy-compatible polynomial objects (generators, domain,
 * printing and the main polynomial API), plus top-level polynomial
 * functions (degree, LC/LM/LT, gcd, lcm, div, factor_list, ...).
 */

import { DomainError, ExactQuotientFailed, InvariantError, NotImplementedError, NotInvertible, PolynomialError, SympifyError } from '../core/errors';
import { parse } from '../parsing/parser';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { asContentPrimitive, asRealImag, isPolynomial } from '../core/methods';
import { at, defined, expectType, first, getOrThrow, pair } from '../core/guard';
import { isIntegerQ, isPositive, isReal } from '../core/assumptions';
import { factorModP } from './zassenhaus';
import type { ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Expr, ExtensionExpr, Float, Fn, Mul, Pow, Rational, Rel, S, Sym, compareExpr, impl, isNum } from '../core/nodes';
import { evalf as evalfExpr } from '../numeric/evalf';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, rebuild, some, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { str } from '../printing/str';
import { expand as expandFull, expandMul as expand } from '../simplify/expand';
import { sqrtdenest } from '../simplify/sqrtdenest';
import { cancel, fraction, together } from '../simplify/rational';
import { decomposePower, keepCoeff } from '../simplify/exprtools';
import { modInverse, rationalFromFloat } from '../core/numberutils';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { ordered as orderedExprs } from '../core/match';
import { divExact, ffDiv, mfactorList, mgcd, mlcm } from './mpoly';
import { countComplexRoots, isolateComplexRootsSqf, isolateRealRoots, isolateRealRootsSqf, isolateRealRootsTagged, refineRealRoot } from './rootisolation';
import { UPoly, polyCoefficients, polyHooks, preprocessRootCoefficients, roots as rootsOf } from './poly';
import { CoercionFailed, EX, QQ, ZZ, groundRational } from './domains';
import type { Domain } from './domains';
import { GeneratorsError, GeneratorsNeeded, MultivariatePolynomialError, OptionError, UnificationFailed } from './polyerrors';
import { gfDiv, gfFactor, gfFactorSqf, gfGcd, gfLcm, gfGcdex, gfQuoGround, gfSqfList, gfSqfPart } from './galoistools';
import { isprime } from '../ntheory/primetest';
import { fact } from '../core/exprfacts';
import { FieldPoly } from './fieldpoly';
import { algebraicEnclosure, compareAlgebraicReal } from './numberfields/interval';
import { MPContext } from './domains/mpelements';

/** Coefficient-domain options shared by polynomial construction and operations. */
export interface PolynomialDomainOptions {
  domain?: string | Domain;
  modulus?: number | bigint;
  symmetric?: boolean;
  /** An algebraic extension of QQ to compute over (SymPy extension=...). */
  extension?: boolean | ExprLike | readonly ExprLike[];
}

/** Construction options for algebraic and Gaussian coefficient domains. */
export interface PolyConstructionOptions extends PolynomialDomainOptions {
  /** Prefer a field: QQ over ZZ, QQ_I over ZZ_I, ZZ(x) over ZZ[x] or QQ[x] (SymPy field=True). */
  field?: boolean;
  extension?: boolean | ExprLike | readonly ExprLike[];
  gaussian?: boolean;
  pure?: boolean;
}
/** Options of Poly.intervals: the real bounds of the roots and the fast refinement of SymPy. */
export interface IntervalsOptions {
  inf?: Rational;
  sup?: Rational;
  fast?: boolean;
}
/** Domain construction is registered by polys/constructor, which depends on Poly. @internal */
export const polyConstructionHooks: {
  domain?: (coeffs: readonly Expr[], opts: PolyConstructionOptions) => Domain;
  algebraic?: (K: Domain) => { generator: Expr; minpoly: Poly; coefficients: (c: Expr) => Rational[] };
} = {};

/** The field a constructed domain prefers with field=True (SymPy: QQ, QQ_I, the fraction field ZZ(x) of ZZ[x] or QQ[x]). */
function fieldDomainName(name: string): string {
  if (name === 'ZZ') return 'QQ';
  if (name === 'ZZ_I') return 'QQ_I';
  const m = /^(?:ZZ|QQ)\[(.*)\]$/.exec(name);
  return m ? `ZZ(${at(m, 1)})` : name;
}

/** Resolve a positive modulus while preserving SymPy's mutually exclusive options. */
function modulusOption(opts: PolynomialDomainOptions): bigint | undefined {
  if (opts.modulus !== undefined && opts.domain !== undefined) throw new OptionError("'modulus' option is not allowed together with 'domain'");
  const match = /^GF\((\d+)\)$/.exec(String(opts.domain));
  const p = opts.modulus === undefined ? (match ? BigInt(at(match, 1)) : undefined) : BigInt(opts.modulus);
  if (p !== undefined && p <= 0n) throw new RangeError('modulus must be positive');
  return p;
}

/** Candidate shifts for Trager norms, followed by complete integer shells. */
function* algebraicNormShifts(degrees: readonly number[]): Generator<number[],never> {
  const n=degrees.length;
  yield Array<number>(n).fill(0);
  for(const i of Array.from({length:n},(_,j)=>j).filter((j)=>at(degrees,j)>0).sort((a,b)=>at(degrees,a)-at(degrees,b)||a-b)){
    const s=Array<number>(n).fill(0);s[i]=1;yield s;
  }
  function* shell(prefix:number[],j:number):Generator<number[]>{
    if(prefix.length===n){if(prefix.includes(j)&&!prefix.every((v)=>v===j))yield prefix;return;}
    for(let i=0;i<=j;i++)yield* shell([...prefix,i],j);
  }
  for(let j=1;;j++){yield Array<number>(n).fill(j);yield* shell([],j);}
}

/** The requested coefficient presentation, or the supplied domain default. */
function finiteSymmetricOption(opts:PolynomialDomainOptions):boolean {
  return opts.symmetric ?? (typeof opts.domain === 'object' && 'symmetric' in opts.domain && typeof opts.domain.symmetric === 'boolean' ? opts.domain.symmetric : true);
}

/** An integer representative of Z/pZ in the requested presentation. */
function finiteCoefficient(c: Expr, p: bigint, symmetric = true): Rational {
  const value = groundRational(c);
  if (value === undefined || value[1] !== 1n) throw new CoercionFailed(`expected an integer coefficient, got ${str(c)}`);
  const r = (value[0] % p + p) % p;
  return Rational.of(symmetric && r > p/2n ? r-p : r);
}


const finiteInverse = (c: bigint, p: bigint): bigint => first(gfQuoGround([1n], c, p));

const isRational = (x: unknown): x is Rational => x instanceof Rational;
/** x as a Rational; throws InvariantError when the algorithm's guarantee that it is one fails. */
const asRational = (x: Expr, what: string): Rational => expectType(x, isRational, what);

/** The expression cannot be written as a polynomial in the generators (SymPy PolificationFailed). */
/** Numeric roots and CRootOf, registered by polys/nroots and polys/rootof (which import this module). @internal */
export const rootHooks: { nroots?: (f: Poly, n: number) => Expr[]; crootof?: (e: Expr, i: number) => Expr } = {};

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
    // a + b*I with rational or floating-point a, b
    const parts = c instanceof Add ? c.args : [c];
    let ok = true;
    for (const p of parts) {
      const [k, r] = p instanceof Mul && (p.args[0] instanceof Rational || p.args[0] instanceof Float) ? [p.args[0], p.args.length === 2 ? at(p.args, 1) : new Mul(p.args.slice(1))] : [S.One, p];
      if (r instanceof Constant && r.name === 'I') {
        complex = true;
        if (k instanceof Float) real = true;
        else if (!k.isInteger) rational = true;
      } else if (p instanceof Float) real = true;
      else if (p instanceof Rational) {
        if (!p.isInteger) rational = true;
      } else ok = false;
    }
    if (!ok) return undefined;
  }
  if (real) return complex ? 'CC' : 'RR';
  if (complex) return rational ? 'QQ_I' : 'ZZ_I';
  return rational ? 'QQ' : 'ZZ';
}

/** The ground domain of the coefficients (SymPy construct_domain): ZZ, QQ, RR, ZZ_I, ZZ[x], ZZ(x), EX. */
export function inferDomain(cs: Expr[]): string {
  const nd = numberDomain(cs);
  if (nd) return nd;
  const syms = new Map<string, Sym>();
  for (const c of cs) for (const s of [...freeSymbols(c)].filter((s) => s instanceof Sym)) syms.set(s.key, s);
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

/** Combine positive rational bases of roots of the same index to detect exact cancellation. */
function combineRationalRadicals(e: Expr): Expr {
  if (!(e instanceof Mul)) return e;
  const roots = new Map<bigint, Rational>();
  const others: Expr[] = [];
  for (const factor of e.args) {
    if (factor instanceof Pow && factor.base instanceof Rational && factor.base.isPositive
        && factor.exp instanceof Rational && !factor.exp.isInteger) {
      const { p, q } = factor.exp;
      const power = asRational(pow(factor.base, Rational.of(p)), 'rational radicand');
      roots.set(q, mulR(roots.get(q) ?? S.One, power));
    } else {
      others.push(factor);
    }
  }
  if (!roots.size) return e;
  return mul(...others, ...[...roots].map(([q, base]) => pow(base, Rational.of(1n, q))));
}

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

  /** Free symbols of a polynomial; PurePoly binds its generators. */
  freeSymbols(): Set<Expr> {
    return this.pure ? this.freeSymbolsInDomain : freeSymbols(this.asExpr());
  }

  get gen(): Expr { return first(this.gens); }
  get freeSymbolsInDomain(): Set<Sym> {
    const symbols = new Map<string, Sym>();
    for (const { coeff } of this.termList) for (const s of [...freeSymbols(coeff)].filter((s) => s instanceof Sym)) symbols.set(s.key, s);
    return new Set(symbols.values());
  }
  get isGround(): boolean { return this.totalDegree() <= 0; }
  get isHomogeneous(): boolean {
    return this.termList.every((t) => t.monom.reduce((a, b) => a + b, 0) === this.totalDegree());
  }
  get isLinear(): boolean { return this.totalDegree() <= 1; }
  get isQuadratic(): boolean { return this.totalDegree() <= 2; }
  get isMonic(): boolean { return this.LC().equals(S.One); }
  get isMonomial(): boolean { return this.termList.length <= 1; }
  get isMultivariate(): boolean { return this.gens.length > 1; }
  get isUnivariate(): boolean { return this.gens.length === 1; }
  get isOne(): boolean { return this.isGround && this.LC().equals(S.One); }
  get isPrimitive(): boolean { return this.content().equals(S.One); }
  get isIrreducible(): boolean {
    // As in SymPy, content is ignored; nonzero ground polynomials have no
    // nonconstant factors. Zero is excluded: it is divisible by every polynomial.
    if (this.isGround) return !this.isZero;
    const [, factors] = this.factorList();
    return factors.length === 1 && first(factors)[1] === 1;
  }
  get isSqf(): boolean {
    // SymPy 1.14 calls zero square-free, but x**2 divides zero. Keep the
    // mathematical predicate false instead of treating an empty factor list as proof.
    if (this.isZero) return false;
    let g: Poly = this;
    for (const x of this.gens) g = g.gcd(this.diff(x));
    return g.isGround;
  }

  /** SymPy dup_cyclotomic_p: split even/odd powers and recurse on degree. */
  get isCyclotomic(): boolean {
    if (!this.isUnivariate || this.isGround || !['ZZ', 'QQ'].includes(this.domain)) return false;
    const cs = this.allCoeffs();
    if (!cs.every((c) => c instanceof Rational && c.isInteger) || !this.isMonic || !this.isIrreducible) return false;
    const tc = this.coeffMonomial([0]);
    if (!tc.equals(S.One) && !tc.equals(S.NegOne)) return false;
    const x = this.gen;
    const part = (parity: number): Poly => Poly.from(add(...this.termList.filter((t) => first(t.monom) % 2 === parity).map((t) => mul(t.coeff, pow(x, Math.floor(first(t.monom) / 2))))), [x]);
    const g = part(this.degree() % 2), h = part(1 - this.degree() % 2);
    const f = g.mul(g).sub(h.mul(h).mul(x)).monic();
    if (f.asExpr().equals(this.asExpr())) return true;
    const mirror = Poly.from(xreplace(this.asExpr(), [[x, mul(-1, x)]]), [x]).monic();
    if (f.asExpr().equals(mirror.asExpr())) return mirror.isCyclotomic;
    const s = f.sqfPart();
    return s.mul(s).asExpr().equals(f.asExpr()) && s.isCyclotomic;
  }

  private constructor(gens: readonly Expr[], terms: Term[], domain: string, pure = false, private readonly coefficientDomain?: Domain, private readonly finiteSymmetric = true) {
    this.gens = gens;
    this.termList = terms.sort((a, b) => monomCmp(b.monom, a.monom));
    this.domain = domain;
    this.pure = pure;
  }

  /** Build from exponent tuples and coefficients (SymPy Poly.from_dict). */
  static fromDict(terms: ReadonlyMap<readonly number[], ExprLike>, gens: readonly Expr[], opts: PolyConstructionOptions & { composite?: boolean } = {}): Poly {
    if (!gens.length) throw new GeneratorsNeeded('polynomial generators are required');
    for (const m of terms.keys()) {
      if (m.length !== gens.length || m.some((e) => !Number.isInteger(e) || e < 0)) throw new PolynomialError('invalid polynomial monomial');
    }
    const p = Poly.from(add(...[...terms].map(([m, c]) => mul(c, ...m.map((e, i) => pow(at(gens, i), e))))), gens, opts);
    return opts.composite === false && /^(?:ZZ|QQ)[[(]/.test(p.domain) ? p.setDomain('EX') : p;
  }

  /** Construct from an expression, requiring at least one generator. */
  static fromExpr(expr: ExprLike | string, gens?: readonly Expr[], opts: PolyConstructionOptions = {}): Poly {
    const parsed = typeof expr === 'string' ? parse(expr, { evaluate: false }) : expr;
    const p = Poly.from(parsed, gens, opts);
    if (p.gens.length) return p;
    if (typeof expr === 'string') {
      const formalGens = sortGens([...freeSymbols(sympify(parsed))]);
      if (formalGens.length) return Poly.from(parsed, formalGens, opts);
    }
    throw new GeneratorsNeeded('polynomial generators are required');
  }

  /** The coefficient domain, including its generators and defining relations. */
  getDomain(): Domain {
    return this.coefficientDomain ?? defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: this.domain });
  }

  /** Change the coefficient domain, converting each coefficient in that domain. */
  setDomain(domain: string | Domain): Poly {
    if (this.finiteModulus !== undefined && String(domain) !== this.domain) throw new CoercionFailed('cannot convert a finite-field polynomial to characteristic zero');
    const K = typeof domain === 'string' ? domain === 'EX' ? EX : defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain }) : domain;
    if (K.symbols.some((s) => this.gens.some((g) => g.key === s.key))) throw new GeneratorsError('coefficient domain and polynomial generators overlap');
    return Poly.from(this.asExpr(), this.gens, { domain: K, pure: this.pure });
  }

  /** Equality with an optional strict comparison of coefficient domains. */
  eq(other: Poly | ExprLike, opts: { strict?: boolean } = {}): boolean {
    if (!(other instanceof Poly)) return opts.strict !== true && this.equals(other);
    if (opts.strict && this.pure !== other.pure) return false;
    return (this.pure && !opts.strict || this.domain === other.domain) && this.equals(other);
  }
  ne(other: Poly | ExprLike, opts: { strict?: boolean } = {}): boolean {
    return !this.eq(other, opts);
  }

  /** Retain terms whose exponent in gen belongs to [start, stop). */
  slice(start: number, stop: number, gen: Expr = first(this.gens)): Poly {
    const i = this.genIndex(gen);
    return new Poly(this.gens, this.termList.filter((t) => at(t.monom, i) >= start && at(t.monom, i) < stop).map((t) => ({ monom: [...t.monom], coeff: t.coeff })), this.domain, this.pure, this.coefficientDomain, this.finiteSymmetric);
  }

  /** Build a univariate polynomial from descending coefficients (SymPy from_list). */
  static fromList(coeffs: readonly ExprLike[], gens: readonly Expr[], opts: PolyConstructionOptions = {}): Poly {
    if (gens.length !== 1) throw new PolynomialError('from_list requires exactly one generator');
    return Poly.from(add(...coeffs.map((c, i) => mul(c, pow(first(gens), coeffs.length - i - 1)))), gens, opts);
  }

  /** Recast a polynomial in new generators or a different coefficient domain. */
  static fromPoly(poly: Poly, gens: readonly Expr[] = poly.gens, opts: PolyConstructionOptions = {}): Poly {
    const same = gens.length === poly.gens.length && gens.every((g) => poly.gens.some((h) => h.key === g.key));
    if (same && poly.finiteModulus !== undefined && String(opts.domain) === 'QQ') throw new CoercionFailed('cannot convert finite-field coefficients to QQ');
    const domain = same && opts.modulus === undefined && opts.field === undefined && opts.extension === undefined
      ? poly.coefficientDomain ?? poly.domain : undefined;
    return Poly.from(poly.asExpr(), gens, { domain, symmetric: poly.finiteSymmetric, pure: poly.pure, ...opts });
  }

  /** Build a polynomial; generators are detected unless given. */
  static from(ex: ExprLike, gens?: readonly Expr[], opts: PolyConstructionOptions = {}): Poly {
    const modulus = modulusOption(opts);
    const requestedDomain = opts.domain === undefined ? undefined : String(opts.domain);
    if (opts.domain !== undefined && opts.field !== undefined) throw new OptionError("'field' option is not allowed together with 'domain'");
    const e = expand(sympify(ex));
    // over RR the generators are the symbols (numbers such as sqrt(3) become coefficients)
    const real = requestedDomain === 'R' || requestedDomain === 'RR' || requestedDomain === 'CC';
    const algebraicDomain = /^(?:ZZ|QQ)(?:_I|<)/.test(requestedDomain ?? '');
    const algebraic = opts.extension !== undefined || opts.gaussian === true || algebraicDomain;
    const gs = gens?.length ? [...gens] : real ? sortGens([...freeSymbols(e)].filter((s) => s instanceof Sym)) : detectGens(e).filter((g) => !algebraic || freeSymbols(g).size > 0);
    if (new Set(gs.map((g) => g.key)).size !== gs.length) throw new GeneratorsError('duplicated polynomial generators');
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
        if (gs.some((g) => f.has(g) && (!(g instanceof Sym) || [...freeSymbols(f)].some((s)=>s.key===g.key)))) throw new PolificationFailed(`${str(e)} is not a polynomial in ${gs.map(str).join(', ')}`);
        rest.push(f);
      }
      const k = monom.join(',');
      const c = mul(...rest);
      const cur = terms.get(k);
      if (cur) cur.coeff = add(cur.coeff, c);
      else terms.set(k, { monom, coeff: c });
    }
    const list = [...terms.values()]
      .map((t) => ({ monom: t.monom, coeff: gs.length && !isNum(t.coeff) ? expand(t.coeff) : t.coeff }))
      .filter(({ coeff }) => !(coeff instanceof Rational && coeff.isZero));
    if (opts.extension !== undefined || opts.gaussian !== undefined || algebraicDomain) {
      const K = defined(polyConstructionHooks.domain, 'polynomial domain construction')(list.map((t) => t.coeff), opts);
      const converted = list.map((t) => ({ monom: t.monom, coeff: K.fromSympy(t.coeff) }));
      return new Poly(gs, converted.filter((t) => !t.coeff.equals(0)), String(K), opts.pure ?? false, K);
    }
    if (modulus !== undefined) {
      const symmetric = finiteSymmetricOption(opts);
      const finite = list.map((t) => ({ monom: t.monom, coeff: finiteCoefficient(t.coeff, modulus, symmetric) })).filter((t) => !t.coeff.isZero);
      return new Poly(gs, finite, `GF(${modulus})`, opts.pure ?? false, undefined, symmetric);
    }
    if (real) {
      // floating-point coefficients
      const real = list.map((t) => ({ monom: t.monom, coeff: impl.evalf(t.coeff, 15) }));
      return new Poly(gs, real, requestedDomain === 'CC' ? 'CC' : 'RR', opts.pure ?? false);
    }
    if (requestedDomain === 'ZZ' || requestedDomain === 'QQ') {
      const K = requestedDomain === 'ZZ' ? ZZ : QQ;
      return new Poly(gs, list.map((t) => ({ monom: t.monom, coeff: K.fromSympy(t.coeff) })), requestedDomain, opts.pure ?? false);
    }
    const composite = /^(ZZ|QQ)([[(])([A-Za-z_0-9, ]+)[\])]$/.exec(requestedDomain ?? '');
    const names = composite ? at(composite, 3).split(',').map((s) => s.trim()) : [];
    const atoms = names.length ? [...freeSymbols(e)] : [];
    const domainGens = names.map((name) => atoms.find((v) => v instanceof Sym && v.name === name) ?? parse(name));
    const K = typeof opts.domain === 'object' ? opts.domain : composite && domainGens.every((g) => g instanceof Sym)
      ? (at(composite, 1) === 'ZZ' ? ZZ : QQ)[at(composite, 2) === '[' ? 'polyRing' : 'fracField'](...domainGens)
      : undefined;
    if (K !== undefined) {
      if (K.symbols.some((s) => gs.some((g) => g.key === s.key))) throw new GeneratorsError('coefficient domain and polynomial generators overlap');
      return new Poly(gs, list.map((t) => ({ monom: t.monom, coeff: K.fromSympy(t.coeff) })).filter((t) => !t.coeff.equals(0)), String(K), opts.pure ?? false, K);
    }
    const inferred = requestedDomain ?? inferDomain(list.length ? list.map((t) => t.coeff) : [S.Zero]);
    const domain = opts.field === true && requestedDomain === undefined ? fieldDomainName(inferred) : inferred;
    const nonzero = list.filter(({ coeff }) => !(coeff instanceof Add && mapBottomUp(coeff, combineRationalRadicals).equals(S.Zero)));
    return new Poly(gs, nonzero, domain, opts.pure ?? false);
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
    if (other instanceof Poly && (this.finiteModulus !== undefined || other.finiteModulus !== undefined) && this.domain !== other.domain) return false;
    let g = other instanceof Poly ? other : asPoly(other, ...this.gens);
    if (isNoMatch(g)) return false;
    if (!(other instanceof Poly) && this.finiteModulus !== undefined) {
      if (g.termList.some((t) => groundRational(t.coeff)?.[1] !== 1n)) return false;
      g = this.like(g.asExpr(),g.gens);
    }
    if (this.pure ? this.gens.length !== g.gens.length : this.gens.length !== g.gens.length || this.gens.some((x, i) => x.key !== at(g.gens, i).key)) return false;
    if (this.termList.length !== g.termList.length) return false;
    return this.termList.every((t, i) => {
      const u = at(g.termList, i);
      return monomCmp(t.monom, u.monom) === 0 && (this.finiteModulus === undefined ? t.coeff.key === u.coeff.key : finiteCoefficient(add(t.coeff,mul(-1,u.coeff)),this.finiteModulus).isZero);
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
    const modulus=this.finiteModulus,K=this.algebraicField ?? (modulus===undefined?undefined:defined(polyConstructionHooks.domain,'polynomial domain construction')([],{domain:this.domain}));
    const leaf=(r:unknown):Expr=>{
      const value=K===undefined?sympifyLeaf(r):K.toSympy(K.convert(r));
      return modulus===undefined?value:finiteCoefficient(value,modulus,this.finiteSymmetric);
    };
    const walk = (r: unknown, level: number, prefix: number[]): void => {
      if (level === gens.length) {
        const c = leaf(r);
        if (!(c instanceof Rational && c.isZero)) terms.push({ monom: prefix, coeff: c });
        return;
      }
      if (!Array.isArray(r)) throw new PolynomialError('per: dense representation nested less deeply than the generators');
      const list: readonly unknown[] = r;
      list.forEach((x, i) => walk(x, level + 1, [...prefix, list.length - 1 - i]));
    };
    if (!gens.length) return leaf(rep.length ? rep[0] : 0);
    walk(rep, 0, []);
    return new Poly(gens, terms, this.domain, this.pure, this.coefficientDomain, this.finiteSymmetric);
  }

  /** [(monomial, coefficient)] in the selected monomial order. */
  terms(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): [number[], Expr][] {
    if (this.isZero) return [[this.gens.map(() => 0), S.Zero]];
    return this.orderedTerms(opts).map((t) => [t.monom, t.coeff]);
  }
  coeffs(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): Expr[] {
    return this.terms(opts).map(([, c]) => c);
  }
  monoms(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): number[][] {
    return this.terms(opts).map(([m]) => m);
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
  /** Terms ordered by the selected admissible monomial ordering. */
  private orderedTerms(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): readonly Term[] {
    const order = opts.order ?? 'lex';
    if (order === 'lex') return this.termList;
    const degree = (m: readonly number[]) => m.reduce((s, e) => s + e, 0);
    return [...this.termList].sort((a, b) => degree(b.monom) - degree(a.monom) || (order === 'grlex' ? monomCmp(b.monom, a.monom) : monomCmp([...a.monom].reverse(), [...b.monom].reverse())));
  }
  LC(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): Expr {
    return this.orderedTerms(opts)[0]?.coeff ?? S.Zero;
  }
  LM(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): Expr {
    const t = this.orderedTerms(opts)[0];
    return t ? mul(...t.monom.map((k, i) => pow(at(this.gens, i), k))) : S.One;
  }
  LT(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): [number[], Expr] {
    const t = this.orderedTerms(opts)[0];
    return t ? [t.monom, t.coeff] : [this.gens.map(() => 0), S.Zero];
  }
  /** The trailing monomial and coefficient in the selected ordering. */
  ET(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): [number[], Expr] {
    const t = this.orderedTerms(opts).at(-1);
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
    if (o instanceof Poly && (this.gens.length !== o.gens.length || this.gens.some((g, i) => g.key !== o.gens[i]?.key))) {
      const [f, g] = this.unify(o);
      return f.add(g);
    }
    if(o instanceof Poly && this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.add(b);}
    const finite = this.finitePair(o);
    if (finite) return finite[0].like(add(finite[0].asExpr(), finite[1].asExpr()));
    const K = this.algebraicField;
    if (K) return this.like(this.fieldPoly(K).add(this.like(toExpr(o)).fieldPoly(K)).asExpr(this.gens));
    return this.coefficientDomain?.isFiniteExtension ? this.like(add(this.asExpr(), toExpr(o))) : Poly.from(add(this.asExpr(), toExpr(o)), this.gens);
  }
  sub(o: Poly | ExprLike): Poly {
    if (o instanceof Poly && (this.gens.length !== o.gens.length || this.gens.some((g, i) => g.key !== o.gens[i]?.key))) {
      const [f, g] = this.unify(o);
      return f.sub(g);
    }
    if(o instanceof Poly && this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.sub(b);}
    const finite = this.finitePair(o);
    if (finite) return finite[0].like(add(finite[0].asExpr(), mul(-1, finite[1].asExpr())));
    const K = this.algebraicField;
    if (K) return this.like(this.fieldPoly(K).sub(this.like(toExpr(o)).fieldPoly(K)).asExpr(this.gens));
    const expression = add(this.asExpr(), mul(-1, toExpr(o)));
    return this.coefficientDomain?.isFiniteExtension ? this.like(expression) : Poly.from(expression, this.gens);
  }
  mul(o: Poly | ExprLike): Poly {
    if(o instanceof Poly && this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.mul(b);}
    const finite = this.finitePair(o);
    if (finite) return finite[0].like(mul(finite[0].asExpr(), finite[1].asExpr()));
    const K = this.algebraicField;
    if (K && (!(o instanceof Poly) || !['RR','CC'].includes(o.domain))) return this.like(this.fieldPoly(K).mul(this.like(toExpr(o)).fieldPoly(K)).asExpr(this.gens));
    const [f, g] = this.unify(o instanceof Poly ? o : Poly.from(o, this.gens));
    return Poly.from(mul(f.asExpr(), g.asExpr()), f.gens, { domain: f.coefficientDomain ?? f.domain });
  }
  pow(n: number): Poly {
    if (this.finiteModulus !== undefined || this.algebraicField !== undefined || this.coefficientDomain?.isFiniteExtension) return this.like(pow(this.asExpr(), n));
    return Poly.from(pow(this.asExpr(), n), this.gens);
  }
  neg(): Poly {
    if (this.finiteModulus !== undefined || this.algebraicField !== undefined || this.coefficientDomain?.isFiniteExtension) return this.like(mul(-1, this.asExpr()));
    return Poly.from(mul(-1, this.asExpr()), this.gens);
  }

  private univariate(): Sym {
    const g = this.gens[0];
    if (this.gens.length !== 1 || !(g instanceof Sym)) throw new PolynomialError('univariate polynomial in a symbol expected');
    return g;
  }

  private get finiteModulus(): bigint | undefined { return modulusOption({ domain: this.domain }); }
  private get algebraicField(): Domain | undefined {
    return /^QQ(?:<.*>|_I)$/.test(this.domain) ? this.coefficientDomain ?? defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: this.domain }) : undefined;
  }
  private fieldPoly(K: Domain): FieldPoly { return new FieldPoly(K, this.gens.length, this.termList.map((t) => [t.monom,t.coeff])); }

  /** Unify generators only after checking that both operands have the same finite coefficient domain. */
  private finitePair(other: Poly | ExprLike): [Poly, Poly, bigint] | undefined {
    const p = this.finiteModulus;
    if (p === undefined) {
      if (other instanceof Poly && other.finiteModulus !== undefined) throw new UnificationFailed(`Cannot unify ${this.domain} with ${other.domain}`);
      return undefined;
    }
    if (other instanceof Poly && other.domain !== this.domain) throw new UnificationFailed(`Cannot unify ${this.domain} with ${other.domain}`);
    const gens = [...this.gens];
    const additions = other instanceof Poly ? other.gens : [...freeSymbols(sympify(other))];
    for (const g of additions) if (!gens.some((h) => h.key === g.key)) gens.push(g);
    try {
      return [this.like(this.asExpr(),gens), this.like(toExpr(other),gens), p];
    } catch (error) {
      if (error instanceof CoercionFailed) throw new UnificationFailed(error.message);
      throw error;
    }
  }

  /** Dense coefficients for the univariate finite-field algorithms. */
  private finiteDense(): bigint[] {
    if (this.gens.length !== 1) throw new NotImplementedError('multivariate polynomials over finite fields');
    return this.isZero ? [] : this.allCoeffs().map((c) => asRational(c, 'finite coefficient').p);
  }
  private fromFiniteDense(cs: readonly bigint[]): Poly {
    const x = first(this.gens);
    return this.like(add(...cs.map((c,i) => mul(Rational.of(c), pow(x, cs.length-1-i)))));
  }

  /** Recursive division over GF(p)[remaining generators] (SymPy dmp_ff_div). */
  private finiteDivMulti(g: Poly): [Poly, Poly] {
    let q = this.like(0), r: Poly = this;
    const x = first(this.gens), rest = this.gens.slice(1), dg = g.degree();
    const leading = (f: Poly): Poly => this.like(add(...f.termList
      .filter((t) => first(t.monom) === f.degree())
      .map((t) => mul(t.coeff, ...t.monom.slice(1).map((e,i) => pow(at(rest,i),e))))), rest);
    const lc = leading(g);
    while (!r.isZero && r.degree() >= dg) {
      const [c, rem] = leading(r).div(lc);
      // A coefficient remainder stops division in the main generator.
      if (!rem.isZero) break;
      const term = this.like(mul(c.asExpr(), pow(x,r.degree()-dg)));
      q = q.add(term);
      r = r.sub(term.mul(g));
    }
    return [q, r];
  }

  /** Division with remainder (univariate over the field of fractions). */
  div(o: Poly): [Poly, Poly] {
    if(o instanceof Poly && this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.div(b);}
    const finite = this.finitePair(o);
    if (finite) {
      const [a, b, p] = finite;
      if (b.isZero) throw new RangeError('polynomial division by zero');
      if (a.gens.length !== 1) return a.finiteDivMulti(b);
      const [q, r] = gfDiv(a.finiteDense(), b.finiteDense(), p);
      return [a.fromFiniteDense(q), a.fromFiniteDense(r)];
    }
    const K = this.algebraicField ?? (this.coefficientDomain?.isFiniteExtension && this.coefficientDomain.isField ? this.coefficientDomain : undefined);
    if (K) {
      const [q,r] = this.fieldPoly(K).div(this.like(o.asExpr()).fieldPoly(K));
      return [this.like(q.asExpr(this.gens)),this.like(r.asExpr(this.gens))];
    }
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
    const qp = Poly.from(add(...q), [x]);
    const rp = Poly.from(r, [x]);
    const dom = fieldDomainName(this.domain === o.domain ? this.domain : inferDomain([...qp.coeffs(), ...rp.coeffs()]));
    const domain = dom === this.domain ? this.coefficientDomain ?? dom : dom;
    return [Poly.from(qp.asExpr(), [x], { domain }), Poly.from(rp.asExpr(), [x], { domain })];
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
    if (this.domain === 'ZZ_I' && o.domain === 'ZZ_I') {
      const [q, r] = this.setDomain('QQ_I').div(o.setDomain('QQ_I'));
      try { return [q.setDomain('ZZ_I'), r.setDomain('ZZ_I')]; }
      catch (error) {
        if (!(error instanceof CoercionFailed)) throw error;
        return auto ? [q, r] : [this.like(0, this.gens, 'ZZ_I'), this];
      }
    }
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
    if (this.gens.length > 1) {
      const x = first(this.gens);
      const r = Poly.from(this.asExpr(), [x]).prem(Poly.from(o.asExpr(), [x]));
      return Poly.from(r.asExpr(), this.gens, { domain: this.domain });
    }
    const finite = this.finitePair(o);
    if (finite) return finite[0].finitePseudoDiv(finite[1])[1];
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
    const finite=this.finitePair(o),K=this.algebraicField;
    if(finite&&isprime(finite[2])){
      const [a,b]=finite,domain=defined(polyConstructionHooks.domain,'polynomial domain construction')([],{domain:a.domain});
      return a.fieldPoly(domain).subresultants(b.fieldPoly(domain)).map((f)=>a.like(f.asExpr(a.gens)));
    }
    if(K)return this.fieldPoly(K).subresultants(this.like(o.asExpr()).fieldPoly(K)).map((f)=>this.like(f.asExpr(this.gens)));
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
    if (this.gens.length > 1) {
      const x = first(this.gens);
      const q = Poly.from(this.asExpr(), [x]).pquo(Poly.from(o.asExpr(), [x]));
      return Poly.from(q.asExpr(), this.gens, { domain: this.domain });
    }
    const finite = this.finitePair(o);
    if (finite) return finite[0].finitePseudoDiv(finite[1])[0];
    const x = this.univariate();
    const k = this.degree() - o.degree() + 1;
    const scaled = mul(pow(o.LC(), Math.max(0, k)), this.asExpr());
    // the scaled dividend minus the pseudo-remainder is an exact multiple of o
    return Poly.from(defined(divExact(expand(add(scaled, mul(-1, this.prem(o).asExpr()))), o.asExpr(), [x]), 'pseudo-quotient'), this.gens);
  }
  exquo(o: Poly): Poly {
    if (this.finiteModulus !== undefined || o.finiteModulus !== undefined || this.algebraicField !== undefined) {
      const [q, r] = this.div(o);
      if (!r.isZero) throw new ExactQuotientFailed('exquo: inexact division');
      return q;
    }
    const q = divExact(this.asExpr(), o.asExpr(), this.gens);
    if (q === undefined) throw new ExactQuotientFailed('exquo: inexact division');
    return Poly.from(q, this.gens);
  }

  gcd(o: Poly): Poly {
    if (this.domain !== o.domain && (o.algebraicField || this.domain.endsWith('_I') || o.domain.endsWith('_I'))) {
      const [a, b] = this.unify(o);
      return a.gcd(b);
    }
    if (this.domain === 'ZZ_I') {
      const K = this.coefficientDomain ?? defined(polyConstructionHooks.domain, 'Gaussian integer domain')([], { domain: 'ZZ_I' });
      const [a, b] = this.unify(o);
      const content = (p: Poly): Expr => p.coeffs().reduce((g, c) => K.toSympy(K.gcd(g, c)), S.Zero);
      const h = a.setDomain('QQ_I').gcd(b.setDomain('QQ_I'));
      if (h.isZero) return a;
      const [, primitive] = primitiveGaussian(h, K);
      return primitive.mulGround(K.toSympy(K.gcd(content(a), content(b)))).setDomain(K);
    }
    if(o instanceof Poly && this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.gcd(b);}
    const finite = this.finitePair(o);
    if (finite) {
      const [a,b,p] = finite;
      if (a.gens.length === 1) return a.fromFiniteDense(gfGcd(a.finiteDense(), b.finiteDense(), p));
      const K = defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: this.domain });
      return a.like(a.fieldPoly(K).gcd(b.fieldPoly(K)).asExpr(a.gens));
    }
    const K = this.algebraicField;
    if (K) return this.like(this.fieldPoly(K).gcd(this.like(o.asExpr()).fieldPoly(K)).asExpr(this.gens));
    const [f, g] = fieldPair(this, o);
    if (f === undefined) return Poly.from(mgcd(this.asExpr(), o.asExpr(), this.gens), this.gens);
    // SymPy dup_inner_gcd: RR and CC are computed over their exact domains
    const h = Poly.from(mgcd(exactCoeffs(f), exactCoeffs(g), f.gens), f.gens, { domain: f.domain });
    return h.isZero ? h : h.monic();
  }
  lcm(o: Poly): Poly {
    if (this.isZero || o.isZero) return this.unify(o)[0].like(0);
    const finite = this.finitePair(o);
    if (finite) {
      const [a,b,p] = finite;
      if (a.gens.length === 1) return a.fromFiniteDense(gfLcm(a.finiteDense(), b.finiteDense(), p));
      return a.mul(b).exquo(a.gcd(b)).monic();
    }
    if (this.algebraicField) return this.mul(o).exquo(this.gcd(o)).monic();
    const [f, g] = fieldPair(this, o);
    if (f === undefined) return Poly.from(mlcm(this.asExpr(), o.asExpr(), this.gens), this.gens);
    // SymPy dmp_ff_lcm: the monic quotient f*g / gcd(f, g)
    return f.mul(g).div(f.gcd(g))[0].monic();
  }
  monic(auto = true): Poly {
    if (!auto) return this.exquoGround(this.LC());
    if (this.finiteModulus !== undefined) return this.isZero ? this : this.exquoGround(this.LC());
    const K = this.algebraicField;
    if(K)return this.like(this.fieldPoly(K).monic().asExpr(this.gens));
    const lc = this.LC();
    // SymPy to_field: ZZ becomes QQ and a polynomial ring K[a] its fraction field K(a)
    // (the domain object keeps its symbols; a domain known only by name is rebuilt from that name)
    const ring = /^(ZZ|QQ)\[(.+)\]$/.exec(this.domain);
    const dom = this.domain === 'ZZ' ? 'QQ' : ring ? this.coefficientDomain?.getField() ?? `${ring[1]}(${ring[2]})` : this.domain;
    return Poly.from(mul(this.asExpr(), pow(lc, -1)), this.gens, { domain: dom });
  }
  /** [content, primitive part] over the integers. */
  primitive(): [Expr, Poly] {
    if (this.finiteModulus !== undefined || this.algebraicField !== undefined || this.domain === 'RR' || this.domain === 'CC' || this.isZero) return [this.content(), this];
    const c = this.content();
    return [c, Poly.from(mul(this.asExpr(), pow(c, -1)), this.gens)];
  }
  content(): Expr {
    if (this.finiteModulus !== undefined || this.algebraicField !== undefined) return this.isZero ? S.Zero : S.One;
    if (this.domain === 'RR' || this.domain === 'CC') return new Float(this.isZero ? 0 : 1);
    let g: Expr = S.Zero;
    for (const t of this.termList) g = mgcd(g, t.coeff, []);
    return g;
  }

  diff(x?: Expr): Poly {
    // a generator need not be a symbol (Poly(pi*x, pi)): differentiate formally through a dummy symbol
    const g = x ?? first(this.gens);
    const d = g instanceof Sym ? diff(this.asExpr(), g) : (() => {
      const t = new Dummy('t');
      return xreplace(diff(xreplace(this.asExpr(), [[g, t]]), t), [[t, g]]);
    })();
    if (this.finiteModulus !== undefined || this.algebraicField !== undefined) return this.like(d);
    return Poly.from(d, this.gens);
  }
  /** The antiderivative in a generator (SymPy Poly.integrate), term by term. */
  integrate(x?: Expr): Poly {
    const i = x === undefined ? 0 : this.genIndex(x);
    const p = this.finiteModulus;
    // SymPy's dense integration divides every coefficient, including zeros.
    // It therefore rejects any denominator divisible by the characteristic.
    if (p !== undefined) {
      const inverses = Array.from({ length: Math.max(0, this.degree(at(this.gens,i)) + 1) }, (_,k) => finiteInverse(BigInt(k+1),p));
      return this.like(add(...this.termList.map((t) => {
        const k = at(t.monom, i) + 1;
        const c = mul(t.coeff, Rational.of(at(inverses,k-1)));
        return mul(c, ...t.monom.map((e,j) => pow(at(this.gens,j), j === i ? k : e)));
      })));
    }
    const domain = this.domain === 'ZZ' ? 'QQ' : this.domain;
    const terms = this.termList.map((t) => {
      const k = at(t.monom, i) + 1;
      return mul(t.coeff, Rational.of(1n, BigInt(k)), ...t.monom.map((e, j) => pow(at(this.gens, j), j === i ? k : e)));
    });
    return this.like(add(...terms),this.gens,domain);
  }
  /** Evaluate at gen = a (first generator by default). */
  eval(a: ExprLike, gen?: Expr, auto = true): Expr | Poly {
    const g = gen ?? first(this.gens);
    const p = this.finiteModulus;
    let value=p===undefined?sympify(a):finiteCoefficient(sympify(a),p,this.finiteSymmetric);
    if (!auto && p === undefined) {
      const domain = this.coefficientDomain ?? defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: this.domain });
      try { value = domain.fromSympy(value); }
      catch (error) {
        if (!(error instanceof CoercionFailed)) throw error;
        throw new DomainError(`cannot evaluate over ${this.domain}`);
      }
    }
    const v=add(...this.termList.map((t)=>mul(t.coeff,...this.gens.map((h,i)=>pow(h.key===g.key?value:h,at(t.monom,i))))));
    const rest = this.gens.filter((h) => h.key !== g.key);
    if (p !== undefined) return rest.length ? this.like(v, rest) : finiteCoefficient(expand(v), p, this.finiteSymmetric);
    const K=this.algebraicField;
    if(K){
      if(rest.length)return this.like(v,rest);
      try{return K.toSympy(K.convert(expand(v)));}
      catch(error){if(!(error instanceof CoercionFailed))throw error;return expand(v);}
    }
    const normalized = this.domain.includes('(') || value instanceof Mul && value.args.some((f) => f instanceof Pow && f.exp instanceof Rational && f.exp.isNegative) ? cancel(v) : v;
    if (rest.length && this.coefficientDomain?.symbols.length && !rest.some((g) => value.has(g))) {
      const K = this.coefficientDomain.unify(defined(polyConstructionHooks.domain, 'polynomial domain construction')([value], {}));
      return Poly.from(normalized, rest, { domain: K });
    }
    return rest.length ? Poly.from(normalized, rest) : expand(normalized);
  }

  /** (content, [(factor, multiplicity)]) with primitive integer factors. */
  factorList(): [Expr, [Poly, number][]] {
    const p = this.finiteModulus;
    if (p !== undefined) {
      const dense=this.finiteDense();
      const [c,fs] = isprime(p)?gfFactor(dense,p):((():[bigint,[bigint[],number][]]=>{
        const [lc,squarefree]=gfSqfList(dense,p);
        return [lc,squarefree.flatMap(([f,k])=>gfFactorSqf(f,p,ZZ,'berlekamp')[1].map((g):[bigint[],number]=>[g,k]))];
      })());
      return [finiteCoefficient(Rational.of(c), p, this.finiteSymmetric), fs.map(([f,k]) => [this.fromFiniteDense(f), k])];
    }
    if (this.algebraicField) return this.factorAlgebraic();
    const [c, fs] = factorListInt(this.asExpr(), this.gens);
    return [c, fs.map(([f, k]) => [Poly.from(f, this.gens), k] as [Poly, number])];
  }
  sqfList(): [Rational, [Poly, number][]] {
    const p = this.finiteModulus;
    if (p !== undefined) {
      // SymPy 1.14 asserts its square-free degree invariant for the zero Poly.
      if (this.isZero) throw new InvariantError('square-free degree invariant for zero polynomial');
      const [c, fs] = gfSqfList(this.finiteDense(), p);
      return [finiteCoefficient(Rational.of(c), p, this.finiteSymmetric), fs.map(([f,k]) => [this.fromFiniteDense(f), k])];
    }
    if (this.isMultivariate && ['ZZ', 'QQ'].includes(this.domain)) {
      return this.sqfListMultivariate();
    }
    const x = this.univariate();
    const up = UPoly.fromExpr(this.asExpr(), x);
    if (!up) return this.sqfListSymbolic(x);
    const content = up.lc;
    const out: [Poly, number][] = up.squareFree().map(([f, k]) => [primitiveIntPoly(f.toExpr(x), x), k]);
    return [content, out];
  }

  /** Yun's square-free decomposition in characteristic zero. */
  private sqfListMultivariate(): [Rational, [Poly, number][]] {
    if (this.isZero) return [S.Zero, []];
    const leading = asRational(this.LC(), 'leading coefficient');
    const c = this.domain === 'QQ' ? leading : asRational(mul(leading.isNegative ? -1 : 1, this.content()), 'square-free content');
    const f = this.exquoGround(c);
    let repeated = f;
    for (const g of this.gens) repeated = repeated.gcd(f.diff(g));
    let previous = f.exquo(repeated);
    const factors: [Poly, number][] = [];
    for (let k = 1; !previous.isOne; k++) {
      const common = previous.gcd(repeated);
      const factor = previous.exquo(common);
      if (!factor.isOne) factors.push([this.like(factor.asExpr(), this.gens, this.domain), k]);
      previous = common;
      repeated = repeated.exquo(common);
    }
    return [c, factors];
  }

  /**
   * Yun's square-free decomposition over ZZ[x, parameters] (symbolic
   * coefficients). A content free of x that is not a number is listed first
   * as a factor of degree 0 (SymPy returns it as the content).
   */
  private sqfListSymbolic(x: Expr): [Rational, [Poly, number][]] {
    const e = this.asExpr();
    const vars = [x, ...sortGens([...freeSymbols(e)].filter((s) => s instanceof Sym).filter((s) => s.key !== x.key))];
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
  /** The polynomial over ZZ, primitive with a positive leading coefficient, as an expression (SymPy's PurePoly of a factor). */
  private primitiveExpr(): Expr {
    const cs = this.denseInts();
    // the irreducible factors have positive leading coefficients
    const g = cs.reduce((a, c) => igcd(a, c), 0n);
    const n = cs.length - 1;
    return add(...cs.map((c, i) => mul(Rational.of(c / g), pow(first(this.gens), n - i))));
  }
  /**
   * Isolating intervals of the real roots with multiplicities in [inf, sup], each narrower than eps
   * (SymPy Poly.intervals); with all, also the isolating rectangles [lower-left, upper-right corner]
   * of the non-real roots of a polynomial with one square-free factor.
   */
  intervals(eps?: Rational, opts?: IntervalsOptions & { all?: false }): [[Rational, Rational], number][];
  intervals(eps: Rational | undefined, opts: IntervalsOptions & { all: true }): [[[Rational, Rational], number][], [[Expr, Expr], number][]];
  intervals(eps?: Rational, opts: IntervalsOptions & { all?: boolean } = {}): [[Rational, Rational], number][] | [[[Rational, Rational], number][], [[Expr, Expr], number][]] {
    if(this.finiteModulus!==undefined)throw new DomainError('isolation of roots not supported over finite domains');
    if (eps !== undefined && !eps.isPositive) throw new RangeError("'eps' must be a positive rational");
    if (this.isGround) return opts.all ? [[], []] : [];
    const [, fs] = this.sqfList();
    const iso = { eps, inf: opts.inf, sup: opts.sup, fast: opts.fast };
    if (!opts.all) return isolateRealRoots(fs.map(([f, k]) => [f.denseInts(), k] as [bigint[], number]), eps, iso);
    // SymPy dup_isolate_all_roots
    if (fs.length !== 1) throw new NotImplementedError('only trivial square-free polynomials are supported');
    const [f, k] = first(fs);
    const real = isolateRealRootsSqf(f.denseInts(), iso).map((iv): [[Rational, Rational], number] => [iv, k]);
    const point = ([re, im]: [Rational, Rational]): Expr => add(re, mul(S.I, im));
    const complex = isolateComplexRootsSqf(f.denseInts(), iso).map((r): [[Expr, Expr], number] => [[point([r.ax, r.ay]), point([r.bx, r.by])], k]);
    return [real, complex];
  }
  /** Refine the isolating interval (s, t) of a real root (SymPy Poly.refine_root). */
  refineRoot(s: Rational, t: Rational, eps?: Rational, steps?: number, fast = false): [Rational, Rational] {
    if(this.finiteModulus!==undefined)throw new DomainError('real root refinement not supported over finite domains');
    if (eps !== undefined && !eps.isPositive) throw new RangeError("'eps' must be a positive rational");
    // SymPy refines the polynomial itself (check_sqf=False), one step when neither eps nor steps is given
    return refineRealRoot(this.denseInts(), s, t, { eps, steps: steps ?? (eps === undefined ? 1 : undefined), fast });
  }

  roots(): Expr[] {
    return rootsOf(this.asExpr(), this.univariate());
  }


  // ---- further SymPy Poly methods --------------------------------------------

  private like(e: ExprLike, gens: readonly Expr[] = this.gens, domain?: string): Poly {
    if (this.finiteModulus !== undefined) return Poly.from(e, gens, { domain: domain ?? this.domain, symmetric: this.finiteSymmetric });
    if (this.algebraicField !== undefined || this.coefficientDomain?.isFiniteExtension) return Poly.from(e, gens, { domain: domain===undefined||domain===this.domain ? this.coefficientDomain ?? this.domain : domain });
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
    // Preserve SymPy 1.14 dmp_sub_ground's TypeError for a zero ground element.
    const p = this.finiteModulus;
    if (p !== undefined && finiteCoefficient(sympify(c),p).isZero) throw new TypeError('cannot subtract a zero ground element');
    return this.like(add(this.asExpr(), mul(-1, c)));
  }
  mulGround(c: ExprLike): Poly {
    return this.like(mul(this.asExpr(), c));
  }
  /** Coefficient-wise quotient (floor division over ZZ). */
  quoGround(c: ExprLike): Poly {
    const k = sympify(c);
    const p = this.finiteModulus;
    if (p !== undefined) return this.mulGround(Rational.of(finiteInverse(finiteCoefficient(k, p).p, p)));
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
    if (this.finiteModulus !== undefined) return this.quoGround(c);
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
    const reps = vs.map((v, i): [Expr, Expr] => {
      if (!isGenValue(v)) return [at(this.gens, i), sympify(v)];
      if (!this.gens.some((g) => g.key === v[0].key)) throw new GeneratorsError('invalid polynomial generator');
      return [v[0], sympify(v[1])];
    });
    return expand(xreplace(this.asExpr(), reps));
  }
  /** (gcd, f/gcd, g/gcd). */
  cofactors(o: Poly): [Poly, Poly, Poly] {
    const h = this.gcd(o);
    return [h, this.exquo(h), o.exquo(h)];
  }
  /** Cancel common factors in a ratio while preserving the coefficient domain. */
  cancel(other: Poly, include: true): [Poly, Poly];
  cancel(other: Poly, include?: false): [Expr, Poly, Poly];
  cancel(other: Poly, include = false): [Poly, Poly] | [Expr, Poly, Poly] {
    const [f, g] = this.unify(other);
    if (f.finiteModulus !== undefined || f.algebraicField !== undefined) {
      const h = f.gcd(g);
      const pair: [Poly, Poly] = h.isZero ? [f, g] : [f.exquo(h), g.exquo(h)];
      return include ? pair : [S.One, ...pair];
    }
    if (f.domain.endsWith(']') || f.domain.endsWith(')')) {
      if (g.isZero) return include ? [f, g] : [S.One, f, g];
      const [p, q] = fraction(cancel(mul(f.asExpr(), pow(g.asExpr(), -1))));
      const pair: [Poly, Poly] = [f.like(p, f.gens, f.domain), f.like(q, f.gens, f.domain)];
      return include ? pair : [S.One, ...pair];
    }
    const [a, F] = f.clearDenoms(true), [b, G] = g.clearDenoms(true);
    const h = F.gcd(G);
    if (h.isZero) return include ? [f, g] : [S.One, f, g];
    const p = F.exquo(h), q = G.exquo(h);
    const numeratorSign = isPositive(mul(-1, p.LC())) === true ? -1 : 1;
    const denominatorSign = isPositive(mul(-1, q.LC())) === true ? -1 : 1;
    const P = f.like(mul(numeratorSign, p.asExpr()), f.gens, f.domain);
    const Q = g.like(mul(denominatorSign, q.asExpr()), g.gens, g.domain);
    const coefficient = asRational(mul(numeratorSign, denominatorSign, b, pow(a, -1)), 'coefficient ratio');
    if (include) return [P.mulGround(Rational.of(coefficient.p)), Q.mulGround(Rational.of(coefficient.q))];
    return [coefficient, P, Q];
  }
  compose(o: Poly): Poly {
    if(this.algebraicField && this.domain!==o.domain){const [a,b]=this.unify(o);return a.compose(b);}
    return this.like(add(...this.termList.map((t)=>mul(t.coeff,pow(o.asExpr(),first(t.monom)),...t.monom.slice(1).map((e,i)=>pow(at(this.gens,i+1),e))))));
  }
  discriminant(): Expr {
    const p=this.finiteModulus;
    if(p!==undefined){
      const n=this.degree();
      if(n<=0)return S.Zero;
      const lc=this.like(add(...this.termList.filter((t)=>first(t.monom)===n).map((t)=>mul(t.coeff,...t.monom.slice(1).map((e,i)=>pow(at(this.gens,i+1),e))))));
      const derivative=this.diff();
      if(derivative.isZero)return S.Zero;
      const resultant=this.like(this.resultant(derivative)),exponent=n-2-derivative.degree();
      const r=exponent<0?resultant.exquo(lc):resultant.mul(lc.pow(exponent));
      return r.mulGround(n*(n-1)/2%2===0?1:-1).asExpr();
    }
    return discriminant(this.asExpr(), this.univariate());
  }
  resultant(o: Poly): Expr {
    const finite = this.finitePair(o);
    if (finite) {
      const [f, g] = finite;
      const x = expectType(first(f.gens), (s): s is Sym => s instanceof Sym, 'resultant generator');
      return f.like(resultant(f.asExpr(), g.asExpr(), x), f.gens.slice(1)).asExpr();
    }
    return resultant(this.asExpr(), o.asExpr(), this.univariate());
  }
  /** Last coefficient in term order. */
  EC(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): Expr {
    return this.ET(opts)[1];
  }
  /** Last monomial in lexicographic term order (SymPy Poly.EM). */
  EM(opts: { order?: 'lex' | 'grlex' | 'grevlex' } = {}): Expr {
    return mul(...this.ET(opts)[0].map((n, i) => pow(at(this.gens, i), n)));
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
    return rest.length ? this.like(v,rest) : this.finiteModulus === undefined ? v : finiteCoefficient(v,this.finiteModulus,this.finiteSymmetric);
  }
  /** Remove generators that do not occur. */
  exclude(): Poly {
    const keep = this.gens.filter((_, i) => this.termList.some((t) => at(t.monom, i) > 0));
    return this.like(this.asExpr(),keep.length ? keep : this.gens);
  }
  hasOnlyGens(...gens: Expr[]): boolean {
    if (gens.some((h) => !this.gens.some((g) => g.key === h.key))) throw new GeneratorsError('invalid polynomial generator');
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
    return this.like(e,gens);
  }
  /** Drop the generators to the left of gen. */
  ltrim(gen: Expr | number): Poly {
    let i = typeof gen === 'number' ? gen : this.gens.findIndex((g) => g.key === gen.key);
    if (typeof gen === 'number' && i < 0) i += this.gens.length;
    if (i < 0 || i >= this.gens.length) throw new PolynomialError(`${String(gen)} is not a valid generator level`);
    if (this.termList.some((t) => t.monom.slice(0, i).some((e) => e !== 0))) throw new PolynomialError('Cannot left trim');
    return this.like(this.asExpr(),this.gens.slice(i));
  }
  /** Reorder the generators; with `{ wrt }` the given generators come first and the rest follow the default order. */
  reorder(...gens: Expr[]): Poly;
  reorder(options: { wrt: Expr | readonly Expr[] }): Poly;
  reorder(...args: (Expr | { wrt: Expr | readonly Expr[] })[]): Poly {
    const [only] = args;
    const gens = args.length === 1 && only !== undefined && !(only instanceof Expr) ? this.gensWrt(only.wrt) : args.filter((a): a is Expr => a instanceof Expr);
    const keys = new Set(this.gens.map((g) => g.key));
    if (gens.length !== this.gens.length || new Set(gens.map((g) => g.key)).size !== keys.size || gens.some((g) => !keys.has(g.key))) {
      throw new PolynomialError('generators list can differ only up to order of elements');
    }
    return this.like(this.asExpr(),gens);
  }
  private gensWrt(wrt: Expr | readonly Expr[]): Expr[] {
    const first = (wrt instanceof Expr ? [wrt] : [...wrt]).filter((w) => this.gens.some((g) => g.key === w.key));
    return [...first, ...sortGens(this.gens.filter((g) => !first.some((w) => w.key === g.key)))];
  }
  replace(x: Expr, y?: Expr): Poly {
    const source=y===undefined?this.gen:x,target=y??x;
    if(y===undefined && this.isMultivariate)throw new PolynomialError('replace requires a source generator for multivariate polynomials');
    if(!this.gens.some((g)=>g.key===source.key))return this;
    if(source.key===target.key)return this;
    if(this.gens.some((g)=>g.key===target.key)||[...freeSymbols(this.asExpr())].some((s)=>s.key===target.key))throw new PolynomialError('replacement generator already occurs');
    const gens=this.gens.map((g)=>g.key===source.key?target:g);
    return this.like(add(...this.termList.map((t)=>mul(t.coeff,...t.monom.map((e,i)=>pow(at(gens,i),e))))),gens);
  }
  /** Substitute a coefficient expression or a generator. */
  subs(from: Expr, to: Expr): Poly | Expr {
    if (from.key === to.key) return this;
    const e = this.asExpr();
    if (!this.gens.some((g) => g.key === from.key)) {
      const changed = e.subs(from, to);
      if (changed.key === e.key) return this;
      return this.gens.some((g) => to.has(g)) ? changed : Poly.from(changed, this.gens);
    }
    if (!(to instanceof Sym)) return this.eval(to, from);
    if (this.gens.some((g) => g.key === to.key) || e.has(to)) return e.subs(from, to);
    return this.replace(from, to);
  }
  /** Pseudo-division: (pquo, prem). */
  pdiv(o: Poly): [Poly, Poly] {
    const finite = this.finitePair(o);
    if (finite) return finite[0].finitePseudoDiv(finite[1]);
    return [this.pquo(o), this.prem(o)];
  }
  /** Pseudo-division in the first generator over a finite coefficient ring. */
  private finitePseudoDiv(g: Poly): [Poly, Poly] {
    if (g.isZero) throw new RangeError('pseudo-division by zero polynomial');
    const x = first(this.gens), dg = g.degree(x);
    let remaining = Math.max(0, this.degree(x) - dg + 1);
    const leading = (f: Poly): Poly => f.like(add(...f.termList.filter((t) => first(t.monom) === f.degree(x)).map((t) => mul(t.coeff, ...f.gens.slice(1).map((s, i) => pow(s, at(t.monom, i + 1)))))));
    const lc = leading(g);
    let q = this.like(0), r: Poly = this;
    while (!r.isZero && r.degree(x) >= dg) {
      const term = leading(r).mul(this.like(pow(x, r.degree(x) - dg)));
      q = q.mul(lc).add(term);
      r = r.mul(lc).sub(term.mul(g));
      remaining--;
    }
    const scale = lc.pow(remaining);
    return [q.mul(scale), r.mul(scale)];
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
    if(this.gens.length!==1)throw new RangeError('univariate polynomial expected');
    const x = first(this.gens);
    return this.like(add(...this.termList.map((t)=>mul(t.coeff,pow(add(x,a),first(t.monom))))));
  }
  /** Translate each generator by its corresponding value. */
  shiftList(values: readonly ExprLike[]): Poly {
    if (values.length !== this.gens.length) throw new PolynomialError('a shift is required for each generator');
    return this.like(this.asExprAt(this.gens.map((g, i) => [g, add(g, at(values, i))] as const)));
  }
  /** Square-free part. */
  sqfPart(): Poly {
    if(this.finiteModulus !== undefined)return this.fromFiniteDense(gfSqfPart(this.finiteDense(),this.finiteModulus));
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
    return [m, this.like(e)];
  }
  /** (gcd of the exponents per generator, deflated polynomial). */
  deflate(): [number[], Poly] {
    const g = (a: number, b: number): number => (b === 0 ? a : g(b, a % b));
    const J = this.gens.map((_, i) => this.termList.reduce((acc, t) => g(acc, at(t.monom, i)), 0) || 1);
    const e = add(...this.termList.map((t) => this.termExpr({ monom: t.monom.map((k, i) => k / at(J, i)), coeff: t.coeff })));
    return [J, this.like(e)];
  }
  toField(): Poly {
    return this.like(this.asExpr(),this.gens,this.domain === 'ZZ' ? 'QQ' : this.domain);
  }
  toRing(): Poly {
    const K = this.coefficientDomain ?? defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: this.domain });
    if (this.finiteModulus !== undefined) throw new DomainError('the finite field has no associated ring');
    return this.like(this.asExpr(), this.gens, String(K.getRing()));
  }
  toExact(): Poly {
    const e = xreplace(
      this.asExpr(),
      this.termList.flatMap((t): [Expr, Expr][] => (t.coeff instanceof Float ? [[t.coeff, Rational.of(...new MPContext(t.coeff.prec, { real: true }).toRational(t.coeff))]] : [])),
    );
    // SymPy get_exact: RR -> QQ, exact domains unchanged
    return this.like(e,this.gens,this.domain === 'RR' ? 'QQ' : this.domain);
  }
  /** q**n * f(p/q). */
  transform(p: Poly, q: Poly): Poly {
    if (!this.isUnivariate || !p.isUnivariate || !q.isUnivariate || p.gen.key !== this.gen.key || q.gen.key !== this.gen.key) {
      throw new RangeError('univariate polynomials with a common generator expected');
    }
    const [pu, qu] = p.unify(q);
    const [fu, common] = this.unify(pu);
    const n = this.degree();
    const e = add(
      ...fu.termList.map((t) => {
        const k = first(t.monom);
        return mul(t.coeff, pow(common.asExpr(), k), pow(qu.asExpr(), n - k));
      }),
    );
    return fu.like(expand(e));
  }
  /** Reduce the coefficients modulo p into the symmetric range. */
  trunc(pIn: ExprLike): Poly {
    const p = asRational(sympify(pIn), 'modulus').p;
    const finite = this.finiteModulus;
    return this.mapCoeffs((c) => {
      const n = finite === undefined ? asRational(c, 'coefficient').p : finiteCoefficient(c, finite, false).p;
      let v = (n % p + p) % p;
      if (v > p / 2n) v -= p;
      return Rational.of(v);
    });
  }
  /** Polynomials with common generators and coefficient domain. */
  unify(other: Poly): [Poly, Poly] {
    const finite = this.finitePair(other);
    if (finite !== undefined) return [finite[0], finite[1]];
    if (this.domain === other.domain && this.gens.length === other.gens.length && this.gens.every((g, i) => g.key === at(other.gens, i).key)) return [this, other];
    const gens = [...this.gens];
    for (const g of other.gens) if (!gens.some((h) => h.key === g.key)) gens.push(g);
    let domain = this.domain;
    let coefficientDomain=this.coefficientDomain ?? other.coefficientDomain;
    if (domain !== other.domain) {
      const construct = defined(polyConstructionHooks.domain, 'polynomial domain construction');
      // CC contains the real and rational coefficient fields, even for
      // polynomials whose complex coefficients happen to be real.
      const numeric = ['ZZ', 'QQ', 'RR', 'CC', 'ZZ_I', 'QQ_I'];
      const domains = [domain, other.domain];
      if (domains.includes('EX')) domain = 'EX';
      else if (domains.every((d) => numeric.includes(d))) {
        const complex = domains.some((d) => ['CC', 'ZZ_I', 'QQ_I'].includes(d));
        const floating = domains.some((d) => ['RR', 'CC'].includes(d));
        const rational = domains.some((d) => ['QQ', 'QQ_I'].includes(d));
        domain = floating ? complex ? 'CC' : 'RR' : complex ? rational ? 'QQ_I' : 'ZZ_I' : 'QQ';
      } else {
        coefficientDomain=(this.coefficientDomain ?? construct([],{domain})).unify(other.coefficientDomain ?? construct([],{domain:other.domain}));
        domain=String(coefficientDomain);
      }
    }
    return [Poly.from(this.asExpr(), gens, { domain: coefficientDomain?.toString()===domain?coefficientDomain:domain, pure: this.pure }), Poly.from(other.asExpr(), gens, { domain: coefficientDomain?.toString()===domain?coefficientDomain:domain, pure: other.pure })];
  }
  /** Clear coefficient denominators while preserving the quotient f/g. */
  ratClearDenoms(other: Poly): [Poly, Poly] {
    const [f, g] = this.unify(other);
    if (f.domain === 'EX') return [f, g];
    const [a, F] = f.clearDenoms(true), [b, G] = g.clearDenoms(true);
    return [F.mulGround(b), G.mulGround(a)];
  }
  /** A translated polynomial and its square-free norm over the ground field. */
  sqfNorm(): [number[], Poly, Poly] {
    if(!this.algebraicField)throw new DomainError('sqf_norm requires an algebraic coefficient domain');
    if(this.isZero)return [this.gens.map(()=>0),this,this.like(0,this.gens,'QQ')];
    if(!this.isSqf)throw new PolynomialError('square-free polynomial expected');
    return this.squarefreeNorm();
  }
  private squarefreeNorm(): [number[],Poly,Poly] {
    const K=defined(this.algebraicField),{generator}=defined(polyConstructionHooks.algebraic,'algebraic field data')(K);
    const candidates=algebraicNormShifts(this.degreeList());
    for(;;){
      const s=candidates.next().value;
      const shifted=this.like(this.fieldPoly(K).shift(s.map((k)=>K.convert(mul(-k,generator)))).asExpr(this.gens));
      const norm=defined(shifted.algebraicNorm(),'algebraic norm');
      if(norm.isSqf)return [s,shifted,norm];
    }
  }

  /** (lcm of denominators, polynomial times it). */
  clearDenoms(convert = false): [Expr, Poly] {
    const fractionDomain = /^(ZZ|QQ)\((.*)\)$/.exec(this.domain);
    if (fractionDomain !== null) {
      let common: Expr = S.One;
      for (const t of this.termList) common = polyLcm(common, fraction(together(t.coeff))[1]);
      const expr = add(...this.termList.map((t) => this.termExpr({ ...t, coeff: cancel(mul(common, t.coeff)) })));
      const domain = convert ? `${at(fractionDomain, 1)}[${at(fractionDomain, 2)}]` : this.domain;
      return [common, Poly.from(expr, this.gens, { domain })];
    }
    let l = 1n;
    const gcdB = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcdB(b, a % b));
    for (const t of this.termList) if (t.coeff instanceof Rational) l = (l / gcdB(l, t.coeff.q)) * t.coeff.q;
    const e = expand(mul(Rational.of(l), this.asExpr()));
    return [Rational.of(l),this.like(e,this.gens,convert && this.domain==='QQ'?'ZZ':this.domain)];
  }
  /** Extended Euclid: (s, t, h) with s*f + t*g = h = gcd(f, g) (monic, over the coefficient field). */
  gcdex(o: Poly, auto = true): [Poly, Poly, Poly] {
    const finite = this.finitePair(o);
    if (finite) {
      const [a,b,p] = finite;
      // Poly.gcdex uses dense Euclid, which divides by g before testing zero.
      if (b.isZero) throw new RangeError('polynomial division by zero');
      const [s,t,h] = gfGcdex(a.finiteDense(), b.finiteDense(), p);
      return [a.fromFiniteDense(s), a.fromFiniteDense(t), a.fromFiniteDense(h)];
    }
    const x = this.univariate();
    if (!auto && fieldDomainName(this.domain) !== this.domain && fieldDomainName(o.domain) !== o.domain) throw new DomainError('extended Euclidean algorithm requires a field');
    const domain = fieldDomainName(this.domain === o.domain ? this.domain : inferDomain([...this.coeffs(), ...o.coeffs()]));
    let [r0, r1] = [this.toField(), o.toField()];
    let [s0, s1] = [Poly.from(1, [x], { domain }), Poly.from(0, [x], { domain })];
    let [t0, t1] = [Poly.from(0, [x], { domain }), Poly.from(1, [x], { domain })];
    while (!r1.isZero) {
      const [q, r] = r0.div(r1);
      [r0, r1] = [r1, r];
      [s0, s1] = [s1, s0.sub(q.mul(s1)).toField()];
      [t0, t1] = [t1, t0.sub(q.mul(t1)).toField()];
    }
    const lc = r0.LC();
    const inv = pow(lc, -1);
    const f = (p: Poly) => Poly.from(expand(mul(inv, p.asExpr())), [x], { domain });
    return [f(s0), f(t0), f(r0)];
  }
  halfGcdex(o: Poly, auto = true): [Poly, Poly] {
    const [s, , h] = this.gcdex(o, auto);
    return [s, h];
  }
  /** Inverse of f modulo g. */
  invert(o: Poly): Poly {
    const [s, , h] = this.gcdex(o);
    if (h.degree() !== 0) throw new NotInvertible('invert: zero divisor');
    return s;
  }
  /** Sturm sequence over the coefficient field. */
  sturm(auto = true): Poly[] {
    const x = this.univariate();
    if (!auto && fieldDomainName(this.domain) !== this.domain) throw new DomainError('Sturm sequence requires a field');
    if (this.finiteModulus !== undefined) {
      const f = this.sqfPart(), seq = [f, f.diff()];
      while (!at(seq, -1).isZero) seq.push(at(seq, -2).rem(at(seq, -1)).neg());
      return seq.slice(0, -1);
    }
    const fieldName = fieldDomainName(this.domain);
    if (/^(ZZ|QQ)\(/.test(fieldName)) return this.sturmOverRationalFunctions(fieldName);
    const field = this.toField();
    if (field.degree() <= 0) return [field.monic()];
    const f = field.exquo(field.gcd(field.diff())).monic();
    const seq: Poly[] = [f, Poly.from(diff(f.asExpr(), x), [x], { domain: f.domain })];
    for (;;) {
      const r = at(seq, -2).div(at(seq, -1))[1];
      if (r.isZero) break;
      seq.push(Poly.from(mul(-1, r.asExpr()), [x], { domain: f.domain }));
    }
    return seq;
  }

  private sturmOverRationalFunctions(domain: string): Poly[] {
    const coefficients = this.coeffs();
    const generators = gensFor(...coefficients.flatMap((c) => fraction(together(c))));
    const replacements = generators.map((g): [Expr, Sym] => [g, new Dummy('c')]);
    const restore = replacements.map(([g, c]): [Expr, Expr] => [c, g]);
    const K = QQ.fracField(...replacements.map(([, c]) => c));
    const f = new FieldPoly(K, 1, this.termList.map(({ monom, coeff }) => [monom, K.convert(xreplace(coeff, replacements))]));
    if (f.isZero) return [this];
    const h = f.exquo(f.gcd(f.diff(0))).monic();
    const sequence = [h, h.diff(0)];
    while (!at(sequence, -1).isZero) sequence.push(at(sequence, -2).div(at(sequence, -1))[1].neg());
    return sequence.slice(0, -1).map((p) => new Poly(this.gens, p.terms.map(([m, c]) => ({
      monom: [...m],
      coeff: xreplace(K.toSympy(c), restore),
    })), domain, this.pure));
  }
  /** Number of real roots in [a, b] (Sturm's theorem). */
  countRoots(a?: ExprLike, b?: ExprLike): number {
    const x = this.univariate();
    if (this.degree() <= 0) return 0;
    if(this.finiteModulus!==undefined)throw new DomainError('sign variation counting not supported over finite domains');
    // over RR the roots of the exact polynomial are counted (SymPy count_roots() over RR gives 2 for x**2 - 2.0)
    if (this.domain === 'RR') return this.toExact().countRoots(a, b);
    const seq = this.sqfPartQQ().sturm();
    const signChanges = (v: Expr | 'inf' | '-inf'): number => {
      const vals = seq.map((p) => {
        if (v === 'inf' || v === '-inf') {
          const sign = p.LC() instanceof Rational ? Math.sign(numValue(p.LC())) : compareAlgebraicReal(p.LC(), S.Zero);
          const d = p.degree();
          return v === 'inf' ? sign : sign * (d % 2 === 0 ? 1 : -1);
        }
        const r = xreplace(p.asExpr(), [[x, v]]);
        return r instanceof Rational ? Math.sign(numValue(r)) : compareAlgebraicReal(r, S.Zero);
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
    // a bound with an imaginary part: the roots in the rectangle of the two corners (SymPy dup_count_complex_roots)
    const corner = (v: ExprLike | undefined): [Rational, Rational] | undefined => (v === undefined ? undefined : pair(asRealImag(sympify(v)).map(bound)));
    const lower = a !== undefined && sympify(a).key === S.NegativeInfinity.key ? undefined : a;
    const upper = b !== undefined && sympify(b).key === S.Infinity.key ? undefined : b;
    const [ca, cb] = [corner(lower), corner(upper)];
    if ([ca, cb].some((c) => c !== undefined && !c[1].isZero)) return countComplexRoots(this.denseInts(), ca, cb);
    const lo = lower === undefined ? '-inf' : bound(lower);
    const hi = upper === undefined ? 'inf' : bound(upper);
    let n = signChanges(lo) - signChanges(hi);
    if (lo !== '-inf') {
      if (expandFull(xreplace(this.asExpr(), [[x, lo]])).equals(0)) n += 1;
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
      if (f.degree() === 1) {
        const value=f.neg().quoGround(f.LC()).TC();
        out.push([value,k]);
      }
    }
    return out;
  }
  /** Series reversion: g with f*g = 1 mod x**n. */
  revert(n: number): Poly {
    const x = this.univariate();
    if(this.finiteModulus !== undefined){
      let g=this.like(1).quoGround(this.TC());
      for(let precision=2;precision<2*n;precision*=2){
        const next=g.mulGround(2).sub(this.mul(g.sqr()));
        g=this.like(add(...next.termList.filter((t)=>first(t.monom)<precision).map((t)=>next.termExpr(t))));
      }
      return g;
    }
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
    if (!Number.isInteger(n) || n < 1) throw new RangeError('a positive integer power is required');
    if (n === 1) return this;
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
    const norm = this.normPoly();
    if (!norm) return undefined;
    const N=norm.sqfPart(),x=this.univariate();
    if (realOnly && this.coeffs().every((c) => isReal(c) === true) && this.gcd(this.diff()).degree() === 0) {
      const normRoots = N.rootsWhere(true);
      // The norm contains every real root of this square-free polynomial.
      // Equal Sturm counts certify that it adds no roots for this embedding.
      if (normRoots.length === this.countRoots()) return normRoots;
    }
    const zeroTest=(p:Poly):((r:Expr)=>boolean)=>{
      const t=new Dummy('value');
      const residual=defined(p.like(add(p.asExpr(),mul(-1,t)),[x,t]).algebraicNorm(),'residual norm');
      const valuePolynomial=Poly.from(resultant(N.asExpr(),residual.asExpr(),x),[t]);
      const cs=valuePolynomial.terms().sort(([a],[b])=>first(a)-first(b)).map(([,c])=>asRational(c,'rational norm coefficient'));
      const absolute=(q:Rational):Rational=>q.p<0n?Rational.of(-q.p,q.q):q;
      const constant=absolute(first(cs)),height=add(...cs.map(absolute));
      // A reciprocal Cauchy bound separates zero from every nonzero residual.
      const bound=asRational(mul(constant,pow(height,-1)),'residual separation');
      return (r:Expr):boolean=>{
        const value=add(...p.termList.map((term)=>mul(term.coeff,pow(r,first(term.monom)))));
        for(let bits=32;;bits*=2){
          try {
            const box=algebraicEnclosure(value,bits);
            if(box.some(([lo,hi])=>lo.p>0n||hi.p<0n))return false;
            const size=asRational(add(...box.map(([lo,hi])=>lo.p*lo.p*hi.q*hi.q>hi.p*hi.p*lo.q*lo.q?absolute(lo):absolute(hi))),'residual size');
            if(size.p*bound.q<bound.p*size.q)return true;
          }catch(error){if(!(error instanceof RangeError))throw error;}
        }
      };
    };
    const tests:((r:Expr)=>boolean)[]=[];
    // GCDs with successive derivatives recover multiplicities of f, rather
    // than the extra multiplicities introduced by the coefficient-field norm.
    for(let g:Poly=this;g.degree()>0;g=g.gcd(g.diff()))tests.push(zeroTest(g));
    return N.rootsWhere(realOnly).flatMap((r)=>{
      let multiplicity=0;
      for(const test of tests){if(!test(r))break;multiplicity++;}
      return Array.from({length:multiplicity},()=>r);
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
    return defined(this.algebraicNorm(),'algebraic norm');
  }
  /** The product of the conjugates over I and square roots of integers; undefined when they do not give a rational polynomial. */
  private algebraicNorm(): Poly | undefined {
    const K = this.algebraicField;
    if (K) {
      const data = defined(polyConstructionHooks.algebraic, 'algebraic field data')(K);
      if (this.isUnivariate && !this.isZero) {
        const minpoly = new UPoly(data.minpoly.allCoeffs().map((c) => asRational(c, 'minimal polynomial coefficient')).reverse());
        const coefficients = this.allCoeffs().map((c) => new UPoly(data.coefficients(c).reverse()));
        // The norm has degree at most [K:QQ] * degree(f). Evaluating the
        // resultant at consecutive integers avoids symbolic PRS growth.
        let samples = Array.from({ length: minpoly.degree * this.degree() + 1 }, (_, i) => {
          const x = Rational.of(i);
          const value = coefficients.reduce((p, c) => p.scale(x).add(c), new UPoly([]));
          return rationalResultant(minpoly, value);
        });
        let norm = new UPoly([]), basis = new UPoly([S.One]);
        for (let i = 0; samples.length > 0; i++) {
          norm = norm.add(basis.scale(first(samples)));
          samples = samples.slice(1).map((v, j) => asRational(add(v, mul(-1, at(samples, j))), 'forward difference'));
          basis = basis.mul(new UPoly([Rational.of(-i), S.One])).scale(Rational.of(1, i + 1));
        }
        return Poly.from(norm.toExpr(this.gen), this.gens, { domain: 'QQ' });
      }
      const t = new Dummy('theta');
      const polynomial = add(...this.termList.map((term) => {
        const cs = data.coefficients(term.coeff);
        return mul(add(...cs.map((c,i) => mul(c,pow(t,cs.length-1-i)))),...term.monom.map((e,i) => pow(at(this.gens,i),e)));
      }));
      return Poly.from(resultant(data.minpoly.asExpr().subs(data.minpoly.gen,t),polynomial,t),this.gens,{domain:'QQ'});
    }
    const cs = this.termList.map((t) => t.coeff);
    const gens = new Map<string, Expr>();
    const findGens = (e: Expr) => {
      if (e instanceof Constant && e.name === 'I') gens.set(e.key, e);
      else if (e instanceof Pow && e.base instanceof Rational && e.base.isInteger && e.exp instanceof Rational && e.exp.key === S.Half.key) gens.set(e.key, e);
      else e.args.forEach(findGens);
    };
    cs.forEach(findGens);
    // the generators of an algebraic field domain QQ<a> count too (QQ<sqrt(2) + sqrt(3)> has degree 4)
    const gl = [...gens.values()];
    if (!gl.length || gl.length > 3) return undefined;
    const f = this.asExpr();
    let norm: Expr = S.One;
    for (let mask = 0; mask < 1 << gl.length; mask++) {
      norm = mul(norm, xreplace(f, gl.map((g, i) => [g, mask & (1 << i) ? mul(-1, g) : g] as [Expr, Expr])));
    }
    const N = Poly.from(expand(norm), this.gens);
    return N.termList.every((t) => t.coeff instanceof Rational) ? Poly.from(N.asExpr(), this.gens, { domain: 'QQ' }) : undefined;
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
    for (const c of this.coeffs()) if (!(c instanceof Rational && c.isInteger)) throw new DomainError('set_modulus: integer coefficients expected');
    const q = this.finiteModulus;
    const expr = q === undefined ? this.asExpr() : add(...this.termList.map((t) => this.termExpr({ ...t, coeff: finiteCoefficient(t.coeff, q, false) })));
    return Poly.from(expr, this.gens, { modulus: p });
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
  realRoots(opts: { extension?: boolean; radicals?: boolean } = {}): Expr[] {
    if (opts.extension === false && this.isUnivariate && !(this.gen instanceof Sym)) throw new PolynomialError('a symbolic generator is required');
    if (opts.extension === false && this.domain === 'EX') throw new NotImplementedError('real root isolation requires a coefficient extension');
    return opts.extension ? this.radicalRoots(true) : this.rootsWhere(true, opts.radicals);
  }
  allRoots(opts: { extension?: boolean; radicals?: boolean } = {}): Expr[] {
    if (opts.extension === false && this.domain === 'EX') throw new NotImplementedError('root isolation requires a coefficient extension');
    return opts.extension ? this.radicalRoots(false) : this.rootsWhere(false, opts.radicals);
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
    const rs=rootsOf(this.asExpr(),this.univariate()).map(tidy);
    const real=rs.filter((r)=>isReal(r)===true).sort(compareAlgebraicReal);
    const cplx=rs.filter((r)=>isReal(r)!==true).sort((a,b)=>{
      const [ar,ai]=asRealImag(a),[br,bi]=asRealImag(b);
      return compareAlgebraicReal(ar,br)||compareAlgebraicReal(ai,bi);
    });
    return realOnly?real:[...real,...cplx];
  }
  private rootsWhere(realOnly: boolean, radicals = true): Expr[] {
    if (this.isZero) return [];
    if (this.isUnivariate && !(this.gen instanceof Sym)) {
      const x = new Sym('x');
      return Poly.from(xreplace(this.asExpr(), [[this.gen, x]]), [x], { domain: this.domain }).rootsWhere(realOnly, radicals);
    }
    if(this.finiteModulus!==undefined || this.domain!=='ZZ'&&this.domain!=='QQ'&&this.termList.every((t)=>t.coeff instanceof Rational))return this.retract().rootsWhere(realOnly,radicals);
    if (this.degree() === 1) {
      const r = cancel(mul(-1,this.TC(),pow(this.LC(),-1)));
      return !realOnly || isReal(r) === true ? [r] : [];
    }
    const lifted = this.liftedRoots(realOnly);
    if (lifted) return lifted;
    const x = this.univariate();
    const primitive = this.clearDenoms(true)[1].primitive()[1];
    const preprocessing = preprocessRootCoefficients(new Map(primitive.termList.map((t)=>[first(t.monom),t.coeff])));
    if (preprocessing) {
      const [scale,cs]=preprocessing;
      const normalized=Poly.from(add(...[...cs].map(([k,c])=>mul(c,pow(x,k)))),[x]);
      return normalized.rootsWhere(realOnly,radicals).map((r)=>mul(scale,r));
    }
    if (!['ZZ', 'QQ'].includes(this.domain)) throw new DomainError(`root isolation over ${this.domain}`);
    const [, fs] = this.factorList();
    const ranks = fs.map(() => [] as number[]);
    isolateRealRootsTagged(fs.map(([f]) => f.denseInts())).forEach(([,i],rank) => at(ranks,i).push(rank));
    type R = [Expr, number];
    const real: R[] = [];
    // SymPy _all_roots: the non-real roots grouped by irreducible factor (as PurePoly in ordered() order),
    // each factor's in its CRootOf index order (by isolating rectangle, the conjugate first)
    const cplx = new Map<string, Expr[]>();
    const factorExprs: Expr[] = [];
    for (const [factorIndex, [f, k]] of fs.entries()) {
      const roots: Expr[] = [];
      const group = (r: Expr) => {
        for (let j = 0; j < k; j++) roots.push(r);
      };
      // SymPy _roots_trivial: radicals for linear factors, and with radicals for quadratic and binomial ones
      const trivial = f.degree() === 1 || (radicals && (f.degree() === 2 || (f.termList.length === 2 && !f.TC().equals(0))));
      if (!trivial) {
        // irreducible factors of degree >= 3: CRootOf(f, i) like SymPy, the real roots first
        const nreal = at(ranks,factorIndex).length;
        const crootof = defined(rootHooks.crootof, 'crootof hook');
        for (let i = 0; i < (realOnly ? nreal : f.degree()); i++) {
          const r = crootof(xreplace(f.asExpr(), [[x, new Sym('x')]]), i);
          if (i < nreal) for (let j = 0; j < k; j++) real.push([r, at(at(ranks,factorIndex),i)]);
          else group(r);
        }
      } else {
        // in the CRootOf index order: by real part, a conjugate pair with the negative imaginary part first
        const rs=rootsOf(f.asExpr(),x);
        const rr=rs.filter((r)=>isReal(r)===true).sort(compareAlgebraicReal);
        rr.forEach((r,i)=>{for(let j=0;j<k;j++)real.push([r,at(at(ranks,factorIndex),i)]);});
        const byRe=(a:Expr,b:Expr):number=>{
          const [ar,ai]=asRealImag(a),[br,bi]=asRealImag(b);
          return compareAlgebraicReal(ar,br)||compareAlgebraicReal(ai,bi);
        };
        for(const r of rs.filter((r)=>isReal(r)!==true).sort(byRe))group(r);
      }
      if (!roots.length) continue;
      const e = f.primitiveExpr();
      factorExprs.push(e);
      cplx.set(e.key, roots);
    }
    real.sort((a, b) => a[1] - b[1]);
    if (realOnly) return real.map(([r]) => r);
    return [...real.map(([r]) => r), ...orderedExprs(factorExprs).flatMap((e) => getOrThrow(cplx, e.key))];
  }
  /** Trager's square-free norm and GCD reconstruction over an algebraic number field. */
  private factorAlgebraic(): [Expr,[Poly,number][]] {
    const K = defined(this.algebraicField), original = this.fieldPoly(K);
    if (original.isZero) return [S.Zero,[]];
    const lc = first(original.terms)[1];
    let F = original.monic();
    if (this.totalDegree() === 0) return [K.toSympy(lc),[]];
    if(this.totalDegree()===1)return [K.toSympy(lc),[[this.like(F.asExpr(this.gens)),1]]];
    if(this.termList.every((t)=>t.coeff instanceof Rational)){
      const [c,fs]=factorListInt(this.asExpr(),this.gens);
      if(fs.length>1||fs.some(([,k])=>k>1)){
        let content:Expr=c;
        const factors:[Poly,number][]=[];
        for(const [f,k] of fs){
          const [a,gs]=this.like(f).factorAlgebraic();
          content=mul(content,pow(a,k));
          for(const [g,m] of gs)factors.push([g,m*k]);
        }
        factors.sort(([a],[b])=>a.totalDegree()-b.totalDegree()||compareExpr(a.asExpr(),b.asExpr()));
        return [content,factors];
      }
    }
    let repeated = F;
    for (let i=0;i<this.gens.length;i++) repeated = repeated.gcd(F.diff(i));
    const squarefree = this.like(F.exquo(repeated).asExpr(this.gens));
    const { generator } = defined(polyConstructionHooks.algebraic,'algebraic field data')(K);
    const [shifts,shifted,norm] = squarefree.squarefreeNorm();
    let remaining = shifted.fieldPoly(K);
    const factors: [Poly,number][] = [];
    for (const [h] of norm.factorList()[1]) {
      const g = remaining.gcd(this.like(h.asExpr()).fieldPoly(K));
      remaining = remaining.exquo(g);
      const back = g.shift(shifts.map((k)=>K.convert(mul(k,generator)))).monic();
      let multiplicity=0;
      for (;;) {
        const [q,r]=F.div(back);
        if (!r.isZero) break;
        F=q;multiplicity++;
      }
      factors.push([this.like(back.asExpr(this.gens)),multiplicity]);
    }
    factors.sort(([a],[b])=>a.totalDegree()-b.totalDegree() || compareExpr(a.asExpr(),b.asExpr()));
    return [K.toSympy(lc),factors];
  }
  root(i: number): Expr {
    return at(this.allRoots(), i);
  }
  /** Compare two roots using a separation bound for this polynomial. */
  sameRoot(a: Expr, b: Expr): boolean {
    if (this.isMultivariate) throw new MultivariatePolynomialError('a univariate polynomial is required');
    if (!['ZZ', 'QQ', 'RR'].includes(this.domain)) throw new DomainError(`root separation is not supported over ${this.domain}`);
    if (this.degree() < 2) throw new PolynomialError('root separation requires degree at least two');
    if (a.key === b.key) return true;
    const exact = this.toExact();
    const f = exact.exquo(exact.gcd(exact.diff())).clearDenoms(true)[1];
    const n = f.degree();
    if (n <= 1) return true;
    const normSquared = add(...f.coeffs().map((c) => pow(c, 2)));
    const discriminant = asRational(f.discriminant(), 'discriminant');
    const absolute = Rational.of(discriminant.p < 0n ? -discriminant.p : discriminant.p, discriminant.q);
    const epsilonSquared = asRational(mul(absolute, Rational.of(1, 3), pow(n, -n - 1), pow(normSquared, 1 - n)), 'root separation bound');
    const digits = Math.ceil(epsilonSquared.q.toString().length / 2) + 10;
    const rationalParts = (root: Expr): [Rational, Rational] => pair(asRealImag(evalfExpr(root, digits)).map((e) => Rational.of(...defined(groundRational(e), 'numeric root component'))));
    const [ar, ai] = rationalParts(a), [br, bi] = rationalParts(b);
    const distanceSquared = asRational(add(pow(add(ar, mul(-1, br)), 2), pow(add(ai, mul(-1, bi)), 2)), 'root distance');
    return distanceSquared.p * epsilonSquared.q < epsilonSquared.p * distanceSquared.q;
  }
  whichRealRoots(cands: readonly Expr[]): Expr[] {
    this.univariate();
    if (this.domain !== 'ZZ' && this.domain !== 'QQ' && !this.domain.startsWith('QQ<')) {
      throw new NotImplementedError(`root counting not supported over ${this.domain}`);
    }
    return this.whichRoots(cands, this.countRoots());
  }
  whichAllRoots(cands: readonly Expr[]): Expr[] {
    this.univariate();
    return this.whichRoots(cands, this.degree());
  }
  private whichRoots(cands: readonly Expr[], rootCount: number): Expr[] {
    const x = this.univariate();
    const candidates = new Map(cands.map((c) => [c.key, c]));
    if (candidates.size <= rootCount) return [...candidates.values()];
    const out: Expr[] = [];
    for (const c of candidates.values()) {
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
  if(f.domain.startsWith('GF(')){
    const P=(e:ExprLike):Poly=>Poly.from(e,[x],{domain:f.domain});
    const n=f.degree();
    for(let s=2;s<n;s++){
      if(n%s)continue;
      const r=n/s;let h=P(pow(x,s));
      for(let i=1;i<s;i++){
        const c=add(...Array.from({length:i},(_,j)=>mul(i-r*j,f.nth(n+j-i),h.nth(s-j))));
        h=h.add(mul(P(c).quoGround(mul(i*r,f.LC())).TC(),pow(x,s-i)));
      }
      let current=f,g=P(0),degree=0;
      while(!current.isZero){
        const [q,rem]=current.div(h);
        if(rem.degree()>0)break;
        g=g.add(mul(rem.TC(),pow(x,degree++)));current=q;
      }
      if(current.isZero)return [g,h];
    }
    return undefined;
  }
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
  gaussian?: boolean;
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
  if (opts.gaussian) {
    const [cp, fp] = factorListOverGaussian(numer, gens);
    const [cq, fq] = factorListOverGaussian(denom, gens);
    if (!opts.frac && fq.length) throw new PolynomialError(`a polynomial expected, got ${str(e)}`);
    const c = mul(cp, pow(cq, -1));
    return opts.frac ? [c, fp, fq] : [c, fp];
  }
  const [cp, fp] = symbolicFactorList(numer, gens);
  const [cq, fq] = symbolicFactorList(denom, gens);
  const frac = opts.frac === true;
  if (fq.length && !frac) throw new PolynomialError(`a polynomial expected, got ${str(e)}`);
  const content = mul(cp, pow(cq, -1));
  const numerFactors = sortedFactors(fp, gens);
  return frac ? [content, numerFactors, sortedFactors(fq, gens)] : [content, numerFactors];
}

function factorListOverGaussian(e: Expr, gens: readonly Expr[]): FactorList {
  const factored = factorOverExtension(e, [S.I]);
  let coefficient: Expr = S.One;
  const factors: [Expr, Expr][] = [];
  for (const t of factored instanceof Mul ? factored.args : [factored]) {
    if (gens.length ? !gens.some((g) => t.has(g)) : t.freeSymbols().size === 0) coefficient = mul(coefficient, t);
    else factors.push(t instanceof Pow && t.exp instanceof Rational && t.exp.isInteger ? [t.base, t.exp] : [t, S.One]);
  }
  const ordered = factors.map((factor) => ({ factor, polynomial: Poly.from(factor[0]) }));
  ordered.sort((a, b) => {
    const p = a.polynomial, q = b.polynomial;
    const degree = p.totalDegree() - q.totalDegree() || p.gens.length - q.gens.length;
    if (degree) return degree;
    return compareGaussianCoefficients(p.coeffs(), q.coeffs());
  });
  return [coefficient, ordered.map(({ factor }) => factor)];
}

function compareGaussianCoefficients(a: readonly Expr[], b: readonly Expr[]): number {
  const length = a.length - b.length;
  if (length) return length;
  for (const [i, value] of a.entries()) {
    const [real, imaginary] = asRealImag(expand(add(value, mul(-1, at(b, i)))));
    for (const part of [real, imaginary]) if (part instanceof Rational && !part.isZero) return part.isNegative ? -1 : 1;
  }
  return 0;
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

/** The domains over which SymPy's gcd and lcm are monic (dmp_ff_prs_gcd, dmp_ff_lcm). */
const MONIC_DOMAINS = new Set(['QQ', 'RR', 'CC']);

/** Two polynomials over a common field among MONIC_DOMAINS, or undefined. */
function fieldPair(a: Poly, b: Poly): [Poly, Poly] | [undefined, undefined] {
  if (!MONIC_DOMAINS.has(a.domain) && !MONIC_DOMAINS.has(b.domain)) return [undefined, undefined];
  const [f, g] = a.unify(b);
  return MONIC_DOMAINS.has(f.domain) ? [f, g] : [undefined, undefined];
}

/** The polynomial as an expression with its floating-point coefficients made exact (SymPy RR.to_rational). */
const exactCoeffs = (p: Poly): Expr => mapBottomUp(p.asExpr(), (e) => (e instanceof Float ? QQ.fromSympy(e) : e));

const mulR = (a: Rational, b: Rational): Rational => asRational(mul(a, b), 'product of rationals');
const powR = (a: Rational, k: number): Rational => asRational(pow(a, k), 'power of a rational');

// ---------------------------------------------------------------------------
// printing (SymPy StrPrinter._print_Poly)
// ---------------------------------------------------------------------------

function coeffStr(c: Expr): string {
  if (c instanceof Float) {
    const v = c.value;
    return Number.isInteger(v) && Math.abs(v) < 1e21 ? `${v}.0` : `${Number(v.toPrecision(15))}`;
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
  for (const f of fs) for (const s of [...freeSymbols(f)].filter((s) => s instanceof Sym)) m.set(s.key, s);
  return sortGens([...m.values()]);
};

/** The generators of several expressions as Poly detects them (symbols and non-rational atoms such as sqrt(2)). */
const gensFor = (...fs: Expr[]): Expr[] => {
  const m = new Map<string, Expr>();
  for (const f of fs) for (const g of detectGens(expand(f))) m.set(g.key, g);
  return sortGens([...m.values()]);
};

/** gcd of polynomials (expressions). */
export function polyGcd(f: Poly | ExprLike, g: Poly | ExprLike, opts: PolynomialDomainOptions = {}): Expr {
  if (opts.extension !== undefined) {
    const vars = varsFor(toExpr(f), toExpr(g));
    return Poly.from(toExpr(f), vars, { extension: opts.extension }).gcd(Poly.from(toExpr(g), vars, { extension: opts.extension })).asExpr();
  }
  if (opts.domain !== undefined || opts.modulus !== undefined) {
    const vars = varsFor(toExpr(f), toExpr(g));
    return Poly.from(toExpr(f), vars, opts).gcd(Poly.from(toExpr(g), vars, opts)).asExpr();
  }
  if (f instanceof Poly && g instanceof Poly) return f.gcd(g).asExpr();
  const a = toExpr(f);
  const b = toExpr(g);
  // SymPy parallel_poly_from_expr: algebraic numbers (sqrt(2), pi) are generators unless an extension is given
  const gens = gensFor(a, b);
  return algebraicGcdLcm(a, b, 'gcd') ?? fieldGcdLcm(a, b, gens, 'gcd') ?? mgcd(a, b, gens);
}
export function polyLcm(f: Poly | ExprLike, g: Poly | ExprLike, opts: PolynomialDomainOptions = {}): Expr {
  if (opts.extension !== undefined) {
    const vars = varsFor(toExpr(f), toExpr(g));
    return Poly.from(toExpr(f), vars, { extension: opts.extension }).lcm(Poly.from(toExpr(g), vars, { extension: opts.extension })).asExpr();
  }
  if (opts.domain !== undefined || opts.modulus !== undefined) {
    const vars = varsFor(toExpr(f), toExpr(g));
    return Poly.from(toExpr(f), vars, opts).lcm(Poly.from(toExpr(g), vars, opts)).asExpr();
  }
  if (f instanceof Poly && g instanceof Poly) return f.lcm(g).asExpr();
  const a = toExpr(f);
  const b = toExpr(g);
  const gens = varsFor(a, b);
  return algebraicGcdLcm(a, b, 'lcm') ?? fieldGcdLcm(a, b, gens, 'lcm') ?? mlcm(a, b, gens);
}

/**
 * SymPy gcd and lcm of two irrational algebraic numbers with a rational ratio a/b = n/d
 * (the domain Q[irrational]): |a/n| and a*d; undefined otherwise.
 */
function algebraicGcdLcm(a: Expr, b: Expr, op: 'gcd' | 'lcm'): Expr | undefined {
  const irrational = (e: Expr): boolean => !(e instanceof Rational) && algebraicNumber(e) && isReal(e) === true;
  if (!irrational(a) || !irrational(b)) return undefined;
  const frc = cancel(mul(a, pow(b, -1)));
  if (!(frc instanceof Rational)) return undefined;
  if (op === 'lcm') return mul(a, Rational.of(frc.q));
  const g = mul(a, Rational.of(1n, frc.p));
  return isPositive(g) === false ? mul(-1, g) : g;
}

/** A number built from rationals by sums, products and rational powers. */
function algebraicNumber(e: Expr): boolean {
  if (e instanceof Rational) return true;
  if (e instanceof Pow) return e.exp instanceof Rational && algebraicNumber(e.base);
  return (e instanceof Add || e instanceof Mul) && e.args.every(algebraicNumber);
}

/**
 * The gcd or lcm over QQ, RR or CC as SymPy computes it from the expressions: monic polynomials,
 * and for numbers the domain's gcd (one over RR and CC) or lcm (the product over RR and CC);
 * undefined for other domains.
 */
function fieldGcdLcm(a: Expr, b: Expr, gens: readonly Expr[], op: 'gcd' | 'lcm'): Expr | undefined {
  if (gens.length === 0) {
    if (!(isNum(a) && isNum(b)) || ![a, b].some((e) => e instanceof Float)) return undefined;
    // SymPy RealField.gcd and lcm
    return op === 'gcd' ? new Float(1) : mul(a, b);
  }
  if (!isPolynomial(a, gens) || !isPolynomial(b, gens)) return undefined;
  const [f, g] = fieldPair(Poly.from(a, gens), Poly.from(b, gens));
  if (f === undefined) return undefined;
  return (op === 'gcd' ? f.gcd(g) : f.lcm(g)).asExpr();
}

/** Degree of f in gen (default: the only/first generator). */
export function degree(f: Poly | ExprLike, gen?: Expr | number): number {
  const p = f instanceof Poly ? f : Poly.from(f);
  if (gen === undefined || typeof gen === 'number') {
    if (!(f instanceof Poly) && p.freeSymbols().size > 1) throw new TypeError('a symbolic generator of interest is required');
    if (gen !== undefined && !Number.isInteger(gen)) throw new PolynomialError('a valid generator index is required');
    return p.degree(gen);
  }
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
  if (orig instanceof Rel) {
    if (orig.op !== 'Eq') throw new TypeError('terms_gcd requires a polynomial expression or an equality');
    return new Rel(orig.op, termsGcd(orig.lhs, ...rest), termsGcd(orig.rhs, ...rest));
  }
  if (orig.args.length === 0 || isNum(orig)) return orig;
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
      if (isNum(g) && !(g instanceof Pow) && !(g instanceof Constant)) return orig;
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
  if (isNum(e)) return e;
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

/** Euclidean resultant over QQ. The leading coefficients account for each reduction. */
function rationalResultant(left: UPoly, right: UPoly): Rational {
  let a = left, b = right;
  let product = S.One;
  while (!b.isZero) {
    if (b.degree === 0) return mulR(product, powR(b.lc, a.degree));
    const r = a.divmod(b)[1];
    if ((a.degree * b.degree) % 2 !== 0) product = mulR(product, S.NegOne);
    product = mulR(product, powR(b.lc, a.degree - r.degree));
    [a, b] = [b, r];
  }
  return S.Zero;
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
 * factor(f, modulus=p)), using the requested coefficient presentation.
 */
function factorModulus(e: Expr, p: bigint, symmetric:boolean): Expr {
  const vars = [...freeSymbols(e)].filter((s) => s instanceof Sym);
  const [x] = vars;
  if (x === undefined || vars.length !== 1) throw new PolynomialError('factor: modulus requires a univariate polynomial');
  const cs = polyCoefficients(e, x);
  if (!cs) throw new DomainError('factor: modulus requires integer coefficients');
  const ints = new Map<number, bigint>();
  for (const [k, c] of cs) {
    if (!(c instanceof Rational && c.q === 1n)) throw new DomainError('factor: modulus requires integer coefficients');
    ints.set(k, c.p);
  }
  if(!isprime(p)){
    const [c,fs]=Poly.from(e,[x],{modulus:p,symmetric}).factorList();
    return keepCoeff(c,mul(...fs.map(([f,k])=>pow(f.asExpr(),k))));
  }
  const n = Math.max(...cs.keys());
  const f = Array.from({ length: n + 1 }, (_, i) => ints.get(i) ?? 0n);
  const sym = (c: bigint) => (symmetric && c > p / 2n ? c - p : c);
  const [lc, fs] = factorModP(f, p);
  const toExpr = (g: bigint[]) => add(...g.map((c, i) => mul(Rational.of(sym(c)), pow(x, i))));
  return keepCoeff(Rational.of(sym(lc)), mul(...fs.map(([g, m]) => pow(toExpr(g), m))));
}

/** Clear denominators, remove content and scale away removable coefficient generators. */
export function preprocessRoots(p:Poly): [Expr,Poly] {
  if(p.domain==='RR'||p.domain==='CC')return [S.One,p];
  if(p.isZero)return [S.One,Poly.from(0,p.gens,{pure:p.pure})];
  const f=p.clearDenoms(true)[1].primitive()[1].retract();
  if(!f.isUnivariate)return [S.One,Poly.from(f.asExpr(),f.gens,{domain:f.domain,pure:p.pure})];
  const pre=preprocessRootCoefficients(new Map(f.termList.map((t)=>[first(t.monom),t.coeff])));
  if(!pre)return [S.One,Poly.from(f.asExpr(),f.gens,{domain:f.domain,pure:p.pure})];
  const [scale,cs]=pre;
  const result = Poly.from(add(...[...cs].map(([k,c])=>mul(c,pow(f.gen,k)))),[f.gen],{pure:p.pure});
  if (result.domain !== 'EX') return [scale, result];
  const domain = formalCoefficientDomain(result.coeffs());
  return [scale, domain ? Poly.from(result.asExpr(), result.gens, { domain, pure: p.pure }) : result];
}

/** Recognize polynomial coefficient domains with formal function generators. @internal */
export function formalCoefficientDomain(coeffs: readonly Expr[]): string | undefined {
  const gens = new Map<string, Expr>();
  let rational = false;
  for (const c of coeffs) for (const t of c instanceof Add ? c.args : [c]) {
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) {
        rational ||= !f.isInteger;
        continue;
      }
      const g = f instanceof Pow && f.exp instanceof Rational && f.exp.isPositive && f.exp.isInteger ? f.base : f;
      if (!(g instanceof Fn || g instanceof Sym || g instanceof Pow && g.base.key === S.E.key)) return undefined;
      gens.set(g.key, g);
    }
  }
  return gens.size ? `${rational ? 'QQ' : 'ZZ'}[${sortGens([...gens.values()]).map(str).join(',')}]` : undefined;
}

export function factor(ex: ExprLike, opts: PolynomialDomainOptions & { deep?: boolean; gaussian?: boolean; fraction?: boolean; gens?: readonly Expr[]; expand?: boolean } = {}): Expr {
  const e = sympify(ex);
  if (e instanceof Rel) return new Rel(e.op, factor(e.lhs, opts), factor(e.rhs, opts));
  if (!e.args.length && !e.isCommutative) return e;
  if (opts.expand === false && opts.gens?.some((g) => hasUnexpandedFactors(e, g))) throw new PolynomialError('unexpanded factor contains a polynomial generator');
  const modulus = modulusOption(opts);
  if (modulus !== undefined) return factorModulus(sympify(ex), modulus,finiteSymmetricOption(opts));
  const domain = String(opts.domain), algebraic = /^QQ<(.+)>$/.exec(domain);
  const algebraicDomain=algebraic && typeof opts.domain==='object'?opts.domain:undefined;
  const domainExtension = domain === 'ZZ_I' || domain === 'QQ_I' ? [S.I] : algebraic ? algebraicDomain?[]:[parse(at(algebraic,1))] : undefined;
  if (opts.domain !== undefined && !domainExtension && !['ZZ','QQ'].includes(domain)) throw new NotImplementedError(`factor over ${domain}`);
  const requested=opts.extension ?? domainExtension;
  const isList=(value:unknown):value is readonly ExprLike[]=>Array.isArray(value);
  const extension=requested===true?true:requested===false||requested===undefined?undefined:isList(requested)?requested.map((e)=>sympify(e)):[sympify(requested)];
  if (!opts.deep && (opts.gaussian || extension===true || extension?.length || algebraicDomain)) {
    return factorOverExtension(sympify(ex), opts.gaussian ? [S.I] : defined(extension, 'extension'),algebraicDomain);
  }
  if (opts.deep) {
    // SymPy deep=True: factor bottom up (keeping the products and powers), then the sums and products inside
    const sub = { ...opts, deep: false };
    const tryFactor = (t: Expr): Expr => {
      if (t instanceof Fn || t.args.length === 0) return t;
      const opaque = new Map<string, [Expr, Expr]>();
      const visit = (e: Expr): void => {
        if (e instanceof Fn) {
          if (!opaque.has(e.key)) opaque.set(e.key, [e, new Dummy('f')]);
        } else e.args.forEach(visit);
      };
      t.args.forEach(visit);
      const replacements = [...opaque.values()];
      const fac = factor(xreplace(t, replacements), sub);
      return fac instanceof Mul || fac instanceof Pow ? xreplace(fac, replacements.map(([f, d]) => [d, f])) : t;
    };
    // (SymPy's second pass over the sums and products finds nothing the bottom-up pass has not tried)
    return mapBottomUp(sympify(ex), tryFactor);
  }
  // SymPy: a PolynomialError for non-commutative expressions leads to factor_nc
  if (!e.isCommutative) return factorNc(e);
  if (e instanceof Add && opts.domain === undefined && opts.extension === undefined && (e.has(S.I) || e.args.some((t) => (t instanceof Mul ? t.args : [t]).some((a) => a instanceof Float)))) {
    // SymPy together (gcd_terms): a Float that is the coefficient of every term up to its sign is taken out,
    // and the rest is factored exactly (1.5*x + 1.5 is 1.5*(x + 1))
    const parts = e.args.map((t): [Float | undefined, Expr] => {
      const float = t instanceof Float ? t : t instanceof Mul ? t.args.find((a): a is Float => a instanceof Float) : undefined;
      return [float, float === undefined || t instanceof Float ? S.One : mul(...(t instanceof Mul ? t.args : []).filter((a) => a !== float))];
    });
    const leading = at(parts, 0)[0];
    const magnitude = Math.abs(leading?.toNumber() ?? 1);
    if (leading !== undefined && parts.every(([c]) => c !== undefined && Math.abs(c.toNumber()) === magnitude)) {
      const inner = add(...parts.map(([c, rest]) => ((c?.toNumber() ?? 1) < 0 ? mul(-1, rest) : rest)));
      if (!some(inner, (a) => a instanceof Float)) {
        // the sign goes with the Float so that the leading coefficient of the rest is positive
        const positive = leading.toNumber() < 0 ? mul(-1, leading) : leading;
        const negative = isNegativeLeading(inner, opts.gens);
        return keepCoeff(negative ? mul(-1, positive) : positive, factor(negative ? mul(-1, inner) : inner, opts));
      }
    }
    const p = Poly.from(e, opts.gens);
    // (generators that are functions, such as sin(x), are factored symbolically below)
    if (p.domain === 'RR' && p.gens.length && p.gens.every((g) => g instanceof Sym)) return factorInexactReal(p);
    if (p.domain === 'ZZ_I' && p.isUnivariate && p.degree() > 1) return factorGaussianInteger(p);
  }
  return symbolicFactor(e, opts.fraction !== false);
}

function primitiveGaussian(f: Poly, K: Domain): [Expr, Poly] {
  const denominator = f.coeffs().flatMap(asRealImag).reduce((d, c) => ilcm(d, asRational(c, 'Gaussian coefficient').q), 1n);
  const integral = f.mulGround(Rational.of(denominator)).setDomain(K);
  const common = integral.coeffs().reduce((g, c) => K.toSympy(K.gcd(g, c)), S.Zero);
  return [mul(common, Rational.of(1n, denominator)), integral.mulGround(pow(common, -1)).setDomain(K)];
}

/** Whether the leading coefficient of e as a polynomial is negative (false when e is no polynomial). */
function isNegativeLeading(e: Expr, gens?: readonly Expr[]): boolean {
  try {
    const lc = Poly.from(e, gens).LC();
    return lc instanceof Rational && lc.isNegative;
  } catch {
    return false;
  }
}

/** Factor over RR through QQ and normalize the factors by their maximum coefficient. */
function factorInexactReal(p: Poly): Expr {
  const [content, factors] = p.toExact().factorList();
  let coefficient = content;
  const exprs = factors.map(([f, k]) => {
    // (SymPy takes a generator common to all terms out before the polynomial is built: it stays exact)
    if (f.termList.length === 1 && f.LC().equals(S.One)) return pow(f.asExpr(), k);
    const norm = f.maxNorm();
    coefficient = mul(coefficient, pow(norm, k));
    const normalized = Poly.from(f.mulGround(pow(norm, -1)).asExpr(), p.gens, { domain: 'RR' });
    return pow(normalized.asExpr(), k);
  });
  return exprs.length > 1 ? new Mul([impl.evalf(coefficient, 15), ...exprs]) : keepCoeff(impl.evalf(coefficient, 15), mul(...exprs));
}

/** Factor over QQ_I, then extract the Gaussian content of each integral factor. */
function factorGaussianInteger(p: Poly): Expr {
  const K = defined(polyConstructionHooks.domain, 'polynomial domain construction')([], { domain: 'ZZ_I' });
  const [content, factors] = p.setDomain('QQ_I').factorList();
  let coefficient = content;
  const exprs: Expr[] = [];
  for (const [f, k] of factors) {
    const [c, primitive] = primitiveGaussian(f, K);
    coefficient = mul(coefficient, pow(c, k));
    exprs.push(pow(primitive.asExpr(), k));
  }
  return mul(expand(coefficient), ...exprs);
}

function hasUnexpandedFactors(e: Expr, g: Expr): boolean {
  for (const term of e instanceof Add ? e.args : [e]) {
    for (const f of term instanceof Mul ? term.args : [term]) {
      if (!f.has(g) || f.key === g.key || f instanceof Pow && f.base.key === g.key && f.exp instanceof Rational && f.exp.isPositive && f.exp.isInteger) continue;
      return true;
    }
  }
  return false;
}

/**
 * Factor over an algebraic coefficient field, treating transcendental atoms
 * as formal polynomial generators.
 */
function extensionGenerators(expressions:readonly Expr[],coefficientGenerator?:Expr):Expr[] {
  return sortGens([...new Map(expressions.flatMap((e)=>detectGens(expand(e))).filter((g)=>g.key!==coefficientGenerator?.key&&(freeSymbols(g).size>0||!(g instanceof ExtensionExpr&&g.name==='CRootOf')&&fact(g,'algebraic')!==true)).map((g)=>[g.key,g])).values()]);
}
function factorOverExtension(e: Expr, ext: true | readonly Expr[], domain?:Domain): Expr {
  if (ext !== true && e instanceof Mul) return mul(...e.args.map((f) => factorOverExtension(f, ext, domain)));
  if (ext !== true && e instanceof Pow && e.exp instanceof Rational && e.exp.isInteger) {
    const base = factorOverExtension(e.base, ext, domain);
    return base instanceof Mul ? mul(...base.args.map((f) => pow(f, e.exp))) : pow(base, e.exp);
  }
  const [numer,denom] = fraction(together(e));
  if (!denom.equals(1)) {
    if(ext===true&&domain===undefined){
      const gens=extensionGenerators([numer,denom]);
      const [n,d]=Poly.from(numer,gens,{extension:true}).unify(Poly.from(denom,gens,{extension:true}));
      const factored=(p:Poly):Expr=>{const [c,fs]=p.factorList();return mul(c,...fs.map(([f,k])=>pow(f.asExpr(),k)));};
      return mul(factored(n),pow(factored(d),-1));
    }
    const n = factorOverExtension(numer,ext,domain), d = factorOverExtension(denom,ext,domain);
    return mul(n,pow(d,-1));
  }
  const generator=domain===undefined?undefined:defined(polyConstructionHooks.algebraic,'algebraic field data')(domain).generator;
  const vars=extensionGenerators([numer],generator);
  if(!vars.length)return numer;
  const p=Poly.from(numer,vars,domain?{domain}:{extension:ext===true||ext.some((v)=>v.key===S.true.key)?true:ext});
  const [c,fs] = p.factorList();
  return mul(c,...fs.map(([f,k]) => pow(f.asExpr(),k)));
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
  const nc = [...freeSymbols(e)].filter((s) => s instanceof Sym).filter((s) => !s.isCommutative);
  // A noncommutative operator can evaluate differently when its operands are
  // made commutative. Replace the application as a whole while factoring.
  const operators = new Map<string, Expr>();
  const visit = (term: Expr): void => {
    if (term instanceof ExtensionExpr && !term.isCommutative && nc.some((symbol) => term.has(symbol))) {
      operators.set(term.key, term);
      return;
    }
    term.args.forEach(visit);
  };
  visit(e);
  // A noncommutative node without noncommutative symbols (e.g. a quaternion) factors its arguments.
  if (!nc.length) return rebuild(e, e.args.map(factorNc));
  const reps: [Expr, Expr][] = [...nc.map((s): [Expr, Expr] => [s, new Sym(`_nc_${s.name}`)]),
    ...[...operators.values()].map((op): [Expr, Expr] => [op, new Dummy('operator')])];
  const f = factor(xreplace(e, reps));
  const back = xreplace(f, reps.map(([a, b]) => [b, a] as [Expr, Expr]));
  const valid = expand(back).key === expand(e).key ? back : e;
  if (!(valid instanceof Add)) return valid;
  const factors = valid.args.map((term) => term instanceof Mul ? term.args : [term]);
  const right = first(factors).at(-1);
  if (right !== undefined && !right.isCommutative && factors.every((term) => term.at(-1)?.equals(right))) {
    const remaining = add(...factors.map((term) => mul(...term.slice(0, -1))));
    return mul(factorNc(remaining), right);
  }
  const [content, primitive] = asContentPrimitive(valid);
  return keepCoeff(content, primitive);
}

/**
 * SymPy sqf_norm(f, extension): [s, g, r] with g(x) = f(x - s*a) for the
 * primitive element a (the sum of the extension generators) and r = norm(g)
 * square-free over QQ.
 */
export function sqfNorm(fIn: ExprLike, x: Sym, extension: readonly Expr[]): [number[], Expr, Expr] {
  const p=Poly.from(fIn,[x],{extension});
  const [s,g,r]=p.sqfNorm();
  return [s,g.asExpr(),r.asExpr()];
}

impl.factor = (e) => factor(e);
polyHooks.factorList = (e) => factorListInt(e);
polyHooks.numericRoots = (e, x) => defined(rootHooks.nroots, 'numeric roots')(Poly.from(e, [x]), 15);
polyHooks.algebraicFactors = (e, x) => {
  try {
    const f = Poly.from(e, [x], { extension: true });
    return f.domain.startsWith('QQ<') || f.domain === 'QQ_I' ? f.factorList()[1].map(([g, k]): [Expr, number] => [g.asExpr(), k]) : [];
  } catch (error) {
    if (error instanceof DomainError || error instanceof CoercionFailed || error instanceof NotImplementedError) return [];
    throw error;
  }
};
polyHooks.cancelDomain = (e, opts) => {
  if (opts.extension !== undefined) {
    // the numerator and denominator over the algebraic field, divided by their gcd
    const gens = varsFor(e);
    const [numer, denom] = fraction(together(e));
    const n = Poly.from(numer, gens, { extension: opts.extension }), d = Poly.from(denom, gens, { extension: opts.extension });
    const g = n.gcd(d);
    return mul(n.exquo(g).asExpr(), pow(d.exquo(g).asExpr(), -1));
  }
  const p = modulusOption(opts);
  if (p === undefined) {
    if (!['ZZ','QQ'].includes(String(opts.domain))) throw new NotImplementedError(`cancel over ${String(opts.domain)}`);
    return cancel(e);
  }
  const gens = varsFor(e);
  if (!gens.length) return e;
  const [numer, denom] = fraction(together(e));
  const n = Poly.from(numer, gens, opts), d = Poly.from(denom, gens, opts);
  if (d.isZero) return n.isZero ? S.NaN : S.ComplexInfinity;
  const g = n.gcd(d);
  const denominator = d.exquo(g), result = mul(n.exquo(g).asExpr(), pow(denominator.asExpr(), -1));
  return denominator.totalDegree() === 0 ? expand(result) : result;
};

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
export function asPoly(ex: ExprLike, ...generators: (Expr | { extension: true })[]): Poly | NoMatchResult {
  const e = sympify(ex);
  const gens = generators.filter((arg): arg is Expr => arg instanceof Expr);
  const options = gens.length === generators.length ? {} : { extension: true as const };
  // SymPy's Poly raises PolynomialError for these (a non-commutative expression, or not a polynomial in gens)
  if (!e.isCommutative || (gens.length > 0 && !isPolynomial(e, gens))) return NoMatch;
  if ('extension' in options && !gens.length && !e.freeSymbols().size) return NoMatch;
  const result = Poly.from(e, gens.length ? gens : undefined, options);
  return result.gens.length ? result : NoMatch;
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
  const [first, ...rest] = seq;
  return first === undefined ? S.Zero : rest.reduce<Expr>((acc, f) => polyGcd(acc, f), toExpr(first));
}

/** SymPy lcm_list(seq, *gens): the least common multiple of the items of seq (1 for none). */
export function lcmList(seq: readonly (Poly | ExprLike)[]): Expr {
  const [first, ...rest] = seq;
  return first === undefined ? S.One : rest.reduce<Expr>((acc, f) => polyLcm(acc, f), toExpr(first));
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
  const r = keepCoeff(content, mul(sqfProduct(numer), pow(sqfProduct(denom), -1)));
  // a polynomial gives a polynomial, as in SymPy
  return ex instanceof Poly ? Poly.from(r, ex.gens) : r;
}

/** The product of the square-free factors: the irreducible factors of each multiplicity multiplied out. */
function sqfProduct(factors: readonly [Expr, Expr][]): Expr {
  return mul(...squareFreeGroups(factors).map(([f, k]) => pow(f, k)));
}

/** List of square-free factors and their multiplicities (SymPy sqf_list). */
export function sqfList(ex: ExprLike, ...gens: Expr[]): FactorList {
  const [content, factors] = factorListExpr(sympify(ex), gens);
  return [content, squareFreeGroups(factors).sort(([, a], [, b]) => asRational(add(a, mul(-1, b)), 'multiplicity difference').toNumber())];
}

/** Try a rescaling or translation to make square-root coefficients rational. */
export function toRationalCoeffs(f: Poly): readonly [Expr | NoMatchResult, Expr | NoMatchResult, Expr | NoMatchResult, Poly] | NoMatchResult {
  if (f.domain !== 'EX' || !f.isUnivariate || !f.gen.isAtom || f.degree() < 1) return NoMatch;
  const rationalRadicals = f.coeffs().flatMap((c) => (c instanceof Add ? c.args : [c]))
    .flatMap((t) => t instanceof Mul ? t.args : [t])
    .filter((a): a is Pow => a instanceof Pow && a.base.isNumber && a.exp instanceof Rational)
    .map((a) => asRational(a.exp, 'rational exponent').q);
  if (!rationalRadicals.includes(2n) || rationalRadicals.some((q) => q > 2n)) return NoMatch;

  const simplify = (e: Expr): Expr => sqrtdenest(cancel(expandFull(e)));
  const monic = f.monic(), cs = monic.allCoeffs().slice(1).map(simplify);
  const n = f.degree(), constant = at(cs, -1), linear = cs.at(-2);
  if (linear !== undefined && !linear.equals(S.Zero) && !constant.equals(S.Zero)) {
    const reciprocalScale = simplify(mul(linear, pow(constant, -1)));
    const scaled = cs.map((c, i) => simplify(mul(c, pow(reciprocalScale, i + 1))));
    if (scaled.every((c) => c instanceof Rational)) {
      return [f.LC(), simplify(pow(reciprocalScale, -1)), NoMatch, Poly.fromList([S.One, ...scaled], f.gens)];
    }
  }

  const next = first(cs);
  if (next instanceof Add) {
    const translation = mul(Rational.of(-1, n), add(...next.args.filter((c) => !(c instanceof Rational))));
    const shifted = monic.shift(translation);
    return [NoMatch, NoMatch, translation, Poly.fromList(shifted.allCoeffs().map(simplify), f.gens)];
  }
  return NoMatch;
}

function squareFreeGroups(factors: readonly [Expr, Expr][]): [Expr, Expr][] {
  const groups = new Map<string, [Expr, Expr[]]>();
  for (const [f, k] of factors) {
    const g = groups.get(k.key);
    if (g) g[1].push(f);
    else groups.set(k.key, [k, [f]]);
  }
  return [...groups.values()].map(([k, fs]) => [fs.length === 1 ? first(fs) : expand(mul(...fs)), k]);
}
