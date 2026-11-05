// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Canonicalizing constructors for Add, Mul and Pow.
 *
 * Automatic simplifications performed (in the spirit of SymPy):
 * - flattening, constant folding, collection of like terms / like bases
 * - exact rational arithmetic and radicals (sqrt(8) -> 2*sqrt(2), 1/sqrt(2) -> sqrt(2)/2)
 * - powers of the imaginary unit (I^2 -> -1)
 * - exp(a)*exp(b) -> exp(a+b), exp(I*pi) -> -1, exp(log(x)) -> x
 * - distribution of a numeric coefficient over a sum (2*(x+1) -> 2*x+2)
 */

import { isIntegerQ, isNegative, isNonNegative, isPolar, isPositive, isReal } from './assumptions';
import type { ComplexValue, ExprLike, Num } from './nodes';
import {
  Add,
  Constant,
  Expr,
  ExtensionExpr,
  Float,
  Fn,
  isAddLike,
  isMulLike,
  Mul,
  registerFromiter,
  Pow,
  Rational,
  Rel,
  S,
  Order,
  Special,
  Sym,
  compareExpr,
  impl,
  isNum,
} from './nodes';
import { mkFloat, numAdd, numInv, numMul, numNeg, numPowInt, ratFloor, toMpf } from './num';
import { ZERO as MPF_ZERO, precToDps } from '../numeric/mpf';
import { cpow as mpCpow, powReal as mpPowReal } from '../numeric/mpfun';
import { factorInt, gcd, iroot, ipow } from './numbers';
import { NotLoadedError, SympifyError, errorSettings } from './errors';
import { at, cast, pair } from './guard';

export function sympify(x: ExprLike): Expr {
  if (x instanceof Expr) return x;
  if (typeof x === 'bigint') return Rational.of(x);
  if (typeof x === 'number') {
    if (Number.isInteger(x)) return Rational.of(BigInt(x));
    return new Float(x);
  }
  throw new SympifyError(`Cannot convert ${String(x)} to an expression`, x);
}

/** Float ** number (SymPy Float._eval_power / Rational._eval_power with a Float exponent). */
function floatPow(b: Num, e: Num): Expr {
  // SymPy: 0**0.5 = 0 (the exact zero is kept), Float(0)**0.5 = 0.0
  if (b.isZero) return e.isPositive ? b : S.ComplexInfinity;
  const fb = b instanceof Float ? b : new Float(toMpf(b, cast(e, Float).prec), cast(e, Float).prec);
  if (e instanceof Rational && e.p === 1n && e.q % 2n === 1n && fb.isNegative) {
    return mul(new Pow(S.NegOne, e), pow(numNeg(fb), e));
  }
  const prec = e instanceof Float ? Math.max(fb.prec, e.prec) : fb.prec;
  const y = toMpf(e, prec);
  if (fb.isPositive) return mkFloat(mpPowReal(fb.mpf, y, prec), prec);
  const [re, im] = mpCpow([fb.mpf, MPF_ZERO], [y, MPF_ZERO], prec);
  return add(mkFloat(re, prec), mul(mkFloat(im, prec), S.I));
}

const isI = (e: Expr): boolean => e instanceof Constant && e.name === 'I';
const isE = (e: Expr): boolean => e instanceof Constant && e.name === 'E';

/** Split e into numeric coefficient and the remaining factor: e = c * rest. */
export function splitCoeff(e: Expr): [Num, Expr] {
  if (isNum(e)) return [e, S.One];
  if (e instanceof Mul) {
    const c = e.args[0];
    if (c !== undefined && isNum(c)) return [c, e.args.length === 2 ? at(e.args, 1) : new Mul(e.args.slice(1))];
  }
  return [S.One, e];
}

/** Return [base, exponent] of e (exponent 1 for non-powers). */
export function asBaseExp(e: Expr): [Expr, Expr] {
  if (e instanceof Pow) return [e.base, e.exp];
  return [e, S.One];
}

/** Build c * rest where rest has no numeric coefficient (no re-canonicalization). */
function mulCoeffRaw(c: Num, rest: Expr): Expr {
  if (c instanceof Rational && c.isOne) return rest;
  if (rest instanceof Rational && rest.isOne) return c;
  if (rest instanceof Mul) return new Mul([c, ...rest.args]);
  return new Mul([c, rest]);
}

// ---------------------------------------------------------------------------
// Add
// ---------------------------------------------------------------------------

/** Finite constant without free symbols (absorbed by an infinity). */
function isFiniteConstant(e: Expr, real: boolean): boolean {
  if (isNum(e)) return true;
  if (impl.freeSymbols(e).size > 0) return false;
  try {
    const v = impl.toComplex(e);
    return Number.isFinite(v.re) && Number.isFinite(v.im) && (!real || Math.abs(v.im) < 1e-300);
  } catch {
    return false;
  }
}

/** A sum with an infinity or nan among the terms (the caller has seen one). */
function addSpecial(args: Expr[]): Expr {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Add ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const specials = flat.filter((e): e is Special => e instanceof Special);
  const names = new Set(specials.map((e) => e.name));
  if (names.has('nan')) return S.NaN;
  let inf: Special;
  if (names.has('zoo')) {
    // zoo + zoo is nan in SymPy (the sum of two complex infinities is undetermined)
    if (names.has('oo') || names.has('-oo') || specials.filter((e) => e.name === 'zoo').length > 1) return S.NaN;
    inf = S.ComplexInfinity;
  } else if (names.has('oo') && names.has('-oo')) return S.NaN;
  else inf = names.has('oo') ? S.Infinity : S.NegativeInfinity;
  const others = flat.filter((e) => !(e instanceof Special) && !isFiniteConstant(e, inf !== S.ComplexInfinity));
  const rest = add(...others);
  // the symbolic terms may cancel ((x + oo) - x = oo)
  if (rest instanceof Rational && rest.isZero) return inf;
  return new Add([...(rest instanceof Add ? rest.args : [rest]), inf].sort(compareExpr));
}

/** Lowest power of t in a term (for Order absorption); undefined if not a simple power product. */
function lowestPower(term: Expr, t: Expr): number | undefined {
  if (!term.has(t)) return 0;
  if (term.key === t.key) return 1;
  if (term instanceof Pow && term.base.key === t.key && term.exp instanceof Rational) return term.exp.value;
  if (term instanceof Mul) {
    let k = 0;
    for (const f of term.args) {
      const p = lowestPower(f, t);
      if (p === undefined) return undefined;
      k += p;
    }
    return k;
  }
  if (term instanceof Add) {
    const ps: number[] = [];
    for (const a of term.args) {
      const p = lowestPower(a, t);
      if (p === undefined) return undefined;
      ps.push(p);
    }
    return Math.min(...ps);
  }
  return undefined;
}

/**
 * Sum containing Order terms (the caller has seen one): keep the weakest Order
 * and drop the terms it absorbs; undefined when the Orders have different bases.
 */
function addOrder(args: Expr[]): Expr | undefined {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Add ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const orders = flat.filter((e): e is Order => e instanceof Order);
  // O((x - x0)**n) : base t = x - x0 (or x), exponent n
  const info = orders.map((o) => {
    const [b, k] = o.expr instanceof Pow ? o.expr.args : [o.expr, S.One];
    return { o, base: b, k: k instanceof Rational ? k.value : NaN };
  });
  const sameBase = info.every((i) => i.base.key === at(info, 0).base.key);
  if (!sameBase) return undefined;
  const weakest = info.reduce((a, b) => (b.k < a.k ? b : a));
  const base = weakest.base;
  // terms are measured in powers of the base, or of x when the base is x - x0
  const rest = flat.filter((e) => !(e instanceof Order));
  const kept = rest.filter((term) => {
    const p = base instanceof Add ? lowestPowerShifted(term, base) : lowestPower(term, base);
    return p === undefined || p < weakest.k;
  });
  const body = add(...kept);
  const parts = body instanceof Rational && body.isZero ? [] : body instanceof Add ? [...body.args] : [body];
  if (parts.length === 0) return weakest.o;
  return new Add([...parts, weakest.o].sort(compareExpr));
}

/**
 * lowestPower for a shifted base (x - x0): only exact powers of the base are
 * recognized. The terms of a flattened sum are never the sum x - x0 itself.
 */
function lowestPowerShifted(term: Expr, base: Expr): number | undefined {
  if (term instanceof Pow && term.base.key === base.key && term.exp instanceof Rational) return term.exp.value;
  if (term instanceof Mul) {
    let k = 0;
    for (const f of term.args) {
      if (f.key === base.key) k += 1;
      else if (f instanceof Pow && f.base.key === base.key && f.exp instanceof Rational) k += f.exp.value;
      else if (impl.freeSymbols(f).size > 0) return undefined;
    }
    return k;
  }
  return impl.freeSymbols(term).size === 0 ? 0 : undefined;
}

/** SymPy raises TypeError for a relational operand of Add, Mul or Pow. */
function rejectRel(args: readonly Expr[], op: string): void {
  if (args.some((e) => e instanceof Rel)) throw new TypeError(`Relational cannot be used in ${op}`);
}

/** oo*t or -oo*t: [the infinity, t]; undefined for other terms. */
function infTerm(e: Expr): [Special, Expr] | undefined {
  if (!(e instanceof Mul)) return undefined;
  const k = e.args.indexOf(S.Infinity);
  if (k < 0) return undefined;
  const rest = e.args.filter((_, i) => i !== k);
  const negative = at(rest, 0) === S.NegOne;
  const t = negative ? rest.slice(1) : rest;
  return [negative ? S.NegativeInfinity : S.Infinity, t.length === 1 ? at(t, 0) : new Mul(t)];
}

export function add(...xs: ExprLike[]): Expr {
  const sx = xs.map(sympify);
  rejectRel(sx, 'Add');
  const own = impl.arithmetic?.('add', sx);
  if (own !== undefined) return own;
  const ab = impl.accumBounds;
  if (ab && sx.some((e) => ab.is(e) || (e instanceof Add && e.args.some((a) => ab.is(a))))) {
    // interval arithmetic: the intervals absorb a numeric remainder, symbolic terms stay beside them
    const flat = sx.flatMap((e) => (e instanceof Add ? e.args : [e]));
    const abs = flat.filter((e) => ab.is(e));
    const rest = add(...flat.filter((e) => !ab.is(e)));
    if (rest.freeSymbols().size === 0) return ab.add(abs, rest);
    // like SymPy, the interval absorbs the numeric term: x + 1 + AccumBounds(1, 2) = x + AccumBounds(2, 3)
    const [c, terms] = rest instanceof Add && isNum(at(rest.args, 0)) ? [at(rest.args, 0), rest.args.slice(1)] : [S.Zero, [rest]];
    return new Add([...terms, ab.add(abs, c)]);
  }
  if (sx.some((e) => e instanceof Order || (e instanceof Add && e.args.some((a) => a instanceof Order)))) {
    const r = addOrder(sx);
    if (r) return r;
  }
  if (sx.some((e) => e instanceof Special || (e instanceof Add && e.args.some((a) => a instanceof Special)))) return addSpecial(sx);
  let c: Num = S.Zero;
  const terms = new Map<string, { term: Expr; coeff: Num }>();
  // SymPy collects oo*x like any other coefficient: x + oo*x = oo*x, oo*x - oo*x = nan
  const infs = new Map<string, { inf: Special; orig: Expr }>();
  const visit = (e: Expr): void => {
    if (isNum(e)) {
      c = numAdd(c, e);
      return;
    }
    if (e instanceof Add) {
      for (const a of e.args) visit(a);
      return;
    }
    const it = infTerm(e);
    if (it) {
      const [inf, t] = it;
      const prev = infs.get(t.key);
      infs.set(t.key, { inf: prev && prev.inf !== inf ? S.NaN : inf, orig: e });
      return;
    }
    const [k, t] = splitCoeff(e);
    const entry = terms.get(t.key);
    if (entry) entry.coeff = numAdd(entry.coeff, k);
    else terms.set(t.key, { term: t, coeff: k });
  };
  for (const x of sx) visit(x);
  if ([...infs.values()].some((v) => v.inf === S.NaN)) return S.NaN;

  const out: Expr[] = [];
  for (const { term, coeff } of terms.values()) {
    if (coeff.isZero || infs.has(term.key)) continue;
    out.push(mulCoeffRaw(coeff, term));
  }
  for (const { orig } of infs.values()) out.push(orig);
  if (out.length === 0) return c;
  out.sort(compareExpr);
  if (!c.isZero) out.unshift(c);
  if (out.length === 1) return at(out, 0);
  return new Add(out);
}

// ---------------------------------------------------------------------------
// Mul
// ---------------------------------------------------------------------------

/** Accumulates rational bases raised to rational powers, factored into primes. */
/** A positive integer raised to a rational power, before simplification. */
type RatPow = readonly [bigint, Rational];

/**
 * The largest k with n = r**k (SymPy perfect_power), or undefined.
 */
function perfectPower(n: bigint): [bigint, bigint] | undefined {
  for (let k = BigInt(n.toString(2).length); k >= 2n; k--) {
    const r = iroot(n, k);
    if (r > 1n && ipow(r, k) === n) return [r, k];
  }
  return undefined;
}

/**
 * SymPy Integer._eval_power for a positive integer n and a rational e that is
 * not an integer: an exact coefficient times powers with exponents in (0, 1)
 * ((2**12)**(1/10) -> 2*2**(1/5), 12**(2/3) -> 2*18**(1/3)).
 */
function intPow(n: bigint, e: Rational): [Rational, RatPow[]] {
  if (e.isNegative) {
    // SymPy Rational._eval_power of 1/n: n**(p*(q - 1)/q) / n**p
    const ne = numNeg(e);
    const [c, rads] = intPow(n, Rational.of(ne.p * (ne.q - 1n), ne.q));
    return [numMul(c, Rational.of(1n, ipow(n, ne.p))), rads];
  }
  const root = iroot(n, e.q);
  if (ipow(root, e.q) === n) return [Rational.of(ipow(root, e.p)), []];
  const pp = perfectPower(n);
  const factors = pp ? new Map([pp]) : factorInt(n);
  let outInt = 1n;
  const out: RatPow[] = [];
  const sqr: [bigint, bigint][] = [];
  for (const [prime, k] of factors) {
    const ex = k * e.p;
    const divE = ex / e.q;
    const divM = ex % e.q;
    if (divE > 0n) outInt *= ipow(prime, divE);
    if (divM > 0n) {
      // (2**2)**(1/10) -> 2**(1/5)
      const g = gcd(divM, e.q);
      if (g !== 1n) out.push([prime, Rational.of(divM / g, e.q / g)]);
      else sqr.push([prime, divM]);
    }
  }
  const sqrGcd = sqr.reduce((g, [, m]) => (g === 0n ? m : gcd(g, m)), 0n);
  const sqrInt = sqr.reduce((acc, [b, m]) => acc * ipow(b, m / sqrGcd), 1n);
  if (sqrInt !== 1n) {
    if (sqrInt === n && outInt === 1n && out.length === 0) return [S.One, [[n, e]]];
    // the remaining power is evaluated again (Pow(sqr_int, sqr_gcd/q))
    const [c, rads] = intPow(sqrInt, Rational.of(sqrGcd, e.q));
    return [numMul(Rational.of(outInt), c), [...out, ...rads]];
  }
  return [Rational.of(outInt), out];
}

/**
 * Numeric radicals of a product, combined as SymPy Mul.flatten does: powers of
 * the same base add their exponents, bases with the same exponent multiply
 * (sqrt(2)*sqrt(6) -> 2*sqrt(3)), and common factors of bases with different
 * exponents are pulled out (2**(1/3)*6**(1/4) -> 2**(7/12)*3**(1/4)).
 */
class Radicals {
  /** positive integer base -> exponents */
  private readonly bases = new Map<bigint, Rational[]>();
  private coeff: Rational = S.One;
  /** exponent of -1 */
  negOne: Rational = S.Zero;

  addPower(baseIn: Rational, exp: Rational): void {
    let base = baseIn;
    if (base.isNegative) {
      this.negOne = numAdd(this.negOne, exp);
      base = Rational.of(-base.p, base.q);
    }
    this.addInt(base.p, exp);
    this.addInt(base.q, numNeg(exp));
  }

  private addInt(n: bigint, exp: Rational): void {
    if (n === 1n) return;
    if (exp.isInteger) {
      this.coeff = numMul(this.coeff, numPowInt(Rational.of(n), exp.p));
      return;
    }
    const [c, rads] = intPow(n, exp);
    this.coeff = numMul(this.coeff, c);
    for (const [b, e] of rads) {
      const es = this.bases.get(b);
      if (es) es.push(e);
      else this.bases.set(b, [e]);
    }
  }

  get isEmpty(): boolean {
    return this.bases.size === 0 && this.negOne.isZero && this.coeff.isOne;
  }

  /** Resolve into a rational coefficient, a power of I, and leftover radical factors. */
  resolve(): { coeff: Rational; iPow: bigint; factors: Expr[] } {
    let coeff = this.coeff;
    const mulCoeff = (r: Rational): void => {
      coeff = numMul(coeff, r);
    };
    /** b**e with e reduced to (0, 1); undefined when nothing is left */
    const reduce = (b: bigint, eIn: Rational): RatPow | undefined => {
      const k = ratFloor(eIn);
      if (k !== 0n) mulCoeff(numPowInt(Rational.of(b), k));
      const e = numAdd(eIn, Rational.of(-k));
      return e.isZero ? undefined : [b, e];
    };
    // same base: add the exponents; then same exponent: multiply the bases
    const combE = new Map<string, { e: Rational; b: bigint }>();
    for (const [b, es] of this.bases) {
      // the exponents are in (0, 1) after intPow, so their sum is positive
      const e = es.reduce((acc, x) => numAdd(acc, x), S.Zero);
      const g = combE.get(e.key);
      if (g) g.b *= b;
      else combE.set(e.key, { e, b });
    }
    const numRat: RatPow[] = [];
    for (const { e, b } of combE.values()) {
      const r = reduce(b, e);
      if (r) numRat.push(r);
    }
    // pull out common factors of the bases: 4**r1*6**r2 -> 2**(r1+r2)*2**r1*3**r2
    const pnew = new Map<string, { e: Rational; b: bigint }>();
    const addNew = (b: bigint, e: Rational): void => {
      const g = pnew.get(e.key);
      if (g) g.b *= b;
      else pnew.set(e.key, { e, b });
    };
    for (let i = 0; i < numRat.length; i++) {
      let [bi] = at(numRat, i);
      const ei = at(numRat, i)[1];
      if (bi === 1n) continue;
      const grow: RatPow[] = [];
      for (let j = i + 1; j < numRat.length && bi !== 1n; j++) {
        const [bj, ej] = at(numRat, j);
        const g = gcd(bi, bj);
        if (g === 1n) continue;
        const r = reduce(g, numAdd(ei, ej));
        if (r) grow.push(r);
        numRat[j] = [bj / g, ej];
        bi /= g;
      }
      if (bi !== 1n) {
        // sqrt(12) -> 2*sqrt(3)
        const [c, rads] = intPow(bi, ei);
        mulCoeff(c);
        for (const [b, e] of rads) addNew(b, e);
      }
      numRat.push(...grow);
    }
    const rats: RatPow[] = [];
    for (const { e, b } of pnew.values()) {
      // the merged base is evaluated again (Pow(b, e))
      const [c, rads] = intPow(b, e);
      mulCoeff(c);
      rats.push(...rads);
    }
    const factors: Expr[] = [];

    // (-1)^n with n reduced to [0, 2)
    let iPow = 0n;
    let n = this.negOne;
    if (!n.isZero) {
      const k = ratFloor(Rational.of(n.p, n.q * 2n));
      n = numAdd(n, Rational.of(-2n * k)); // n in [0, 2)
      const twice = numMul(n, S.Two);
      if (twice.isInteger) {
        iPow += twice.p; // (-1)^(m/2) = I^m
      } else {
        // SymPy: (-1)**(p/q) = (-1)**i * (-1)**(r/q) with r/q in [0, 1)
        let r = n;
        if (n.p > n.q) {
          r = numAdd(n, Rational.of(-1n));
          iPow += 2n;
        }
        // SymPy joins the power of -1 to a positive base with the same exponent: (-1)**(1/3)*2**(1/3) -> (-2)**(1/3)
        const k = rats.findIndex(([, e]) => e.key === r.key);
        if (k >= 0) rats[k] = [-at(rats, k)[0], r];
        else factors.push(new Pow(S.NegOne, r));
      }
    }
    for (const [rb, re] of rats) factors.push(new Pow(Rational.of(rb), re));
    return { coeff, iPow, factors };
  }
}

/** A product with an infinity or nan among the factors (the caller has seen one). */
function mulSpecial(args: Expr[]): Expr {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Mul ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const specials = flat.filter((e): e is Special => e instanceof Special);
  if (specials.some((e) => e.name === 'nan')) return S.NaN;
  const c = mul(...flat.filter((e) => !(e instanceof Special)));
  if (c instanceof Rational && c.isZero) {
    // 0/0 (SymPy seterr(divide=True) raises)
    if (errorSettings.divide && specials.some((e) => e.name === 'zoo')) throw new RangeError('Indeterminate 0/0');
    return S.NaN;
  }
  if (specials.some((e) => e.name === 'zoo')) {
    return impl.freeSymbols(c).size === 0 ? S.ComplexInfinity : new Mul([c, S.ComplexInfinity]);
  }
  let sign = specials.filter((e) => e.name === '-oo').length % 2 === 0 ? 1 : -1;
  const [k, r] = splitCoeff(c);
  if (k.isNegative) sign = -sign;
  let rest = r;
  if (!(rest instanceof Rational && rest.isOne)) {
    if (isPositive(rest)) rest = S.One;
    else if (isNegative(rest)) {
      sign = -sign;
      rest = S.One;
    }
  }
  if (rest instanceof Rational && rest.isOne) return sign > 0 ? S.Infinity : S.NegativeInfinity;
  const factors = [...(rest instanceof Mul ? rest.args : [rest]), S.Infinity].sort(compareExpr);
  return new Mul(sign > 0 ? factors : [S.NegOne, ...factors]);
}

export function mul(...xs: ExprLike[]): Expr {
  const args = xs.map(sympify);
  rejectRel(args, 'Mul');
  const own = impl.arithmetic?.('mul', args);
  if (own !== undefined) return own;
  const ab = impl.accumBounds;
  if (ab && args.some((e) => ab.is(e))) {
    const abs = args.filter((e) => ab.is(e));
    const rest = mul(...args.filter((e) => !ab.is(e)));
    if (rest.freeSymbols().size === 0) return ab.mul(abs, rest);
    return new Mul([rest, ab.mul(abs, S.One)]);
  }
  if (args.some((e) => e instanceof Special || (e instanceof Mul && e.args.some((a) => a instanceof Special)))) return mulSpecial(args);

  // SymPy's two-argument rule: Rational * Add distributes (2*(x + 1) -> 2*x + 2).
  if (args.length === 2) {
    let [a, b] = pair(args);
    if (b instanceof Rational) [a, b] = [b, a];
    if (a instanceof Rational && !a.isZero && !a.isOne) {
      const [r, rest] = splitCoeff(b);
      if (rest instanceof Add) {
        if (r instanceof Rational && r.isOne) return add(...rest.args.map((t) => mul(a, t)));
        return new Mul([numMul(a, r), rest]);
      }
    }
  }

  let coeff: Num = S.One;
  let iPow = 0n;
  // base -> (exponent term -> coefficients); SymPy `_gather`
  const general = new Map<string, { base: Expr; terms: Map<string, { term: Expr; coeffs: Num[]; orig: Expr }> }>();
  // numeric bases raised to non-rational exponents (SymPy num_exp), gathered below
  const numExp: { base: Num; exp: Expr; orig: Expr }[] = [];
  const radicals = new Radicals();

  // non-commutative factors keep their order; equal neighbouring bases combine
  const ncPart: Expr[] = [];
  const pushNc = (e: Expr): void => {
    const last = ncPart[ncPart.length - 1];
    if (last) {
      const [b1, e1] = asBaseExp(last);
      const [b2, e2] = asBaseExp(e);
      // SymPy: combine only when the new exponent is not an Add (A**x*A**y and exp(A)*exp(B) stay apart)
      const ne = b1.key === b2.key ? add(e1, e2) : undefined;
      if (ne && !(ne instanceof Add)) {
        ncPart.pop();
        const r = pow(b1, ne);
        if (!(r instanceof Rational && r.isOne)) pushNc(r);
        return;
      }
    }
    ncPart.push(e);
  };
  const visit = (e: Expr): void => {
    if (isNum(e)) {
      coeff = numMul(coeff, e);
      return;
    }
    if (e instanceof Mul) {
      for (const a of e.args) visit(a);
      return;
    }
    if (!e.isCommutative) {
      pushNc(e);
      return;
    }
    if (isI(e)) {
      // SymPy treats I as (-1)**(1/2): I*(-1)**(1/3) -> (-1)**(5/6)
      radicals.negOne = numAdd(radicals.negOne, S.Half);
      return;
    }
    const [b, x] = asBaseExp(e);
    if (b instanceof Rational && x instanceof Rational) {
      radicals.addPower(b, x);
      return;
    }
    if (isNum(b) && (b.isPositive || isIntegerQ(x))) {
      numExp.push({ base: b, exp: x, orig: e });
      return;
    }
    const [c, t] = splitCoeff(x);
    let g = general.get(b.key);
    if (!g) {
      g = { base: b, terms: new Map() };
      general.set(b.key, g);
    }
    const tg = g.terms.get(t.key);
    if (tg) tg.coeffs.push(c);
    else g.terms.set(t.key, { term: t, coeffs: [c], orig: e });
  };
  for (const x of args) visit(x);

  if (coeff instanceof Rational && coeff.isZero) return S.Zero;

  const factors: Expr[] = [];
  const absorb = (r: Expr): void => {
    if (isNum(r)) coeff = numMul(coeff, r);
    else if (isI(r)) iPow += 1n;
    else factors.push(r);
  };

  // SymPy _gather rebuilds each exponent as the product c*t of its as_coeff_Mul parts, which
  // distributes a number over a sum left unevaluated by factor_terms (_keep_coeff):
  // z*exp(-2*(3*x + 4*y)/25) -> z*exp(-6*x/25 - 8*y/25). A Mul of one factor is that factor.
  const several = args.filter((a) => !(a instanceof Rational && a.isOne)).length > 1;
  for (const { base, terms } of general.values()) {
    for (const { term, coeffs, orig } of terms.values()) {
      if (coeffs.length === 1) {
        const c = at(coeffs, 0);
        // otherwise a single occurrence is already canonical
        if (several && term instanceof Add && c instanceof Rational && !c.isOne) absorb(pow(base, mul(c, term)));
        else factors.push(orig);
        continue;
      }
      const c = coeffs.reduce((acc, k) => numAdd(acc, k));
      if (c instanceof Rational && c.isZero) continue;
      const r = pow(base, mul(c, term));
      if (r instanceof Mul) r.args.forEach(absorb);
      else absorb(r);
    }
  }

  // SymPy _gather(num_exp): powers of the same base add the coefficients of like exponent terms
  // (2**s*2**(-s) -> 1, 2**(2*x)*2**x -> 2**(3*x)), then bases with the same exponent multiply
  // (2**x*3**x -> 6**x). A number raised to a symbolic exponent is a number, a power or an
  // infinity (never a product).
  const byBase = new Map<string, { base: Num; terms: Map<string, { term: Expr; coeffs: Num[]; orig: Expr }> }>();
  for (const { base, exp, orig } of numExp) {
    const [c, t] = splitCoeff(exp);
    let g = byBase.get(base.key);
    if (!g) {
      g = { base, terms: new Map() };
      byBase.set(base.key, g);
    }
    const tg = g.terms.get(t.key);
    if (tg) tg.coeffs.push(c);
    else g.terms.set(t.key, { term: t, coeffs: [c], orig });
  }
  const byExp = new Map<string, { exp: Expr; bases: Num[]; orig?: Expr }>();
  for (const { base, terms } of byBase.values()) {
    for (const { term, coeffs, orig } of terms.values()) {
      const c = coeffs.reduce((acc, k) => numAdd(acc, k));
      if (c.isZero) continue;
      const exp = coeffs.length === 1 ? asBaseExp(orig)[1] : mul(c, term);
      const g = byExp.get(exp.key);
      if (g) {
        g.bases.push(base);
        g.orig = undefined;
      } else byExp.set(exp.key, { exp, bases: [base], orig: coeffs.length === 1 ? orig : undefined });
    }
  }
  for (const { exp, bases, orig } of byExp.values()) {
    absorb(orig ?? pow(bases.reduce((acc, k) => numMul(acc, k)), exp));
  }

  if (!radicals.isEmpty) {
    const res = radicals.resolve();
    coeff = numMul(coeff, res.coeff);
    iPow += res.iPow;
    factors.push(...res.factors);
  }

  const m = ((iPow % 4n) + 4n) % 4n;
  if (m >= 2n) coeff = numNeg(coeff);
  if (m % 2n === 1n) factors.push(S.I);

  // exp_polar(c1*t)*exp_polar(c2*t) = exp_polar((c1 + c2)*t) for numbers c1, c2, as in SymPy's
  // Mul.flatten: ExpBase.as_base_exp is (exp_polar(1), arg) and exponents of a common base are
  // gathered by their as_coeff_Mul term, so exp_polar(x)*exp_polar(y) stays as it is.
  const epGroups = new Map<string, { term: Expr; coeffs: Expr[]; members: Expr[] }>();
  for (const f of factors) {
    if (!(f instanceof Fn) || f.name !== 'exp_polar') continue;
    const a = at(f.args, 0);
    const lead = a instanceof Mul ? at(a.args, 0) : a;
    const split = a instanceof Mul && (lead instanceof Rational || lead instanceof Float);
    const term = split ? mul(...a.args.slice(1)) : a instanceof Rational || a instanceof Float ? S.One : a;
    const c = split ? lead : a instanceof Rational || a instanceof Float ? a : S.One;
    const key = term.toString();
    const g = epGroups.get(key) ?? { term, coeffs: [], members: [] };
    g.coeffs.push(c);
    g.members.push(f);
    epGroups.set(key, g);
  }
  for (const g of epGroups.values()) {
    if (g.members.length < 2) continue;
    for (const f of g.members) factors.splice(factors.indexOf(f), 1);
    const total = add(...g.coeffs);
    // exp_polar(1)**0 is 1, so exp_polar(x)*exp_polar(-x) = 1
    if (!(total instanceof Rational && total.isZero)) factors.push(new Fn('exp_polar', [mul(total, g.term)]));
  }
  if (ncPart.length) {
    factors.sort(compareExpr);
    const isOne1 = coeff instanceof Rational && coeff.isOne;
    const all = [...(isOne1 ? [] : [coeff]), ...factors, ...ncPart];
    return all.length === 1 ? at(all, 0) : new Mul(all);
  }
  if (factors.length === 0) return coeff;
  factors.sort(compareExpr);
  const isOne = coeff instanceof Rational && coeff.isOne;
  if (factors.length === 1 && isOne) return at(factors, 0);
  // end of SymPy Mul.flatten: Number * Add distributes (2*(1 + a) -> 2 + 2*a)
  if (factors.length === 1 && factors[0] instanceof Add) {
    const c = coeff;
    return add(...factors[0].args.map((t) => keepCoeffMul(c, t)));
  }
  return new Mul(isOne ? factors : [coeff, ...factors]);
}

/** SymPy _keep_coeff(c, t) for a product term. */
function keepCoeffMul(c: Num, t: Expr): Expr {
  return mul(c, t);
}

// ---------------------------------------------------------------------------
// Pow
// ---------------------------------------------------------------------------

let IPI: Expr | undefined;
const iPi = (): Expr => (IPI ??= new Mul([S.I, S.Pi]));

export function pow(bx: ExprLike, ex: ExprLike): Expr {
  const b = sympify(bx);
  const e = sympify(ex);
  rejectRel([b, e], 'Pow');
  const own = impl.arithmetic?.('pow', [b, e]);
  if (own !== undefined) return own;
  if (impl.accumBounds?.is(b) && e.freeSymbols().size === 0) return impl.accumBounds.pow(b, e);
  if (impl.accumBounds?.is(e) && b.freeSymbols().size === 0 && b.toNumber() > 0) {
    // a positive base: b**x is monotone in x (exp(AccumBounds(0, 1)) = AccumBounds(1, E))
    const [lo, hi] = impl.accumBounds.bounds(e);
    const [p, q] = [pow(b, lo), pow(b, hi)];
    return b.toNumber() >= 1 ? impl.accumBounds.make(p, q) : impl.accumBounds.make(q, p);
  }

  if (e instanceof Rational) {
    if (e.isZero) return S.One;
    if (e.isOne) return b;
  }
  if (b instanceof Rational && b.isOne && !(e instanceof Special)) return S.One;
  if (isE(b) && e instanceof Float) return impl.evalf(new Pow(b, e), precToDps(e.prec));
  if (b instanceof Fn && b.name === 'exp_polar') return new Fn('exp_polar', [mul(at(b.args, 0), e)]);
  // SymPy KroneckerDelta._eval_power: a positive power is the delta, a negative one (other than -1) its reciprocal
  if (b instanceof Fn && b.name === 'KroneckerDelta') {
    if (isPositive(e)) return b;
    if (isNegative(e) && !(e instanceof Rational && e.p === -1n && e.q === 1n)) return new Pow(b, S.NegOne);
  }

  if (b instanceof Special || e instanceof Special) {
    const r = powSpecial(b, e);
    if (r) return r;
  }

  if (isNum(b) && isNum(e)) {
    if (e instanceof Rational && e.isInteger) {
      if (b.isZero && e.isNegative) return S.ComplexInfinity;
      return numPowInt(b, e.p);
    }
    if (b instanceof Float || e instanceof Float) return floatPow(b, e);
    if (b.isZero) return e.isPositive ? S.Zero : S.ComplexInfinity;
    return mul(new Pow(b, e));
  }

  // SymPy Rational._eval_power: (-2)**(2*n) = 2**(2*n) for an even exponent
  if ((b instanceof Rational || b instanceof Float) && b.isNegative && isEvenQ(e)) return pow(numNeg(b), e);

  if (b instanceof Rational && b.isZero) {
    if (isPositive(e)) return S.Zero;
    if (isNegative(e)) return S.ComplexInfinity;
  }

  if (isI(b) && e instanceof Rational && e.isInteger) {
    const m = ((e.p % 4n) + 4n) % 4n;
    return at([S.One, S.I, S.NegOne, mul(-1, S.I)], Number(m));
  }

  // a number with an infinite part off the real axis (oo + I, 1 - oo*I): its powers are zoo, 0 for a
  // negative exponent (SymPy (oo + I)**(1/2) = zoo, (oo + I)**-1 = 0)
  if (b instanceof Add && (e instanceof Rational || e instanceof Float) && b.args.some(hasInfinity) && b.freeSymbols().size === 0) {
    return e.isNegative ? S.Zero : S.ComplexInfinity;
  }

  if (b instanceof Add && e instanceof Rational && e.p === -1n && e.q === 1n) {
    const pc = pureComplex(b);
    if (pc) {
      const [r, i] = pc;
      const den = numAdd(numMul(r, r), numMul(i, i));
      const num = add(r, mul(numNeg(i), S.I));
      const k = den instanceof Rational ? Rational.of(den.q, den.p) : numInv(den);
      if (k instanceof Rational && k.isOne) return num;
      // num = r - i*I is a sum: r is the nonzero numeric term of b
      return new Mul([k, num]);
    }
  }

  // Abs(u)**(2k) = u**(2k) for real u
  if (b instanceof Fn && b.name === 'abs' && e instanceof Rational && e.isInteger && e.p % 2n === 0n && isReal(at(b.args, 0))) {
    return pow(at(b.args, 0), e);
  }

  if (b instanceof Pow) {
    const r = powOfPow(b, e);
    if (r) return r;
  }

  // SymPy Mul._eval_power: distribute integer powers; split off positive factors only for numeric exponents
  if (b instanceof Mul && !b.isCommutative) return new Pow(b, e);
  if (b instanceof Mul && (e instanceof Rational || e instanceof Float)) {
    if (e instanceof Rational && e.isInteger) return mul(...b.args.map((f) => pow(f, e)));
    return mulPow(b, e);
  }

  if (isE(b)) {
    const ei = expImaginaryInfinity(e);
    if (ei !== undefined) return ei;
    if (e instanceof Fn && e.name === 'log') return at(e.args, 0);
    const terms = e instanceof Add ? e.args : [e];
    let m = 0n;
    let extracted = false;
    const remaining: Expr[] = [];
    for (const t of terms) {
      const [c, rest] = splitCoeff(t);
      if (c instanceof Rational && rest.key === iPi().key) {
        const twice = numMul(c, S.Two);
        if (twice.isInteger) {
          m += twice.p;
          extracted = true;
          continue;
        }
      }
      remaining.push(t);
    }
    if (extracted) {
      const k = ((m % 4n) + 4n) % 4n;
      const f = at([S.One, S.I, S.NegOne, mul(-1, S.I)], Number(k));
      return mul(f, pow(b, add(...remaining)));
    }
    // exp(c*I*pi) for a rational c (not a half-integer, handled above): c is reduced into (-1, 1]
    // (SymPy exp.eval: exp(4*I*pi/3) = exp(-2*I*pi/3))
    if (e instanceof Mul) {
      const [c, rest] = splitCoeff(e);
      if (c instanceof Rational && rest.key === iPi().key) {
        const period = 2n * c.q;
        let r = ((c.p % period) + period) % period;
        if (r > c.q) r -= period;
        if (r !== c.p) return pow(b, mul(Rational.of(r, c.q), iPi()));
      }
    }
    // exp(c*log(x)) -> x**c when the other factors are real numbers (SymPy exp.eval: comparable
    // terms; a node such as a real CRootOf says itself whether it is real)
    if (e instanceof Mul) {
      let logTerm: Expr | undefined;
      const coeffs: Expr[] = [];
      let ok = true;
      for (const t of e.args) {
        if (t instanceof Fn && t.name === 'log' && t.args.length === 1) {
          if (logTerm !== undefined) {
            ok = false;
            break;
          }
          logTerm = at(t.args, 0);
        } else if ((impl.freeSymbols(t).size === 0 || t instanceof ExtensionExpr) && isReal(t) === true) coeffs.push(t);
        else {
          ok = false;
          break;
        }
      }
      if (ok && logTerm !== undefined) return pow(logTerm, mul(...coeffs));
    }
    // exp(a + b) with exp(a) evaluating to a non-exp: split it off (SymPy exp.eval for Add)
    if (e instanceof Add) {
      const out: Expr[] = [];
      const rest: Expr[] = [];
      let changed = false;
      for (const a of e.args) {
        if (a instanceof Rational && a.isOne) {
          rest.push(a);
          continue;
        }
        const na = pow(b, a);
        if (na instanceof Pow && isE(na.base)) {
          if (na.exp.key !== a.key) changed = true;
          rest.push(na.exp);
        } else out.push(na);
      }
      if (out.length || changed) return mul(...out, rest.length ? pow(b, add(...rest)) : S.One);
    }
  }

  return new Pow(b, e);
}

/** A term oo, -oo or a product with oo (oo*I). */
const hasInfinity = (t: Expr): boolean => t instanceof Special || (t instanceof Mul && t.args.includes(S.Infinity));

/**
 * exp of a sum with an imaginary part +-oo: SymPy exp(oo*I) = nan, exp(x + oo*I) = nan, and the
 * limits exp(-oo + oo*I) = 0 (the modulus exp(-oo) vanishes; SymPy gives nan) and exp(oo + oo*I) =
 * zoo (the modulus grows without bound; SymPy gives nan); undefined for other exponents.
 */
function expImaginaryInfinity(e: Expr): Expr | undefined {
  const terms = e instanceof Add ? e.args : [e];
  // (c*oo*I with a real constant c: -oo*I, oo*I*pi)
  const isImInf = (t: Expr): boolean =>
    t instanceof Mul && t.args.includes(S.Infinity) && t.args.includes(S.I) && t.args.every((a) => a === S.Infinity || a === S.I || (a.freeSymbols().size === 0 && isReal(a) === true));
  if (!terms.some(isImInf)) return undefined;
  if (terms.includes(S.NegativeInfinity)) return S.Zero;
  return terms.includes(S.Infinity) ? S.ComplexInfinity : S.NaN;
}

/**
 * SymPy Mul._eval_power for a commutative product and a non-integer Rational or Float
 * exponent: sqrt(c*I) for a rational c with c/2 a square, then
 * Pow._eval_expand_power_base. Nonnegative (and polar) factors come out, negative factors
 * come out negated in pairs (sqrt(k*n) = sqrt(-k)*sqrt(-n) for negative k, n), and the
 * remaining factors stay under one power (sqrt(-3*x*y) = sqrt(3)*sqrt(-x*y)).
 */
function mulPow(b: Mul, e: Rational | Float): Expr {
  if (e instanceof Rational && e.q === 2n && b.args.length === 2) {
    const [a, u] = pair(b.args);
    if (a instanceof Rational && isI(u)) {
      const h = Rational.of(a.p < 0n ? -a.p : a.p, 2n * a.q);
      const rn = iroot(h.p, 2n);
      const rd = iroot(h.q, 2n);
      if (rn * rn === h.p && rd * rd === h.q) {
        const [c, rest] = splitCoeff(pow(add(1, a.isNegative ? mul(S.NegOne, S.I) : S.I), Rational.of(e.p)));
        return mulCoeffRaw(numMul(numPowInt(Rational.of(rn, rd), e.p), c), rest);
      }
    }
  }
  const other: Expr[] = [];
  const nonneg: Expr[] = [];
  const negs: Expr[] = [];
  for (const f of b.args) {
    if (isReal(f) === false) other.push(f);
    else if ((f instanceof Sym && f.assumptions.polar === true) || (f instanceof Fn && f.name === 'exp_polar')) nonneg.push(f);
    else {
      const nn = isNonNegative(f);
      (nn === true ? nonneg : nn === false ? negs : other).push(f);
    }
  }
  // the exponent is not an integer: negative factors come out in pairs, the residual -1 stays in `other`
  if (negs.length > 1) {
    let o: Num = S.One;
    const h = at(negs, 0);
    if (other.length === 0 && isNum(h)) {
      negs.shift();
      o = h;
    }
    if (negs.length % 2 === 1) o = numNeg(o);
    for (const n of negs) nonneg.push(neg(n));
    if (!(o instanceof Rational && o.isOne)) other.push(o);
  } else {
    const h = negs[0];
    if (h !== undefined && other.length > 0 && isNum(h) && h !== S.NegOne) {
      other.push(S.NegOne);
      nonneg.push(numNeg(h));
    } else other.push(...negs);
  }
  // a factor that is a product again (a negated negative factor) keeps its power unevaluated
  const parts = nonneg.map((f) => (f instanceof Mul ? new Pow(f, e) : pow(f, e)));
  if (other.length > 0) {
    const m = mul(...other);
    parts.push(m instanceof Mul ? new Pow(m, e) : pow(m, e));
  }
  return mul(...parts);
}

/** floor(t) of a branch number; t is an integer exactly for a rational angle (floor(0) = 0 in SymPy), so a tie rounds. */
function branchFloor(t: number): bigint {
  return BigInt(Math.abs(t - Math.round(t)) < 1e-9 ? Math.round(t) : Math.floor(t));
}

/** SymPy _half: the numerator of an exponent with a literal 2 as denominator, else undefined. */
function halfExp(e: Expr): Expr | undefined {
  const [c, rest] = splitCoeff(e);
  if (!(c instanceof Rational) || c.q !== 2n || isIntegerQ(rest) !== true) return undefined;
  return mul(Rational.of(c.p), rest);
}

/**
 * SymPy Pow._eval_power: (x**a)**e = s*x**(a*e) with s = 1 for an integer e, a polar x, |a| < 1,
 * a = 1 or a nonnegative x (after |x| for an even a and real x), and s = +-1 from the branch
 * floor(1/2 - a*arg(x)/(2*pi)) for an e with denominator 2 and a number x; (x**-1)**(1/2) =
 * (-1)**(1/2)*(-x)**(-1/2) for x < 0. Undefined when it stays unevaluated.
 */
function powOfPow(b: Pow, e: Expr): Expr | undefined {
  let [x, a] = b.args;
  const done = (sg: Expr): Expr => mul(sg, pow(x, mul(a, e)));
  if (isIntegerQ(e) === true) return done(S.One);
  if (isPolar(x)) return done(S.One);
  const realA = isReal(a);
  if (realA === true) {
    const half = halfExp(e);
    if (a instanceof Rational && a.p === -1n && a.q === 1n && half) {
      const nx = isNegative(x);
      if (nx === true) return mul(pow(S.NegOne, e), pow(neg(x), neg(e)));
      if (nx === false) return pow(x, neg(e));
    } else if (isEvenQ(a) && isReal(x) === true) x = impl.abs(x);
    const aVal = isNum(a) ? a.value : undefined;
    const absA = aVal === undefined ? undefined : Math.abs(aVal);
    // (SymPy also has a == 1, which a power never has)
    if ((absA !== undefined && absA < 1) || isNonNegative(x) === true) return done(S.One);
    if (half && aVal !== undefined) {
      const v = numericValue(x);
      if (v === undefined) return undefined;
      const k = branchFloor(0.5 - (aVal * Math.atan2(v.im, v.re)) / (2 * Math.PI));
      if (k === 0n) return done(S.One);
      // s = exp(pi*I*n*k) = (-1)**(n*k) for the numerator n of e
      if (half instanceof Rational) return done((half.p * k) % 2n === 0n ? S.One : S.NegOne);
    }
    return undefined;
  }
  if (realA === false) {
    // s = exp(2*pi*I*e*floor(1/2 - im(a*log(x))/(2*pi))) when it is +-1 (exp(4*I)**(1/2) = -exp(2*I))
    const vx = numericValue(x);
    const va = numericValue(a);
    if (vx === undefined || va === undefined) return undefined;
    const imLog = va.im * Math.log(Math.hypot(vx.re, vx.im)) + va.re * Math.atan2(vx.im, vx.re);
    const k = branchFloor(0.5 - imLog / (2 * Math.PI));
    if (k === 0n) return done(S.One);
    if (e instanceof Rational) {
      const twice = Rational.of(2n * e.p * k, e.q);
      if (twice.isInteger) return done(twice.p % 2n === 0n ? S.One : S.NegOne);
    }
  }
  return undefined;
}

/** Is e known to be an even integer (an even integer times an integer)? */
function isEvenQ(e: Expr): boolean {
  const [c, r] = splitCoeff(e);
  return c instanceof Rational && c.isInteger && c.p % 2n === 0n && isIntegerQ(r) === true;
}

/** The complex value of an expression without free symbols; undefined when it has none. */
function numericValue(e: Expr): ComplexValue | undefined {
  if (isNum(e)) return { re: e.value, im: 0 };
  if (impl.freeSymbols(e).size > 0) return undefined;
  try {
    return impl.toComplex(e);
  } catch {
    return undefined;
  }
}

/** oo**e (SymPy Infinity._eval_power); undefined when it stays unevaluated. */
function infPow(e: Expr): Expr | undefined {
  if (e instanceof Special) return e.name === 'oo' ? S.Infinity : e.name === '-oo' ? S.Zero : S.NaN;
  if (isPositive(e)) return S.Infinity;
  if (isNegative(e)) return S.Zero;
  const v = numericValue(e);
  if (v === undefined) return undefined;
  // a real number of unknown sign: decided numerically unless it is too close to 0
  if (v.im === 0) return Math.abs(v.re) > 1e-9 ? (v.re > 0 ? S.Infinity : S.Zero) : undefined;
  // a non-real exponent: the sign of the real part decides
  return v.re > 0 ? S.ComplexInfinity : v.re < 0 ? S.Zero : S.NaN;
}

/** Powers involving oo, -oo, zoo, nan (exponent 0 and 1 are handled by the caller). */
function powSpecial(b: Expr, e: Expr): Expr | undefined {
  if ((b instanceof Special && b.name === 'nan') || (e instanceof Special && e.name === 'nan')) return S.NaN;
  if (b instanceof Special) {
    if (b.name === 'oo') return infPow(e);
    if (b.name === 'zoo') {
      // SymPy gives zoo**oo = 0; |zoo|**oo is infinite, so zoo**oo = zoo here
      if (e instanceof Special && e.name === 'zoo') return S.NaN;
      if (isPositive(e)) return b;
      if (isNegative(e)) return S.Zero;
      return undefined;
    }
    // -oo (SymPy NegativeInfinity._eval_power: (-1)**e * oo**e)
    if (e instanceof Special) return S.NaN;
    if (e instanceof Rational && e.isInteger) {
      if (e.isNegative) return S.Zero;
      return e.p % 2n === 0n ? S.Infinity : S.NegativeInfinity;
    }
    if (impl.freeSymbols(e).size > 0) return isNegative(e) ? S.Zero : undefined;
    const inf = infPow(e);
    // (-oo)**(1/2) = oo*I, (-oo)**2.0 = oo, (-oo)**1.5 = -oo*I
    if (inf === S.Infinity) return mul(pow(S.NegOne, e), S.Infinity);
    // 0 for a negative exponent; zoo or nan for a non-real one, as (-1)**e is finite and nonzero
    return inf;
  }
  // exponent is oo, -oo or zoo
  const ex = cast(e, Special, 'exponent');
  if (ex.name === 'zoo') return S.NaN;
  const c = numericValue(b);
  // a non-real base (such as (1 + I)**oo) stays unevaluated, as in SymPy
  if (c?.im !== 0) return undefined;
  const v = c.re;
  const up = ex.name === 'oo';
  if (v === 1 || v === -1) return S.NaN;
  if (v > 1) return up ? S.Infinity : S.Zero;
  if (v > -1) {
    if (v === 0) return up ? S.Zero : S.ComplexInfinity;
    // SymPy gives (-1/2)**-oo = nan but (-2)**oo = zoo; both have modulus oo, so zoo here
    return up ? S.Zero : v > 0 ? S.Infinity : S.ComplexInfinity;
  }
  return up ? S.ComplexInfinity : S.Zero;
}

/** SymPy `pure_complex`: a + b*I with numeric a, b. */
function pureComplex(e: Add): [Num, Num] | undefined {
  if (e.args.length !== 2) return undefined;
  const [h, t] = pair(e.args);
  if (!isNum(h)) return undefined;
  if (isI(t)) return [h, S.One];
  if (t instanceof Mul && t.args.length === 2) {
    const [t0, t1] = pair(t.args);
    if (isNum(t0) && isI(t1)) return [h, t0];
  }
  return undefined;
}

export function neg(x: ExprLike): Expr {
  return mul(S.NegOne, x);
}

export function sub(a: ExprLike, b: ExprLike): Expr {
  return impl.arithmetic?.('sub', [sympify(a), sympify(b)]) ?? add(a, mul(S.NegOne, b));
}

export function div(a: ExprLike, b: ExprLike): Expr {
  return mul(a, pow(b, S.NegOne));
}

/** Square root: x^(1/2). */
export function sqrt(x: ExprLike): Expr {
  return pow(x, S.Half);
}

/** The exponential function, represented as E^x. */
export function exp(x: ExprLike): Expr {
  return pow(S.E, x);
}

/** Exact rational p/q. */
export function rational(p: bigint | number, q: bigint | number = 1): Rational {
  return Rational.of(p, q);
}

/**
 * Heuristic: does the expression "look negative" (a leading minus sign could be
 * extracted)? Used to choose canonical signs, e.g. sin(-x) -> -sin(x).
 */
export function couldExtractMinusSign(e: Expr): boolean {
  if (isNum(e)) return e.isNegative;
  if (isMulLike(e)) {
    const c = at(e.args, 0);
    return isNum(c) && c.isNegative;
  }
  if (isAddLike(e)) {
    let negCount = 0;
    let posCount = 0;
    for (const t of e.args) {
      if (couldExtractMinusSign(t)) negCount++;
      else posCount++;
    }
    if (negCount !== posCount) return negCount > posCount;
    // SymPy decides a tie by sort_key, preferring x - 1 to 1 - x and 3 - sqrt(2) to -3 + sqrt(2)
    const n = neg(e);
    return impl.compareSortKey ? impl.compareSortKey(e, n) < 0 : n.key < e.key;
  }
  return false;
}

impl.sympify = sympify;
registerFromiter(Add, (args) => add(...args));
registerFromiter(Mul, (args) => mul(...args));
registerFromiter(Pow, (args) => pow(at(args, 0), at(args, 1)));
impl.add = add;
impl.mul = mul;
impl.pow = pow;
impl.couldExtractMinusSign = couldExtractMinusSign;

/** SymPy root(x, n, k): the k-th n-th root, x**(1/n)*(-1)**(2*k/n). */
export function root(x: ExprLike, n: ExprLike, k: ExprLike = 0): Expr {
  const nn = sympify(n);
  const kk = sympify(k);
  const r = pow(x, pow(nn, -1));
  if (kk instanceof Rational && kk.isZero) return r;
  return mul(r, pow(S.NegOne, mul(2, kk, pow(nn, -1))));
}

/** SymPy cbrt(x) = x**(1/3). */
export function cbrt(x: ExprLike): Expr {
  return pow(x, Rational.of(1n, 3n));
}

/** SymPy real_root(x, n): the real n-th root for real x and odd n. */
export function realRoot(xIn: ExprLike, nIn: ExprLike): Expr {
  const x = sympify(xIn);
  const n = sympify(nIn);
  if (n instanceof Rational && n.isInteger) {
    if (n.p === 1n || n.p === -1n) return root(x, n);
    if (n.p % 2n !== 0n && isReal(x) === true) {
      if (impl.sign === undefined) throw new NotLoadedError("sign is not available: import '@symjs/symjs/core' (or '@symjs/symjs')");
      return mul(impl.sign(x), root(impl.abs(x), n));
    }
  }
  return root(x, n);
}
