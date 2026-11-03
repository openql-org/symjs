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

import { isIntegerQ, isNegative, isPositive, isReal } from './assumptions';
import type { ComplexValue, ExprLike, Num } from './nodes';
import {
  Add,
  Constant,
  Expr,
  Float,
  Fn,
  Mul,
  Pow,
  Rational,
  S,
  Order,
  Special,
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
    if (names.has('oo') || names.has('-oo')) return S.NaN;
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

export function add(...xs: ExprLike[]): Expr {
  const sx = xs.map(sympify);
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
  const visit = (e: Expr): void => {
    if (isNum(e)) {
      c = numAdd(c, e);
      return;
    }
    if (e instanceof Add) {
      for (const a of e.args) visit(a);
      return;
    }
    const [k, t] = splitCoeff(e);
    const entry = terms.get(t.key);
    if (entry) entry.coeff = numAdd(entry.coeff, k);
    else terms.set(t.key, { term: t, coeff: k });
  };
  for (const x of sx) visit(x);

  const out: Expr[] = [];
  for (const { term, coeff } of terms.values()) {
    if (coeff.isZero) continue;
    out.push(mulCoeffRaw(coeff, term));
  }
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
    const factors: Expr[] = [];
    for (const { e, b } of pnew.values()) {
      // the merged base is evaluated again (Pow(b, e))
      const [c, rads] = intPow(b, e);
      mulCoeff(c);
      for (const [rb, re] of rads) factors.push(new Pow(Rational.of(rb), re));
    }

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
        factors.push(new Pow(S.NegOne, r));
      }
    }
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
  // numeric bases raised to non-rational exponents, grouped by exponent (2**x*3**x -> 6**x)
  const numExp = new Map<string, { exp: Expr; bases: Num[] }>();
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
      iPow += 1n;
      return;
    }
    const [b, x] = asBaseExp(e);
    if (b instanceof Rational && x instanceof Rational) {
      radicals.addPower(b, x);
      return;
    }
    if (isNum(b) && (b.isPositive || isIntegerQ(x))) {
      const g = numExp.get(x.key);
      if (g) g.bases.push(b);
      else numExp.set(x.key, { exp: x, bases: [b] });
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

  for (const { base, terms } of general.values()) {
    for (const { term, coeffs, orig } of terms.values()) {
      if (coeffs.length === 1) {
        // a single occurrence is already canonical
        factors.push(orig);
        continue;
      }
      const c = coeffs.reduce((acc, k) => numAdd(acc, k));
      if (c instanceof Rational && c.isZero) continue;
      const r = pow(base, mul(c, term));
      if (r instanceof Mul) r.args.forEach(absorb);
      else absorb(r);
    }
  }

  // a number raised to a symbolic exponent is a number, a power or an infinity (never a product)
  for (const { exp, bases } of numExp.values()) {
    const b = bases.reduce((acc, k) => numMul(acc, k));
    absorb(bases.length === 1 ? new Pow(b, exp) : pow(b, exp));
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

  // exp_polar(a)*exp_polar(b) = exp_polar(a + b)
  const eps = factors.filter((f) => f instanceof Fn && f.name === 'exp_polar');
  if (eps.length > 1) {
    const merged = new Fn('exp_polar', [add(...eps.map((f) => at(f.args, 0)))]);
    for (const f of eps) factors.splice(factors.indexOf(f), 1);
    factors.push(merged);
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

  if (b instanceof Rational && b.isZero) {
    if (isPositive(e)) return S.Zero;
    if (isNegative(e)) return S.ComplexInfinity;
  }

  if (isI(b) && e instanceof Rational && e.isInteger) {
    const m = ((e.p % 4n) + 4n) % 4n;
    return at([S.One, S.I, S.NegOne, mul(-1, S.I)], Number(m));
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
    const [x, a] = b.args;
    if (e instanceof Rational && e.isInteger) return pow(x, mul(a, e));
    // SymPy Pow._eval_power: (b**a)**e = b**(a*e) for b > 0 and real a, or exp(a) with |im(a)| < pi
    if (isPositive(x) && isReal(a)) return pow(x, mul(a, e));
    if (isE(x) && !(e instanceof Rational && e.isInteger)) {
      const ia = impl.freeSymbols(a).size === 0 ? (() => {
        try {
          return impl.toComplex(a).im;
        } catch {
          return undefined;
        }
      })() : undefined;
      if (ia !== undefined && Math.abs(ia) < Math.PI) return pow(x, mul(a, e));
    }
    // (x^(2k))^e = |x|^(2k e) for real x
    if (a instanceof Rational && a.isInteger && a.p % 2n === 0n && isReal(x) && isReal(e)) {
      return pow(impl.abs(x), mul(a, e));
    }
  }

  // SymPy Mul._eval_power: distribute integer powers; split off positive factors only for numeric exponents
  if (b instanceof Mul && !b.isCommutative) return new Pow(b, e);
  if (b instanceof Mul && (e instanceof Rational || e instanceof Float)) {
    if (e instanceof Rational && e.isInteger) return mul(...b.args.map((f) => pow(f, e)));
    const pos: Expr[] = [];
    const rest: Expr[] = [];
    for (const f of b.args) {
      if (isNum(f) && f.isNegative && !(f instanceof Rational && f.p === -1n && f.q === 1n)) {
        pos.push(numNeg(f));
        rest.push(S.NegOne);
      } else if (isPositive(f)) pos.push(f);
      else rest.push(f);
    }
    if (pos.length > 0) {
      const parts = pos.map((f) => pow(f, e));
      if (rest.length > 0) parts.push(pow(mul(...rest), e));
      return mul(...parts);
    }
  }

  if (isE(b)) {
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
    // exp(c*log(x)) -> x**c when the other factors are numbers (SymPy exp.eval)
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
        } else if (impl.freeSymbols(t).size === 0 && isReal(t) === true) coeffs.push(t);
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
    // (-oo)**(1/2) = oo*I; a Float exponent stays unevaluated
    if (inf === S.Infinity) return e instanceof Float ? undefined : mul(pow(S.NegOne, e), S.Infinity);
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
  return add(a, mul(S.NegOne, b));
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
  if (e instanceof Mul) {
    const c = at(e.args, 0);
    return isNum(c) && c.isNegative;
  }
  if (e instanceof Add) {
    let negCount = 0;
    let posCount = 0;
    for (const t of e.args) {
      if (couldExtractMinusSign(t)) negCount++;
      else posCount++;
    }
    if (negCount !== posCount) return negCount > posCount;
    return neg(e).key < e.key;
  }
  return false;
}

impl.sympify = sympify;
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
