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
import {
  Add,
  Constant,
  Expr,
  ExprLike,
  Float,
  Fn,
  Mul,
  Num,
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
import { factorInt } from './numbers';

export function sympify(x: ExprLike): Expr {
  if (x instanceof Expr) return x;
  if (typeof x === 'bigint') return Rational.of(x);
  if (typeof x === 'number') {
    if (Number.isInteger(x)) return Rational.of(BigInt(x));
    return new Float(x);
  }
  throw new TypeError(`Cannot convert ${String(x)} to an expression`);
}

/** Float ** number (SymPy Float._eval_power / Rational._eval_power with a Float exponent). */
function floatPow(b: Num, e: Num): Expr {
  const fb = b instanceof Float ? b : new Float(toMpf(b, (e as Float).prec), (e as Float).prec);
  if (fb.isZero) return e.isPositive ? fb : S.ComplexInfinity;
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
  if (e instanceof Mul && isNum(e.args[0]!)) {
    const rest = e.args.length === 2 ? e.args[1]! : new Mul(e.args.slice(1));
    return [e.args[0] as Num, rest];
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
  if (e instanceof Special) return false;
  if (impl.freeSymbols(e).size > 0) return false;
  try {
    const v = impl.toComplex(e);
    return Number.isFinite(v.re) && Number.isFinite(v.im) && (!real || Math.abs(v.im) < 1e-300);
  } catch {
    return false;
  }
}

function addSpecial(args: Expr[]): Expr | undefined {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Add ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const specials = flat.filter((e): e is Special => e instanceof Special);
  if (specials.length === 0) return undefined;
  const names = new Set(specials.map((e) => e.name));
  if (names.has('nan')) return S.NaN;
  let inf: Special;
  if (names.has('zoo')) {
    if (names.has('oo') || names.has('-oo')) return S.NaN;
    inf = S.ComplexInfinity;
  } else if (names.has('oo') && names.has('-oo')) return S.NaN;
  else inf = names.has('oo') ? S.Infinity : S.NegativeInfinity;
  const others = flat.filter((e) => !(e instanceof Special) && !isFiniteConstant(e, inf !== S.ComplexInfinity));
  if (others.length === 0) return inf;
  const rest = add(...others);
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
    const ps = term.args.map((a) => lowestPower(a, t));
    if (ps.some((p) => p === undefined)) return undefined;
    return Math.min(...(ps as number[]));
  }
  return undefined;
}

/** Sum containing Order terms: keep the weakest Order and drop the terms it absorbs. */
function addOrder(args: Expr[]): Expr | undefined {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Add ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const orders = flat.filter((e): e is Order => e instanceof Order);
  if (orders.length === 0) return undefined;
  // O((x - x0)**n) : base t = x - x0 (or x), exponent n
  const info = orders.map((o) => {
    const [b, k] = o.expr instanceof Pow ? o.expr.args : [o.expr, S.One];
    return { o, base: b, k: k instanceof Rational ? k.value : NaN };
  });
  const sameBase = info.every((i) => i.base.key === info[0]!.base.key);
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

/** lowestPower for a shifted base (x - x0): only exact powers of the base are recognized. */
function lowestPowerShifted(term: Expr, base: Expr): number | undefined {
  if (term.key === base.key) return 1;
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
  if (sx.some((e) => e instanceof Order || (e instanceof Add && e.args.some((a) => a instanceof Order)))) {
    const r = addOrder(sx);
    if (r) return r;
  }
  if (sx.some((e) => e instanceof Special || (e instanceof Add && e.args.some((a) => a instanceof Special)))) {
    const r = addSpecial(sx);
    if (r) return r;
  }
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
  if (out.length === 1) return out[0]!;
  return new Add(out);
}

// ---------------------------------------------------------------------------
// Mul
// ---------------------------------------------------------------------------

/** Accumulates rational bases raised to rational powers, factored into primes. */
class Radicals {
  /** prime (or unfactored cofactor) -> exponent */
  private readonly primes = new Map<bigint, Rational>();
  /** exponent of -1 */
  negOne: Rational = S.Zero;

  addPower(base: Rational, exp: Rational): void {
    if (base.isNegative) {
      this.negOne = numAdd(this.negOne, exp) as Rational;
      base = Rational.of(-base.p, base.q);
    }
    if (base.isOne) return;
    const push = (n: bigint, sign: bigint) => {
      if (n === 1n) return;
      for (const [p, k] of factorInt(n)) {
        const inc = numMul(exp, Rational.of(sign * k)) as Rational;
        this.primes.set(p, numAdd(this.primes.get(p) ?? S.Zero, inc) as Rational);
      }
    };
    push(base.p, 1n);
    push(base.q, -1n);
  }

  get isEmpty(): boolean {
    return this.primes.size === 0 && this.negOne.isZero;
  }

  /** Resolve into a rational coefficient, a power of I, and leftover radical factors. */
  resolve(): { coeff: Rational; iPow: bigint; factors: Expr[] } {
    let coeff: Rational = S.One;
    let iPow = 0n;
    const factors: Expr[] = [];
    // group by fractional exponent
    const groups = new Map<string, { exp: Rational; base: bigint }>();
    for (const [p, e] of this.primes) {
      if (e.isZero) continue;
      const k = ratFloor(e);
      const f = numAdd(e, Rational.of(-k)) as Rational;
      if (k !== 0n) coeff = numMul(coeff, numPowInt(Rational.of(p), k)) as Rational;
      if (!f.isZero) {
        const g = groups.get(f.key);
        if (g) g.base *= p;
        else groups.set(f.key, { exp: f, base: p });
      }
    }
    for (const { exp, base } of groups.values()) factors.push(new Pow(Rational.of(base), exp));

    // (-1)^n with n reduced to [0, 2)
    let n = this.negOne;
    if (!n.isZero) {
      const k = ratFloor(Rational.of(n.p, n.q * 2n));
      n = numAdd(n, Rational.of(-2n * k)) as Rational; // n in [0, 2)
      const twice = numMul(n, S.Two) as Rational;
      if (twice.isInteger) {
        iPow += twice.p; // (-1)^(m/2) = I^m
      } else {
        // represent with exponent in (-1, 1]
        const r = numCmp1(n) > 0 ? (numAdd(n, Rational.of(-2n)) as Rational) : n;
        factors.push(new Pow(S.NegOne, r));
      }
    }
    return { coeff, iPow, factors };
  }
}

const numCmp1 = (r: Rational): number => {
  const d = r.p - r.q;
  return d > 0n ? 1 : d < 0n ? -1 : 0;
};

function mulSpecial(args: Expr[]): Expr | undefined {
  const flat: Expr[] = [];
  const visit = (e: Expr) => (e instanceof Mul ? e.args.forEach(visit) : flat.push(e));
  args.forEach(visit);
  const specials = flat.filter((e): e is Special => e instanceof Special);
  if (specials.length === 0) return undefined;
  if (specials.some((e) => e.name === 'nan')) return S.NaN;
  const c = mul(...flat.filter((e) => !(e instanceof Special)));
  if (c instanceof Rational && c.isZero) return S.NaN;
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
  if (args.some((e) => e instanceof Special || (e instanceof Mul && e.args.some((a) => a instanceof Special)))) {
    const r = mulSpecial(args);
    if (r) return r;
  }

  // SymPy's two-argument rule: Rational * Add distributes (2*(x + 1) -> 2*x + 2).
  if (args.length === 2) {
    let [a, b] = args as [Expr, Expr];
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

  const visit = (e: Expr): void => {
    if (isNum(e)) {
      coeff = numMul(coeff, e);
      return;
    }
    if (e instanceof Mul) {
      for (const a of e.args) visit(a);
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

  for (const { exp, bases } of numExp.values()) {
    const b = bases.reduce((acc, k) => numMul(acc, k));
    const r = bases.length === 1 ? new Pow(b, exp) : pow(b, exp);
    if (r instanceof Mul) r.args.forEach(absorb);
    else absorb(r);
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

  if (coeff instanceof Rational && coeff.isZero) return S.Zero;
  if (factors.length === 0) return coeff;
  factors.sort(compareExpr);
  const isOne = coeff instanceof Rational && coeff.isOne;
  if (factors.length === 1 && isOne) return factors[0]!;
  // end of SymPy Mul.flatten: Number * Add distributes (2*(1 + a) -> 2 + 2*a)
  if (factors.length === 1 && factors[0] instanceof Add) {
    const c = coeff as Num;
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

  if (e instanceof Rational) {
    if (e.isZero) return S.One;
    if (e.isOne) return b;
  }
  if (b instanceof Rational && b.isOne && !(e instanceof Special)) return S.One;
  if (isE(b) && e instanceof Float) return impl.evalf(new Pow(b, e), precToDps(e.prec));

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
    return [S.One, S.I, S.NegOne, mul(-1, S.I)][Number(m)]!;
  }

  if (b instanceof Add && e instanceof Rational && e.p === -1n && e.q === 1n) {
    const pc = pureComplex(b);
    if (pc) {
      const [r, i] = pc;
      const den = numAdd(numMul(r, r), numMul(i, i));
      const num = add(r, mul(numNeg(i), S.I));
      const k = den instanceof Rational ? Rational.of(den.q, den.p) : numInv(den);
      if (k instanceof Rational && k.isOne) return num;
      return new Mul([k, ...(num instanceof Mul ? num.args : [num])]);
    }
  }

  // Abs(u)**(2k) = u**(2k) for real u
  if (b instanceof Fn && b.name === 'abs' && e instanceof Rational && e.isInteger && e.p % 2n === 0n && isReal(b.args[0]!)) {
    return pow(b.args[0]!, e);
  }

  if (b instanceof Pow) {
    const [x, a] = b.args;
    if (e instanceof Rational && e.isInteger) return pow(x, mul(a, e));
    if (isPositive(x) && isReal(a) && isReal(e)) return pow(x, mul(a, e));
    // (x^(2k))^e = |x|^(2k e) for real x
    if (a instanceof Rational && a.isInteger && a.p % 2n === 0n && isReal(x) && isReal(e)) {
      return pow(impl.abs(x), mul(a, e));
    }
  }

  // SymPy Mul._eval_power: distribute integer powers; split off positive factors only for numeric exponents
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
    if (e instanceof Fn && e.name === 'log') return e.args[0]!;
    const terms = e instanceof Add ? e.args : [e];
    let m = 0n;
    let extracted = false;
    const remaining: Expr[] = [];
    for (const t of terms) {
      const [c, rest] = splitCoeff(t);
      if (c instanceof Rational && rest.key === iPi().key) {
        const twice = numMul(c, S.Two) as Rational;
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
      const f = [S.One, S.I, S.NegOne, mul(-1, S.I)][Number(k)]!;
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
          logTerm = t.args[0]!;
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

function realValue(e: Expr): number | undefined {
  if (isNum(e)) return e instanceof Rational ? e.value : e.value;
  if (impl.freeSymbols(e).size > 0) return undefined;
  try {
    const v = impl.toComplex(e);
    return v.im === 0 ? v.re : undefined;
  } catch {
    return undefined;
  }
}

/** Powers involving oo, -oo, zoo, nan (exponent 0 and 1 are handled by the caller). */
function powSpecial(b: Expr, e: Expr): Expr | undefined {
  if ((b instanceof Special && b.name === 'nan') || (e instanceof Special && e.name === 'nan')) return S.NaN;
  if (b instanceof Special) {
    const pos = isPositive(e);
    const neg = isNegative(e);
    if (b.name === 'oo' || b.name === 'zoo') {
      if (pos) return b;
      if (neg) return S.Zero;
      return undefined;
    }
    // -oo
    if (e instanceof Rational && e.isInteger) {
      if (e.isNegative) return S.Zero;
      return e.p % 2n === 0n ? S.Infinity : S.NegativeInfinity;
    }
    if (neg) return S.Zero;
    return undefined;
  }
  // exponent is oo, -oo or zoo
  const ex = e as Special;
  if (ex.name === 'zoo') return S.NaN;
  const v = realValue(b);
  if (v === undefined) return undefined;
  const up = ex.name === 'oo';
  if (v === 1 || v === -1) return S.NaN;
  if (v > 1) return up ? S.Infinity : S.Zero;
  if (v > -1) {
    if (v === 0) return up ? S.Zero : S.ComplexInfinity;
    return up ? S.Zero : v > 0 ? S.Infinity : S.ComplexInfinity;
  }
  return up ? S.ComplexInfinity : S.Zero;
}

/** SymPy `pure_complex`: a + b*I with numeric a, b. */
function pureComplex(e: Add): [Num, Num] | undefined {
  if (e.args.length !== 2) return undefined;
  const [h, t] = e.args as [Expr, Expr];
  if (!isNum(h)) return undefined;
  if (isI(t)) return [h, S.One];
  if (t instanceof Mul && t.args.length === 2 && isNum(t.args[0]!) && isI(t.args[1]!)) return [h, t.args[0] as Num];
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
    const c = e.args[0]!;
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
