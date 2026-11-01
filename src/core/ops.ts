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

import { isNegative, isPositive, isReal } from './assumptions';
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
  compareExpr,
  impl,
  isNum,
} from './nodes';
import { numAdd, numMul, numNeg, numPowInt, ratFloor } from './num';
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

export function add(...xs: ExprLike[]): Expr {
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
  for (const x of xs) visit(sympify(x));

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

export function mul(...xs: ExprLike[]): Expr {
  let coeff: Num = S.One;
  let iPow = 0n;
  const general = new Map<string, { base: Expr; exps: Expr[] }>();
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
    const g = general.get(b.key);
    if (g) g.exps.push(x);
    else general.set(b.key, { base: b, exps: [x] });
  };
  for (const x of xs) visit(sympify(x));

  if (coeff instanceof Rational && coeff.isZero) return S.Zero;

  const factors: Expr[] = [];
  const absorb = (r: Expr): void => {
    if (isNum(r)) coeff = numMul(coeff, r);
    else if (isI(r)) iPow += 1n;
    else if (r instanceof Rational && r.isOne) return;
    else factors.push(r);
  };

  for (const { base, exps } of general.values()) {
    const x = exps.length === 1 ? exps[0]! : add(...exps);
    if (x instanceof Rational && x.isZero) continue;
    // A single occurrence is already canonical; only combined exponents need re-evaluation.
    const r = exps.length > 1 ? pow(base, x) : x instanceof Rational && x.isOne ? base : new Pow(base, x);
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
  if (factors.length === 1) {
    const f = factors[0]!;
    if (isOne) return f;
    if (f instanceof Add) return add(...f.args.map((t) => mul(coeff, t)));
    return new Mul([coeff, f]);
  }
  return new Mul(isOne ? factors : [coeff, ...factors]);
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
  if (b instanceof Rational && b.isOne) return S.One;

  if (isNum(b) && isNum(e)) {
    if (e instanceof Rational && e.isInteger) return numPowInt(b, e.p);
    if (b instanceof Float || e instanceof Float) {
      const bv = b instanceof Rational ? b.value : b.value;
      const ev = e instanceof Rational ? e.value : e.value;
      if (bv >= 0) return new Float(Math.pow(bv, ev));
      const r = Math.pow(-bv, ev);
      return add(new Float(r * Math.cos(Math.PI * ev)), mul(new Float(r * Math.sin(Math.PI * ev)), S.I));
    }
    if (b.isZero) {
      if (e.isPositive) return S.Zero;
      throw new RangeError('Division by zero: 0 raised to a negative power');
    }
    return mul(new Pow(b, e));
  }

  if (b instanceof Rational && b.isZero) {
    if (isPositive(e)) return S.Zero;
    if (isNegative(e)) throw new RangeError('Division by zero: 0 raised to a negative power');
  }

  if (isI(b) && e instanceof Rational && e.isInteger) {
    const m = ((e.p % 4n) + 4n) % 4n;
    return [S.One, S.I, S.NegOne, mul(-1, S.I)][Number(m)]!;
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

  if (b instanceof Mul) {
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
    // canonical exponent: distribute products over sums, exp(I*(a+b)) -> exp(I*a + I*b)
    if (e instanceof Mul && e.args.some((f) => f instanceof Add)) return pow(b, impl.expand(e));
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
  }

  return new Pow(b, e);
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
