// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/core/assumptions.py: _ask; the _eval_is_* handlers of
// sympy/core/add.py, sympy/core/mul.py, sympy/core/power.py, sympy/core/numbers.py,
// sympy/core/mod.py and sympy/functions/elementary/{exponential,complexes,integers,trigonometric}.py;
// _monotonic_sign of sympy/core/exprtools.py; fraction of sympy/simplify/radsimp.py;
// _peeloff_pi of sympy/functions/elementary/trigonometric.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License.

/**
 * @file The assumption facts of an expression as SymPy's `expr.is_<fact>`
 * properties compute them: each fact is decided by the handler of the
 * expression's class (`_eval_is_<fact>`) or, when that gives no answer, by
 * the handlers of the facts that can imply it (`_assume_rules.prereq`),
 * and every value found is closed under the implications between the facts
 * and cached on the expression.
 *
 * Numbers, constants and symbols have their facts from their values and
 * assumptions; sums, products, powers, `exp`, `Abs`, `re`, `im`, `sign`,
 * `floor`, `ceiling`, `frac`, `tan`, `cot`, `exp_polar` and `Mod` have
 * SymPy's handlers; other expressions take what `ask` decides for each
 * predicate.
 */

import type { Expr } from './nodes';
import { Add, Constant, Dummy, ExtensionExpr, Float, Fn, Mul, Pow, Rational, S, Special, Sym, impl } from './nodes';
import { add, asBaseExp, mul, neg, pow, sub } from './ops';
import { freeSymbols, subs, xreplace } from './traverse';
import { asCoeffMul, asNumerDenom, coeff, isPolynomial } from './methods';
import { FACT_PREREQUISITES, deduceFacts } from './facts';
import { Q, ask } from './refine';
import { assumptions } from './checkassumptions';
import { isNegative as numberIsNegative, isPositive as numberIsPositive } from './assumptions';
import { at } from './guard';

/** A fact value: true, false or undefined for SymPy's None. */
type V = boolean | undefined;

type Handler = (e: Expr) => V;

interface FactState {
  /** The facts known (the knowledge base, closed under the implications). */
  readonly kb: Map<string, boolean>;
  /** Facts already found to be undecidable. */
  readonly none: Set<string>;
  /** Facts being decided (a query for one of them gives undefined). */
  readonly busy: Set<string>;
}

const states = new WeakMap<Expr, FactState>();

/** SymPy `expr.is_<name>` for an assumption fact name such as 'positive' or 'extended_real'. */
export function fact(e: Expr, name: string): V {
  // (SymPy Pow sets is_commutative directly, outside the facts; it has no handler for it)
  if (name === 'commutative' && e instanceof Pow) return e.isCommutative;
  // (SymPy Float: is_rational and is_irrational are None)
  if (e instanceof Float && (name === 'rational' || name === 'irrational')) return undefined;
  const st = stateOf(e);
  const known = st.kb.get(name);
  if (known !== undefined || st.none.has(name) || st.busy.has(name)) return known;
  st.busy.add(name);
  try {
    // SymPy _ask: the handler of the fact, then those of its prerequisites (breadth first)
    const queue = [name];
    for (const f of queue) {
      if (st.kb.has(f)) continue;
      // (a handler querying a fact being decided gets undefined, which bounds the recursion)
      const v = handlerFor(e, f)?.();
      if (v !== undefined) tell(st, f, v);
      const r = st.kb.get(name);
      if (r !== undefined) return r;
      for (const p of FACT_PREREQUISITES.get(f) ?? []) if (!queue.includes(p)) queue.push(p);
    }
    st.none.add(name);
    return undefined;
  } finally {
    st.busy.delete(name);
  }
}

/** Adds a fact and its consequences; a value contradicting what is known is dropped. */
function tell(st: FactState, k: string, v: boolean): void {
  const next = new Map(st.kb);
  try {
    deduceFacts(next, [[k, v]]);
  } catch {
    return;
  }
  for (const [nk, nv] of next) st.kb.set(nk, nv);
}

function stateOf(e: Expr): FactState {
  let st = states.get(e);
  if (st === undefined) {
    st = { kb: new Map(), none: new Set(), busy: new Set() };
    states.set(e, st);
    for (const [k, v] of initialFacts(e)) tell(st, k, v);
  }
  return st;
}

const fromRecord = (r: Readonly<Record<string, boolean>>): Map<string, boolean> => deduceFacts(new Map(), Object.entries(r));

/** The class facts of SymPy's constants (NumberSymbol, ImaginaryUnit) and infinities. */
const CONSTANT_FACTS: Readonly<Record<string, Readonly<Record<string, boolean>>>> = {
  pi: { positive: true, irrational: true, transcendental: true },
  E: { positive: true, irrational: true, transcendental: true },
  I: { imaginary: true, algebraic: true },
  EulerGamma: { positive: true },
  Catalan: { positive: true },
  GoldenRatio: { positive: true, irrational: true, algebraic: true },
  TribonacciConstant: { positive: true, irrational: true, algebraic: true },
  'oo': { extended_positive: true, infinite: true },
  '-oo': { extended_negative: true, infinite: true },
  zoo: { infinite: true, extended_real: false },
  nan: {},
};

/** The facts an expression has before any handler runs. */
function initialFacts(e: Expr): Map<string, boolean> {
  if (e instanceof Rational) {
    const r: Record<string, boolean> = { rational: true, zero: e.p === 0n, positive: e.p > 0n, negative: e.p < 0n, integer: e.q === 1n };
    if (e.q === 1n) {
      r['odd'] = e.p % 2n !== 0n;
      // SymPy Integer._eval_is_prime and _eval_is_composite
      const prime = e.p > 1n && ask(Q.prime(e)) === true;
      r['prime'] = prime;
      r['composite'] = e.p > 1n && !prime;
    }
    return fromRecord({ commutative: true, ...r });
  }
  if (e instanceof Float) {
    // SymPy Float: real, with _eval_is_integer true for 0 and false when not integer valued
    const r: Record<string, boolean> = { commutative: true, real: true, zero: e.isZero, positive: e.isPositive, negative: e.isNegative };
    if (e.isZero) r['integer'] = true;
    else if (BigInt(e.mpf.exp) < 0n) r['integer'] = false;
    return fromRecord(r);
  }
  if (e instanceof Constant || e instanceof Special) return fromRecord({ commutative: true, ...CONSTANT_FACTS[e.name] });
  if (e instanceof Sym) return e.assumptions0;
  if (e instanceof ExtensionExpr && 'assumptions0' in e && e.assumptions0 instanceof Map && e.assumptions0.size > 0) return e.assumptions0;
  if (e instanceof Add || e instanceof Mul || e instanceof Pow) return new Map();
  // (SymPy Function._eval_is_commutative: all the arguments are commutative)
  const f = functionFacts(e);
  if (f !== undefined) return fromRecord({ ...f.given, commutative: e.isCommutative });
  const kb = new Map<string, boolean>(assumptions(e));
  kb.set('commutative', e.isCommutative);
  return kb;
}

/** The handler of a fact for the class of e, bound to e. */
function handlerFor(e: Expr, f: string): (() => V) | undefined {
  const bind = <T extends Expr>(h: ((x: T) => V) | undefined, x: T): (() => V) | undefined => (h === undefined ? undefined : () => h(x));
  if (f === 'finite' && e instanceof Fn && (e.name === 'sin' || e.name === 'cos') && is(at(e.args, 0), 'extended_real')) return () => true;
  if (e instanceof Add) return bind(ADD[f], e);
  if (e instanceof Mul) return bind(MUL[f], e);
  if (e instanceof Pow) return bind((isExp(e) ? EXP : POW)[f], e);
  const f2 = functionFacts(e);
  // (SymPy Expr: the sign of a number from its value, unless the class decides it)
  const sign = f === 'extended_positive' ? 1 : f === 'extended_negative' ? -1 : 0;
  return bind(f2?.handlers[f] ?? (f2 && sign !== 0 ? (x: Expr) => numberSign(x, sign === 1 ? 1 : -1) : undefined), e);
}

/** The class facts and handlers of the functions whose SymPy handlers are ported here. */
function functionFacts(e: Expr): FunctionFacts | undefined {
  if (e instanceof Fn) return FUNCTIONS[e.name];
  return e instanceof ExtensionExpr ? FUNCTIONS[e.name] : undefined;
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

const is = (e: Expr, k: string): boolean => fact(e, k) === true;
const isNot = (e: Expr, k: string): boolean => fact(e, k) === false;
const fuzzyNot = (v: V): V => (v === undefined ? undefined : !v);
function fuzzyOr(vs: readonly (() => V)[]): V {
  let rv: V = false;
  for (const f of vs) {
    const v = f();
    if (v === true) return true;
    if (v === undefined) rv = undefined;
  }
  return rv;
}

/**
 * SymPy `_fuzzy_group`: true when all are true, undefined when one is
 * unknown, false otherwise (with quick: undefined when more than one is false).
 */
function group(args: readonly Expr[], k: string, quick = true): V {
  let other = false;
  for (const a of args) {
    const v = fact(a, k);
    if (v === true) continue;
    if (v === undefined) return undefined;
    if (quick && other) return undefined;
    other = true;
  }
  return !other;
}

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const isRat = (e: Expr, p: bigint, q = 1n): boolean => e instanceof Rational && e.p === p && e.q === q;
const isAbsOne = (e: Expr): boolean => e instanceof Rational && e.q === 1n && (e.p === 1n || e.p === -1n);
const isZeroValue = (e: Expr): boolean => (e instanceof Rational || e instanceof Float) && e.isZero;
const isI = (e: Expr): boolean => e instanceof Constant && e.name === 'I';
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const without = (xs: readonly Expr[], x: Expr): Expr[] => {
  const i = xs.indexOf(x);
  return [...xs.slice(0, i), ...xs.slice(i + 1)];
};
/** SymPy as_coeff_Add: the numeric term and the rest. */
function coeffAdd(e: Expr): [Expr, Expr] {
  const [c] = e.args;
  if (e instanceof Add && (c instanceof Rational || c instanceof Float)) return [c, add(...e.args.slice(1))];
  return [S.Zero, e];
}
/** The number of trailing zero bits of an integer, 0 for 0 (SymPy trailing). */
function trailing(n: bigint): number {
  let m = n < 0n ? -n : n;
  let t = 0;
  while (m !== 0n && (m & 1n) === 0n) {
    m >>= 1n;
    t++;
  }
  return t;
}
/** The exponents of the even factors (SymPy `Add(*[i.as_base_exp()[1] for i in xs if i.is_even])`). */
const evenExponents = (xs: readonly Expr[]): Expr => add(...xs.filter((i) => is(i, 'even')).map((i) => asBaseExp(i)[1]));
/** A named function of the elementary functions module (undefined when it is not loaded). */
const fn = (name: 'log' | 'arg', x: Expr): Expr | undefined => impl.fn?.(name, [x]);
const logImaginary = (b: Expr): V => {
  const l = fn('log', b);
  return l && fact(l, 'imaginary');
};
/** Every Pow node of an expression (SymPy atoms(Pow)). */
function powsOf(e: Expr): Pow[] {
  const out: Pow[] = [];
  const go = (x: Expr): void => {
    if (x instanceof Pow) out.push(x);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

/**
 * SymPy fraction(expr): the numerator and denominator of a product, a
 * factor with a negative exponent going to the denominator.
 */
function fraction(e: Expr): [Expr, Expr] {
  const numer: Expr[] = [];
  const denom: Expr[] = [];
  for (const term of mulArgs(e)) {
    if (term.isCommutative && term instanceof Pow) {
      const [b, ex] = term.args;
      if (is(ex, 'negative')) denom.push(isRat(ex, -1n) ? b : pow(b, neg(ex)));
      else if (is(ex, 'positive') || !(ex instanceof Mul)) numer.push(term);
      else {
        const [n, d] = asNumerDenom(term);
        numer.push(n);
        denom.push(d);
      }
    } else if (term instanceof Rational && term.q !== 1n) {
      if (term.p !== 1n) numer.push(Rational.of(term.p));
      denom.push(Rational.of(term.q));
    } else {
      numer.push(term);
    }
  }
  return [mul(...numer), mul(...denom)];
}

/** SymPy Expr._eval_is_extended_positive_negative for a number (its numerical sign). */
const numberSign = (e: Expr, sign: 1 | -1): V => (e.isNumber ? (sign === 1 ? numberIsPositive(e) : numberIsNegative(e)) : undefined);

// ---------------------------------------------------------------------------
// _monotonic_sign
// ---------------------------------------------------------------------------

const EPS = new Dummy('eps', { positive: true });
const signDummy = (name: 'pos' | 'nneg' | 'neg' | 'npos'): Expr =>
  new Dummy(name, name === 'pos' ? { positive: true } : name === 'nneg' ? { nonnegative: true } : name === 'neg' ? { negative: true } : { nonpositive: true });

/**
 * SymPy _monotonic_sign: the value closest to 0 that the expression may have
 * when all its symbols are signed and its sign is the same for all their
 * values (a signed symbol for a value that is only known by its sign), or
 * undefined. The roots of the derivative of a univariate polynomial are not
 * computed here; such a polynomial is only decided when it is linear.
 */
export function monotonicSign(self: Expr): Expr | undefined {
  if (!is(self, 'extended_real')) return undefined;
  const ns = neg(self);
  if (ns instanceof Sym) {
    const rv = monotonicSign(ns);
    return rv === undefined ? undefined : neg(rv);
  }
  if (!(self instanceof Add) && asNumerDenom(self)[1].isNumber) {
    const s = self;
    if (is(s, 'prime')) return Rational.of(is(s, 'odd') ? 3 : 2);
    if (is(s, 'composite')) return Rational.of(is(s, 'odd') ? 9 : 4);
    if (is(s, 'positive')) {
      // (a positive even number that is not prime is composite, above)
      if (is(s, 'even')) return Rational.of(2);
      return is(s, 'integer') ? S.One : EPS;
    }
    if (is(s, 'extended_negative')) {
      if (is(s, 'even')) return Rational.of(-2);
      return is(s, 'integer') ? Rational.of(-1) : neg(EPS);
    }
    return is(s, 'zero') || is(s, 'extended_nonpositive') || is(s, 'extended_nonnegative') ? S.Zero : undefined;
  }
  const free = [...freeSymbols(self)];
  const [x] = free;
  if (x !== undefined && free.length === 1) {
    if (isPolynomial(self)) {
      let x0 = monotonicSign(x);
      if (x0 !== undefined && (x0 === EPS || neg(x0) === EPS)) x0 = S.Zero;
      if (x0 === undefined) return undefined;
      const d = impl.diff(self, x, 1);
      if (!d.isNumber) return undefined;
      const y = subs(self, [[x, x0]]);
      // (y is a number)
      if (is(x, 'nonnegative')) {
        if (is(y, 'nonnegative') && is(d, 'positive')) return isZeroValue(y) ? signDummy('nneg') : y;
        if (is(y, 'nonpositive') && is(d, 'negative')) return isZeroValue(y) ? signDummy('npos') : y;
      } else if (is(x, 'nonpositive')) {
        if (is(y, 'nonnegative') && is(d, 'negative')) return signDummy(isZeroValue(y) ? 'nneg' : 'pos');
        if (is(y, 'nonpositive') && is(d, 'positive')) return signDummy(isZeroValue(y) ? 'npos' : 'neg');
      }
      return undefined;
    }
    const [n, d] = asNumerDenom(self);
    let den: Expr | undefined;
    if (n.isNumber) den = monotonicSign(d);
    else if (!d.isNumber && monotonicSign(n) !== undefined) den = monotonicSign(d);
    // (a denominator that may be 0 leaves the expression not known to be extended real, above)
    if (den !== undefined) {
      const v = mul(n, den);
      if (is(v, 'positive')) return signDummy('pos');
      if (is(v, 'nonnegative')) return signDummy('nneg');
      if (is(v, 'negative')) return signDummy('neg');
      // (n has a sign and den is not 0, so v is nonnegative or nonpositive)
      return signDummy('npos');
    }
    return undefined;
  }
  const [c, a] = coeffAdd(self);
  let v: Expr | undefined;
  if (!isPolynomial(a)) {
    const [n, d] = asNumerDenom(a);
    if (!(n.isNumber || d.isNumber)) return undefined;
    if ((a instanceof Mul || a instanceof Pow) && is(a, 'rational') && powsOf(a).every((p) => p.exp instanceof Rational && p.exp.q === 1n) && (is(a, 'positive') || is(a, 'negative'))) {
      v = S.One;
      for (const ai of mulArgs(a)) {
        if (ai.isNumber) {
          v = mul(v, ai);
          continue;
        }
        const reps: [Expr, Expr][] = [];
        for (const s of freeSymbols(ai)) {
          const r = monotonicSign(s);
          if (r === undefined) return undefined;
          reps.push([s, r]);
        }
        v = mul(v, subs(ai, reps));
      }
    }
  } else if (!isZeroValue(c)) {
    const free = [...freeSymbols(a)];
    const signs = free.map((i) => [i, monotonicSign(i)] as const).filter((iv): iv is readonly [Expr, Expr] => iv[1] !== undefined);
    if (signs.length === free.length && !powsOf(a).some((p) => !p.isNumber) && (is(a, 'nonpositive') || is(a, 'nonnegative'))) {
      v = xreplace(a, signs.map(([i, vi]) => [i, isZeroValue(vi) ? (is(i, 'nonnegative') ? EPS : neg(EPS)) : vi]));
    }
  }
  if (v !== undefined) {
    const rv = add(v, c);
    if ((is(v, 'nonnegative') && is(rv, 'positive')) || (is(v, 'nonpositive') && is(rv, 'negative'))) return subs(rv, [[EPS, 0]]);
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Add
// ---------------------------------------------------------------------------

/** The real coefficient c of a product c*I (SymPy `a.as_coeff_mul(S.ImaginaryUnit)`), or undefined. */
function imaginaryCoeff(a: Expr): Expr | undefined {
  if (!(a instanceof Mul) || !a.args.some(isI)) return undefined;
  const [c, ai] = asCoeffMul(a, [S.I]);
  return ai.length === 1 && isI(at(ai, 0)) && is(c, 'extended_real') ? c : undefined;
}

function addImaginary(e: Expr): V {
  const nz: Expr[] = [];
  const imI: Expr[] = [];
  for (const a of e.args) {
    if (is(a, 'extended_real')) {
      const z = fact(a, 'zero');
      if (z === undefined) return undefined;
      if (!z) nz.push(a);
    } else if (is(a, 'imaginary')) {
      imI.push(mul(a, S.I));
    } else {
      const c = imaginaryCoeff(a);
      if (c === undefined) return undefined;
      imI.push(neg(c));
    }
  }
  const b = add(...nz);
  if (b.key === e.key) return undefined;
  const bz = fact(b, 'zero');
  if (bz === true) return fuzzyNot(fact(add(...imI), 'zero'));
  return bz === false ? false : undefined;
}

function addZero(e: Expr): V {
  if (!e.isCommutative) return undefined;
  const nz: Expr[] = [];
  let z = 0;
  let imOrZ = false;
  let im = 0;
  for (const a of e.args) {
    if (is(a, 'extended_real')) {
      const az = fact(a, 'zero');
      if (az === undefined) return undefined;
      if (az) z++;
      else nz.push(a);
    } else if (is(a, 'imaginary')) {
      im++;
    } else if (imaginaryCoeff(a) !== undefined) {
      imOrZ = true;
    } else {
      return undefined;
    }
  }
  if (z === e.args.length) return true;
  if (nz.length === 0 || nz.length === e.args.length) return undefined;
  const bz = fact(add(...nz), 'zero');
  if (bz === true && !imOrZ) {
    if (im === 0) return true;
    if (im === 1) return false;
  }
  return bz === false ? false : undefined;
}

function addOdd(e: Expr): V {
  const l = e.args.filter((f) => !is(f, 'even'));
  const [first] = l;
  if (first === undefined) return false;
  return is(first, 'odd') ? fact(add(...l.slice(1)), 'even') : undefined;
}

function addIrrational(e: Expr): V {
  for (const t of e.args) {
    const a = fact(t, 'irrational');
    if (a === true) return without(e.args, t).every((x) => is(x, 'rational')) ? true : undefined;
    if (a === undefined) return undefined;
  }
  return false;
}

/** SymPy Add._eval_is_extended_positive (sign 1) and _eval_is_extended_negative (sign -1). */
function addSign(e: Expr, sign: 1 | -1): V {
  if (e.isNumber) return numberSign(e, sign);
  const P = sign === 1 ? 'extended_positive' : 'extended_negative';
  const NN = sign === 1 ? 'extended_nonnegative' : 'extended_nonpositive';
  const NP = sign === 1 ? 'extended_nonpositive' : 'extended_nonnegative';
  const [c, a] = coeffAdd(e);
  if (!isZeroValue(c)) {
    const v = monotonicSign(a);
    if (v !== undefined) {
      const s = add(v, c);
      if (s.key !== e.key && is(s, P) && is(a, NN)) return true;
      if (freeSymbols(e).size === 1) {
        const w = monotonicSign(e);
        if (w !== undefined && w.key !== e.key && is(w, P)) return true;
      }
    }
  }
  let pos = false;
  let nonneg = false;
  let nonpos = false;
  let unknownSign = false;
  const sawInf = new Set<V>();
  const args = e.args.filter((x) => !is(x, 'zero'));
  if (args.length === 0) return false;
  for (const x of args) {
    const isPos = fact(x, P);
    const infinite = fact(x, 'infinite');
    if (infinite === true) {
      sawInf.add(fuzzyOr([() => isPos, () => fact(x, NN)]));
      if (sawInf.has(true) && sawInf.has(false)) return undefined;
    }
    if (isPos === true) {
      pos = true;
      continue;
    }
    if (is(x, NN)) {
      nonneg = true;
      continue;
    }
    if (is(x, NP)) {
      nonpos = true;
      continue;
    }
    if (infinite === undefined) return undefined;
    unknownSign = true;
  }
  if (sawInf.size) return sawInf.size > 1 ? undefined : [...sawInf][0];
  if (unknownSign) return undefined;
  if (!nonpos && pos) return true;
  if (!pos && !nonneg) return false;
  return undefined;
}

/** SymPy Add._eval_is_extended_nonnegative (sign 1) and _eval_is_extended_nonpositive (sign -1). */
function addWeakSign(e: Expr, sign: 1 | -1): V {
  if (e.isNumber) return undefined;
  const NN = sign === 1 ? 'extended_nonnegative' : 'extended_nonpositive';
  const [c, a] = coeffAdd(e);
  if (isZeroValue(c) || !is(a, NN)) return undefined;
  const v = monotonicSign(a);
  if (v === undefined) return undefined;
  const s = add(v, c);
  if (s.key !== e.key && is(s, NN)) return true;
  if (freeSymbols(e).size === 1) {
    const w = monotonicSign(e);
    if (w !== undefined && w.key !== e.key && is(w, NN)) return true;
  }
  return undefined;
}

const ADD: Readonly<Partial<Record<string, Handler>>> = {
  commutative: (e) => group(e.args, 'commutative', false),
  real: (e) => group(e.args, 'real'),
  extended_real: (e) => group(e.args, 'extended_real'),
  complex: (e) => group(e.args, 'complex'),
  antihermitian: (e) => group(e.args, 'antihermitian'),
  finite: (e) => group(e.args, 'finite'),
  hermitian: (e) => group(e.args, 'hermitian'),
  integer: (e) => group(e.args, 'integer'),
  rational: (e) => group(e.args, 'rational'),
  algebraic: (e) => group(e.args, 'algebraic'),
  infinite: (e) => {
    let saw = false;
    for (const a of e.args) {
      const v = fact(a, 'infinite');
      if (v === undefined) return undefined;
      if (v) {
        if (saw) return undefined;
        saw = true;
      }
    }
    return saw;
  },
  imaginary: addImaginary,
  zero: addZero,
  odd: addOdd,
  irrational: addIrrational,
  extended_positive: (e) => addSign(e, 1),
  extended_negative: (e) => addSign(e, -1),
  extended_nonnegative: (e) => addWeakSign(e, 1),
  extended_nonpositive: (e) => addWeakSign(e, -1),
};

// ---------------------------------------------------------------------------
// Mul
// ---------------------------------------------------------------------------

/** SymPy Mul._eval_is_zero_infinite_helper: [seen zero, seen infinite]. */
function zeroInfinite(e: Expr): [V, V] {
  let seenZero: V = false;
  let seenInfinite: V = false;
  for (const a of e.args) {
    const z = fact(a, 'zero');
    if (z === true) {
      if (seenInfinite !== false) return [undefined, undefined];
      seenZero = true;
      continue;
    }
    const inf = fact(a, 'infinite');
    if (inf === true) {
      if (seenZero !== false) return [undefined, undefined];
      seenInfinite = true;
      continue;
    }
    if (seenZero === false && z === undefined) {
      if (seenInfinite !== false) return [undefined, undefined];
      seenZero = undefined;
    }
    if (seenInfinite === false && inf === undefined) {
      if (seenZero !== false) return [undefined, undefined];
      seenInfinite = undefined;
    }
  }
  return [seenZero, seenInfinite];
}

function mulZero(e: Expr): V {
  const [z, inf] = zeroInfinite(e);
  if (z === false) return false;
  return z === true && inf === false ? true : undefined;
}

/** SymPy Mul._eval_is_rational and _eval_is_algebraic. */
function mulGroup(e: Expr, k: 'rational' | 'algebraic'): V {
  const r = group(e.args, k);
  if (r === true) return true;
  return r === false && e.args.every((a) => isNot(a, 'zero')) ? false : undefined;
}

function mulInteger(e: Expr): V {
  if (mulGroup(e, 'rational') === false) return false;
  const numerators: Expr[] = [];
  const denominators: Expr[] = [];
  let unknown = false;
  for (const a of e.args) {
    if (is(a, 'integer')) {
      if (!isAbsOne(a)) numerators.push(a);
    } else if (a instanceof Rational) {
      if (a.p !== 1n && a.p !== -1n) numerators.push(Rational.of(a.p));
      denominators.push(Rational.of(a.q));
    } else if (a instanceof Pow && !isExp(a)) {
      const [b, ex] = a.args;
      if (!is(b, 'integer') || !is(ex, 'integer')) unknown = true;
      if (!is(ex, 'negative')) return undefined;
      denominators.push(pow(a, -1));
    } else {
      return undefined;
    }
  }
  if (!denominators.length && !unknown) return true;
  const allOdd = (xs: readonly Expr[]): boolean => xs.every((i) => is(i, 'odd'));
  const allEven = (xs: readonly Expr[]): boolean => xs.every((i) => is(i, 'even'));
  const anyEven = (xs: readonly Expr[]): boolean => xs.some((i) => is(i, 'even'));
  if (!numerators.length && denominators.length && denominators.every((d) => is(sub(d, 1), 'extended_positive'))) return false;
  if (unknown) return undefined;
  if (allOdd(numerators) && anyEven(denominators)) return false;
  if (anyEven(numerators) && denominators.length === 1 && isRat(at(denominators, 0), 2n)) return true;
  if (allEven(numerators) && allOdd(denominators) && is(sub(mul(...denominators), 1), 'positive')) return false;
  const [d] = denominators;
  if (denominators.length === 1 && d instanceof Rational && d.q === 1n && is(d, 'even')) {
    if (is(sub(evenExponents(numerators), trailing(d.p)), 'nonnegative')) return true;
  }
  const [n] = numerators;
  if (numerators.length === 1 && n instanceof Rational && n.q === 1n && is(n, 'even')) {
    if (is(sub(evenExponents(denominators), trailing(n.p)), 'positive')) return false;
  }
  return undefined;
}

/** SymPy Mul._eval_real_imag: real is true for is_extended_real, false for is_imaginary. */
function realImag(e: Expr, realIn: boolean): V {
  let real = realIn;
  let zero: V = false;
  let tNotReIm: Expr | undefined;
  for (const t of e.args) {
    const ci = is(t, 'complex') ? true : fact(t, 'infinite');
    if (ci === false && isNot(t, 'extended_real')) return false;
    if (is(t, 'imaginary')) {
      real = !real;
    } else if (is(t, 'extended_real')) {
      // (zero is never true: a zero factor ends the loop)
      const z = fact(t, 'zero');
      if (z !== true && zero === false) zero = z;
      else if (z === true) return e.args.every((a) => is(a, 'finite')) ? true : undefined;
    } else if (isNot(t, 'extended_real') || isNot(t, 'imaginary')) {
      if (tNotReIm !== undefined) return undefined;
      tNotReIm = t;
    } else {
      return undefined;
    }
  }
  if (tNotReIm !== undefined) {
    if (isNot(tNotReIm, 'extended_real') && real) return zero;
    if (isNot(tNotReIm, 'imaginary') && !real) return zero;
    return undefined;
  }
  if (zero === false || real) return real;
  return undefined;
}

/** SymPy Mul._eval_herm_antiherm: herm is true for is_hermitian, false for is_antihermitian. */
function hermAntiherm(e: Expr, hermIn: boolean): V {
  let herm = hermIn;
  for (const t of e.args) {
    const h = fact(t, 'hermitian');
    const ah = fact(t, 'antihermitian');
    if (h === undefined || ah === undefined) return undefined;
    if (h) continue;
    if (!ah) return undefined;
    herm = !herm;
  }
  if (herm) return true;
  const z = mulZero(e);
  return z === true ? true : z === false ? herm : undefined;
}

function mulIrrational(e: Expr): V {
  for (const t of e.args) {
    const a = fact(t, 'irrational');
    if (a === true) return without(e.args, t).every((x) => is(x, 'rational') && isNot(x, 'zero')) ? true : undefined;
    if (a === undefined) return undefined;
  }
  return e.args.every((x) => is(x, 'real')) ? false : undefined;
}

/** SymPy Mul._eval_pos_neg. */
function mulSign(e: Expr, signIn: 1 | -1): V {
  let sign = signIn;
  let sawNon = false;
  let sawNot = false;
  for (const t of e.args) {
    if (is(t, 'extended_positive')) continue;
    if (is(t, 'extended_negative')) {
      sign = sign === 1 ? -1 : 1;
    } else if (is(t, 'zero')) {
      return e.args.every((a) => is(a, 'finite')) ? false : undefined;
    } else if (is(t, 'extended_nonpositive')) {
      sign = sign === 1 ? -1 : 1;
      sawNon = true;
    } else if (is(t, 'extended_nonnegative')) {
      sawNon = true;
    } else if (isNot(t, 'positive')) {
      sign = sign === 1 ? -1 : 1;
      if (sawNot) return undefined;
      sawNot = true;
    } else if (isNot(t, 'negative')) {
      if (sawNot) return undefined;
      sawNot = true;
    } else {
      return undefined;
    }
  }
  if (sign === 1 && !sawNon && !sawNot) return true;
  return sign < 0 ? false : undefined;
}

function mulOdd(e: Expr): V {
  const isInteger = mulInteger(e);
  if (isInteger !== true) return isInteger;
  const [n, d] = fraction(e);
  if (d instanceof Rational && d.q === 1n && is(d, 'even')) {
    return is(sub(evenExponents(mulArgs(n)), trailing(d.p)), 'positive') ? false : undefined;
  }
  let r: V = true;
  let acc: Expr | undefined;
  for (const t of e.args) {
    if (isAbsOne(t)) continue;
    if (is(t, 'even')) return false;
    if (r === false) {
      // stays false
    } else if (acc !== undefined && is(add(acc, t), 'odd')) {
      r = false;
    } else if (fact(t, 'even') === undefined) {
      r = undefined;
    }
    acc = t;
  }
  return r;
}

function mulEven(e: Expr): V {
  const [n, d] = fraction(e);
  // (SymPy also answers false for a numerator 0, which is even)
  if (n instanceof Rational && n.q === 1n && n.p !== 0n && is(n, 'even') && is(sub(evenExponents(mulArgs(d)), trailing(n.p)), 'nonnegative')) return false;
  return undefined;
}

const MUL: Readonly<Partial<Record<string, Handler>>> = {
  commutative: (e) => group(e.args, 'commutative', false),
  complex: (e) => {
    const comp = group(e.args, 'complex', false);
    if (comp === false && e.args.some((a) => is(a, 'infinite'))) return e.args.some((a) => !isNot(a, 'zero')) ? undefined : false;
    return comp;
  },
  zero: mulZero,
  infinite: (e) => {
    const [z, inf] = zeroInfinite(e);
    if (inf === true && z === false) return true;
    return inf === false ? false : undefined;
  },
  rational: (e) => mulGroup(e, 'rational'),
  algebraic: (e) => mulGroup(e, 'algebraic'),
  integer: mulInteger,
  polar: (e) => e.args.some((a) => is(a, 'polar')) && e.args.every((a) => is(a, 'polar') || is(a, 'positive')),
  extended_real: (e) => realImag(e, true),
  imaginary: (e) => (e.args.every((a) => isNot(a, 'zero') && is(a, 'finite')) ? realImag(e, false) : undefined),
  hermitian: (e) => hermAntiherm(e, true),
  antihermitian: (e) => hermAntiherm(e, false),
  irrational: mulIrrational,
  extended_positive: (e) => mulSign(e, 1),
  extended_negative: (e) => mulSign(e, -1),
  odd: mulOdd,
  even: mulEven,
  composite: (e) => {
    let count = 0;
    for (const a of e.args) {
      if (!(is(a, 'integer') && is(a, 'positive'))) return undefined;
      if (is(sub(a, 1), 'positive')) count++;
    }
    return count > 1 ? true : undefined;
  },
};

// ---------------------------------------------------------------------------
// Pow
// ---------------------------------------------------------------------------

function powExtendedNegative(e: Pow): V {
  const [b, ex] = e.args;
  if (isRat(ex, 1n, 2n) && (is(b, 'complex') || is(b, 'extended_real'))) return false;
  if (is(b, 'extended_negative')) {
    if (is(ex, 'odd') && is(b, 'finite')) return true;
    return is(ex, 'even') ? false : undefined;
  }
  if (is(b, 'extended_positive') || is(b, 'zero')) return is(ex, 'extended_real') ? false : undefined;
  if (is(b, 'extended_nonnegative')) return is(ex, 'extended_nonnegative') ? false : undefined;
  if (is(b, 'extended_nonpositive') || is(b, 'extended_real')) return is(ex, 'even') ? false : undefined;
  return undefined;
}

function powExtendedPositive(e: Pow): V {
  const [b, ex] = e.args;
  if (b.key === ex.key) return is(b, 'extended_nonnegative') ? true : undefined;
  if (is(b, 'positive')) return is(ex, 'real') ? true : undefined;
  if (is(b, 'extended_negative')) {
    if (is(ex, 'even')) return true;
    return is(ex, 'odd') ? false : undefined;
  }
  if (is(b, 'zero')) return is(ex, 'extended_real') ? fact(ex, 'zero') : undefined;
  if (is(b, 'extended_nonpositive')) return is(ex, 'odd') ? false : undefined;
  if (is(b, 'imaginary')) {
    if (is(ex, 'integer') && ex instanceof Rational) return ((ex.p % 4n) + 4n) % 4n === 0n;
    if (is(ex, 'imaginary')) return logImaginary(b);
  }
  return undefined;
}

function powZero(e: Pow): V {
  const [b, ex] = e.args;
  const bz = fact(b, 'zero');
  if (bz === true) {
    if (is(ex, 'extended_positive')) return true;
    return is(ex, 'extended_nonpositive') ? false : undefined;
  }
  if (bz === false) {
    if (is(b, 'finite') && is(ex, 'finite')) return false;
    if (is(ex, 'negative')) return fact(b, 'infinite');
    if (is(ex, 'nonnegative')) return false;
    if (is(ex, 'infinite') && is(ex, 'extended_real')) {
      const d = sub(1, impl.abs(b));
      if (is(d, 'extended_positive')) return fact(ex, 'extended_positive');
      if (is(d, 'extended_negative')) return fact(ex, 'extended_negative');
    }
    return undefined;
  }
  return is(b, 'finite') && is(ex, 'negative') ? false : undefined;
}

function powInteger(e: Pow): V {
  const [b, ex] = e.args;
  if (is(b, 'rational') && isNot(b, 'integer') && is(ex, 'positive')) return false;
  if (is(b, 'integer') && is(ex, 'integer')) {
    if (isRat(b, -1n)) return true;
    if (is(ex, 'nonnegative') || is(ex, 'positive')) return true;
  }
  // (SymPy also asks that e be finite or an integer, which a negative e is)
  if (is(b, 'integer') && is(ex, 'negative')) {
    if (isNot(sub(b, 1), 'zero') && isNot(add(b, 1), 'zero')) return false;
  }
  const isNumberClass = (x: Expr): boolean => x instanceof Rational || x instanceof Float || (x instanceof Special && x.name !== 'zoo');
  if (isNumberClass(b) && isNumberClass(ex)) {
    const check = pow(b, ex);
    return check instanceof Rational && check.q === 1n;
  }
  if (is(ex, 'negative') && is(b, 'positive') && is(sub(b, 1), 'positive')) return false;
  if (is(ex, 'negative') && is(b, 'negative') && is(add(b, 1), 'negative')) return false;
  return undefined;
}

function powExtendedReal(e: Pow): V {
  const [b, ex] = e.args;
  const realB = fact(b, 'extended_real');
  if (realB === undefined) return b instanceof Pow && isExp(b) && is(b.exp, 'imaginary') ? fact(ex, 'imaginary') : undefined;
  const realE = fact(ex, 'extended_real');
  if (realE === undefined) return undefined;
  if (realB && realE) {
    if (is(b, 'extended_positive')) return true;
    if (is(b, 'extended_nonnegative') && is(ex, 'extended_nonnegative')) return true;
    if (is(ex, 'integer') && is(b, 'extended_nonzero')) return true;
    if (is(ex, 'integer') && is(ex, 'nonnegative')) return true;
    if (is(b, 'extended_negative') && ex instanceof Rational) return false;
  }
  if (realE && is(ex, 'extended_negative') && isNot(b, 'zero')) return fact(pow(b, neg(ex)), 'extended_real');
  const imE = fact(ex, 'imaginary');
  if (is(b, 'imaginary')) {
    if (is(ex, 'integer')) {
      if (is(ex, 'even')) return true;
      if (is(ex, 'odd')) return false;
    } else if (imE === true && logImaginary(b) === true) {
      return true;
    } else if (ex instanceof Add) {
      const [c, a] = coeffAdd(ex);
      if (c instanceof Rational && c.q === 1n && c.p !== 0n) return fact(new Mul([pow(b, c), pow(b, a)]), 'extended_real');
    } else if (isI(b) || isI(neg(b))) {
      if (isNot(mul(ex, Rational.of(1, 2)), 'integer')) return false;
    }
  }
  if (realB && imE === true) {
    if (isRat(b, -1n)) return true;
    const c = coeff(ex, S.I);
    if (!isZeroValue(c)) {
      if (is(b, 'rational') && is(c, 'rational') && is(b, 'nonzero') && is(sub(b, 1), 'nonzero') && is(c, 'nonzero')) return false;
      const l = fn('log', b);
      const ok = l && fact(mul(c, l, pow(S.Pi, -1)), 'integer');
      if (ok !== undefined) return ok;
    }
  }
  if (!realB && realE) {
    if (ex instanceof Rational && ex.p === 1n) return false;
    const ar = fn('arg', b);
    const i = ar && mul(ar, ex, pow(S.Pi, -1));
    if (i && is(i, 'complex')) return fact(i, 'integer');
  }
  return undefined;
}

function powFinite(e: Pow): V {
  const [b, ex] = e.args;
  if (is(ex, 'negative')) {
    if (is(b, 'zero')) return false;
    if (is(b, 'infinite') || is(b, 'nonzero')) return true;
  }
  const c1 = fact(b, 'finite');
  if (c1 === undefined) return undefined;
  const c2 = fact(ex, 'finite');
  if (c2 === undefined) return undefined;
  return c1 && c2 && (is(ex, 'nonnegative') || isNot(b, 'zero')) ? true : undefined;
}

function powImaginary(e: Pow): V {
  const [b, ex] = e.args;
  if (!b.isCommutative) return false;
  if (is(b, 'imaginary') && is(ex, 'integer')) return fact(ex, 'odd');
  if (is(ex, 'imaginary') && logImaginary(b) !== undefined) return false;
  if (is(b, 'extended_real') && is(ex, 'extended_real')) {
    if (is(b, 'positive')) return false;
    const rat = fact(ex, 'rational');
    if (rat !== true) return rat;
    if (is(ex, 'integer')) return false;
    const half = fact(mul(2, ex), 'integer');
    return half === true ? fact(b, 'negative') : half;
  }
  if (isNot(b, 'extended_real')) {
    const ar = fn('arg', b);
    return ar && fact(mul(2, ar, ex, pow(S.Pi, -1)), 'odd');
  }
  return undefined;
}

function powRational(e: Pow): V {
  const [b, ex] = e.args;
  // (b**e with e < 0 is not rational only for b = 0)
  if (is(ex, 'integer') && is(b, 'rational') && (isNot(ex, 'negative') || isNot(b, 'zero'))) return true;
  // (an unevaluated power is decided by its value)
  const value = pow(b, ex);
  if (!(value instanceof Pow)) return fact(value, 'rational');
  if (ex instanceof Rational && b instanceof Rational) return false;
  if (is(ex, 'integer')) {
    if (is(b, 'rational')) {
      if (isNot(b, 'zero') || is(ex, 'nonnegative') || b.key === ex.key) return true;
    } else if (is(b, 'irrational')) {
      return fact(ex, 'zero');
    }
  }
  return undefined;
}

function powAlgebraic(e: Pow): V {
  const [b, ex] = e.args;
  const isOne = (x: Expr): V => fact(sub(x, 1), 'zero');
  // (SymPy gives True for every power of 0; 0**e is complex infinity for e < 0)
  if (is(b, 'zero')) return is(ex, 'nonnegative') ? true : isNot(ex, 'nonnegative') && is(ex, 'extended_real') ? false : undefined;
  if (isOne(b) === true) return true;
  if (is(ex, 'rational')) {
    if (isNot(b, 'algebraic')) return fact(ex, 'zero');
    if (isNot(b, 'zero')) {
      if (is(ex, 'nonzero')) return fact(b, 'algebraic');
      if (is(b, 'algebraic')) return true;
    }
    return is(ex, 'positive') ? fact(b, 'algebraic') : undefined;
  }
  if (is(b, 'algebraic') && is(ex, 'algebraic')) {
    if ((isNot(b, 'zero') && isOne(b) === false) || isNot(b, 'integer') || is(b, 'irrational')) return fact(ex, 'rational');
  }
  return undefined;
}

type PowHandler = (e: Pow) => V;

const POW: Readonly<Partial<Record<string, PowHandler>>> = {
  even: (e) => (is(e.exp, 'integer') && is(e.exp, 'positive') ? fact(e.base, 'even') : undefined),
  negative: (e) => {
    const n = powExtendedNegative(e);
    return n === true ? fact(e, 'finite') : n;
  },
  extended_positive: powExtendedPositive,
  extended_negative: powExtendedNegative,
  zero: powZero,
  integer: powInteger,
  extended_real: powExtendedReal,
  complex: (e) => (e.args.every((a) => is(a, 'complex')) && powFinite(e) === true ? true : undefined),
  imaginary: powImaginary,
  odd: (e) => {
    const [b, ex] = e.args;
    if (!is(ex, 'integer')) return undefined;
    if (is(ex, 'positive')) return fact(b, 'odd');
    return (is(ex, 'nonnegative') && is(b, 'odd')) || isRat(b, -1n) ? true : undefined;
  },
  finite: powFinite,
  prime: (e) => (is(e.base, 'integer') && is(e.exp, 'integer') && is(sub(e.exp, 1), 'positive') ? false : undefined),
  composite: (e) => {
    const [b, ex] = e.args;
    if (!(is(b, 'integer') && is(ex, 'integer'))) return undefined;
    const big = is(sub(b, 1), 'positive') && is(sub(ex, 1), 'positive');
    const evenNegative = is(add(b, 1), 'negative') && is(ex, 'positive') && is(ex, 'even');
    return big || evenNegative ? true : undefined;
  },
  polar: (e) => fact(e.base, 'polar'),
  rational: powRational,
  algebraic: powAlgebraic,
};

interface FunctionFacts {
  /** The facts of the class (SymPy class attributes such as is_extended_real = True). */
  readonly given?: Readonly<Record<string, boolean>>;
  readonly handlers: Readonly<Partial<Record<string, Handler>>>;
}

/** A handler of the first argument. */
const on = (f: (a: Expr) => V): Handler => (e) => f(at(e.args, 0));
/** The fact of the first argument when it is extended real (SymPy Abs). */
const ofReal = (k: string): Handler => on((a) => (is(a, 'extended_real') ? fact(a, k) : undefined));
const ifFinite = on((a) => (is(a, 'finite') ? true : undefined));

/**
 * SymPy _peeloff_pi: arg as rest + k*pi with k a multiple of 1/2 taken from its rational
 * multiples of pi, as [rest, k] ([arg, 0] when it has none).
 */
function peeloffPi(arg: Expr): [Expr, Rational] {
  let piCoeff = Rational.of(0);
  const rest: Expr[] = [];
  for (const a of arg instanceof Add ? arg.args : [arg]) {
    const k = coeff(a, S.Pi);
    if (k instanceof Rational && !k.isZero) piCoeff = Rational.of(piCoeff.p * k.q + k.p * piCoeff.q, piCoeff.q * k.q);
    else rest.push(a);
  }
  if (piCoeff.isZero) return [arg, piCoeff];
  // m2 = the largest multiple of 1/2 not above the coefficient
  const twice = 2n * piCoeff.p;
  const floorHalf = twice >= 0n ? twice / piCoeff.q : -((-twice + piCoeff.q - 1n) / piCoeff.q);
  const m2 = Rational.of(floorHalf, 2);
  return [add(...rest, mul(sub(piCoeff, m2), S.Pi)), m2];
}

/** tan and cot: real, finite and complex for a real argument away from the poles (arg/pi - shift not an integer). */
const awayFromPoles = (shift: Expr): Handler => on((a) => (is(a, 'real') && isNot(sub(mul(a, pow(S.Pi, -1)), shift), 'integer') ? true : undefined));
const trigFinite = (shift: Expr): Handler => {
  const away = awayFromPoles(shift);
  return (e) => away(e) ?? (is(at(e.args, 0), 'imaginary') ? true : undefined);
};

/** SymPy TrigonometricFunction._eval_is_algebraic and _eval_is_rational. */
const trigAlgebraic = on((a) => {
  if (isNot(a, 'zero') && is(a, 'algebraic')) return false;
  return mul(a, pow(S.Pi, -1)) instanceof Rational ? true : undefined;
});
const trigRational = on((a) => (is(a, 'rational') && isNot(a, 'zero') ? false : undefined));

const ifExtendedReal = on((a) => (is(a, 'extended_real') ? true : undefined));
const extendedReal = on((a) => fact(a, 'extended_real'));
const allReal: Handler = (e) => (e.args.every((a) => is(a, 'real')) ? true : undefined);
const besselReal = (argumentFact: string): FunctionFacts => ({
  handlers: { extended_real: (e) => (is(at(e.args, 0), 'integer') && is(at(e.args, 1), argumentFact) ? true : undefined) },
});
const airyFacts: FunctionFacts = { handlers: { extended_real: extendedReal } };
const fresnelFacts: FunctionFacts = { handlers: { extended_real: extendedReal, finite: extendedReal } };
const tensorFacts: FunctionFacts = { given: { integer: true }, handlers: {} };

const gammaReal: Handler = on((z) => {
  if (is(z, 'nonpositive') && is(z, 'integer')) return false;
  if (z instanceof Float && z.toNumber() <= 0 && Number.isInteger(z.toNumber())) return false;
  if (is(z, 'positive') || is(z, 'noninteger')) return true;
  return undefined;
});
const polygammaSign = (positive: boolean): Handler => (e) => {
  const n = at(e.args, 0), z = at(e.args, 1);
  if (is(n, 'positive')) {
    if (is(n, 'odd') && is(z, 'real')) return positive;
    if (is(n, 'even') && is(z, 'positive')) return !positive;
    return numberSign(e, positive ? 1 : -1);
  }
  return undefined;
};

/** SymPy handlers of Abs, re, im, sign, floor, ceiling, frac, tan, cot, exp_polar and Mod. */
const FUNCTIONS: Readonly<Partial<Record<string, FunctionFacts>>> = {
  besselj: besselReal('extended_real'),
  besseli: besselReal('extended_real'),
  bessely: besselReal('positive'),
  besselk: besselReal('positive'),
  airyai: airyFacts,
  airybi: airyFacts,
  airyaiprime: airyFacts,
  airybiprime: airyFacts,
  LeviCivita: tensorFacts,
  KroneckerDelta: tensorFacts,
  erf: { handlers: {
    real: ifExtendedReal,
    imaginary: on((a) => (is(a, 'imaginary') ? true : undefined)),
    finite: on((a) => fuzzyOr([() => fact(a, 'finite'), () => fact(a, 'extended_real')])),
    zero: ofReal('zero'),
    positive: ofReal('extended_positive'),
    negative: ofReal('extended_negative'),
  } },
  erfc: { handlers: { real: on((a) => (is(a, 'extended_real') ? true : is(a, 'imaginary') ? false : undefined)) } },
  erf2: { handlers: { extended_real: (e) => fact(at(e.args, 0), 'extended_real') && fact(at(e.args, 1), 'extended_real') } },
  fresnels: fresnelFacts,
  fresnelc: fresnelFacts,
  beta: { handlers: { real: (e) => fact(at(e.args, 0), 'real') && fact(at(e.args, 1), 'real') } },
  betainc: { handlers: { real: allReal } },
  betainc_regularized: { handlers: { real: allReal } },
  gamma: { handlers: { real: gammaReal, positive: on((z) => {
    if (is(z, 'positive')) return true;
    if (z instanceof Add) {
      const numeric = z.args.find((term) => term instanceof Rational && !term.isInteger);
      if (numeric instanceof Rational) {
        const integerPart = add(...z.args.filter((term) => term !== numeric));
        if (is(integerPart, 'integer')) {
          const floor = numeric.p / numeric.q - (numeric.isNegative ? 1n : 0n);
          return fact(add(integerPart, Rational.of(floor)), 'even');
        }
      }
    }
    if (is(z, 'noninteger')) {
      const floored = impl.fn?.('floor', [z]);
      return floored === undefined ? undefined : fact(floored, 'even');
    }
    return undefined;
  }) } },
  loggamma: { handlers: { real: on((z) => (is(z, 'positive') ? true : is(z, 'nonpositive') ? false : undefined)) } },
  polygamma: { handlers: {
    real: (e) => (e.args.every((a) => is(a, 'positive')) ? true : undefined),
    positive: polygammaSign(true),
    negative: polygammaSign(false),
  } },
  multigamma: { handlers: { real: (e) => {
    const twice = mul(2, at(e.args, 0));
    const difference = add(twice, neg(at(e.args, 1)), 1);
    if (is(difference, 'positive') || is(twice, 'noninteger') && !(twice instanceof Float && Number.isInteger(twice.toNumber()))) return true;
    if (is(difference, 'nonpositive') && (is(twice, 'integer') || twice instanceof Float && Number.isInteger(twice.toNumber()))) return false;
    return undefined;
  } } },
  zeta: { handlers: { finite: on((s) => fuzzyNot(fact(add(s, -1), 'zero'))) } },
  abs: {
    given: { extended_real: true, extended_negative: false, extended_nonnegative: true },
    handlers: {
      real: ifFinite,
      integer: ofReal('integer'),
      extended_nonzero: on((a) => fuzzyNot(fact(a, 'zero'))),
      zero: on((a) => fact(a, 'zero')),
      extended_positive: on((a) => fuzzyNot(fact(a, 'zero'))),
      rational: ofReal('rational'),
      even: ofReal('even'),
      odd: ofReal('odd'),
      algebraic: on((a) => fact(a, 'algebraic')),
    },
  },
  re: {
    given: { extended_real: true },
    handlers: {
      algebraic: on((a) => fact(a, 'algebraic')),
      zero: on((a) => fuzzyOr([() => fact(a, 'imaginary'), () => fact(a, 'zero')])),
      finite: ifFinite,
      complex: ifFinite,
    },
  },
  im: {
    given: { extended_real: true },
    handlers: { algebraic: on((a) => fact(a, 'algebraic')), zero: on((a) => fact(a, 'extended_real')), finite: ifFinite, complex: ifFinite },
  },
  sign: {
    given: { complex: true },
    handlers: {
      nonnegative: on((a) => (is(a, 'nonnegative') ? true : undefined)),
      nonpositive: on((a) => (is(a, 'nonpositive') ? true : undefined)),
      imaginary: on((a) => fact(a, 'imaginary')),
      integer: on((a) => fact(a, 'extended_real')),
      zero: on((a) => fact(a, 'zero')),
    },
  },
  floor: {
    handlers: {
      finite: on((a) => fact(a, 'finite')),
      real: on((a) => fact(a, 'real')),
      integer: on((a) => fact(a, 'real')),
      negative: on((a) => fact(a, 'negative')),
      nonnegative: on((a) => fact(a, 'nonnegative')),
    },
  },
  ceiling: {
    handlers: {
      finite: on((a) => fact(a, 'finite')),
      real: on((a) => fact(a, 'real')),
      integer: on((a) => fact(a, 'real')),
      positive: on((a) => fact(a, 'positive')),
      nonpositive: on((a) => fact(a, 'nonpositive')),
    },
  },
  frac: {
    handlers: {
      finite: () => true,
      real: on((a) => fact(a, 'extended_real')),
      imaginary: on((a) => fact(a, 'imaginary')),
      integer: on((a) => fact(a, 'integer')),
      zero: on((a) => fuzzyOr([() => fact(a, 'zero'), () => fact(a, 'integer')])),
      negative: () => false,
    },
  },
  tan: {
    handlers: {
      extended_real: on((a) => fact(a, 'extended_real')),
      real: awayFromPoles(Rational.of(1, 2)),
      finite: trigFinite(Rational.of(1, 2)),
      complex: awayFromPoles(Rational.of(1, 2)),
      algebraic: trigAlgebraic,
      rational: trigRational,
      zero: on((a) => {
        const [rest, k] = peeloffPi(a);
        return is(rest, 'zero') ? k.q === 1n : undefined;
      }),
    },
  },
  cot: {
    handlers: {
      extended_real: on((a) => fact(a, 'extended_real')),
      real: awayFromPoles(S.Zero),
      finite: trigFinite(S.Zero),
      complex: awayFromPoles(S.Zero),
      algebraic: trigAlgebraic,
      rational: trigRational,
      zero: on((a) => {
        const [rest, k] = peeloffPi(a);
        return !k.isZero && is(rest, 'zero') ? k.q !== 1n : undefined;
      }),
    },
  },
  exp_polar: {
    given: { polar: true },
    handlers: {
      extended_real: on((a) => (is(a, 'extended_real') ? true : undefined)),
      finite: on(expFinite),
      zero: on((a) => a instanceof Special && a.name === '-oo'),
    },
  },
  Mod: {
    handlers: {
      integer: (e) => {
        const [p, q] = e.args;
        return p !== undefined && q !== undefined && is(p, 'integer') && is(q, 'integer') && isNot(q, 'zero') ? true : undefined;
      },
      nonnegative: (e) => (is(at(e.args, 1), 'positive') ? true : undefined),
      nonpositive: (e) => (is(at(e.args, 1), 'negative') ? true : undefined),
    },
  },
};

/** SymPy ExpBase._eval_is_finite of exp(x). */
function expFinite(x: Expr): V {
  if (is(x, 'infinite')) {
    if (is(x, 'extended_negative')) return true;
    if (is(x, 'extended_positive')) return false;
  }
  return is(x, 'finite') ? true : undefined;
}

/** SymPy exp and ExpBase handlers for exp(x) (Pow(E, x) here). */
const EXP: Readonly<Partial<Record<string, PowHandler>>> = {
  finite: ({ exp: x }) => expFinite(x),
  rational: ({ exp: x }) => {
    const z = fact(x, 'zero');
    if (z === true) return true;
    return is(x, 'rational') && z === false ? false : undefined;
  },
  zero: ({ exp: x }) => x instanceof Special && x.name === '-oo',
  extended_real: ({ exp: x }) => {
    if (is(x, 'extended_real')) return true;
    return is(x, 'imaginary') ? fact(mul(-2, S.I, x, pow(S.Pi, -1)), 'even') : undefined;
  },
  complex: ({ exp: x }) => fuzzyOr([() => fact(x, 'complex'), () => fact(x, 'extended_negative')]),
  algebraic: ({ exp: x }) => {
    if (is(mul(x, pow(S.Pi, -1), pow(S.I, -1)), 'rational')) return true;
    if (isNot(x, 'zero')) {
      if (is(x, 'algebraic')) return false;
      if (is(mul(x, pow(S.Pi, -1)), 'rational')) return false;
    }
    return undefined;
  },
  extended_positive: ({ exp: x }) => {
    if (is(x, 'extended_real')) return !(x instanceof Special && x.name === '-oo');
    return is(x, 'imaginary') ? fact(mul(-1, S.I, x, pow(S.Pi, -1)), 'even') : undefined;
  },
  extended_negative: (e) => numberSign(e, -1),
};
