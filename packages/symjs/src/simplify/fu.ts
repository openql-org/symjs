// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/simplify/fu.py (BSD 3-Clause, Copyright (c) SymPy Development Team).

/**
 * @file The Fu et al. trigonometric simplification (SymPy fu.py): the
 * transformation rules TR0-TR22, TRmorrie, TRpower, the rule lists of the
 * algorithm and `fu` itself, together with the helpers trig_split,
 * as_f_sign_1 and hyper_as_trig (the Osborne rule).
 *
 * Reference: Fu, Hongguang, Xiuqin Zhong and Zhenbing Zeng, "Automated and
 * readable simplification of trigonometric expressions", Mathematical and
 * Computer Modelling 44 (2006) 1169-1177.
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, BoolAtom, Derivative, Dummy, Float, Fn, Mul, Pow, Rational, Rel, S, isNum } from '../core/nodes';
import { BoolOp } from '../core/boolalg';
import { add, asBaseExp, mul, neg, pow, sqrt, sub, sympify } from '../core/ops';
import { count, countOps, ordered } from '../core/match';
import { asIndependent, asNumerDenom, asPowersDict, extractAdditively } from '../core/methods';
import { ExprMap } from '../core/exprmap';
import { Factors } from '../core/factors';
import { isIntegerQ, isNegative, isPositive, isReal } from '../core/assumptions';
import { rebuild, some, xreplace } from '../core/traverse';
import { fn } from '../functions/elementary/elementary';
import { perfectPower } from '../ntheory/factor';
import { factor } from '../polys/sympoly';
import { expand } from './expand';
import { factorTerms, gcdTerms, signsimp } from './exprtools';
import { collect } from './radsimp';
import { fraction } from './rational';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, cast, defined, first, getOrThrow, last, pair } from '../core/guard';

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

type TrigName = 'sin' | 'cos' | 'tan' | 'cot' | 'sec' | 'csc';
type HyperName = 'sinh' | 'cosh' | 'tanh' | 'coth' | 'sech' | 'csch';
const TRIG: ReadonlySet<string> = new Set<TrigName>(['sin', 'cos', 'tan', 'cot', 'sec', 'csc']);
const HYPER: ReadonlySet<string> = new Set<HyperName>(['sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);

/** An instance of one of the named functions (SymPy isinstance(e, (f, g, ...))). */
export const isF = (e: Expr, ...names: readonly FnName[]): e is Fn => e instanceof Fn && names.includes(e.name);
/** SymPy isinstance(e, TrigonometricFunction). */
export const isTrigFunction = (e: Expr): e is Fn => e instanceof Fn && TRIG.has(e.name);
/** SymPy isinstance(e, HyperbolicFunction). */
export const isHyperFunction = (e: Expr): e is Fn => e instanceof Fn && HYPER.has(e.name);
/** SymPy e.has(f, g, ...) for function classes. */
export const hasF = (e: Expr, ...names: readonly FnName[]): boolean => some(e, (x) => isF(x, ...names));
/** SymPy e.has(TrigonometricFunction). */
export const hasTrigFunction = (e: Expr): boolean => some(e, isTrigFunction);
/** SymPy e.has(HyperbolicFunction). */
export const hasHyperFunction = (e: Expr): boolean => some(e, isHyperFunction);

const arg0 = (e: Fn): Expr => first(e.args);
const F = (name: FnName, a: ExprLike): Expr => fn(name, [a]);
/** f(a, evaluate=False). */
const rawF = (name: FnName, a: Expr): Expr => new Fn(name, [a]);
const eq = (a: Expr, b: Expr): boolean => a.key === b.key;
const isOne = (e: Expr): boolean => e instanceof Rational && e.isOne;
const isNegOne = (e: Expr): boolean => e instanceof Rational && e.p === -1n && e.q === 1n;
const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isIntegerAtom = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;
/** SymPy is_Pow (exp(x) is not a Pow in SymPy). */
const isPowNode = (e: Expr): e is Pow => e instanceof Pow && !eq(e.base, S.E);
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const isTrue = (t: boolean | undefined): boolean => t === true;

/** SymPy as_coeff_Mul(rational=...). */
export function asCoeffMul(e: Expr, rational = false): [Expr, Expr] {
  const isCoeff = (c: Expr): boolean => c instanceof Rational || (!rational && c instanceof Float);
  if (e instanceof Mul && isCoeff(first(e.args))) return [first(e.args), mul(...e.args.slice(1))];
  if (isCoeff(e)) return [e, S.One];
  return [S.One, e];
}

/** SymPy bottom_up: F applied to every non-atomic node, children first. */
export function bottomUp(e: Expr, f: (e: Expr) => Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map((a) => bottomUp(a, f));
  const changed = args.some((a, i) => a.key !== at(e.args, i).key);
  return f(changed ? rebuild(e, args) : e);
}

/** A sign test with a numeric fallback for closed numbers (SymPy is_positive). */
export function positive(e: Expr): boolean | undefined {
  const p = isPositive(e);
  if (p !== undefined) return p;
  if (e.freeSymbols().size > 0) return undefined;
  try {
    const v = e.toComplex();
    if (Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re))) return false;
    return Math.abs(v.re) < 1e-12 ? undefined : v.re > 0;
  } catch {
    return undefined;
  }
}

/** SymPy's Mul._eval_expand_mul applied deeply to a fixed point (expand_mul: no multinomial expansion). */
export function expandMulOnly(eIn: ExprLike): Expr {
  const node = (e: Mul): Expr => {
    let [n, d] = fraction(e);
    if (d instanceof Mul) {
      n = n instanceof Mul ? node(n) : n;
      d = node(d);
    }
    const ex = mul(n, pow(d, -1));
    if (!(ex instanceof Mul) || !ex.args.some((a) => a instanceof Add)) return ex;
    // the sums are multiplied out in order; non-commutative factors keep their place
    const plain: Expr[] = [];
    let terms: Expr[][] = [[]];
    for (const a of ex.args) {
      if (a instanceof Add) terms = terms.flatMap((t) => a.args.map((u) => [...t, u]));
      else if (a.isCommutative) plain.push(a);
      else terms = terms.map((t) => [...t, a]);
    }
    return add(...terms.map((t) => mul(...plain, ...t)));
  };
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const args = e.args.map(go);
    const r = args.some((a, i) => a !== at(e.args, i)) ? rebuild(e, args) : e;
    return r instanceof Mul ? node(r) : r;
  };
  let cur = sympify(eIn);
  for (;;) {
    const next = go(cur);
    if (eq(next, cur)) return next;
    cur = next;
  }
}

/** SymPy _mexpand: expand_mul(expand_multinomial(e)) to a fixed point. */
export function mexpand(eIn: ExprLike): Expr {
  let cur = sympify(eIn);
  for (;;) {
    const next = expandMulOnly(expand(cur, { mul: false, power_exp: false, power_base: false, log: false }));
    if (eq(next, cur)) return next;
    cur = next;
  }
}

/** SymPy Expr.normal(). */
export function normal(e: Expr): Expr {
  const [n, d] = asNumerDenom(e);
  return isOne(d) ? n : mul(n, pow(d, -1));
}

/** SymPy L: the number of trigonometric functions. */
export function L(rv: ExprLike): Expr {
  return Rational.of(count(sympify(rv), isTrigFunction));
}

/**
 * SymPy Factors(e): a negative numeric coefficient is split into -1 and
 * its absolute value (SymPy args_cnc splits it).
 */
function factorsOf(e: Expr): Factors {
  const f = new Factors(e);
  const negs = [...f.factors.keys()].filter((k) => k instanceof Rational && k.isNegative && !isNegOne(k));
  if (negs.length === 0) return f;
  const m = new ExprMap(f.factors);
  for (const k of negs) {
    const x = getOrThrow(m, k);
    m.delete(k);
    m.set(neg(k), add(m.get(neg(k)) ?? S.Zero, x));
    m.set(S.NegOne, add(m.get(S.NegOne) ?? S.Zero, x));
  }
  return new Factors(m);
}

/** Factors.normal(other): self and other with the common factors removed. */
function factorsNormal(self: Factors, other: Factors): [Factors, Factors] {
  const sf = new ExprMap(self.factors);
  const of = new ExprMap(other.factors);
  for (const [factorE, selfExp] of self.factors) {
    const otherExp0 = other.factors.get(factorE);
    if (otherExp0 === undefined) continue;
    const ex = sub(selfExp, otherExp0);
    if (isZero(ex)) {
      sf.delete(factorE);
      of.delete(factorE);
    } else if (isNum(ex)) {
      if (ex.isPositive) {
        sf.set(factorE, ex);
        of.delete(factorE);
      } else {
        sf.delete(factorE);
        of.set(factorE, neg(ex));
      }
    } else {
      const r = extractAdditively(selfExp, otherExp0);
      if (r !== undefined) {
        // r = selfExp - otherExp is not a number here, so it is not zero
        sf.set(factorE, r);
        of.delete(factorE);
      } else {
        let otherExp = otherExp0;
        const [sc, sa] = coeffAdd(selfExp);
        if (!isZero(sc)) {
          const [oc, oa] = coeffAdd(otherExp);
          const diff = sub(sc, oc);
          if (isTrue(isPositive(diff))) {
            sf.set(factorE, sub(getOrThrow(sf, factorE), oc));
            otherExp = oa;
          } else if (isTrue(isNegative(diff))) {
            sf.set(factorE, sub(getOrThrow(sf, factorE), sc));
            otherExp = sub(oa, diff);
          } else {
            sf.set(factorE, sa);
            otherExp = oa;
          }
        }
        // (otherExp is not zero: a numeric exponent of other is extracted by extract_additively above)
        of.set(factorE, otherExp);
      }
    }
  }
  return [new Factors(sf), new Factors(of)];
}

/** SymPy as_coeff_Add. */
function coeffAdd(e: Expr): [Expr, Expr] {
  if (isNum(e)) return [e, S.Zero];
  if (e instanceof Add && isNum(first(e.args))) return [first(e.args), add(...e.args.slice(1))];
  return [S.Zero, e];
}

/** Factors.gcd(other). */
function factorsGcd(self: Factors, other: Factors): Factors {
  const out = new ExprMap<Expr>();
  for (const [factorE, ex] of self.factors) {
    const o = other.factors.get(factorE);
    if (o === undefined) continue;
    const lt = isNegative(sub(ex, o));
    if (lt === true) out.set(factorE, ex);
    else if (lt === false) out.set(factorE, o);
  }
  return new Factors(out);
}

/** SymPy min(seq, key): the first element with the smallest key. */
function minBy<T>(xs: readonly T[], key: (x: T) => Measured): T {
  let best = first(xs);
  let bk = key(best);
  for (const x of xs.slice(1)) {
    const k = key(x);
    if (compareMeasured(k, bk) < 0) {
      best = x;
      bk = k;
    }
  }
  return best;
}

/** A value of an objective: a number or a tuple of numbers compared lexicographically. */
export type Measured = number | readonly number[];

/** Lexicographic comparison of objective values. */
export function compareMeasured(a: Measured, b: Measured): number {
  const xs = typeof a === 'number' ? [a] : a;
  const ys = typeof b === 'number' ? [b] : b;
  const n = Math.min(xs.length, ys.length);
  for (let i = 0; i < n; i++) {
    const d = at(xs, i) - at(ys, i);
    if (d !== 0) return d;
  }
  return xs.length - ys.length;
}

/** A rule: an expression transformation. */
export type Rule = (e: Expr) => Expr;
/** A strategy tree of SymPy strategies.tree: a rule, a chain (tuple) or a choice (list). */
export type Tree = Rule | { readonly chain: readonly Tree[] } | { readonly choice: readonly Tree[] };
/** A tuple of SymPy's trees: the rules applied in sequence. */
export const chain = (...ts: Tree[]): Tree => ({ chain: ts });
/** A list of SymPy's trees: the result with the smallest objective. */
export const choice = (...ts: Tree[]): Tree => ({ choice: ts });
/** SymPy identity. */
export const identity: Rule = (e) => e;

/** SymPy strategies.tree.greedy. */
export function greedy(tree: Tree, objective: (e: Expr) => Measured): Rule {
  if (typeof tree === 'function') return tree;
  if ('chain' in tree) {
    const rules = tree.chain.map((t) => greedy(t, objective));
    return (e) => rules.reduce((x, r) => r(x), e);
  }
  const rules = tree.choice.map((t) => greedy(t, objective));
  return (e) => minBy(rules.map((r) => r(e)), objective);
}

// ---------------------------------------------------------------------------
// the transformation rules
// ---------------------------------------------------------------------------

/** TR0: simplification of rational polynomials (normal, factor, expand). */
export function TR0(rv: ExprLike): Expr {
  return expand(factor(normal(sympify(rv))));
}

/** TR1: sec -> 1/cos, csc -> 1/sin. */
export function TR1(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (isF(e, 'sec')) return pow(F('cos', arg0(e)), -1);
    if (isF(e, 'csc')) return pow(F('sin', arg0(e)), -1);
    return e;
  });
}

/** TR2: tan -> sin/cos, cot -> cos/sin. */
export function TR2(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (isF(e, 'tan')) return mul(F('sin', arg0(e)), pow(F('cos', arg0(e)), -1));
    if (isF(e, 'cot')) return mul(F('cos', arg0(e)), pow(F('sin', arg0(e)), -1));
    return e;
  });
}

/** TR2i: sin/cos -> tan (and, with half, sin/(1 + cos) -> tan of the half angle). */
export function TR2i(rv: ExprLike, half = false): Expr {
  const ok = (k: Expr, e: Expr): boolean =>
    (isTrue(isIntegerQ(e)) || isTrue(positive(k))) &&
    (isF(k, 'sin', 'cos') || (half && k instanceof Add && k.args.length >= 2 && k.args.some((a) => mulArgs(a).some((ai) => isF(ai, 'cos')))));
  const f = (rv0: Expr): Expr => {
    if (!(rv0 instanceof Mul)) return rv0;
    const [n0, d0] = asNumerDenom(rv0);
    if (n0.args.length === 0 || d0.args.length === 0) return rv0;
    const n = asPowersDict(n0);
    const ndone: [Expr, Expr][] = [];
    for (const [k, v] of [...n]) {
      if (!ok(k, v)) {
        ndone.push([k, v]);
        n.delete(k);
      }
    }
    if (n.size === 0) return rv0;
    const d = asPowersDict(d0);
    const ddone: [Expr, Expr][] = [];
    for (const [k, v] of [...d]) {
      if (!ok(k, v)) {
        ddone.push([k, v]);
        d.delete(k);
      }
    }
    if (d.size === 0) return rv0;
    const factorize = (dd: ExprMap<Expr>, done: [Expr, Expr][]): void => {
      const newk: [Expr, Expr][] = [];
      for (const k of dd.keys()) {
        if (k instanceof Add && k.args.length > 1) {
          // (a sum is kept in the dict only with half, so SymPy's factor_terms branch is never taken)
          const knew = factor(k);
          if (!eq(knew, k)) newk.push([k, knew]);
        }
      }
      if (newk.length === 0) return;
      for (const [k] of newk) dd.delete(k);
      // (SymPy Mul(*newk).as_powers_dict(): the factors of the factored sums, kept as factored)
      const pd = new ExprMap<Expr>();
      for (const [, kn] of newk) for (const [k, e] of asPowersDict(kn)) pd.set(k, add(pd.get(k) ?? S.Zero, e));
      for (const [k, e] of pd) {
        const v = add(dd.get(k) ?? S.Zero, e);
        if (ok(k, v)) dd.set(k, v);
        else {
          dd.set(k, dd.get(k) ?? S.Zero);
          done.push([k, v]);
        }
      }
    };
    factorize(n, ndone);
    factorize(d, ddone);
    const t: Expr[] = [];
    const used = new Set<string>();
    // (each key of d belongs to one key of n: cos(x) and 1 + cos(x) to sin(x), sin(x) to cos(x) or 1 + cos(x))
    const dget = (a: Expr): Expr | undefined => d.get(a);
    for (const [k, nk] of n) {
      const take = (dk: Expr, r: Expr): void => {
        t.push(r);
        used.add(`n${k.key}`).add(`d${dk.key}`);
      };
      if (isF(k, 'sin')) {
        const a = rawF('cos', arg0(k));
        const da = dget(a);
        if (da !== undefined && eq(da, nk)) take(a, pow(F('tan', arg0(k)), nk));
        else if (half) {
          const a1 = add(1, a);
          const da1 = dget(a1);
          if (da1 !== undefined && eq(da1, nk)) take(a1, pow(F('tan', mul(arg0(k), S.Half)), nk));
        }
      } else if (isF(k, 'cos')) {
        const a = rawF('sin', arg0(k));
        const da = dget(a);
        if (da !== undefined && eq(da, nk)) take(a, pow(F('tan', arg0(k)), neg(nk)));
      } else if (half && k instanceof Add && isOne(first(k.args)) && isF(at(k.args, 1), 'cos')) {
        const a = rawF('sin', arg0(cosArg(k)));
        const da = dget(a);
        if (da !== undefined && eq(da, nk) && (isTrue(isIntegerQ(da)) || isTrue(positive(a)))) take(a, pow(F('tan', mul(arg0(cosArg(k)), S.Half)), neg(nk)));
      }
    }
    if (t.length === 0) return rv0;
    const keep = (m: ExprMap<Expr>, tag: string): Expr[] => [...m].filter(([b, e]) => !used.has(`${tag}${b.key}`) && !isZero(e)).map(([b, e]) => pow(b, e));
    const r = mul(...t, ...keep(n, 'n'), pow(mul(...keep(d, 'd')), -1));
    return mul(r, ...ndone.map(([b, e]) => pow(b, e)), pow(mul(...ddone.map(([b, e]) => pow(b, e))), -1));
  };
  return bottomUp(sympify(rv), f);
}

/** The cos(...) term of 1 + cos(...). */
const cosArg = (k: Expr): Fn => cast(at(k.args, 1), Fn);

/** TR3: induced formulas, e.g. sin(-a) = -sin(a), and reduction to angles in [0, pi/4]. */
export function TR3(rv: ExprLike): Expr {
  const fmap: Record<TrigName, TrigName> = { cos: 'sin', sin: 'cos', tan: 'cot', cot: 'tan', sec: 'csc', csc: 'sec' };
  return bottomUp(sympify(rv), (e0) => {
    if (!isTrigFunction(e0)) return e0;
    const e = F(e0.name, signsimp(arg0(e0)));
    if (!isTrigFunction(e)) return e;
    const a = arg0(e);
    if (isTrue(positive(sub(a, mul(S.Pi, Rational.of(1n, 4n))))) && isTrue(positive(sub(mul(S.Pi, S.Half), a)))) {
      // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- e is a trigonometric function
      return F(fmap[e.name as TrigName], sub(mul(S.Pi, S.Half), a));
    }
    return e;
  });
}

/** TR4: the values at special angles (applied by the automatic evaluation). */
export function TR4(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!isTrigFunction(e)) return e;
    const r = mul(arg0(e), pow(S.Pi, -1));
    if (r instanceof Rational && [1n, 2n, 3n, 4n, 6n].includes(r.q)) return F(e.name, rebuild(arg0(e), arg0(e).args));
    return e;
  });
}

/** Helper for TR5 and TR6: f(x)**e -> h(g(x)**2)**(e/2). */
export function TR56(rv: ExprLike, f: FnName, g: FnName, h: (x: Expr) => Expr, max: number, usePow: boolean): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && isF(e.base, f))) return e;
    const x = e.exp;
    if (!isTrue(isReal(x))) return e;
    if (!(x instanceof Rational) || !x.isInteger) return e;
    const n = x.p;
    if (n < 0n || n > BigInt(max) || n === 1n) return e;
    const a = arg0(e.base);
    if (n === 2n) return h(pow(F(g, a), 2));
    if (n % 2n === 1n) return mul(F(f, a), pow(h(pow(F(g, a), 2)), Rational.of(n / 2n)));
    let k: bigint;
    if (n === 4n) k = 2n;
    else if (!usePow) k = n / 2n;
    else {
      if (perfectPower(n) === false) return e;
      k = n / 2n;
    }
    return pow(h(pow(F(g, a), 2)), Rational.of(k));
  });
}

/** TR5: sin**2 -> 1 - cos**2. */
export function TR5(rv: ExprLike, opts: { max?: number; pow?: boolean } = {}): Expr {
  return TR56(rv, 'sin', 'cos', (x) => sub(1, x), opts.max ?? 4, opts.pow ?? false);
}

/** TR6: cos**2 -> 1 - sin**2. */
export function TR6(rv: ExprLike, opts: { max?: number; pow?: boolean } = {}): Expr {
  return TR56(rv, 'cos', 'sin', (x) => sub(1, x), opts.max ?? 4, opts.pow ?? false);
}

/** TR7: lowering the degree of cos(x)**2. */
export function TR7(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && isF(e.base, 'cos') && eq(e.exp, S.Two))) return e;
    return mul(add(1, F('cos', mul(2, arg0(e.base)))), S.Half);
  });
}

/** TR8: products of sin and cos -> sums. */
export function TR8(rv: ExprLike, first0 = true): Expr {
  const f = (e: Expr): Expr => {
    if (!(e instanceof Mul || (isPowNode(e) && isF(e.base, 'cos', 'sin') && (isTrue(isIntegerQ(e.exp)) || isTrue(positive(e.base)))))) return e;
    if (first0) {
      const [n0, d0] = asNumerDenom(e);
      const n = expandMulOnly(n0);
      const d = expandMulOnly(d0);
      const newn = TR8(n, false);
      const newd = TR8(d, false);
      let r: Expr = e;
      if (!eq(newn, n) || !eq(newd, d)) {
        r = gcdTerms(mul(newn, pow(newd, -1)));
        if (r instanceof Mul && first(r.args) instanceof Rational && r.args.length === 2 && at(r.args, 1) instanceof Add) r = mul(...asCoeffMul(r));
      }
      return r;
    }
    const c: Expr[] = [];
    const s: Expr[] = [];
    const args: Expr[] = [];
    for (const a of mulArgs(e)) {
      if (isF(a, 'cos', 'sin')) (a.name === 'cos' ? c : s).push(arg0(a));
      else if (isPowNode(a) && isIntegerAtom(a.exp) && a.exp.isPositive && isF(a.base, 'cos', 'sin')) {
        const list = a.base.name === 'cos' ? c : s;
        for (let i = 0n; i < a.exp.p; i++) list.push(arg0(a.base));
      } else args.push(a);
    }
    if (!((c.length > 0 && s.length > 0) || c.length > 1 || s.length > 1)) return e;
    const n = Math.min(c.length, s.length);
    for (let i = 0; i < n; i++) {
      const a1 = popLast(s);
      const a2 = popLast(c);
      args.push(mul(add(F('sin', add(a1, a2)), F('sin', sub(a1, a2))), S.Half));
    }
    while (c.length > 1) {
      const a1 = popLast(c);
      const a2 = popLast(c);
      args.push(mul(add(F('cos', add(a1, a2)), F('cos', sub(a1, a2))), S.Half));
    }
    if (c.length) args.push(F('cos', popLast(c)));
    while (s.length > 1) {
      const a1 = popLast(s);
      const a2 = popLast(s);
      args.push(mul(add(neg(F('cos', add(a1, a2))), F('cos', sub(a1, a2))), S.Half));
    }
    if (s.length) args.push(F('sin', popLast(s)));
    return TR8(expandMulOnly(mul(...args)));
  };
  return bottomUp(sympify(rv), f);
}

function popLast<T>(xs: T[]): T {
  const v = last(xs);
  xs.pop();
  return v;
}

/** The pairwise combination loop shared by TR9 and TR10i (the `do` of SymPy). */
function pairwise(rv: Expr, two: (a: Expr, b: Expr, rv: Expr) => Expr): Expr {
  const go = (r: Expr): Expr => {
    const terms = ordered(r instanceof Add ? r.args : [r]);
    if (terms.length === 2) {
      const [x, y] = pair(terms);
      return two(x, y, r);
    }
    const args: (Expr | undefined)[] = terms;
    let hit = false;
    for (let i = 0; i < args.length; i++) {
      const ai = args[i];
      if (ai === undefined) continue;
      for (let j = i + 1; j < args.length; j++) {
        const aj = args[j];
        if (aj === undefined) continue;
        const was = add(ai, aj);
        const nw = go(was);
        if (!eq(nw, was)) {
          args[i] = nw;
          args[j] = undefined;
          hit = true;
          break;
        }
      }
    }
    if (!hit) return r;
    return go(add(...args.filter((x): x is Expr => x !== undefined)));
  };
  return go(rv);
}

/** TR9: sums of sin or cos -> products. */
export function TR9(rv: ExprLike): Expr {
  const two = (x: Expr, y: Expr, r: Expr): Expr => {
    const split = trigSplit(x, y);
    if (split === undefined) return r;
    const [gcd, n1, n2, a0, b0, iscos] = split;
    let [a, b] = [a0, b0];
    if (iscos) {
      if (n1 === n2) return mul(gcd, n1, 2, F('cos', mul(add(a, b), S.Half)), F('cos', mul(sub(a, b), S.Half)));
      if (n1 < 0) [a, b] = [b, a];
      return mul(-2, gcd, F('sin', mul(add(a, b), S.Half)), F('sin', mul(sub(a, b), S.Half)));
    }
    if (n1 === n2) return mul(gcd, n1, 2, F('sin', mul(add(a, b), S.Half)), F('cos', mul(sub(a, b), S.Half)));
    if (n1 < 0) [a, b] = [b, a];
    return mul(2, gcd, F('cos', mul(add(a, b), S.Half)), F('sin', mul(sub(a, b), S.Half)));
  };
  return bottomUp(sympify(rv), (e) => (e instanceof Add ? processCommonAddends(e, (x) => pairwise(x, two)) : e));
}

/** TR10: sin and cos of sums -> sums of products. */
export function TR10(rv: ExprLike, first0 = true): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!isF(e, 'cos', 'sin')) return e;
    const a0 = arg0(e);
    if (!(a0 instanceof Add)) return e;
    const args = first0 ? ordered(a0.args) : [...a0.args];
    const a = popLast(args);
    const b = add(...args);
    if (b instanceof Add) {
      if (e.name === 'sin') return add(mul(F('sin', a), TR10(F('cos', b), false)), mul(F('cos', a), TR10(F('sin', b), false)));
      return sub(mul(F('cos', a), TR10(F('cos', b), false)), mul(F('sin', a), TR10(F('sin', b), false)));
    }
    if (e.name === 'sin') return add(mul(F('sin', a), F('cos', b)), mul(F('cos', a), F('sin', b)));
    return sub(mul(F('cos', a), F('cos', b)), mul(F('sin', a), F('sin', b)));
  });
}

/** TR10i: sums of products -> sin and cos of sums. */
export function TR10i(rv: ExprLike): Expr {
  const two = (x: Expr, y: Expr, r: Expr): Expr => {
    const split = trigSplit(x, y, true);
    if (split === undefined) return r;
    const [gcd0, n1, n2, a, b, same] = split;
    const gcd = mul(n1, gcd0);
    if (same) return n1 === n2 ? mul(gcd, F('cos', sub(a, b))) : mul(gcd, F('cos', add(a, b)));
    return n1 === n2 ? mul(gcd, F('sin', add(a, b))) : mul(gcd, F('sin', sub(b, a)));
  };
  const doit = (x: Expr): Expr => pairwise(x, two);
  const f = (e: Expr): Expr => {
    if (!(e instanceof Add)) return e;
    let r = processCommonAddends(e, doit, (x) => ordered([...x.freeSymbols()]).map((s) => s.key).join(','));
    while (r instanceof Add) {
      const byrad = new ExprMap<(Expr | undefined)[]>();
      for (const a of r.args) {
        let hit = false;
        if (a instanceof Mul) {
          for (const ai of a.args) {
            if (isPowNode(ai) && eq(ai.exp, S.Half) && isIntegerAtom(ai.base)) {
              byrad.set(ai, [...(byrad.get(ai) ?? []), a]);
              hit = true;
              break;
            }
          }
        }
        if (!hit) byrad.set(S.One, [...(byrad.get(S.One) ?? []), a]);
      }
      const args: Expr[] = [];
      for (const a of byrad.keys()) {
        for (const b of [mul(sqrt(3), a), pow(sqrt(3), -1)]) {
          const lb = byrad.get(b);
          if (lb === undefined) continue;
          const la = getOrThrow(byrad, a);
          for (let i = 0; i < la.length; i++) {
            // (a list is emptied only while it is the list of a; b = sqrt(3)*a never has a list of its own b)
            const x = defined(la[i]);
            for (let j = 0; j < lb.length; j++) {
              const y = lb[j];
              if (y === undefined) continue;
              const was = add(x, y);
              const nw = doit(was);
              if (!eq(nw, was)) {
                args.push(nw);
                la[i] = undefined;
                lb[j] = undefined;
                break;
              }
            }
          }
        }
      }
      if (args.length) r = add(...args, ...[...byrad.values()].map((v) => add(...v.filter((x): x is Expr => x !== undefined))));
      else {
        r = doit(r);
        break;
      }
    }
    return r;
  };
  return bottomUp(sympify(rv), f);
}

/** TR11: double angles -> products of the single angle. */
export function TR11(rv: ExprLike, base?: Expr): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!isF(e, 'cos', 'sin')) return e;
    if (base !== undefined) {
      let t = F(e.name, mul(base, 2));
      let co: Expr = S.One;
      if (t instanceof Mul) [co, t] = asCoeffMul(t);
      if (!isF(t, 'cos', 'sin')) return e;
      if (eq(arg0(e), arg0(t))) {
        const c = F('cos', base);
        const s = F('sin', base);
        if (e.name === 'cos') return mul(sub(pow(c, 2), pow(s, 2)), pow(co, -1));
        return mul(2, c, s, pow(co, -1));
      }
      return e;
    }
    if (isNum(arg0(e))) return e;
    const [c, m] = asCoeffMul(arg0(e), true);
    if (!(c instanceof Rational) || c.p % 2n !== 0n) return e;
    const a = mul(Rational.of(c.p / 2n), m, Rational.of(1n, c.q));
    const cc = TR11(F('cos', a));
    const ss = TR11(F('sin', a));
    return e.name === 'sin' ? mul(2, ss, cc) : sub(pow(cc, 2), pow(ss, 2));
  });
}

/** _TR11: TR11 applied to the double angles whose half angle appears in the denominator. */
export function TR11Half(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e0) => {
    if (isBooleanNode(e0)) return e0;
    const sincosArgs = (flat: Expr): Record<'sin' | 'cos', ExprMap<true>> => {
      const out = { sin: new ExprMap<true>(), cos: new ExprMap<true>() };
      for (const fi of mulArgs(flat)) {
        const [b, x] = asBaseExp(fi);
        if (isIntegerAtom(x) && x.isPositive && isF(b, 'cos', 'sin')) out[b.name === 'cos' ? 'cos' : 'sin'].set(arg0(b), true);
      }
      return out;
    };
    const [nE, dE] = asNumerDenom(e0);
    const handle = (r0: Expr, na: Record<'sin' | 'cos', ExprMap<true>>, da: Record<'sin' | 'cos', ExprMap<true>>): Expr => {
      let r = r0;
      for (const narg of na.sin.keys()) {
        const half = mul(narg, S.Half);
        const func = da.cos.has(half) ? 'cos' : da.sin.has(half) ? 'sin' : undefined;
        if (func === undefined) continue;
        r = TR11(r, half);
        da[func].delete(half);
      }
      return r;
    };
    const na = sincosArgs(nE);
    const da = sincosArgs(dE);
    return handle(handle(e0, na, da), da, na);
  });
}

const isBooleanNode = (e: Expr): boolean => e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp;

/** TR12: tan of sums -> quotients of tan. */
export function TR12(rv: ExprLike, first0 = true): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!isF(e, 'tan')) return e;
    const a0 = arg0(e);
    if (!(a0 instanceof Add)) return e;
    const args = first0 ? ordered(a0.args) : [...a0.args];
    const a = popLast(args);
    const b = add(...args);
    const tb = b instanceof Add ? TR12(F('tan', b), false) : F('tan', b);
    return mul(add(F('tan', a), tb), pow(sub(1, mul(F('tan', a), tb)), -1));
  });
}

/** TR12i: (tan(y) + tan(x))/(tan(x)*tan(y) - 1) -> -tan(x + y). */
export function TR12i(rv: ExprLike): Expr {
  const f = (e: Expr): Expr => {
    if (!(e instanceof Add || e instanceof Mul || isPowNode(e))) return e;
    const [n, d] = asNumerDenom(e);
    if (d.args.length === 0 || n.args.length === 0) return e;
    const dok = new ExprMap<Expr>();
    const okd = (di: Expr): [Expr, Expr] | undefined => {
      const m = asFSign1(di);
      if (m === undefined) return undefined;
      const [g, ff, s] = m;
      if (isNegOne(s) && ff instanceof Mul && ff.args.length === 2 && ff.args.every((fi) => isF(fi, 'tan'))) return [g, ff];
      return undefined;
    };
    const tanSum = (t: Expr): Expr => add(...t.args.map((x) => first(x.args)));
    const dArgs: Expr[] = [...mulArgs(d)];
    for (let i = 0; i < dArgs.length; i++) {
      let di = at(dArgs, i);
      const m = okd(di);
      if (m) {
        const [g, t] = m;
        dok.set(tanSum(t), S.One);
        dArgs[i] = g;
        continue;
      }
      if (di instanceof Add) {
        di = factor(di);
        if (di instanceof Mul) {
          dArgs.push(...di.args);
          dArgs[i] = S.One;
        }
      } else if (isPowNode(di) && (isTrue(isIntegerQ(di.exp)) || isTrue(positive(di.base)))) {
        const mb = okd(di.base);
        if (mb) {
          const [g, t] = mb;
          dok.set(tanSum(t), di.exp);
          dArgs[i] = pow(g, di.exp);
        } else {
          di = factor(di);
          if (di instanceof Mul) {
            dArgs.push(...di.args);
            dArgs[i] = S.One;
          }
        }
      }
    }
    if (dok.size === 0) return e;
    const okn = (ni: Expr): [Expr, Expr] | undefined => {
      if (ni instanceof Add && ni.args.length === 2) {
        const [a, b] = [at(ni.args, 0), at(ni.args, 1)];
        if (isF(a, 'tan') && isF(b, 'tan')) return [a, b];
      }
      return undefined;
    };
    const nArgs: Expr[] = [...mulArgs(factorTerms(n))];
    let hit = false;
    for (let i = 0; i < nArgs.length; i++) {
      let ni = at(nArgs, i);
      // the factor tan(a) + tan(b) (or its negative, or a power of it) and what is left of it
      // (SymPy also tries -ni; factor_terms has already taken the sign out of the sums)
      let m = okn(ni);
      let k: Expr = S.One;
      if (!m) {
        if (ni instanceof Add) {
          ni = factor(ni);
          if (ni instanceof Mul) {
            nArgs.push(...ni.args);
            nArgs[i] = S.One;
          }
          continue;
        } else if (isPowNode(ni) && (isTrue(isIntegerQ(ni.exp)) || isTrue(positive(ni.base)))) {
          m = okn(ni.base);
          if (m) k = ni.exp;
          else {
            ni = factor(ni);
            if (ni instanceof Mul) {
              nArgs.push(...ni.args);
              nArgs[i] = S.One;
            }
            continue;
          }
        } else continue;
      }
      const s = add(...m.map((x) => first(x.args)));
      const ed = dok.get(s);
      // (SymPy raises KeyError for a sum of tangents without its denominator)
      if (ed === undefined) continue;
      // SymPy takes one power of tan(a) + tan(b) whatever its exponent and puts the remaining
      // denominator back as (tan(a) + tan(b) - 1)**e, which is wrong:
      // TR12i((tan(x) + tan(y))**2/(tan(x)*tan(y) - 1)**2) = -tan(x + y)/(tan(x) + tan(y) - 1)
      // there (x = y = pi/8 gives 1 and -1/(2*sqrt(2) - 3)); here the common power is taken
      // and the rest of the denominator is (tan(a)*tan(b) - 1)**e
      let j: Expr = S.One;
      let newed: Expr | undefined;
      if (isIntegerAtom(k) && isIntegerAtom(ed)) {
        j = k.toNumber() < ed.toNumber() ? k : ed;
        newed = sub(ed, j);
      } else newed = extractAdditively(ed, S.One);
      if (newed === undefined) continue;
      hit = true;
      if (isZero(newed)) dok.delete(s);
      else dok.set(s, newed);
      nArgs[i] = mul(pow(add(...m), sub(k, j)), pow(neg(F('tan', s)), j));
    }
    if (!hit) return e;
    return mul(
      ...nArgs,
      pow(mul(...dArgs), -1),
      pow(mul(...[...dok].map(([s, ex]) => pow(sub(mul(...s.args.map((a) => F('tan', a))), 1), ex))), -1),
    );
  };
  return bottomUp(sympify(rv), f);
}

/** TR13: products of tan or cot -> sums. */
export function TR13(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!(e instanceof Mul)) return e;
    const t: Expr[] = [];
    const c: Expr[] = [];
    const args: Expr[] = [];
    for (const a of e.args) {
      if (isF(a, 'tan')) t.push(arg0(a));
      else if (isF(a, 'cot')) c.push(arg0(a));
      else args.push(a);
    }
    if (t.length < 2 && c.length < 2) return e;
    while (t.length > 1) {
      const t1 = popLast(t);
      const t2 = popLast(t);
      const ts = F('tan', add(t1, t2));
      args.push(sub(1, add(mul(F('tan', t1), pow(ts, -1)), mul(F('tan', t2), pow(ts, -1)))));
    }
    if (t.length) args.push(F('tan', popLast(t)));
    while (c.length > 1) {
      const t1 = popLast(c);
      const t2 = popLast(c);
      const cs = F('cot', add(t1, t2));
      args.push(add(1, mul(F('cot', t1), cs), mul(F('cot', t2), cs)));
    }
    if (c.length) args.push(F('cot', popLast(c)));
    return mul(...args);
  });
}

/** TRmorrie: cos(x)*cos(2*x)*...*cos(2**(k-1)*x) -> sin(2**k*x)/(2**k*sin(x)). */
export function TRmorrie(rv: ExprLike): Expr {
  const f = (e: Expr, first0 = true): Expr => {
    if (!(e instanceof Mul)) return e;
    if (first0) {
      const [n, d] = asNumerDenom(e);
      return mul(f(n, false), pow(f(d, false), -1));
    }
    const args = new ExprMap<Expr[]>();
    const coss = new ExprMap<Expr>();
    const other: Expr[] = [];
    for (const c of e.args) {
      const [b, x] = asBaseExp(c);
      if (isIntegerAtom(x) && isF(b, 'cos')) {
        const [co, a] = asCoeffMul(arg0(b));
        args.set(a, [...(args.get(a) ?? []), co]);
        coss.set(b, x);
      } else other.push(c);
    }
    const nw: Expr[] = [];
    for (const [a, c] of args) {
      c.sort((u, v) => u.toNumber() - v.toNumber());
      const has = (v: Expr): boolean => c.some((w) => eq(w, v));
      while (c.length) {
        let k = 0;
        const ci = first(c);
        let cc = ci;
        while (has(cc)) {
          k += 1;
          cc = mul(cc, 2);
        }
        if (k > 1) {
          const newarg = mul(F('sin', mul(2 ** k, ci, a)), Rational.of(1n, 2n ** BigInt(k)), pow(F('sin', mul(ci, a)), -1));
          const ccs: Expr[] = [];
          const exps: Expr[] = [];
          for (let i = 0; i < k; i++) {
            cc = mul(cc, S.Half);
            exps.push(getOrThrow(coss, rawF('cos', mul(a, cc))));
            ccs.push(cc);
          }
          const tk = exps.reduce((m, x) => (x.toNumber() < m.toNumber() ? x : m));
          for (let i = 0; i < k; i++) {
            const c2 = popLast(ccs);
            const key = rawF('cos', mul(a, c2));
            const left = sub(getOrThrow(coss, key), tk);
            coss.set(key, left);
            if (isZero(left)) c.splice(c.findIndex((w) => eq(w, c2)), 1);
          }
          nw.push(pow(newarg, tk));
        } else {
          const b = F('cos', mul(first(c), a));
          c.shift();
          other.push(pow(b, getOrThrow(coss, b)));
        }
      }
    }
    if (nw.length === 0) return e;
    return mul(...nw, ...other);
  };
  return bottomUp(sympify(rv), (e) => f(e));
}

/** TR14: factored powers of sin or cos -> cos or sin powers, e.g. (1 - cos(x))*(1 + cos(x)) -> sin(x)**2. */
export function TR14(rv: ExprLike, first0 = true): Expr {
  const f = (e: Expr): Expr => {
    if (!(e instanceof Mul)) return e;
    if (first0) {
      const [n, d] = asNumerDenom(e);
      if (!isOne(d)) {
        const newn = TR14(n, false);
        const newd = TR14(d, false);
        return !eq(newn, n) || !eq(newd, d) ? mul(newn, pow(newd, -1)) : e;
      }
    }
    const other: Expr[] = [];
    type Item = { g: Expr; isNum: boolean; e: Expr; f: Fn; si: Expr; a: Expr };
    let proc: Item[] = [];
    for (const a0 of e.args) {
      let a = a0;
      let x: Expr = S.One;
      if (isPowNode(a)) {
        const [b, ex] = asBaseExp(a);
        if (!(isTrue(isIntegerQ(ex)) || isTrue(positive(b)))) {
          other.push(a);
          continue;
        }
        a = b;
        x = ex;
      }
      const m = asFSign1(a);
      if (m === undefined || !isF(m[1], 'cos', 'sin')) {
        other.push(isOne(x) ? a : pow(a, x));
        continue;
      }
      proc.push({ g: m[0], isNum: isNum(x), e: x, f: m[1], si: m[2], a });
    }
    proc = orderedItems(proc, (p) => [p.g, p.isNum ? S.One : S.Zero, p.e, p.f, p.si, p.a]);
    const nother = other.length;
    while (proc.length) {
      const A = defined(proc.shift());
      if (proc.length) {
        let B = first(proc);
        if (isNum(A.e) && isNum(B.e)) {
          if (eq(A.f, B.f) && !eq(A.si, B.si)) {
            B = defined(proc.shift());
            const take = A.e.toNumber() <= B.e.toNumber() ? A.e : B.e;
            if (!eq(B.e, take)) proc.unshift({ ...B, e: sub(B.e, take) });
            else if (!eq(A.e, take)) proc.unshift({ ...A, e: sub(A.e, take) });
            const t: FnName = A.f.name === 'cos' ? 'sin' : 'cos';
            other.push(pow(mul(-1, A.g, B.g, pow(F(t, arg0(A.f)), 2)), take));
            continue;
          }
        } else if (eq(A.e, B.e) && eq(A.f, B.f) && !eq(A.si, B.si)) {
          B = defined(proc.shift());
          const t: FnName = A.f.name === 'cos' ? 'sin' : 'cos';
          other.push(pow(mul(-1, A.g, B.g, pow(F(t, arg0(A.f)), 2)), A.e));
          continue;
        }
      }
      other.push(pow(A.a, A.e));
    }
    return other.length !== nother ? mul(...other) : e;
  };
  return bottomUp(sympify(rv), f);
}


/**
 * SymPy ordered() of tuples: by node count, then elementwise by sort key
 * (each element replaced by the rank of its default_sort_key among the values at its position).
 */
function orderedItems<T>(xs: readonly T[], parts: (x: T) => readonly Expr[]): T[] {
  const ps = xs.map(parts);
  const width = ps.length ? first(ps).length : 0;
  const ranks = Array.from({ length: width }, (_, i) => uniqExprs(ps.map((p) => at(p, i))).sort((u, v) => compareKeys(sortKey(u), sortKey(v))));
  const keyOf = (p: readonly Expr[]): number[] => [1 + p.reduce((n, x) => n + nodeCount(x), 0), ...p.map((x, i) => at(ranks, i).findIndex((y) => eq(x, y)))];
  const keyed = xs.map((x, i) => ({ x, k: keyOf(at(ps, i)) }));
  keyed.sort((u, v) => compareMeasured(u.k, v.k));
  return keyed.map((k) => k.x);
}

function uniqExprs(xs: readonly Expr[]): Expr[] {
  const m = new ExprMap<true>();
  for (const x of xs) m.set(x, true);
  return [...m.keys()];
}

/** SymPy _node_count (Floats count 1/2, exp(x) is one node). */
export function nodeCount(e: Expr): number {
  if (e instanceof Float) return 0.5;
  if (e instanceof Pow && eq(e.base, S.E)) return 1 + nodeCount(e.exp);
  // (SymPy _nodes: a derivative counts its expression and the orders of differentiation)
  if (e instanceof Derivative) return nodeCount(e.expr) + e.variableCount.reduce((n, [, k]) => n + k, 0);
  let n = 1;
  for (const a of e.args) n += nodeCount(a);
  return n;
}

/** TR15: negative powers of sin -> cot powers. */
export function TR15(rv: ExprLike, opts: { max?: number; pow?: boolean } = {}): Expr {
  return TR1516(rv, 'sin', 'cot', opts);
}

/** TR16: negative powers of cos -> tan powers. */
export function TR16(rv: ExprLike, opts: { max?: number; pow?: boolean } = {}): Expr {
  return TR1516(rv, 'cos', 'tan', opts);
}

function TR1516(rv: ExprLike, f: FnName, g: FnName, opts: { max?: number; pow?: boolean }): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && isF(e.base, f))) return e;
    const x = e.exp;
    // (SymPy: TR15 is applied for an odd exponent in both TR15 and TR16)
    if (x instanceof Rational && x.isInteger && ((x.p % 2n) + 2n) % 2n === 1n) return mul(TR15(pow(e.base, add(x, 1))), pow(e.base, -1));
    const ia = pow(e, -1);
    const a = TR56(ia, f, g, (y) => add(1, y), opts.max ?? 4, opts.pow ?? false);
    return eq(a, ia) ? e : a;
  });
}

/** TR111: negative powers of sin, cos and tan -> positive powers of csc, sec and cot. */
export function TR111(rv: ExprLike): Expr {
  const inv: Partial<Record<FnName, FnName>> = { tan: 'cot', sin: 'csc', cos: 'sec' };
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && (isTrue(positive(e.base)) || (isTrue(isIntegerQ(e.exp)) && isTrue(isNegative(e.exp)))))) return e;
    if (e.base instanceof Fn) {
      const r = inv[e.base.name];
      if (r !== undefined) return pow(F(r, arg0(e.base)), neg(e.exp));
    }
    return e;
  });
}

/** TR22: tan**2 -> sec**2 - 1, cot**2 -> csc**2 - 1. */
export function TR22(rv: ExprLike, opts: { max?: number; pow?: boolean } = {}): Expr {
  const max = opts.max ?? 4;
  const p = opts.pow ?? false;
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && isF(e.base, 'cot', 'tan'))) return e;
    const r = TR56(e, 'tan', 'sec', (x) => sub(x, 1), max, p);
    return TR56(r, 'cot', 'csc', (x) => sub(x, 1), max, p);
  });
}

/** TRpower: positive integer powers of sin and cos -> sums of multiple angles. */
export function TRpower(rv: ExprLike): Expr {
  return bottomUp(sympify(rv), (e) => {
    if (!(isPowNode(e) && isF(e.base, 'sin', 'cos'))) return e;
    const b = e.base;
    const n0 = e.exp;
    const x = arg0(b);
    if (!(isIntegerAtom(n0) && n0.isPositive)) return e;
    const n = n0.p;
    const odd = n % 2n === 1n;
    const terms: Expr[] = [];
    const kmax = odd ? (n + 1n) / 2n : n / 2n;
    for (let k = 0n; k < kmax; k++) {
      const c = Rational.of(binom(n, k));
      const sign = b.name === 'sin' && k % 2n === 1n ? -1 : 1;
      const angle = mul(Rational.of(n - 2n * k), x);
      terms.push(mul(c, b.name === 'cos' ? 1 : sign, F(b.name === 'cos' || !odd ? 'cos' : 'sin', angle)));
    }
    const scale = mul(Rational.of(1n, 2n ** (n - 1n)), b.name === 'sin' ? pow(-1, Rational.of(odd ? (n - 1n) / 2n : n / 2n)) : 1);
    let r = mul(scale, add(...terms));
    if (!odd) r = add(r, mul(Rational.of(1n, 2n ** n), Rational.of(binom(n, n / 2n))));
    return r;
  });
}

function binom(n: bigint, k: bigint): bigint {
  let r = 1n;
  for (let i = 0n; i < k; i++) r = (r * (n - i)) / (i + 1n);
  return r;
}

// ---------------------------------------------------------------------------
// the algorithm
// ---------------------------------------------------------------------------

const TR0r: Rule = (e) => TR0(e);
const TR5r: Rule = (e) => TR5(e);
const TR6r: Rule = (e) => TR6(e);
const CTR1 = choice(chain(TR5r, TR0r), chain(TR6r, TR0r), identity);
const CTR2 = chain((e) => TR11(e), choice(chain(TR5r, TR0r), chain(TR6r, TR0r), TR0r));
const CTR3 = choice(chain(TRmorrie, (e) => TR8(e), TR0r), chain(TRmorrie, (e) => TR8(e), TR10i, TR0r), identity);
const CTR4 = choice(chain(TR4, TR10i), identity);
const RL1 = chain(TR4, TR3, TR4, (e) => TR12(e), TR4, TR13, TR4, TR0r);
const RL2 = choice(
  chain(TR4, TR3, (e) => TR10(e), TR4, TR3, (e) => TR11(e)),
  chain(TR5r, TR7, (e) => TR11(e), TR4),
  chain(CTR3, CTR1, TR9, CTR2, TR4, TR9, TR9, CTR4),
  identity,
);

/** The default objective of fu: (L(x), count_ops(x)). */
const defaultMeasure = (x: Expr): Measured => [count(x, isTrigFunction), countOps(x)];

/**
 * Simplify a trigonometric expression with the algorithm of Fu et al.
 * (SymPy fu): the rule lists RL1 (tan and cot) and RL2 (sin and cos) are
 * applied greedily, keeping the result with the smallest measure (by
 * default the number of trigonometric functions, then count_ops).
 */
export function fu(rvIn: ExprLike, opts: { measure?: (e: Expr) => Measured } = {}): Expr {
  const measure = opts.measure ?? defaultMeasure;
  const was = sympify(rvIn);
  // (SymPy maps fu over the arguments of a non-Expr: Relational, Boolean)
  if (isBooleanNode(was)) return rebuild(was, was.args.map((a) => fu(a, opts)));
  const fRL1 = greedy(RL1, measure);
  const fRL2 = greedy(RL2, measure);
  let rv = TR1(was);
  if (hasF(rv, 'tan', 'cot')) {
    const rv1 = fRL1(rv);
    if (compareMeasured(measure(rv1), measure(rv)) < 0) rv = rv1;
    if (hasF(rv, 'tan', 'cot')) rv = TR2(rv);
  }
  if (hasF(rv, 'sin', 'cos')) {
    const rv1 = fRL2(rv);
    const rv2 = TR8(TRmorrie(rv1));
    rv = minBy([was, rv, rv1, rv2], measure);
  }
  return minBy([TR2i(rv), rv], measure);
}

/**
 * Apply `doit` to the groups of terms of a sum that share the absolute
 * value of their numeric coefficient (and, with key2, its value).
 */
export function processCommonAddends(rv: Expr, doit: Rule, key2?: (e: Expr) => string): Expr {
  const absc = new Map<string, [Expr, Expr[]]>();
  for (const a0 of rv.args) {
    // (SymPy's key1=False is not used by the rules)
    let [c, a] = asCoeffMul(a0);
    if (isTrue(isNegative(c))) {
      c = neg(c);
      a = neg(a);
    }
    const k = `${c.key}|${key2 ? key2(a) : '1'}`;
    const cur = absc.get(k);
    if (cur) cur[1].push(a);
    else absc.set(k, [c, [a]]);
  }
  const args: Expr[] = [];
  let hit = false;
  for (const [c, v] of absc.values()) {
    if (v.length > 1) {
      const e = add(...v);
      const nw = doit(e);
      if (!eq(nw, e)) hit = true;
      args.push(mul(c, nw));
    } else args.push(mul(c, first(v)));
  }
  return hit ? add(...args) : rv;
}

/** The rules of fu by name (SymPy FU). */
export const FU: ReadonlyMap<string, (e: Expr) => Expr> = new Map<string, (e: Expr) => Expr>([
  ['TR0', TR0], ['TR1', TR1], ['TR2', (e) => TR2(e)], ['TR3', TR3], ['TR4', TR4], ['TR5', TR5r], ['TR6', TR6r],
  ['TR7', TR7], ['TR8', (e) => TR8(e)], ['TR9', TR9], ['TR10', (e) => TR10(e)], ['TR10i', TR10i], ['TR11', (e) => TR11(e)],
  ['TR12', (e) => TR12(e)], ['TR13', TR13], ['L', L], ['TR2i', (e) => TR2i(e)], ['TRmorrie', TRmorrie], ['TR12i', TR12i],
  ['TR14', (e) => TR14(e)], ['TR15', (e) => TR15(e)], ['TR16', (e) => TR16(e)], ['TR111', TR111], ['TR22', (e) => TR22(e)],
]);

// ---------------------------------------------------------------------------
// trig_split, as_f_sign_1
// ---------------------------------------------------------------------------

/**
 * SymPy trig_split: the gcd, the signs, the arguments and the kind of a pair
 * of terms that combine by an angle sum or difference formula.
 */
export function trigSplit(aIn: Expr, bIn: Expr, two = false): [Expr, number, number, Expr, Expr, boolean] | undefined {
  const fa = factorsOf(aIn);
  const fb = factorsOf(bIn);
  let [ua, ub] = factorsNormal(fa, fb);
  let gcd = factorsGcd(fa, fb).asExpr();
  let n1 = 1;
  let n2 = 1;
  if (ua.factors.has(S.NegOne)) {
    ua = ua.quo(S.NegOne);
    n1 = -n1;
  } else if (ub.factors.has(S.NegOne)) {
    ub = ub.quo(S.NegOne);
    n2 = -n2;
  }
  const powCosSin = (a0: Expr): [Expr | undefined, Fn | undefined, Fn | undefined] | undefined => {
    let c: Fn | undefined;
    let s: Fn | undefined;
    let co: Expr = S.One;
    const isSqrt = (x: Expr): boolean => isPowNode(x) && eq(x.exp, S.Half);
    if (a0 instanceof Mul) {
      const [co0, a] = asCoeffMul(a0);
      co = co0;
      if (a.args.length > 2 || !two) return undefined;
      const args = [...mulArgs(a)];
      const x = defined(args.shift());
      if (isF(x, 'cos')) c = x;
      else if (isF(x, 'sin')) s = x;
      else if (isSqrt(x)) co = mul(co, x);
      else return undefined;
      if (args.length) {
        const b = first(args);
        if (isF(b, 'cos')) {
          if (c) s = b;
          else c = b;
        } else if (isF(b, 'sin')) {
          if (s) c = b;
          else s = b;
        } else if (isSqrt(b)) co = mul(co, b);
        else return undefined;
      }
      return [isOne(co) ? undefined : co, c, s];
    }
    if (isF(a0, 'cos')) c = a0;
    else if (isF(a0, 'sin')) s = a0;
    if (c === undefined && s === undefined) return undefined;
    return [undefined, c, s];
  };
  const ma = powCosSin(ua.asExpr());
  if (ma === undefined) return undefined;
  const mb = powCosSin(ub.asExpr());
  if (mb === undefined) return undefined;
  let [coa, ca, sa] = ma;
  let [cob, cb, sb] = mb;
  if ((!ca && cb) || (ca && isF(ca, 'sin'))) {
    [coa, ca, sa, cob, cb, sb] = [cob, cb, sb, coa, ca, sa];
    [n1, n2] = [n2, n1];
  }
  if (!two) {
    const c = defined(ca ?? sa);
    const s = defined(cb ?? sb);
    if (c.name !== s.name) return undefined;
    return [gcd, n1, n2, arg0(c), arg0(s), c.name === 'cos'];
  }
  if (!coa && !cob && ca && cb && sa && sb) {
    if ((ca.name === sa.name) !== (cb.name === sb.name)) return undefined;
    const argsSet = [ca, sa].map((j) => arg0(j).key);
    if (![cb, sb].every((i) => argsSet.includes(arg0(i).key))) return undefined;
    return [gcd, n1, n2, arg0(ca), arg0(sa), ca.name === sa.name];
  }
  if ((ca && sa) || (cb && sb) || (ca === undefined && sa === undefined) || (cb === undefined && sb === undefined)) return undefined;
  const c = defined(ca ?? sa);
  const s = defined(cb ?? sb);
  if (!eq(arg0(c), arg0(s))) return undefined;
  const ca1 = coa ?? S.One;
  const cb1 = cob ?? S.One;
  if (eq(ca1, cb1)) {
    gcd = mul(gcd, sqrt(2));
    return [gcd, n1, n2, arg0(c), mul(S.Pi, Rational.of(1n, 4n)), false];
  }
  const ratio = mul(ca1, pow(cb1, -1));
  if (eq(ratio, sqrt(3))) return [mul(gcd, 2, cb1), n1, n2, arg0(c), mul(S.Pi, Rational.of(1n, 3n)), false];
  if (eq(ratio, pow(sqrt(3), -1))) return [mul(gcd, 2, ca1), n1, n2, arg0(c), mul(S.Pi, Rational.of(1n, 6n)), false];
  return undefined;
}

/** SymPy as_f_sign_1: e = g*(f + s) with s = +-1, or undefined. */
export function asFSign1(e: Expr): [Expr, Expr, Expr] | undefined {
  if (!(e instanceof Add) || e.args.length !== 2) return undefined;
  let [a, b] = [at(e.args, 0), at(e.args, 1)];
  if (isOne(a) || isNegOne(a)) {
    let g: Expr = S.One;
    if (b instanceof Mul && isNum(first(b.args)) && isTrue(isNegative(first(b.args)))) {
      [a, b] = [neg(a), neg(b)];
      g = neg(g);
    }
    return [g, b, a];
  }
  const fa = factorsOf(a);
  const fb = factorsOf(b);
  let [ua, ub] = factorsNormal(fa, fb);
  let gcd = factorsGcd(fa, fb).asExpr();
  let n1: number;
  let n2: number;
  if (ua.factors.has(S.NegOne)) {
    ua = ua.quo(S.NegOne);
    n1 = -1;
    n2 = 1;
  } else if (ub.factors.has(S.NegOne)) {
    ub = ub.quo(S.NegOne);
    n1 = 1;
    n2 = -1;
  } else n1 = n2 = 1;
  [a, b] = [ua.asExpr(), ub.asExpr()];
  if (isOne(a)) {
    [a, b] = [b, a];
    [n1, n2] = [n2, n1];
  }
  if (n1 === -1) {
    gcd = neg(gcd);
    n2 = -n2;
  }
  if (isOne(b)) return [gcd, a, Rational.of(n2)];
  return undefined;
}

// ---------------------------------------------------------------------------
// hyperbolic functions as trigonometric ones (Osborne's rule)
// ---------------------------------------------------------------------------

function osborne(e: Expr, d: Dummy): Expr {
  return bottomUp(e, (rv) => {
    if (!isHyperFunction(rv)) return rv;
    const a0 = arg0(rv);
    const a = a0 instanceof Add ? add(...a0.args.map((i) => mul(i, d))) : mul(a0, d);
    switch (rv.name) {
      case 'sinh':
        return mul(S.I, F('sin', a));
      case 'cosh':
        return F('cos', a);
      case 'tanh':
        return mul(S.I, F('tan', a));
      case 'coth':
        return mul(F('cot', a), pow(S.I, -1));
      case 'sech':
        return F('sec', a);
      default:
        return mul(F('csc', a), pow(S.I, -1));
    }
  });
}

function osbornei(e: Expr, d: Dummy): Expr {
  return bottomUp(e, (rv) => {
    if (!isTrigFunction(rv)) return rv;
    const [cst, x] = asIndependent(arg0(rv), [d], { asAdd: true });
    const a = add(xreplace(x, [[d, S.One]]), mul(cst, S.I));
    switch (rv.name) {
      case 'sin':
        return mul(F('sinh', a), pow(S.I, -1));
      case 'cos':
        return F('cosh', a);
      case 'tan':
        return mul(F('tanh', a), pow(S.I, -1));
      case 'cot':
        return mul(F('coth', a), S.I);
      case 'sec':
        return F('sech', a);
      default:
        return mul(F('csch', a), S.I);
    }
  });
}

/**
 * SymPy hyper_as_trig: the expression with hyperbolic functions written as
 * trigonometric ones, and the function that undoes it.
 */
export function hyperAsTrig(rvIn: ExprLike): [Expr, (x: Expr) => Expr] {
  const rv = sympify(rvIn);
  const trigs = new ExprMap<Dummy>();
  some(rv, (x) => {
    if (isTrigFunction(x) && !trigs.has(x)) trigs.set(x, new Dummy());
    return false;
  });
  const masked = xreplace(rv, [...trigs].map(([k, v]) => [k, v] as const));
  const back = [...trigs].map(([k, v]) => [v, k] as const);
  const d = new Dummy();
  return [osborne(masked, d), (x: Expr) => collect(signsimp(xreplace(osbornei(x, d), back)), S.I)];
}

/** SymPy sincos_to_sum: powers and products of sin and cos -> sums of multiple angles. */
export function sincosToSum(expr: ExprLike): Expr {
  const e = sympify(expr);
  if (!hasF(e, 'cos', 'sin')) return e;
  return TR8(expandMulOnly(TRpower(e)));
}
