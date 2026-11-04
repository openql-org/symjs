// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file powsimp, powdenest, logcombine and posify (ports of SymPy's
 * simplify.powsimp and the corresponding parts of simplify.simplify).
 */

import { isIntegerQ, isNegative, isNonNegative, isPositive, isReal } from '../core/assumptions';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Float, Fn, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, splitCoeff, sympify } from '../core/ops';
import { countOps, ordered } from '../core/match';
import { keepCoeff } from '../core/methods';
import { rebuild, subs, xreplace } from '../core/traverse';
import { log } from '../functions/elementary/elementary';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand_log, expandMul } from './expand';
import { factorTerms } from './exprtools';
import { fraction } from './rational';
import { cast, defined, first, getOrThrow } from '../core/guard';

type Combine = 'all' | 'exp' | 'base';
export interface PowsimpOptions {
  deep?: boolean;
  combine?: Combine;
  force?: boolean;
}

const isExpPow = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
/** The exponent of exp(x), or undefined for any other node. */
const expExponent = (e: Expr): Expr | undefined => (e instanceof Pow && isExpPow(e) ? e.exp : undefined);
const isRat = (e: Expr): e is Rational => e instanceof Rational;
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isOneE = (e: Expr) => e instanceof Rational && e.isOne;
const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;
const asBaseExp = (e: Expr): [Expr, Expr] => (e instanceof Pow ? [e.base, e.exp] : [e, S.One]);
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);

/** Map keyed by expression with insertion order. */
class EMap<V> {
  readonly m = new Map<string, [Expr, V]>();
  get(k: Expr): V | undefined {
    return this.m.get(k.key)?.[1];
  }
  has(k: Expr): boolean {
    return this.m.has(k.key);
  }
  set(k: Expr, v: V): void {
    const cur = this.m.get(k.key);
    this.m.set(k.key, [cur ? cur[0] : k, v]);
  }
  delete(k: Expr): void {
    this.m.delete(k.key);
  }
  entries(): [Expr, V][] {
    return [...this.m.values()];
  }
}

function ilcm(a: bigint, b: bigint): bigint {
  const g = (x: bigint, y: bigint): bigint => (y === 0n ? x : g(y, x % y));
  return (a / g(a, b)) * b;
}

/** Number of times p divides n (p >= 2, n >= 1: the callers pass the parts of rationals other than 0 and 1). */
function multiplicityInt(p: bigint, nIn: bigint): number {
  let n = nIn;
  let m = 0;
  while (n % p === 0n) {
    n /= p;
    m++;
  }
  return m;
}

/** SymPy multiplicity(p, n) for positive rationals. */
function multiplicity(p: Rational, n: Rational): number {
  if (p.q === 1n) {
    if (n.p === 1n) return -multiplicityInt(p.p, n.q);
    return multiplicityInt(p.p, n.p) - multiplicityInt(p.p, n.q);
  }
  if (p.p === 1n) return multiplicityInt(p.q, n.q);
  const like = Math.min(multiplicityInt(p.p, n.p), multiplicityInt(p.q, n.q));
  const cross = Math.min(multiplicityInt(p.q, n.p), multiplicityInt(p.p, n.q));
  return like - cross;
}

const absR = (r: Rational): Rational => (r.isNegative ? Rational.of(-r.p, r.q) : r);

/** Reduce x**y by combining bases and exponents (SymPy powsimp). */
export function powsimp(exIn: ExprLike, opts: PowsimpOptions = {}): Expr {
  const deep = opts.deep ?? false;
  const combine = opts.combine ?? 'all';
  const force = opts.force ?? false;
  const recurse = (arg: Expr, o: PowsimpOptions = {}): Expr =>
    powsimp(arg, { deep: o.deep ?? deep, combine: o.combine ?? combine, force: o.force ?? force });

  let expr = sympify(exIn);
  if (expr.args.length === 0) return expr;

  if (deep || expr instanceof Add || (expr instanceof Mul && !expr.args.some((a) => a.key === Y.key))) {
    const ex = expExponent(expr);
    expr = ex !== undefined ? exp(recurse(ex)) : rebuild(expr, expr.args.map((w) => recurse(w)));
  }
  if (expr instanceof Pow) {
    return mul(recurse(mul(expr, Y), { deep: false }), pow(Y, -1));
  }
  if (!(expr instanceof Mul)) return expr;

  if (combine === 'exp' || combine === 'all') {
    const cPowers = new EMap<Expr[]>();
    // non-commutative factors keep their order; adjacent equal bases combine (A**x*A**y = A**(x + y))
    const ncPart: Expr[] = [];
    let coeff: Expr = S.One;
    for (let term of expr.args) {
      if (isRat(term)) {
        coeff = mul(coeff, term);
        continue;
      }
      if (term instanceof Pow && !isExpPow(term)) term = denestPow(term);
      if (!term.isCommutative) {
        const prev = ncPart.at(-1);
        if (prev !== undefined) {
          const [b1, e1] = asBaseExp(prev);
          const [b2, e2] = asBaseExp(term);
          if (b1.key === b2.key && e1.isCommutative && e2.isCommutative) {
            ncPart[ncPart.length - 1] = pow(b1, add(e1, e2));
            continue;
          }
        }
        ncPart.push(term);
        continue;
      }
      let [b, e] = asBaseExp(term);
      if (deep) {
        b = recurse(b);
        e = recurse(e);
      }
      if (b instanceof Pow) {
        b = pow(b, e);
        e = S.One;
      }
      const cur = cPowers.get(b);
      if (cur) cur.push(e);
      else cPowers.set(b, [e]);
    }
    // add up exponents of common bases
    const summed = new EMap<Expr>();
    for (const [b, es] of orderedEntries(cPowers.entries())) {
      if (
        isRat(b) &&
        !es.every((ei) => isRat(ei) || ei instanceof Float) &&
        !isOneE(coeff) &&
        !(b.isOne || (b.p === -1n && b.q === 1n)) &&
        isRat(coeff)
      ) {
        const m = multiplicity(absR(b), absR(coeff));
        if (m) {
          es.push(Rational.of(BigInt(m)));
          coeff = mul(coeff, pow(b, -m));
        }
      }
      summed.set(b, add(...es));
    }
    if (!isOneE(coeff)) {
      const cur = summed.get(coeff);
      summed.set(coeff, cur ? add(cur, 1) : S.One);
    }
    // base and inverted base pairs
    const skip = new Set<string>();
    for (const [b, e0] of summed.entries()) {
      if (skip.has(b.key) || !summed.has(b)) continue;
      // SymPy's special case for the float 1: 1.0**e = 1.0
      if (b instanceof Float && b.value === 1) {
        summed.set(b, S.One);
        continue;
      }
      if (isPositive(b)) {
        const binv = pow(b, -1);
        if (b.key !== binv.key && summed.has(binv)) {
          if (isOneE(fraction(b)[0])) {
            const e = defined(summed.get(b));
            summed.delete(b);
            summed.set(binv, add(defined(summed.get(binv)), mul(-1, e)));
          } else {
            skip.add(binv.key);
            const e = defined(summed.get(binv));
            summed.delete(binv);
            summed.set(b, add(defined(summed.get(b)), mul(-1, e)));
          }
        }
        void e0;
      }
    }
    // base and negated base pairs
    for (const [b] of summed.entries()) {
      const nb = mul(-1, b);
      const eb = summed.get(b);
      const enb = summed.get(nb);
      if ((b instanceof Sym || b instanceof Add) && enb !== undefined && eb !== undefined) {
        let e = eb;
        if (isPositive(b) !== undefined || isIntegerQ(e) === true) {
          if (isIntegerQ(e) === true || isNegative(b) === true) {
            summed.set(nb, add(enb, e));
            summed.delete(b);
          } else {
            e = enb;
            summed.delete(nb);
            summed.set(b, add(eb, e));
          }
          const cur = summed.get(S.NegOne);
          summed.set(S.NegOne, cur ? add(cur, e) : e);
        }
      }
    }
    let cList: [Expr, Expr][] = summed.entries().filter(([, e]) => !isZeroE(e));

    // ---- combine Mul bases of rational powers with separated bases
    type BKey = { b: Expr; q: bigint; key: string };
    const mk = (b: Expr, q: bigint): BKey => ({ b, q, key: `${b.key}|${q}` });
    const bkey = (b: Expr, e?: Expr): [BKey, Expr] => {
      if (e === undefined) {
        const [bb, ee] = asBaseExp(b);
        return bkey(bb, ee);
      }
      if (isInt(e)) return [mk(b, 1n), e];
      if (isRat(e)) return [mk(b, e.q), Rational.of(e.p)];
      const [c, m] = splitCoeff(e);
      if (isRat(c) && !c.isOne) {
        if (isIntegerQ(m) === true) return [mk(b, c.q), mul(m, Rational.of(c.p))];
        return [mk(pow(b, m), c.q), Rational.of(c.p)];
      }
      return [mk(pow(b, e), 1n), S.One];
    };
    const ratq = (x: Expr): bigint => bkey(x)[0].q;
    const commonB = new Map<string, [BKey, Expr]>();
    const bases: BKey[] = [];
    const done: [Expr, Expr][] = [];
    const cbGet = (k: BKey) => commonB.get(k.key)?.[1];
    const cbSet = (k: BKey, v: Expr) => commonB.set(k.key, [commonB.get(k.key)?.[0] ?? k, v]);
    /** common_b[k] += e (starting from 0). */
    const cbAdd = (k: BKey, e: Expr) => {
      const cur = cbGet(k);
      cbSet(k, cur === undefined ? e : add(cur, e));
    };
    // update is called right after the exponent of k is set; it may be symbolic when an
    // earlier update in the same step added n*e for an integer symbol n (SymPy raises there)
    const update = (k: BKey) => {
      const v = defined(cbGet(k), 'exponent of the base');
      if (!isInt(v)) return;
      const q = BigInt(k.q);
      const newe = v.p >= 0n ? v.p / q : -((-v.p + q - 1n) / q);
      const r = v.p - newe * q;
      if (r === 0n) {
        commonB.delete(k.key);
        if (newe !== 0n) {
          for (const m of mulArgs(pow(k.b, Rational.of(newe)))) {
            const [bk, e] = bkey(m);
            cbAdd(bk, e);
            if (bk.q !== 1n) bases.push(bk);
          }
        }
      }
    };
    for (const [b0, e0] of cList) {
      const [b, e] = bkey(b0, e0);
      cbAdd(b, e);
      if (b.q !== 1n && b.b instanceof Mul) bases.push(b);
    }
    // (no two of these bases have the same b: each comes from a distinct product base of a rational power)
    bases.sort((x, y) => compareKeys(sortKey(x.b), sortKey(y.b)));
    bases.sort((x, y) => countOps(y.b) - countOps(x.b));
    for (const base of bases) {
      if (!commonB.has(base.key)) continue;
      let b = base.b;
      const exponent = Rational.of(base.q);
      let last = false;
      let qlcm = 1n;
      for (;;) {
        const bstart = b;
        const qstart = qlcm;
        let bb: BKey[] = [];
        let ee: [Rational, Rational][] = [];
        for (const bi of mulArgs(b)) {
          const [bib, bie] = bkey(bi);
          const cur = cbGet(bib);
          if (cur === undefined || !isInt(cur) || !isInt(bie) || cur.p * 1n < bie.p) {
            ee = [];
            bb = [];
            break;
          }
          ee.push([bie, cur]);
          bb.push(bib);
        }
        if (ee.length) {
          const fl = (a: Rational, d: Rational) => {
            const q = a.p / d.p;
            return a.p < 0n !== d.p < 0n && q * d.p !== a.p ? q - 1n : q;
          };
          const e0 = first(ee);
          const eRest = ee.slice(1);
          let min1 = fl(e0[1], e0[0]);
          let ok = true;
          for (const [eie, eicur] of eRest) {
            const rat = fl(eicur, eie);
            if (rat < 1n) {
              ok = false;
              break;
            }
            if (rat < min1) min1 = rat;
          }
          if (ok) {
            bb.forEach((bk, i) => {
              cbAdd(bk, mul(-1, Rational.of(min1), defined(ee[i])[0]));
              update(bk);
            });
            cbAdd(base, mul(Rational.of(min1), Rational.of(qstart), exponent));
          }
        }
        if (last || commonB.size === 1 || [...commonB.values()].every(([k]) => k.q === 1n)) break;
        qlcm = mulArgs(bstart).reduce((acc, bi) => ilcm(acc, ratq(bi)), 1n);
        if (qlcm === 1n) break;
        b = pow(bstart, Rational.of(qlcm));
        qlcm *= qstart;
        if (mulArgs(b).every((bi) => ratq(bi) === 1n)) last = true;
      }
      // update deletes only factor keys of base.b (never base itself), so the entry is still there
      const v = defined(cbGet(base), 'exponent of the base');
      commonB.delete(base.key);
      done.push([base.b, mul(v, Rational.of(1n, base.q))]);
    }
    cList = done;
    for (const [k, e] of commonB.values()) {
      let b: Expr;
      if (k.b instanceof Pow && k.q !== 1n && !isRat(k.b.exp)) {
        b = pow(k.b.base, mul(k.b.exp, Rational.of(1n, k.q)));
      } else b = pow(k.b, Rational.of(1n, k.q));
      cList.push([b, e]);
    }
    const newexpr = mul(...cList.map(([b, e]) => pow(b, e)));
    if (combine === 'exp') return mul(newexpr, ...ncPart);
    if (!ncPart.length) return recurse(newexpr, { combine: 'base' });
    return mul(recurse(newexpr, { combine: 'base' }), recurse(mul(...ncPart), { combine: 'base' }));
  }

  // combine === 'base'
  const ncFactors = expr.args.filter((t) => !t.isCommutative);
  let cPowers: [Expr, Expr][] = expr.args.filter((t) => t.isCommutative).map((t) => asBaseExp(t));
  cPowers = cPowers.map(([b, e]) => {
    const [n, d] = fraction(b);
    if (!((isNonNegative(n) === true && isNonNegative(d) === true) || isIntegerQ(e) === true || force)) return [b, e];
    const [c, t] = splitCoeff(e);
    if (isRat(c) && !c.isOne && !isOneE(t)) return [pow(b, c), t];
    return [b, e];
  });
  const cExp = new EMap<Expr[]>();
  for (let [b, e] of cPowers) {
    if (deep) e = recurse(e);
    if (e instanceof Add && (isPositive(b) === true || isIntegerQ(e) === true)) {
      e = factorTerms(e);
      const [c, t] = splitCoeff(e);
      if (couldExtractMinusSign(e) && c.isNegative) {
        // -e from the coefficient (-1 times the unevaluated -(i + 1) of factor_terms would stay a product 1*(i + 1))
        e = keepCoeff(mul(-1, c), t);
        b = pow(b, -1);
      }
    }
    const cur = cExp.get(e);
    if (cur) cur.push(b);
    else cExp.set(e, [b]);
  }
  const out = new EMap<Expr[]>();
  const push = (b: Expr, e: Expr) => {
    const cur = out.get(b);
    if (cur) cur.push(e);
    else out.set(b, [e]);
  };
  for (const [e, bases] of cExp.entries()) {
    let newBase: Expr;
    if (bases.length === 1) newBase = first(bases);
    else if (isIntegerQ(e) === true || force) newBase = mul(...bases);
    else {
      let unk: Expr[] = [];
      const nonneg: Expr[] = [];
      let neg: Expr[] = [];
      for (const bi of bases) {
        if (isNegative(bi) === true) neg.push(bi);
        else if (isNonNegative(bi) === true) nonneg.push(bi);
        else unk.push(bi);
      }
      if ((unk.length === 1 && !neg.length) || (neg.length === 1 && !unk.length)) {
        nonneg.push(...unk, ...neg);
        unk = [];
        neg = [];
      } else if (neg.length) {
        let israt = isRat(e);
        if (!israt) {
          const [p, d] = fraction(e);
          israt = isIntegerQ(p) === true && isIntegerQ(d) === true;
        }
        if (israt) {
          neg = neg.map((w) => mul(-1, w));
          unk.push(...neg.map(() => S.NegOne));
        } else {
          unk.push(...neg);
          neg = [];
        }
      }
      for (const b of unk) push(b, e);
      newBase = mul(...nonneg, ...neg);
      const terms = (x: Expr): number =>
        x instanceof Add ? x.args.reduce((s, a) => s + terms(a), 0) : x instanceof Mul ? x.args.reduce((p, a) => p * terms(a), 1) : 1;
      const xnew = expandMul(newBase);
      if (addArgs(xnew).length < terms(newBase)) newBase = factorTerms(xnew);
    }
    push(newBase, e);
  }
  return mul(...out.entries().flatMap(([b, es]) => es.map((ei) => pow(b, ei))), ...ncFactors);
}

const Y = new Dummy('y');

function orderedEntries<V>(xs: [Expr, V][]): [Expr, V][] {
  const keys = ordered(xs.map(([k]) => k));
  return keys.map((k) => defined(xs.find(([b]) => b.key === k.key)));
}

/** SymPy _denest_pow: denest one power. */
function denestPow(eq: Pow): Expr {
  const [b, e] = isExpPow(eq) ? [S.E, eq.exp] : [eq.base, eq.exp];
  // exp with log terms in the exponent
  if (b instanceof Constant && b.name === 'E' && e instanceof Mul) {
    const logs: Expr[] = [];
    const other: Expr[] = [];
    for (const ei of e.args) {
      if (addArgs(ei).some((ai) => ai instanceof Fn && ai.name === 'log')) logs.push(ei);
      else other.push(ei);
    }
    return pow(exp(logcombine(mul(...logs))), mul(...other));
  }
  const [, be] = asBaseExp(b);
  if (isOneE(be) && !(b instanceof Mul || (isRat(b) && b.q !== 1n) || isPositive(b) === true)) return eq;
  if (isInt(b)) {
    const logb = expand_log(log(b));
    // a perfect power: expand_log gives k*log(root)
    if (logb instanceof Mul) {
      const [c, l] = splitCoeff(logb);
      return pow(first(cast(l, Fn, 'the logarithm of the root').args), mul(e, c));
    }
  }
  if (!(b instanceof Mul) || b.args.some((s) => s.args.length === 0)) return eq;
  let glogb = expand_log(log(b));
  if (glogb instanceof Add) {
    const args = glogb.args;
    const ncGcd = (aa: Expr, bb: Expr): Expr => {
      const [ca, ma] = splitCoeff(aa);
      const [cb, mb] = splitCoeff(bb);
      const g = isRat(ca) && isRat(cb) ? Rational.of(gcdI(ca.p, cb.p)) : S.One;
      const sa = new Set(mulArgs(ma).map((x) => x.key));
      const common = mulArgs(mb).filter((x) => sa.has(x.key));
      return mul(g, ...common);
    };
    const g = args.slice(1).reduce(ncGcd, first(args));
    // the gcd stays outside the sum (SymPy _keep_coeff)
    if (!isOneE(g)) glogb = keepCoeff(g, add(...args.map((a) => mul(a, pow(g, -1)))));
  }
  // SymPy denests a power inside the logarithm here; b is a product of non-atoms, so
  // expand_log gives log(b) itself or a sum of logarithms, never the log of a power
  if ((glogb instanceof Fn && glogb.name === 'log') || !(glogb instanceof Mul)) return eq;
  const adds: Expr[] = [];
  const other: Expr[] = [];
  for (const a of glogb.args) (a instanceof Add ? adds : other).push(a);
  return pow(exp(logcombine(mul(...adds))), mul(e, ...other));
}

function gcdI(aIn: bigint, bIn: bigint): bigint {
  let a = aIn;
  let b = bIn;
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b) [a, b] = [b, a % b];
  return a;
}

/** Collect exponents on powers as assumptions allow (SymPy powdenest). */
export function powdenest(eqIn: ExprLike, opts: { force?: boolean } = {}): Expr {
  let eq = sympify(eqIn);
  if (opts.force) {
    const denestRec = (b: Expr, e: Expr): [boolean | undefined, Expr] => {
      if (!(b instanceof Pow)) return [isPositive(b), new Pow(b, e)];
      return denestRec(isExpPow(b) ? S.E : b.base, mul(b.exp, e));
    };
    const reps: [Expr, Expr][] = [];
    const visit = (p: Expr) => {
      p.args.forEach(visit);
      if (p instanceof Pow && p.base instanceof Pow) {
        const [ok, dp] = denestRec(p.base, p.exp);
        if (ok !== false) reps.push([p, dp]);
      }
    };
    visit(eq);
    if (reps.length) eq = subs(eq, new Map(reps));
    const [peq, back] = posify(eq);
    return xreplace(powdenest(peq), [...back]);
  }
  const ne = powsimp(eq);
  return transformPows(ne);
}

/** Apply denestPow top-down to powers (SymPy xreplace(Transform(...))). */
function transformPows(e: Expr): Expr {
  if (e instanceof Pow) return denestPow(e);
  if (e.args.length === 0) return e;
  const args = e.args.map(transformPows);
  return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
}

/**
 * Replace symbols that are not known to be positive with positive dummies
 * (SymPy posify). Returns the new expression and the map back.
 */
export function posify(eIn: ExprLike): [Expr, Map<Expr, Expr>] {
  const e = sympify(eIn);
  const reps: [Expr, Expr][] = [];
  const back = new Map<Expr, Expr>();
  for (const s of e.freeSymbols()) {
    if (isPositive(s) === undefined) {
      const d = new Dummy(s.name, { ...s.assumptions, positive: true });
      reps.push([s, d]);
      back.set(d, s);
    }
  }
  return [xreplace(e, reps), back];
}

/** Combine logarithms using log(x) + log(y) = log(x*y) and a*log(x) = log(x**a) (SymPy logcombine). */
export function logcombine(exprIn: ExprLike, opts: { force?: boolean } = {}): Expr {
  const force = opts.force ?? false;
  const isLog = (e: Expr): e is Fn => e instanceof Fn && e.name === 'log' && e.args.length === 1;
  // a numeric coefficient with an imaginary part is not real even when the assumptions cannot tell
  const nonReal = (a: Expr): boolean => {
    if (a.freeSymbols().size !== 0) return false;
    try {
      return a.toComplex().im !== 0;
    } catch {
      return false;
    }
  };
  // (SymPy also excludes a = -1, but negative rationals are split off before gooda is asked)
  const gooda = (a: Expr) => isReal(a) === true || (force && isReal(a) !== false && !nonReal(a));
  // (log(0) evaluates to zoo, so the argument of a logarithm is never 0)
  const goodlog = (l: Fn) => {
    const a = first(l.args);
    return isPositive(a) === true || (force && isNegative(a) !== true);
  };
  const f = (rv: Expr): Expr => {
    if (!(rv instanceof Add || rv instanceof Mul)) return rv;
    const other: Expr[] = [];
    const logs: [Expr[], Expr[], Fn[]][] = [];
    const log1 = new Map<string, { k: Expr[]; items: [Expr[], Fn][] }>();
    const put = (k: Expr[], item: [Expr[], Fn]) => {
      const key = k.map((x) => x.key).join(',');
      const cur = log1.get(key);
      if (cur) cur.items.push(item);
      else log1.set(key, { k, items: [item] });
    };
    for (const a of addArgs(rv)) {
      if (isLog(a) && goodlog(a)) put([], [[], a]);
      else if (!(a instanceof Mul)) other.push(a);
      else {
        const ot: Expr[] = [];
        const co: Expr[] = [];
        const lo: Fn[] = [];
        for (const ai of a.args) {
          if (ai instanceof Rational && ai.isNegative) {
            ot.push(S.NegOne);
            co.push(mul(-1, ai));
          } else if (isLog(ai) && goodlog(ai)) lo.push(ai);
          else if (gooda(ai)) co.push(ai);
          else ot.push(ai);
        }
        if (lo.length > 1) logs.push([ot, co, lo]);
        else if (lo.length) put(ot, [co, first(lo)]);
        else other.push(a);
      }
    }
    const only = other.length === 1 ? first(other) : undefined;
    if (only !== undefined && isLog(only)) {
      other.pop();
      put([], [[], only]);
    }
    if (!logs.length && [...log1.values()].every((v) => v.items.length === 1 && first(v.items)[0].length === 0)) return rv;
    for (const [o, e0, l0] of logs) {
      const [l1, ...lRest] = ordered(l0).map((x) => first(x.args));
      let e: Expr = log(pow(defined(l1), mul(...e0)));
      for (const li of lRest) e = log(pow(li, e));
      // a logarithm of a power of a positive (or forced) base stays a logarithm
      put([mul(...o)], [[], cast(e, Fn, 'logcombine: the combined logarithm')]);
    }
    const combined = new Map<string, [Expr, Expr, Expr]>();
    for (const { k, items } of log1.values()) {
      const kk = mul(...k);
      const inner = logcombine(mul(...items.map(([c, l]) => pow(first(l.args), mul(...c)))), opts);
      combined.set(kk.key, [kk, new Fn('log', [inner]), inner]);
    }
    for (const k of ordered([...combined.values()].map(([kk]) => kk))) {
      if (!combined.has(k.key)) continue;
      const nk = mul(-1, k);
      if (combined.has(nk.key)) {
        let num = k;
        let den = nk;
        if (countOps(num) > countOps(den)) [num, den] = [den, num];
        const a = getOrThrow(combined, num.key)[2];
        const b = getOrThrow(combined, den.key)[2];
        combined.delete(num.key);
        combined.delete(den.key);
        other.push(mul(num, new Fn('log', [mul(a, pow(b, -1))])));
      } else {
        other.push(mul(k, getOrThrow(combined, k.key)[1]));
        combined.delete(k.key);
      }
    }
    return add(...other);
  };
  const bottomUp = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const ex = expExponent(e);
    let ne: Expr;
    if (ex !== undefined) ne = exp(bottomUp(ex));
    else {
      const args = e.args.map(bottomUp);
      ne = args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
    }
    return f(ne);
  };
  return bottomUp(sympify(exprIn));
}


