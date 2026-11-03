// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rational-function manipulation: fraction, together, cancel.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, Fn, impl, Mul, Pow, Rational, S, Sym, isNum } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { freeSymbols, rebuild, xreplace } from '../core/traverse';
import { str } from '../printing/str';
import { divExact, mgcd } from '../polys/mpoly';
import { UPoly, polyHooks } from '../polys/poly';
import { expandMul as expand } from './expand';
import { isNegative, isPositive } from '../core/assumptions';
import { at, defined, first } from '../core/guard';
import { decomposePower } from './exprtools';

const negExponent = (x: Expr): boolean => {
  // SymPy fraction: exponents known to be negative go to the denominator
  if (isNegative(x) === true) return true;
  if (isPositive(x) === true) return false;
  const [c] = splitCoeff(x);
  return c.isNegative;
};

/** Split e into [numerator, denominator]. */
export function fraction(ex: ExprLike, opts: { exact?: boolean } = {}): [Expr, Expr] {
  const e = sympify(ex);
  const factors = e instanceof Mul ? e.args : [e];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const f of factors) {
    if (f instanceof Rational) {
      num.push(Rational.of(f.p));
      den.push(Rational.of(f.q));
    } else if (opts.exact && f instanceof Pow) {
      // SymPy exact=True: only exponents known to be negative, symbolic ones stay in the numerator
      const ex = f.exp;
      const negative = ex instanceof Rational ? ex.isNegative : isNegative(ex) === true;
      if (negative && ex instanceof Rational && ex.p === -1n && ex.q === 1n) den.push(f.base);
      else if (negative && ex.freeSymbols().size === 0) den.push(pow(f.base, mul(-1, ex)));
      else num.push(f);
    } else if (f instanceof Pow && negExponent(f.exp)) {
      den.push(pow(f.base, mul(-1, f.exp)));
    } else {
      num.push(f);
    }
  }
  if (opts.exact) {
    // SymPy Mul(*numer, evaluate=not exact): the factors as they are (2*(x + 1) stays)
    const raw = (xs: Expr[]): Expr => {
      const ys = xs.filter((y) => !(y instanceof Rational && y.p === 1n && y.q === 1n));
      return ys.length === 0 ? Rational.of(1n) : ys.length === 1 ? first(ys) : new Mul(ys);
    };
    return [raw(num), raw(den)];
  }
  return [mul(...num), mul(...den)];
}

/** Combine a sum of fractions over a common denominator (recursively). */
export function together(ex: ExprLike, opts: { deep?: boolean } = {}): Expr {
  const deep = opts.deep ?? false;
  // SymPy _together: gcd_terms over the recursively combined terms of every sum
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const isExp = e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
    if ((e instanceof Fn || isExp) && !deep) return e;
    // (registered by simplify/exprtools, which every entry point that loads this module loads)
    if (e instanceof Add) return defined(impl.gcdTermsOf?.(e.args.map(go)), 'impl.gcdTermsOf (simplify/exprtools)');
    if (e instanceof Pow) return pow(go(e.base), deep ? go(e.exp) : e.exp);
    const args = e.args.map(go);
    return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
  };
  return go(sympify(ex));
}

/**
 * Put e into the form p/q with expanded p, q and cancel common factors.
 * Polynomial GCD cancellation is performed for univariate rational functions.
 */
/** sqrt(g) times a sum: the square root of the gcd of the integer radicands of every term. */
function radicalContent(e: Expr): [Expr, Expr] | undefined {
  if (!(e instanceof Add)) return undefined;
  let g = 0n;
  const gcd = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcd(b, a % b));
  for (const t of e.args) {
    let radicand: bigint | undefined;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Pow && f.base instanceof Rational && f.base.q === 1n && f.exp instanceof Rational && f.exp.p === 1n && f.exp.q === 2n) {
        radicand = f.base.p;
        break;
      }
    }
    if (radicand === undefined) return undefined;
    g = gcd(g, radicand);
  }
  if (g <= 1n) return undefined;
  const sg = pow(Rational.of(g), Rational.of(1n, 2n));
  return [sg, expand(mul(e, pow(sg, -1)))];
}

function radicalContentRatio(n: Expr, d: Expr): Expr | undefined {
  const a = radicalContent(n);
  const b = radicalContent(d);
  if (!a || !b || a[1].key !== b[1].key) return undefined;
  // (registered by simplify/sqrtdenest, which every entry point that loads this module loads)
  return defined(impl.radsimp?.(mul(a[0], pow(b[0], -1))), 'impl.radsimp (simplify/sqrtdenest)');
}

/** Symbols ordered by name (a Dummy and a Symbol may share one). */
const byName = (a: Sym, b: Sym): number => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0);

export function cancel(ex: ExprLike): Expr {
  const e = together(sympify(ex));
  let [n, d] = fraction(e);
  n = expand(n);
  d = expand(d);
  if (d instanceof Rational && d.isOne) return n;
  // a common square root content: (sqrt(3) + sqrt(15)*A)/(sqrt(2) + sqrt(10)*A) = sqrt(6)/2
  const rc = radicalContentRatio(n, d);
  if (rc) return rc;
  const syms = new Map<string, Sym>();
  for (const s of [...freeSymbols(n), ...freeSymbols(d)]) syms.set(s.key, s);
  if (syms.size === 1) {
    const x = first([...syms.values()]);
    const pn = UPoly.fromExpr(n, x);
    const pd = UPoly.fromExpr(d, x);
    if (pn && pd) {
      const g = pn.gcd(pd);
      let qn = g.degree > 0 ? pn.divmod(g)[0] : pn;
      let qd = g.degree > 0 ? pd.divmod(g)[0] : pd;
      // normalize: monic denominator
      const lc = qd.lc;
      qn = qn.scale(Rational.of(lc.q, lc.p));
      qd = qd.scale(Rational.of(lc.q, lc.p));
      if (qd.degree === 0) return qn.toExpr(x);
      return mul(qn.toExpr(x), pow(qd.toExpr(x), -1));
    }
  }
  if (isNum(d)) return expand(mul(n, pow(d, -1)));
  if (syms.size > 1) {
    const vars = [...syms.values()].sort(byName);
    try {
      const g = mgcd(n, d, vars);
      if (!(g instanceof Rational)) {
        // g divides both (a failure is caught below and leaves the fraction as it is)
        const nn = defined(divExact(n, g, vars), 'exact quotient');
        const dd = defined(divExact(d, g, vars), 'exact quotient');
        n = nn;
        d = dd;
      }
    } catch {
      // not polynomial: keep as is
    }
    if (d instanceof Rational) return expand(mul(n, pow(d, -1)));
  }
  // SymPy's cancel normalizes the leading coefficient of the denominator (lex order of the
  // generators): positive, or for a Gaussian coefficient in the first quadrant
  const u = leadingUnit(d, ratsimpGens([n, d]));
  if (u !== undefined) [n, d] = [expand(mul(u, n)), expand(mul(u, d))];
  return mul(n, pow(d, -1));
}

/** The expanded polynomial e with each generator power gens[i]**k written as dummies[i]**k. */
function inGens(e: Expr, gens: readonly Expr[], dummies: readonly Expr[]): Expr {
  return add(
    ...(e instanceof Add ? e.args : [e]).map((t) =>
      mul(
        ...(t instanceof Mul ? t.args : [t]).map((f) => {
          const [b, k] = decomposePower(f);
          const i = gens.findIndex((g) => g.key === b.key);
          return i < 0 ? f : pow(at(dummies, i), k);
        }),
      ),
    ),
  );
}

/**
 * The unit (-1, I or -I) that moves the coefficient of the lex-leading term of the expanded
 * polynomial d into the first quadrant (re > 0, im >= 0); undefined when it is there already.
 */
function leadingUnit(d: Expr, gens: readonly Expr[]): Expr | undefined {
  // the coefficients of the monomials (terms that differ by I share one)
  const coeffs = new Map<string, [number[], Expr]>();
  for (const t of d instanceof Add ? d.args : [d]) {
    const m = gens.map(() => 0);
    let c: Expr = Rational.of(1n);
    for (const f of t instanceof Mul ? t.args : [t]) {
      const [b, k] = decomposePower(f);
      const i = gens.findIndex((g) => g.key === b.key);
      if (i < 0) c = mul(c, f);
      else m[i] = at(m, i) + k;
    }
    const cur = coeffs.get(m.join(','));
    coeffs.set(m.join(','), [m, cur ? add(cur[1], c) : c]);
  }
  let best: [number[], Expr] | undefined;
  for (const mc of coeffs.values()) if (best === undefined || lexGreater(mc[0], best[0])) best = mc;
  const { re, im } = defined(best, 'a term of the denominator')[1].toComplex();
  // (the coefficient is a nonzero number: a product of numbers and I)
  if (re > 0 && im >= 0) return undefined;
  if (re <= 0 && im > 0) return mul(-1, S.I);
  if (re < 0 && im <= 0) return S.NegOne;
  return S.I;
}

/** a > b in lex order (for distinct monomials a and b). */
const lexGreater = (a: readonly number[], b: readonly number[]): boolean =>
  a.reduce<boolean | undefined>((r, v, i) => r ?? (v !== at(b, i) ? v > at(b, i) : undefined), undefined) === true;

impl.fraction = (e) => fraction(e);

/** SymPy ratsimp: polynomial part plus a cancelled remainder over a single denominator. */
export function ratsimp(ex: ExprLike): Expr {
  const c = cancel(sympify(ex));
  const [f, g] = fraction(c);
  if (!g.freeSymbols().size) return c;
  // the generators of the polynomials in SymPy's order (symbols, functions, radicals, ...): those
  // that are not symbols are divided as dummies
  const [fe, ge] = [expand(f), expand(g)];
  const gens = ratsimpGens([fe, ge]);
  const dummies = gens.map((x) => (x instanceof Sym ? x : new Dummy('g')));
  const back = gens.map((x, i): [Expr, Expr] => [at(dummies, i), x]).filter(([d, x]) => x !== d);
  // multivariate division of f by g in lex order (registered by polys/groebner, which the
  // simplify entry point and the root entry point, the ones that export ratsimp, load)
  const [q, r] = defined(impl.polyReduce?.(inGens(fe, gens, dummies), inGens(ge, gens, dummies), dummies), 'impl.polyReduce (polys/groebner)').map((e) => xreplace(e, back));
  return add(defined(q), cancel(mul(defined(r), pow(g, -1))));
}

// SymPy _sort_gens: single letters in the order x, y, z, p..w, a..o, then everything else by name
const GENS_ORDER: Record<string, number> = {
  a: 301, b: 302, c: 303, d: 304, e: 305, f: 306, g: 307, h: 308, i: 309, j: 310, k: 311, l: 312, m: 313,
  n: 314, o: 315, p: 216, q: 217, r: 218, s: 219, t: 220, u: 221, v: 222, w: 223, x: 124, y: 125, z: 126,
};
const genKey = (g: Expr): [number, string, number] => {
  // (the pattern matches every string)
  const m = defined(/^(.*?)(\d*)$/.exec(str(g)), 'generator name');
  const name = at(m, 1);
  const digits = at(m, 2);
  return [GENS_ORDER[name] ?? 1000, name, digits ? Number(digits) : 0];
};

/** The generators of expanded polynomials (SymPy _dict_from_expr_no_gens), sorted as SymPy does. */
function ratsimpGens(es: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  for (const e of es) {
    for (const t of e instanceof Add ? e.args : [e]) {
      for (const f of t instanceof Mul ? t.args : [t]) {
        if (isNum(f) || (f instanceof Constant && f.name === 'I')) continue;
        const b = decomposePower(f)[0];
        gens.set(b.key, b);
      }
    }
  }
  return [...gens.values()].sort((a, b) => {
    const [a0, a1, a2] = genKey(a);
    const [b0, b1, b2] = genKey(b);
    return a0 !== b0 ? a0 - b0 : a1 !== b1 ? (a1 < b1 ? -1 : 1) : a2 - b2;
  });
}

polyHooks.cancel = (e) => cancel(e);
