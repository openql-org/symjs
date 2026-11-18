// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file series(): power series expansion with an Order term, SymPy style.
 */

import { NotImplementedError } from '../core/errors';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Fn, Order, Pow, Rational, S, Special, Sym, impl, registerArithmetic } from '../core/nodes';
import { add, exp, mul, neg, pow, sympify } from '../core/ops';
import { Mul, isMulLike } from '../core/nodes';
import { expandMul } from '../simplify/expand';
import { mapBottomUp, xreplace as subs } from '../core/traverse';
import { log, sin } from '../functions/elementary/elementary';
import { bernoulliNumber } from '../functions/special/special';
import { EssentialSingularity, Expander, type PS, isE } from './puiseux';
import { isPositive, isReal } from '../core/assumptions';
import { at, cast, first, getOrThrow } from '../core/guard';
import { parserHooks } from '../parsing/parser';
import { diffHooks } from '../calculus/diff';
import { asIndependent } from '../core/methods';

/** Array.isArray does not narrow a readonly array union. */
const isSymList = (v: Sym | readonly Sym[] | undefined): v is readonly Sym[] => Array.isArray(v);

/**
 * O(expr) for x -> x0. Like SymPy, the argument is reduced to its leading
 * power: O(x + x**2) = O(x), O(cos(x)) = O(1), O(cos(x), x, pi/2) = O(x - pi/2).
 */
export function O(ex: ExprLike, xIn?: Sym | readonly Sym[], x0: ExprLike = 0): Expr {
  const e = sympify(ex);
  if (e.equals(S.Zero)) return S.Zero;
  if (e === S.NaN) return e;
  if (e instanceof Order) {
    if (xIn === undefined) return e;
    const previous = e.args.length > 1 ? at(e.args, -1) : S.Zero;
    if (!previous.equals(sympify(x0))) throw new NotImplementedError('Order at different points');
    return O(e.expr, [...new Map([...orderVariables(e), ...(isSymList(xIn) ? xIn : [xIn])].map((v) => [v.key, v])).values()], x0);
  }
  const p = sympify(x0);
  const syms = [...e.freeSymbols()].filter((s) => s instanceof Sym);
  const vars = isSymList(xIn) ? xIn : xIn === undefined && syms.length > 1 ? (sortSyms(syms)) : undefined;
  if (vars && vars.length > 1) return orderMulti(e, vars, p);
  const x: Sym | undefined = isSymList(xIn) ? xIn[0] : xIn;
  const v = x ?? (syms.length === 1 ? syms[0] : undefined);
  const atZero = p instanceof Rational && p.isZero;
  if (v !== undefined && e instanceof Pow && e.exp.has(v) && !isE(e.base)) return O(exp(mul(e.exp, log(e.base))), v, p);
  if (v !== undefined && p instanceof Special && (p.name === 'oo' || p.name === '-oo')) {
    // leading behaviour at infinity: substitute x = 1/t, t -> 0+
    try {
      const t = new Sym('_o', { positive: true });
      // (the coefficients of an expansion are free of t)
      const expander = new Expander(t);
      const lead = expander.leading(subs(e, [[v, mul(p.name === 'oo' ? 1 : -1, pow(t, -1))]]));
      const logarithms = asIndependent(lead.c, [expander.L], { asAdd: false })[1];
      return new Order([mul(pow(v, neg(lead.e)), subs(logarithms, [[expander.L, log(pow(v, -1))]])), v, p]);
    } catch {
      if (e instanceof Add) {
        const combined = add(...e.args.map((term) => O(term, v, p)));
        if (combined instanceof Order) return combined;
      }
    }
  }
  if (v === undefined || p instanceof Special) {
    const reduced = e.freeSymbols().size === 0 ? S.One : e;
    return new Order(x === undefined || atZero ? [reduced] : [reduced, x, p]);
  }
  let reduced: Expr = e;
  try {
    const t = new Sym('_o');
    const expander = new Expander(t);
    const lead = expander.leading(subs(e, [[v, add(p, t)]]));
    const logarithms = asIndependent(lead.c, [expander.L], { asAdd: false })[1];
    const displacement = atZero ? v : add(v, mul(-1, p));
    reduced = mul(pow(displacement, lead.e), subs(logarithms, [[expander.L, log(displacement)]]));
  } catch {
    if (e instanceof Add) {
      const combined = add(...e.args.map((term) => O(term, v, p)));
      if (combined instanceof Order) return combined;
    }
  }
  return atZero && reduced.has(v) ? new Order([reduced]) : new Order([reduced, v, p]);
}

function sortSyms(xs: Sym[]): Sym[] {
  return [...xs].sort((a, b) => Number(a.name > b.name) - Number(a.name < b.name));
}

/**
 * Order term in several variables at 0 or oo: the monomials that no other one
 * dominates (has exponents at most, at 0, or at least, at oo, in every variable),
 * without their coefficients (SymPy Order: O(x**3 + y, x, y), O(x*y + x**2*y**2, x, y) = O(x*y)).
 */
function orderMulti(e: Expr, vars: readonly Sym[], p: Expr): Expr {
  const atZero = p instanceof Rational && p.isZero;
  const atOo = p instanceof Special && p.name === 'oo';
  let reduced = e;
  if (atZero || atOo) {
    const ex = expandMul(e);
    const terms = ex instanceof Add ? ex.args : [ex];
    // SymPy scales every variable by t -> 0: a power v**k whose exponent k (in the order variables, without a constant
    // term) also vanishes at 0 has the leading term 1 (O(x**y) is O(1, x, y))
    const vanishingPower = (f: Expr): boolean => atZero && f instanceof Pow && vars.some((v) => v.key === f.base.key)
      && !(f.exp instanceof Rational) && [...f.exp.freeSymbols()].every((s) => vars.some((v) => v.key === s.key))
      && subs(f.exp, vars.map((v) => [v, S.Zero] as [Expr, Expr])).equals(S.Zero);
    /** The exponents of the variables in a monomial (undefined if a variable is inside a function). */
    const degs = (t: Expr): number[] | undefined => {
      const d = vars.map(() => 0);
      for (const f of t instanceof Mul ? t.args : [t]) {
        if (vanishingPower(f)) continue;
        const [base, k] = f instanceof Pow && f.exp instanceof Rational ? [f.base, f.exp.value] : [f, 1];
        const i = vars.findIndex((v) => v.key === base.key);
        if (i >= 0) d[i] = at(d, i) + k;
        else if ([...f.freeSymbols()].filter((s) => s instanceof Sym).some((s) => vars.some((v) => v.key === s.key))) return undefined;
      }
      return d;
    };
    const ds = terms.map(degs);
    if (ds.every((d) => d !== undefined)) {
      // a dominates b near the point when a is larger there: smaller exponents at 0, larger at oo
      const dominates = (a: number[], b: number[]) => a.some((u, i) => u !== at(b, i)) && a.every((u, i) => (atZero ? u <= at(b, i) : u >= at(b, i)));
      const strip = (t: Expr) => mul(...(t instanceof Mul ? t.args : [t]).filter((f) => f.freeSymbols().size !== 0 && !vanishingPower(f)));
      reduced = add(...terms.filter((_, i) => !ds.some((o) => dominates(o, at(ds, i)))).map(strip));
    }
  }
  return new Order([reduced, ...vars, p]);
}

/**
 * Series expansion of e about x = x0 up to O((x - x0)**n). Like SymPy, an
 * exact (finite) expansion is returned without an Order term.
 */
/**
 * Series at +oo or -oo (SymPy series(f, x, oo, n)): x = sign/t with t -> 0+,
 * the expansion in t written back in x, with O(x**(-n), (x, oo)).
 */
function seriesAtInfinity(e: Expr, x: Sym, sign: 1 | -1, n: number): Expr {
  const t = new Sym('_t_inf', { positive: true });
  const st = series(subs(e, [[x, mul(sign, pow(t, -1))]]), t, 0, n);
  const back = (u: Expr) => subs(u, [[t, mul(sign, pow(x, -1))]]);
  const terms = st instanceof Add ? st.args : [st];
  const out: Expr[] = [];
  let order: Expr | undefined;
  for (const u of terms) {
    if (u instanceof Order) {
      // the Order of a series in t is O(t**k) (O(t) or O(1) for k = 1 or 0); at -oo it is written in -1/x (SymPy)
      const lead = first(u.args);
      const k = lead instanceof Pow ? lead.exp : lead.key === t.key ? S.One : S.Zero;
      order = new Order([pow(mul(sign, pow(x, -1)), k), x, sign === 1 ? S.Infinity : S.NegativeInfinity]);
    } else out.push(back(u));
  }
  if (!order) return add(...out);
  // the Order at infinity must not absorb the terms (they are larger there): smallest terms first, like SymPy
  const body = add(...out);
  const parts = (body instanceof Add ? body.args : [body]).filter((u) => !(u instanceof Rational && u.isZero));
  const deg = (u: Expr): number => {
    let d = 0;
    for (const f of u instanceof Mul ? u.args : [u]) {
      if (f.key === x.key) d += 1;
      else if (f instanceof Pow && f.base.key === x.key && f.exp instanceof Rational) d += f.exp.toNumber();
    }
    return d;
  };
  parts.sort((a, b) => deg(a) - deg(b));
  return new Add([...parts, order]);
}

export function series(ex: ExprLike, x: Sym, x0x: ExprLike = 0, n = 6, dir: '+' | '-' = '+', opts: { logx?: Expr } = {}): Expr {
  // sinc(u) = sin(u)/u has a removable singularity at u = 0
  let e = mapBottomUp(sympify(ex), (t) => {
    if (!(t instanceof Fn && t.name === 'sinc')) return t;
    const u = first(t.args);
    return mul(sin(u), pow(u, -1));
  });
  const x00 = sympify(x0x);
  const atZero = x00 instanceof Rational && x00.isZero;
  if (opts.logx && atZero) {
    // SymPy logx: log(x) stands for the given symbol; x**c = exp(c*log(x)) for symbolic c
    e = mapBottomUp(e, (t) => (t instanceof Pow && t.base.key === x.key && !(t.exp instanceof Rational) && !t.exp.has(x) ? exp(mul(t.exp, log(x))) : t));
    e = subs(e, [[log(x), opts.logx]]);
    if (!e.has(x)) return e;
  }
  // x**c with symbolic c is its own expansion at 0
  if (atZero && e instanceof Pow && e.base.key === x.key && !(e.exp instanceof Rational) && !e.exp.has(x)) return e;
  const x0 = sympify(x0x);
  if (x0 instanceof Special && (x0.name === 'oo' || x0.name === '-oo')) return seriesAtInfinity(e, x, x0.name === 'oo' ? 1 : -1, n);
  // at zoo SymPy substitutes x = sign(zoo)/x: only a Laurent polynomial in x comes back as it is
  // (series(x, x, zoo) = x); other expansions there are not defined
  if (x0 instanceof Special && x0.name === 'zoo' && isLaurentPolynomial(e, x)) return e;
  if (x0 instanceof Special) throw new NotImplementedError('series: expansion at this point is not supported');
  if (!e.has(x)) return e;
  const t = new Sym('_s', { positive: true });
  const ex0 = new Expander(t);
  // from the left: x = x0 - t with t -> 0+, written in powers of (x0 - x)
  const shifted = subs(e, [[x, dir === '-' ? add(x0, mul(-1, t)) : add(x0, t)]]);
  if (n < 0) throw new RangeError('series: the order n must be nonnegative');
  // the expansion variable is positive (SymPy series): oo*x is oo there
  if (!shifted.has(t)) return shifted;
  // (expanded to at least the order 1 and then truncated: series(sin(x), x, 0, 0) = O(1))
  let ps: PS;
  try {
    ps = ex0.ser(shifted, Rational.of(Math.max(n, 1))).truncate(Rational.of(n));
  } catch (err) {
    // exp(g) with g -> oo (or of unknown sign) has no expansion: SymPy returns it unchanged, but
    // raises PoleError for a complex g (exp(I/x))
    if (err instanceof EssentialSingularity && e instanceof Pow && isE(e.base) && isReal(err.coeff) !== false) return e;
    if (err instanceof EssentialSingularity) return essentialSeries(e, x, x0, n, dir, err);
    throw err;
  }
  const base = dir === '-' ? add(x0, mul(-1, x)) : x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  const back = (c: Expr) => subs(c, [[ex0.L, log(base)]]);
  const terms = ps.terms.map((term) => mul(back(term.c), pow(base, term.e)));
  const body = add(...terms);
  if (ps.order.value >= 1e5) return body;
  const lin = x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  let remainder = pow(lin, ps.order);
  if (ps.terms.some((term) => term.c.has(ex0.L))) {
    const boundary = ex0.ser(shifted, Rational.of(ps.order.p + ps.order.q, ps.order.q)).terms.find((term) => term.e.equals(ps.order));
    if (boundary?.c.has(ex0.L)) {
      let logarithms = asIndependent(boundary.c, [ex0.L], { asAdd: false })[1];
      if (logarithms instanceof Pow && logarithms.exp instanceof Rational) {
        if (logarithms.exp.isNegative) logarithms = S.One;
        else if (e instanceof Pow && isE(e.base) && e.exp.has(x)) logarithms = pow(ex0.L, Math.max(n, logarithms.exp.value));
      }
      remainder = mul(remainder, back(logarithms));
    }
  }
  const ord = x0 instanceof Rational && x0.isZero ? new Order([remainder]) : new Order([remainder, x, x0]);
  return add(body, ord);
}

/** A sum of terms c*x**k with c free of x and integers k. */
function isLaurentPolynomial(e: Expr, x: Sym): boolean {
  const monomial = (f: Expr): boolean => !f.has(x) || f.key === x.key || (f instanceof Pow && f.base.key === x.key && f.exp instanceof Rational && f.exp.isInteger);
  return (e instanceof Add ? e.args : [e]).every((t) => (t instanceof Mul ? t.args : [t]).every(monomial));
}

/**
 * The series of a sum of terms with factors exp(g) (or b**g) where g -> +oo on the side of approach:
 * like SymPy, those factors are kept as they are and multiply the series of the rest
 * (series(x*exp(1/x), x) = x*exp(1/x); series(exp(1/x)*sin(x), x) = x*exp(1/x) - x**3*exp(1/x)/6 + ... +
 * O(x**6*exp(1/x))). The error of the expansion is raised again when no term has such a factor.
 */
function essentialSeries(e: Expr, x: Sym, x0: Expr, n: number, dir: '+' | '-', err: EssentialSingularity): Expr {
  // the exponent of exp(g), or g*log(b) for b**g (in SymPy b**g is exp(g*log(b)): 2**(1/x) -> exp(log(2)/x))
  const exponent = (f: Expr): Expr | undefined => {
    if (!(f instanceof Pow && f.exp.has(x) && (isE(f.base) || (f.base.freeSymbols().size === 0 && isPositive(f.base))))) return undefined;
    const g = isE(f.base) ? f.exp : mul(f.exp, log(f.base));
    // (g -> oo, or to an infinity of unknown real direction (y/x -> oo*sign(y)), which SymPy keeps too)
    const l = impl.limit(g, x, x0, dir);
    const kept = (l instanceof Special && l.name === 'oo') || (l instanceof Mul && l.has(S.Infinity) && isReal(g) !== false && l.args.some((a) => a instanceof Fn && a.name === 'sign'));
    return kept ? g : undefined;
  };
  const ex = expandMul(e);
  const terms = (ex instanceof Add ? ex.args : [ex]).map((term) => {
    const factors = term instanceof Mul ? term.args : [term];
    return { term, factors, gs: factors.map(exponent) };
  });
  if (terms.every(({ gs }) => gs.every((g) => g === undefined))) throw err;
  const out: Expr[] = [];
  for (const { term, factors, gs } of terms) {
    if (gs.every((g) => g === undefined)) {
      out.push(series(term, x, x0, n, dir));
      continue;
    }
    const E = exp(add(...gs.filter((g) => g !== undefined)));
    const rest = series(mul(...factors.filter((_, i) => gs[i] === undefined)), x, x0, n, dir);
    for (const u of rest instanceof Add ? rest.args : [rest]) out.push(u instanceof Order ? new Order([mul(first(u.args), E), ...u.args.slice(1)]) : mul(u, E));
  }
  return add(...out);
}

impl.series = series;
impl.leadterm = (e, x) => leadterm(e, x);

/** Leading term c*x**e of e as x -> 0 (SymPy leadterm): [c, e]. */
export function leadterm(ex: ExprLike, x: Sym): [Expr, Expr] {
  const e = sympify(ex);
  if (isMulLike(e) && !(e instanceof Mul)) {
    // a matrix product x*A with constant matrix factors: the leading term of the scalar coefficient
    // times the matrices (SymPy (x*A).as_leading_term(x) = x*A; its leadterm fails with a TypeError)
    const scalars = e.args.filter((f) => f.isCommutative);
    const matrices = e.args.filter((f) => !f.isCommutative);
    if (matrices.some((f) => f.has(x))) throw new NotImplementedError(`leading term of ${e.toString()}, whose matrix factors depend on ${x.name}`);
    const [c, p] = leadterm(mul(...scalars), x);
    return [mul(c, ...matrices), p];
  }
  // powers of x to constant exponents that are not rational (x**(-sqrt(2))) are factored out: the
  // expansion of the rest is a Puiseux series (SymPy: leadterm(x**(1 - sqrt(2))) = (1, 1 - sqrt(2)))
  const factors = e instanceof Mul ? e.args : [e];
  const irrational = (f: Expr): f is Pow => f instanceof Pow && f.base.key === x.key && !(f.exp instanceof Rational) && !f.exp.has(x);
  const powers = factors.filter(irrational);
  if (powers.length === 0) return leadtermExact(e, x);
  const [c, p] = leadtermExact(mul(...factors.filter((f) => !irrational(f))), x);
  return [c, add(p, ...powers.map((f) => f.exp))];
}

/** leadterm with the exponent typed as the Rational it always is. */
function leadtermExact(ex: ExprLike, x: Sym): [Expr, Rational] {
  const e = sympify(ex);
  if (!e.has(x)) return [e, S.Zero];
  const t = new Sym('_s');
  const exp0 = new Expander(t);
  const l = exp0.leading(subs(e, [[x, t]]));
  const c = subs(l.c, [[exp0.L, log(x)]]);
  return [c, l.e];
}

/**
 * Leading terms of functions that depend on the side of approach (SymPy
 * _eval_as_leading_term with cdir): the function, the variable and the
 * direction; undefined leaves the generic expansion.
 */
export const leadingTermRules: Partial<Record<string, (e: Fn, x: Sym, cdir: Expr) => Expr | undefined>> = {};

/**
 * SymPy as_leading_term(x, cdir=...): the leading term as x -> 0 from the direction cdir (0 when
 * not given: the side does not matter, or x approaches 0 from above).
 */
export function asLeadingTerm(ex: ExprLike, x: Sym, opts: { cdir?: ExprLike; logx?: ExprLike } = {}): Expr {
  const e = sympify(ex);
  const rule = e instanceof Fn ? leadingTermRules[e.name] : undefined;
  const special = rule?.(cast(e, Fn, 'function'), x, sympify(opts.cdir ?? 0));
  let result: Expr;
  if (special !== undefined) result = special;
  else if (e instanceof Mul) result = mul(...e.args.map((a) => asLeadingTerm(a, x, opts)));
  else {
    const ray = sympify(opts.cdir ?? 1);
    if (ray instanceof Rational && (ray.isZero || ray.key === S.One.key)) {
      const [c, p] = leadterm(e, x);
      result = mul(c, pow(x, p));
    } else {
      if (isReal(ray) !== true) throw new NotImplementedError('leading term in a nonreal direction');
      const t = new Sym('_leading', { positive: true });
      const [c, p] = leadterm(subs(e, [[x, mul(ray, t)]]), t);
      result = expandMul(subs(mul(c, pow(t, p)), [[log(t), add(log(x), neg(log(ray)))], [t, mul(x, pow(ray, -1))]]));
    }
  }
  return opts.logx === undefined ? result : subs(result, [[log(x), sympify(opts.logx)]]);
}

/** Order of the O term in a sum, or undefined (SymPy getn). */
export function getn(ex: ExprLike): Expr | undefined {
  const e = sympify(ex);
  const o = (e instanceof Add ? e.args : [e]).find((a) => a instanceof Order);
  if (!o) return undefined;
  // SymPy Order.getn: O(1) -> 0, O(x) -> 1, O(x**n) -> n, O(x**n*log(x)**m) -> |n|
  const b = first(o.args);
  if (b instanceof Rational) return S.Zero;
  if (b instanceof Sym) return S.One;
  if (b instanceof Pow) return b.exp;
  if (b instanceof Mul) {
    for (const f of b.args) {
      if (f instanceof Sym) return S.One;
      if (f instanceof Pow && f.base instanceof Sym && f.exp instanceof Rational) return f.exp.isNegative ? neg(f.exp) : f.exp;
    }
  }
  throw new NotImplementedError(`not sure of order of ${b.toString()}`);
}


/** Leading terms of a sum as x -> 0 with their order terms (SymPy extract_leading_order). */
export function extractLeadingOrder(ex: ExprLike, x: Sym): [Expr, Expr][] {
  const e = sympify(ex);
  const terms = e instanceof Add ? e.args : [e];
  const orders = terms.map((t) => leadtermExact(t, x)[1]);
  const minO = orders.reduce((m, o) => (o.value < m.value ? o : m));
  return terms.filter((_, i) => orders[i]?.key === minO.key).map((t) => [t, O(t, x)]);
}

const factorialOf = (n: number): bigint => {
  let f = 1n;
  for (let i = 2n; i <= BigInt(n); i++) f *= i;
  return f;
};

/** (1/2)_k*n/(k!*k**2)*x**n/4 with k = n/2: the coefficient shared by the asec, acsc, asech and acsch series. */
function halfRisingTerm(n: number, x: Expr): Expr {
  const k = n / 2;
  // (1/2)_k = 1*3*...*(2k - 1)/2**k
  let odd = 1n;
  for (let i = 0; i < k; i++) odd *= BigInt(2 * i + 1);
  return mul(Rational.of(odd * BigInt(n), (1n << BigInt(k)) * factorialOf(k) * BigInt(k * k) * 4n), pow(x, n));
}

/**
 * The n-th term of the series at 0 of functions without a Maclaurin series, in the form SymPy's
 * taylor_term gives it (Laurent terms of cot and csc, the log term of asec, acsc, asech, acsch).
 */
const SERIES_TERMS: Readonly<Record<string, (n: number, x: Expr) => Expr>> = {
  cot: (n, x) => n === 0 ? pow(x, -1) : n < 0 || n % 2 === 0 ? S.Zero
    : mul((n + 1) % 4 === 0 ? 1 : -1, pow(2, n + 1), bernoulliNumber(n + 1), Rational.of(1n, factorialOf(n + 1)), pow(x, n)),
  csc: (n, x) => {
    if (n === 0) return pow(x, -1);
    if (n < 0 || n % 2 === 0) return S.Zero;
    const k = (n - 1) / 2 + 1;
    return mul(k % 2 === 1 ? 1 : -1, 2, add(pow(2, 2 * k - 1), -1), bernoulliNumber(2 * k), pow(x, 2 * k - 1), Rational.of(1n, factorialOf(2 * k)));
  },
  log: (n, x) => n < 0 ? S.Zero : mul(Rational.of(n % 2 === 0 ? 1 : -1, n + 1), pow(x, n + 1)),
  asec: (n, x) => n === 0 ? mul(S.I, log(mul(2, pow(x, -1)))) : n < 0 || n % 2 === 1 ? S.Zero : mul(neg(S.I), halfRisingTerm(n, x)),
  acsc: (n, x) => n === 0 ? add(mul(S.Pi, S.Half), mul(neg(S.I), log(2)), mul(S.I, log(x))) : n < 0 || n % 2 === 1 ? S.Zero : mul(S.I, halfRisingTerm(n, x)),
  asech: (n, x) => n === 0 ? log(mul(2, pow(x, -1))) : n < 0 || n % 2 === 1 ? S.Zero : neg(halfRisingTerm(n, x)),
  acsch: (n, x) => n === 0 ? log(mul(2, pow(x, -1))) : n < 0 || n % 2 === 1 ? S.Zero : mul((n / 2) % 2 === 1 ? 1 : -1, halfRisingTerm(n, x)),
};

/**
 * SymPy Expr.taylor_term(n, x): the n-th term of the Maclaurin series, f^(n)(0)*x**n/n!; for cot,
 * csc, asec, acsc, asech and acsch of x the n-th term of their series at 0.
 * For log(x), SymPy's class convention gives the n-th term of log(1 + x).
 */
export function taylorTerm(eIn: ExprLike, n: number, x: Sym): Expr {
  const e = sympify(eIn);
  const special = e instanceof Fn && e.args.length === 1 && first(e.args).key === x.key ? SERIES_TERMS[e.name] : undefined;
  if (special !== undefined) return special(n, x);
  return mul(subs(impl.diff(e, x, n), [[x, S.Zero]]), pow(x, n), Rational.of(1n, factorialOf(n)));
}

/**
 * SymPy Expr.aseries(x, n, hir): asymptotic expansion at x -> oo in the most
 * rapidly varying decaying exponential w = exp(-b*x). Without hir only the
 * leading term in w is kept and its coefficient is expanded in 1/x; with hir
 * the terms up to w**n. Expressions without exponentials give their series
 * at infinity; growing exponentials are returned unchanged.
 */
export function aseries(ex: ExprLike, x: Sym, n = 6, hir = false): Expr {
  const e = sympify(ex);
  const rates: Rational[] = [];
  let growing = false as boolean; // set inside a callback
  let other = false as boolean;
  const walk = (u: Expr) => {
    if (u instanceof Pow && u.base === S.E && u.exp.has(x)) {
      const c = expandMul(mul(u.exp, pow(x, -1)));
      if (c instanceof Rational) {
        if (c.isPositive) growing = true;
        else rates.push(c);
      } else other = true;
    }
    u.args.forEach(walk);
  };
  walk(e);
  if (growing || other) return e;
  if (!rates.length) return series(e, x, S.Infinity, n);
  // the slowest decay
  const b = first([...rates].sort((r, u) => Math.abs(r.toNumber()) - Math.abs(u.toNumber())));
  const w = new Sym('_w_as', { positive: true });
  // exp(c*x) = w**(c/b)
  const replaced = mapBottomUp(e, (u) => (u instanceof Pow && u.base === S.E && u.exp.has(x) ? pow(w, mul(expandMul(mul(u.exp, pow(x, -1))), pow(b, -1))) : u));
  const sw = series(replaced, w, 0, hir ? n : 3);
  const terms = sw instanceof Add ? sw.args : [sw];
  const byPower = new Map<number, Expr[]>();
  for (const t of terms) {
    if (t instanceof Order) continue;
    let k = 0;
    const cs: Expr[] = [];
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f.key === w.key) k += 1;
      else if (f instanceof Pow && f.base.key === w.key && f.exp instanceof Rational) k += f.exp.toNumber();
      else cs.push(f);
    }
    byPower.set(k, [...(byPower.get(k) ?? []), mul(...cs)]);
  }
  const ks = [...byPower.keys()].sort((a, c) => a - c);
  if (!ks.length) return e;
  const wx = (k: number) => exp(mul(k, b, x));
  if (!hir) {
    const k = first(ks);
    const coeff = series(add(...getOrThrow(byPower, k)), x, S.Infinity, n);
    return mul(coeff, wx(k));
  }
  const parts = ks.filter((k) => k < n).sort((a, c) => c - a).map((k) => mul(add(...getOrThrow(byPower, k)), wx(k)));
  return new Add([...parts, new Order([wx(n), x, S.Infinity])]);
}

// the parser reduces O(...) to its leading term with this O (parse('O(x + x**2)') = O(x), as in SymPy)
parserHooks.order = (e, vars, p) => O(e, vars.length ? vars : undefined, p);
// and the derivative of an Order (diff(O(x**2), x) = O(x))
diffHooks.order = parserHooks.order;

/** Expansion variables, including those absent from a constant leading term. */
function orderVariables(o: Order): Sym[] {
  return o.args.length > 1 ? o.args.slice(1, -1).filter((v): v is Sym => v instanceof Sym) : [...o.expr.freeSymbols()].filter((s) => s instanceof Sym);
}

impl.orderContains = (o, e) => {
  let variables = orderVariables(o);
  const point = o.args.length > 1 ? at(o.args, -1) : S.Zero;
  const other = e instanceof Order ? e.expr : e;
  const otherVariables = e instanceof Order ? orderVariables(e) : [...e.freeSymbols()].filter((s) => s instanceof Sym);
  if (other.has(S.NaN)) return false;
  if (!variables.length && other.freeSymbols().size > 0) variables = otherVariables;
  if (e instanceof Order && variables.length && otherVariables.length && !variables.some((v) => otherVariables.some((w) => w.equals(v)))) return 'unknown';
  if (!variables.length && otherVariables.length) return false;
  if (e instanceof Order && e.args.length > 1 && !at(e.args, -1).equals(point)) return 'unknown';
  if (other.equals(S.Zero)) return true;
  if (o.expr.equals(S.Zero)) return false;
  if (!variables.length) return ![S.Infinity, S.NegativeInfinity, S.ComplexInfinity].some((v) => other.has(v));
  let result: boolean | 'unknown' = 'unknown';
  for (const variable of variables) {
    const ratio = impl.limit(mul(o.expr, pow(other, -1)), variable, point, '+');
    if (ratio.has(S.NaN) || ratio.kind === 'Limit') return 'unknown';
    const contained = !ratio.equals(S.Zero);
    if (result !== 'unknown' && result !== contained) return 'unknown';
    result = contained;
  }
  return result;
};

registerArithmetic((op, args) => {
  if (op === 'pow') {
    const [base, exponent] = [at(args, 0), at(args, 1)];
    if (!(base instanceof Order) || !(exponent instanceof Rational) || !exponent.isPositive) return undefined;
    return O(pow(base.expr, exponent), orderVariables(base), base.args.length > 1 ? at(base.args, -1) : S.Zero);
  }
  const flat = op === 'add' ? args.flatMap((a) => a instanceof Add ? [...a.args] : [a]) : args;
  if (op === 'add' && flat.some((a) => a instanceof Order && a.expr.equals(S.Zero))) return add(...flat.filter((a) => !(a instanceof Order && a.expr.equals(S.Zero))));
  const orders = flat.filter((a): a is Order => a instanceof Order);
  if (!orders.length) return undefined;
  if (op === 'add') {
    const kept: Order[] = [];
    const contains = (o: Order, e: Expr): boolean => {
      if (o.key === e.key) return true;
      const variables = orderVariables(o);
      const other = e instanceof Order ? orderVariables(e) : [...e.freeSymbols()].filter((s): s is Sym => s instanceof Sym);
      const query = variables.length === 0 && o.args.length === 1 ? new Order([o.expr, ...other, S.Zero]) : o;
      return query.contains(e) === true;
    };
    for (const o of orders) {
      if (kept.some((other) => contains(other, o))) continue;
      for (let i = kept.length - 1; i >= 0; i--) if (contains(o, at(kept, i))) kept.splice(i, 1);
      kept.push(o);
    }
    const body = add(...flat.filter((e) => !(e instanceof Order) && !kept.some((o) => contains(o, e))));
    const terms = body.equals(S.Zero) ? [] : body instanceof Add ? [...body.args] : [body];
    return terms.length + kept.length === 1 ? first([...terms, ...kept]) : new Add([...terms, ...kept]);
  }
  if (op !== 'mul') return undefined;
  const point = (o: Order): Expr => o.args.length > 1 ? at(o.args, -1) : S.Zero;
  const p = point(first(orders));
  if (orders.some((o) => !point(o).equals(p))) return undefined;
  const variables = [...new Map(orders.flatMap(orderVariables).map((v) => [v.key, v])).values()];
  return O(mul(...args.map((a) => a instanceof Order ? a.expr : a)), variables, p);
});
