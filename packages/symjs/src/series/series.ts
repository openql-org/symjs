// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file series(): power series expansion with an Order term, SymPy style.
 */

import { NotImplementedError, PoleError } from '../core/errors';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, Derivative, ExtensionExpr, Float, Integral, Fn, Limit, Order, Piecewise, Pow, Rational, S, Special, Sym, impl, registerArithmetic } from '../core/nodes';
import { add, exp, mul, neg, pow, sympify } from '../core/ops';
import { Mul, isMulLike } from '../core/nodes';
import { expandMul } from '../simplify/expand';
import { mapBottomUp, some, substitutionHooks, xreplace as subs } from '../core/traverse';
import { cos, fn, im, infiniteForm, log, sin } from '../functions/elementary/elementary';
import { bernoulliNumber } from '../functions/special/special';
import { besselLocalExpansion } from '../functions/special/bessel';
import { EssentialSingularity, Expander, SeriesError, type PS, isE } from './puiseux';
import { isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import { at, cast, first, getOrThrow, last } from '../core/guard';
import { parserHooks } from '../parsing/parser';
import { diffHooks } from '../calculus/diff';
import { DefinedFunctionCall } from '../core/defun';
import { SubsNode } from '../core/subsnode';
import { powsimp } from '../simplify/powsimp';
import { together } from '../simplify/rational';
import { Gruntz } from './gruntz';
import { asIndependent } from '../core/methods';
import { AccumBounds, AccumBoundsNode } from '../core/accumbounds';

/** Array.isArray does not narrow a readonly array union. */
const isSymList = (v: Sym | readonly Sym[] | undefined): v is readonly Sym[] => Array.isArray(v);

/**
 * O(expr) for x -> x0. Like SymPy, the argument is reduced to its leading
 * power: O(x + x**2) = O(x), O(cos(x)) = O(1), O(cos(x), x, pi/2) = O(x - pi/2).
 */
export function O(ex: ExprLike, xIn?: Sym | readonly Sym[], x0: ExprLike = 0): Expr {
  const e = mapBottomUp(sympify(ex), (v) => v instanceof Integral && impl.doit ? impl.doit(v) : v);
  if (isSymList(xIn) && new Set(xIn.map((v) => v.key)).size !== xIn.length) throw new RangeError('Repeated order variable');
  if (e.equals(S.Zero)) return new Order([e]);
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
    if (e instanceof Mul) {
      const factors = e.args.filter((factor) => {
        if (!(factor instanceof Fn) || !['sin', 'cos'].includes(factor.name)) return true;
        const argument = first(factor.args);
        const ray = new Dummy('r', { real: true });
        if (isReal(subs(argument, [[v, ray]])) !== true) return true;
        const phase = impl.limit(argument, v, p, '+');
        return phase !== S.Infinity && phase !== S.NegativeInfinity;
      });
      if (factors.length < e.args.length) return O(mul(...factors), v, p);
    }
    // leading behaviour at infinity: substitute x = 1/t, t -> 0+
    try {
      const t = new Sym('_o', { positive: true });
      // (the coefficients of an expansion are free of t)
      const expander = new Expander(t);
      const lead = expander.leading(subs(e, [[v, mul(p.name === 'oo' ? 1 : -1, pow(t, -1))]]));
      const logarithms = asIndependent(lead.c, [expander.L], { asAdd: false })[1];
      return new Order([mul(pow(p.name === '-oo' ? neg(v) : v, neg(lead.e)), subs(logarithms, [[expander.L, log(pow(v, -1))]])), v, p]);
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
    reduced = mul(pow(displacement, lead.e), subs(together(logarithms), [[expander.L, log(displacement)]]));
  } catch {
    // Along a fixed ray a nonzero real scale changes a monomial only by a constant.
    if (atZero && e instanceof Mul) {
      const powers = e.args.filter((factor) => factor.has(v)).map((factor) => {
        const [base, exponent] = factor instanceof Pow ? factor.args : [factor, S.One];
        return { scale: mul(base, pow(v, -1)), exponent };
      });
      if (powers.every(({ scale, exponent }) => scale instanceof Rational && !exponent.has(v))) {
        const base = powers.some(({ scale, exponent }) => isNegative(scale) && isReal(exponent) !== true) ? neg(v) : v;
        reduced = pow(base, add(...powers.map(({ exponent }) => exponent)));
      }
    }
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
    const leadingFactor = (f: Expr): Expr => {
      if (!(atZero && f instanceof Fn)) return f;
      const [v, ...rest] = vars.filter((s) => f.has(s));
      if (!v || rest.length) return f;
      try { return asLeadingTerm(f, v); }
      catch { return f; }
    };
    const original = expandMul(e);
    const summands = original instanceof Add ? original.args : [original];
    const monomials = summands.map((u) => u instanceof Mul ? mul(...u.args.map(leadingFactor)) : leadingFactor(u));
    const ex = add(...monomials);
    // If leading monomials cancel, their higher terms can still dominate on some paths.
    if (!ex.equals(original) && ex instanceof Add && ex.args.length < summands.length) return new Order([e, ...vars, p]);
    if (!ex.equals(original) && !(ex instanceof Add) && summands.length > 1) return new Order([e, ...vars, p]);
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
 * Series at +oo or -oo (SymPy series(f, x, oo, n)): x = sign/t with t -> 0+,
 * the expansion in t written back in x, with O(x**(-n), (x, oo)).
 */
function seriesAtInfinity(e: Expr, x: Sym, ray: Expr, point: Expr, n: number, algebraic: boolean): Expr {
  if (!algebraic && e instanceof Fn && point instanceof Special) {
    const special = specialSeriesAtInfinity(e, x, point === S.Infinity ? 1 : -1, n);
    if (special !== undefined) return special;
  }
  const t = new Sym('_t_inf', { positive: true });
  const st = series(subs(e, [[x, mul(ray, pow(t, -1))]]), t, 0, n);
  const back = (u: Expr) => subs(u, [[t, mul(ray, pow(x, -1))]]);
  const terms = st instanceof Add ? st.args : [st];
  const out: Expr[] = [];
  let order: Expr | undefined;
  for (const u of terms) {
    if (u instanceof Order) {
      // the Order of a series in t is O(t**k) (O(t) or O(1) for k = 1 or 0); at -oo it is written in -1/x (SymPy)
      const lead = first(u.args);
      const k = lead instanceof Pow ? lead.exp : lead.key === t.key ? S.One : S.Zero;
      const remainder = point instanceof Special ? mul(ray, pow(x, -1)) : pow(x, -1);
      order = new Order([pow(remainder, k), x, point]);
    } else out.push(back(u));
  }
  if (!order) return add(...out);
  if (point === S.Infinity && !out.length && e instanceof Add && some(e, (f) => f instanceof Pow && isE(f.base) && f.exp.has(x))) return aseries(e, x, n);
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

/** Asymptotic expansions with exponential or oscillatory factors kept outside their series. */
function specialSeriesAtInfinity(e: Fn, x: Sym, sign: 1 | -1, n: number): Expr | undefined {
  const z = last(e.args), name = e.name;
  const point = sign === 1 ? S.Infinity : S.NegativeInfinity;
  const inverse = mul(sign, pow(x, -1));
  const order = (power: ExprLike): Order => new Order([pow(inverse, power), x, point]);
  if (name === 'lowergamma' && sign === 1 && first(e.args).key === x.key && !z.has(x)) {
    const terms: Expr[] = [];
    let denominator: Expr = S.One;
    for (let k = 0; k < n - 1; k++) {
      terms.push(mul(pow(z, k), pow(denominator, -1)));
      denominator = mul(denominator, add(x, k + 1));
    }
    return add(mul(pow(z, x), exp(neg(z)), pow(x, -1), add(...terms)), new Order([mul(exp(mul(x, log(z))), pow(x, -n)), x, point]));
  }
  if (!['besseli', 'besselk', 'erf', 'erfc', 'erfi', 'Ei', 'expint', 'Si', 'Ci', 'fresnelc', 'fresnels'].includes(name)) return undefined;
  const t = new Sym('_asym', { positive: true });
  const argument = subs(z, [[x, mul(sign, pow(t, -1))]]);
  const [coefficient, exponent] = leadtermExact(argument, t);
  if (!exponent.isNegative || isReal(coefficient) !== true) return undefined;
  if (!argument.equals(mul(coefficient, pow(t, exponent)))) return undefined;
  const degree = -exponent.value;
  const negative = isNegative(coefficient) === true;
  const inverseZ = mul(pow(coefficient, -1), pow(inverse, neg(exponent)));
  if (name === 'besseli' || name === 'besselk') {
    const nu = first(e.args);
    const reverse = negative && name === 'besseli';
    const reciprocal = negative ? neg(inverseZ) : inverseZ;
    const terms: Expr[] = [];
    let c: Expr = reverse ? exp(mul(S.I, S.Pi, nu)) : negative ? neg(S.I) : S.One;
    for (let k = 0; k < n; k++) {
      terms.push(mul(c, pow(reciprocal, Rational.of(2 * k + 1, 2))));
      const j = Rational.of(2 * k + 1, 2);
      c = mul(c, add(j, neg(nu)), add(j, nu), Rational.of(name === 'besseli' || negative ? 1 : -1, 2 * (k + 1)));
    }
    const front = mul(pow(2, S.NegHalf), pow(S.Pi, name === 'besseli' ? S.NegHalf : S.Half));
    return mul(front, exp(name === 'besseli' && !reverse ? z : neg(z)), add(...terms, new Order([pow(reciprocal, Rational.of(2 * n + 1, 2)), x, point])));
  }
  if (name === 'erf' || name === 'erfc' || name === 'erfi') {
    if (isPositive(coefficient) !== true) return undefined;
    const terms: Expr[] = [];
    let c: Expr = S.One;
    for (let k = 0; (2 * k + 1) * degree < n; k++) {
      terms.push(mul(c, pow(inverseZ, 2 * k + 1)));
      c = mul(c, Rational.of((name === 'erfi' ? 1 : -1) * (2 * k + 1), 2));
    }
    const tail = mul(pow(S.Pi, S.NegHalf), exp(mul(name === 'erfi' ? 1 : -1, pow(z, 2))), add(...terms, order(n)));
    return name === 'erf' ? add(1, neg(tail)) : name === 'erfi' ? add(tail, neg(S.I)) : tail;
  }
  if (name === 'Ei' || name === 'expint') {
    const terms: Expr[] = [];
    let c: Expr = S.One;
    for (let k = 0; k * degree < n; k++) {
      terms.push(mul(c, pow(inverseZ, k)));
      c = mul(c, name === 'Ei' ? k + 1 : neg(add(first(e.args), k)));
    }
    return mul(pow(z, -1), exp(name === 'Ei' ? z : neg(z)), add(...terms, order(n)));
  }
  const fresnel = name === 'fresnelc' || name === 'fresnels';
  const phase = fresnel ? mul(S.Half, S.Pi, pow(z, 2)) : z;
  const odd: Expr[] = [], even: Expr[] = [];
  let c: Expr = fresnel ? pow(S.Pi, -1) : S.One;
  const step = fresnel ? 2 : 1;
  for (let k = 0; (step * k + 1) * degree < n; k++) {
    const term = mul(k % 4 < 2 ? 1 : -1, c, pow(inverseZ, step * k + 1));
    (k % 2 === 0 ? odd : even).push(term);
    c = mul(c, step * k + 1, fresnel ? pow(S.Pi, -1) : S.One);
  }
  if (fresnel) {
    const sine = name === 'fresnels';
    return add(negative ? S.NegHalf : S.Half, mul(sine ? cos(phase) : sin(phase), add(...(sine ? odd.map(neg) : odd))),
      neg(mul(sine ? sin(phase) : cos(phase), add(...even))), order(n));
  }
  const si = name === 'Si';
  return add(si ? mul(negative ? S.NegHalf : S.Half, S.Pi) : negative ? mul(S.I, S.Pi) : S.Zero,
    mul(si ? -1 : 1, si ? cos(phase) : sin(phase), add(...odd, order(n))),
    neg(mul(si ? sin(phase) : cos(phase), add(...even, order(n)))));
}

const isSingularity = (e: Expr): boolean => e instanceof ExtensionExpr && e.name === 'SingularityFunction';

/** Replace a singularity function by its local form at the expansion point. */
function singularityLocalForm(e: Expr, x: Sym, fromLeft: boolean): Expr {
  return mapBottomUp(e, (term) => {
    if (!isSingularity(term) || !term.has(x)) return term;
    const shift = add(first(term.args), neg(at(term.args, 1)));
    const power = at(term.args, 2);
    const origin = subs(shift, [[x, S.Zero]]);
    if (isZero(power) === true && isZero(origin) === true) return fromLeft ? S.Zero : S.One;
    return isNegative(power) !== true && isPositive(origin) === true ? pow(shift, power) : S.Zero;
  });
}

/**
 * Series expansion of e about x = x0 up to O((x - x0)**n). Like SymPy, an
 * exact (finite) expansion is returned without an Order term.
 * The algebraic option uses an inverse-power expansion at infinity, as in formal series.
 */
export function series(ex: ExprLike, variable?: Sym, x0x: ExprLike = 0, n = 6, dir: '+' | '-' = '+', opts: { logx?: Expr; local?: boolean; algebraic?: boolean } = {}): Expr {
  if (!['+', '-'].includes(dir)) throw new RangeError('Series direction must be + or -');
  const original = sympify(ex);
  const free = [...original.freeSymbols()].filter((v) => v instanceof Sym);
  if (!variable && !free.length) return original;
  if (!variable && free.length > 1) throw new RangeError('Specify the series variable');
  const x = variable ?? first(free);
  if (original instanceof SubsNode) {
    if (!free.some((v) => v.equals(x))) return original;
    const position = original.point.findIndex((v) => v.equals(x));
    const inner = position < 0 ? x : cast(at(original.variables, position), Sym);
    const expansion = series(original.expr, inner, x0x, n, dir, opts);
    const terms = expansion instanceof Add ? expansion.args : [expansion];
    return add(...terms.map((u) => u instanceof Order ? subs(u, [[inner, x]]) : original.withArgs([u, ...original.args.slice(1)])));
  }
  if (original instanceof Derivative && original.expr.has(x)) {
    const count = original.variableCount.reduce((k, [v, m]) => k + (v.equals(x) ? m : 0), 0);
    const expansion = series(original.expr, x, x0x, n + count, dir, opts);
    const terms = expansion instanceof Add ? expansion.args : [expansion];
    return add(...terms.map((u) => u instanceof Order ? u.diff(x, count) : original.withArgs([u, ...original.args.slice(1)])));
  }
  // sinc(u) = sin(u)/u has a removable singularity at u = 0
  let e = mapBottomUp(original, (t) => {
    if (t instanceof Integral && impl.doit) return impl.doit(t);
    if (!(t instanceof Fn && t.name === 'sinc')) return t;
    const u = first(t.args);
    return mul(sin(u), pow(u, -1));
  });
  const x00 = sympify(x0x);
  const atZero = x00 instanceof Rational && x00.isZero;
  if (opts.local && atZero && some(e, isSingularity)) {
    if (e instanceof Add) return add(...e.args.map((term) => series(term, x, x00, n, dir, opts)));
    const local = singularityLocalForm(e, x, dir === '-');
    const expansion = series(local, x, x00, n, dir, { logx: opts.logx });
    return e instanceof Mul && local.has(x) ? add(expansion, new Order([pow(x, n)])) : expansion;
  }
  if (opts.logx && atZero) {
    // SymPy logx: log(x) stands for the given symbol; x**c = exp(c*log(x)) for symbolic c
    const logSymbol = new Dummy('logx');
    e = mapBottomUp(e, (u) => {
      if (!(u instanceof Pow) || u.exp instanceof Rational || u.exp.has(x) || !u.base.has(x)) return u;
      if (u.base.equals(x)) return exp(mul(u.exp, logSymbol));
      if (dir === '-') return u;
      // Factor the leading monomial before expanding a symbolic power.
      const [coefficient, degree] = leadterm(u.base, x);
      if (degree.equals(0) || isPositive(coefficient) !== true) return u;
      return mul(exp(mul(degree, logSymbol, u.exp)), pow(mul(u.base, pow(x, neg(degree))), u.exp));
    });
    e = mapBottomUp(e, (t) => {
      if (dir !== '+' || !(t instanceof Fn) || t.name !== 'log') return t;
      const argument = first(t.args);
      return argument instanceof Pow && argument.base.key === x.key && argument.exp instanceof Rational ? mul(argument.exp, logSymbol) : t;
    });
    e = subs(e, [[log(x), logSymbol], [log(pow(x, -1)), neg(logSymbol)]]);
    return subs(series(e, x, x00, n, dir, { local: opts.local }), [[logSymbol, opts.logx], [log(x), opts.logx]]);
  }
  if (atZero && e instanceof Pow && isE(e.base) && e.exp instanceof Mul) {
    const coefficient = asIndependent(e.exp, [x], { asAdd: false });
    if (coefficient[1].equals(log(x)) && coefficient[0].isNumber && !im(coefficient[0]).equals(S.Zero)) throw new PoleError('Cannot expand an oscillatory logarithmic exponential');
  }
  // x**c with symbolic c is its own expansion at 0
  if (atZero && e instanceof Pow && e.base.key === x.key && !(e.exp instanceof Rational) && !e.exp.has(x)) {
    if (isReal(e.exp) === false || (e.exp.isNumber && !im(e.exp).equals(S.Zero))) throw new PoleError('Cannot expand a power with a nonreal exponent');
    return e;
  }
  const x0 = sympify(x0x);
  if (x0 === S.Infinity || x0 === S.NegativeInfinity) {
    return seriesAtInfinity(e, x, x0 === S.Infinity ? S.One : S.NegOne, x0, n, opts.algebraic === true);
  }
  const form = infiniteForm(x0);
  if (form?.kind === 'I' && form.a === 0) {
    return seriesAtInfinity(e, x, mul(form.t, S.I), x0, n, opts.algebraic === true);
  }
  // at zoo SymPy substitutes x = sign(zoo)/x: only a Laurent polynomial in x comes back as it is
  // (series(x, x, zoo) = x); other expansions there are not defined
  if (x0 instanceof Special && x0.name === 'zoo' && isLaurentPolynomial(e, x)) return e;
  if (x0 instanceof Special) throw new NotImplementedError('series: expansion at this point is not supported');
  if (!e.has(x)) return e;
  if (n >= 0 && atZero && dir === '+' && opts.logx === undefined && e instanceof Fn) {
    if ((e.name === 'li' || e.name === 'Li') && first(e.args).key === x.key) {
      // Ei(log(x)) is expanded at negative infinity in powers of 1/log(x).
      const logarithm = log(x);
      const terms = Array.from({ length: n }, (_, k) => mul(Rational.of(factorialOf(k)), pow(logarithm, -k)));
      const tail = mul(x, pow(logarithm, -1), add(...terms, new Order([pow(logarithm, -n), x, S.Zero])));
      return e.name === 'Li' ? add(tail, neg(fn('li', [2]))) : tail;
    }
    const bessel = besselSeriesAtZero(e, x, n);
    if (bessel !== undefined) return bessel;
  }
  const t = new Sym('_s', { positive: true });
  const ex0 = new Expander(t, x);
  // from the left: x = x0 - t with t -> 0+, written in powers of (x0 - x)
  const shifted = subs(e, [[x, dir === '-' ? add(x0, mul(-1, t)) : add(x0, t)]]);
  if (n < 0) throw new RangeError('series: the order n must be nonnegative');
  // the expansion variable is positive (SymPy series): oo*x is oo there
  if (!shifted.has(t)) return n === 0 && e instanceof Fn && e.name === 'arg' ? new Order([S.One]) : shifted;
  // (expanded to at least the order 1 and then truncated: series(sin(x), x, 0, 0) = O(1))
  let ps: PS;
  try {
    let cutoff = Rational.of(n);
    if (opts.local && atZero && shifted instanceof Pow && isE(shifted.base) && shifted.exp instanceof Add) {
      const [constant, increment] = asIndependent(shifted.exp, [t], { asAdd: true });
      if (!constant.equals(0)) {
        const degree = ex0.leading(increment).e;
        if (degree.isPositive && degree.value < 1) cutoff = Rational.of(degree.p * BigInt(n), degree.q);
      }
    }
    ps = ex0.ser(shifted, Rational.of(Math.max(n, 1))).truncate(cutoff);
  } catch (err) {
    // exp(g) with g -> oo (or of unknown sign) has no expansion: SymPy returns it unchanged, but
    // raises PoleError for a complex g (exp(I/x))
    if (err instanceof EssentialSingularity && e instanceof Pow && isE(e.base) && isReal(err.coeff) !== false) return e;
    if (err instanceof EssentialSingularity) return essentialSeries(e, x, x0, n, dir, err);
    if (err instanceof SeriesError && err.message === 'non-rational exponent' && atZero && dir === '+') {
      const generalized = binomialSeries(shifted, t, n);
      if (generalized !== undefined) return subs(generalized, [[t, x]]);
    }
    throw err;
  }
  const base = dir === '-' ? add(x0, mul(-1, x)) : x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  const back = (c: Expr) => subs(c, [[ex0.L, log(base)]]);
  const terms = ps.terms.map((term) => {
    const raw = back(term.c);
    const coefficient = raw.has(S.I) && some(raw, (u) => u instanceof Pow && isE(u.base) && u.exp.has(S.Pi)) ? powsimp(raw) : raw;
    const value = mul(e instanceof Pow && !e.base.has(x) && e.exp.has(x) ? expandMul(coefficient) : coefficient, pow(base, term.e));
    return opts.local && atZero ? expandMul(value) : value;
  });
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
    if (e instanceof Fn && ['bessely', 'besselk', '_eis'].includes(e.name)) remainder = mul(pow(lin, ps.order), log(base));
  }
  const ord = x0 instanceof Rational && x0.isZero ? new Order([remainder]) : new Order([remainder, x, x0]);
  return add(body, ord);
}

/** Binomial and logarithmic expansions with real, nonrational monomial exponents. */
function binomialSeries(e: Expr, x: Sym, n: number): Expr | undefined {
  const terms = expandMul(e);
  const result: Expr[] = [];
  let truncated = false;
  for (const term of terms instanceof Add ? terms.args : [terms]) {
    const [factor, f] = asIndependent(term, [x], { asAdd: false });
    const logarithm = f instanceof Fn && f.name === 'log';
    if (!(f instanceof Pow || logarithm)) return undefined;
    const base = first(f.args);
    const exponent = f instanceof Pow ? f.exp : S.Zero;
    if (!exponent.isNumber || isReal(exponent) !== true) return undefined;
    const summands = base instanceof Add ? base.args : [base];
    if (summands.length > 2) return undefined;
    const powers = summands.map((u) => {
      const [c, monomial] = asIndependent(u, [x], { asAdd: false });
      const power = monomial instanceof Pow && monomial.base.equals(x) ? monomial.exp : monomial.equals(x) ? S.One : S.Zero;
      return { c, power, valid: monomial.equals(pow(x, power)) && power.isNumber && isReal(power) === true };
    });
    if (!powers.every((p) => p.valid)) return undefined;
    powers.sort((a, b) => a.power.toNumber() - b.power.toNumber());
    const lead = first(powers);
    if (isPositive(lead.c) !== true) return undefined;
    const start = mul(lead.power, exponent);
    const front = mul(factor, pow(lead.c, exponent));
    if (logarithm) result.push(mul(factor, add(log(lead.c), mul(lead.power, log(x)))));
    const next = powers[1];
    if (!next) {
      if (!logarithm) return undefined;
      continue;
    }
    const step = expandMul(add(next.power, neg(lead.power)));
    if (isPositive(step) !== true) return undefined;
    const count = Math.ceil((n - start.toNumber()) / step.toNumber());
    if (count > 10000) return undefined;
    let binomial: Expr = S.One;
    const ratio = mul(next.c, pow(lead.c, -1));
    for (let j = 0; ; j++) {
      const degree = expandMul(add(start, mul(j, step)));
      const below = isPositive(add(n, neg(degree)));
      if (below === undefined) return undefined;
      if (!below) break;
      if (!logarithm || j > 0) {
        const c = logarithm ? Rational.of(j % 2 ? 1 : -1, j) : binomial;
        result.push(mul(front, c, pow(ratio, j), pow(x, degree)));
      }
      binomial = mul(binomial, add(exponent, -j), Rational.of(1, j + 1));
    }
    truncated = true;
  }
  return add(expandMul(add(...result)), ...(truncated ? [new Order([pow(x, n), x, S.Zero])] : []));
}

/** Preserve the Frobenius powers and logarithmic coefficients of a monomial argument. */
function besselSeriesAtZero(e: Fn, x: Sym, n: number): Expr | undefined {
  const name = e.name;
  if (name !== 'besselj' && name !== 'besseli' && name !== 'bessely' && name !== 'besselk') return undefined;
  const nu = first(e.args), z = last(e.args);
  if (!(nu instanceof Rational && nu.isInteger && !nu.isNegative && z.has(x))) return undefined;
  const [coefficient, exponent] = leadterm(z, x);
  if (!(exponent instanceof Rational || exponent instanceof Float) || !exponent.isPositive) return undefined;
  const degree = exponent.toNumber();
  if (isPositive(coefficient) !== true) return undefined;
  if (!z.equals(mul(coefficient, pow(x, exponent)))) {
    if (nu.isZero && (name === 'bessely' || name === 'besselk')) return composedOrderZeroBessel(name, z, x, degree, n);
    if ((name === 'besselj' || name === 'besseli') && nu.isPositive && nu.value * degree < n && (nu.value + 2) * degree >= n) {
      const r = seriesBody(series(mul(S.Half, z), x, 0, n));
      return add(mul(pow(r, nu), pow(fn('gamma', [add(nu, 1)]), -1)), new Order([pow(x, n)]));
    }
    return undefined;
  }
  const monomial = { base: x, coefficient, exponent };
  const body = besselLocalExpansion(name, nu, z, degree, n, monomial);
  const logarithmic = (name === 'bessely' || name === 'besselk') && n >= nu.value * degree;
  return add(body, new Order([mul(pow(x, n), logarithmic ? log(x) : S.One)]));
}

function seriesBody(expansion: Expr): Expr {
  const terms = expansion instanceof Add ? expansion.args : [expansion];
  return add(...terms.filter((term) => !(term instanceof Order)));
}

/** Compose the logarithmic and digamma parts of the order-zero Frobenius series. */
function composedOrderZeroBessel(name: 'bessely' | 'besselk', z: Expr, x: Sym, degree: number, n: number): Expr {
  const y = name === 'bessely';
  const r = mul(S.Half, z);
  const scaled = mul(y ? mul(2, pow(S.Pi, -1)) : -1, log(r), fn(y ? 'besselj' : 'besseli', [0, z]));
  const logarithmic = series(scaled, x, 0, n);
  const terms = logarithmic instanceof Add ? logarithmic.args : [logarithmic];
  const groups = new Map<string, { power: Expr; coefficients: Expr[] }>();
  const extra: Expr[] = [];
  function collectTerm(term: Expr, expandCoefficient: boolean): void {
    const factors = term instanceof Mul ? term.args : [term];
    const power = factors.find((factor) => factor.key === x.key || factor instanceof Pow && factor.base.key === x.key) ?? S.One;
    const coefficient = mul(...factors.filter((factor) => factor !== power));
    const group = groups.get(power.key) ?? { power, coefficients: [] };
    group.coefficients.push(expandCoefficient ? expandMul(coefficient) : coefficient);
    groups.set(power.key, group);
  }
  for (const term of terms) if (!(term instanceof Order)) collectTerm(term, true);
  let c = y ? pow(S.Pi, -1) : S.Half;
  for (let k = 0; 2 * k * degree < n; k++) {
    const psi = mul(2, fn('polygamma', [0, k + 1]));
    const body = expandMul(mul(c, seriesBody(series(pow(r, 2 * k), x, 0, n))));
    if (body instanceof Add) extra.push(mul(y ? -1 : 1, psi, body));
    else collectTerm(mul(y ? -1 : 1, psi, body), false);
    c = mul(c, Rational.of(y ? -1 : 1, (k + 1) ** 2));
  }
  return add(...extra, ...[...groups.values()].map(({ power, coefficients }) => mul(power, add(...coefficients))),
    new Order([mul(log(x), pow(x, n))]));
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
  const irrational = (f: Expr): f is Pow => f instanceof Pow && f.base.key === x.key && !(f.exp instanceof Rational) && !f.exp.has(x);
  if (e instanceof Add && e.args.some((term) => (term instanceof Mul ? term.args : [term]).some(irrational))) {
    const leaders = e.args.map((term) => leadterm(term, x));
    const best = leaders.find(([, p]) => leaders.every(([, q]) => p.key === q.key || isPositive(add(q, neg(p))) === true));
    if (best !== undefined) {
      const coefficient = add(...leaders.filter(([, p]) => p.key === best[1].key).map(([c]) => c));
      if (coefficient.key !== S.Zero.key) return [coefficient, best[1]];
    }
  }
  const factors = e instanceof Mul ? e.args : [e];
  const powers = factors.filter(irrational);
  if (powers.length === 0) {
    try {
      return leadtermExact(e, x);
    } catch (error) {
      if (!(e instanceof Add) || !(error instanceof SeriesError && error.message === 'non-rational exponent')) throw error;
      const value = impl.limit(e, x, S.Zero, '+');
      if (value instanceof Rational && !value.isZero) return [value, S.Zero];
      throw error;
    }
  }
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

/** Evaluate expressions with oscillating factors by their accumulation ranges. */
function oscillatingLeadingTerm(e: Expr, x: Sym, cdir: Expr): Expr | undefined {
  if (e instanceof Fn && e.name === 'log') {
    const range = oscillatingLeadingTerm(first(e.args), x, cdir);
    return range === undefined ? undefined : log(range);
  }
  if (e instanceof Fn) {
    if (!['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(e.name)) return undefined;
    const value = leadingTermRules[e.name]?.(e, x, cdir);
    return value instanceof AccumBoundsNode ? value : undefined;
  }
  if (e instanceof Pow && isE(e.base)) {
    const range = oscillatingLeadingTerm(e.exp, x, cdir);
    return range === undefined ? undefined : exp(range);
  }
  if (e instanceof Pow) {
    if (e.exp.has(x)) return undefined;
    const range = oscillatingLeadingTerm(e.base, x, cdir);
    return range === undefined ? undefined : pow(range, e.exp);
  }
  if (e instanceof Add || e instanceof Mul) {
    const values = e.args.map((term) => oscillatingLeadingTerm(term, x, cdir));
    if (values.includes(S.NaN)) return S.NaN;
    const ranges = values.filter((value): value is Expr => value !== undefined);
    if (ranges.length !== 1) return undefined;
    const range = first(ranges);
    const other = e.args.filter((_, i) => values[i] === undefined);
    if (e instanceof Add) return other.some((term) => term.has(x)) ? undefined : add(range, ...other);
    const remaining = mul(...other);
    if (!remaining.has(x)) return mul(range, remaining);
    if (!(range instanceof AccumBoundsNode)) return mul(range, asLeadingTerm(remaining, x, { cdir }));
    const factor = asLeadingTerm(remaining, x, { cdir });
    if (subs(factor, [[x, S.Zero]]) !== S.Zero) return undefined;
    const ray = new Sym('_oscillation', { positive: true });
    const sign = isPositive(subs(factor, [[x, mul(cdir, ray)]]));
    if (sign === undefined) return undefined;
    const lower = sign ? range.min : neg(range.max);
    const upper = sign ? range.max : neg(range.min);
    const lo = lower === S.NegativeInfinity ? lower : S.Zero;
    const hi = upper === S.Infinity ? upper : S.Zero;
    return lo === hi ? lo : AccumBounds(lo, hi);
  }
  return undefined;
}

for (const name of ['besselj', 'besseli', 'bessely', 'besselk'] as const) leadingTermRules[name] = (e, x, cdir) => {
  const nu = first(e.args), z = last(e.args);
  if (!z.has(x) || nu.has(x)) return undefined;
  const [c, power] = leadterm(z, x);
  if (!(power instanceof Rational) || power.isZero) return undefined;
  const leading = mul(c, pow(x, power));
  if (power.isNegative) {
    if (name !== 'besselk' && name !== 'besseli') return undefined;
    if (name === 'besseli' && isNegative(mul(c, pow(cdir.equals(0) ? S.One : cdir, power))) === true) return e;
    return name === 'besselk' ? mul(pow(S.Pi, S.Half), exp(neg(leading)), pow(mul(2, leading), S.NegHalf))
      : mul(exp(leading), pow(mul(2, S.Pi, leading), S.NegHalf));
  }
  if (name === 'besselj' || name === 'besseli') return mul(pow(leading, nu), pow(2, neg(nu)), pow(fn('gamma', [add(nu, 1)]), -1));
  if (nu.equals(0)) {
    const logTerm = add(log(leading), S.EulerGamma, neg(log(2)));
    return name === 'besselk' ? neg(logTerm) : mul(2, pow(S.Pi, -1), logTerm);
  }
  if (!(nu instanceof Rational)) return undefined;
  if (name === 'bessely' && nu.isNegative && !nu.isInteger) {
    const angle = mul(S.Pi, nu);
    const cosine = cos(angle);
    const order = cosine.equals(0) ? neg(nu) : nu;
    return mul(fn('csc', [angle]), cosine.equals(0) ? -1 : cosine, pow(mul(S.Half, leading), order),
      pow(fn('gamma', [add(1, order)]), -1));
  }
  const absOrder = Rational.of(nu.p < 0n ? -nu.p : nu.p, nu.q);
  const magnitude = mul(fn('gamma', [absOrder]), pow(mul(S.Half, leading), neg(absOrder)));
  return name === 'besselk' ? mul(S.Half, magnitude) : mul(-1, pow(S.Pi, -1), magnitude);
};

for (const name of ['erf', 'erfc', 'erfi'] as const) leadingTermRules[name] = (e, x, cdir) => {
  const [coefficient, exponent] = leadterm(last(e.args), x);
  if (isNegative(exponent) !== true) return undefined;
  if (name === 'erfi') return e;
  const c = mul(coefficient, pow(cdir.equals(0) ? S.One : cdir, exponent));
  if (isPositive(c) === true) return name === 'erf' ? S.One : S.Zero;
  if (isNegative(c) === true) return name === 'erf' ? S.NegOne : S.Two;
  return undefined;
};

/**
 * SymPy as_leading_term(x, cdir=...): the leading term as x -> 0 from the direction cdir (0 when
 * not given: the side does not matter, or x approaches 0 from above).
 */
export function asLeadingTerm(ex: ExprLike, x: Sym, opts: { cdir?: ExprLike; logx?: ExprLike } = {}): Expr {
  let e = sympify(ex);
  if (e instanceof Fn && e.name === 'arg' && e.has(x)) {
    const ray = sympify(opts.cdir ?? 1);
    const t = new Sym('_arg', { positive: true });
    const u = first(e.args);
    const directed = subs(u, [[x, mul(ray.equals(S.Zero) ? S.One : ray, t)]]);
    if (isPositive(directed) === true) return S.Zero;
    if (isNegative(directed) === true) return S.Pi;
    throw new NotImplementedError(`cannot expand ${String(e)} around 0`);
  }
  if (e instanceof Piecewise) {
    const branch = e.pairs.find(([, condition]) => subs(condition, [[x, S.Zero]]) === S.true);
    if (branch) return asLeadingTerm(branch[0], x, opts);
  }
  if ((e instanceof Derivative || e instanceof Integral) && impl.doit) {
    const evaluated = impl.doit(e);
    if (evaluated.key !== e.key) return asLeadingTerm(evaluated, x, opts);
  }
  if (some(e, isSingularity)) e = singularityLocalForm(e, x, sympify(opts.cdir ?? 0).equals(-1));
  if (e instanceof DefinedFunctionCall) {
    const bounded = new Order([S.One, x, S.Zero]);
    if (e.args.some((arg) => {
      const term = asLeadingTerm(arg, x);
      return term.has(x) && orderContains(bounded, term) === true;
    })) throw new NotImplementedError(`leading term of ${e.name}`);
    return e;
  }
  const rule = e instanceof Fn ? leadingTermRules[e.name] : undefined;
  const special = rule?.(cast(e, Fn, 'function'), x, sympify(opts.cdir ?? 0));
  const ray = sympify(opts.cdir ?? 1);
  const range = (e instanceof Pow && isE(e.base) || e instanceof Fn && e.name === 'log') && e.has(x)
    ? oscillatingLeadingTerm(e, x, ray === S.Zero ? S.One : ray)
    : undefined;
  let result: Expr;
  if (special !== undefined) result = special;
  else if (range !== undefined) result = range;
  else if (e instanceof Mul) result = mul(...e.args.map((a) => asLeadingTerm(a, x, opts)));
  else {
    if (ray instanceof Rational && (ray.isZero || ray.key === S.One.key)) {
      result = directionalLeadingTerm(e, x);
    } else {
      if (isReal(ray) !== true) throw new NotImplementedError('leading term in a nonreal direction');
      const t = new Sym('_leading', { positive: true });
      const leading = asLeadingTerm(subs(e, [[x, mul(ray, t)]]), t);
      result = expandMul(subs(leading, [[log(t), add(log(x), neg(log(ray)))], [t, mul(x, pow(ray, -1))]]));
    }
  }
  return opts.logx === undefined ? result : subs(result, [[log(x), sympify(opts.logx)]]);
}

function directionalLeadingTerm(e: Expr, x: Sym): Expr {
  try {
    const [coefficient, exponent] = leadterm(e, x);
    return mul(coefficient, pow(x, exponent));
  } catch (error) {
    if (!(error instanceof SeriesError) || !(e instanceof Fn) || e.name === 'arg') throw error;
    const value = impl.limit(e, x, S.Zero, '+');
    if (value instanceof Limit || value instanceof Special || value.key === S.Zero.key || value.has(x)) throw error;
    return value;
  }
}

/** Order of the O term in a sum, or undefined (SymPy getn). */
export function getn(ex: ExprLike): Expr | undefined {
  const e = sympify(ex);
  const orders = (e instanceof Add ? e.args : [e]).filter((a) => a instanceof Order);
  if (orders.length > 1) throw new NotImplementedError('Several independent Order terms');
  const o = orders[0];
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
  fresnelc: (n, x) => n < 0 ? S.Zero : mul(pow(mul(S.Half, S.Pi), 2 * n), pow(x, 4 * n + 1),
    Rational.of(n % 2 === 0 ? 1n : -1n, factorialOf(2 * n) * BigInt(4 * n + 1))),
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
  if (growing || other) {
    if (!(e instanceof Add || e instanceof Mul)) return e;
    const algorithm = new Gruntz();
    const [omega, expression] = algorithm.mrv(e, x);
    if (omega.has(x)) return e;
    const w = new Dummy('w', { positive: true });
    const [rewritten, logw] = algorithm.rewrite(expression, omega, x, w);
    const expansion = new Expander(w);
    if (hir) {
      const ps = expansion.ser(rewritten, Rational.of(n));
      const power = (k: Expr) => exp(mul(k, logw));
      return new Add([...ps.terms.map(({ c, e: k }) => mul(c, power(k))), new Order([power(ps.order), x, S.Infinity])]);
    }
    const lead = expansion.leading(rewritten);
    const coefficient = series(lead.c, x, S.Infinity, n);
    if (some(coefficient, (u) => u instanceof Order)) return mul(coefficient, exp(mul(lead.e, logw)));
    const ps = expansion.ser(rewritten, Rational.of(n));
    const terms = ps.terms.map((u) => expandMul(mul(powsimp(expandMul(u.c)), exp(mul(u.e, logw)))));
    if (!ps.isExact) terms.push(new Order([exp(mul(ps.order, logw)), x, S.Infinity]));
    return add(...terms);
  }
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

/** The leading expression and merged (variable, point) pairs of an Order. */
export function asExprVariables(o: Order, existing: readonly (readonly [Sym, Expr])[] = []): [Expr, [Sym, Expr][]] {
  const p = o.args.length > 1 ? at(o.args, -1) : S.Zero;
  const variables = new Map<string, [Sym, Expr]>();
  for (const [v, point] of existing) {
    if (!point.equals(p)) throw new NotImplementedError('Multiplying Order at different points');
    variables.set(v.key, [v, point]);
  }
  for (const v of orderVariables(o)) variables.set(v.key, [v, p]);
  return [o.expr, [...variables.values()].sort(([a], [b]) => Number(a.name > b.name) - Number(a.name < b.name))];
}

// Pull back the expansion point through a change of variable (Order._eval_subs).
substitutionHooks.order = (o, old, replacement) => {
  const variables = orderVariables(o);
  if (variables.length !== 1 || !first(variables).equals(old)) return undefined;
  const point = o.point ?? S.Zero;
  const symbols = [...replacement.freeSymbols()].filter((s) => s instanceof Sym);
  const variable = symbols.find((s) => s.equals(old)) ?? (symbols.length === 1 ? first(symbols) : undefined);
  if (!variable) return undefined;
  const expr = o.expr.subs(old, replacement);
  if (replacement instanceof Order) {
    const expansionPoint = replacement.point ?? S.Zero;
    if (!impl.limit(replacement.expr, variable, expansionPoint, '+').equals(point)) {
      throw new NotImplementedError('Cannot invert an order with an incompatible limit');
    }
    return O(expr, variable, expansionPoint);
  }
  if (replacement instanceof Sym) return O(expr, replacement, point);
  if (subs(replacement, [[variable, point]]).equals(point)) return O(expr, variable, point);
  // Invert affine substitutions and reciprocals before taking the limit.
  const slope = replacement.diff(variable);
  const intercept = subs(replacement, [[variable, S.Zero]]);
  if (!slope.has(variable) && !slope.equals(0)) return O(expr, variable, mul(add(point, neg(intercept)), pow(slope, -1)));
  if (replacement instanceof Pow && replacement.base.equals(variable) && !replacement.exp.has(variable)) {
    const inverse = pow(variable, pow(replacement.exp, -1));
    return O(expr, variable, impl.limit(inverse, variable, point, '+'));
  }
  return new SubsNode([o, old, replacement]);
};

impl.rebuildOrder = (args) => {
  const variables = args.slice(1, -1).filter((v): v is Sym => v instanceof Sym);
  return O(first(args), variables.length ? variables : undefined, args.length === 1 ? S.Zero : at(args, -1));
};

function orderContains(o: Order, e: Expr, strict = true): boolean | 'unknown' {
  let variables = orderVariables(o);
  const point = o.args.length > 1 ? at(o.args, -1) : S.Zero;
  const other = e instanceof Order ? e.expr : e;
  const otherVariables = e instanceof Order ? orderVariables(e) : [...e.freeSymbols()].filter((s) => s instanceof Sym);
  if (other.has(S.NaN)) return false;
  if (!variables.length && other.freeSymbols().size > 0) variables = otherVariables;
  if (e instanceof Order && variables.length && otherVariables.length && !variables.some((v) => otherVariables.some((w) => w.equals(v)))) return 'unknown';
  if (!variables.length && otherVariables.length) return false;
  if (e instanceof Order) {
    const otherPoint = e.args.length > 1 ? at(e.args, -1) : S.Zero;
    if (!otherPoint.equals(point)) return 'unknown';
    if (point.equals(S.Zero) && o.expr instanceof Add && !(other instanceof Add)) {
      return o.expr.args.some((term) => {
        const termOrder = O(term, variables, point);
        return termOrder instanceof Order && termOrder.contains(e) === true;
      });
    }
    if (other instanceof Add && o.expr.equals(S.One)) return other.args.every((term) => o.contains(term) === true);
    if (otherVariables.length) variables = variables.filter((v) => otherVariables.some((w) => w.equals(v)));
  }
  if (other.equals(S.Zero)) return true;
  if (o.expr.equals(S.Zero)) return false;
  if (!variables.length) return ![S.Infinity, S.NegativeInfinity, S.ComplexInfinity].some((v) => other.has(v));
  let result: boolean | 'unknown' = 'unknown';
  for (const variable of variables) {
    const quotient = mul(o.expr, pow(other, -1));
    const t = new Sym('_o');
    try {
      const expander = new Expander(t);
      const shifted = point instanceof Special ? mul(point.name === 'oo' ? 1 : -1, pow(t, -1)) : add(point, t);
      const lead = expander.leading(subs(quotient, [[variable, shifted]]));
      if (!lead.c.has(t) && !lead.c.has(expander.L)) {
        const contained = !lead.e.isPositive;
        if (result !== 'unknown' && result !== contained) return 'unknown';
        result = contained;
        continue;
      }
    } catch {
      // Essential singularities require the limit algorithms.
    }
    const ratio = impl.limit(powsimp(quotient), variable, point, '+');
    if (ratio instanceof Limit && ratio.expr instanceof Pow && ratio.expr.base.equals(variable) && ratio.expr.exp.freeSymbols().size) {
      if (strict && !(e instanceof Order)) throw new NotImplementedError('Cannot determine the sign of the order exponent');
      return 'unknown';
    }
    if (ratio.has(S.NaN) || ratio.kind === 'Limit') return 'unknown';
    const contained = !ratio.equals(S.Zero);
    if (result !== 'unknown' && result !== contained) return 'unknown';
    result = contained;
  }
  return result;
}

impl.orderContains = orderContains;

registerArithmetic((op, args) => {
  if (op === 'pow') {
    const [base, exponent] = [at(args, 0), at(args, 1)];
    if (base instanceof Order && exponent instanceof Order && base.expr.equals(S.One) && exponent.expr.equals(S.One)) return base;
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
      return orderContains(query, e, false) === true;
    };
    for (const o of orders) {
      if (kept.some((other) => contains(other, o))) continue;
      for (let i = kept.length - 1; i >= 0; i--) if (contains(o, at(kept, i))) kept.splice(i, 1);
      kept.push(o);
    }
    kept.sort((a, b) => Number(a.key > b.key) - Number(a.key < b.key));
    const body = add(...flat.filter((e) => !(e instanceof Order) && !kept.some((o) => contains(o, e))));
    const terms = body.equals(S.Zero) ? [] : body instanceof Add ? [...body.args] : [body];
    return terms.length + kept.length === 1 ? first([...terms, ...kept]) : new Add([...terms, ...kept]);
  }
  if (op !== 'mul') return undefined;
  const point = (o: Order): Expr => o.args.length > 1 ? at(o.args, -1) : S.Zero;
  const p = point(first(orders));
  if (orders.some((o) => !point(o).equals(p))) throw new NotImplementedError('Multiplying Order at different points');
  const variables = [...new Map(orders.flatMap(orderVariables).map((v) => [v.key, v])).values()];
  return O(mul(...args.map((a) => a instanceof Order ? a.expr : a)), variables, p);
});
