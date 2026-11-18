// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Tree traversal utilities: rebuild, substitution, free symbols, size.
 */

import { piecewise, rel } from './logic';
import { toRational } from '../numeric/mpf';
import { Concrete } from './concrete';
import { compareKeys, sortKey } from '../printing/sortkey';
import type { Key } from '../printing/sortkey';
import type { ExprLike, Substitution } from './nodes';
import { Add, Derivative, Dummy, Expr, ExtensionExpr, Float, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, S, Sym, UndefFn, asRational, impl, isNum } from './nodes';
import { add, mul, pow, splitCoeff, sympify } from './ops';
import { isIntegerQ, isNonNegative, isPositive, isReal } from './assumptions';
import { SubsNode } from './subsnode';
import { BoolOp, and } from './boolalg';
import { at, cast, defined, first } from './guard';

const isSubsMap = (s: Substitution): s is ReadonlyMap<Expr, ExprLike> => s instanceof Map;
const isSubsPairs = (s: Substitution): s is readonly (readonly [Expr, ExprLike])[] => Array.isArray(s);

/**
 * Rebuild a node of the same type with new arguments (re-canonicalizing).
 * Without `args`, the whole tree is rebuilt bottom-up (SymPy
 * `sympy.strategies.rl.rebuild` and `sympy.unify.rebuild`), which
 * canonicalizes nodes built unevaluated.
 *
 * @experimental May change in a minor release.
 */
export function rebuild(e: Expr, args?: readonly Expr[]): Expr {
  if (args === undefined) return e.isAtom ? e : rebuild(e, e.args.map((a) => rebuild(a)));
  if (e instanceof ExtensionExpr || e instanceof BoolOp) return e.withArgs(args);
  if (e instanceof Sym && e.args.length > 0) return e.func(...args);
  if (e instanceof Add) return add(...args);
  if (e instanceof Mul) return mul(...args);
  if (e instanceof Pow) return pow(at(args, 0), at(args, 1));
  if (e instanceof Fn) return defined(impl.fn?.(e.name, args), 'function constructors');
  if (e instanceof Rel) return rel(e.op, at(args, 0), at(args, 1));
  if (e instanceof Piecewise) {
    const pairs: [Expr, Expr][] = [];
    for (let i = 0; i < args.length; i += 2) pairs.push([at(args, i), at(args, i + 1)]);
    return piecewise(...pairs);
  }
  if (e instanceof Integral) return new Integral(args);
  if (e instanceof Limit) return new Limit(args, e.dir);
  if (e instanceof Order) return new Order(args);
  if (e instanceof UndefFn) return new UndefFn(e.name, args);
  if (e instanceof Concrete) return new Concrete(e.kind2, args);
  // SymPy keeps a rebuilt derivative unevaluated: Derivative(f(x), x).subs(f(x), x**2) = Derivative(x**2, x)
  if (e instanceof Derivative) return e.withArgs(args);
  // a set node (sets/ is a higher layer, which registers its constructors)
  if (e.kind === 'Set') return defined(impl.rebuildSet, 'sets')(e, args);
  // atoms (and nodes of higher layers without withArgs) are returned as they are
  return e;
}

impl.rebuild = (e, args) => rebuild(e, args);

/** Apply f bottom-up to every node. */
export function mapBottomUp(e: Expr, f: (e: Expr) => Expr): Expr {
  if (e.args.length === 0) return f(e);
  const args = e.args.map((a) => mapBottomUp(a, f));
  const changed = args.some((a, i) => a !== e.args[i]);
  return f(changed ? rebuild(e, args) : e);
}

type Rule = { match: (e: Expr) => boolean; to: Expr };

function toRules(s: Substitution): Rule[] {
  const rules: Rule[] = [];
  const pushPair = (from: Expr | string, to: ExprLike) => {
    const target = sympify(to);
    if (typeof from === 'string') {
      rules.push({ match: (e) => e instanceof Sym && e.name === from, to: target });
    } else {
      const key = from.key;
      rules.push({ match: (e) => e.key === key, to: target });
    }
  };
  if (isSubsMap(s)) {
    for (const [k, v] of s) pushPair(k, v);
  } else if (isSubsPairs(s)) {
    for (const [k, v] of s) pushPair(k, v);
  } else {
    for (const [k, v] of Object.entries(s)) pushPair(k, v);
  }
  return rules;
}

/**
 * Simultaneous structural substitution (SymPy `xreplace`): only exact
 * subtrees are replaced. Keys may be expressions or (in a plain object)
 * symbol names.
 */
export function xreplace(e: Expr, s: Substitution): Expr {
  const rules = toRules(s);
  if (rules.length === 0) return e;
  const go = (x: Expr): Expr => {
    for (const r of rules) if (r.match(x)) return r.to;
    if (x.args.length === 0) return x instanceof Sym ? (x.substituteInner(go) ?? x) : x;
    const args = x.args.map(go);
    return args.some((a, i) => a !== x.args[i]) ? rebuild(x, args) : x;
  };
  return go(e);
}

function toPairs(s: Substitution): [Expr, Expr][] {
  const out: [Expr, Expr][] = [];
  const key = (k: Expr | string): Expr => (typeof k === 'string' ? new Sym(k) : k);
  if (isSubsMap(s)) for (const [k, v] of s) out.push([key(k), sympify(v)]);
  else if (isSubsPairs(s)) for (const [k, v] of s) out.push([k, sympify(v)]);
  else for (const [k, v] of Object.entries(s)) out.push([key(k), sympify(v)]);
  return out;
}

/**
 * SymPy Pow._eval_subs _check for commutative objects: the power k with
 * old**k equal to a power whose exponent splits into ct1 (old's exponent
 * splits into ct2), when (b**e)**k == b**(e*k) holds.
 */
function powerOf(ct1: [Expr, Expr], ct2: [Expr, Expr], old: Pow): Expr | undefined {
  if (ct1[1].key !== ct2[1].key) return undefined;
  const k = mul(ct1[0], pow(ct2[0], -1));
  if (k instanceof Rational && k.isInteger) return k;
  if (k instanceof Float && k.mpf.exp >= 0n && isNum(ct1[0]) && isNum(ct2[0])) {
    const exact = (n: Float | Rational): Rational => n instanceof Float ? Rational.of(...toRational(n.mpf)) : n;
    const a = exact(ct1[0]);
    const b = exact(ct2[0]);
    const ratio = Rational.of(a.p * b.q, a.q * b.p);
    if (ratio.isInteger && ratio.key === exact(k).key) return k;
  }
  const combines = (isPositive(old.base) === true && isReal(old.exp) === true) || (isNonNegative(old.base) === true && isNonNegative(old.exp) === true);
  return combines ? k : undefined;
}

/** SymPy as_independent(Symbol, as_Add=False): the factors without symbols and the rest. */
function splitSymbolFactors(e: Expr): [Expr, Expr] {
  const hasSym = (t: Expr): boolean => t instanceof Sym || t.args.some(hasSym);
  const factors = e instanceof Mul ? e.args : [e];
  return [mul(...factors.filter((t) => !hasSym(t))), mul(...factors.filter(hasSym))];
}

/** SymPy as_coeff_Add of a sum: the numeric term and the rest. */
function asCoeffAdd(e: Add): [Expr, Expr] {
  const c = first(e.args);
  if (isNum(c)) return [c, e.args.length === 2 ? at(e.args, 1) : new Add(e.args.slice(1))];
  return [Rational.of(0n), e];
}

/**
 * SymPy log(b, c) when it is a number: the integer k with b = c**k for a rational b and an
 * integer c > 1 (log(1/4, 2) = -2); undefined otherwise (log(2, 4) and log(6, 2) stay symbolic).
 */
function intLog(b: Expr, c: Expr): number | undefined {
  if (!(b instanceof Rational) || !(c instanceof Rational) || c.q !== 1n || c.p < 2n || !b.isPositive) return undefined;
  const [num, sign] = b.p === 1n ? [b.q, -1] : b.q === 1n ? [b.p, 1] : [0n, 0];
  if (num === 0n) return undefined;
  let k = 0;
  let v = num;
  while (v % c.p === 0n) {
    v /= c.p;
    k++;
  }
  return v === 1n && k > 0 ? sign * k : undefined;
}

/** SymPy `_eval_subs` for Add, Mul and Pow (algebraic substitution). */
function evalSubs(e: Expr, old: Expr, nw: Expr): Expr | undefined {
  // Derivative(f, (x, 2)).subs(Derivative(f, x), y) -> Derivative(y, x) (SymPy Derivative._eval_subs)
  if (e instanceof Derivative && old instanceof Derivative && e.expr.key === old.expr.key) {
    const remaining = new Map(e.variableOrders.map((pair) => [pair[0].key, pair] as const));
    for (const [v, n] of old.variableOrders) {
      const h = remaining.get(v.key);
      if (!h) return undefined;
      const order = add(h[1], mul(-1, n));
      if (order.key === S.Zero.key) remaining.delete(v.key);
      else if (isPositive(order) === true) remaining.set(v.key, [v, order]);
      else return undefined;
    }
    return remaining.size ? new Derivative([nw, ...[...remaining.values()].flat()]) : nw;
  }
  if (e instanceof Add && old.isNumber) {
    const negative = mul(-1, old);
    if (e.args.some((term) => term.key === negative.key)) return add(...e.args.filter((term) => term.key !== negative.key), mul(-1, nw));
  }
  if (e instanceof Add && old instanceof Add) {
    // SymPy Add._eval_subs
    const [cs, ts] = asCoeffAdd(e);
    const [co, to] = asCoeffAdd(old);
    const rationals = cs instanceof Rational && co instanceof Rational;
    const negTo = mul(-1, to);
    if (rationals) {
      // (2 + a).subs(3 + a, y) -> y - 1; (2 + a).subs(-3 - a, y) -> -y - 1
      if (ts.key === to.key) return add(nw, cs, mul(-1, co));
      if (ts.key === negTo.key) return add(mul(-1, nw), cs, co);
    }
    if (rationals || cs.key === co.key) {
      // (a + b + c).subs(b + c, x) -> a + x; (a + b + c + d).subs(-b - c, x) -> a - x + d
      const selfArgs = ts instanceof Add ? ts.args : [ts];
      for (const [sign, oldTerms] of [
        [1, to instanceof Add ? to.args : [to]],
        [-1, negTo instanceof Add ? negTo.args : [negTo]],
      ] as const) {
        if (oldTerms.length >= selfArgs.length) continue;
        const selfKeys = new Map(selfArgs.map((a) => [a.key, a]));
        if (oldTerms.every((t) => selfKeys.has(t.key))) {
          for (const t of oldTerms) selfKeys.delete(t.key);
          const rest = [...selfKeys.values()].map((a) => subsOne(a, old, nw));
          return sign === 1 ? add(nw, cs, mul(-1, co), ...rest) : add(mul(-1, nw), cs, co, ...rest);
        }
      }
    }
    return undefined;
  }
  if (e instanceof Mul && old instanceof Mul) return subsMul(e, old, nw);
  // Noncommutative powers admit only integral exponent blocks; fractional roots cannot be chosen.
  if (e instanceof Pow && old instanceof Pow && !e.base.isCommutative && e.base.key === old.base.key) {
    if (isIntegerQ(e.exp) !== true || isIntegerQ(old.exp) !== true) return e;
    const [oc, or] = splitCoeff(old.exp);
    const terms = e.exp instanceof Add ? e.exp.args : [e.exp];
    const rest: Expr[] = [];
    let quotient = 0n;
    for (const term of terms) {
      const [ec, er] = splitCoeff(term);
      if (ec instanceof Rational && oc instanceof Rational && ec.isInteger && oc.isInteger && !oc.isZero && er.key === or.key && isIntegerQ(er) === true) {
        quotient += ec.p / oc.p;
        rest.push(mul(Rational.of(ec.p % oc.p), er));
      } else rest.push(term);
    }
    if (quotient !== 0n) return mul(pow(nw, Rational.of(quotient)), pow(e.base, add(...rest)));
    return e;
  }
  // SymPy issue 10829: (4**x).subs(2**x, y) -> y**2, for log(4, 2) a number
  if (e instanceof Pow && old instanceof Pow && e.exp.key === old.exp.key) {
    const k = intLog(e.base, old.base);
    if (k !== undefined) return pow(nw, k);
  }
  // SymPy Pow._eval_subs for powers of the same base (exp(a) is E**a)
  if (e instanceof Pow && old instanceof Pow && e.base.key === old.base.key) {
    if (!(e.exp instanceof Add)) {
      // (x**(6*y)).subs(x**(3*y), z) -> z**2
      const k = powerOf(splitSymbolFactors(e.exp), splitSymbolFactors(old.exp), old);
      return k === undefined ? undefined : pow(nw, k);
    }
    // b**(6*x + a).subs(b**(3*x), y) -> y**2*b**a, term by term
    const ct2 = splitCoeff(old.exp);
    const powers: Expr[] = [];
    const rest: Expr[] = [];
    for (const t of e.exp.args) {
      const nt = subsOne(t, old, nw);
      const k = powerOf(splitCoeff(nt), ct2, old);
      if (k === undefined) rest.push(nt);
      else powers.push(pow(nw, k));
    }
    return powers.length ? mul(...powers, pow(e.base, add(...rest))) : undefined;
  }
  return undefined;
}

/** e as a Rational, or undefined. */
const ratOf = (e: Expr): Rational | undefined => (e instanceof Rational ? e : undefined);

/** Multiplicity of the integer p > 1 in the integer n != 0. */
function intMultiplicity(p: bigint, n0: bigint): number {
  let n = n0 < 0n ? -n0 : n0;
  let m = 0;
  while (n % p === 0n) {
    n /= p;
    m++;
  }
  return m;
}

/** SymPy multiplicity(p, n) of the rationals p > 0 (p != 1) and n != 0. */
function ratMultiplicity(p: Rational, n: Rational): number {
  // p != 1, so the numerator of an integer p and the denominator of a fraction p are greater than 1
  const im = intMultiplicity;
  if (p.q === 1n) return n.p === 1n || n.p === -1n ? -im(p.p, n.q) : im(p.p, n.p) - im(p.p, n.q);
  if (p.p === 1n) return im(p.q, n.q);
  return Math.min(im(p.p, n.p), im(p.q, n.q)) - Math.min(im(p.q, n.p), im(p.p, n.q));
}

/** SymPy extract_multiplicatively for rationals: a / b unless that changes the sign of a positive a. */
function extractRational(a: Rational, b: Rational): Rational | undefined {
  // b > 0 here (a negative coefficient of old is handled before), so a / b has the sign of a
  const qt = asRational(mul(a, pow(b, -1)));
  return a.q === 1n && qt.q !== 1n ? undefined : qt;
}

/** Match noncommutative runs with integer powers represented as counted factors. */
function subsNcRun(e: Mul, old: Mul, nw: Expr): Expr | undefined {
  const commutative = old.args.filter((a) => a.isCommutative);
  const sourceCommutative = e.args.filter((a) => a.isCommutative);
  const commutativeOld = mul(...commutative);
  const source = mul(...sourceCommutative);
  let available: bigint | undefined;
  if (commutative.length) {
    const counts = breakup(new Mul(sourceCommutative));
    for (const [key, value] of breakup(new Mul(commutative))) {
      const have = counts.get(key);
      if (!have || have.exp.isNegative !== value.exp.isNegative) return undefined;
      const count = have.exp.p * value.exp.q / (have.exp.q * value.exp.p);
      available = available === undefined || count < available ? count : available;
    }
    if (available !== undefined && available < 1n) return undefined;
  }
  const runs = (m: Mul): [Expr, bigint][] => m.args.filter((a) => !a.isCommutative).map((a) =>
    a instanceof Pow && a.exp instanceof Rational && a.exp.isInteger && a.exp.isPositive ? [a.base, a.exp.p] : [a, 1n]);
  const pattern = runs(old);
  if (!pattern.length) {
    const replaced = subsOne(source, old, nw);
    return replaced.key === source.key ? undefined : mul(replaced, ...e.args.filter((a) => !a.isCommutative));
  }
  const factors = runs(e);
  const out: Expr[] = [];
  let used = 0n;
  for (let i = 0; i < factors.length;) {
    const [base, count] = at(factors, i);
    const matches = (available === undefined || used < available) && pattern.every(([b, n], j) => {
      const factor = factors[i + j];
      return factor !== undefined && factor[0].key === b.key && (j === 0 || j === pattern.length - 1 ? factor[1] >= n : factor[1] === n);
    });
    if (!matches || count < first(pattern)[1]) {
      out.push(subsOne(pow(base, Rational.of(count)), old, nw));
      i++;
      continue;
    }
    const firstCount = first(pattern)[1];
    if (pattern.length === 1) {
      const quotient = count / firstCount;
      const n = available === undefined || quotient < available - used ? quotient : available - used;
      out.push(pow(nw, n), pow(base, Rational.of(count - n * firstCount)));
      used += n;
      i++;
      continue;
    }
    out.push(pow(base, Rational.of(count - firstCount)), nw);
    used++;
    const lastIndex = i + pattern.length - 1;
    const last = at(factors, lastIndex);
    const remaining = last[1] - at(pattern, pattern.length - 1)[1];
    i = lastIndex;
    if (remaining) factors[i] = [last[0], remaining];
    else i++;
  }
  return used ? mul(source, pow(commutativeOld, -used), ...out) : undefined;
}

/** The factors of a commutative product as base -> rational exponent (SymPy Mul._eval_subs breakup). */
function breakup(e: Mul): Map<string, { base: Expr; exp: Rational }> {
  const out = new Map<string, { base: Expr; exp: Rational }>();
  for (const a of e.args) {
    let [b, x]: [Expr, Expr] = a instanceof Pow ? [a.base, a.exp] : [a, Rational.of(1n)];
    let co = ratOf(x);
    if (!co) {
      // b**(2*y): base b**y, exponent 2
      const c = x instanceof Mul ? ratOf(first(x.args)) : undefined;
      co = c ?? Rational.of(1n);
      b = pow(b, mul(x, pow(co, -1)));
    }
    x = co;
    const cur = out.get(b.key);
    out.set(b.key, { base: b, exp: cur ? asRational(add(cur.exp, x)) : co });
  }
  return out;
}

/** SymPy Mul._eval_subs for commutative products: old replaced as often as it divides e. */
function subsMul(e: Mul, old: Mul, nw: Expr): Expr | undefined {
  if (!e.isCommutative || !old.isCommutative) return subsNcRun(e, old, nw);
  const lead = (m: Mul): Rational | undefined => ratOf(first(m.args));
  const coOld0 = lead(old);
  if (coOld0?.isNegative) {
    const coSelf0 = lead(e);
    // (-4*x).subs(-2*x, y) = (-4*x).subs(2*x, -y); a positive coefficient does not contain -2
    if (coSelf0 === undefined) return undefined;
    return coSelf0.isNegative ? subsOne(e, mul(-1, old), mul(-1, nw)) : undefined;
  }
  const coSelf = lead(e);
  if (coOld0 && !coSelf) return undefined;
  const c = breakup(e);
  const oldC = breakup(old);
  let residual: Expr = Rational.of(1n);
  if (coOld0 && coSelf && coOld0.key !== coSelf.key && !coOld0.isOne) {
    const xmul = extractRational(coSelf, coOld0);
    if (xmul && !xmul.isZero) {
      const m = ratMultiplicity(coOld0, coSelf);
      c.delete(coSelf.key);
      const cur = c.get(coOld0.key);
      c.set(coOld0.key, { base: coOld0, exp: asRational(add(cur?.exp ?? 0, m)) });
      residual = mul(coSelf, pow(coOld0, -m));
    }
  }
  // old has a factor that is not a number, so k becomes finite
  let k = Infinity;
  let direction = 0;
  for (const [key, { exp: oe }] of oldC) {
    const mine = c.get(key);
    if (!mine) return undefined;
    const sign = mine.exp.isNegative === oe.isNegative ? 1 : -1;
    if (direction && direction !== sign) return undefined;
    direction = sign;
    // SymPy ndiv: the number of times oe divides mine.exp when one denominator divides the other
    const a = mine.exp;
    const r = a.q % oe.q === 0n || oe.q % a.q === 0n ? Math.trunc(a.value / oe.value) : 0;
    if (!r) return undefined;
    k = Math.min(k, Math.abs(r));
  }
  k *= direction;
  const rest: Expr[] = [residual];
  for (const [key, { base, exp }] of c) {
    const o = oldC.get(key);
    rest.push(subsOne(pow(base, o ? add(exp, mul(-k, o.exp)) : exp), old, nw));
  }
  return mul(pow(nw, k), ...rest);
}

/** Substitute a function head while preserving argument arity and differentiation variables. */
export function subsFunction(expr: Expr, name: string, replacement: (...args: Expr[]) => Expr, arities?: readonly number[]): Expr {
  const go = (e: Expr): Expr => {
    if (e instanceof Derivative) {
      let body = e.expr;
      const variables: Expr[] = [];
      const points: [Expr, Expr][] = [];
      for (const [v, n] of e.variableOrders) {
        const value = go(v);
        if (!(value instanceof Sym || value instanceof UndefFn)) {
          const dummy = new Dummy('xi');
          body = xreplace(body, [[v, dummy]]);
          variables.push(dummy, go(n));
          points.push([dummy, value]);
        } else variables.push(value, go(n));
      }
      const result = new Derivative([go(body), ...variables]);
      return points.length ? new SubsNode([result, ...points.map(([v]) => v), ...points.map(([, p]) => p)]) : result;
    }
    const args = e.args.map(go);
    const matches = (e instanceof UndefFn || e instanceof Fn) && e.name === name || e instanceof Pow && e.base.key === S.E.key && name === 'exp';
    if (matches) {
      const xs = e instanceof Pow ? [at(args, 1)] : args;
      if (arities === undefined || arities.includes(xs.length)) return replacement(...xs);
    }
    return args.some((a, i) => a.key !== at(e.args, i).key) ? rebuild(e, args) : e;
  };
  return go(expr);
}

impl.subsFunction = subsFunction;

/** Variables bound by a definite Integral or a Sum/Product (SymPy bound_symbols). */
export function boundSymbols(e: Expr): Expr[] {
  if (e instanceof Integral && e.args.length >= 3) return [e.variable];
  if (e instanceof ExtensionExpr) return (e.bindings()?.variables ?? []).map((i) => at(e.args, i));
  if (e instanceof Concrete) return e.limits.map(([k]) => k);
  return [];
}

function subsOne(e: Expr, old: Expr, nw: Expr): Expr {
  if (e.key === old.key) return nw;
  if (e instanceof Sym && old instanceof Pow && e.key === old.base.key) {
    const power = new Pow(e, S.One);
    const result = evalSubs(power, old, nw);
    if (result !== undefined && result !== power) return result;
  }
  if (e.args.length === 0) return e instanceof Sym ? (e.substituteInner((x) => subsOne(x, old, nw)) ?? e) : e;
  // Derivative._eval_subs preserves the independent differentiation variables.
  if (e instanceof Derivative && old instanceof Sym) {
    const variables = e.variableOrders.map(([v]) => v);
    const changingVariable = variables.some((v) => v.key === old.key);
    const validVariable = nw instanceof Sym || nw instanceof UndefFn;
    if (changingVariable && !validVariable) return new SubsNode([e, old, nw]);
    if (changingVariable && nw.key !== old.key && e.expr.has(nw)) return new SubsNode([e, old, nw]);
  }
  if (e instanceof SubsNode) return e.subsSelf(old, nw, (x) => subsOne(x, old, nw));
  // the variable of an indefinite integral replaced: the antiderivative at that point (SymPy (x, b) limit)
  if (e instanceof Integral && e.args.length === 2 && e.variable.key === old.key && !(nw instanceof Sym)) return new Integral([e.integrand, old, nw]);
  // a bound variable is not free: only the limits are substituted
  const bound = boundSymbols(e);
  if (bound.length && bound.some((b) => old.key === b.key)) {
    if (e instanceof ExtensionExpr) {
      // boundSymbols found the variables of an extension node through its bindings
      const b = defined(e.bindings(), 'bindings');
      const fixed = new Set([...b.variables, ...b.scope]);
      const args = e.args.map((a, i) => (fixed.has(i) ? a : subsOne(a, old, nw)));
      return args.some((a, i) => a !== e.args[i]) ? e.withArgs(args) : e;
    }
    if (e instanceof Integral) {
      // only the limits are substituted ((x, b) or (x, a, b))
      const lims = e.args.slice(2);
      const lims2 = lims.map((l) => subsOne(l, old, nw));
      return lims2.every((l, i) => l === lims[i]) ? e : rebuild(e, [e.integrand, e.variable, ...lims2]);
    }
    const args = e.args.map((a, i) => (i === 0 || (i - 1) % 3 === 0 ? a : subsOne(a, old, nw)));
    return args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;
  }
  if (e.kind === 'Set') {
    // a set binding a variable substitutes like SymPy's _eval_subs
    const rs = defined(impl.subsSet, 'sets')(e, old, nw, (x) => subsOne(x, old, nw));
    if (rs !== undefined) return rs;
  }
  if (e instanceof ExtensionExpr) {
    const own = e.subsSelf(old, nw, (x) => subsOne(x, old, nw));
    if (own !== undefined) return own;
  }
  const r = evalSubs(e, old, nw);
  if (r !== undefined) return r;
  if (e instanceof Piecewise) {
    const pairs: [Expr, Expr][] = [];
    for (const [value, condition] of e.pairs) {
      const substituted = subsOne(condition, old, nw);
      if (substituted === S.false) continue;
      pairs.push([subsOne(value, old, nw), substituted]);
      if (substituted === S.true) break;
    }
    return piecewise(...pairs);
  }
  const args = e.args.map((a) => subsOne(a, old, nw));
  if (e instanceof Derivative && old instanceof Sym && e.expr.key !== old.key && first(args).key !== e.expr.key) {
    const introduced = new Set([...nw.freeSymbols()].map((v) => v.key));
    if (e.variableCount.some(([v]) => introduced.has(v.key) && !old.has(v) && e.expr.has(v))) return new SubsNode([e, old, nw]);
  }
  return args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;
}

/**
 * Substitution like SymPy `subs`: pairs are applied in order (unless
 * `simultaneous`), and sums, products and powers are matched algebraically,
 * e.g. (x + y + z).subs(x + y, 1) = z + 1 and (x**4).subs(x**2, y) = y**2.
 */
export function subs(e: Expr, s: Substitution, opts: { simultaneous?: boolean } = {}): Expr {
  let pairs = toPairs(s);
  if (!Array.isArray(s)) {
    // unordered mapping (SymPy dict): more complex keys first, then by sort key
    pairs = [...pairs].sort((a, b) => {
      const d = countOps(b[0]) - countOps(a[0]);
      return d !== 0 ? d : compareKeys(sortKey(a[0]), sortKey(b[0]));
    });
  }
  if (opts.simultaneous) {
    const dummies = pairs.map((_, i) => new Sym(`_subs${i}`));
    let r = e;
    pairs.forEach(([o], i) => (r = subsOne(r, o, at(dummies, i))));
    return xreplace(r, pairs.map(([, n], i) => [at(dummies, i), n] as const));
  }
  let r = e;
  for (const [o, n] of pairs) r = subsOne(r, o, n);
  return r;
}

export function freeSymbols(e: Expr): Set<Expr> {
  const out = new Map<string, Expr>();
  const go = (x: Expr) => {
    const explicit = x instanceof ExtensionExpr ? x.freeSymbolsSelf() : undefined;
    if (explicit !== undefined) {
      for (const s of explicit) out.set(s.key, s);
      return;
    }
    const b = x instanceof ExtensionExpr ? x.bindings() : undefined;
    if (x instanceof Sym) {
      out.set(x.key, x);
      for (const s of x.innerFreeSymbols()) out.set(s.key, s);
    } else if (b) {
      const bound = new Set(b.variables.map((i) => at(x.args, i).key));
      x.args.forEach((a, i) => {
        if (b.variables.includes(i)) return;
        if (b.scope.includes(i)) {
          for (const s of freeSymbols(a)) if (!bound.has(s.key)) out.set(s.key, s);
        } else go(a);
      });
    } else if (x instanceof Derivative) {
      go(x.expr);
      for (const [, order] of x.variableOrders) go(order);
    } else if (x instanceof Integral && x.args.length >= 3) {
      // the integration variable of a definite integral (or one with an upper limit) is bound
      const v = x.variable;
      // A function can itself be the bound variable, e.g. Integral(f(x), (f(x), 1, g(y))).
      const integrand = v instanceof Sym ? x.integrand : xreplace(x.integrand, [[v, Rational.of(0)]]);
      for (const s of freeSymbols(integrand)) if (s.key !== v.key) out.set(s.key, s);
      x.args.slice(2).forEach(go);
    } else if (x instanceof Concrete) {
      for (const s of x.freeSymbols()) out.set(s.key, s);
    } else x.args.forEach(go);
  };
  go(e);
  return new Set(out.values());
}

/** Number of nodes in the tree, used as a complexity measure. */
export function countOps(e: Expr): number {
  let n = 1;
  for (const a of e.args) n += countOps(a);
  return n;
}

/** Does any node satisfy the predicate? */
export function some(e: Expr, pred: (e: Expr) => boolean): boolean {
  if (pred(e)) return true;
  return e.args.some((a) => some(a, pred));
}

impl.subs = (e, s) => subs(e, s);
impl.xreplace = xreplace;
impl.freeSymbols = freeSymbols;

/**
 * SymPy use(expr, func, level): func applied to the subexpressions at depth
 * `level` (0 is the expression itself); atoms above that depth are kept.
 */
export function use(e: ExprLike, func: (x: Expr) => Expr, level = 0): Expr {
  const go = (x: Expr, k: number): Expr => {
    if (k === 0) return func(x);
    if (x.args.length === 0) return x;
    return rebuild(
      x,
      x.args.map((a) => go(a, k - 1)),
    );
  };
  return go(sympify(e), level);
}

/** A pre-order traversal of an expression tree (SymPy preorder_traversal), with skip() to leave out the subtree of the last node. */
export class PreorderTraversal implements Iterable<Expr> {
  private skipped = false;
  constructor(
    readonly node: Expr,
    readonly keys: boolean | ((e: Expr) => unknown) = false,
  ) {}
  /** Do not visit the arguments of the node yielded last. */
  skip(): void {
    this.skipped = true;
  }
  *[Symbol.iterator](): Iterator<Expr> {
    yield* this.walk(this.node);
  }
  private *walk(x: Expr): Generator<Expr> {
    yield x;
    if (this.skipped) {
      this.skipped = false;
      return;
    }
    for (const a of this.orderedArgs(x)) yield* this.walk(a);
  }
  private orderedArgs(x: Expr): readonly Expr[] {
    const keys = this.keys;
    if (keys === true) return [...x.args].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
    if (keys === false) return x.args;
    return x.args
      .map((a) => [a, toKey(keys(a))] as const)
      .sort((p, q) => compareKeys(p[1], q[1]))
      .map(([a]) => a);
  }
}

/** A key function's value as a sort key (an expression by its sort key, a number or string as it is). */
const toKey = (v: unknown): Key => (v instanceof Expr ? sortKey(v) : typeof v === 'number' || typeof v === 'string' ? v : String(v));

/**
 * SymPy preorder_traversal(node, keys): the nodes of the tree, each before
 * its arguments; with keys (true for the default sort key, or a key
 * function) the arguments of each node are visited in sorted order.
 */
export function preorderTraversal(node: ExprLike, keys: boolean | ((e: Expr) => unknown) = false): PreorderTraversal {
  return new PreorderTraversal(sympify(node), keys);
}

/**
 * SymPy piecewise_fold (sympy/functions/elementary/piecewise.py): an
 * expression with Piecewise arguments as one Piecewise whose branches are
 * the expression at each branch of the arguments. Extension nodes and
 * boolean connectives are not folded (their arguments are).
 */
export function piecewiseFold(e: Expr): Expr {
  if (e.isAtom || e instanceof Piecewise) return e;
  const args = e.args.map(piecewiseFold);
  const i = args.findIndex((a) => a instanceof Piecewise);
  if (i < 0 || e instanceof ExtensionExpr || e instanceof BoolOp) return args.some((a, j) => a !== e.args[j]) ? rebuild(e, args) : e;
  const pairs: (readonly [Expr, Expr])[] = [];
  const selected = cast(at(args, i), Piecewise);
  const conditions = selected.pairs.map(([, c]) => c.key).join(";");
  for (const [index, [ei, ci]] of selected.pairs.entries()) {
    const v = piecewiseFold(rebuild(e, args.map((a, j) => {
      if (j === i) return ei;
      // Equal condition sequences select the same branch, avoiding a Cartesian product.
      if (a instanceof Piecewise && a.pairs.map(([, c]) => c.key).join(";") === conditions) return at(a.pairs, index)[0];
      return a;
    })));
    // a branch that is a Piecewise itself (another argument was one) is flattened into the conditions
    if (v instanceof Piecewise) for (const [ej, cj] of v.pairs) pairs.push([ej, and(ci, cj)]);
    else pairs.push([v, ci]);
  }
  return piecewise(...pairs);
}
