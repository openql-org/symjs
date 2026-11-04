// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Polar numbers on the Riemann surface of the logarithm (SymPy
 * exp_polar, polar_lift, periodic_argument, principal_branch,
 * unbranched_argument, unpolarify, extract_branch_factor) and the
 * branch rules of the exponential integrals that use them.
 */

import { isIntegerQ, isPositive } from '../core/assumptions';
import { defined, first, pair } from '../core/guard';
import type { Expr, ExprLike, Substitution } from '../core/nodes';
import { Add, Constant, Dummy, Fn, Mul, Pow, Rational, S, Special, Sym } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { asCoefficient } from '../core/methods';
import { rebuild, subs, xreplace } from '../core/traverse';
import { mpFns } from '../numeric/mpeval';
import { numericFns } from '../numeric/evalf';
import * as M from '../numeric/mpfun';
import { abs, arg, conjugateCommutes, evaluators, fn, im, log, re } from './elementary';
import { Chi, Ci, Ei, Shi, Si, expint, factorial, gamma } from './special';

export const expPolar = (z: ExprLike): Expr => fn('exp_polar', [z]);
export const polarLift = (z: ExprLike): Expr => fn('polar_lift', [z]);
export const periodicArgument = (z: ExprLike, period: ExprLike): Expr => fn('periodic_argument', [z, period]);
export const principalBranch = (z: ExprLike, period: ExprLike): Expr => fn('principal_branch', [z, period]);
export const unbranchedArgument = (z: ExprLike): Expr => periodicArgument(z, S.Infinity);

const ipi = () => mul(S.Pi, S.I);
const isFnN = (e: Expr, name: string): e is Fn => e instanceof Fn && e.name === name;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
export const isPolar = (e: Expr): boolean =>
  isFnN(e, 'exp_polar') ||
  isFnN(e, 'polar_lift') ||
  isFnN(e, 'principal_branch') ||
  (e instanceof Sym && e.assumptions.polar === true) ||
  (e instanceof Mul && e.args.some(isPolar) && e.args.every((a) => isPolar(a) || isPositive(a) === true)) ||
  (e instanceof Pow && isPolar(e.base));

/** SymPy Expr.extract_branch_factor: (rest, n) with the exp_polar argument reduced by 2*pi*I*n. */
export function extractBranchFactor(eIn: ExprLike, allowHalf = false): [Expr, Expr] {
  const e = sympify(eIn);
  let res: Expr = S.One;
  const exps: Expr[] = [];
  for (const a of e instanceof Mul ? e.args : [e]) {
    if (isFnN(a, 'exp_polar')) exps.push(first(a.args));
    else res = mul(res, a);
  }
  let piimult: Expr = S.Zero;
  const extras: Expr[] = [];
  for (let x = exps.pop(); x !== undefined; x = exps.pop()) {
    if (x instanceof Add) {
      exps.push(...x.args);
      continue;
    }
    if (x instanceof Mul) {
      const c = asCoefficient(x, ipi());
      if (c !== undefined) {
        piimult = add(piimult, c);
        continue;
      }
    }
    extras.push(x);
  }
  let coeff: Expr;
  let tail: Expr[];
  if (piimult.freeSymbols().size === 0) {
    coeff = piimult;
    tail = [];
  } else {
    const terms = piimult instanceof Add ? piimult.args : [piimult];
    coeff = add(...terms.filter((t) => t.freeSymbols().size === 0));
    tail = terms.filter((t) => t.freeSymbols().size > 0);
  }
  // round down to the nearest multiple of 2: n = ceiling(coeff/2 - 1/2)
  let n: Expr;
  let c: Expr;
  if (coeff instanceof Rational) {
    const half = Rational.of(coeff.p - coeff.q, 2n * coeff.q); // coeff/2 - 1/2
    const ceil = half.p >= 0n ? (half.p + half.q - 1n) / half.q : -((-half.p) / half.q);
    n = Rational.of(ceil);
    c = Rational.of(coeff.p - 2n * ceil * coeff.q, coeff.q); // coeff - 2 n
    if (allowHalf && c.key === S.One.key) {
      n = add(n, Rational.of(1n, 2n));
      c = S.Zero;
    }
  } else {
    // an irrational or complex number: its ceiling numerically, part by part like SymPy's
    // ceiling (a rational number would be exact)
    const v = coeff.toComplex();
    n = add(Rational.of(BigInt(Math.ceil(v.re / 2 - 0.5))), mul(Rational.of(BigInt(Math.ceil(v.im / 2))), S.I));
    c = add(coeff, mul(-2, n));
  }
  const newexp = add(mul(ipi(), add(c, ...tail)), ...extras);
  if (!(newexp instanceof Rational && newexp.isZero)) res = mul(res, expPolar(newexp));
  return [res, n];
}

/** SymPy _unpolarify(eq, exponents_only=True, pause). */
function unpolarifyStep(eq: Expr, pause: boolean): Expr {
  if (eq.args.length === 0) return eq;
  const go = unpolarifyStep;
  if (!pause) {
    if (isFnN(eq, 'exp_polar')) return exp(go(first(eq.args), false));
    if (isFnN(eq, 'principal_branch') && pair(eq.args)[1].key === mul(2, S.Pi).key) return go(first(eq.args), false);
    // (SymPy also descends into booleans and relations here; with exponentsOnly, the only mode
    // that uses this function, an unpaused node is part of an exponent and is never one)
    if (eq instanceof Add || eq instanceof Mul) return rebuild(eq, eq.args.map((a) => go(a, false)));
    if (isFnN(eq, 'polar_lift')) return go(first(eq.args), false);
  }
  if (eq instanceof Pow) {
    const expo = go(eq.exp, false);
    return pow(go(eq.base, !(isIntegerQ(expo) === true && !pause)), expo);
  }
  // the arguments of every other node, unbranched functions included, are paused
  const args = eq.args.map((a) => go(a, true));
  return args.every((a, i) => a === eq.args[i]) ? eq : rebuild(eq, args);
}

/**
 * Every polar construct replaced by its projection, inside any function: what SymPy's
 * unpolarify gives for the unbranched functions, applied to all of them (the integration
 * algorithms ported from SymPy rely on it).
 */
function unpolarifyAll(e: Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map(unpolarifyAll);
  if (isFnN(e, 'exp_polar')) return exp(first(args));
  if (isFnN(e, 'polar_lift')) return first(args);
  if (isFnN(e, 'principal_branch') && args[1]?.key === mul(2, S.Pi).key) return first(args);
  return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
}

/**
 * Replace polar constructs by ordinary numbers (SymPy unpolarify): the result has the same
 * projection to the complex plane. `subs` is applied first (and then, as in SymPy, the default mode
 * is used). With `exponentsOnly`, only the exponents of powers are unpolarified, as in SymPy.
 *
 * Without `exponentsOnly`, the arguments of every function are unpolarified, where SymPy keeps
 * them in the functions that are not unbranched (SymPy: unpolarify(besselj(a, polar_lift(x))) is
 * besselj(a, polar_lift(x)), here besselj(a, x)).
 */
export function unpolarify(eIn: ExprLike, opts: { subs?: Substitution; exponentsOnly?: boolean } = {}): Expr {
  const eq = sympify(eIn);
  if (opts.subs !== undefined) return unpolarify(subs(eq, opts.subs));
  if (opts.exponentsOnly !== true) return unpolarifyAll(eq);
  let res = eq;
  for (let next = unpolarifyStep(res, true); next.key !== res.key; next = unpolarifyStep(res, true)) res = next;
  // replacing exp_polar(0) by 1 and polar_lift(0) by 0 is always correct
  return xreplace(res, [
    [expPolar(0), S.One],
    [polarLift(0), S.Zero],
  ]);
}

/** SymPy periodic_argument._getunbranched: the argument of a polar number on the Riemann surface. */
function unbranched(ar: Expr): Expr | undefined {
  let u: Expr = S.Zero;
  for (const a of ar instanceof Mul ? ar.args : [ar]) {
    if (!isPolar(a)) u = add(u, arg(a));
    else if (isFnN(a, 'exp_polar')) u = add(u, im(first(a.args)));
    else if (a instanceof Pow) u = add(u, mul(re(a.exp), unbranchedArgument(a.base)), mul(im(a.exp), log(abs(a.base))));
    else if (isFnN(a, 'polar_lift')) u = add(u, arg(first(a.args)));
    else return undefined;
  }
  return u;
}

const evalPeriodicArgument = (ar: Expr, period: Expr): Expr | undefined => {
  if (isPositive(period) !== true) return undefined;
  if (isOo(period) && isFnN(ar, 'principal_branch')) return periodicArgument(...pair(ar.args));
  if (isFnN(ar, 'polar_lift') && (isOo(period) || (period.freeSymbols().size === 0 && period.toNumber() >= 2 * Math.PI))) return periodicArgument(first(ar.args), period);
  if (ar instanceof Mul) {
    const keep = ar.args.filter((x) => isPositive(x) !== true);
    if (keep.length !== ar.args.length) return periodicArgument(mul(...keep), period);
  }
  const u = unbranched(ar);
  if (u === undefined) return undefined;
  if ([...findFns(u)].some((n) => ['atan', 'atan2', 'periodic_argument'].includes(n))) return undefined;
  if (isOo(period)) return u;
  const q = mul(u, pow(period, -1));
  if (q.freeSymbols().size) return undefined;
  const t = add(q, Rational.of(-1n, 2n));
  const tv = t.toNumber();
  const n = Math.ceil(tv - 1e-12);
  return add(u, mul(-1, n, period));
};

function findFns(e: Expr): Set<string> {
  const out = new Set<string>();
  const go = (x: Expr) => {
    if (x instanceof Fn) out.add(x.name);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

const evalPrincipalBranch = (x: Expr, period: Expr): Expr | undefined => {
  if (isFnN(x, 'polar_lift')) return principalBranch(first(x.args), period);
  if (isOo(period)) return x;
  const factors = x instanceof Mul ? x.args : [x];
  let c: Expr = S.One;
  const others: Expr[] = [];
  for (const y of factors) {
    if (y.freeSymbols().size === 0 || isPositive(y) === true) c = mul(c, y);
    else others.push(y);
  }
  const a = periodicArgument(c, period);
  // c has no free symbols apart from positive factors, which periodic_argument drops, so an
  // evaluated a is a number
  if (isFnN(a, 'periodic_argument')) return undefined;
  const ub = unbranchedArgument(c);
  const absC = abs(unpolarify(c));
  if (ub.key !== a.key || (a instanceof Rational && a.isZero && others.length && !(c instanceof Rational && c.isOne))) {
    if (a instanceof Rational && a.isZero) {
      return others.length ? mul(absC, new Fn('principal_branch', [mul(...others), period])) : mul(absC, new Fn('exp_polar', [S.Zero]));
    }
    return mul(principalBranch(mul(expPolar(mul(S.I, a)), ...others), period), absC);
  }
  if (!others.length) return mul(expPolar(mul(a, S.I)), absC);
  return undefined;
};

const evalPolarLift = (z: Expr): Expr | undefined => {
  // oo*exp_polar(0) = oo and oo*exp_polar(I*pi) = -oo (SymPy's Mul absorbs the polar factor)
  if (z instanceof Special && (z.name === 'oo' || z.name === '-oo')) return z;
  if (z.freeSymbols().size === 0 && !(z instanceof Special)) {
    const a = arg(z);
    const known = [S.Zero, mul(S.Pi, Rational.of(1n, 2n)), mul(S.Pi, Rational.of(-1n, 2n)), S.Pi];
    if (known.some((k) => k.key === a.key)) return mul(expPolar(mul(S.I, a)), abs(z));
  }
  const args = z instanceof Mul ? z.args : [z];
  const included: Expr[] = [];
  const positive: Expr[] = [];
  const excluded: Expr[] = [];
  for (const a of args) {
    if (isPolar(a)) included.push(a);
    else if (isPositive(a) === true) positive.push(a);
    else excluded.push(a);
  }
  if (excluded.length < args.length) {
    if (excluded.length) return mul(...included, ...positive, polarLift(mul(...excluded)));
    if (included.length) return mul(...included, ...positive);
    return mul(...positive, expPolar(0));
  }
  return undefined;
};

// the rules of exp, log, Abs, arg and conjugate for polar numbers: log(exp_polar(z)) =
// unpolarify(z) (log.eval), |exp_polar(z)| = exp(re(z)) and |polar_lift(z)| = |z| (_eval_Abs),
// arg(exp_polar(z)) = periodic_argument(exp_polar(z), oo) (arg.eval) and
// conjugate(exp_polar(z)) = exp_polar(conjugate(z)) (ExpBase._eval_conjugate)
const elementaryBase = { log: defined(evaluators.log), abs: defined(evaluators.abs), arg: defined(evaluators.arg) };
evaluators.log = (z, ...rest) => (rest.length === 0 && isFnN(z, 'exp_polar') ? unpolarify(first(z.args)) : elementaryBase.log(z, ...rest));
evaluators.abs = (z) => {
  if (isFnN(z, 'exp_polar')) return exp(re(first(z.args)));
  if (isFnN(z, 'polar_lift')) return abs(first(z.args));
  // the Abs of a product evaluates its factors without this evaluator; as in SymPy, the factors
  // whose Abs does not evaluate stay together in one Abs
  const isLift = (t: Expr) => isFnN(t, 'exp_polar') || isFnN(t, 'polar_lift');
  if (!(z instanceof Mul) || !z.args.some(isLift)) return elementaryBase.abs(z);
  const known: Expr[] = [];
  const inside: Expr[] = [];
  for (const t of z.args.filter(isLift)) {
    const v = abs(t);
    if (isFnN(v, 'abs')) inside.push(t);
    else known.push(v);
  }
  const rest = abs(mul(...z.args.filter((t) => !isLift(t))));
  if (inside.length === 0) return mul(...known, rest);
  const restFactors = rest instanceof Mul ? rest.args : [rest];
  for (const t of restFactors) {
    if (isFnN(t, 'abs')) inside.push(first(t.args));
    else known.push(t);
  }
  return mul(...known, new Fn('abs', [mul(...inside)]));
};
evaluators.arg = (z) => (isFnN(z, 'exp_polar') ? unbranchedArgument(z) : elementaryBase.arg(z));
conjugateCommutes.add('exp_polar');
evaluators.exp_polar = () => undefined;
evaluators.polar_lift = evalPolarLift;
evaluators.periodic_argument = evalPeriodicArgument;
evaluators.principal_branch = evalPrincipalBranch;
// (no derivative: SymPy's exp_polar has no fdiff, diff(exp_polar(x), x) stays Derivative(exp_polar(x), x))
mpFns.exp_polar = (args, p) => M.cexp(first(args), p);
mpFns.polar_lift = (args) => first(args);
numericFns.exp_polar = (args) => {
  const z = first(args);
  const m = Math.exp(z.re);
  return { re: m * Math.cos(z.im), im: m * Math.sin(z.im) };
};
numericFns.polar_lift = (args) => first(args);

// ---------------------------------------------------------------------------
// branch rules of the exponential integrals
// ---------------------------------------------------------------------------

/** The evaluators of special.ts, captured before the branch rules below wrap them. */
const base = {
  Ei: defined(evaluators.Ei),
  expint: defined(evaluators.expint),
  Si: defined(evaluators.Si),
  Ci: defined(evaluators.Ci),
  Shi: defined(evaluators.Shi),
  Chi: defined(evaluators.Chi),
};
const pl = (z: ExprLike) => polarLift(z);
const extractFactor = (z: Expr, f: Expr): Expr | undefined => {
  const fs = z instanceof Mul ? z.args : [z];
  const i = fs.findIndex((t) => t.key === f.key);
  return i < 0 ? undefined : mul(...fs.filter((_, j) => j !== i));
};

evaluators.Ei = (z) => {
  const r = base.Ei(z);
  if (r !== undefined) return r;
  const [nz, n] = extractBranchFactor(z);
  if (!(n instanceof Rational && n.isZero)) return add(Ei(nz), mul(2, S.I, S.Pi, n));
  return undefined;
};

function trigIntegral(name: 'Si' | 'Ci' | 'Shi' | 'Chi', self: (z: Expr) => Expr, iFactor: (z: Expr, s: number) => Expr, minus: (z: Expr) => Expr, atZeroIsZero: boolean): void {
  const prev = base[name];
  evaluators[name] = (z) => {
    for (const [f, s] of [
      [pl(S.I), 1],
      [pl(mul(-1, S.I)), -1],
    ] as const) {
      const nz = extractFactor(z, f);
      if (nz !== undefined) return iFactor(nz, s);
    }
    const nm = extractFactor(z, pl(-1));
    if (nm !== undefined) return minus(nm);
    const r = prev(z);
    if (r !== undefined) return r;
    const [nz, n] = extractBranchFactor(z);
    if (n instanceof Rational && n.isZero) return undefined;
    return add(atZeroIsZero ? S.Zero : mul(2, S.Pi, S.I, n), self(nz));
  };
}

trigIntegral('Ci', Ci, (z, s) => add(Chi(z), mul(S.I, S.Pi, Rational.of(s, 2))), (z) => add(Ci(z), mul(S.I, S.Pi)), false);
trigIntegral('Chi', Chi, (z, s) => add(Ci(z), mul(S.I, S.Pi, Rational.of(s, 2))), (z) => add(Chi(z), mul(S.I, S.Pi)), false);
trigIntegral('Si', Si, (z, s) => mul(S.I, Shi(z), s), (z) => mul(-1, Si(z)), true);
trigIntegral('Shi', Shi, (z, s) => mul(S.I, Si(z), s), (z) => mul(-1, Shi(z)), true);

evaluators.expint = (nu, z) => {
  const r = base.expint(nu, z);
  if (r !== undefined) return unpolarify(r);
  const [nz, n] = extractBranchFactor(z);
  if (n instanceof Rational && n.isZero) return undefined;
  // an integer nu <= 0 is evaluated by base.expint (z**(nu - 1)*uppergamma(1 - nu, z))
  if (nu instanceof Rational && nu.isInteger) {
    return add(
      expint(nu, nz),
      mul(-2, S.Pi, S.I, n, pow(-1, add(nu, -1)), pow(factorial(add(nu, -1)), -1), pow(unpolarify(nz), add(nu, -1))),
    );
  }
  return add(mul(add(exp(mul(2, S.I, S.Pi, nu, n)), -1), pow(nz, add(nu, -1)), gamma(add(1, mul(-1, nu)))), expint(nu, nz));
};


// lowergamma(a, z) and uppergamma(a, z) are entire in z for a positive integer a (SymPy unpolarifies z)
for (const name of ['lowergamma', 'uppergamma'] as const) {
  const prev = defined(evaluators[name]);
  evaluators[name] = (a, z) => {
    if (a instanceof Rational && a.isInteger && a.isPositive) {
      const nz = unpolarify(z);
      if (nz.key !== z.key) return fn(name, [a, nz]);
    }
    return prev(a, z);
  };
}

/** SymPy _polarify. */
function polarifyInner(eq: Expr, lift: boolean, pause = false): Expr {
  if (isPolar(eq)) return eq;
  if (eq.freeSymbols().size === 0 && !pause && !(eq instanceof Special)) return polarLift(eq);
  if (eq instanceof Sym && !pause && lift) return polarLift(eq);
  if (eq.args.length === 0) return eq;
  if (eq instanceof Add) {
    const r = add(...eq.args.map((a) => polarifyInner(a, lift, true)));
    return lift ? polarLift(r) : r;
  }
  if (eq instanceof Pow && eq.base instanceof Constant && eq.base.name === 'E') return exp(polarifyInner(eq.exp, lift, false));
  if (eq instanceof Fn) return fn(eq.name, eq.args.map((a) => polarifyInner(a, lift, false)));
  return rebuild(eq, eq.args.map((a) => polarifyInner(a, lift, pause)));
}

/**
 * SymPy polarify: numbers become polar numbers (exp_polar) and, with subs,
 * the symbols are replaced by polar dummies; returns [expr, reps] in that
 * case (reps maps each dummy back to its symbol).
 */
export function polarify(ex: ExprLike, opts: { subs?: boolean; lift?: boolean } = {}): Expr | [Expr, [Expr, Expr][]] {
  const lift = opts.lift ?? false;
  const subs = lift ? false : (opts.subs ?? true);
  const eq = polarifyInner(sympify(ex), lift);
  if (!subs) return eq;
  const syms = [...eq.freeSymbols()].sort((a, b) => (a.name < b.name ? -1 : 1));
  const reps = syms.map((s) => [s, new Dummy(s.name, { ...s.assumptions, polar: true })] as [Expr, Expr]);
  return [xreplace(eq, reps), reps.map(([s, d]) => [d, s] as [Expr, Expr])];
}
