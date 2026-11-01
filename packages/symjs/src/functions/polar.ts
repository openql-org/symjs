// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Polar numbers on the Riemann surface of the logarithm (SymPy
 * exp_polar, polar_lift, periodic_argument, principal_branch,
 * unbranched_argument, unpolarify, extract_branch_factor) and the
 * branch rules of the exponential integrals that use them.
 */

import { isPositive } from '../core/assumptions';
import { Add, Expr, ExprLike, Fn, FnName, Mul, Pow, Rational, S, Special, Sym } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { asCoefficient } from '../core/methods';
import { rebuild } from '../core/traverse';
import { fnPartials } from '../calculus/diff';
import { mpFns } from '../numeric/mpeval';
import { numericFns } from '../numeric/evalf';
import * as M from '../numeric/mpfun';
import { abs, arg, evaluators, fn, im } from './elementary';
import { Chi, Ci, Ei, Shi, Si, expint, factorial, gamma } from './special';

export const expPolar = (z: ExprLike): Expr => fn('exp_polar', [z]);
export const polarLift = (z: ExprLike): Expr => fn('polar_lift', [z]);
export const periodicArgument = (z: ExprLike, period: ExprLike): Expr => fn('periodic_argument', [z, period]);
export const principalBranch = (z: ExprLike, period: ExprLike): Expr => fn('principal_branch', [z, period]);
export const unbranchedArgument = (z: ExprLike): Expr => periodicArgument(z, S.Infinity);

const ipi = () => mul(S.Pi, S.I);
const isFnN = (e: Expr, name: string): e is Fn => e instanceof Fn && e.name === name;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
const isPolar = (e: Expr): boolean => isFnN(e, 'exp_polar') || isFnN(e, 'polar_lift') || isFnN(e, 'principal_branch');

/** SymPy Expr.extract_branch_factor: (rest, n) with the exp_polar argument reduced by 2*pi*I*n. */
export function extractBranchFactor(eIn: ExprLike, allowHalf = false): [Expr, Expr] {
  const e = sympify(eIn);
  let res: Expr = S.One;
  const exps: Expr[] = [];
  for (const a of e instanceof Mul ? e.args : [e]) {
    if (isFnN(a, 'exp_polar')) exps.push(a.args[0]!);
    else res = mul(res, a);
  }
  let piimult: Expr = S.Zero;
  const extras: Expr[] = [];
  while (exps.length) {
    const x = exps.pop()!;
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
  if (!(coeff instanceof Rational)) return [e, S.Zero];
  // round down to the nearest multiple of 2
  const v = Rational.of(coeff.p, coeff.q * 2n);
  const half = add(v, Rational.of(-1n, 2n)) as Rational;
  const ceil = half.p >= 0n ? (half.p + half.q - 1n) / half.q : -((-half.p) / half.q);
  const branchfact = Rational.of(ceil * 2n);
  let n: Expr = Rational.of(ceil);
  let c = add(coeff, mul(-1, branchfact)) as Rational;
  if (allowHalf && c.p === c.q) {
    n = add(n, Rational.of(1n, 2n));
    c = S.Zero as Rational;
  }
  const newexp = add(mul(ipi(), add(c, ...tail)), ...extras);
  if (!(newexp instanceof Rational && newexp.isZero)) res = mul(res, expPolar(newexp));
  return [res, n];
}

/** Replace polar constructs by ordinary numbers (SymPy unpolarify). */
export function unpolarify(eIn: ExprLike): Expr {
  const go = (x: Expr): Expr => {
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    if (isFnN(x, 'exp_polar')) return exp(args[0]!);
    if (isFnN(x, 'polar_lift')) return args[0]!;
    if (isFnN(x, 'principal_branch') && args[1]!.key === mul(2, S.Pi).key) return args[0]!;
    return args.every((a, i) => a === x.args[i]) ? x : rebuild(x, args);
  };
  return go(sympify(eIn));
}

function unbranched(ar: Expr): Expr | undefined {
  let u: Expr = S.Zero;
  for (const a of ar instanceof Mul ? ar.args : [ar]) {
    if (isFnN(a, 'exp_polar')) u = add(u, im(a.args[0]!));
    else if (isFnN(a, 'polar_lift')) u = add(u, arg(a.args[0]!));
    else if (a instanceof Pow && isPolar(a.base)) return undefined;
    else if (!isPolar(a)) u = add(u, arg(a));
    else return undefined;
  }
  return u;
}

const evalPeriodicArgument = (ar: Expr, period: Expr): Expr | undefined => {
  if (isPositive(period) !== true) return undefined;
  if (isOo(period) && isFnN(ar, 'principal_branch')) return periodicArgument(ar.args[0]!, ar.args[1]!);
  if (isFnN(ar, 'polar_lift') && (isOo(period) || (period.freeSymbols().size === 0 && period.toNumber() >= 2 * Math.PI))) return periodicArgument(ar.args[0]!, period);
  if (ar instanceof Mul) {
    const keep = ar.args.filter((x) => isPositive(x) !== true);
    if (keep.length !== ar.args.length) return periodicArgument(mul(...keep), period);
  }
  const u = unbranched(ar);
  if (u === undefined || u.has(new Sym('__never__'))) return undefined;
  if ([...findFns(u)].some((n) => ['arg', 'atan', 'atan2', 'periodic_argument'].includes(n))) return undefined;
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
  if (isFnN(x, 'polar_lift')) return principalBranch(x.args[0]!, period);
  if (isOo(period)) return x;
  const factors = x instanceof Mul ? x.args : [x];
  let c: Expr = S.One;
  const others: Expr[] = [];
  for (const y of factors) {
    if (y.freeSymbols().size === 0 || isPositive(y) === true) c = mul(c, y);
    else others.push(y);
  }
  const a = periodicArgument(c, period);
  if (a.has(new Sym('__never__')) || isFnN(a, 'periodic_argument')) return undefined;
  if (a.freeSymbols().size) return undefined;
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

evaluators.exp_polar = () => undefined;
evaluators.polar_lift = evalPolarLift;
evaluators.periodic_argument = evalPeriodicArgument;
evaluators.principal_branch = evalPrincipalBranch;
fnPartials.exp_polar = ([z]) => expPolar(z!);
mpFns.exp_polar = ([z], p) => M.cexp(z!, p);
mpFns.polar_lift = ([z]) => z!;
numericFns.exp_polar = ([z]) => {
  const m = Math.exp(z!.re);
  return { re: m * Math.cos(z!.im), im: m * Math.sin(z!.im) };
};
numericFns.polar_lift = ([z]) => z!;

// ---------------------------------------------------------------------------
// branch rules of the exponential integrals
// ---------------------------------------------------------------------------

const base = { ...evaluators };
const pl = (z: ExprLike) => polarLift(z);
const extractFactor = (z: Expr, f: Expr): Expr | undefined => {
  const fs = z instanceof Mul ? z.args : [z];
  const i = fs.findIndex((t) => t.key === f.key);
  return i < 0 ? undefined : mul(...fs.filter((_, j) => j !== i));
};

evaluators.Ei = (z) => {
  const r = base.Ei!(z);
  if (r !== undefined) return r;
  const [nz, n] = extractBranchFactor(z);
  if (!(n instanceof Rational && n.isZero)) return add(Ei(nz), mul(2, S.I, S.Pi, n));
  return undefined;
};

function trigIntegral(name: 'Si' | 'Ci' | 'Shi' | 'Chi', self: (z: Expr) => Expr, iFactor: (z: Expr, s: number) => Expr, minus: (z: Expr) => Expr, atZeroIsZero: boolean): void {
  const prev = base[name as FnName]!;
  evaluators[name as FnName] = (z) => {
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
  const r = base.expint!(nu, z!);
  if (r !== undefined) return r;
  const [nz, n] = extractBranchFactor(z!);
  if (n instanceof Rational && n.isZero) return undefined;
  if (nu instanceof Rational && nu.isInteger) {
    if (!nu.isPositive) return undefined;
    return add(
      expint(nu, nz),
      mul(-2, S.Pi, S.I, n, pow(-1, add(nu, -1)), pow(factorial(add(nu, -1)), -1), pow(unpolarify(nz), add(nu, -1))),
    );
  }
  return add(mul(add(exp(mul(2, S.I, S.Pi, nu, n)), -1), pow(nz, add(nu, -1)), gamma(add(1, mul(-1, nu)))), expint(nu, nz));
};
