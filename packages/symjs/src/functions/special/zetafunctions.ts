// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/zeta_functions.py), BSD
// 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The Lerch transcendent (lerchphi), the polylogarithm (polylog), the
 * Dirichlet eta function, the Riemann Xi function and the Stieltjes
 * constants, with the rewrites of the Riemann and Hurwitz zeta functions
 * between them (SymPy zeta_functions).
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Float, Fn, Pow, Rational, S, Special, Sym } from '../../core/nodes';
import { at, pair } from '../../core/guard';
import { isIntegerQ, isNegative, isPositive, isZero } from '../../core/assumptions';
import { add, exp, mul, neg, pow, sqrt } from '../../core/ops';
import { Eq, piecewise } from '../../core/logic';
import { subs } from '../../core/traverse';
import { diff, fnPartials } from '../../calculus/diff';
import { mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import * as M from '../../numeric/mpfun';
import { type Mpc } from '../../numeric/mpfun';
import * as SP from '../../numeric/mpspecial';
import { caltzeta } from '../../numeric/mppolylog';
import { numericFns } from '../../numeric/evalf';
import { expandMulOnly } from '../../simplify/expand';
import { registerRewrite } from '../../simplify/rewrite';
import { abs, evaluators, fn, log } from '../elementary/elementary';
import { expandFuncRules, mpNumeric, noPartial } from './special';
import { expPolar, unpolarify } from '../elementary/complexes';

const R = (p: bigint | number, q: bigint | number = 1): Rational => Rational.of(p, q);
const isRat = (e: Expr, p: bigint, q = 1n): boolean => e instanceof Rational && e.p === p && e.q === q;
/** b**(-s), with (1/q)**(-s) = q**s as SymPy writes it. */
const powNeg = (b: Rational, s: Expr): Expr => {
  // 1/0**s = zoo**s
  if (b.isZero) return pow(S.ComplexInfinity, s);
  return b.p === 1n ? pow(R(b.q), s) : pow(pow(b, s), -1);
};
const isInteger = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const binom = (n: bigint, k: bigint): bigint => {
  let r = 1n;
  for (let i = 0n; i < k; i++) r = (r * (n - i)) / (i + 1n);
  return r;
};

// ---- constructors ---------------------------------------------------------------------

/** SymPy lerchphi(z, s, a): the Lerch transcendent sum_n z**n/(n + a)**s. */
export const lerchphi = (z: ExprLike, s: ExprLike, a: ExprLike): Expr => fn('lerchphi', [z, s, a]);
/** SymPy polylog(s, z): the polylogarithm sum_n z**n/n**s. */
export const polylog = (s: ExprLike, z: ExprLike): Expr => fn('polylog', [s, z]);
/** SymPy dirichlet_eta(s) and dirichlet_eta(s, a): the alternating zeta function. */
export const dirichletEta = (s: ExprLike, a?: ExprLike): Expr => fn('dirichlet_eta', a === undefined ? [s] : [s, a]);
/** SymPy riemann_xi(s): the Riemann Xi function s*(s - 1)*gamma(s/2)*zeta(s)/(2*pi**(s/2)). */
export const riemannXi = (s: ExprLike): Expr => fn('riemann_xi', [s]);
/** SymPy stieltjes(n) and stieltjes(n, a): the (generalized) Stieltjes constants. */
export const stieltjes = (n: ExprLike, a?: ExprLike): Expr => fn('stieltjes', a === undefined ? [n] : [n, a]);

const zeta = (s: Expr, a?: Expr): Expr => fn('zeta', a === undefined ? [s] : [s, a]);
const digamma = (x: Expr): Expr => fn('polygamma', [0, x]);

// ---- polylog --------------------------------------------------------------------------

/** SymPy _dilogtable: polylog(2, z) at special points. */
let dilogTable: Map<string, Expr> | undefined;
function dilog(z: Expr): Expr | undefined {
  if (!dilogTable) {
    const s5 = sqrt(5);
    const l2 = log(2);
    const pi2 = pow(S.Pi, 2);
    const lm = log(mul(add(s5, -1), S.Half));
    const entries: [Expr, Expr][] = [
      [S.Half, add(mul(R(1, 12), pi2), mul(R(-1, 2), pow(l2, 2)))],
      [R(2), add(mul(R(1, 4), pi2), mul(-1, S.I, S.Pi, l2))],
      [mul(R(-1, 2), add(s5, -1)), add(mul(R(-1, 15), pi2), mul(S.Half, pow(lm, 2)))],
      [mul(R(-1, 2), add(s5, 1)), add(mul(R(-1, 10), pi2), mul(-1, pow(log(mul(add(s5, 1), S.Half)), 2)))],
      [mul(S.Half, add(3, neg(s5))), add(mul(R(1, 15), pi2), neg(pow(lm, 2)))],
      [mul(S.Half, add(s5, -1)), add(mul(R(1, 10), pi2), neg(pow(lm, 2)))],
      [S.I, add(mul(S.I, S.Catalan), mul(R(-1, 48), pi2))],
      [neg(S.I), add(mul(-1, S.I, S.Catalan), mul(R(-1, 48), pi2))],
      [add(1, neg(S.I)), add(mul(R(1, 16), pi2), mul(-1, S.I, S.Catalan), mul(R(-1, 4), S.Pi, S.I, l2))],
      [add(1, S.I), add(mul(R(1, 16), pi2), mul(S.I, S.Catalan), mul(R(1, 4), S.Pi, S.I, l2))],
      [mul(S.Half, add(1, neg(S.I))), add(mul(R(-1, 8), pow(l2, 2)), mul(R(1, 8), S.Pi, S.I, l2), mul(R(5, 96), pi2), mul(-1, S.I, S.Catalan))],
    ];
    dilogTable = new Map(entries.map(([k, v]) => [k.key, v]));
  }
  return dilogTable.get(z.key);
}

const hasPolar = (e: Expr): boolean => (e instanceof Fn && (e.name === 'exp_polar' || e.name === 'polar_lift')) || e.args.some(hasPolar);

/** SymPy polylog.eval. */
evaluators.polylog = (s, z) => {
  const isNumber = z.freeSymbols().size === 0;
  if (isNumber) {
    if (isRat(z, 1n)) return zeta(s);
    if (isRat(z, -1n)) return neg(dirichletEta(s));
    if (isRat(z, 0n)) return S.Zero;
    if (isRat(s, 2n)) {
      const v = dilog(z);
      if (v !== undefined) return v;
    }
  }
  if (isZero(z) === true) return S.Zero;
  // z.equals(1) is False for an expression with symbols and for a number other than 1
  if (equalsOne(z)) return zeta(s);
  if (isRat(s, 0n) || isZero(s) === true) return mul(z, pow(add(1, neg(z)), -1));
  if (isRat(s, -1n)) return mul(z, pow(add(1, neg(z)), -2));
  // polylog is branched, but not over the unit disk
  if (isNumber && hasPolar(z) && abs(unpolarify(z)).toNumber() <= 1) return polylog(s, unpolarify(z));
  return undefined;
};

/** SymPy z.equals(1): false for an expression with symbols, a number that is not 1 or one that cannot be evaluated. */
function equalsOne(z: Expr): boolean {
  if (z.freeSymbols().size > 0) return false;
  try {
    const v = unpolarify(z).toComplex();
    return Math.abs(v.re - 1) < 1e-14 && Math.abs(v.im) < 1e-14;
  } catch {
    return false;
  }
}

// d/dz polylog(s, z) = polylog(s - 1, z)/z
fnPartials.polylog = (args, i) => {
  const [s, z] = pair(args);
  return i === 1 ? mul(polylog(add(s, -1), z), pow(z, -1)) : noPartial('polylog', args, i);
};
registerRewrite('polylog', 'lerchphi', (args) => {
  const [s, z] = pair(args);
  return mul(z, lerchphi(z, s, 1));
});

/** SymPy polylog._eval_expand_func: -log(1 - z) for s = 1, a rational function for an integer s <= 0. */
function expandPolylog(s: Expr, z: Expr): Expr {
  if (isRat(s, 1n)) return neg(log(add(1, neg(z))));
  if (isInteger(s) && !s.isPositive) {
    const u = new Sym('_u');
    let start = mul(u, pow(add(1, neg(u)), -1));
    for (let k = 0n; k < -s.p; k++) start = mul(u, diff(start, u));
    return subs(expandMulOnly(start), [[u, z]]);
  }
  return polylog(s, z);
}
expandFuncRules.polylog = (e) => {
  const [s, z] = pair(e.args);
  const r = expandPolylog(s, z);
  return r.key === e.key ? undefined : r;
};

// ---- lerchphi -------------------------------------------------------------------------

// d/dz lerchphi = (lerchphi(z, s - 1, a) - a*lerchphi(z, s, a))/z, d/da lerchphi = -s*lerchphi(z, s + 1, a)
fnPartials.lerchphi = (args, i) => {
  const [z, s, a] = [at(args, 0), at(args, 1), at(args, 2)];
  if (i === 0) return mul(add(lerchphi(z, add(s, -1), a), mul(-1, a, lerchphi(z, s, a))), pow(z, -1));
  if (i === 2) return mul(-1, s, lerchphi(z, add(s, 1), a));
  return noPartial('lerchphi', args, i);
};

/** floor of a nonnegative Rational. */
const floorQ = (a: Rational): bigint => a.p / a.q;

/** z = exp(I*pi*r) with a rational r (SymPy: isinstance(z, exp) and (z.args[0]/(pi*I)).is_Rational, or z in (-1, I, -I)): r/2 = p/q. */
function rootOfUnity(z: Expr): [bigint, bigint] | undefined {
  if (isRat(z, -1n)) return [1n, 2n];
  if (z.key === S.I.key) return [1n, 4n];
  if (z.key === neg(S.I).key) return [-1n, 4n];
  if (z instanceof Pow && z.base.key === S.E.key) {
    const r = mul(z.exp, pow(mul(2, S.Pi, S.I), -1));
    if (r instanceof Rational) return [r.p, r.q];
  }
  return undefined;
}

/** exp(2*pi*I*k/n) with the exponent reduced to (-pi, pi] (as SymPy's exp writes it). */
function unitRoot(k: bigint, n: bigint): Expr {
  let r = ((k % n) + n) % n;
  if (2n * r > n) r -= n;
  return exp(mul(2, S.Pi, S.I, R(r, n)));
}

/** SymPy lerchphi._eval_expand_func. */
function expandLerchphi(z: Expr, s: Expr, a0: Expr): Expr | undefined {
  if (isRat(z, 1n)) return zeta(s, a0);
  if (isInteger(s) && !s.isPositive) {
    // (t + a)**(-s) = sum_k c_k t**k, and sum_k c_k (t d/dt)**k 1/(1 - t)
    const t = new Sym('_t');
    const m = -s.p;
    let start = pow(add(1, neg(t)), -1);
    const res: Expr[] = [];
    for (let k = 0n; k <= m; k++) {
      res.push(mul(R(binom(m, k)), pow(a0, R(m - k)), start));
      start = mul(t, diff(start, t));
    }
    return subs(add(...res), [[t, z]]);
  }
  if (a0 instanceof Rational) {
    // Roach, Hypergeometric Function Representations (ISSAC 1997), section 18:
    // first reduce a to the interval (0, 1]
    let a = a0;
    let addend: Expr = S.Zero;
    let factor: Expr = S.One;
    if (a.p > a.q) {
      let n = floorQ(a);
      if (a.q === 1n) n -= 1n;
      a = R(a.p - n * a.q, a.q);
      factor = pow(z, R(-n));
      addend = add(...Array.from({ length: Number(n) }, (_, k) => mul(-1, pow(z, R(BigInt(k) - n)), powNeg(R(a.p + BigInt(k) * a.q, a.q), s))));
    } else if (a.p <= 0n) {
      const n = floorQ(R(-a.p, a.q)) + 1n;
      a = R(a.p + n * a.q, a.q);
      factor = pow(z, R(n));
      addend = add(...Array.from({ length: Number(n) }, (_, k) => mul(pow(z, R(n - 1n - BigInt(k))), powNeg(R(a.p - BigInt(k + 1) * a.q, a.q), s))));
    }
    const [m, n] = [a.p, a.q];
    const root = pow(z, R(1n, n));
    const terms: Expr[] = [];
    for (let k = 0n; k < n; k++) {
      // zet**k = exp_polar(2*pi*I*k/n), its unpolarified value exp(2*pi*I*k/n)
      let p = polylog(s, mul(k === 0n ? S.One : expPolar(mul(2, S.Pi, S.I, R(k, n))), root));
      if (p instanceof Fn && p.name === 'polylog') p = expandPolylog(pair(p.args)[0], pair(p.args)[1]);
      terms.push(mul(p, unitRoot(-k * m, n), pow(root, R(-m))));
    }
    return add(addend, mul(factor, pow(R(n), add(s, -1)), add(...terms)));
  }
  const root = rootOfUnity(z);
  if (root) {
    const [p, q] = root;
    return add(...Array.from({ length: Number(q) }, (_, k) => mul(unitRoot(BigInt(k) * p, q), pow(pow(R(q), s), -1), zeta(s, mul(add(k, a0), R(1n, q))))));
  }
  return undefined;
}
expandFuncRules.lerchphi = (e) => expandLerchphi(at(e.args, 0), at(e.args, 1), at(e.args, 2));

/** SymPy lerchphi._eval_rewrite_helper: the expansion when it has the target function. */
for (const target of ['zeta', 'polylog'] as const) {
  registerRewrite('lerchphi', target, (args) => {
    const r = expandLerchphi(at(args, 0), at(args, 1), at(args, 2));
    return r !== undefined && hasFn(r, target) ? r : undefined;
  });
}
const hasFn = (e: Expr, name: string): boolean => (e instanceof Fn && e.name === name) || e.args.some((a) => hasFn(a, name));

// ---- zeta -----------------------------------------------------------------------------

registerRewrite('zeta', 'dirichlet_eta', (args) => {
  const [s, a] = args;
  if (s === undefined || (a !== undefined && !isRat(a, 1n))) return undefined;
  return mul(dirichletEta(s), pow(add(1, neg(pow(2, add(1, neg(s))))), -1));
});
registerRewrite('zeta', 'lerchphi', (args) => lerchphi(1, at(args, 0), args[1] ?? S.One));

/** SymPy zeta._eval_expand_func: zeta(s) - harmonic(a - 1, s) for a positive integer a. */
expandFuncRules.zeta = (e) => {
  const [s, a] = e.args;
  if (s === undefined || a === undefined || isIntegerQ(a) !== true) return undefined;
  // (harmonic(n, s) of an integer n is the sum of k**(-s))
  if (a instanceof Rational && a.isPositive) return add(zeta(s), ...Array.from({ length: Number(a.p) - 1 }, (_, k) => neg(pow(R(k + 1), neg(s)))));
  if (isPositive(a) === true) return add(zeta(s), neg(fn('harmonic', [add(a, -1), s])));
  if (isPositive(a) === false && (isIntegerQ(s) === false || isPositive(s) === true)) return S.NaN;
  return undefined;
};

// ---- dirichlet_eta --------------------------------------------------------------------

/** SymPy dirichlet_eta.eval. */
evaluators.dirichlet_eta = (s, ...rest) => {
  const a = rest[0];
  if (a !== undefined && isRat(a, 1n)) return dirichletEta(s);
  if (a === undefined) {
    if (isRat(s, 1n)) return log(2);
    const z = zeta(s);
    return hasFn(z, 'zeta') ? undefined : mul(add(1, neg(pow(2, add(1, neg(s))))), z);
  }
  if (isRat(s, 1n)) return add(log(2), neg(digamma(a)), digamma(mul(add(a, 1), S.Half)));
  const z1 = zeta(s, a);
  const z2 = zeta(s, mul(add(a, 1), S.Half));
  return hasFn(z1, 'zeta') || hasFn(z2, 'zeta') ? undefined : add(z1, mul(-1, pow(2, add(1, neg(s))), z2));
};
registerRewrite('dirichlet_eta', 'zeta', (args) => {
  const [s, a] = [at(args, 0), args[1]];
  if (a === undefined || isRat(a, 1n)) return piecewise([log(2), Eq(s, 1)], [mul(add(1, neg(pow(2, add(1, neg(s))))), zeta(s)), true]);
  return piecewise(
    [add(log(2), neg(digamma(a)), digamma(mul(add(a, 1), S.Half))), Eq(s, 1)],
    [add(zeta(s, a), mul(-1, pow(2, add(1, neg(s))), zeta(s, mul(add(a, 1), S.Half)))), true],
  );
});
// eta(s, a) = zeta(s, a) - 2**(1 - s)*zeta(s, (a + 1)/2), at s = 1 log(2) - digamma(a) + digamma((a + 1)/2)
mpFns.dirichlet_eta = (args, prec) => {
  const s = at(args, 0);
  const a = args[1];
  if (a === undefined) return caltzeta(s, prec);
  const wp = prec + 30;
  const half: Mpc = [{ man: 1n, exp: -1n }, F.ZERO];
  const a2 = M.cmul(M.cadd(a, M.C1, wp), half, wp);
  if (M.isReal(s) && F.cmp(s[0], F.ONE) === 0) {
    const two: Mpc = [F.fromInt(2n), F.ZERO];
    const v = M.cadd(M.csub(M.clog(two, wp), SP.cpolygamma(0, a, wp), wp), SP.cpolygamma(0, a2, wp), wp);
    return [F.round(v[0], prec), F.round(v[1], prec)];
  }
  const p2 = M.cpow([F.fromInt(2n), F.ZERO], M.csub(M.C1, s, wp), wp);
  const v = M.csub(SP.czeta(s, wp, a), M.cmul(p2, SP.czeta(s, wp, a2), wp), wp);
  return [F.round(v[0], prec), F.round(v[1], prec)];
};

// ---- riemann_xi -----------------------------------------------------------------------

const xiOfZeta = (s: Expr, z: Expr): Expr => mul(s, add(s, -1), fn('gamma', [mul(s, S.Half)]), z, pow(mul(2, pow(S.Pi, mul(s, S.Half))), -1));

/** SymPy riemann_xi.eval: 1/2 at 0 and 1, the zeta form where zeta(s) evaluates. */
evaluators.riemann_xi = (s) => {
  if (isRat(s, 0n) || isRat(s, 1n)) return S.Half;
  const z = zeta(s);
  return z instanceof Fn && z.name === 'zeta' ? undefined : xiOfZeta(s, z);
};
registerRewrite('riemann_xi', 'zeta', (args) => xiOfZeta(at(args, 0), zeta(at(args, 0))));

// ---- stieltjes ------------------------------------------------------------------------

/** SymPy stieltjes.eval. */
evaluators.stieltjes = (n, ...rest) => {
  const a = rest[0];
  if (a !== undefined) {
    if (a instanceof Special && a.name === 'nan') return S.NaN;
    if (isInteger(a) && !a.isPositive) return S.ComplexInfinity;
  }
  const aOne = a === undefined || isRat(a, 1n);
  if (n instanceof Special && n.name === 'nan') return S.NaN;
  if (n instanceof Rational || n instanceof Float) {
    if (!(n instanceof Rational && n.isInteger && !n.isNegative)) return S.ComplexInfinity;
    if (n.isZero && aOne) return S.EulerGamma;
  }
  // (SymPy also gives EulerGamma for an n known to be zero, which the assumptions do not derive for a symbol)
  if (isNegative(n) === true || isIntegerQ(n) === false) return S.ComplexInfinity;
  return undefined;
};

for (const name of ['polylog', 'lerchphi', 'dirichlet_eta'] as const) numericFns[name] = (args) => mpNumeric(name, args);
