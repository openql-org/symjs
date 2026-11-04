// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Spherical Bessel and Hankel functions (SymPy functions/special/bessel.py):
 * hn1 and hn2, the rewrites and expand_func of jn, yn, hn1 and hn2, jn_zeros,
 * and the rewrites of the Airy functions as hypergeometric functions (kept
 * here because functions/special/bessel.ts cannot import functions/special/hyper.ts).
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { NotImplementedError } from '../../core/errors';
import { defined, first, pair } from '../../core/guard';
import { isIntegerQ } from '../../core/assumptions';
import type { Expr, ExprLike } from '../../core/nodes';
import { Float, Rational, S } from '../../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../../core/ops';
import { fnPartials } from '../../calculus/diff';
import { c as cx, cadd, cmul } from '../../numeric/complex';
import { numericFns } from '../../numeric/evalf';
import { mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import * as M from '../../numeric/mpfun';
import { besselJZeros } from '../../numeric/mpbesselzero';
import { registerRewrite } from '../../simplify/rewrite';
import { expand } from '../../simplify/expand';
import { cos, fn, sin } from '../elementary/elementary';
import { funcExpanders } from './special';
import { hyper } from './hyper';
import './bessel';

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const negOnePow = (e: ExprLike): Expr => pow(-1, e);
/** sqrt(pi/(2*z)) */
const sphericalFactor = (z: Expr): Expr => sqrt(mul(S.Pi, pow(mul(2, z), -1)));
/** The sign of I*yn in hn1 = jn + I*yn and hn2 = jn - I*yn (SymPy _hankel_kind_sign). */
const kindSign = (name: 'hn1' | 'hn2'): number => (name === 'hn1' ? 1 : -1);

// ---- spherical_bessel_fn and the expansions of integer orders --------------------------

/** Coefficients (lowest degree first) of a polynomial in t with integer coefficients. */
type Poly = bigint[];
const shift = (p: Poly): Poly => [0n, ...p];
const scale = (p: Poly, c: bigint): Poly => p.map((x) => x * c);
/** p - q for q not longer than p. */
const sub = (p: Poly, q: Poly): Poly => p.map((x, i) => x - (q[i] ?? 0n));

/** SymPy spherical_bessel_fn(n, z) (polys/orthopolys.py): fn(0) = 1/z, fn(1) = 1/z**2, fn(n - 1) + fn(n + 1) = (2n + 1)/z fn(n). */
export function sphericalBesselFn(n: number, z: ExprLike): Expr {
  let m2: Poly;
  let m1: Poly;
  let poly: Poly;
  if (n >= 0) {
    // dup_spherical_bessel_fn in t = 1/z
    [m2, m1] = [[1n], [0n, 1n]];
    for (let i = 2; i <= n; i++) [m2, m1] = [m1, sub(scale(shift(m1), BigInt(2 * i - 1)), m2)];
    poly = n < 1 ? [0n, 1n] : shift(m1);
  } else {
    // dup_spherical_bessel_fn_minus
    [m2, m1] = [[0n, 1n], [0n]];
    for (let i = 2; i <= -n; i++) [m2, m1] = [m1, sub(scale(shift(m1), BigInt(3 - 2 * i)), m2)];
    poly = m1;
  }
  const zz = sympify(z);
  return add(...poly.map((c, k) => mul(Rational.of(c), pow(zz, -k))));
}

/** jn(n, z) = fn(n, z)*sin(z) + (-1)**(n + 1)*fn(-n - 1, z)*cos(z) (SymPy _jn). */
function expandedJn(n: number, z: Expr): Expr {
  return add(mul(sphericalBesselFn(n, z), sin(z)), mul(negOnePow(n + 1), sphericalBesselFn(-n - 1, z), cos(z)));
}
/** yn(n, z) = (-1)**(n + 1)*fn(-n - 1, z)*sin(z) - fn(n, z)*cos(z) (SymPy _yn). */
function expandedYn(n: number, z: Expr): Expr {
  return add(mul(negOnePow(n + 1), sphericalBesselFn(-n - 1, z), sin(z)), mul(-1, sphericalBesselFn(n, z), cos(z)));
}

funcExpanders.jn = (args) => {
  const [n, z] = pair(args);
  return isInt(n) ? expandedJn(Number(n.p), z) : undefined;
};
funcExpanders.yn = (args) => {
  const [n, z] = pair(args);
  return isInt(n) ? expandedYn(Number(n.p), z) : undefined;
};
for (const name of ['hn1', 'hn2'] as const) {
  const s = kindSign(name);
  funcExpanders[name] = (args) => {
    const [n, z] = pair(args);
    if (isInt(n)) return expand(add(expandedJn(Number(n.p), z), mul(s, S.I, expandedYn(Number(n.p), z))));
    return add(fn('jn', [n, z]), mul(s, S.I, fn('yn', [n, z])));
  };
}

// ---- derivatives and numerics -------------------------------------------------------

for (const name of ['hn1', 'hn2'] as const) {
  // d/dz f(n, z) = f(n - 1, z) - (n + 1)/z * f(n, z) (SymPy SphericalBesselBase.fdiff)
  fnPartials[name] = (args, i) => {
    if (i !== 1) throw new NotImplementedError(`diff: ${name} w.r.t. its order`);
    const [n, z] = pair(args);
    return add(fn(name, [add(n, -1), z]), mul(-1, add(n, 1), pow(z, -1), fn(name, [n, z])));
  };
  const s = kindSign(name);
  // (like SymPy, only an integer order is evaluated)
  numericFns[name] = (args) => {
    const n = first(args);
    if (n.im !== 0 || !Number.isInteger(n.re)) throw new NotImplementedError(`${name} of a non-integer order`);
    return cadd(defined(numericFns['jn'], 'jn numerics')(args), cmul(cx(0, s), defined(numericFns['yn'], 'yn numerics')(args)));
  };
  // integer order: sqrt(pi/(2 z)) (J(n + 1/2, z) +- I (-1)**(n + 1) J(-n - 1/2, z)) (SymPy rewrite(besselj))
  mpFns[name] = (args, p) => {
    const [n, z] = pair(args);
    const [np, nq] = F.toRational(n[0]);
    if (!M.isReal(n) || nq !== 1n) throw new NotImplementedError(`${name} of a non-integer order`);
    const wp = p + 20;
    const besselj = defined(mpFns['besselj'], 'mp besselj');
    const half: M.Mpc = [{ man: 1n, exp: -1n }, F.ZERO];
    const j1 = besselj([M.cadd(n, half, wp), z], wp);
    const j2 = besselj([M.cneg(M.cadd(n, half, wp)), z], wp);
    const sign = (np + 1n) % 2n === 0n ? s : -s;
    const sum = M.cadd(j1, M.cmul([F.ZERO, F.fromInt(BigInt(sign))], j2, wp), wp);
    const factor = M.csqrt(M.cdiv([M.mpPi(wp), F.ZERO], M.cmul([F.fromInt(2n), F.ZERO], z, wp), wp), wp);
    return M.cmul(factor, sum, p);
  };
}

// ---- rewrites -------------------------------------------------------------------------

/** A rule applied only for an integer order (SymPy assume_integer_order). */
const integerOrder =
  (f: (n: Expr, z: Expr) => Expr) =>
  (args: readonly Expr[]): Expr | undefined => {
    const [n, z] = pair(args);
    return isIntegerQ(n) === true ? f(n, z) : undefined;
  };
const half = S.Half;

// jn and yn in terms of besselj, bessely and each other
registerRewrite('jn', 'besselj', (args) => {
  const [n, z] = pair(args);
  return mul(sphericalFactor(z), fn('besselj', [add(n, half), z]));
});
registerRewrite('jn', 'bessely', (args) => {
  const [n, z] = pair(args);
  return mul(negOnePow(n), sphericalFactor(z), fn('bessely', [add(mul(-1, n), S.NegHalf), z]));
});
registerRewrite('jn', 'yn', (args) => {
  const [n, z] = pair(args);
  return mul(negOnePow(n), fn('yn', [add(mul(-1, n), -1), z]));
});
registerRewrite('yn', 'besselj', integerOrder((n, z) => mul(negOnePow(add(n, 1)), sphericalFactor(z), fn('besselj', [add(mul(-1, n), S.NegHalf), z]))));
registerRewrite('yn', 'bessely', integerOrder((n, z) => mul(sphericalFactor(z), fn('bessely', [add(n, half), z]))));
registerRewrite('yn', 'jn', (args) => {
  const [n, z] = pair(args);
  return mul(negOnePow(add(n, 1)), fn('jn', [add(mul(-1, n), -1), z]));
});

// hn1 and hn2 (SymPy SphericalHankelBase)
for (const name of ['hn1', 'hn2'] as const) {
  const s = kindSign(name);
  registerRewrite(
    name,
    'besselj',
    integerOrder((n, z) => mul(sphericalFactor(z), add(fn('besselj', [add(n, half), z]), mul(s, S.I, negOnePow(add(n, 1)), fn('besselj', [add(mul(-1, n), S.NegHalf), z]))))),
  );
  registerRewrite(
    name,
    'bessely',
    integerOrder((n, z) => mul(sphericalFactor(z), add(mul(negOnePow(n), fn('bessely', [add(mul(-1, n), S.NegHalf), z])), mul(s, S.I, fn('bessely', [add(n, half), z]))))),
  );
  registerRewrite(name, 'yn', (args) => {
    const [n, z] = pair(args);
    return add(mul(negOnePow(n), fn('yn', [add(mul(-1, n), -1), z])), mul(s, S.I, fn('yn', [n, z])));
  });
  registerRewrite(name, 'jn', (args) => {
    const [n, z] = pair(args);
    return add(fn('jn', [n, z]), mul(s, S.I, negOnePow(add(n, 1)), fn('jn', [add(mul(-1, n), -1), z])));
  });
  const hankel = name === 'hn1' ? 'hankel1' : 'hankel2';
  registerRewrite(name, hankel, integerOrder((n, z) => mul(sphericalFactor(z), fn(hankel, [n, z]))));
}

// the Airy functions as hypergeometric functions (SymPy _eval_rewrite_as_hyper)
const third = Rational.of(1, 3);
const twoThirds = Rational.of(2, 3);
const g13 = (): Expr => fn('gamma', [third]);
const g23 = (): Expr => fn('gamma', [twoThirds]);
const h = (b: Expr, z: Expr): Expr => hyper([], [b], mul(pow(z, 3), Rational.of(1, 9)));
registerRewrite('airyai', 'hyper', (args) => {
  const z = first(args);
  const pf1 = pow(mul(pow(3, twoThirds), g23()), -1);
  const pf2 = mul(z, pow(mul(pow(3, third), g13()), -1));
  return add(mul(pf1, h(twoThirds, z)), mul(-1, pf2, h(Rational.of(4, 3), z)));
});
registerRewrite('airybi', 'hyper', (args) => {
  const z = first(args);
  const pf1 = pow(mul(pow(3, Rational.of(1, 6)), g23()), -1);
  const pf2 = mul(z, pow(3, Rational.of(1, 6)), pow(g13(), -1));
  return add(mul(pf1, h(twoThirds, z)), mul(pf2, h(Rational.of(4, 3), z)));
});
registerRewrite('airyaiprime', 'hyper', (args) => {
  const z = first(args);
  const pf1 = mul(pow(z, 2), pow(mul(2, pow(3, twoThirds), g23()), -1));
  const pf2 = pow(mul(pow(3, third), g13()), -1);
  return add(mul(pf1, h(Rational.of(5, 3), z)), mul(-1, pf2, h(third, z)));
});
registerRewrite('airybiprime', 'hyper', (args) => {
  const z = first(args);
  const pf1 = mul(pow(z, 2), pow(mul(2, pow(3, Rational.of(1, 6)), g23()), -1));
  const pf2 = mul(pow(3, Rational.of(1, 6)), pow(g13(), -1));
  return add(mul(pf1, h(Rational.of(5, 3), z)), mul(pf2, h(third, z)));
});

// ---- public API ---------------------------------------------------------------------

/** SymPy hn1(n, z) = jn(n, z) + I*yn(n, z): spherical Hankel function of the first kind. */
export const hn1 = (n: ExprLike, z: ExprLike): Expr => fn('hn1', [n, z]);
/** SymPy hn2(n, z) = jn(n, z) - I*yn(n, z): spherical Hankel function of the second kind. */
export const hn2 = (n: ExprLike, z: ExprLike): Expr => fn('hn2', [n, z]);

/**
 * SymPy jn_zeros(n, k, dps=15): the first k positive zeros of the spherical
 * Bessel function jn(n, z), i.e. of besselj(n + 1/2, z), as Floats with dps digits.
 * Only SymPy's default method ("sympy", by mpmath besseljzero) is available.
 * @example
 * jnZeros(2, 4, { dps: 5 })  // [5.7635, 9.0950, 12.323, 15.515]
 */
export function jnZeros(n: ExprLike, k: ExprLike, opts: { method?: string; dps?: ExprLike } = {}): Float[] {
  if ((opts.method ?? 'sympy') !== 'sympy') throw new NotImplementedError('Unknown method.');
  const prec = F.dpsToPrec(smallInt(opts.dps ?? 15));
  return besselJZeros(smallInt(n) + 0.5, smallInt(k), prec).map((r) => new Float(r, prec));
}

/** An integer argument as a JS number. */
function smallInt(x: ExprLike): number {
  const e = sympify(x);
  if (!isInt(e)) throw new TypeError(`an integer is required, got ${e.toString()}`);
  return Number(e.p);
}
