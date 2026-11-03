// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Minimal complex arithmetic for numeric evaluation.
 * Values are plain `{ re, im }` objects (compatible with q5m.js `Complex`).
 */

import type { ComplexValue as C } from '../core/nodes';

export const c = (re: number, im = 0): C => ({ re, im });

export const cadd = (a: C, b: C): C => ({ re: a.re + b.re, im: a.im + b.im });
export const cmul = (a: C, b: C): C => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
export const cdiv = (a: C, b: C): C => {
  const d = b.re * b.re + b.im * b.im;
  if (d === 0) throw new RangeError('Division by zero');
  return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d };
};
export const cneg = (a: C): C => ({ re: -a.re, im: -a.im });
export const cconj = (a: C): C => ({ re: a.re, im: -a.im });
export const cabs = (a: C): number => Math.hypot(a.re, a.im);
export const carg = (a: C): number => Math.atan2(a.im, a.re);

export const cexp = (a: C): C => {
  const r = Math.exp(a.re);
  return { re: r * Math.cos(a.im), im: r * Math.sin(a.im) };
};
export const clog = (a: C): C => {
  if (a.re === 0 && a.im === 0) throw new RangeError('log(0) is undefined');
  return { re: Math.log(cabs(a)), im: carg(a) };
};

export function cpow(a: C, b: C): C {
  if (b.im === 0 && Number.isInteger(b.re) && Math.abs(b.re) <= 64) {
    let n = Math.abs(b.re);
    let result: C = c(1);
    let base = a;
    while (n > 0) {
      if (n & 1) result = cmul(result, base);
      base = cmul(base, base);
      n >>= 1;
    }
    return b.re < 0 ? cdiv(c(1), result) : result;
  }
  if (a.re === 0 && a.im === 0) {
    if (b.re > 0) return c(0);
    throw new RangeError('Division by zero: 0 raised to a non-positive power');
  }
  if (a.im === 0 && a.re > 0 && b.im === 0) return c(Math.pow(a.re, b.re));
  return cexp(cmul(b, clog(a)));
}

export const csin = (a: C): C => ({ re: Math.sin(a.re) * Math.cosh(a.im), im: Math.cos(a.re) * Math.sinh(a.im) });
export const ccos = (a: C): C => ({ re: Math.cos(a.re) * Math.cosh(a.im), im: -Math.sin(a.re) * Math.sinh(a.im) });
export const ctan = (a: C): C => cdiv(csin(a), ccos(a));
export const csinh = (a: C): C => ({ re: Math.sinh(a.re) * Math.cos(a.im), im: Math.cosh(a.re) * Math.sin(a.im) });
export const ccosh = (a: C): C => ({ re: Math.cosh(a.re) * Math.cos(a.im), im: Math.sinh(a.re) * Math.sin(a.im) });
export const ctanh = (a: C): C => cdiv(csinh(a), ccosh(a));

const I1: C = c(0, 1);
const csqrt = (a: C): C => cpow(a, c(0.5));

// asin z = -i log(iz + sqrt(1 - z^2))
export const casin = (z: C): C => {
  if (z.im === 0 && Math.abs(z.re) <= 1) return c(Math.asin(z.re));
  return cmul(cneg(I1), clog(cadd(cmul(I1, z), csqrt(cadd(c(1), cneg(cmul(z, z)))))));
};
// acos z = pi/2 - asin z
export const cacos = (z: C): C => {
  if (z.im === 0 && Math.abs(z.re) <= 1) return c(Math.acos(z.re));
  return cadd(c(Math.PI / 2), cneg(casin(z)));
};
// atan z = (i/2) log((i + z)/(i - z))
export const catan = (z: C): C => {
  if (z.im === 0) return c(Math.atan(z.re));
  return cmul(c(0, 0.5), clog(cdiv(cadd(I1, z), cadd(I1, cneg(z)))));
};

/** Branch k of the Lambert W function by Halley iteration (double precision; starts as in mpmath lambertw). */
export function cLambertW(z: C, k: number): C {
  let w: C;
  if (k === 0 || k === -1) w = lambertwStart(z.re, z.im, k);
  else {
    const L1 = cadd(clog(z), c(0, 2 * Math.PI * k));
    w = asymptoticD(L1, clog(L1));
  }
  for (let i = 0; i < 100; i++) {
    const ew = cexp(w);
    const f = cadd(cmul(w, ew), cmul(c(-1), z));
    const wp1 = cadd(w, c(1));
    const denom = cadd(cmul(ew, wp1), cmul(c(-1), cdiv(cmul(cadd(w, c(2)), f), cmul(c(2), wp1))));
    const dw = cdiv(f, denom);
    w = cadd(w, cmul(c(-1), dw));
    if (Math.hypot(dw.re, dw.im) <= 1e-17 * Math.max(1, Math.hypot(w.re, w.im))) break;
  }
  return w;
}

const R0 = -0.367879441171442;

/** L1 - L2 + L2/L1 + L2 (L2 - 2)/(2 L1**2) in double precision. */
function asymptoticD(L1: C, L2: C): C {
  const t3 = cdiv(cmul(L2, cadd(L2, c(-2))), cmul(c(2), cmul(L1, L1)));
  return cadd(cadd(cadd(L1, cmul(c(-1), L2)), cdiv(L2, L1)), t3);
}

const sqrtD = (z: C): C => cpow(z, c(0.5));
/** -1 +- 2.33164398159712 sqrt(z - r) - 1.81218788563936 (z - r): the start near the branch point. */
const branchD = (z: C, sgn: 1 | -1): C => {
  const d = cadd(z, c(-R0));
  return cadd(cadd(c(-1), cmul(c(sgn * 2.33164398159712), sqrtD(d))), cmul(c(-1.81218788563936), d));
};

/**
 * A double-precision start for W_0 and W_-1 at x + iy (mpmath
 * _lambertw_approx_hybrid, ported from mpmath 1.3.0, BSD 3-Clause).
 */
export function lambertwStart(x: number, y: number, k: 0 | -1): C {
  const imagSign = y === 0 ? 0 : y < 0 ? -1 : 1;
  const z = c(x, y);
  let L1: C;
  if (k === 0) {
    if (-4 < y && y < 4 && -1 < x && x < 2.5) {
      if (imagSign !== 0) {
        // Taylor series in the upper / lower half-plane
        if (y > 1) return cadd(c(0.876, 0.645), cmul(c(0.118, -0.174), cadd(z, c(-0.75, -2.5))));
        if (y > 0.25) return cadd(c(0.505, 0.204), cmul(c(0.375, -0.132), cadd(z, c(-0.75, -0.5))));
        if (y < -1) return cadd(c(0.876, -0.645), cmul(c(0.118, 0.174), cadd(z, c(-0.75, 2.5))));
        if (y < -0.25) return cadd(c(0.505, -0.204), cmul(c(0.375, 0.132), cadd(z, c(-0.75, 0.5))));
      }
      // Taylor series near -1
      if (x < -0.5) {
        if (imagSign >= 0) return cadd(c(-0.318, 1.34), cmul(c(-0.697, -0.593), cadd(z, c(1))));
        return cadd(c(-0.318, -1.34), cmul(c(-0.697, 0.593), cadd(z, c(1))));
      }
      // the singularity near -1/e, the Taylor series near 0, a linear approximation
      if (x < -0.2) return branchD(z, 1);
      if (x < 0.5) return z;
      return cadd(c(0.2), cmul(c(0.3), z));
    }
    L1 = imagSign === 0 && x > 0 ? c(Math.log(x)) : clog(z);
  } else {
    if (imagSign >= 0 && y < 0.1 && -0.6 < x && x < -0.2) return branchD(z, -1);
    if (imagSign === 0 && -0.2 <= x && x < 0) {
      const l = Math.log(-x);
      return c(l - Math.log(-l));
    }
    L1 = cadd(clog(z), c(0, -2 * Math.PI));
  }
  return asymptoticD(L1, clog(L1));
}


