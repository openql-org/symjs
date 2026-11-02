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

/** Branch k of the Lambert W function by Halley iteration (double precision). */
export function cLambertW(z: C, k: number): C {
  // initial guess: asymptotic log expansion, or the branch-point series near -1/e
  const twoPiIk = c(0, 2 * Math.PI * k);
  let w: C;
  const nearBranch = Math.hypot(z.re + Math.exp(-1), z.im) < 0.3;
  if (k === 0 && nearBranch) w = cadd(c(-1), csqrtC(cmul(c(2 * Math.E), cadd(z, c(Math.exp(-1))))));
  else if (k === 0 && Math.hypot(z.re, z.im) <= 3) w = clog(cadd(c(1), z));
  else if (k === -1 && nearBranch && Math.abs(z.im) < 1e-300 && z.re < 0) w = cadd(c(-1), cmul(c(-1), csqrtC(cmul(c(2 * Math.E), cadd(z, c(Math.exp(-1)))))));
  else {
    const L1 = cadd(clog(z), twoPiIk);
    w = cadd(L1, cmul(c(-1), clog(L1)));
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

function csqrtC(z: C): C {
  return cpow(z, c(0.5));
}

