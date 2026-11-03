// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Arbitrary-precision values of the special functions (Gamma, zeta, error
 * functions, exponential integrals, Lambert W, Bessel and Airy functions),
 * registered into the evaluator table of numeric/mpeval. Imported by the
 * modules defining these functions so that the core does not carry them.
 */

import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import * as F from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc } from './mpfun';
import * as SP from './mpspecial';
import * as EI from './mpexpint';
import { clambertw } from './mplambertw';
import { caltzeta, clerchphi, cpolylog } from './mppolylog';
import * as OP from './mporthopoly';
import { cellipe, cellipeInc, cellipf, cellipk, cellippi } from './mpelliptic';
import { mpFn1, mpFn2, mpFns } from './mpeval';

const toInt = (z: Mpc): number => {
  const [p, q] = F.toRational(z[0]);
  if (!F.isZero(z[1]) || q !== 1n) throw new TypeError('integer expected');
  return Number(p);
};
const one: Mpc = M.C1;

Object.assign(mpFns, {
  gamma: mpFn1(SP.cgamma),
  loggamma: mpFn1(SP.cloggamma),
  factorial: mpFn1((a, p) => SP.cgamma(M.cadd(a, one, p + 20), p)),
  polygamma: mpFn2((n, z, p) => SP.cpolygamma(toInt(n), z, p)),
  harmonic: (args, p) => {
    const wp = p + 20;
    const n1 = M.cadd(at(args, 0), one, wp);
    // H(n, m) = zeta(m) - zeta(m, n + 1)
    const m = args[1];
    if (m && !(M.isReal(m) && F.cmp(m[0], F.ONE) === 0)) return M.csub(SP.czeta(m, wp), SP.czeta(m, wp, n1), p);
    return M.cadd(SP.cpolygamma(0, n1, wp), [M.mpEuler(wp), ZERO], p);
  },
  catalan: mpFn1((z, p) => {
    // 4^z Gamma(z + 1/2) / (sqrt(pi) Gamma(z + 2))
    const wp = p + 30;
    const half: Mpc = [{ man: 1n, exp: -1 }, ZERO];
    const num = M.cmul(M.cpow([F.fromInt(4n), ZERO], z, wp), SP.cgamma(M.cadd(z, half, wp), wp), wp);
    const den = M.cmul([F.sqrt(M.mpPi(wp), wp), ZERO], SP.cgamma(M.cadd(z, [F.fromInt(2n), ZERO], wp), wp), wp);
    return M.cdiv(num, den, p);
  }),
  beta: mpFn2((a, b, p) => {
    const wp = p + 30;
    return M.cdiv(M.cmul(SP.cgamma(a, wp), SP.cgamma(b, wp), wp), SP.cgamma(M.cadd(a, b, wp), wp), p);
  }),
  binomial: mpFn2((n, k, p) => {
    const wp = p + 30;
    const [kp, kq] = F.toRational(k[0]);
    if (M.isReal(k) && kq === 1n && kp >= 0n && kp <= 10000n) {
      // n (n - 1) ... (n - k + 1) / k!, also at the poles of the Gamma form
      let num = one;
      for (let i = 0n; i < kp; i++) num = M.cdiv(M.cmul(num, M.csub(n, [F.fromInt(i), ZERO], wp), wp), [F.fromInt(i + 1n), ZERO], wp);
      return [F.round(num[0], p), F.round(num[1], p)];
    }
    const g = (z: Mpc) => SP.cgamma(M.cadd(z, one, wp), wp);
    return M.cdiv(g(n), M.cmul(g(k), g(M.csub(n, k, wp)), wp), p);
  }),
  zeta: (args, p) => SP.czeta(at(args, 0), p, args[1]),
  dirichlet_eta: (args, p) => {
    if (args.length > 1) throw new NotImplementedError('dirichlet_eta(s, a)');
    return caltzeta(at(args, 0), p);
  },
  polylog: mpFn2(cpolylog),
  lerchphi: (args, p) => clerchphi(at(args, 0), at(args, 1), at(args, 2), p),
  legendre: mpFn2(OP.clegendre),
  assoc_legendre: (args, p) => OP.clegenp(at(args, 0), at(args, 1), at(args, 2), p),
  jacobi: (args, p) => OP.cjacobi(at(args, 0), at(args, 1), at(args, 2), at(args, 3), p),
  gegenbauer: (args, p) => OP.cgegenbauer(at(args, 0), at(args, 1), at(args, 2), p),
  chebyshevt: mpFn2(OP.cchebyt),
  chebyshevu: mpFn2(OP.cchebyu),
  elliptic_k: mpFn1(cellipk),
  elliptic_e: (args, p) => (args.length > 1 ? cellipeInc(at(args, 0), at(args, 1), p) : cellipe(at(args, 0), p)),
  elliptic_f: mpFn2(cellipf),
  elliptic_pi: (args, p) => (args.length > 2 ? cellippi(at(args, 0), at(args, 1), at(args, 2), p) : cellippi(at(args, 0), undefined, at(args, 1), p)),
  erf: mpFn1(SP.cerf),
  erfc: mpFn1(SP.cerfc),
  erfi: mpFn1(SP.cerfi),
  erf2: mpFn2((x, y, p) => M.csub(SP.cerf(y, p + 20), SP.cerf(x, p + 20), p)),
  erfinv: mpFn1((a, p) => {
    if (!M.isReal(a)) throw new NotImplementedError('complex erfinv');
    return [SP.erfinv(a[0], p), ZERO];
  }),
  erfcinv: mpFn1((a, p) => {
    if (!M.isReal(a)) throw new NotImplementedError('complex erfcinv');
    return [SP.erfinv(F.sub(F.ONE, a[0], p + 20), p), ZERO];
  }),
  fresnels: mpFn1((a, p) => SP.cfresnel('S', a, p)),
  fresnelc: mpFn1((a, p) => SP.cfresnel('C', a, p)),
  Ei: mpFn1(EI.cei),
  expint: mpFn2(EI.cexpint),
  LambertW: (args, p) => {
    const k = args[1];
    return clambertw(at(args, 0), k ? toInt(k) : 0, p);
  },
  besselj: mpFn2((nu, z, p) => mpBessel('J', nu, z, p)),
  bessely: mpFn2((nu, z, p) => mpBessel('Y', nu, z, p)),
  besseli: mpFn2((nu, z, p) => mpBessel('I', nu, z, p)),
  besselk: mpFn2((nu, z, p) => mpBessel('K', nu, z, p)),
  airyai: mpFn1((z, p) => mpAiry('ai', z, p)),
  airybi: mpFn1((z, p) => mpAiry('bi', z, p)),
  airyaiprime: mpFn1((z, p) => mpAiry('aip', z, p)),
  airybiprime: mpFn1((z, p) => mpAiry('bip', z, p)),
  li: mpFn1(EI.cli),
  Li: mpFn1((a, p) => M.csub(EI.cli(a, p + 20), EI.cli([F.fromInt(2n), ZERO], p + 20), p)),
  Si: mpFn1(EI.csi),
  Shi: mpFn1(EI.cshi),
  Ci: mpFn1(EI.cci),
  Chi: mpFn1(EI.cchi),
  lowergamma: mpFn2(SP.clowergamma),
  uppergamma: mpFn2(SP.cuppergamma),
} satisfies typeof mpFns);

// ---- Bessel and Airy functions by power series in arbitrary precision -------------------

/** n/d at wp bits (exact for an integer). */
const cr = (n: number | bigint, d: number | bigint = 1, wp = 200): Mpc => [d === 1 ? F.fromInt(BigInt(n)) : F.fromRational(BigInt(n), BigInt(d), wp), ZERO];
/** True when the term t is below 2**-wp relative to the sum (by exponents, so values beyond the range of doubles compare too). */
const small = (t: Mpc, sum: Mpc, wp: number) => Math.max(F.mag(t[0]), F.mag(t[1])) < Math.max(F.mag(sum[0]), F.mag(sum[1])) - wp - 4;

/** sum_k s**k (z/2)**(2k + nu) / (k! Gamma(k + nu + 1)). */
function mpBesselSeries(nu: Mpc, z: Mpc, sign: 1 | -1, wp: number): Mpc {
  const h = M.cmul(z, cr(1, 2), wp);
  const h2 = M.cmul(h, h, wp);
  let term = M.cdiv(M.cpow(h, nu, wp), SP.cgamma(M.cadd(nu, one, wp), wp), wp);
  let sum = term;
  for (let k = 1; k < 5000; k++) {
    term = M.cdiv(M.cmul(term, h2, wp), M.cmul(cr(sign * k), M.cadd(nu, cr(k), wp), wp), wp);
    sum = M.cadd(sum, term, wp);
    if (small(term, sum, wp)) break;
  }
  return sum;
}

function mpBessel(kind: 'J' | 'Y' | 'I' | 'K', nu: Mpc, z: Mpc, p: number): Mpc {
  const wp = p + 30 + Math.ceil(2 * Math.abs(F.toNumber(M.cabs(z, 53))));
  if (kind === 'J') return mpBesselSeries(nu, z, -1, wp);
  if (kind === 'I') return mpBesselSeries(nu, z, 1, wp);
  const nv = F.toNumber(nu[0]);
  const n = Math.round(nv);
  const isIntOrder = M.isReal(nu) && Math.abs(nv - n) < 1e-30;
  const pi: Mpc = [M.mpPi(wp), ZERO];
  if (!isIntOrder) {
    const s = M.csin(M.cmul(nu, pi, wp), wp);
    const neg = M.cmul(cr(-1), nu, wp);
    if (kind === 'Y') {
      const j = mpBesselSeries(nu, z, -1, wp);
      const jm = mpBesselSeries(neg, z, -1, wp);
      return M.cdiv(M.csub(M.cmul(j, M.ccos(M.cmul(nu, pi, wp), wp), wp), jm, wp), s, p);
    }
    const i = mpBesselSeries(nu, z, 1, wp);
    const im = mpBesselSeries(neg, z, 1, wp);
    return M.cmul(M.cdiv(pi, M.cmul(cr(2), s, wp), wp), M.csub(im, i, wp), p);
  }
  // integer order: limit formulas
  const m = Math.abs(n);
  const h = M.cmul(z, cr(1, 2), wp);
  const lg = M.clog(h, wp);
  const sign: 1 | -1 = kind === 'Y' ? -1 : 1;
  const Jn = mpBesselSeries(cr(m), z, sign, wp);
  const fact = (k: number) => {
    let r = 1n;
    for (let i = 2n; i <= BigInt(k); i++) r *= i;
    return r;
  };
  let s1 = M.C0;
  for (let k = 0; k < m; k++) {
    const c = cr((kind === 'K' && k % 2 ? -1n : 1n) * fact(m - k - 1), fact(k), wp);
    s1 = M.cadd(s1, M.cmul(c, M.cpowInt(h, BigInt(2 * k - m), wp), wp), wp);
  }
  const euler: Mpc = [M.mpEuler(wp), ZERO];
  const psi = (k: number): Mpc => {
    let acc = M.cmul(cr(-1), euler, wp);
    for (let j = 1; j < k; j++) acc = M.cadd(acc, cr(1, j, wp), wp);
    return acc;
  };
  let s2 = M.C0;
  const h2 = M.cmul(h, h, wp);
  let pw = M.cpowInt(h, BigInt(m), wp);
  for (let k = 0; k < 5000; k++) {
    const c = M.cdiv(M.cadd(psi(k + 1), psi(m + k + 1), wp), cr(fact(k) * fact(m + k)), wp);
    const t = M.cmul(M.cmul(c, cr(kind === 'Y' && k % 2 ? -1 : 1), wp), pw, wp);
    s2 = M.cadd(s2, t, wp);
    pw = M.cmul(pw, h2, wp);
    if (k > 2 && small(t, s2, wp)) break;
  }
  if (kind === 'Y') {
    const a = M.cmul(M.cdiv(cr(2), pi, wp), M.cmul(Jn, lg, wp), wp);
    return M.csub(a, M.cdiv(M.cadd(s1, s2, wp), pi, wp), p);
  }
  const sg = m % 2 ? -1 : 1;
  return M.cadd(M.cadd(M.cmul(cr(-sg), M.cmul(lg, Jn, wp), wp), M.cmul(cr(1, 2), s1, wp), wp), M.cmul(cr(sg, 2), s2, wp), p);
}

function mpAiry(kind: 'ai' | 'bi' | 'aip' | 'bip', z: Mpc, p: number): Mpc {
  // the terms grow to about exp(2/3 |z|^(3/2)) while Ai decays like exp(-2/3 z^(3/2))
  const az = F.toNumber(M.cabs(z, 53));
  const wp = p + 30 + Math.ceil(3 * az + 1.93 * az ** 1.5);
  const q = (n: number, d: number): Mpc => [F.fromRational(BigInt(n), BigInt(d), wp), ZERO];
  const g23 = SP.cgamma(q(2, 3), wp);
  const g13 = SP.cgamma(q(1, 3), wp);
  const c1 = M.cdiv(one, M.cmul(M.cpow(cr(3), q(2, 3), wp), g23, wp), wp);
  const c2 = M.cdiv(one, M.cmul(M.cpow(cr(3), q(1, 3), wp), g13, wp), wp);
  const deriv = kind === 'aip' || kind === 'bip';
  const z3 = M.cmul(M.cmul(z, z, wp), z, wp);
  let f = M.C0;
  let g = M.C0;
  let tf: Mpc = one;
  let tg: Mpc = z;
  for (let k = 0; k < 5000; k++) {
    if (deriv) {
      if (k > 0) f = M.cadd(f, M.cmul(cr(3 * k), M.cdiv(tf, z, wp), wp), wp);
      g = M.cadd(g, M.cmul(cr(3 * k + 1), M.cdiv(tg, z, wp), wp), wp);
    } else {
      f = M.cadd(f, tf, wp);
      g = M.cadd(g, tg, wp);
    }
    tf = M.cdiv(M.cmul(tf, z3, wp), cr((3 * k + 2) * (3 * k + 3)), wp);
    tg = M.cdiv(M.cmul(tg, z3, wp), cr((3 * k + 3) * (3 * k + 4)), wp);
    if (k > 2 && small(M.cadd(tf, tg, wp), M.cadd(f, g, wp), wp)) break;
  }
  if (kind === 'ai' || kind === 'aip') return M.csub(M.cmul(c1, f, wp), M.cmul(c2, g, wp), p);
  return M.cmul(M.csqrt(cr(3), wp), M.cadd(M.cmul(c1, f, wp), M.cmul(c2, g, wp), wp), p);
}
