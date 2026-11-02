// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Arbitrary-precision values of the special functions (Gamma, zeta, error
 * functions, exponential integrals, Lambert W, Bessel and Airy functions),
 * registered into the evaluator table of numeric/mpeval. Imported by the
 * modules defining these functions so that the core does not carry them.
 */

import { NotImplementedError } from '../core/errors';
import * as F from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc } from './mpfun';
import * as SP from './mpspecial';
import { cLambertW } from './complex';
import { mpFns } from './mpeval';

const toInt = (z: Mpc): number => {
  const [p, q] = F.toRational(z[0]);
  if (!F.isZero(z[1]) || q !== 1n) throw new TypeError('integer expected');
  return Number(p);
};
const one: Mpc = M.C1;

Object.assign(mpFns, {
  gamma: ([a], p) => SP.cgamma(a!, p),
  loggamma: ([a], p) => SP.cloggamma(a!, p),
  factorial: ([a], p) => SP.cgamma(M.cadd(a!, one, p + 20), p),
  polygamma: ([n, z], p) => SP.cpolygamma(toInt(n!), z!, p),
  harmonic: (args, p) => {
    if (args.length !== 1) throw new NotImplementedError('harmonic(n, m)');
    const wp = p + 20;
    return M.cadd(SP.cpolygamma(0, M.cadd(args[0]!, one, wp), wp), [M.mpEuler(wp), ZERO], p);
  },
  catalan: ([z], p) => {
    // 4^z Gamma(z + 1/2) / (sqrt(pi) Gamma(z + 2))
    const wp = p + 30;
    const half: Mpc = [{ man: 1n, exp: -1 }, ZERO];
    const num = M.cmul(M.cpow([F.fromInt(4n), ZERO], z!, wp), SP.cgamma(M.cadd(z!, half, wp), wp), wp);
    const den = M.cmul([F.sqrt(M.mpPi(wp), wp), ZERO], SP.cgamma(M.cadd(z!, [F.fromInt(2n), ZERO], wp), wp), wp);
    return M.cdiv(num, den, p);
  },
  beta: ([a, b], p) => {
    const wp = p + 30;
    return M.cdiv(M.cmul(SP.cgamma(a!, wp), SP.cgamma(b!, wp), wp), SP.cgamma(M.cadd(a!, b!, wp), wp), p);
  },
  zeta: (args, p) => {
    if (args.length !== 1) throw new NotImplementedError('Hurwitz zeta');
    return SP.czeta(args[0]!, p);
  },
  erf: ([a], p) => SP.cerf(a!, p),
  erfc: ([a], p) => SP.cerfc(a!, p),
  erfi: ([a], p) => SP.cerfi(a!, p),
  erf2: ([x, y], p) => M.csub(SP.cerf(y!, p + 20), SP.cerf(x!, p + 20), p),
  erfinv: ([a], p) => {
    if (!M.isReal(a!)) throw new NotImplementedError('complex erfinv');
    return [SP.erfinv(a![0], p), ZERO];
  },
  erfcinv: ([a], p) => {
    if (!M.isReal(a!)) throw new NotImplementedError('complex erfcinv');
    return [SP.erfinv(F.sub(F.ONE, a![0], p + 20), p), ZERO];
  },
  fresnels: ([a], p) => SP.cfresnel('S', a!, p),
  fresnelc: ([a], p) => SP.cfresnel('C', a!, p),
  Ei: ([a], p) => SP.cei(a!, p),
  LambertW: ([a, k], p) => mpLambertW(a!, k ? toInt(k) : 0, p),
  besselj: ([nu, z], p) => mpBessel('J', nu!, z!, p),
  bessely: ([nu, z], p) => mpBessel('Y', nu!, z!, p),
  besseli: ([nu, z], p) => mpBessel('I', nu!, z!, p),
  besselk: ([nu, z], p) => mpBessel('K', nu!, z!, p),
  airyai: ([z], p) => mpAiry('ai', z!, p),
  airybi: ([z], p) => mpAiry('bi', z!, p),
  airyaiprime: ([z], p) => mpAiry('aip', z!, p),
  airybiprime: ([z], p) => mpAiry('bip', z!, p),
  li: ([a], p) => SP.cli(a!, p),
  Li: ([a], p) => M.csub(SP.cli(a!, p + 20), SP.cli([F.fromInt(2n), ZERO], p + 20), p),
  Si: ([a], p) => SP.csi(a!, p, false),
  Shi: ([a], p) => SP.csi(a!, p, true),
  Ci: ([a], p) => SP.cci(a!, p, false),
  Chi: ([a], p) => SP.cci(a!, p, true),
  lowergamma: ([s, z], p) => SP.clowergamma(s!, z!, p),
  uppergamma: ([s, z], p) => SP.cuppergamma(s!, z!, p),
} satisfies typeof mpFns);

/** Lambert W by Halley iteration from a double-precision start (branch k). */
function mpLambertW(z: Mpc, k: number, p: number): Mpc {
  const wp = p + 30;
  const start = numericFnsForStart(z, k);
  let w: Mpc = [F.fromNumber(start.re), F.fromNumber(start.im)];
  const two: Mpc = [F.fromInt(2n), ZERO];
  for (let i = 0; i < 200; i++) {
    const ew = M.cexp(w, wp);
    const f = M.csub(M.cmul(w, ew, wp), z, wp);
    const wp1 = M.cadd(w, one, wp);
    const denom = M.csub(M.cmul(ew, wp1, wp), M.cdiv(M.cmul(M.cadd(w, two, wp), f, wp), M.cmul(two, wp1, wp), wp), wp);
    const dw = M.cdiv(f, denom, wp);
    w = M.csub(w, dw, wp);
    const small = F.mag(M.cabs(dw, wp));
    const size = Math.max(0, F.mag(M.cabs(w, wp)));
    if (F.toNumber(M.cabs(dw, wp)) === 0 || small < size - wp + 4) break;
  }
  return [F.round(w[0], p), F.round(w[1], p)];
}

function numericFnsForStart(z: Mpc, k: number): { re: number; im: number } {
  return cLambertW({ re: F.toNumber(z[0]), im: F.toNumber(z[1]) }, k);
}


// ---- Bessel and Airy functions by power series in arbitrary precision -------------------

const cr = (n: number | bigint, d: number | bigint = 1): Mpc => [F.fromRational(BigInt(n), BigInt(d), 200), ZERO];
const small = (t: Mpc, sum: Mpc, wp: number) => {
  const a = F.toNumber(M.cabs(t, 53));
  const b = F.toNumber(M.cabs(sum, 53));
  return a === 0 || (b > 0 && Math.log2(a / b) < -wp - 4);
};

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
    const c = cr((kind === 'K' && k % 2 ? -1n : 1n) * fact(m - k - 1), fact(k));
    s1 = M.cadd(s1, M.cmul(c, M.cpowInt(h, BigInt(2 * k - m), wp), wp), wp);
  }
  const euler: Mpc = [M.mpEuler(wp), ZERO];
  const psi = (k: number): Mpc => {
    let acc = M.cmul(cr(-1), euler, wp);
    for (let j = 1; j < k; j++) acc = M.cadd(acc, cr(1, j), wp);
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
  const wp = p + 30 + Math.ceil(3 * Math.abs(F.toNumber(M.cabs(z, 53))));
  const g23 = SP.cgamma(cr(2, 3), wp);
  const g13 = SP.cgamma(cr(1, 3), wp);
  const c1 = M.cdiv(one, M.cmul(M.cpow(cr(3), cr(2, 3), wp), g23, wp), wp);
  const c2 = M.cdiv(one, M.cmul(M.cpow(cr(3), cr(1, 3), wp), g13, wp), wp);
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
    tf = M.cmul(tf, M.cmul(z3, cr(3 * k + 1, (3 * k + 1) * (3 * k + 2) * (3 * k + 3)), wp), wp);
    tg = M.cmul(tg, M.cmul(z3, cr(3 * k + 2, (3 * k + 2) * (3 * k + 3) * (3 * k + 4)), wp), wp);
    if (k > 2 && small(M.cadd(tf, tg, wp), M.cadd(f, g, wp), wp)) break;
  }
  if (kind === 'ai' || kind === 'aip') return M.csub(M.cmul(c1, f, wp), M.cmul(c2, g, wp), p);
  return M.cmul(M.csqrt(cr(3), wp), M.cadd(M.cmul(c1, f, wp), M.cmul(c2, g, wp), wp), p);
}
