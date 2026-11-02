// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision evaluation of expression trees (SymPy evalf).
 *
 * `evalMp` evaluates at a working precision; `evalAdaptive` repeats the
 * evaluation with more guard bits until the result rounded to the target
 * precision is stable, which certifies the digits in the presence of
 * cancellation.
 */

import { Add, Constant, Expr, ExtensionExpr, Float, Fn, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul } from '../core/ops';
import * as F from './mpf';
import { Mpf, ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc } from './mpfun';
import * as SP from './mpspecial';
import { cLambertW } from './complex';

const toInt = (z: Mpc): number => {
  const [p, q] = F.toRational(z[0]);
  if (!F.isZero(z[1]) || q !== 1n) throw new Error('integer expected');
  return Number(p);
};
const one: Mpc = M.C1;

export type { Mpc };

/** Arbitrary-precision implementations of functions: args and result as Mpc at `prec` bits. */
export const mpFns: Record<string, (args: Mpc[], prec: number) => Mpc> = {
  sin: ([a], p) => M.csin(a!, p),
  cos: ([a], p) => M.ccos(a!, p),
  tan: ([a], p) => M.ctan(a!, p),
  asin: ([a], p) => M.casin(a!, p),
  acos: ([a], p) => M.cacos(a!, p),
  atan: ([a], p) => M.catan(a!, p),
  sinh: ([a], p) => M.csinh(a!, p),
  cosh: ([a], p) => M.ccosh(a!, p),
  tanh: ([a], p) => M.ctanh(a!, p),
  asinh: ([a], p) => M.casinh(a!, p),
  acosh: ([a], p) => M.cacosh(a!, p),
  atanh: ([a], p) => M.catanh(a!, p),
  log: (args, p) => {
    const l = M.clog(args[0]!, p + 10);
    if (args.length === 1) return [F.round(l[0], p), F.round(l[1], p)];
    return M.cdiv(l, M.clog(args[1]!, p + 10), p);
  },
  exp: ([a], p) => M.cexp(a!, p),
  abs: ([a], p) => [M.cabs(a!, p), ZERO],
  re: ([a], p) => [F.round(a![0], p), ZERO],
  im: ([a], p) => [F.round(a![1], p), ZERO],
  arg: ([a], p) => [M.carg(a!, p), ZERO],
  conjugate: ([a], p) => [F.round(a![0], p), F.round(F.neg(a![1]), p)],
  sign: ([a], p) => {
    if (M.isReal(a!)) return [F.fromInt(BigInt(F.sign(a![0]))), ZERO];
    return M.cdiv(a!, [M.cabs(a!, p + 10), ZERO], p);
  },
  atan2: ([y, x], p) => [M.atan2(y![0], x![0], p), ZERO],
  gamma: ([a], p) => SP.cgamma(a!, p),
  loggamma: ([a], p) => SP.cloggamma(a!, p),
  factorial: ([a], p) => SP.cgamma(M.cadd(a!, one, p + 20), p),
  polygamma: ([n, z], p) => SP.cpolygamma(toInt(n!), z!, p),
  harmonic: (args, p) => {
    if (args.length !== 1) throw new Error('harmonic(n, m)');
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
    if (args.length !== 1) throw new Error('Hurwitz zeta');
    return SP.czeta(args[0]!, p);
  },
  erf: ([a], p) => SP.cerf(a!, p),
  erfc: ([a], p) => SP.cerfc(a!, p),
  erfi: ([a], p) => SP.cerfi(a!, p),
  erf2: ([x, y], p) => M.csub(SP.cerf(y!, p + 20), SP.cerf(x!, p + 20), p),
  erfinv: ([a], p) => {
    if (!M.isReal(a!)) throw new Error('complex erfinv');
    return [SP.erfinv(a![0], p), ZERO];
  },
  erfcinv: ([a], p) => {
    if (!M.isReal(a!)) throw new Error('complex erfcinv');
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
};

/** Fallback double-precision implementations (registered by evalf.ts / special.ts). */
let doubleFallback: (name: string, args: Mpc[]) => Mpc | undefined = () => undefined;
export function setDoubleFallback(f: typeof doubleFallback): void {
  doubleFallback = f;
}

function constant(name: string, prec: number): Mpc {
  switch (name) {
    case 'pi':
      return [M.mpPi(prec), ZERO];
    case 'E':
      return [M.mpE(prec), ZERO];
    case 'I':
      return M.CI;
    case 'EulerGamma':
      return [M.mpEuler(prec), ZERO];
    case 'Catalan':
      return [M.mpCatalan(prec), ZERO];
    case 'GoldenRatio':
      return [M.mpPhi(prec), ZERO];
    case 'TribonacciConstant':
      return [M.mpTribonacci(prec), ZERO];
  }
  throw new Error(`unknown constant ${name}`);
}

/** Evaluate at working precision wp (each operation rounded to wp bits). */
export function evalMp(e: Expr, wp: number, lookup: (s: Sym) => Mpc | undefined): Mpc {
  const ev = (x: Expr): Mpc => {
    if (x instanceof Rational) return [x.q === 1n ? F.fromInt(x.p) : F.fromRational(x.p, x.q, wp), ZERO];
    if (x instanceof Float) return [x.mpf, ZERO];
    if (x instanceof Constant) return constant(x.name, wp);
    if (x instanceof Sym) {
      const v = lookup(x);
      if (v === undefined) throw new Error(`no value for ${x.name}`);
      return v;
    }
    if (x instanceof Add) {
      let acc: Mpc = M.C0;
      for (const a of x.args) acc = M.cadd(acc, ev(a), wp);
      return acc;
    }
    if (x instanceof Mul) {
      let acc: Mpc = M.C1;
      for (const a of x.args) acc = M.cmul(acc, ev(a), wp);
      return acc;
    }
    if (x instanceof Pow) {
      if (x.base instanceof Constant && x.base.name === 'E') return M.cexp(ev(x.exp), wp);
      const b = ev(x.base);
      if (x.exp instanceof Rational) {
        if (x.exp.q === 1n) return M.cpowInt(b, x.exp.p, wp);
        if (x.exp.q === 2n) return M.cpowInt(M.csqrt(b, wp + 10), x.exp.p, wp);
        if (M.isReal(b) && b[0].man > 0n && x.exp.p === 1n) return [M.nthRoot(b[0], x.exp.q, wp), ZERO];
      }
      return M.cpow(b, ev(x.exp), wp);
    }
    if (x instanceof Fn) {
      const args = x.args.map(ev);
      const f = mpFns[x.name];
      if (f) return f(args, wp);
      const d = doubleFallback(x.name, args);
      if (d) return d;
      throw new Error(`cannot evaluate ${x.name}`);
    }
    if (x instanceof ExtensionExpr) {
      const v = x.numericValue(Math.ceil(wp / 3.32) + 5);
      if (v !== undefined) return ev(v);
    }
    throw new Error(`cannot evaluate ${x.kind}`);
  };
  return ev(e);
}

function sameAt(a: Mpf, b: Mpf, prec: number): boolean {
  const ra = F.round(a, prec);
  const rb = F.round(b, prec);
  return ra.man === rb.man && ra.exp === rb.exp;
}

/** True when part x is negligible next to `ref` at working precision wp. */
function negligible(x: Mpf, ref: number, wp: number): boolean {
  return F.isZero(x) || F.mag(x) < ref - wp + 8;
}

/**
 * Evaluate to `prec` correct bits, raising the working precision until two
 * successive evaluations agree. Parts that vanish relative to the other
 * part (cancellation to zero) are returned as exact zeros.
 */
export function evalAdaptive(e: Expr, prec: number, lookup: (s: Sym) => Mpc | undefined): Mpc {
  let wp = prec + 20;
  let prev = evalMp(e, wp, lookup);
  for (let i = 0; i < 8; i++) {
    const wp2 = prec + 20 + 40 * 2 ** (i + 1);
    const cur = evalMp(e, wp2, lookup);
    const ref = Math.max(F.mag(cur[0]), F.mag(cur[1]));
    let ok = true;
    const out: Mpf[] = [];
    for (const k of [0, 1] as const) {
      const negPrev = negligible(prev[k], Math.max(F.mag(prev[0]), F.mag(prev[1])), wp);
      const negCur = negligible(cur[k], ref, wp2);
      if (negPrev && negCur) out.push(ZERO);
      else if (!negPrev && !negCur && sameAt(prev[k], cur[k], prec)) out.push(F.round(cur[k], prec));
      else ok = false;
    }
    if (ok) return [out[0]!, out[1]!];
    prev = cur;
    wp = wp2;
  }
  return [F.round(prev[0], prec), F.round(prev[1], prec)];
}

/** Build a Float / complex Float expression from an Mpc. */
export function fromMpc(v: Mpc, prec: number, chop?: boolean | number): Expr {
  let [re, im] = v;
  if (chop !== undefined && chop !== false) {
    // SymPy chop_parts: drop parts below 2**(-chopPrec + 4)
    const chopPrec = chop === true ? prec : Math.round(-3.321 * Math.log10(chop) + 2.5);
    if (!F.isZero(re) && F.mag(re) < -chopPrec + 4) re = ZERO;
    if (!F.isZero(im) && F.mag(im) < -chopPrec + 4) im = ZERO;
  }
  if (F.isZero(im)) return F.isZero(re) ? S.Zero : new Float(re, prec);
  const imPart = mul(new Float(im, prec), S.I);
  if (F.isZero(re)) return imPart;
  return add(new Float(re, prec), imPart);
}


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
  return cLambertW({ re: F.toNumber(z[0]), im: F.toNumber(z[1]) } as never, k);
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
