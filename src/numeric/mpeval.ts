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

import { Add, Constant, Expr, Float, Fn, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul } from '../core/ops';
import * as F from './mpf';
import { Mpf, ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc } from './mpfun';
import * as SP from './mpspecial';

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
