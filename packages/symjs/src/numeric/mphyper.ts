// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/hypergeometric.py: hypercomb, hyper, _hyp0f1, _hyp1f1,
// _hyp1f2, _hyp2f2, _hyp2f3, _hyp2f0, _hypq1fq, _hyp_borel; ctx_mp.py: hypsum; libmp/libhyper.py:
// make_hyp_summator; calculus/extrapolation.py: nsum, adaptive_extrapolation, richardson, shanks;
// gammaprod), Copyright (c) 2005-2023 Fredrik Johansson and mpmath contributors, BSD
// 3-Clause License (see LICENSE).

/**
 * @file The generalized hypergeometric function pFq at arbitrary precision (mpmath hyper): the
 * series summed in fixed point (hypsum), the asymptotic expansions of 0F1, 1F1, 1F2, 2F2, 2F3 and
 * 2F0 at large arguments and the 1/z transformation of q+1Fq, combined by hypercomb, which
 * perturbs the parameters at the poles of the gamma factors; q+1Fq near the unit circle with
 * convergence acceleration (nsum: Richardson and Shanks), divergent series by their Borel
 * integral (quad), with Euler-Maclaurin summation as the final convergent-series fallback.
 */

import { at, defined } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';
import * as M from './mpfun';
import { C0, C1, CI, type Mpc, cadd, cdiv, cexp, cmul, cneg, csub } from './mpfun';
import { bernoulli, cgamma, cloggamma, cpolygamma } from './mpspecial';
import { chyp2f1 } from './mporthopoly';
import { quad } from './mpquad';

/** mpmath NoConvergence: a series that converges too slowly (or an asymptotic one that diverges). */
export class NoConvergence extends RangeError {
  constructor(message = 'Hypergeometric series converges too slowly. Try increasing maxterms.') {
    super(message);
    this.name = 'NoConvergence';
  }
}

/** mpmath's ZeroDivisionError of a series with a pole (a nonpositive integer lower parameter). */
export class HyperPoleError extends RangeError {
  constructor() {
    super('pole in hypergeometric series');
    this.name = 'HyperPoleError';
  }
}

/** mpmath's infinite value of q+1Fq at z = 1 where the series diverges; sign is the sign of the series below 1. */
export class HyperInfinity extends RangeError {
  constructor(readonly value: Mpc) {
    super('hypergeometric series diverges at 1');
    this.name = 'HyperInfinity';
  }
}

/** Options of mpmath's hypergeometric functions. */
export interface HyperOptions {
  forceSeries?: boolean;
  maxterms?: number;
  maxprec?: number;
  /** Bound convergence-acceleration work before trying another method. @internal */
  maxNsumTerms?: number;
}

const real = (x: Mpf): Mpc => [x, ZERO];
const int = (n: bigint | number): Mpc => [F.fromInt(BigInt(n)), ZERO];
const HALF: Mpf = { man: 1n, exp: -1n };
const half: Mpc = [HALF, ZERO];
const isZeroC = (z: Mpc): boolean => F.isZero(z[0]) && F.isZero(z[1]);
const isRealC = (z: Mpc): boolean => F.isZero(z[1]);
/** mpmath mag of a complex number (one more than the larger part when both are nonzero). */
const cmag = (z: Mpc): number => (F.isZero(z[0]) || F.isZero(z[1]) ? Math.max(F.mag(z[0]), F.mag(z[1])) : 1 + Math.max(F.mag(z[0]), F.mag(z[1])));
/** log2 |z| (-Infinity at 0), without overflow. */
function log2abs(z: Mpc): number {
  const m = Math.max(F.mag(z[0]), F.mag(z[1]));
  if (m === -Infinity) return -Infinity;
  return m + Math.log2(Math.hypot(F.toNumber(F.ldexp(z[0], -m)), F.toNumber(F.ldexp(z[1], -m))));
}
/** mpmath mag(abs(z)). */
const magAbs = (z: Mpc): number => F.mag(M.cabs(z, 53));
const absD = (z: Mpc): number => Math.hypot(F.toNumber(z[0]), F.toNumber(z[1]));
const rnd = (z: Mpc, p: number): Mpc => [F.round(z[0], p), F.round(z[1], p)];
const sameC = (a: Mpc, b: Mpc): boolean => F.cmp(a[0], b[0]) === 0 && F.cmp(a[1], b[1]) === 0;
/** An integer (mpmath's 'Z' parameter type). */
const isInt = (z: Mpc): boolean => isRealC(z) && F.toRational(z[0])[1] === 1n;
const isNpInt = (z: Mpc): boolean => isInt(z) && F.sign(z[0]) <= 0;
const defaultMaxprec = (p: number): number => Math.floor(1000 * p ** 0.25 + 4 * p);
const sumC = (xs: readonly Mpc[], wp: number): Mpc => xs.reduce((s, x) => cadd(s, x, wp), C0);

/**
 * mpmath nint_distance: the nearest integer n to the real part and the binary logarithm d of the
 * distance to it (and of the imaginary part); -Infinity for an integer.
 */
export function nintDistance(z: Mpc): [n: bigint, d: number] {
  const im = F.isZero(z[1]) ? -Infinity : F.mag(z[1]);
  const re = z[0];
  // |re| < 1/2 (and re = 0)
  if (F.mag(re) < 0) return [0n, Math.max(F.mag(re), im)];
  // (exact: the bits of re below the binary point)
  const wp = F.mag(re) + Math.max(0, -Number(re.exp)) + 10;
  const n = F.floor(F.add(re, HALF, wp));
  const r = F.sub(re, F.fromInt(n), wp);
  return [n, Math.max(F.mag(r), im)];
}

// ---------------------------------------------------------------------------
// hypsum: the series in fixed point
// ---------------------------------------------------------------------------

const toFixed = (x: Mpf, wp: number): bigint => {
  const off = x.exp + BigInt(wp);
  return off >= 0n ? x.man << off : x.man >> -off;
};
const babs = (x: bigint): bigint => (x < 0n ? -x : x);

/** A parameter of the summator: an exact integer, or a fixed-point real or complex number. */
interface Param {
  int?: bigint;
  re: bigint;
  im: bigint;
}

/**
 * The sum of the series with absolute error about 2**-wp (mpmath's generated hypsum_p_q
 * summators, with integer parameters exact): [value, magnitude of the value]; magnitudes of the
 * terms at the indices of magCheck are recorded there.
 */
function summator(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, wp: number, epsshift: number, magCheck: Map<number, number | undefined>, maxterms: number): [Mpc, number] {
  const W = BigInt(wp);
  const one = 1n << W;
  const high = 1n << BigInt(epsshift);
  const param = (c: Mpc): Param => (isInt(c) ? { int: F.toRational(c[0])[0], re: 0n, im: 0n } : { re: toFixed(c[0], wp), im: toFixed(c[1], wp) });
  const A = as.map(param);
  const B = bs.map(param);
  const Aint = A.filter((c) => c.int !== undefined);
  const Bint = B.filter((c) => c.int !== undefined);
  const Areal = A.filter((c) => c.int === undefined && c.im === 0n);
  const Breal = B.filter((c) => c.int === undefined && c.im === 0n);
  const Acomplex = A.filter((c) => c.int === undefined && c.im !== 0n);
  const Bcomplex = B.filter((c) => c.int === undefined && c.im !== 0n);
  const zr = toFixed(z[0], wp);
  const zi = toFixed(z[1], wp);
  const complex = zi !== 0n || Acomplex.length > 0 || Bcomplex.length > 0;
  let sre = one;
  let sim = 0n;
  let pre = one;
  let pim = 0n;
  for (let n = 1; ; n++) {
    if (magCheck.has(n)) magCheck.set(n, wp - Math.max(F.bitLength(babs(pre)), F.bitLength(babs(pim))));
    let mul = 1n;
    for (const c of Aint) mul *= defined(c.int);
    let div = BigInt(n);
    for (const c of Bint) div *= defined(c.int);
    // a zero integer lower parameter: hypsum has checked that an integer upper parameter reaches
    // zero no later, which ends the series (mul = 0 or an earlier zero term)
    if (div === 0n) break;
    for (const c of Areal) {
      pre = (pre * c.re) >> W;
      pim = (pim * c.re) >> W;
    }
    // (a real lower parameter is not an integer, and hypsum's working precision resolves its
    // distance to the nearest one, so c.re is not 0)
    for (const c of Breal) {
      pre = (pre << W) / c.re;
      pim = (pim << W) / c.re;
    }
    if (complex) {
      const r = (mul * (pre * zr - pim * zi)) / div;
      pim = ((mul * (pim * zr + pre * zi)) / div) >> W;
      pre = r >> W;
      for (const c of Acomplex) {
        const r2 = (pre * c.re - pim * c.im) >> W;
        pim = (pim * c.re + pre * c.im) >> W;
        pre = r2;
      }
      for (const c of Bcomplex) {
        const m = c.re * c.re + c.im * c.im;
        const r2 = ((pre * c.re + pim * c.im) << W) / m;
        pim = ((pim * c.re - pre * c.im) << W) / m;
        pre = r2;
      }
    } else {
      pre = ((pre * mul * zr) >> W) / div;
    }
    sre += pre;
    sim += pim;
    if (babs(pre) < high && babs(pim) < high) break;
    if (n > maxterms) throw new NoConvergence();
    for (const c of Aint) c.int = defined(c.int) + 1n;
    for (const c of Bint) c.int = defined(c.int) + 1n;
    for (const c of [...Areal, ...Breal, ...Acomplex, ...Bcomplex]) c.re += one;
  }
  const v: Mpc = [F.normalize(sre, -wp, prec), F.normalize(sim, -wp, prec)];
  return [v, isZeroC(v) ? -wp + 1 : cmag(v)];
}

/** mpmath hypsum: the series of pFq at z to prec bits, with the working precision raised until the cancellation is covered. */
export function hypsum(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions = {}): Mpc {
  const maxprec = opts.maxprec ?? defaultMaxprec(prec);
  let extraprec = 50;
  let epsshift = 25;
  // jumps in magnitude occur when lower parameters are close to nonpositive integers
  const magnitudeCheck = new Map<number, number>();
  let maxTotalJump = 0;
  for (const [i, c] of [...as, ...bs].entries()) {
    const lower = i >= as.length;
    if (isInt(c)) {
      if (lower && F.sign(c[0]) <= 0 && !as.some((a) => isNpInt(a) && F.cmp(c[0], a[0]) <= 0)) throw new HyperPoleError();
      continue;
    }
    const [n0, d0] = nintDistance(c);
    const n = -Number(n0);
    const d = -d0;
    if (lower && n >= 0 && d > 4) {
      magnitudeCheck.set(n, (magnitudeCheck.get(n) ?? 0) + d);
      extraprec = Math.max(extraprec, d - prec + 60);
    }
    maxTotalJump += Math.abs(d);
  }
  for (;;) {
    if (extraprec > maxprec) throw new RangeError(`hypsum() failed to converge to the requested ${prec} bits of accuracy using a working precision of ${prec + extraprec} bits`);
    const wp = prec + extraprec;
    const magDict = new Map<number, number | undefined>([...magnitudeCheck.keys()].map((k) => [k, undefined]));
    const [v, magnitude] = summator(as, bs, z, prec, wp, epsshift, magDict, opts.maxterms ?? wp * 100);
    const cancel = -magnitude;
    const jumpsResolved = extraprec >= maxTotalJump || [...magDict.values()].every((m) => m !== undefined && m >= prec);
    if (jumpsResolved && cancel < extraprec - 30) return v;
    extraprec = extraprec * 2 + 5;
    epsshift += 5;
  }
}

// ---------------------------------------------------------------------------
// hypercomb
// ---------------------------------------------------------------------------

/** One term of hypercomb: prod(w**c) prod(gamma(alpha))/prod(gamma(beta)) pFq(a; b; z). */
export type HyperTerm = readonly [w: readonly Mpc[], c: readonly Mpc[], alpha: readonly Mpc[], beta: readonly Mpc[], a: readonly Mpc[], b: readonly Mpc[], z: Mpc];

/** Gamma(z), mpmath's error at a pole (a HyperPoleError). */
function cgammaChecked(z: Mpc, wp: number): Mpc {
  if (isNpInt(z)) throw new HyperPoleError();
  return cgamma(z, wp);
}
const crgamma = (z: Mpc, wp: number): Mpc => (isNpInt(z) ? C0 : cdiv(C1, cgamma(z, wp + 10), wp));
/** mpmath power(w, c): 0 for w = 0 and re(c) > 0. */
const cpower = (w: Mpc, c: Mpc, wp: number): Mpc => (isZeroC(w) && F.sign(c[0]) > 0 ? C0 : M.cpow(w, c, wp));

/** mpmath _check_need_perturb. */
function checkNeedPerturb(terms: readonly HyperTerm[]): { perturb: boolean; recompute: boolean; extraprec: number; discard: number[] } {
  let perturb = false;
  let recompute = false;
  let extraprec = 0;
  const discard: number[] = [];
  for (const [termIndex, [ws, cs, alphas, betas, as, bs]] of terms.entries()) {
    let singularWeight = false;
    // division by zero in the leading factors
    for (const [k, w] of ws.entries()) {
      const c = at(cs, k);
      if (isZeroC(w) && F.sign(c[0]) <= 0 && !isZeroC(c)) {
        perturb = recompute = true;
        singularWeight = true;
      }
    }
    const poleCount = [0, 0, 0];
    for (const [dataIndex, data] of [alphas, betas, bs].entries()) {
      for (const x of data) {
        const [n, d] = nintDistance(x);
        if (n > 0n) continue;
        if (d === -Infinity) {
          // a pole of the series is no pole when the series terminates before
          if (dataIndex === 2 && as.some((u) => isNpInt(u) && F.cmp(u[0], F.fromInt(n)) >= 0)) continue;
          poleCount[dataIndex] = at(poleCount, dataIndex) + 1;
        } else if (d < -4) {
          extraprec += -d;
          recompute = true;
        }
      }
    }
    const [p0, p1, p2] = [at(poleCount, 0), at(poleCount, 1), at(poleCount, 2)];
    if (p1 > p0 + p2 && !singularWeight) discard.push(termIndex);
    else if (p0 + p1 + p2) perturb = recompute = true;
  }
  return { perturb, recompute, extraprec, discard };
}

/**
 * mpmath hypercomb: the sum of the terms fn(params, wp), with the parameters perturbed by a
 * small h at poles of the gamma factors (the limit is reached when two perturbations agree)
 * and the working precision raised for cancellation between the terms.
 */
export function hypercomb(fn: (params: Mpc[], wp: number) => HyperTerm[], params: readonly Mpc[], prec: number, opts: HyperOptions = {}): Mpc {
  const maxprec = opts.maxprec ?? defaultMaxprec(prec);
  const inner: HyperOptions = { ...opts, maxprec };
  let cur = prec;
  let sumvalue: Mpc = C0;
  let reference: Mpc | undefined;
  let hextra = 0;
  for (;;) {
    cur += 10;
    if (cur > maxprec) throw new RangeError(`hypercomb() failed to converge to the requested ${prec} bits of accuracy using a working precision of ${cur} bits`);
    const orig2 = cur;
    const ps = [...params];
    let terms = fn(ps, cur);
    const { perturb, recompute, extraprec, discard } = checkNeedPerturb(terms);
    cur += extraprec;
    if (perturb) {
      const hmag = prec + 10 + hextra;
      let h = F.ldexp(ONE, -hmag);
      cur = orig2 + 10 + hmag + 10;
      for (let k = 0; k < ps.length; k++) {
        ps[k] = cadd(at(ps, k), real(h), cur);
        // independent perturbations, so that two of them do not cancel in a subtraction
        h = F.add(h, F.div(h, F.fromInt(BigInt(k + 1)), cur), cur);
      }
    }
    if (recompute) terms = fn(ps, cur);
    // (mpmath's discard_known_zeros)
    terms = terms.filter((_, i) => !discard.includes(i));
    if (!terms.length) return C0;
    const wp = cur;
    const evaluated = terms.map(([ws, cs, alphas, betas, as, bs, z]) => {
      let v = hyper(as, bs, z, wp, inner);
      for (const a of alphas) v = cmul(v, cgammaChecked(a, wp), wp);
      for (const b of betas) v = cmul(v, crgamma(b, wp), wp);
      for (const [k, w] of ws.entries()) v = cmul(v, cpower(w, at(cs, k), wp), wp);
      return v;
    });
    if (evaluated.length === 1 && !perturb) {
      sumvalue = at(evaluated, 0);
      break;
    }
    sumvalue = sumC(evaluated, wp);
    const maxMagnitude = Math.max(...evaluated.map(cmag));
    const cancellation = maxMagnitude - cmag(sumvalue);
    const precisionOk = cancellation < cur - prec;
    if ((precisionOk && !perturb) || Number.isNaN(cancellation)) break;
    if (precisionOk) {
      if (reference === undefined) {
        hextra += 20;
        reference = sumvalue;
        continue;
      }
      if (cmag(csub(sumvalue, reference, wp)) <= cmag(sumvalue) - prec) break;
      hextra *= 2;
      reference = sumvalue;
    } else {
      cur += Math.min(Math.max(cancellation, prec >> 1), Math.max(extraprec, prec));
    }
  }
  return rnd(sumvalue, prec);
}

// ---------------------------------------------------------------------------
// hyper and the special cases
// ---------------------------------------------------------------------------

/** exp(i pi x) (mpmath expjpi). */
const expjpi = (x: Mpc, wp: number): Mpc => cexp(cmul([ZERO, M.mpPi(wp)], x, wp), wp);
/** sin(pi x) (mpmath sinpi). */
const sinpi = (x: Mpc, wp: number): Mpc => M.csin(cmul(real(M.mpPi(wp)), x, wp + 10), wp);
const allReal = (xs: readonly Mpc[]): boolean => xs.every(isRealC);
const reIf = (v: Mpc, cond: boolean): Mpc => (cond ? [v[0], ZERO] : v);
/** Try an asymptotic expansion; NoConvergence falls back to undefined. */
function attempt(f: () => Mpc): Mpc | undefined {
  try {
    return f();
  } catch (err) {
    if (err instanceof NoConvergence) return undefined;
    throw err;
  }
}

/**
 * mpmath hyper: pFq(as; bs; z) to prec bits. Parameters common to as and bs cancel (unless they
 * are nonpositive integers), and the special cases use their own methods.
 */
export function hyper(asIn: readonly Mpc[], bsIn: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions = {}): Mpc {
  const as = [...asIn];
  const bs = [...bsIn];
  for (let i = 0; i < bs.length && as.length; ) {
    const b = at(bs, i);
    const j = as.findIndex((a) => sameC(a, b));
    if (j >= 0 && !isNpInt(b)) {
      as.splice(j, 1);
      bs.splice(i, 1);
    } else i++;
  }
  const p = as.length;
  const q = bs.length;
  if (p === 0 && q === 0) return cexp(z, prec);
  if (p === 0 && q === 1) return hyp0f1(at(bs, 0), z, prec, opts);
  if (p === 1 && q === 0) {
    // (1 - z)**(-a), mpmath's inf at z = 1 for re(a) > 0
    if (sameC(z, C1) && F.sign(at(as, 0)[0]) > 0) throw new HyperInfinity(C1);
    return M.cpow(csub(C1, z, prec + 10), cneg(at(as, 0)), prec);
  }
  if (p === 1 && q === 1) return hyp1f1(at(as, 0), at(bs, 0), z, prec, opts);
  if (p === 1 && q === 2) return hyp1f2(as, bs, z, prec, opts);
  if (p === 2 && q === 1) return hyp2f1(at(as, 0), at(as, 1), at(bs, 0), z, prec, opts);
  if (p === 2 && q === 2) return hyp2f2(as, bs, z, prec, opts);
  if (p === 2 && q === 3) return hyp2f3(as, bs, z, prec, opts);
  if (p === 2 && q === 0) return hyp2f0(at(as, 0), at(as, 1), z, prec, opts);
  if (p === q + 1) return hypq1fq(as, bs, z, prec, opts);
  if (p > q + 1 && !opts.forceSeries) return hypBorel(as, bs, z, prec, opts);
  return hypsum(as, bs, z, prec, opts);
}

/**
 * mpmath _hyp2f1 at its special points, else chyp2f1: at z = 1 Gauss's value where the series
 * converges or terminates, inf times the value at 1 - 2 eps where it diverges; a nonpositive
 * integer c is a pole (inf) unless the series terminates first, when it is summed; 1 at z = 0
 * (indeterminate for c = 0).
 */
function hyp2f1(a: Mpc, b: Mpc, c: Mpc, z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const first = (t: Mpc): boolean => isNpInt(t) && F.cmp(c[0], t[0]) <= 0;
  const zerodiv = isNpInt(c) && !first(a) && !first(b);
  if (sameC(z, C1)) {
    const convergent = F.sign(csub(csub(c, a, prec), b, prec)[0]) > 0;
    if (zerodiv) throw new HyperInfinity(C1);
    if (!convergent && !isNpInt(a) && !isNpInt(b)) throw new HyperInfinity(hyp2f1(a, b, c, real(F.sub(ONE, F.ldexp(ONE, 2 - prec), prec)), prec, opts));
  }
  if (isZeroC(z)) {
    // (mpmath's nan for 0/0 in the first term)
    if (isZeroC(c) && !isZeroC(a) && !isZeroC(b)) throw new RangeError('hyp2f1(a, b, 0, 0) is indeterminate');
    return C1;
  }
  if (isNpInt(c)) {
    if (zerodiv) throw new HyperInfinity(C1);
    return hypsum([a, b], [c], z, prec, opts);
  }
  return chyp2f1(a, b, c, z, prec);
}

/** mpmath _hyp0f1: the asymptotic expansion in two 2F0 series for |z| >= 2**8. */
function hyp0f1(b: Mpc, z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const magz = isZeroC(z) ? 0 : cmag(z);
  if (magz >= 8 && !opts.forceSeries) {
    const v = attempt(() => {
      const wp = prec + 12 + Math.floor(magz / 2);
      const h = (_: Mpc[], p: number): HyperTerm[] => {
        const w = M.csqrt(cneg(z), p);
        const jw = cmul(CI, w, p);
        const u = cdiv(C1, cmul(int(4), jw, p), p);
        const c = csub(half, b, p);
        const E = cexp(cmul(int(2), jw, p), p);
        const ab = [csub(b, half, p), csub([F.fromRational(3n, 2n, p), ZERO], b, p)];
        return [
          [[cneg(jw), E], [c, int(-1)], [], [], ab, [], cneg(u)],
          [[jw, E], [c, C1], [], [], ab, [], u],
        ];
      };
      let r = hypercomb(h, [], wp, { forceSeries: true });
      r = cmul(cdiv(cgammaChecked(b, wp), real(F.mul(F.fromInt(2n), F.sqrt(M.mpPi(wp), wp), wp)), wp), r, wp);
      return rnd(reIf(r, isRealC(b) && isRealC(z)), prec);
    });
    if (v) return v;
  }
  return hypsum([], [b], z, prec, opts);
}

/** mpmath _hyp1f1: the asymptotic expansion in two 2F0 series for |z| >= 2**7. */
function hyp1f1(a: Mpc, b: Mpc, z: Mpc, prec: number, opts: HyperOptions): Mpc {
  if (isZeroC(z)) return C1;
  const magz = cmag(z);
  if (magz >= 7 && !(isInt(a) && F.sign(a[0]) <= 0)) {
    const v = attempt(() => {
      const wp = prec + magz;
      const sector = F.sign(z[1]) < 0;
      const h = (ps: Mpc[], p: number): HyperTerm[] => {
        const [A, B] = [at(ps, 0), at(ps, 1)];
        const E = expjpi(sector ? cneg(A) : A, p);
        const rz = cdiv(C1, z, p);
        return [
          [[E, z], [C1, cneg(A)], [B], [csub(B, A, p)], [A, cadd(C1, csub(A, B, p), p)], [], cneg(rz)],
          [[cexp(z, p), z], [C1, csub(A, B, p)], [B], [A], [csub(B, A, p), csub(C1, A, p)], [], rz],
        ];
      };
      const r = hypercomb(h, [a, b], wp, { forceSeries: true });
      return rnd(reIf(r, allReal([a, b, z])), prec);
    });
    if (v) return v;
  }
  return hypsum([a], [b], z, prec, opts);
}

/**
 * The asymptotic series sum_k c_k w**k of 2F2 and of 1F2, 2F3 (c from a recurrence): the sum, or
 * NoConvergence when the terms do not decrease fast enough.
 */
function asymptoticSum(coef: (k: number) => Mpc, term: (ck: Mpc, k: number) => [Mpc, Mpc], wp: number): [Mpc, Mpc] {
  // |t1| < 0.1*eps with mpmath's eps = 2**(1 - wp)
  const tol = 1 - wp + Math.log2(0.1);
  let sums: [Mpc, Mpc] = [C0, C0];
  let tprev = 0;
  for (let k = 0; ; k++) {
    const ts = term(coef(k), k);
    const t1 = log2abs(ts[0]);
    if (t1 < tol) break;
    // the series does not converge quickly enough: |t[k-1]|/|t[k]| < 1.5
    if (k > 5 && tprev - t1 < Math.log2(1.5)) throw new NoConvergence();
    sums = [cadd(sums[0], ts[0], wp), cadd(sums[1], ts[1], wp)];
    tprev = t1;
  }
  return sums;
}

/** A memoized coefficient sequence c(k) with c(0), c(1), ... given and a recurrence for the rest. */
function memo(initial: Mpc[], next: (k: number, c: (j: number) => Mpc) => Mpc): (k: number) => Mpc {
  const cache = [...initial];
  const c = (k: number): Mpc => {
    while (cache.length <= k) cache.push(next(cache.length, (j) => at(cache, j)));
    return at(cache, k);
  };
  return c;
}

const sq = (x: Mpc, p: number): Mpc => cmul(x, x, p);
const kc = (k: number): Mpc => int(k);
const lin = (p: number, ...xs: Mpc[]): Mpc => sumC(xs, p);
const rat = (n: bigint, d: bigint, p: number): Mpc => [F.fromRational(n, d, p), ZERO];

/** mpmath _hyp2f2: the asymptotic expansion (in exp(z) and two 3F1 series) for |z| > 8. */
function hyp2f2(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const [a1, a2] = [at(as, 0), at(as, 1)];
  const [b1, b2] = [at(bs, 0), at(bs, 1)];
  const magz = cmag(z);
  if (!opts.forceSeries && magAbs(z) > 3) {
    const v = attempt(() => {
      const wp = prec + magz;
      const h = (ps: Mpc[], p: number): HyperTerm[] => {
        const [A1, A2, B1, B2] = [at(ps, 0), at(ps, 1), at(ps, 2), at(ps, 3)];
        const X = csub(cadd(A1, A2, p), cadd(B1, B2, p), p);
        const As = cadd(A1, A2, p);
        const Bs = cadd(B1, B2, p);
        const c1 = cadd(cmul(csub(As, C1, p), X, p), csub(cmul(B1, B2, p), cmul(A1, A2, p), p), p);
        const c = memo([C1, c1], (k, cc) => {
          const K = kc(k);
          const uu1 = lin(
            p,
            C1,
            cneg(Bs),
            cmul(int(2), A1, p),
            sq(A1, p),
            cmul(int(2), A2, p),
            sq(A2, p),
            cneg(cmul(As, Bs, p)),
            cmul(A1, A2, p),
            cmul(B1, B2, p),
            cmul(csub(cmul(int(2), Bs, p), cmul(int(3), cadd(As, C1, p), p), p), K, p),
            cmul(int(2), sq(K, p), p),
          );
          const uu2 = cmul(cmul(lin(p, K, cneg(As), B1, int(-1)), lin(p, K, cneg(As), B2, int(-1)), p), lin(p, K, cneg(X), int(-2)), p);
          return cdiv(csub(cmul(uu1, cc(k - 1), p), cmul(uu2, cc(k - 2), p), p), K, p);
        });
        const rz = cdiv(C1, z, p);
        const [s1] = asymptoticSum(c, (ck, k) => [cmul(ck, M.cpowInt(rz, BigInt(k), p), p), C0], p);
        const S = cmul(cexp(z, p), s1, p);
        const nrz = cneg(rz);
        return [
          [[z, S], [X, C1], [B1, B2], [A1, A2], [], [], C0],
          [[cneg(z)], [cneg(A1)], [B1, B2, csub(A2, A1, p)], [A2, csub(B1, A1, p), csub(B2, A1, p)], [A1, lin(p, A1, cneg(B1), C1), lin(p, A1, cneg(B2), C1)], [lin(p, A1, cneg(A2), C1)], nrz],
          [[cneg(z)], [cneg(A2)], [B1, B2, csub(A1, A2, p)], [A1, csub(B1, A2, p), csub(B2, A2, p)], [A2, lin(p, A2, cneg(B1), C1), lin(p, A2, cneg(B2), C1)], [lin(p, cneg(A1), A2, C1)], nrz],
        ];
      };
      const r = hypercomb(h, [a1, a2, b1, b2], wp, { forceSeries: true, maxterms: 4 * wp });
      return rnd(reIf(r, allReal([a1, a2, b1, b2, z])), prec);
    });
    if (v) return v;
  }
  return hypsum(as, bs, z, prec, opts);
}

/**
 * The exponential part 0.5*S of the asymptotic expansions of 1F2 and 2F3: the two series in
 * (+-i/2)**k (-z)**(-k/2) times exp(+-i (pi X + 2 sqrt(-z))).
 */
function oscillatingPart(c: (k: number) => Mpc, X: Mpc, z: Mpc, p: number): Mpc {
  const r = M.cpow(cneg(z), real(F.neg(HALF)), p);
  const [s1, s2] = asymptoticSum(
    c,
    (ck, k) => {
      const w = cmul(ck, M.cpowInt(cmul(r, half, p), BigInt(k), p), p);
      return [cmul(M.cpowInt(cneg(CI), BigInt(k), p), w, p), cmul(M.cpowInt(CI, BigInt(k), p), w, p)];
    },
    p,
  );
  const phase = cadd(cmul(real(M.mpPi(p)), X, p), cmul(int(2), M.csqrt(cneg(z), p), p), p);
  const S = cadd(cmul(cexp(cmul(CI, phase, p), p), s1, p), cmul(cexp(cmul(cneg(CI), phase, p), p), s2, p), p);
  return cmul(half, S, p);
}

/** mpmath _hyp1f2: the asymptotic expansion for |z| > 2**19 and sqrt(|z|) > 1.5 prec. */
function hyp1f2(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const a1 = at(as, 0);
  const [b1, b2] = [at(bs, 0), at(bs, 1)];
  if (!opts.forceSeries && magAbs(z) > 19 && Math.sqrt(absD(z)) > 1.5 * prec) {
    const v = attempt(() => {
      const wp = prec + Math.floor(cmag(z) / 2);
      const h = (ps: Mpc[], p: number): HyperTerm[] => {
        const [A1, B1, B2] = [at(ps, 0), at(ps, 1), at(ps, 2)];
        const X = cmul(half, lin(p, A1, cneg(B1), cneg(B2), half), p);
        const d = lin(p, A1, cneg(B1), cneg(B2));
        const e = lin(p, cmul(int(3), A1, p), B1, B2, int(-2));
        const q4 = rat(1n, 4n, p);
        const q316 = rat(3n, 16n, p);
        const c1 = cmul(int(2), lin(p, cmul(cmul(q4, e, p), d, p), cmul(B1, B2, p), cneg(q316)), p);
        const c2 = cadd(
          cmul(int(2), sq(lin(p, cmul(B1, B2, p), cmul(cmul(q4, d, p), e, p), cneg(q316)), p), p),
          cmul(rat(1n, 16n, p), lin(p, cmul(cmul(int(-16), csub(cmul(int(2), A1, p), int(3), p), p), cmul(B1, B2, p), p), cmul(cmul(int(4), d, p), lin(p, cmul(int(-8), sq(A1, p), p), cmul(int(11), A1, p), B1, B2, int(-2)), p), int(-3)), p),
          p,
        );
        const c = memo([C1, c1, c2], (k, cc) => {
          const K = kc(k);
          const uu1 = lin(p, cmul(int(3), sq(K, p), p), cmul(lin(p, cmul(int(-6), A1, p), cmul(int(2), B1, p), cmul(int(2), B2, p), int(-4)), K, p), cmul(int(3), sq(A1, p), p), cneg(sq(csub(B1, B2, p), p)), cneg(cmul(cmul(int(2), A1, p), lin(p, B1, B2, int(-2)), p)), q4);
          const uu2 = cmul(cmul(lin(p, K, cneg(A1), B1, cneg(B2), cneg(half)), lin(p, K, cneg(A1), cneg(B1), B2, cneg(half)), p), lin(p, K, cneg(A1), B1, B2, rat(-5n, 2n, p)), p);
          return cdiv(csub(cmul(uu1, cc(k - 1), p), cmul(uu2, cc(k - 2), p), p), cmul(int(2), K, p), p);
        });
        const S2 = oscillatingPart(c, X, z, p);
        return [
          [[S2, real(M.mpPi(p)), cneg(z)], [C1, real(F.neg(HALF)), X], [B1, B2], [A1], [], [], C0],
          [[cneg(z)], [cneg(A1)], [B1, B2], [csub(B1, A1, p), csub(B2, A1, p)], [A1, lin(p, A1, cneg(B1), C1), lin(p, A1, cneg(B2), C1)], [], cdiv(C1, z, p)],
        ];
      };
      const r = hypercomb(h, [a1, b1, b2], wp, { forceSeries: true, maxterms: 4 * wp });
      return rnd(reIf(r, allReal([a1, b1, b2, z])), prec);
    });
    if (v) return v;
  }
  return hypsum(as, bs, z, prec, opts);
}

/** mpmath _hyp2f3: the asymptotic expansion for |z| > 2**19 and sqrt(|z|) > 1.5 prec. */
function hyp2f3(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const [a1, a2] = [at(as, 0), at(as, 1)];
  const [b1, b2, b3] = [at(bs, 0), at(bs, 1), at(bs, 2)];
  if (!opts.forceSeries && magAbs(z) > 19 && Math.sqrt(absD(z)) > 1.5 * prec) {
    const v = attempt(() => {
      const wp = prec + Math.floor(cmag(z) / 2);
      const h = (ps: Mpc[], p: number): HyperTerm[] => {
        const [A1, A2, B1, B2, B3] = [at(ps, 0), at(ps, 1), at(ps, 2), at(ps, 3), at(ps, 4)];
        const X = cmul(half, lin(p, A1, A2, cneg(B1), cneg(B2), cneg(B3), half), p);
        const A2s = cadd(A1, A2, p);
        const B3s = lin(p, B1, B2, B3);
        const A = cmul(A1, A2, p);
        const B = lin(p, cmul(B1, B2, p), cmul(B3, B2, p), cmul(B1, B3, p));
        const R = cmul(cmul(B1, B2, p), B3, p);
        const c1 = cmul(int(2), lin(p, B, cneg(A), cmul(cmul(rat(1n, 4n, p), lin(p, cmul(int(3), A2s, p), B3s, int(-2)), p), csub(A2s, B3s, p), p), rat(-3n, 16n, p)), p);
        const c2 = cadd(
          cmul(half, sq(c1, p), p),
          cmul(rat(1n, 16n, p), lin(p, cmul(cmul(int(-16), csub(cmul(int(2), A2s, p), int(3), p), p), csub(B, A, p), p), cmul(int(32), R, p), cmul(cmul(int(4), lin(p, cmul(int(-8), sq(A2s, p), p), cmul(int(11), A2s, p), cmul(int(8), A, p), B3s, int(-2)), p), csub(A2s, B3s, p), p), int(-3)), p),
          p,
        );
        const X2 = cmul(int(2), X, p);
        const c = memo([C1, c1, c2], (k, cc) => {
          const K = kc(k);
          const K1 = kc(k - 1);
          const uu1 = cmul(cmul(cmul(lin(p, K, cneg(X2), int(-3)), lin(p, K, cneg(X2), cmul(int(-2), B1, p), int(-1)), p), lin(p, K, cneg(X2), cmul(int(-2), B2, p), int(-1)), p), lin(p, K, cneg(X2), cmul(int(-2), B3, p), int(-1)), p);
          const uu2 = lin(
            p,
            cmul(int(4), M.cpowInt(K1, 3n, p), p),
            cneg(cmul(cmul(int(6), cadd(cmul(int(4), X, p), B3s, p), p), sq(K1, p), p)),
            cmul(cmul(int(2), lin(p, cmul(int(24), sq(X, p), p), cmul(cmul(int(12), B3s, p), X, p), cmul(int(4), B, p), B3s, int(-1)), p), K1, p),
            cmul(int(-32), M.cpowInt(X, 3n, p), p),
            cneg(cmul(cmul(int(24), B3s, p), sq(X, p), p)),
            cmul(int(-4), B, p),
            cmul(int(-8), R, p),
            cneg(cmul(cmul(int(4), lin(p, cmul(int(4), B, p), B3s, int(-1)), p), X, p)),
            cmul(int(2), B3s, p),
            int(-1),
          );
          const uu3 = lin(p, cmul(int(5), sq(K1, p), p), cmul(cmul(int(2), lin(p, cmul(int(-10), X, p), A2s, cmul(int(-3), B3s, p), int(3)), p), K1, p), cmul(int(2), c1, p));
          return cdiv(lin(p, cmul(uu1, cc(k - 3), p), cneg(cmul(uu2, cc(k - 2), p)), cmul(uu3, cc(k - 1), p)), cmul(int(2), K, p), p);
        });
        const S2 = oscillatingPart(c, X, z, p);
        const rz = cdiv(C1, z, p);
        return [
          [[S2, real(M.mpPi(p)), cneg(z)], [C1, real(F.neg(HALF)), X], [B1, B2, B3], [A1, A2], [], [], C0],
          [[cneg(z)], [cneg(A1)], [B1, B2, B3, csub(A2, A1, p)], [A2, csub(B1, A1, p), csub(B2, A1, p), csub(B3, A1, p)], [A1, lin(p, A1, cneg(B1), C1), lin(p, A1, cneg(B2), C1), lin(p, A1, cneg(B3), C1)], [lin(p, A1, cneg(A2), C1)], rz],
          [[cneg(z)], [cneg(A2)], [B1, B2, B3, csub(A1, A2, p)], [A1, csub(B1, A2, p), csub(B2, A2, p), csub(B3, A2, p)], [A2, lin(p, A2, cneg(B1), C1), lin(p, A2, cneg(B2), C1), lin(p, A2, cneg(B3), C1)], [lin(p, cneg(A1), A2, C1)], rz],
        ];
      };
      const r = hypercomb(h, [a1, a2, b1, b2, b3], wp, { forceSeries: true, maxterms: 4 * wp });
      return rnd(reIf(r, allReal([a1, a2, b1, b2, b3, z])), prec);
    });
    if (v) return v;
  }
  return hypsum(as, bs, z, prec, opts);
}

/** mpmath _hyp2f0: the (divergent) series when it is accurate enough, else through the confluent function U. */
function hyp2f0(a: Mpc, b: Mpc, z: Mpc, prec: number, opts: HyperOptions): Mpc {
  try {
    return hypsum([a, b], [], z, prec, { ...opts, maxterms: opts.maxterms ?? prec });
  } catch (err) {
    if (!(err instanceof NoConvergence) || opts.forceSeries) throw err;
  }
  // (the parameters are a and 1 + a - b, named a and b in h as in mpmath)
  const h = (ps: Mpc[], p: number): HyperTerm[] => {
    const [a0, b0] = [at(ps, 0), at(ps, 1)];
    const w = sinpi(b0, p);
    const rz = cneg(cdiv(C1, z, p));
    const pi = real(M.mpPi(p));
    return [
      [[pi, w, rz], [C1, int(-1), a0], [], [lin(p, a0, cneg(b0), C1), b0], [a0], [b0], rz],
      [[cneg(pi), w, rz], [C1, int(-1), lin(p, C1, a0, cneg(b0))], [], [a0, csub(int(2), b0, p)], [lin(p, a0, cneg(b0), C1)], [csub(int(2), b0, p)], rz],
    ];
  };
  return hypercomb(h, [a, lin(prec + 20, C1, a, cneg(b))], prec, opts);
}

// ---------------------------------------------------------------------------
// nsum: convergence acceleration (mpmath calculus/extrapolation.py)
// ---------------------------------------------------------------------------

/**
 * Python's random.Random(seed).getrandbits(10) sequence (MT19937 seeded by init_by_array with the
 * seed as one 32-bit word), which mpmath's randomized Shanks transformation uses.
 */
export function pyRandomBits10(seed: number): () => number {
  const N = 624;
  const mt = new Uint32Array(N);
  mt[0] = 19650218;
  for (let i = 1; i < N; i++) {
    const v = at(mt, i - 1);
    mt[i] = Math.imul(1812433253, v ^ (v >>> 30)) + i;
  }
  let i = 1;
  for (let k = N; k > 0; k--) {
    const v = at(mt, i - 1);
    // (the key has one word, so j stays 0)
    mt[i] = (at(mt, i) ^ Math.imul(v ^ (v >>> 30), 1664525)) + seed;
    i++;
    if (i >= N) {
      mt[0] = at(mt, N - 1);
      i = 1;
    }
  }
  for (let k = N - 1; k > 0; k--) {
    const v = at(mt, i - 1);
    mt[i] = (at(mt, i) ^ Math.imul(v ^ (v >>> 30), 1566083941)) - i;
    i++;
    if (i >= N) {
      mt[0] = at(mt, N - 1);
      i = 1;
    }
  }
  mt[0] = 0x80000000;
  let index = N;
  return () => {
    if (index >= N) {
      for (let k = 0; k < N; k++) {
        const y = (at(mt, k) & 0x80000000) | (at(mt, (k + 1) % N) & 0x7fffffff);
        mt[k] = at(mt, (k + 397) % N) ^ (y >>> 1) ^ (y & 1 ? 0x9908b0df : 0);
      }
      index = 0;
    }
    let y = at(mt, index++);
    y ^= y >>> 11;
    y ^= (y << 7) & 0x9d2c5680;
    y ^= (y << 15) & 0xefc60000;
    y ^= y >>> 18;
    return (y >>> 0) >>> 22;
  };
}

/** mpmath sign of a number: -1, 0, 1 for a real one, z/|z| for a complex one. */
function csign(z: Mpc, wp: number): Mpc {
  if (isRealC(z)) return int(F.sign(z[0]));
  return cdiv(z, real(M.cabs(z, wp)), wp);
}

/**
 * mpmath richardson: Richardson extrapolation of the partial sums seq (of every other one when the
 * last differences change sign); [the estimate, the largest weight].
 */
export function richardson(seqIn: readonly Mpc[], wp: number): [Mpc, Mpf] {
  const d = (i: number): Mpc => csub(at(seqIn, seqIn.length - i), at(seqIn, seqIn.length - i - 1), wp);
  const seq = sameC(csign(d(1), wp), csign(d(2), wp)) ? seqIn : seqIn.filter((_, i) => i % 2 === 0);
  const N = Math.floor(seq.length / 2) - 1;
  const n = BigInt(N);
  let fac = 1n;
  for (let k = 2n; k <= n; k++) fac *= k;
  let c = F.div(F.fromInt((N % 2 ? -1n : 1n) * n ** n), F.fromInt(fac), wp);
  let s: Mpc = C0;
  let maxc: Mpf = ONE;
  for (let k = 0; k <= N; k++) {
    s = cadd(s, cmul(real(c), at(seq, N + k), wp), wp);
    if (F.cmp(F.abs(c), maxc) > 0) maxc = F.abs(c);
    c = F.mul(c, F.mulInt(F.powInt(F.fromInt(BigInt(k + N + 1)), n, wp), BigInt(k - N), wp), wp);
    c = F.div(c, F.mulInt(F.powInt(F.fromInt(BigInt(k + N)), n, wp), BigInt(1 + k), wp), wp);
  }
  return [s, maxc];
}

/**
 * mpmath shanks(seq, table, randomized=True): the epsilon table of the partial sums, extended from
 * the rows already in table; a zero difference is replaced by a small random multiple of eps.
 */
export function shanks(seq: readonly Mpc[], table: Mpc[][], wp: number): Mpc[][] {
  const start = table.length;
  let stop = seq.length - 1;
  if (stop & 1) stop -= 1;
  const eps = F.ldexp(ONE, 1 - wp);
  const rnd = pyRandomBits10(start);
  for (let i = start; i < stop; i++) {
    const row: Mpc[] = [];
    for (let j = 0; j <= i; j++) {
      let a: Mpc;
      let b: Mpc;
      if (j === 0) {
        a = C0;
        b = csub(at(seq, i + 1), at(seq, i), wp);
      } else {
        const prev = at(table, i - 1);
        a = j === 1 ? at(seq, i) : at(prev, j - 2);
        b = csub(at(row, j - 1), at(prev, j - 1), wp);
      }
      if (isZeroC(b)) b = real(F.mulInt(eps, BigInt(1 + rnd())));
      row.push(cadd(a, cdiv(C1, b, wp), wp));
    }
    table.push(row);
  }
  return table;
}

/**
 * mpmath nsum(term, [0, inf], method='r+s', strict=True): the partial sums extended in steps of
 * 10, 20, 30, ... terms and extrapolated by Richardson's and Shanks' methods, at 4 (prec + 10)
 * bits, until an estimate changes by less than eps/2**10; NoConvergence after maxterms terms
 * (mpmath's default 10 dps).
 */
export function nsum(term: (k: number, wp: number) => Mpc, prec: number, maxterms = F.precToDps(prec) * 10): Mpc {
  const tol = F.ldexp(ONE, -9 - prec);
  const wp = (prec + 10) * 4;
  const eps = F.ldexp(ONE, 1 - wp);
  const absC = (z: Mpc): Mpf => M.cabs(z, wp);
  let tryRichardson = true;
  let tryShanks = true;
  let lastRichardson: Mpc = C0;
  let table: Mpc[][] = [];
  const partial: Mpc[] = [];
  let psum: Mpc = C0;
  for (let index = 0, step = 10; index < maxterms; step += 10) {
    for (let k = index; k < index + step; k++) {
      psum = cadd(psum, term(k, wp), wp);
      partial.push(psum);
    }
    index += step;
    const best = at(partial, partial.length - 1);
    if (F.cmp(absC(csub(best, at(partial, partial.length - 2), wp)), tol) <= 0) return rnd(best, prec);
    if (tryRichardson) {
      const [value, maxc] = richardson(partial, wp);
      if (F.cmp(absC(csub(value, lastRichardson, wp)), tol) <= 0) return rnd(value, prec);
      lastRichardson = value;
      // unreliable because of cancellation
      if (F.cmp(F.mul(eps, maxc), tol) > 0) tryRichardson = false;
    }
    if (tryShanks) {
      table = shanks(partial, table, wp);
      const row = at(table, table.length - 1);
      const est1 = at(row, row.length - 1);
      if (F.cmp(absC(csub(est1, at(row, row.length - 3), wp)), tol) <= 0) return rnd(est1, prec);
      if (F.cmp(F.mul(eps, absC(at(row, row.length - 2))), tol) > 0) tryShanks = false;
    }
  }
  throw new NoConvergence('nsum did not converge');
}

/**
 * mpmath gammaprod(a, b) as Buhring's expansion uses it: 0 when b has more poles than a,
 * undefined (inf) when a has more. With equal numbers the poles are the same values in a and b
 * (the parameters b - a3 that appear in both), whose limit ratios are 1.
 */
function gammaprod(a: readonly Mpc[], b: readonly Mpc[], prec: number): Mpc | undefined {
  const wp = prec + 15;
  const polesNum = a.filter(isNpInt).length;
  const polesDen = b.filter(isNpInt).length;
  if (polesNum < polesDen) return C0;
  if (polesNum > polesDen) return undefined;
  let r: Mpc = C1;
  for (const x of a) if (!isNpInt(x)) r = cmul(r, cgamma(x, wp), wp);
  for (const x of b) if (!isNpInt(x)) r = cdiv(r, cgamma(x, wp), wp);
  return rnd(r, prec);
}

/**
 * mpmath _hypq1fq (3F2, 4F3, ...): the series for |z| < 1 or a terminating series; near the unit
 * circle 3F2 by Buhring's expansion at z = 1 (|z - 1| < 0.05) and the series with convergence
 * acceleration (nsum); the 1/z transformation outside. Where nsum fails mpmath sums by
 * Euler-Maclaurin, which is not ported (NotImplementedError).
 */
function hypq1fq(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions): Mpc {
  const absz = absD(z);
  const ispoly = as.some(isNpInt);
  if (absz < 1 || ispoly) {
    try {
      return hypsum(as, bs, z, prec, opts);
    } catch (err) {
      // (mpmath also rethrows for |z| > 1.1, which the series is not tried at)
      if (!(err instanceof NoConvergence) || ispoly) throw err;
    }
  }
  if (sameC(z, C1)) {
    const S = F.sub(sumC(bs, prec)[0], sumC(as, prec)[0], prec);
    // the divergent series at 1: hyper(as, bs, 0.9)*inf
    if (F.sign(S) <= 0) throw new HyperInfinity(hyper(as, bs, real(F.fromRational(9n, 10n, prec)), prec, opts));
  }
  if (as.length === 3 && absD(csub(z, C1, 53)) < 0.05) {
    const [a1, a2, a3] = [at(as, 0), at(as, 1), at(as, 2)];
    const [b1, b2] = [at(bs, 0), at(bs, 1)];
    const u0 = csub(cadd(b1, b2, prec), a3, prec);
    // (a1, a2 are not nonpositive integers here, so the numerator has no poles of its own)
    const cache = [defined(gammaprod([csub(b2, a3, prec), csub(b1, a3, prec), a1, a2], [csub(b2, a3, prec), csub(b1, a3, prec), C1, u0], prec))];
    const term = (k: number, wp: number): Mpc => {
      const u = cadd(u0, int(k), wp);
      for (let j = cache.length; j <= k; j++) {
        const t = cmul(cmul(at(cache, j - 1), lin(wp, b1, int(j - 1), cneg(a3)), wp), lin(wp, b2, int(j - 1), cneg(a3)), wp);
        cache.push(cdiv(t, cmul(int(j), lin(wp, u0, int(j - 1)), wp), wp));
      }
      return cmul(at(cache, k), chyp2f1(a1, a2, u, z, wp), wp);
    };
    try {
      const S = nsum(term, prec);
      const g = gammaprod([b1, b2], [a1, a2, a3], prec);
      // mpmath's S*inf for a nonpositive integer b
      if (g === undefined) throw new HyperInfinity(S);
      return rnd(cmul(S, g, prec), prec);
    } catch (err) {
      if (!(err instanceof NoConvergence)) throw err;
    }
  }
  if (absz < 1.1 && F.cmp(z[0], ONE) <= 0) {
    const cache: Mpc[] = [C1];
    const term = (k: number, wp: number): Mpc => {
      for (let j = cache.length; j <= k; j++) {
        let t = at(cache, j - 1);
        for (const a of as) t = cmul(t, cadd(a, int(j - 1), wp), wp);
        for (const b of bs) t = cdiv(t, cadd(b, int(j - 1), wp), wp);
        cache.push(cdiv(cmul(t, z, wp), int(j), wp));
      }
      return at(cache, k);
    };
    try {
      return nsum(term, prec, opts.maxNsumTerms);
    } catch (err) {
      if (!(err instanceof NoConvergence)) throw err;
    }
    if (absz <= 1) return hyperEulerMaclaurin(as, bs, z, prec);
  }
  const p = as.length;
  const h = (ps: Mpc[], wp: number): HyperTerm[] => {
    const a = ps.slice(0, p);
    const b = ps.slice(p);
    const recz = cdiv(C1, z, wp);
    const negz = cneg(z);
    return a.map((ak, k) => [
      [negz],
      [cneg(ak)],
      [...b, ak, ...a.filter((_, j) => j !== k).map((aj) => csub(aj, ak, wp))],
      [...a, ...b.map((bj) => csub(bj, ak, wp))],
      [ak, ...b.map((bj) => lin(wp, ak, cneg(bj), C1))],
      a.filter((_, j) => j !== k).map((aj) => lin(wp, C1, cneg(aj), ak)),
      recz,
    ]);
  };
  return hypercomb(h, [...as, ...bs], prec, opts);
}

/**
 * mpmath _hypq1fq's last resort: integrate the gamma-ratio tail and add
 * Euler–Maclaurin corrections. Logarithmic derivatives are polygammas;
 * exponential Bell polynomials recover the derivatives of the term itself.
 * maxTruncations bounds work when the error estimate does not converge.
 * @internal
 */
export function hyperEulerMaclaurin(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, maxTruncations = 5, initialTruncation = Math.max(32, 2 * prec)): Mpc {
  const lower = [...bs, C1];
  const upperGamma = [...as];
  const lowerGamma = [...lower];
  const shifts: Mpc[] = [];
  // Gamma(n+a)/Gamma(n+a+1) = 1/(n+a). This also avoids cancellation
  // in logarithmic derivatives and repeated gamma evaluations at quadrature nodes.
  for (let i = upperGamma.length - 1; i >= 0; i--) {
    const a = at(upperGamma, i);
    const j = lowerGamma.findIndex((b) => sameC(csub(b, a, prec + 20), C1));
    if (j >= 0) {
      shifts.push(a);
      upperGamma.splice(i, 1);
      lowerGamma.splice(j, 1);
    }
  }
  const tolerance = F.ldexp(ONE, -prec - 10);
  // The continuous tail must start to the right of all gamma poles.
  let trunc = Math.max(initialTruncation, 1 + Math.ceil(Math.max(0, ...as.map((a) => -F.toNumber(a[0])))));
  for (let attempt = 0; attempt < maxTruncations; attempt++, trunc *= 2) {
    const wp = prec + 35 + attempt * Math.ceil(prec / 2);
    const logz = M.clog(z, wp);
    const scale = defined(gammaprod(bs, as, wp), 'finite hypergeometric prefactor');
    let head: Mpc = C0;
    let term: Mpc = C1;
    for (let k = 0; k < trunc; k++) {
      head = cadd(head, term, wp);
      for (const a of as) term = cmul(term, cadd(a, int(k), wp), wp);
      for (const b of lower) term = cdiv(term, cadd(b, int(k), wp), wp);
      term = cmul(term, z, wp);
    }
    const continuousTerm = (n: Mpc, p: number): Mpc => {
      // Large quadrature nodes need extra bits when log-gamma terms cancel.
      const work = p + Math.max(0, cmag(n)) + 20;
      const logs = csub(sumC(upperGamma.map((a) => cloggamma(cadd(a, n, work), work)), work), sumC(lowerGamma.map((b) => cloggamma(cadd(b, n, work), work)), work), work);
      let value = cmul(scale, cexp(cadd(logs, cmul(n, logz, work), work), work), work);
      for (const a of shifts) value = cdiv(value, cadd(n, a, work), work);
      return rnd(value, p);
    };
    const [integral, error] = quad(continuousTerm, [int(trunc)], true, wp);
    if (F.cmp(error, tolerance) > 0) continue;
    let tail = cadd(integral, cmul(term, real(F.ldexp(ONE, -1)), wp), wp);
    const derivatives: Mpc[] = [term];
    const logs: Mpc[] = [];
    let factorial = 1n;
    let previous = Infinity;
    for (let order = 1; order <= Math.max(12, prec); order++) {
      let logarithmic = csub(sumC(upperGamma.map((a) => cpolygamma(order - 1, cadd(a, int(trunc), wp), wp)), wp), sumC(lowerGamma.map((b) => cpolygamma(order - 1, cadd(b, int(trunc), wp), wp)), wp), wp);
      for (const a of shifts) logarithmic = cadd(logarithmic, cmul(int(order % 2 ? -factorial : factorial), M.cpowInt(cadd(a, int(trunc), wp), -BigInt(order), wp), wp), wp);
      if (order === 1) logarithmic = cadd(logarithmic, logz, wp);
      logs.push(logarithmic);
      let derivative: Mpc = C0;
      let binomial = 1n;
      for (let j = 0; j < order; j++) {
        derivative = cadd(derivative, cmul(int(binomial), cmul(at(derivatives, order - 1 - j), at(logs, j), wp), wp), wp);
        binomial = binomial * BigInt(order - 1 - j) / BigInt(j + 1);
      }
      derivatives.push(derivative);
      factorial *= BigInt(order);
      if (order % 2 === 0) continue;
      const [bp, bq] = bernoulli(order + 1);
      const correction = cmul(derivative, real(F.fromRational(bp, bq * factorial * BigInt(order + 1), wp)), wp);
      const magnitude = cmag(correction);
      if (magnitude > previous) break;
      tail = csub(tail, correction, wp);
      if (magnitude < -prec - 12) return rnd(cadd(head, tail, wp), prec);
      previous = magnitude;
    }
  }
  throw new NoConvergence('Euler-Maclaurin summation did not converge');
}

/**
 * mpmath _hyp_borel (p > q + 1): the divergent series summed while its terms are small enough,
 * else (p <= q + 3) its Borel sum by numerical integration; NoConvergence when the integral is not
 * accurate.
 */
function hypBorel(as: readonly Mpc[], bs: readonly Mpc[], z: Mpc, prec: number, opts: HyperOptions): Mpc {
  try {
    return hypsum(as, bs, z, prec, { ...opts, maxterms: opts.maxterms ?? prec });
  } catch (err) {
    if (!(err instanceof NoConvergence)) throw err;
  }
  const wp = prec + 10;
  // |t| <= eps/4 with mpmath's eps = 2**(1 - prec)
  const tol = -1 - prec;
  let t: Mpc = C1;
  let s: Mpc = C1;
  for (let k = 1; k < wp; k++) {
    for (const a of as) t = cmul(t, cadd(a, int(k - 1), wp), wp);
    for (const b of bs) t = cdiv(t, cadd(b, int(k - 1), wp), wp);
    t = cdiv(cmul(t, z, wp), int(k), wp);
    s = cadd(s, t, wp);
    if (Math.log2(absD(t)) <= tol) return rnd(s, prec);
  }
  if (as.length <= bs.length + 3) {
    // the Borel integral int_0^oo exp(-t) pF(q+1)(as; bs, 1; t z) dt, on a path around the
    // positive real axis (where the integrand is branched) for arg(z) < 0.25
    const argz = F.toNumber(M.carg(z, 53));
    let contour: Mpc[] = [C0];
    if (argz < 0.25) {
      const u = cdiv(z, real(F.fromNumber(Math.max(1, absD(z)))), wp);
      const j2: Mpc = [ZERO, F.fromInt(argz >= 0 ? 2n : -2n)];
      contour = [C0, j2, cdiv(cadd(j2, int(2), wp), u, wp), cdiv(int(2), u, wp)];
    }
    const g = (t: Mpc, p: number): Mpc => cmul(cexp(cneg(t), p), hyper(as, [...bs, C1], cmul(t, z, p), p), p);
    const [I, err] = quad(g, contour, true, prec);
    if (F.cmp(err, F.mul(M.cabs(I, prec), F.ldexp(ONE, 4 - prec))) <= 0) return I;
  }
  throw new NoConvergence('the Borel sum of a divergent hypergeometric series did not converge');
}
