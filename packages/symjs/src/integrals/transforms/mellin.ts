// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Mellin transform and its inverse (SymPy mellin_transform,
 * inverse_mellin_transform, _rewrite_sin and _rewrite_gamma).
 *
 * SymPy computes Mellin transforms with its Meijer G integrator and inverts
 * them through Meijer G functions and hyperexpand. symjs uses a table of
 * Mellin transforms for the forward direction and, for the inverse,
 * SymPy's reduction of F(s) to a Meijer G function (_rewrite_gamma)
 * followed by the closed forms of the elementary G functions; rational
 * F(s) are inverted by residues.
 */

import type { ExprLike, Sym } from '../../core/nodes';
import { Add, Dummy, Expr, Fn, Integral, Mul, Pow, Rational, S, Constant } from '../../core/nodes';
import { and, or } from '../../core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne } from '../../core/logic';
import { add, exp, mul, neg, pow, sqrt, sub, sympify } from '../../core/ops';
import { isNegative, isPositive, isReal } from '../../core/assumptions';
import { asCoeffMul, asIndependent, asNumerDenom, asRealImag, isRationalFunction } from '../../core/methods';
import { some, subs } from '../../core/traverse';
import { igcd, ilcm } from '../../core/numberutils';
import { abs, arg, re, sin } from '../../functions/elementary';
import { Max, Min, ceiling, gamma } from '../../functions/special';
import { besselj, besselk } from '../../functions/bessel';
import { MeijerG, meijerg } from '../../functions/hyper';
import { diff } from '../../calculus/diff';
import { Poly, factor } from '../../polys/sympoly';
import { rootsDict } from '../../polys/poly';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { expand, expandMul, expand_power_exp as expandPowerExp } from '../../simplify/expand';
import { cancel, together } from '../../simplify/rational';
import { gammasimp } from '../../simplify/gammasimp';
import { rewrite } from '../../simplify/rewrite';
import type { TransformHints, TransformResult } from './base';
import type { IntegralTransform } from './base';
import { GenericIntegralTransform, IntegralTransformError, decide, holds, isFalseExpr, isPolyIn, matchByName, mget, mulArgs, wild, transformArgs } from './base';
import { at, defined, first, pair } from '../../core/guard';
import { InvariantError } from '../../core/errors';
import { Heaviside, isHeaviside } from './delta';

const isExpPow = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const isRat = (e: Expr): e is Rational => e instanceof Rational;

/** The strip and the result of a Mellin transform: [F, [a, b], cond]. */
export type MellinTriple = [Expr, [Expr, Expr], Expr];

// ---------------------------------------------------------------------------
// Forward transform
// ---------------------------------------------------------------------------

/**
 * Split f into C * x**alpha * rest, with C and alpha free of x.
 */
function splitPower(f: Expr, x: Sym): [Expr, Expr, Expr[]] {
  let C: Expr = S.One;
  let alpha: Expr = S.Zero;
  const rest: Expr[] = [];
  for (const fac of mulArgs(f)) {
    if (!fac.has(x)) C = mul(C, fac);
    else if (fac.key === x.key) alpha = add(alpha, 1);
    else if (fac instanceof Pow && fac.base.key === x.key && !fac.exp.has(x)) alpha = add(alpha, fac.exp);
    else rest.push(fac);
  }
  return [C, alpha, rest];
}

/** The Mellin transform from the table: [F, a, b, cond] in s. */
function mellinTable(f: Expr, x: Sym, s: Expr): [Expr, Expr, Expr, Expr] | undefined {
  const [C, alpha, rest] = splitPower(f, x);
  const sp = add(s, alpha);
  const b = wild('b', x);
  const p = wild('p', x);
  const r = wild('r', x);
  if (rest.length === 1) {
    const g = at(rest, 0);
    // exp(-b*x**p)
    if (g instanceof Pow && isExpPow(g)) {
      const lin = matchByName(g.exp, mul(-1, b, x));
      const m = matchByName(g.exp, mul(-1, b, pow(x, p))) ?? (lin ? new Map([...lin, ['p', S.One]]) : undefined);
      if (m) {
        const B = mget(m, 'b');
        const P = mget(m, 'p');
        if (isRat(P) && !P.isZero) {
          const q = mul(sp, pow(P, -1));
          const F = mul(C, gamma(q), pow(abs(P), -1), expandPowerExp(pow(B, neg(q))));
          const cond = Gt0(re(B));
          if (isFalseExpr(cond)) return undefined;
          return P.isPositive ? [F, re(neg(alpha)), S.Infinity, cond] : [F, S.NegativeInfinity, re(neg(alpha)), cond];
        }
      }
    }
    // Heaviside(1 - x), Heaviside(x - 1)
    if (isHeaviside(g) && g.args.length === 1) {
      const a0 = at(g.args, 0);
      if (a0.key === sub(1, x).key) return [mul(C, pow(sp, -1)), re(neg(alpha)), S.Infinity, S.true];
      if (a0.key === sub(x, 1).key) return [mul(C, -1, pow(sp, -1)), S.NegativeInfinity, re(neg(alpha)), S.true];
    }
    // (1 + b*x)**(-r)
    if (g instanceof Pow && !isExpPow(g)) {
      const m = matchByName(g.base, add(1, mul(b, x)));
      if (m && !g.exp.has(x)) {
        const B = mget(m, 'b');
        // only for b off the negative real axis (1/(1 - x) has no Mellin transform)
        const argOk = decide(Lt(abs(arg(B)), S.Pi));
        if (argOk === false || isNegative(B) === true) return undefined;
        const R = neg(g.exp);
        const F = mul(C, gamma(sp), gamma(sub(R, sp)), pow(gamma(R), -1), expandPowerExp(pow(B, neg(sp))));
        return [F, re(neg(alpha)), re(sub(R, alpha)), argOk === true ? S.true : Lt(abs(arg(B)), S.Pi)];
      }
    }
    if (g instanceof Fn && (g.name === 'sin' || g.name === 'cos' || g.name === 'besselj')) {
      const argi = g.name === 'besselj' ? at(g.args, 1) : at(g.args, 0);
      const m = matchByName(argi, mul(b, x));
      if (m && isPositive(mget(m, 'b')) === true) {
        const B = mget(m, 'b');
        const scale = expandPowerExp(pow(B, neg(sp)));
        if (g.name === 'sin') {
          const F = mul(C, pow(2, sp), S.Half, sqrt(S.Pi), gamma(add(mul(sp, S.Half), S.Half)), pow(gamma(sub(1, mul(sp, S.Half))), -1), scale);
          return [F, re(sub(-1, alpha)), re(sub(1, alpha)), S.true];
        }
        if (g.name === 'cos') {
          const F = mul(C, pow(2, sp), S.Half, sqrt(S.Pi), gamma(mul(sp, S.Half)), pow(gamma(sub(S.Half, mul(sp, S.Half))), -1), scale);
          return [F, re(neg(alpha)), re(sub(1, alpha)), S.true];
        }
        const nu = at(g.args, 0);
        const F = mul(C, pow(2, sub(sp, 1)), gamma(mul(add(nu, sp), S.Half)), pow(gamma(add(mul(sub(nu, sp), S.Half), 1)), -1), scale);
        return [F, re(sub(neg(nu), alpha)), re(sub(Rational.of(3n, 2n), alpha)), S.true];
      }
    }
  }
  if (rest.length === 2) {
    // (x - 1)**(r - 1)*Heaviside(x - 1)
    const hj = rest.findIndex((g) => isHeaviside(g) && g.args.length === 1 && at(g.args, 0).key === sub(x, 1).key);
    if (hj >= 0) {
      const m = matchByName(at(rest, 1 - hj), pow(sub(x, 1), r));
      if (m) {
        const R = add(mget(m, 'r'), 1);
        return [mul(C, gamma(R), gamma(sub(sub(1, R), sp)), pow(gamma(sub(1, sp)), -1)), S.NegativeInfinity, re(sub(sub(1, R), alpha)), Gt0(re(R))];
      }
    }
    // (1 - x)**(r - 1)*Heaviside(1 - x)
    const hi = rest.findIndex((g) => isHeaviside(g) && g.args.length === 1 && at(g.args, 0).key === sub(1, x).key);
    if (hi >= 0) {
      const other = at(rest, 1 - hi);
      const m = matchByName(other, pow(sub(1, x), r));
      if (m) {
        const R = add(mget(m, 'r'), 1);
        return [mul(C, gamma(R), gamma(sp), pow(gamma(add(sp, R)), -1)), re(neg(alpha)), S.Infinity, Gt0(re(R))];
      }
    }
  }
  return undefined;
}

const Gt0 = (e: Expr): Expr => Gt(e, 0);

/** SymPy _mellin_transform: [F, [a, b], cond]. */
export function mellinTransformImpl(f: Expr, x: Sym, s: Expr, simplify: boolean): MellinTriple {
  const r = mellinTable(f, x, s);
  if (!r) throw new IntegralTransformError('Mellin', f, 'could not compute integral');
  const [F, a, b, cond] = r;
  const out = simplify ? gammasimp(F) : F;
  return [out, [a, b], cond];
}

/**
 * The unevaluated Mellin transform of f(x) (SymPy MellinTransform).
 */
export class MellinTransform extends GenericIntegralTransform {
  constructor(f: ExprLike, x: ExprLike, s: ExprLike) {
    super('MellinTransform', [sympify(f), sympify(x), sympify(s)]);
  }
  /** SymPy MellinTransform._name. */
  static readonly transformName = 'Mellin';
  get transformName(): string {
    return 'Mellin';
  }
  protected get latexName(): string {
    return '\\mathcal{M}';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MellinTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new MellinTransform(f, this.functionVariable, this.transformVariable);
  }
  get asIntegral(): Expr {
    const x = this.functionVariable;
    return new Integral([mul(this.function, pow(x, sub(this.transformVariable, 1))), x, S.Zero, S.Infinity]);
  }
  protected computeTransform(f: Expr, x: Sym, s: Sym, hints: TransformHints & { simplify: boolean }): TransformResult {
    const r = mellinTransformImpl(f, x, s, hints.simplify);
    return hints.noconds === true ? r[0] : r;
  }
  protected override collapseExtra(extra: readonly (readonly (Expr | readonly [Expr, Expr])[])[]): readonly (Expr | readonly [Expr, Expr])[] {
    const as: Expr[] = [];
    const bs: Expr[] = [];
    const conds: Expr[] = [];
    for (const e of extra) {
      const [strip, c] = pair(e);
      if (strip instanceof Expr || !(c instanceof Expr)) throw new InvariantError('Mellin transform extra data is not (strip, condition)');
      as.push(strip[0]);
      bs.push(strip[1]);
      conds.push(c);
    }
    const A = Max(...as);
    const B = Min(...bs);
    const cond = and(...conds);
    if (holds(Ge(A, B)) || isFalseExpr(cond)) throw new IntegralTransformError('Mellin', undefined, 'no combined convergence.');
    return [[A, B], cond];
  }
}

/**
 * The Mellin transform F(s) of f(x), the integral of x**(s - 1)*f(x) over
 * (0, oo) (SymPy mellin_transform). Returns [F, [a, b], cond] with the
 * fundamental strip a < Re(s) < b, F alone with `noconds: true`, or an
 * unevaluated MellinTransform.
 *
 * @example
 * mellinTransform(exp(-x), x, s)  // [gamma(s), [0, oo], True]
 */
export function mellinTransform(f: ExprLike, x: Sym, s: ExprLike, hints: TransformHints = {}): TransformResult {
  return new MellinTransform(f, x, s).doit(hints);
}

// ---------------------------------------------------------------------------
// _rewrite_sin and _rewrite_gamma
// ---------------------------------------------------------------------------

/**
 * Rewrite sin(m*s + n) as fac/(gamma1*gamma2) with the gamma functions on
 * the right side of the strip (a, b) (SymPy _rewrite_sin).
 *
 * @internal
 */
export function rewriteSin(mn: readonly [ExprLike, ExprLike], s: Expr, a: ExprLike, _b: ExprLike): [Expr, Expr, Expr] {
  const m = expandMul(mul(sympify(mn[0]), pow(S.Pi, -1)));
  const n = expandMul(mul(sympify(mn[1]), pow(S.Pi, -1)));
  const r = ceiling(sub(mul(-1, m, sympify(a)), asRealImag(n)[0]));
  return [gamma(add(mul(m, s), n, r)), gamma(sub(sub(sub(1, n), r), mul(m, s))), mul(pow(-1, r), S.Pi)];
}

/** The result of rewriteGamma: [[an, ap], [bm, bq], arg, exponent, fac]. */
export type RewrittenGamma = [[Expr[], Expr[]], [Expr[], Expr[]], Expr, Expr, Expr];

/** A pole lies inside the fundamental strip (SymPy MellinTransformStripError). */
export class MellinTransformStripError extends RangeError {
  constructor(msg: string) {
    super(msg);
    this.name = 'MellinTransformStripError';
  }
}

type PendingFactor = { fact: Expr; sinArg?: undefined } | { fact?: undefined; sinArg: Expr };

/**
 * Rewrite a product of gamma functions, linear factors, exponentials and
 * trigonometric functions of s as the Mellin transform of a Meijer G
 * function (SymPy _rewrite_gamma). Returns [[an, ap], [bm, bq], C, e, fac]
 * such that fac*meijerg((an, ap), (bm, bq), C/x**e) is the inverse Mellin
 * transform of f over the strip (a, b); a or b may be undefined.
 *
 * @internal
 */
export function rewriteGamma(fIn: ExprLike, s: Sym, aIn: ExprLike | undefined, bIn: ExprLike | undefined): RewrittenGamma {
  let f = sympify(fIn);
  let a_: Expr | undefined = aIn === undefined ? undefined : sympify(aIn);
  let b_: Expr | undefined = bIn === undefined ? undefined : sympify(bIn);
  const left = (c0: Expr, isNumer: boolean): boolean | undefined => {
    const c = expand(re(c0));
    if (a_ === undefined && b_ !== undefined && b_.key === S.Infinity.key) return true;
    if (a_ === undefined) return b_ === undefined ? true : holds(Lt(c, b_));
    if (b_ === undefined) return holds(Le(c, a_));
    if (holds(Ge(c, b_))) return false;
    if (holds(Le(c, a_))) return true;
    if (isNumer) return undefined;
    if (a_.freeSymbols().size || b_.freeSymbols().size || c.freeSymbols().size) return undefined;
    throw new MellinTransformStripError('Pole inside critical strip?');
  };
  // 1) the common multiplier of s
  const mults: Expr[] = [];
  const collectCoeff = (argE: Expr, div: Expr): void => {
    let ar = argE;
    if (ar instanceof Add) ar = asIndependent(ar, [s])[1];
    const [coeff] = asCoeffMul(ar, [s]);
    mults.push(mul(coeff, pow(div, -1)));
  };
  const fnAtoms = (names: readonly string[]): Fn[] => {
    const out = new Map<string, Fn>();
    some(f, (n) => {
      if (n instanceof Fn && names.includes(n.name) && n.has(s)) out.set(n.key, n);
      return false;
    });
    return [...out.values()];
  };
  for (const g of fnAtoms(['gamma'])) collectCoeff(at(g.args, 0), S.One);
  for (const g of fnAtoms(['sin', 'cos', 'tan', 'cot'])) collectCoeff(at(g.args, 0), S.Pi);
  const sMults = mults.map((x) => (isReal(x) === true ? abs(x) : x));
  let common: Expr = S.One;
  for (const x of sMults) {
    if (!isRat(x)) {
      common = x;
      break;
    }
  }
  const scaled = sMults.map((x) => mul(x, pow(common, -1)));
  if (!scaled.every(isRat) || isReal(common) !== true) throw new IntegralTransformError('Gamma', undefined, 'Nonrational multiplier');
  const rats = scaled.filter(isRat);
  let sMultiplier: Expr = mul(common, pow(Rational.of(ilcm(1n, ...rats.map((x) => x.q))), -1));
  if (sMultiplier.key === common.key) {
    sMultiplier = rats.length === 0 ? common : mul(common, Rational.of(igcd(...rats.map((x) => x.p))));
  }
  f = subs(f, [[s, mul(s, pow(sMultiplier, -1))]]);
  let fac: Expr = pow(sMultiplier, -1);
  const exponent = pow(sMultiplier, -1);
  if (a_ !== undefined) a_ = mul(a_, sMultiplier);
  if (b_ !== undefined) b_ = mul(b_, sMultiplier);
  // 2) process the factors
  const [numer, denom] = asNumerDenom(f);
  const args: [PendingFactor, boolean][] = [...mulArgs(numer).map((x): [PendingFactor, boolean] => [{ fact: x }, true]), ...mulArgs(denom).map((x): [PendingFactor, boolean] => [{ fact: x }, false])];
  const facs: Expr[] = [];
  const dfacs: Expr[] = [];
  const numerGammas: [Expr, Expr][] = [];
  const denomGammas: [Expr, Expr][] = [];
  const exponentials: Expr[] = [];
  const exception = (fact: Expr): IntegralTransformError => new IntegralTransformError('Inverse Mellin', f, `Unrecognised form '${String(fact)}'`);
  const linearArg = (argE: Expr, fact: Expr): [Expr, Expr] => {
    if (!isPolyIn(argE, s)) throw exception(fact);
    const p = Poly.from(argE, [s]);
    if (p.degree() !== 1) throw exception(fact);
    return pair(p.allCoeffs());
  };
  while (args.length) {
    const [item, isNumer] = defined(args.pop(), 'factor');
    const [ugammas, lgammas] = isNumer ? [numerGammas, denomGammas] : [denomGammas, numerGammas];
    const ufacs = isNumer ? facs : dfacs;
    if (item.sinArg !== undefined) {
      const a = item.sinArg;
      let g1: Expr;
      let g2: Expr;
      let fac_: Expr;
      if (isNumer) [g1, g2, fac_] = [gamma(mul(a, pow(S.Pi, -1))), gamma(sub(1, mul(a, pow(S.Pi, -1)))), S.Pi];
      else [g1, g2, fac_] = rewriteSin(linearArg(a, sin(a)), s, a_ ?? S.NegativeInfinity, b_ ?? S.Infinity);
      args.push([{ fact: g1 }, !isNumer], [{ fact: g2 }, !isNumer]);
      ufacs.push(fac_);
      continue;
    }
    const fact = item.fact;
    if (!fact.has(s)) {
      ufacs.push(fact);
    } else if (fact instanceof Pow) {
      const base = fact.base;
      const ex = fact.exp;
      if (ex instanceof Rational && ex.isInteger) {
        let cond = isNumer;
        if (ex.isNegative) cond = !cond;
        const n = Number(ex.p < 0n ? -ex.p : ex.p);
        for (let i = 0; i < n; i++) args.push([{ fact: base }, cond]);
        continue;
      } else if (!base.has(s)) {
        const [a, b] = linearArg(ex, fact);
        const bb = isNumer ? base : pow(base, -1);
        exponentials.push(pow(bb, a));
        facs.push(pow(bb, b));
      } else throw exception(fact);
    } else if (isPolyIn(fact, s)) {
      const p = Poly.from(fact, [s]);
      if (p.degree() !== 1) {
        const coeff = p.LC();
        const rs = rootsDict(fact, s, { multiple: true });
        if (rs.length !== p.degree()) throw exception(fact);
        ufacs.push(coeff);
        for (const c of rs) args.push([{ fact: sub(s, c) }, isNumer]);
        continue;
      }
      const [a, c0] = pair(p.allCoeffs());
      ufacs.push(a);
      const cc = mul(c0, -1, pow(a, -1));
      if (left(cc, isNumer) === true) {
        ugammas.push([S.One, add(neg(cc), 1)]);
        lgammas.push([S.One, neg(cc)]);
      } else {
        ufacs.push(S.NegOne);
        ugammas.push([S.NegOne, add(cc, 1)]);
        lgammas.push([S.NegOne, cc]);
      }
    } else if (fact instanceof Fn && fact.name === 'gamma') {
      const [a, b] = linearArg(at(fact.args, 0), fact);
      if (isNumer) {
        const pos = holds(Lt(0, a));
        const negv = holds(Lt(a, 0));
        const l = left(mul(-1, b, pow(a, -1)), isNumer);
        if ((pos && l === false) || (negv && l === true)) throw new IntegralTransformError('Inverse Mellin', f, 'Gammas partially over the strip');
      }
      ugammas.push([a, b]);
    } else if (fact instanceof Fn && fact.name === 'sin') {
      args.push([{ sinArg: at(fact.args, 0) }, isNumer]);
    } else if (fact instanceof Fn && fact.name === 'tan') {
      const a = at(fact.args, 0);
      args.push([{ sinArg: a }, isNumer], [{ sinArg: sub(mul(S.Pi, S.Half), a) }, !isNumer]);
    } else if (fact instanceof Fn && fact.name === 'cos') {
      args.push([{ sinArg: sub(mul(S.Pi, S.Half), at(fact.args, 0)) }, isNumer]);
    } else if (fact instanceof Fn && fact.name === 'cot') {
      const a = at(fact.args, 0);
      args.push([{ sinArg: sub(mul(S.Pi, S.Half), a) }, isNumer], [{ sinArg: a }, !isNumer]);
    } else throw exception(fact);
  }
  fac = mul(fac, ...facs, ...dfacs.map((d) => pow(d, -1)));
  // 3) gamma functions of +-s + c
  const an: Expr[] = [];
  const ap: Expr[] = [];
  const bm: Expr[] = [];
  const bq: Expr[] = [];
  for (const [gammas, plus, minus, isNumer] of [
    [numerGammas, an, bm, true],
    [denomGammas, bq, ap, false],
  ] as const) {
    while (gammas.length) {
      const [a, c] = defined(gammas.pop(), 'gamma factor');
      if (a.key !== S.One.key && a.key !== S.NegOne.key) {
        if (!(a instanceof Rational) || !a.isInteger) throw new TypeError('a is not an integer');
        const p = a.isNegative ? neg(a) : a;
        const P = Number(a.isNegative ? -a.p : a.p);
        const newa = mul(a, pow(p, -1));
        const newc = mul(c, pow(p, -1));
        for (let k = 0; k < P; k++) gammas.push([newa, add(newc, Rational.of(BigInt(k), BigInt(P)))]);
        const factor0 = mul(pow(mul(2, S.Pi), mul(sub(1, p), S.Half)), pow(p, sub(c, S.Half)));
        if (isNumer) {
          fac = mul(fac, factor0);
          exponentials.push(pow(p, a));
        } else {
          fac = mul(fac, pow(factor0, -1));
          exponentials.push(pow(p, neg(a)));
        }
        continue;
      }
      if (a.key === S.One.key) plus.push(sub(1, c));
      else minus.push(c);
    }
  }
  const argE = mul(...exponentials);
  const byKey = (p: Expr, q: Expr): number => compareKeys(sortKey(p), sortKey(q));
  an.sort(byKey);
  ap.sort(byKey);
  bm.sort(byKey);
  bq.sort(byKey);
  return [[an, ap], [bm, bq], argE, exponent, fac];
}

/** Split z = C*x**(-e) into [C, e] (C free of x). */
function asCoeffX(z: Expr, x: Expr): [Expr, Expr] | undefined {
  let C: Expr = S.One;
  let e: Expr = S.Zero;
  for (const f of mulArgs(z)) {
    if (!f.has(x)) C = mul(C, f);
    else if (f.key === x.key) e = sub(e, 1);
    else if (f instanceof Pow && f.base.key === x.key && !f.exp.has(x)) e = sub(e, f.exp);
    else return undefined;
  }
  return [C, e];
}

// ---------------------------------------------------------------------------
// Meijer G functions with elementary closed forms
// ---------------------------------------------------------------------------

/**
 * The closed form of meijerg((an, ap), (bm, bq), z) for the elementary
 * cases (SymPy hyperexpand for one or two parameters), or undefined.
 */
function meijergClosedForm(an0: readonly Expr[], ap0: readonly Expr[], bm0: readonly Expr[], bq0: readonly Expr[], z: Expr, xv: Expr): Expr | undefined {
  // equal parameters in (an, bq) and in (ap, bm) cancel (SymPy hyperexpand reduces the order)
  const cancelPairs = (xs: readonly Expr[], ys: readonly Expr[]): [Expr[], Expr[]] => {
    const a = [...xs];
    const b = [...ys];
    for (let i = a.length - 1; i >= 0; i--) {
      const ai = at(a, i);
      const j = b.findIndex((y) => y.key === ai.key);
      if (j >= 0) {
        a.splice(i, 1);
        b.splice(j, 1);
      }
    }
    return [a, b];
  };
  const [an, bq] = cancelPairs(an0, bq0);
  const [ap, bm] = cancelPairs(ap0, bm0);
  const [n, m, p, q] = [an.length, bm.length, an.length + ap.length, bm.length + bq.length];
  if (m === 0 && n === 0) return undefined;
  const zc = asCoeffX(z, xv);
  // Heaviside(1 - z) and Heaviside(z - 1) in terms of x > 0 when z = C*x**(-e)
  const stepBelow = (): Expr => (zc && isPositive(zc[0]) === true ? (isPositive(zc[1]) === true ? Heaviside(sub(pow(xv, zc[1]), zc[0])) : Heaviside(sub(zc[0], pow(xv, zc[1])))) : Heaviside(sub(1, z)));
  const stepAbove = (): Expr => (zc && isPositive(zc[0]) === true ? (isPositive(zc[1]) === true ? Heaviside(sub(zc[0], pow(xv, zc[1]))) : Heaviside(sub(pow(xv, zc[1]), zc[0]))) : Heaviside(sub(z, 1)));
  // G^{1,0}_{1,1}(z | a; b) = z**b*(1 - z)**(a - b - 1)/gamma(a - b) for z < 1
  if (m === 1 && n === 0 && ap.length === 1 && bq.length === 0) {
    const a = at(ap, 0);
    const b = at(bm, 0);
    return mul(pow(z, b), pow(sub(1, z), sub(sub(a, b), 1)), pow(gamma(sub(a, b)), -1), stepBelow());
  }
  // G^{0,1}_{1,1}(z | a; b) = z**(a - 1)*(1 - 1/z)**(a - b - 1)/gamma(a - b) for z > 1
  if (m === 0 && n === 1 && ap.length === 0 && bq.length === 1) {
    const a = at(an, 0);
    const b = at(bq, 0);
    const w = pow(z, -1);
    return mul(pow(w, sub(1, a)), pow(sub(1, w), sub(sub(a, b), 1)), pow(gamma(sub(a, b)), -1), stepAbove());
  }
  // G^{1,0}_{0,1}(z | -; b) = z**b*exp(-z)
  if (m === 1 && n === 0 && p === 0 && q === 1) return mul(pow(z, at(bm, 0)), exp(neg(z)));
  // G^{0,1}_{1,0}(z | a; -) = z**(a - 1)*exp(-1/z)
  if (m === 0 && n === 1 && p === 1 && q === 0) return mul(pow(z, sub(at(an, 0), 1)), exp(neg(pow(z, -1))));
  // G^{1,1}_{1,1}(z | a; b) = gamma(1 - a + b)*z**b*(1 + z)**(a - b - 1)
  if (m === 1 && n === 1 && p === 1 && q === 1) {
    const a = at(an, 0);
    const b = at(bm, 0);
    const q = sub(sub(a, b), 1);
    // with z = C/x**e (x > 0): z**b*(1 + z)**q = C**b*x**(-e*(b + q))*(x**e + C)**q
    if (zc) {
      const [C, e] = zc;
      return mul(gamma(add(sub(1, a), b)), pow(C, b), pow(xv, mul(-1, e, add(b, q))), pow(add(pow(xv, e), C), q));
    }
    return mul(gamma(add(sub(1, a), b)), pow(z, b), pow(add(z, 1), q));
  }
  // G^{1,0}_{0,2}(z | -; b1, b2) = z**((b1 + b2)/2)*besselj(b1 - b2, 2*sqrt(z))
  if (m === 1 && n === 0 && p === 0 && q === 2) {
    const [b1, b2] = [at(bm, 0), at(bq, 0)];
    return mul(pow(z, mul(add(b1, b2), S.Half)), besselj(sub(b1, b2), mul(2, sqrt(z))));
  }
  // G^{2,0}_{0,2}(z | -; b1, b2) = 2*z**((b1 + b2)/2)*besselk(b1 - b2, 2*sqrt(z))
  if (m === 2 && n === 0 && p === 0 && q === 2) {
    const [b1, b2] = pair(bm);
    return mul(2, pow(z, mul(add(b1, b2), S.Half)), besselk(sub(b1, b2), mul(2, sqrt(z))));
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Inverse transform
// ---------------------------------------------------------------------------

/**
 * Write a sum of terms c*x**e as x**e0*(sum of c*x**(e - e0)), with e0 the
 * smallest (`low`) or the largest exponent, as SymPy's hyperexpand writes
 * the two regions of a Meijer G function.
 */
function powerFactored(terms: readonly Expr[], x: Expr, low: boolean, pullContent: boolean): Expr {
  if (terms.length <= 1) return add(...terms);
  const exps = terms.map((t) => {
    for (const f of mulArgs(t)) {
      if (f.key === x.key) return S.One;
      if (f instanceof Pow && f.base.key === x.key && isRat(f.exp)) return f.exp;
    }
    return S.Zero;
  });
  if (!exps.every(isRat) || terms.some((t) => some(t, (n) => n instanceof Fn && n.name === 'log'))) return add(...terms);
  const vals = exps.filter(isRat).map((e) => e.value);
  const e0 = defined(exps[vals.indexOf(low ? Math.min(...vals) : Math.max(...vals))], 'extreme exponent');
  const inner = terms.map((t) => mul(t, pow(x, neg(e0))));
  if (!pullContent) return new Mul([pow(x, e0), add(...inner)].sort((p, q) => compareKeys(sortKey(p), sortKey(q))));
  const cs = inner.map((t) => asCoeffMul(t)[0]);
  const c = first(cs);
  return mul(c, pow(x, e0), add(...inner.map((t) => mul(t, pow(c, -1)))));
}

/** The inverse Mellin transform of a rational function of s by residues. */
function inverseMellinRational(F: Expr, s: Sym, x: Expr, strip: readonly [Expr | undefined, Expr | undefined]): Expr {
  const G0 = cancel(F);
  const [num0, den0] = asNumerDenom(G0);
  const pn = Poly.from(num0, [s]);
  const pd = Poly.from(den0, [s]);
  if (pn.degree() >= pd.degree()) throw new IntegralTransformError('Inverse Mellin', F, 'does not converge');
  // the constant factor stays outside, as SymPy's _rewrite_gamma keeps it in fac
  const content = mul(pn.LC(), pow(pd.LC(), -1));
  const G = cancel(mul(G0, pow(content, -1)));
  const den = asNumerDenom(G)[1];
  const [a, b] = strip;
  const isLeft = (c: Expr): boolean => {
    const rc = re(c);
    if (a === undefined && b !== undefined && b.key === S.Infinity.key) return true;
    if (a === undefined) return b === undefined ? true : holds(Lt(rc, b));
    if (b === undefined) return holds(Le(rc, a));
    if (holds(Ge(rc, b))) return false;
    if (holds(Le(rc, a))) return true;
    throw new MellinTransformStripError('Pole inside critical strip?');
  };
  const leftTerms: Expr[] = [];
  const rightTerms: Expr[] = [];
  const kernel = pow(x, neg(s));
  for (const [c, mult] of rootsDict(den, s)) {
    // h = G*(s - c)**mult, with the factor divided out of the denominator exactly
    const [gn, gd] = asNumerDenom(G);
    const [q] = Poly.from(expand(gd), [s]).div(Poly.from(expand(pow(sub(s, c), mult)), [s]));
    const h = mul(gn, pow(q.asExpr(), -1));
    let d = mul(h, kernel);
    for (let k = 1; k < mult; k++) d = diff(d, s);
    let fact = 1;
    for (let k = 2; k < mult; k++) fact *= k;
    const res = expand(mul(subs(d, [[s, c]]), Rational.of(1n, BigInt(fact))));
    for (const t of res instanceof Add ? res.args : [res]) (isLeft(c) ? leftTerms : rightTerms).push(t);
  }
  const lt = powerFactored(leftTerms, x, true, false);
  const gt = powerFactored(rightTerms.map(neg), x, false, true);
  return mul(content, add(mul(Heaviside(sub(x, 1)), gt), mul(Heaviside(sub(1, x)), lt)));
}

/** SymPy _inverse_mellin_transform: [f, cond]. */
function inverseMellinTransformImpl(F0: Expr, s: Sym, x_: Expr, strip: readonly [Expr | undefined, Expr | undefined]): [Expr, Expr] {
  const x = new Dummy('t', { positive: true });
  const F = rewrite(F0, 'gamma');
  for (const g of [factor(F), expandMul(F), expand(F)]) {
    if (g instanceof Add) {
      const ress = g.args.map((G) => inverseMellinTransformImpl(G, s, x, strip));
      let res = add(...ress.map((r) => r[0]));
      // SymPy: factor(res, gens=Heaviside atoms), a full factorization when there are none
      if (!some(res, isHeaviside) && !some(res, (n) => n instanceof MeijerG)) res = factor(together(res));
      return [subs(res, [[x, x_]]), and(...ress.map((r) => r[1]))];
    }
    const gs = gammasimp(g);
    if (isRationalFunction(gs, [s])) {
      return [subs(inverseMellinRational(gs, s, x, strip), [[x, x_]]), S.true];
    }
    let rg: RewrittenGamma;
    try {
      rg = rewriteGamma(g, s, strip[0], strip[1]);
    } catch (e) {
      if (e instanceof IntegralTransformError) continue;
      throw e;
    }
    const [[an, ap], [bm, bq], C, e, fac] = rg;
    const z = mul(C, pow(pow(x, e), -1));
    const h = meijergClosedForm(an, ap, bm, bq, z, x) ?? meijerg(an, ap, bm, bq, z);
    const delta = sub(add(bm.length, an.length), mul(ap.length + an.length + bm.length + bq.length, S.Half));
    const nu = sub(add(...bm, ...bq), add(...an, ...ap));
    const argz = abs(arg(z));
    const cond = or(Lt(argz, mul(delta, S.Pi)), and(or(Ne(ap.length + an.length, bm.length + bq.length), Ge(0, add(re(nu), 1))), Eq(argz, mul(delta, S.Pi))));
    if (isFalseExpr(cond)) throw new IntegralTransformError('Inverse Mellin', F, 'does not converge');
    return [subs(mul(h, fac), [[x, x_]]), cond];
  }
  throw new IntegralTransformError('Inverse Mellin', F, '');
}

const ALLOWED = new Set(['gamma', 'sin', 'cos', 'tan', 'cot', 'cosh', 'sinh', 'tanh', 'coth', 'factorial', 'rf']);
/** SymPy's sentinel for a missing strip bound (printed as _None). */
const NONE_SENTINEL = new Dummy('None');

/**
 * The unevaluated inverse Mellin transform of F(s) over the strip (a, b)
 * (SymPy InverseMellinTransform).
 */
export class InverseMellinTransform extends GenericIntegralTransform {
  constructor(F: ExprLike, s: ExprLike, x: ExprLike, a?: ExprLike, b?: ExprLike) {
    super('InverseMellinTransform', [sympify(F), sympify(s), sympify(x), a === undefined ? NONE_SENTINEL : sympify(a), b === undefined ? NONE_SENTINEL : sympify(b)]);
  }
  /** SymPy InverseMellinTransform._name. */
  static readonly transformName = 'Inverse Mellin';
  get transformName(): string {
    return 'Inverse Mellin';
  }
  protected get latexName(): string {
    return '\\mathcal{M}^{-1}';
  }
  /** The fundamental strip; undefined bounds were not given (SymPy fundamental_strip). */
  get fundamentalStrip(): [Expr | undefined, Expr | undefined] {
    const [a, b] = [at(this.args, 3), at(this.args, 4)];
    return [a === NONE_SENTINEL ? undefined : a, b === NONE_SENTINEL ? undefined : b];
  }
  protected override get defaultNoconds(): boolean {
    return true;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseMellinTransform(...transformArgs(args), args[3], args[4]);
  }
  protected withFunction(f: Expr): IntegralTransform {
    const [a, b] = this.fundamentalStrip;
    return new InverseMellinTransform(f, this.functionVariable, this.transformVariable, a, b);
  }
  get asIntegral(): Expr {
    const c = new Dummy('c');
    const s = this.functionVariable;
    const integral = new Integral([mul(this.function, pow(this.transformVariable, neg(s))), s, sub(c, mul(S.I, S.Infinity)), add(c, mul(S.I, S.Infinity))]);
    return mul(integral, pow(mul(2, S.Pi, S.I), -1));
  }
  protected computeTransform(F: Expr, s: Sym, x: Sym, hints: TransformHints): TransformResult {
    if (some(F, (n) => n instanceof Fn && n.has(s) && !ALLOWED.has(n.name))) throw new IntegralTransformError('Inverse Mellin', F, 'Component not recognised');
    if (some(F, (n) => n instanceof Pow && !isExpPow(n) && n.base.has(s) && !n.exp.has(s) && !isRat(n.exp))) throw new IntegralTransformError('Inverse Mellin', F, 'Component not recognised');
    const r = inverseMellinTransformImpl(F, s, x, this.fundamentalStrip);
    return hints.noconds === false ? r : r[0];
  }
}

/**
 * The inverse Mellin transform of F(s) over the fundamental strip
 * strip = [a, b] (SymPy inverse_mellin_transform); x is assumed positive.
 * One bound may be undefined. Returns f, [f, cond] with `noconds: false`,
 * or an unevaluated InverseMellinTransform.
 *
 * @example
 * inverseMellinTransform(gamma(s), s, x, [0, oo])  // exp(-x)
 */
export function inverseMellinTransform(F: ExprLike, s: Sym, x: ExprLike, strip: readonly [ExprLike | undefined, ExprLike | undefined], hints: TransformHints = {}): TransformResult {
  return new InverseMellinTransform(F, s, x, strip[0], strip[1]).doit(hints);
}
