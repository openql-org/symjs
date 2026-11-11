// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/numberfields/galois_resolvents.py, BSD-3-Clause; see LICENSE.

/**
 * @file Galois resolvents. Given a polynomial T, a resolvent is a polynomial R
 * whose roots are functions of the roots of T. The Resolvent class computes R
 * for a given T by approximating the roots of T to a sufficient precision;
 * the remaining functions compute the coefficients of resolvents as functions
 * of the coefficients of T, which is how the tables of the resolvent lookup
 * module were produced.
 */

import { at, expectType } from '../../core/guard';
import { Rational, Sym } from '../../core/nodes';
import type { Expr, ExprLike } from '../../core/nodes';
import { mul, pow, sympify } from '../../core/ops';
import { asRealImag } from '../../core/methods';
import { xreplace } from '../../core/traverse';
import { NoMatch } from '../../core/truth';
import type { NoMatchResult } from '../../core/truth';
import { str } from '../../printing/str';
import { evalf } from '../../numeric/evalf';
import * as F from '../../numeric/mpf';
import { Permutation } from '../../combinatorics/permutations';
import { PGL2F5 } from '../../combinatorics/galois';
import { ComplexElement, MPContext } from '../domains/mpelements';
import type { RealElement } from '../domains/mpelements';
import { xring } from '../rings';
import type { PolyElement } from '../rings';
import { Poly } from '../sympoly';
import { resolventCoefficients } from './resolventlookup';

/** An error in the computation of a Galois group. */
export class GaloisGroupException extends RangeError {}

/** A form or a set of cosets that the Resolvent class cannot work with. */
export class ResolventException extends GaloisGroupException {}

/** A conjugate of the form of a resolvent, as a function of the values of its variables. */
export type ResolventRootLambda = (...args: readonly (ExprLike | ComplexElement)[]) => Expr | ComplexElement;

/** The precision target of a resolvent: its coefficients, or its possible integer roots. */
export type ResolventTarget = 'coeffs' | 'roots';

const isNumeric = (v: unknown): v is ComplexElement => v instanceof ComplexElement;

/** The nearest integer, ties to even (mpmath nint). */
function nearestInteger([p, q]: readonly [bigint, bigint]): bigint {
  const floor = p >= 0n ? p / q : -((-p + q - 1n) / q);
  const twice = 2n * (p - floor * q);
  return twice > q || (twice === q && floor % 2n !== 0n) ? floor + 1n : floor;
}

/** floor(log2(p/q)) + 1 for p/q >= 1 (mpmath fastlog of the unrounded value). */
function magnitude(p: bigint, q: bigint): number {
  const k = F.bitLength(p) - F.bitLength(q);
  return k + Number(p >= q << BigInt(k));
}

/** The value of the dense integer polynomial f at a (SymPy dup_eval over ZZ). */
const dupEval = (f: readonly bigint[], a: bigint): bigint => f.reduce((r, c) => r * a + c, 0n);

/**
 * The resolvent R(Y) = prod_{sigma in s} (Y - F(X_sigma(1), ..., X_sigma(n))) of a
 * form F in the variables X, for a set s of left coset representatives of the
 * stabilizer of F in a subgroup G of S_n (Cohen, Def. 6.3.2).
 *
 * When T is a polynomial with Gal(T) <= G, the coefficients of R evaluated at
 * the roots of T are integers. They are determined by approximating the roots
 * of T to a precision that bounds the error of every coefficient by 1/2: F
 * must be homogeneous of total degree t with r terms of unit coefficient, and
 * the number m of conjugates must satisfy m < r 2^t. The error bound of the
 * coefficients is then r^m (mt + 1) M^(mt - 1) epsilon for roots of absolute
 * value at most M >= 2 approximated within epsilon, and that of the single
 * conjugates (the candidates for integer roots of R) is r (t + 1) M^(t - 1)
 * epsilon.
 *
 * @example
 * const X = symbols('X0 X1 X2 X3');
 * const R = new Resolvent(X[0]*X[2] + X[1]*X[3], X, [new Permutation([0, 1, 2, 3]),
 *   new Permutation([1, 0, 2, 3]), new Permutation([3, 1, 2, 0])]);
 * R.rootLambdas[1](...X); // X0*X3 + X1*X2
 */
export class Resolvent {
  readonly F: Expr;
  readonly X: readonly Sym[];
  readonly s: readonly Permutation[];
  /** The number of conjugates of F. */
  readonly m: number;
  /** The total degree of F. */
  readonly t: number;
  /** The number of terms of F. */
  readonly r: number;
  /** The error bound factor that determines the coefficients of the resolvent, a polynomial in M. */
  readonly coeffPrecFunc: Poly;
  /** The error bound factor that determines its integer roots, a polynomial in M. */
  readonly rootPrecFunc: Poly;
  /**
   * The conjugates of F, the roots of the resolvent: the conjugate sigma F is
   * F evaluated at sigma^-1 X. Given symbols they return expressions, given
   * complex numbers their numerical values.
   */
  readonly rootLambdas: readonly ResolventRootLambda[];
  /** The coefficients of the monic polynomial with the given numbers as roots, highest degree first. */
  readonly esfLambdas: readonly ((...roots: readonly ComplexElement[]) => ComplexElement)[];
  readonly #conjugates: readonly ((values: readonly ComplexElement[]) => ComplexElement)[];

  constructor(F: ExprLike, X: readonly Sym[], s: readonly Permutation[]) {
    this.F = sympify(F);
    this.X = X;
    this.s = s;
    this.m = s.length;
    const terms: [readonly number[], bigint][] = [];
    for (const [monom, coeff] of Poly.from(this.F, [...X]).terms()) {
      if (!(coeff instanceof Rational && coeff.q === 1n && (coeff.p === 1n || coeff.p === -1n))) throw new ResolventException('Resolvent class expects forms with unit coeffs');
      terms.push([monom, coeff.p]);
    }
    const degrees = new Set(terms.map(([monom]) => monom.reduce((a, b) => a + b, 0)));
    if (degrees.size > 1) throw new ResolventException('Resolvent class expects homogeneous forms');
    const m = this.m, t = at([...degrees], 0), r = terms.length;
    this.t = t;
    this.r = r;
    if (!(m < r * 2 ** t)) throw new ResolventException('Resolvent class expects m < r*2^t');
    const M = new Sym('M');
    this.coeffPrecFunc = Poly.from(mul(BigInt(r) ** BigInt(m) * BigInt(m * t + 1), pow(M, m * t - 1)), [M]);
    this.rootPrecFunc = Poly.from(mul(r * (t + 1), pow(M, t - 1)), [M]);
    this.#conjugates = s.map((sigma) => {
      const params = sigma.inverse().call([...X]);
      const position = X.map((x) => params.indexOf(x));
      return (values: readonly ComplexElement[]): ComplexElement => {
        const ctx = at(values, 0).context;
        return terms.reduce((sum, [monom, coeff]) => sum.add(monom.reduce((product, e, i) => {
          let v = product;
          for (let k = 0; k < e; k++) v = v.mul(at(values, at(position, i)));
          return v;
        }, ctx.mpc(coeff))), ctx.mpc(0));
      };
    });
    this.rootLambdas = s.map((sigma, j) => {
      const params = sigma.inverse().call([...X]);
      return (...args: readonly (ExprLike | ComplexElement)[]): Expr | ComplexElement => {
        if (args.length !== X.length) throw new TypeError(`expected ${X.length} arguments, got ${args.length}`);
        const values = args.filter(isNumeric);
        if (values.length === args.length) return at(this.#conjugates, j)(values);
        return xreplace(this.F, params.map((p, k) => [p, sympify(expectType(at(args, k), (a: unknown): a is ExprLike => !isNumeric(a), 'all symbolic or all numeric arguments'))]));
      };
    });
    this.esfLambdas = Array.from({ length: m + 1 }, (_, k) => (...roots: readonly ComplexElement[]): ComplexElement => {
      const ctx = at(roots, 0).context;
      let c = [ctx.mpc(1)];
      for (const root of roots) c = [...c, ctx.mpc(0)].map((ci, i) => i === 0 ? ci : ci.sub(at(c, i - 1).mul(root)));
      return at(c, k);
    });
  }

  /**
   * A sufficient precision for evaluating complex numbers of absolute value
   * at most M plugged in for the variables: an int m such that an error below
   * 2^-m determines the coefficients ('coeffs') or the possible integer roots
   * ('roots') of the resolvent.
   */
  getPrec(M: ExprLike | RealElement, target: ResolventTarget = 'coeffs'): number {
    const ctx = new MPContext();
    const [p0, q0] = ctx.toRational(ctx.mpf(M), false);
    const [p, q] = p0 >= 2n * q0 ? [p0, q0] : [2n, 1n];
    const f = target === 'coeffs' ? this.coeffPrecFunc : this.rootPrecFunc;
    const c = f.allCoeffs().map((a) => expectType(a, (e): e is Rational => e instanceof Rational, 'integer coefficient').p);
    const n = c.length - 1;
    const num = c.reduce((sum, a, i) => sum + a * p ** BigInt(n - i) * q ** BigInt(i), 0n);
    return magnitude(2n * num, q ** BigInt(n)) + 1;
  }

  /**
   * The roots of T approximated precisely enough to evaluate the coefficients
   * of this resolvent ('coeffs') or to find its possible integer roots ('roots').
   */
  approximateRootsOfPoly(T: Poly, target: ResolventTarget = 'coeffs'): ComplexElement[] {
    const ctx = new MPContext();
    const roots = T.allRoots({ radicals: false });
    const complex = (r: Expr, digits: number): ComplexElement => {
      const [re, im] = asRealImag(evalf(r, digits));
      return ctx.mpc(re, im);
    };
    // A coarse approximation bounds the magnitude of the roots; 1 covers its error.
    const bound = roots.map((r) => complex(r, 15).abs()).reduce((a, b) => (a.gt(b) ? a : b));
    const [p, q] = ctx.toRational(bound, false);
    const m = this.getPrec(Rational.of(p + q, q), target);
    const n = magnitude(p + q, q) + 1;
    ctx.prec = m + n + 1;
    const digits = F.precToDps(ctx.prec);
    return roots.map((r) => complex(r, digits));
  }

  /** The nearest integer to an integer or real number (ties to even). */
  static roundMpf(a: bigint | number | RealElement): bigint {
    if (typeof a === 'bigint') return a;
    if (typeof a === 'number') return nearestInteger(new MPContext().toRational(a, false));
    return nearestInteger(a.context.toRational(a, false));
  }

  /**
   * The roots of this resolvent for T rounded to the nearest integers: a Map
   * from the indices of the permutations in s whose conjugate rounds to a
   * rational integer to that integer. Any integer root of the resolvent is
   * among them.
   */
  roundRootsToIntegersForPoly(T: Poly): Map<number, bigint> {
    const roots = this.approximateRootsOfPoly(T, 'roots');
    const result = new Map<number, bigint>();
    this.s.forEach((_, i) => {
      const r = at(this.#conjugates, i)(roots);
      if (Resolvent.roundMpf(r.imag) === 0n) result.set(i, Resolvent.roundMpf(r.real));
    });
    return result;
  }

  /**
   * The resolvent for T as a dense polynomial over ZZ, with the coefficients
   * evaluated at the roots of T. With findIntegerRoot, also its first
   * integer root and the index of the permutation in s that gives it (NoMatch
   * for both when there is none, or when findIntegerRoot is false).
   */
  evalForPoly(T: Poly, findIntegerRoot = false): [bigint[], bigint | NoMatchResult, number | NoMatchResult] {
    const roots = this.approximateRootsOfPoly(T, 'coeffs');
    const conjugates = this.#conjugates.map((conjugate) => conjugate(roots));
    const R = this.esfLambdas.map((esf) => {
      const c = esf(...conjugates);
      if (Resolvent.roundMpf(c.imag) !== 0n) throw new ResolventException(`Got non-integer coeff for resolvent: ${c.toString()}`);
      return Resolvent.roundMpf(c.real);
    });
    if (findIntegerRoot) {
      for (const [i, r] of conjugates.entries()) {
        if (Resolvent.roundMpf(r.imag) !== 0n) continue;
        const a = Resolvent.roundMpf(r.real);
        if (dupEval(R, a) === 0n) return [R, a, i];
      }
    }
    return [R, NoMatch, NoMatch];
  }
}

/** Line-wrap a polynomial expression at the first space after width columns. */
export function wrap(text: string, width = 80): string {
  let out = '', col = 0;
  for (const c of text) {
    if (c === ' ' && col > width) {
      out += '\n';
      col = 0;
    } else {
      col += 1;
      out += c;
    }
  }
  return out;
}

/** The symbols s1, ..., sn standing for the elementary symmetric polynomials. */
export function sVars(n: number): Sym[] {
  return Array.from({ length: n }, (_, i) => new Sym(`s${i + 1}`));
}

const seconds = (): number => performance.now() / 1000;

/**
 * The coefficients of the resolvent of the sparse polynomial F in the ring
 * generators X with coset representatives s, besides the leading 1, as
 * functions of the coefficients of T: polynomials in the elementary symmetric
 * polynomials s1, ..., sn of the roots, printed as strings. Also returns the
 * seconds each symmetrization took. Progress messages go to verbose.
 */
export function sparseSymmetrizeResolventCoeffs(F: PolyElement, X: readonly PolyElement[], s: readonly Permutation[], verbose?: (text: string) => void): [string[], number[]] {
  const rootForms = s.map((sigma) => F.compose(X.map((x, i) => [x, at(sigma.call([...X]), i)] as const)));
  verbose?.('----\nComputing the products of the root forms...');
  let t0 = seconds();
  // The coefficients of prod (Y - root) are (-1)^i times the elementary symmetric polynomials.
  let coeffs = [F.ring.one];
  for (const root of rootForms) coeffs = [...coeffs, F.ring.zero].map((c, i) => i === 0 ? c : c.sub(at(coeffs, i - 1).mul(root)));
  verbose?.(`took ${seconds() - t0} seconds`);
  const ss = sVars(X.length);
  const symmetrized: string[] = [];
  const times: number[] = [];
  coeffs.slice(1).forEach((A, i) => {
    verbose?.(`-----\nCoeff ${i + 1}...`);
    t0 = seconds();
    const [B, rem] = A.symmetrize();
    const t = seconds() - t0;
    if (!rem.isZero) throw new ResolventException(`Got nonzero remainder ${rem.toString()} for resolvent (F, X, s) = (${F.toString()}, [${X.join(', ')}], [${s.join(', ')}])`);
    const text = str(B.asExpr(...ss));
    symmetrized.push(text);
    times.push(t);
    verbose?.(`${wrap(text)}\ntook ${t} seconds`);
  });
  return [symmetrized, times];
}

/** A resolvent definition: the form F over the ring generators X, and the coset representatives s. */
export type ResolventDefinition = [F: PolyElement, X: PolyElement[], s: Permutation[]];

/**
 * The resolvents used for polynomials T of degrees 4 through 6, keyed by
 * "degree,number" ("4,0", "4,1", "5,1", "6,1", "6,2").
 */
export function defineResolvents(): Map<string, ResolventDefinition> {
  const cycle = (size: number, ...c: number[]): Permutation => c.length ? new Permutation(size).call(...c) : new Permutation(size);
  const [, X4] = xring('X0,X1,X2,X3');
  let X = X4;
  const x = (i: number): PolyElement => at(X, i);
  const F40 = x(0).mul(x(1).pow(2)).add(x(1).mul(x(2).pow(2))).add(x(2).mul(x(3).pow(2))).add(x(3).mul(x(0).pow(2)));
  const s40 = [cycle(3), cycle(3, 0, 1), cycle(3, 0, 2), cycle(3, 0, 3), cycle(3, 1, 2), cycle(3, 2, 3)];
  const F41 = x(0).mul(x(2)).add(x(1).mul(x(3)));
  const s41 = [cycle(3), cycle(3, 0, 1), cycle(3, 0, 3)];
  const [, X5] = xring('X0,X1,X2,X3,X4');
  X = X5;
  const sq = (i: number): PolyElement => x(i).pow(2);
  const F51 = sq(0).mul(x(1).mul(x(4)).add(x(2).mul(x(3))))
    .add(sq(1).mul(x(2).mul(x(0)).add(x(3).mul(x(4)))))
    .add(sq(2).mul(x(3).mul(x(1)).add(x(4).mul(x(0)))))
    .add(sq(3).mul(x(4).mul(x(2)).add(x(0).mul(x(1)))))
    .add(sq(4).mul(x(0).mul(x(3)).add(x(1).mul(x(2)))));
  const s51 = [cycle(4), cycle(4, 0, 1), cycle(4, 0, 2), cycle(4, 0, 3), cycle(4, 0, 4), cycle(4, 1, 4)];
  const [R6, X6] = xring('X0,X1,X2,X3,X4,X5');
  X = X6;
  const term0 = sq(0).mul(sq(5)).mul(x(1).mul(x(4)).add(x(2).mul(x(3))));
  const terms = new Map<string, PolyElement>();
  for (const sigma of PGL2F5().elements) {
    const t = term0.compose(X6.map((g, i) => [g, at(sigma.call([...X6]), i)] as const));
    terms.set(t.toString(), t);
  }
  const F61 = [...terms.values()].reduce((a, b) => a.add(b), R6.zero);
  const s61 = [cycle(5), ...[1, 2, 3, 4, 5].map((n) => cycle(5, 0, n))];
  const F62 = x(0).mul(x(1)).mul(x(2)).add(x(3).mul(x(4)).mul(x(5)));
  const s62 = [cycle(5), ...[0, 1, 2].flatMap((i) => [0, 1, 2].map((j) => cycle(5, i, j + 3)))];
  return new Map<string, ResolventDefinition>([
    ['4,0', [F40, X4, s40]], ['4,1', [F41, X4, s41]], ['5,1', [F51, X5, s51]], ['6,1', [F61, X6, s61]], ['6,2', [F62, X6, s62]],
  ]);
}

/**
 * The whole lookup table of resolvent coefficient functions as the source
 * text of the SymPy resolvent_lookup module. trialRun stops after the first
 * resolvent; jobs defaults to defineResolvents().
 */
export function generateLambdaLookup(verbose?: (text: string) => void, trialRun = false, jobs: ReadonlyMap<string, ResolventDefinition> = defineResolvents()): string {
  const lambdaLists: [string, string][] = [];
  let totalTime = 0, timeFor61 = 0, timeFor61Last = 0;
  for (const [k, [F, X, s]] of jobs) {
    const [symmetrized, times] = sparseSymmetrizeResolventCoeffs(F, X, s, verbose);
    const sum = times.reduce((a, b) => a + b, 0);
    totalTime += sum;
    if (k === '6,1') {
      timeFor61 = sum;
      timeFor61Last = at(times, times.length - 1);
    }
    const head = `lambda ${sVars(X.length).join(', ')}:`;
    lambdaLists.push([k, symmetrized.map((f) => `${head} (${wrap(f)})`).join(',\n        ')]);
    if (trialRun) break;
  }
  let table = '# This table was generated by a call to\n'
    + '# `sympy.polys.numberfields.galois_resolvents.generate_lambda_lookup()`.\n'
    + `# The entire job took ${totalTime.toFixed(2)}s.\n`
    + `# Of this, Case (6, 1) took ${timeFor61.toFixed(2)}s.\n`
    + `# The final polynomial of Case (6, 1) alone took ${timeFor61Last.toFixed(2)}s.\n`
    + 'resolvent_coeff_lambdas = {\n';
  for (const [k, L] of lambdaLists) table += `    (${k.replace(',', ', ')}): [\n        ${L}\n    ],\n`;
  return table + '}\n';
}

/** Exact resolvent coefficients, in descending order, for degrees four through six. */
export function getResolventByLookup(polynomial: Poly, number: number): Rational[] {
  if (!polynomial.isMonic) throw new RangeError('resolvents require a monic polynomial');
  return resolventCoefficients(polynomial.allCoeffs().slice(1).map((c) => expectType(c, (e): e is Rational => e instanceof Rational, 'rational coefficient')), number);
}
