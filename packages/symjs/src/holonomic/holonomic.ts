// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (holonomic/holonomic.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Holonomic functions (SymPy sympy.holonomic.holonomic): solutions of
 * linear homogeneous differential equations with polynomial coefficients,
 * given by an annihilator (an operator of the Weyl algebra in `Dx`) and
 * initial conditions; their sums, products, compositions, derivatives and
 * integrals, power series, recurrences, and conversions from and to
 * expressions, hypergeometric and Meijer G-functions.
 */

import { NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, first, getOrThrow, last } from '../core/guard';
import type { Truth } from '../core/truth';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, ExtensionExpr, Float, Fn, Mul, Pow, Rational, S, Special, Sym, UndefFn } from '../core/nodes';
import { add, asBaseExp, exp, mul, neg, pow, sqrt, sympify } from '../core/ops';
import { ExprMap } from '../core/exprmap';
import { ordered } from '../core/match';
import { asRealImag, isPolynomial, isRationalFunction } from '../core/methods';
import { Q, ask } from '../core/refine';
import { freeSymbols, mapBottomUp, subs } from '../core/traverse';
import { diff as diffExpr } from '../calculus/diff';
import { evalf as evalfExpr } from '../numeric/evalf';
import { nsimplify } from '../numeric/nfloat';
import { floatString, str } from '../printing/str';
import { compareKeys, sortKey } from '../printing/sortkey';
import { binomial, factorial, gamma } from '../functions/special/special';
import { Hyper, MeijerG, hyper, meijerg } from '../functions/special/hyper';
import { DMP, EX, QQ, RR } from '../polys/domains';
import type { DMF, Domain, GlobalPolynomialRing, OldFractionField } from '../polys/domains';
import { polyCoefficients, rootsDict } from '../polys/poly';
import { divisors } from '../ntheory/factor';
import { gcd as igcd } from '../core/numbers';
import { expandMul } from '../simplify/expand';
import { fraction, together } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { O } from '../series/series';
import { limit } from '../series/limits';
import { linsolve } from '../solvers/public';
import { hyperexpand } from '../simplify/hyperexpand';
import { getCoeffExp, rewrite1 } from '../integrals/meijerint';
import { NotHolonomicError, NotHyperSeriesError, SeriesExpansionError, SingularityError } from './holonomicerrors';
import { HolonomicSequence, RecurrenceOperator, RecurrenceOperators, addLists, listsEqual } from './recurrence';
import { evalfHolonomic } from './numerical';

// ---------------------------------------------------------------------------
// the Weyl algebra
// ---------------------------------------------------------------------------

/** An operand of the operator arithmetic: an operator, a polynomial of the base ring or an expression. */
export type DifferentialOperand = DifferentialOperator | DMP | ExprLike;

/**
 * The algebra of differential operators over a base polynomial ring and the
 * operator `Dx` (SymPy DifferentialOperators).
 */
export function DifferentialOperators(base: GlobalPolynomialRing, generator?: string | Sym): [DifferentialOperatorAlgebra, DifferentialOperator] {
  const ring = new DifferentialOperatorAlgebra(base, generator);
  return [ring, ring.derivativeOperator];
}

/**
 * The Weyl algebra: noncommutative polynomials in `Dx` with coefficients in
 * a base polynomial ring, with Dx*a = a*Dx + a' (SymPy
 * DifferentialOperatorAlgebra).
 */
export class DifferentialOperatorAlgebra {
  /** The operator `Dx` (SymPy derivative_operator). */
  readonly derivativeOperator: DifferentialOperator;
  /** The generator symbol (SymPy gen_symbol). */
  readonly genSymbol: Sym;
  constructor(
    readonly base: GlobalPolynomialRing,
    generator?: string | Sym,
  ) {
    this.derivativeOperator = new DifferentialOperator([base.zero, base.one], this);
    this.genSymbol = generator instanceof Sym ? generator : new Sym(generator ?? 'Dx', { commutative: false });
  }
  toString(): string {
    return `Univariate Differential Operator Algebra in intermediate ${str(this.genSymbol)} over the base ring ${this.base.toString()}`;
  }
  equals(o: DifferentialOperatorAlgebra): boolean {
    return this.base.equals(o.base) && this.genSymbol.key === o.genSymbol.key;
  }
}

/**
 * A differential operator: a list of polynomials of the base ring, one for
 * each power of `Dx` (SymPy DifferentialOperator).
 */
export class DifferentialOperator {
  /** The coefficients of Dx**0, Dx**1, ... (SymPy listofpoly). */
  readonly listofpoly: DMP[];
  /** The variable of the base ring. */
  readonly x: Sym;
  constructor(
    listOfPoly: readonly DifferentialOperand[] | readonly (DMP | ExprLike)[],
    readonly parent: DifferentialOperatorAlgebra,
  ) {
    const base = parent.base;
    this.x = base.gen;
    this.listofpoly = listOfPoly.map((j) => {
      if (j instanceof DMP) return j.ring.equals(base) ? new DMP(j.rep, base) : base.fromSympy(j.toSympy());
      if (j instanceof DifferentialOperator) throw new TypeError('the coefficients of an operator are polynomials');
      return base.fromSympy(sympify(j));
    });
  }
  /** The highest power of `Dx`. */
  get order(): number {
    return this.listofpoly.length - 1;
  }
  private poly(o: DMP | ExprLike): DMP {
    return o instanceof DMP ? o : this.parent.base.fromSympy(sympify(o));
  }
  /** self*other with Dx*a = a*Dx + a' (SymPy __mul__). */
  mul(other: DifferentialOperand): DifferentialOperator {
    const listofself = this.listofpoly;
    let listofother = other instanceof DifferentialOperator ? other.listofpoly : [this.poly(other)];
    const mulDmp = (b: DMP, l: readonly DMP[]): DMP[] => l.map((i) => i.mul(b));
    let sol = mulDmp(first(listofself), listofother);
    // Dx**i * b
    const mulDxB = (b: readonly DMP[]): DMP[] =>
      addLists(
        [this.parent.base.zero, ...b],
        b.map((i) => i.diff()),
      );
    for (const p of listofself.slice(1)) {
      listofother = mulDxB(listofother);
      sol = addLists(sol, mulDmp(p, listofother));
    }
    return new DifferentialOperator(sol, this.parent);
  }
  /** other*self for a polynomial or expression (SymPy __rmul__). */
  rmul(other: DMP | ExprLike): DifferentialOperator {
    const o = this.poly(other);
    return new DifferentialOperator(
      this.listofpoly.map((j) => o.mul(j)),
      this.parent,
    );
  }
  /** self + other (SymPy __add__ and __radd__). */
  add(other: DifferentialOperand): DifferentialOperator {
    if (other instanceof DifferentialOperator) return new DifferentialOperator(addLists(this.listofpoly, other.listofpoly), this.parent);
    return new DifferentialOperator([first(this.listofpoly).add(this.poly(other)), ...this.listofpoly.slice(1)], this.parent);
  }
  /** self - other. */
  sub(other: DifferentialOperand): DifferentialOperator {
    return this.add(other instanceof DifferentialOperator ? other.rmul(-1) : this.poly(other).neg());
  }
  /** other - self. */
  rsub(other: DMP | ExprLike): DifferentialOperator {
    return this.rmul(-1).add(other);
  }
  /** -self. */
  neg(): DifferentialOperator {
    return this.rmul(-1);
  }
  /** self/other for a constant other (SymPy __truediv__). */
  div(other: ExprLike): DifferentialOperator {
    return this.mul(pow(other, -1));
  }
  /** self**n for an integer n >= 0 (SymPy __pow__). */
  pow(nIn: number): DifferentialOperator {
    if (nIn === 1) return this;
    let result = new DifferentialOperator([this.parent.base.one], this.parent);
    if (nIn === 0) return result;
    const base = this.parent.base;
    if (listsEqual(this.listofpoly, this.parent.derivativeOperator.listofpoly)) {
      return new DifferentialOperator([...Array.from({ length: nIn }, () => base.zero), base.one], this.parent);
    }
    let x: DifferentialOperator = this;
    let n = nIn;
    for (;;) {
      if (n % 2) result = result.mul(x);
      n = Math.floor(n / 2);
      if (!n) break;
      x = x.mul(x);
    }
    return result;
  }
  toString(): string {
    let printStr = '';
    const g = str(this.parent.genSymbol);
    for (const [i, j] of this.listofpoly.entries()) {
      if (j.isZero) continue;
      const s = str(j.toSympy());
      if (i === 0) {
        printStr += `(${s})`;
        continue;
      }
      if (printStr) printStr += ' + ';
      printStr += i === 1 ? `(${s})*${g}` : `(${s})*${g}**${i}`;
    }
    return printStr;
  }
  /**
   * Equality with an operator, or with a polynomial or expression (the
   * operator of order 0). SymPy compares the higher coefficients with the
   * zero element by identity, so an operator with zero higher coefficients
   * never equals a polynomial there; here they are compared by value.
   */
  equals(other: DifferentialOperand): boolean {
    if (other instanceof DifferentialOperator) return listsEqual(this.listofpoly, other.listofpoly) && this.parent.equals(other.parent);
    return first(this.listofpoly).equals(other instanceof DMP ? other : sympify(other)) && this.listofpoly.slice(1).every((p) => p.isZero);
  }
  /** Whether the differential equation is singular at x0 (SymPy is_singular). */
  isSingular(x0: ExprLike): boolean {
    return vanishesAt(last(this.listofpoly).toSympy(), this.x, sympify(x0));
  }
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/** The roots of a polynomial with their multiplicities (empty for a constant). */
function rootsOf(p: Expr, x: Sym): ExprMap<number> {
  return rootsDict(p, x);
}

/**
 * p(x0) = 0: x0 is a root of p (SymPy tests membership in roots(p), which
 * gives the same answer for the roots it finds, and needs radicals for the
 * irreducible factors of higher degree).
 */
function vanishesAt(p: Expr, x: Sym, x0: Expr): boolean {
  const v = expandMul(subs(p, [[x, x0]]));
  return (v instanceof Rational || v instanceof Float) && v.isZero;
}

/** The integer roots of a polynomial (SymPy roots(p, n, filter='Z')): the divisors of the last nonzero coefficient that are roots. */
function integerRoots(p: Expr, n: Sym): Rational[] {
  const cs = defined(polyCoefficients(p, n), 'a polynomial');
  const deg = Math.max(...cs.keys());
  const coeffs = Array.from({ length: deg + 1 }, (_, k) => cs.get(k) ?? S.Zero);
  const rs = coeffs.filter((c): c is Rational => c instanceof Rational);
  if (rs.length < coeffs.length) {
    return [...rootsOf(p, n).keys()].filter((r): r is Rational => r instanceof Rational && r.isInteger);
  }
  let den = 1n;
  for (const r of rs) den = (den / igcd(den, r.q)) * r.q;
  const ints = rs.map((r) => (r.p * den) / r.q);
  const out: Rational[] = [];
  let k = 0;
  while (at(ints, k) === 0n) k++;
  if (k > 0) out.push(Rational.of(0n));
  const value = (t: bigint) => ints.reduceRight((acc, c) => acc * t + c, 0n);
  for (const d of divisors(at(ints, k) < 0n ? -at(ints, k) : at(ints, k))) for (const t of [d, -d]) if (value(t) === 0n) out.push(Rational.of(t));
  return out;
}

/** The roots of a polynomial with float coefficients, as floats. */
function floatRoots(p: Expr, x: Sym): ExprMap<number> {
  const out = new ExprMap<number>();
  for (const [r, m] of rootsOf(p, x)) {
    const v = evalfExpr(r, 15, { chop: true });
    out.set(v, (out.get(v) ?? 0) + m);
  }
  return out;
}

/** A sympy integer (SymPy int_valued): an Integer or an integral Float. */
function intValued(e: Expr): boolean {
  if (e instanceof Rational) return e.isInteger;
  return e instanceof Float && Number.isInteger(e.value);
}

/** The value of a real number for comparisons. */
function realValue(e: Expr): number {
  return evalfExpr(e).toNumber();
}

/** `val.is_finite is False` / `is True` for a value of the algorithms. */
function finiteness(e: Expr): Truth {
  if (e instanceof Special) return false;
  // a number without symbols is finite unless it is an infinity (which evaluates to a Special)
  if (freeSymbols(e).size === 0) return true;
  return ask(Q.finite(e));
}

const isNaN = (e: Expr): boolean => e instanceof Special && e.name === 'nan';

/** Ordinary (list) or singular (map from the exponent to the series coefficients) initial conditions. */
export type InitialConditions = Expr[] | ExprMap<Expr[]>;

/** Initial conditions as given by the user: a list of values or a map exponent -> series coefficients. */
export type InitialConditionsLike = readonly ExprLike[] | ReadonlyMap<ExprLike, readonly ExprLike[]>;

const isIcsList = (y0: InitialConditionsLike): y0 is readonly ExprLike[] => Array.isArray(y0);

function toIcs(y0: InitialConditionsLike | undefined): InitialConditions | undefined {
  if (y0 === undefined) return undefined;
  if (isIcsList(y0)) return y0.map((u) => sympify(u));
  const m = new ExprMap<Expr[]>();
  for (const [k, v] of y0) m.set(sympify(k), v.map((u) => sympify(u)));
  return m;
}

/** An element of a container as SymPy's sstr prints it: a Float loses its trailing zeros. */
const strElem = (e: Expr): string => (e instanceof Float ? floatString(e, true) : str(e));

/** The initial conditions as SymPy's sstr of a list or dict prints them. */
function strIcs(y0: InitialConditions): string {
  const list = (l: readonly Expr[]) => `[${l.map(strElem).join(', ')}]`;
  if (!(y0 instanceof ExprMap)) return list(y0);
  const keys = [...y0.keys()].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  return `{${keys.map((k) => `${strElem(k)}: ${list(getOrThrow(y0, k))}`).join(', ')}}`;
}

const zeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;
const intE = (n: number): Rational => Rational.of(BigInt(n));

/** The reduced row echelon form of a matrix over K(x) and its pivot columns. */
function rref(rowsIn: readonly (readonly DMF[])[], ncols: number): [DMF[][], number[]] {
  const rows = rowsIn.map((r) => [...r]);
  const pivots: number[] = [];
  for (let c = 0; c < ncols && pivots.length < rows.length; c++) {
    const r = pivots.length;
    const p = rows.findIndex((row, i) => i >= r && !at(row, c).isZero);
    if (p < 0) continue;
    [rows[r], rows[p]] = [at(rows, p), at(rows, r)];
    const pr = at(rows, r);
    const pv = at(pr, c);
    for (let j = 0; j < ncols; j++) pr[j] = at(pr, j).div(pv);
    for (const [i, row] of rows.entries()) {
      const f = at(row, c);
      if (i !== r) for (let j = 0; j < ncols; j++) row[j] = at(row, j).sub(f.mul(at(pr, j)));
    }
    pivots.push(c);
  }
  return [rows, pivots];
}

/** The nullspace vectors of the free columns (the free variable 1, the others 0). */
function nullVectors(K: OldFractionField, rowsIn: readonly (readonly DMF[])[], ncols: number): DMF[][] {
  const [rows, pivots] = rref(rowsIn, ncols);
  const out: DMF[][] = [];
  for (let c = 0; c < ncols; c++) {
    if (pivots.includes(c)) continue;
    const v: DMF[] = Array.from({ length: ncols }, () => K.zero);
    v[c] = K.one;
    for (const [ip, p] of pivots.entries()) v[p] = at(at(rows, ip), c).neg();
    out.push(v);
  }
  return out;
}

/** The sum of the nullspace basis vectors, zero when there is none (SymPy _find_nonzero_solution). */
function findNonzeroSolution(K: OldFractionField, rows: readonly (readonly DMF[])[], ncols: number): DMF[] {
  return nullVectors(K, rows, ncols).reduce(
    (acc, v) => acc.map((u, i) => u.add(at(v, i))),
    Array.from({ length: ncols }, () => K.zero),
  );
}

/** Normalize an annihilator: clear the denominators and the common factor of the coefficients (SymPy _normalize). */
function normalize(listOf: readonly (DMF | DMP)[], parent: DifferentialOperatorAlgebra, negative = true): DifferentialOperator {
  const base = parent.base;
  const K = base.getField();
  const listOfCoeff = listOf.map((j) => (j instanceof DMP ? K.new(j) : j));
  const num = listOfCoeff.map((c) => c.numer());
  const denom = listOfCoeff.map((c) => c.denom());
  let lcmDenom = base.one;
  for (const i of denom) lcmDenom = i.lcm(lcmDenom);
  if (negative) lcmDenom = lcmDenom.neg();
  const lcmK = K.new(lcmDenom);
  const scaled = listOfCoeff.map((j) => j.mul(lcmK));
  const lastC = last(scaled);
  let gcdNumer = lastC.numer().exquo(lastC.denom());
  for (const i of num) gcdNumer = i.gcd(gcdNumer);
  const gcdK = K.new(gcdNumer);
  return new DifferentialOperator(
    scaled.map((j) => {
      const f = j.div(gcdK);
      return f.numer().exquo(f.denom());
    }),
    parent,
  );
}

/** The coefficients of the equation obtained by differentiating a0*y + a1*y' + ... = 0 (SymPy _derivate_diff_eq). */
function derivateDiffEq(listofpoly: readonly DMF[]): DMF[] {
  const sol = [first(listofpoly).diff()];
  for (const [i, j] of listofpoly.slice(1).entries()) sol.push(j.diff().add(at(listofpoly, i)));
  sol.push(last(listofpoly));
  return sol;
}

/** p(x0)/q(x0) for a fraction p/q (SymPy DMFsubs). */
export function DMFsubs(frac: DMF, x0In: ExprLike): Expr {
  const x0 = sympify(x0In);
  const dom = frac.field.dom;
  const value = (p: DMP): Expr => {
    if (dom.symbols.length && x0 instanceof Rational) {
      let s = dom.zero;
      for (const c of p.rep) s = dom.add(dom.mul(s, x0), c);
      return dom.toSympy(s);
    }
    const cs = [...p.rep].reverse();
    return add(...cs.map((c, i) => mul(dom.toSympy(c), pow(x0, i))));
  };
  return mul(value(frac.num), pow(value(frac.den), -1));
}

/** More initial conditions from the differential equation at the point (SymPy _extend_y0). */
function extendY0(h: HolonomicFunction, n: number): InitialConditions | undefined {
  const y0 = h.y0;
  if (h.annihilator.isSingular(h.x0) || y0 instanceof ExprMap) return y0;
  const annihilator = h.annihilator;
  const a = annihilator.order;
  const K = annihilator.parent.base.getField();
  const listofpoly = annihilator.listofpoly.map((j) => K.new(j));
  const ys = y0 ?? [];
  if (ys.length < a || n <= ys.length) return y0;
  let listRed = listofpoly.slice(0, a).map((p) => p.neg().div(at(listofpoly, a)));
  const y1 = ys.slice(0, Math.min(ys.length, a));
  for (let k = 0; k < n - a; k++) {
    let sol: Expr = S.Zero;
    for (const [i, b] of listRed.entries()) {
      const r = DMFsubs(b, h.x0);
      if (finiteness(r) !== true) return y0;
      sol = add(sol, mul(at(y1, i), r));
    }
    y1.push(sol);
    listRed = derivateDiffEq(listRed);
  }
  return [...ys, ...y1.slice(ys.length)];
}

/** extendY0 for a function with ordinary initial conditions. */
function extendList(h: HolonomicFunction, n: number): Expr[] {
  const y = extendY0(h, n);
  return y instanceof ExprMap ? [] : (y ?? []);
}

/** [f(x0), f'(x0), ...] of an expression, or undefined when a value is not finite (SymPy _find_conditions). */
function findConditions(funcIn: Expr, x: Sym, x0: Expr, order: number, evalf = false, useLimit = true): Expr[] | undefined {
  let func = funcIn;
  const y0: Expr[] = [];
  for (let k = 0; k < order; k++) {
    let val = subs(func, [[x, x0]]);
    if (evalf) val = evalfExpr(val);
    if (useLimit && isNaN(val)) val = limit(func, x, x0);
    if (finiteness(val) === false || isNaN(val)) return undefined;
    y0.push(val);
    func = diffExpr(func, x);
  }
  return y0;
}

/** Conditions found at x0, x0 + 1, ... (the first point where they exist). */
function findConditionsFrom(func: Expr, x: Sym, x0In: Expr, order: number, evalf = false, useLimit = true): [Expr, Expr[]] {
  let x0 = x0In;
  let y0 = findConditions(func, x, x0, order, evalf, useLimit);
  while (!y0?.length) {
    x0 = add(x0, 1);
    y0 = findConditions(func, x, x0, order, evalf, useLimit);
  }
  return [x0, y0];
}

/** h.to_expr(), or undefined when there is no power series or no hypergeometric one (SymPy catches NotHyperSeriesError and NotPowerSeriesError). */
function tryToExpr(h: HolonomicFunction): Expr | undefined {
  try {
    return h.toExpr();
  } catch (e) {
    if (e instanceof SeriesExpansionError) return undefined;
    throw e;
  }
}

/** SymPy hyper -> meijerg conversion (_hyper_to_meijerg). */
function hyperToMeijerg(func: Hyper): Expr {
  const ap = func.ap;
  const bq = func.bq;
  if (ap.some((i) => i instanceof Rational && i.isInteger && i.p <= 0n)) return hyperexpand(func);
  const z = func.argument;
  let k: Expr = S.One;
  for (const i of bq) k = mul(k, gamma(i));
  for (const i of ap) k = mul(k, pow(gamma(i), -1));
  return mul(
    k,
    meijerg(
      ap.map((i) => add(1, neg(i))),
      [],
      [S.Zero],
      bq.map((i) => add(1, neg(i))),
      neg(z),
    ),
  );
}

/** SymPy solve(eqs, *unknowns) for the linear systems of to_sequence: the solved unknowns, or undefined for SymPy's list result. @internal */
export function solveLinear(eqs: readonly Expr[], unknowns: readonly Sym[]): ExprMap<Expr> | undefined {
  const nonzero = eqs.filter((e) => !zeroE(e));
  if (!nonzero.length || !unknowns.length) return undefined;
  const r = linsolve(nonzero, unknowns);
  if (!Array.isArray(r)) return undefined;
  const out = new ExprMap<Expr>();
  for (const [i, s] of unknowns.entries()) {
    const v = at(r, i);
    if (v.key !== s.key) out.set(s, v);
  }
  return out;
}

/** rf(a, k) for an integer k >= 0 as SymPy evaluates it: (a)*(a + 1)*... */
function risingFactorial(a: Expr, k: number): Expr {
  let r: Expr = S.One;
  for (let i = 0; i < k; i++) r = mul(r, add(a, i));
  return r;
}

/** A dict keyed by integer pairs, in insertion order. */
class PairDict {
  readonly keys: [number, number][] = [];
  readonly values = new Map<string, Expr>();
  add(k: [number, number], v: Expr): void {
    const s = k.join(',');
    const old = this.values.get(s);
    if (old === undefined) this.keys.push(k);
    this.values.set(s, old === undefined ? v : add(old, v));
  }
  get(k: readonly [number, number]): Expr {
    return defined(this.values.get(k.join(',')), 'recurrence term');
  }
}

/** Options of HolonomicFunction.evalf: the method (RK4 by default) and the step for a single point. */
export interface EvalfOptions {
  method?: 'RK4' | 'Euler';
  h?: number;
}

const isLimits = (l: Sym | readonly [Sym, ExprLike, ExprLike]): l is readonly [Sym, ExprLike, ExprLike] => Array.isArray(l);

const isPointList = (p: ExprLike | readonly ExprLike[]): p is readonly ExprLike[] => Array.isArray(p);

/** A term of HolonomicFunction.toHyper(true): [c*x**k] or [c*x**k, hyper(...)]. */
export type HyperTerm = [Expr] | [Expr, Expr];

/** A recurrence with its exponent and the n from which it holds. */
interface Recur {
  seq: HolonomicSequence;
  p: Expr;
  n0: number;
  /** At a regular singular point (a root p of the indicial equation). */
  singular: boolean;
}


/** One recurrence of HolonomicFunction.toSequence: (sequence, n0), (sequence, p, n0), or without n0 when lb is false. */
export type SequenceSolution = HolonomicSequence | [HolonomicSequence, number] | [HolonomicSequence, Expr] | [HolonomicSequence, Expr, number];

/** The initial values of a recurrence by the series method (part of SymPy to_sequence and _frobenius). */
function seriesConditions(
  dict1: PairDict,
  u0In: readonly Expr[],
  order: number,
  range: [number, number],
  letter: string,
): [Expr[], boolean] {
  const u0 = [...u0In];
  const dummys = new Map<number, Expr>();
  const eqs: Expr[] = [];
  const unknowns: Sym[] = [];
  const n = (k: [number, number], i: number) => subs(dict1.get(k), [[nSym, intE(i)]]);
  for (let i = range[0]; i < range[1]; i++) {
    let eq: Expr = S.Zero;
    for (const j of dict1.keys) {
      const t = i + j[0];
      if (t < 0) dummys.set(t, S.Zero);
      else if (t < u0.length) dummys.set(t, at(u0, t));
      else if (!dummys.has(t)) {
        const s = new Sym(`${letter}_${t}`);
        dummys.set(t, s);
        unknowns.push(s);
      }
      if (j[1] <= i) eq = add(eq, mul(n(j, i), defined(dummys.get(t), 'dummy')));
    }
    eqs.push(eq);
  }
  const soleqs = solveLinear(eqs, unknowns);
  for (let i = u0.length; i < order; i++) {
    if (!dummys.has(i)) dummys.set(i, new Sym(`${letter}_${i}`));
    const d = defined(dummys.get(i), 'dummy');
    u0.push(soleqs?.get(d) ?? d);
  }
  return [u0, soleqs !== undefined];
}

/** The integer variable of the recurrences. */
const nSym = new Sym('n', { integer: true });

/** The recurrence of the series coefficients from the terms of the annihilator (part of SymPy to_sequence and _frobenius). */
function recurrenceFrom(dict1: PairDict, dom: Domain): [RecurrenceOperator, number, number] {
  const [R] = RecurrenceOperators(dom.oldPolyRing(nSym), 'Sn');
  const keylist = dict1.keys.map((k) => k[0]);
  const lower = Math.min(...keylist);
  const upper = Math.max(...keylist);
  const sol: Expr[] = [];
  for (let j = lower; j <= upper; j++) {
    const terms = dict1.keys.filter((k) => k[0] === j).map((k) => subs(dict1.get(k), [[nSym, add(nSym, -lower)]]));
    sol.push(add(...terms));
  }
  const rec = new RecurrenceOperator(sol, R);
  const intRoots = integerRoots(last(rec.listofpoly).toSympy(), nSym);
  const maxRoot = intRoots.length ? Math.max(...intRoots.map((r) => Number(r.p))) + 1 : -Infinity;
  return [rec, lower, maxRoot];
}

// ---------------------------------------------------------------------------
// holonomic functions
// ---------------------------------------------------------------------------

/**
 * A holonomic function: a solution of L.f = 0 for an annihilator L (a
 * DifferentialOperator) with optional initial conditions at x0, either the
 * values [f(x0), f'(x0), ...] at an ordinary point or, at a regular singular
 * point, a map from the roots of the indicial equation to the first series
 * coefficients (SymPy HolonomicFunction).
 */
export class HolonomicFunction {
  /** The initial conditions (SymPy y0), undefined when none are given. */
  y0: InitialConditions | undefined;
  /** The point of the initial conditions. */
  x0: Expr;
  constructor(
    readonly annihilator: DifferentialOperator,
    readonly x: Sym,
    x0: ExprLike = 0,
    y0?: InitialConditionsLike,
  ) {
    this.x0 = sympify(x0);
    this.y0 = toIcs(y0);
  }
  toString(): string {
    if (this.haveInitCond()) return `HolonomicFunction(${this.annihilator.toString()}, ${str(this.x)}, ${str(this.x0)}, ${strIcs(defined(this.y0))})`;
    return `HolonomicFunction(${this.annihilator.toString()}, ${str(this.x)})`;
  }
  /** The two functions over a common base ring (SymPy unify). */
  unify(other: HolonomicFunction): [HolonomicFunction, HolonomicFunction] {
    const R1 = this.annihilator.parent.base;
    const R2 = other.annihilator.parent.base;
    if (R1.equals(R2)) return [this, other];
    const R = R1.dom.unify(R2.dom).oldPolyRing(this.x);
    const [newparent] = DifferentialOperators(R, str(this.annihilator.parent.genSymbol));
    const sol1 = new DifferentialOperator(
      this.annihilator.listofpoly.map((i) => i.toSympy()),
      newparent,
    );
    const sol2 = new DifferentialOperator(
      other.annihilator.listofpoly.map((i) => i.toSympy()),
      newparent,
    );
    return [new HolonomicFunction(sol1, this.x, this.x0, this.y0), new HolonomicFunction(sol2, other.x, other.x0, other.y0)];
  }
  /** Whether the initial conditions are singular (a map): true, false for a list, 'unknown' without initial conditions (SymPy is_singularics, None). */
  isSingularics(): Truth {
    if (this.y0 === undefined) return 'unknown';
    return this.y0 instanceof ExprMap;
  }
  /** Whether initial conditions are given (SymPy _have_init_cond). */
  haveInitCond(): boolean {
    return this.y0 !== undefined && (this.y0 instanceof ExprMap ? this.y0.size > 0 : this.y0.length > 0);
  }
  private ordinary(): boolean {
    return Array.isArray(this.y0);
  }
  /** Singular initial conditions as ordinary ones when the only exponent is a positive integer (SymPy _singularics_to_ord). */
  private singularicsToOrd(y0: ExprMap<Expr[]>): HolonomicFunction | undefined {
    const [a, b] = first([...y0.entries()]);
    if (y0.size === 1 && a instanceof Rational && a.isInteger && a.p > 0n) {
      const k = Number(a.p);
      const ys = [...Array.from({ length: k }, () => S.Zero), ...b.map((j, i) => mul(j, factorial(k + i)))];
      return new HolonomicFunction(this.annihilator, this.x, this.x0, ys);
    }
    return undefined;
  }
  /** self + other (SymPy __add__). */
  add(other: HolonomicFunction): HolonomicFunction {
    if (!this.annihilator.parent.base.equals(other.annihilator.parent.base)) {
      const [a, b] = this.unify(other);
      return a.add(b);
    }
    const deg1 = this.annihilator.order;
    const deg2 = other.annihilator.order;
    let dim = Math.max(deg1, deg2);
    const K = this.annihilator.parent.base.getField();
    const rowsself = [this.annihilator];
    const rowsother = [other.annihilator];
    const gen = this.annihilator.parent.derivativeOperator;
    for (let i = 0; i < dim - deg1; i++) rowsself.push(gen.mul(last(rowsself)));
    for (let i = 0; i < dim - deg2; i++) rowsother.push(gen.mul(last(rowsother)));
    const solve = (): DMF[] => {
      const row = [...rowsself, ...rowsother];
      // the transposed matrix of the ansatz
      const r: DMF[][] = [];
      for (let i = 0; i <= dim; i++) r.push(row.map((e) => (i >= e.listofpoly.length ? K.zero : K.new(at(e.listofpoly, i)))));
      return findNonzeroSolution(K, r, row.length);
    };
    let sol = solve();
    while (sol.every((s) => s.isZero)) {
      dim += 1;
      rowsself.push(gen.mul(last(rowsself)));
      rowsother.push(gen.mul(last(rowsother)));
      sol = solve();
    }
    const sol1 = normalize(sol.slice(0, dim + 1 - deg1), this.annihilator.parent);
    const ann = normalize(sol1.mul(this.annihilator).listofpoly, this.annihilator.parent, false);
    if (!(this.haveInitCond() && other.haveInitCond())) return new HolonomicFunction(ann, this.x);
    if (this.ordinary() && other.ordinary()) {
      if (this.x0.key === other.x0.key) {
        const y1 = extendList(this, ann.order);
        const y2 = extendList(other, ann.order);
        const n = Math.min(y1.length, y2.length);
        return new HolonomicFunction(
          ann,
          this.x,
          this.x0,
          y1.slice(0, n).map((a, i) => add(a, at(y2, i))),
        );
      }
      const selfat0 = this.annihilator.isSingular(0);
      const otherat0 = other.annihilator.isSingular(0);
      if (zeroE(this.x0) && !selfat0 && !otherat0) return this.add(other.changeIcs(0));
      if (zeroE(other.x0) && !selfat0 && !otherat0) return this.changeIcs(0).add(other);
      const selfatx0 = this.annihilator.isSingular(this.x0);
      const otheratx0 = other.annihilator.isSingular(this.x0);
      if (!selfatx0 && !otheratx0) return this.add(other.changeIcs(this.x0));
      return this.changeIcs(other.x0).add(other);
    }
    if (this.x0.key !== other.x0.key) return new HolonomicFunction(ann, this.x);
    const [y1, y2] = this.singularPair(other);
    const y0 = new ExprMap<Expr[]>();
    for (const [i, c] of y1) {
      const d = y2.get(i);
      y0.set(i, d ? c.slice(0, Math.min(c.length, d.length)).map((a, k) => add(a, at(d, k))) : c);
    }
    for (const [i, c] of y2) if (!y1.has(i)) y0.set(i, c);
    return new HolonomicFunction(ann, this.x, this.x0, y0);
  }
  /** The initial conditions of two functions as singular ones (ordinary conditions converted to series coefficients). */
  private singularPair(other: HolonomicFunction): [ExprMap<Expr[]>, ExprMap<Expr[]>] {
    const conv = (h: HolonomicFunction): ExprMap<Expr[]> => {
      const ys = defined(h.y0, 'initial conditions');
      if (ys instanceof ExprMap) return ys;
      return new ExprMap([[S.Zero, ys.map((j, i) => mul(j, pow(factorial(i), -1)))]]);
    };
    return [conv(this), conv(other)];
  }
  /**
   * The integral (SymPy integrate): an indefinite integral for a symbol, a
   * function for limits (x, a, x) and a value for limits (x, a, b) with a
   * number b. With `initcond` an indefinite integral without initial
   * conditions gets the condition 0 at x0.
   */
  integrate(limits: Sym | readonly [Sym, ExprLike, ExprLike], initcond = false): HolonomicFunction | Expr {
    const D = this.annihilator.parent.derivativeOperator;
    const annD = this.annihilator.mul(D);
    if (this.y0 instanceof ExprMap) {
      const r = this.singularicsToOrd(this.y0);
      if (r) return r.integrate(limits, initcond);
      const y0 = new ExprMap<Expr[]>();
      for (const [i, c] of this.y0) {
        const c2: Expr[] = [];
        for (const [j, cj] of c.entries()) {
          if (zeroE(cj)) c2.push(S.Zero);
          else if (zeroE(add(i, j + 1))) throw new NotImplementedError('logarithmic terms in the series are not supported');
          else c2.push(mul(cj, pow(add(i, j + 1), -1)));
        }
        y0.set(add(i, 1), c2);
      }
      if (isLimits(limits)) throw new NotImplementedError('Definite integration for singular initial conditions');
      return new HolonomicFunction(annD, this.x, this.x0, y0);
    }
    if (!this.haveInitCond()) {
      if (initcond) return new HolonomicFunction(annD, this.x, this.x0, [S.Zero]);
      return new HolonomicFunction(annD, this.x);
    }
    const y0 = [S.Zero, ...extendList(this, 0)];
    const indefinite = new HolonomicFunction(annD, this.x, this.x0, y0);
    if (!isLimits(limits)) return indefinite;
    const [lx, aIn, bIn] = limits;
    if (lx.key !== this.x.key) return indefinite;
    const a = sympify(aIn);
    const b = sympify(bIn);
    const atPoint = (e: Expr, p: Expr): Expr => {
      const v = subs(e, [[this.x, p]]);
      return isNaN(v) ? limit(e, this.x, p) : v;
    };
    if (this.x0.key !== a.key) {
      const indefiniteExpr = tryToExpr(indefinite);
      const lower = indefiniteExpr ? atPoint(indefiniteExpr, a) : indefinite.evalfAt(a);
      if (b.key === this.x.key) {
        y0[0] = add(first(y0), neg(lower));
        return new HolonomicFunction(annD, this.x, this.x0, y0);
      }
      if (b.isNumber) {
        const upper = indefiniteExpr ? atPoint(indefiniteExpr, b) : indefinite.evalfAt(b);
        return add(upper, neg(lower));
      }
    }
    if (b.key === this.x.key) return new HolonomicFunction(annD, this.x, a, y0);
    if (b.isNumber) {
      const h = new HolonomicFunction(annD, this.x, a, y0);
      const s = tryToExpr(h);
      return s ? atPoint(s, b) : h.evalfAt(b);
    }
    return new HolonomicFunction(annD, this.x);
  }
  /**
   * The derivative (SymPy diff): diff() or diff(x) once, diff(x, n) n times;
   * 0 for another variable.
   */
  diff(x?: Expr, n?: number): HolonomicFunction | Expr {
    if (x !== undefined) {
      if (x.key !== this.x.key) return S.Zero;
      if (n !== undefined) {
        let sol: HolonomicFunction | Expr = this;
        for (let i = 0; i < n; i++) sol = sol instanceof HolonomicFunction ? sol.diff(x) : S.Zero;
        return sol;
      }
    }
    const ann = this.annihilator;
    if (first(ann.listofpoly).isZero && ann.order === 1) return S.Zero;
    if (first(ann.listofpoly).isZero) {
      const sol = new DifferentialOperator(ann.listofpoly.slice(1), ann.parent);
      const ys = this.y0;
      if (Array.isArray(ys) && this.haveInitCond()) return new HolonomicFunction(sol, this.x, this.x0, ys.slice(1));
      return new HolonomicFunction(sol, this.x);
    }
    const K = ann.parent.base.getField();
    const seqDmf = ann.listofpoly.map((i) => K.new(i));
    const rhs = [K.zero, ...seqDmf.slice(1).map((i) => i.div(first(seqDmf)))];
    let sol = derivateDiffEq(rhs);
    sol = addLists(sol, [K.zero, K.one]);
    const solAnn = normalize(sol.slice(1), this.annihilator.parent, false);
    if (!this.haveInitCond() || this.isSingularics() === true) return new HolonomicFunction(solAnn, this.x);
    const y0 = extendList(this, solAnn.order + 1).slice(1);
    return new HolonomicFunction(solAnn, this.x, this.x0, y0);
  }
  /** Equal annihilators and variables, and equal initial conditions when both have them (SymPy __eq__). */
  equals(other: HolonomicFunction): boolean {
    if (!this.annihilator.equals(other.annihilator) || this.x.key !== other.x.key) return false;
    if (this.haveInitCond() && other.haveInitCond()) return this.x0.key === other.x0.key && icsEqual(defined(this.y0), defined(other.y0));
    return true;
  }
  /**
   * self*other for a holonomic function or a constant (SymPy __mul__ and
   * __rmul__). SymPy fails on a constant factor of a function with initial
   * conditions (it builds a Poly from each value); here the values are
   * multiplied by the constant.
   */
  mul(otherIn: HolonomicFunction | ExprLike): HolonomicFunction {
    const annSelf = this.annihilator;
    if (!(otherIn instanceof HolonomicFunction)) {
      const other = sympify(otherIn);
      if (other.has(this.x)) throw new NotImplementedError(" Can't multiply a HolonomicFunction and expressions/functions.");
      if (!this.haveInitCond()) return this;
      if (this.y0 instanceof ExprMap) {
        const m = new ExprMap<Expr[]>();
        for (const [k, v] of this.y0) m.set(k, v.map((j) => mul(j, other)));
        return new HolonomicFunction(annSelf, this.x, this.x0, m);
      }
      const y0 = extendList(this, annSelf.order);
      return new HolonomicFunction(
        annSelf,
        this.x,
        this.x0,
        y0.map((j) => mul(j, other)),
      );
    }
    const other = otherIn;
    if (!this.annihilator.parent.base.equals(other.annihilator.parent.base)) {
      const [a, b] = this.unify(other);
      return a.mul(b);
    }
    const annOther = other.annihilator;
    const a = annSelf.order;
    const b = annOther.order;
    const K = annSelf.parent.base.getField();
    const listSelf = annSelf.listofpoly.map((j) => K.new(j));
    const listOther = annOther.listofpoly.map((j) => K.new(j));
    const selfRed = listSelf.slice(0, a).map((p) => p.neg().div(at(listSelf, a)));
    const otherRed = listOther.slice(0, b).map((p) => p.neg().div(at(listOther, b)));
    // coeffMul[i][j] is the coefficient of Dx^i(f).Dx^j(g)
    const coeffMul: DMF[][] = Array.from({ length: a + 1 }, () => Array.from({ length: b + 1 }, () => K.zero));
    at(coeffMul, 0)[0] = K.one;
    const flat = (): DMF[] => {
      const out: DMF[] = [];
      for (let i = 0; i < a; i++) for (let j = 0; j < b; j++) out.push(at(at(coeffMul, i), j));
      return out;
    };
    const linSysElements = [flat()];
    const solve = () => {
      const r: DMF[][] = [];
      for (let k = 0; k < a * b; k++) r.push(linSysElements.map((e) => at(e, k)));
      return findNonzeroSolution(K, r, linSysElements.length);
    };
    let sol = solve();
    while (sol.every((s) => s.isZero)) {
      for (let i = a - 1; i >= 0; i--) {
        for (let j = b - 1; j >= 0; j--) {
          const ci = at(coeffMul, i);
          const cij = at(ci, j);
          ci[j + 1] = at(ci, j + 1).add(cij);
          at(coeffMul, i + 1)[j] = at(at(coeffMul, i + 1), j).add(cij);
          ci[j] = cij.diff();
        }
      }
      for (let i = 0; i <= a; i++) {
        const ci = at(coeffMul, i);
        if (at(ci, b).isZero) continue;
        for (let j = 0; j < b; j++) ci[j] = at(ci, j).add(at(otherRed, j).mul(at(ci, b)));
        ci[b] = K.zero;
      }
      const ca = at(coeffMul, a);
      for (let j = 0; j < b; j++) {
        if (at(ca, j).isZero) continue;
        for (let i = 0; i < a; i++) at(coeffMul, i)[j] = at(at(coeffMul, i), j).add(at(selfRed, i).mul(at(ca, j)));
        ca[j] = K.zero;
      }
      linSysElements.push(flat());
      sol = solve();
    }
    const solAnn = normalize(sol, this.annihilator.parent, false);
    if (!(this.haveInitCond() && other.haveInitCond())) return new HolonomicFunction(solAnn, this.x);
    if (this.ordinary() && other.ordinary()) {
      if (this.x0.key === other.x0.key) {
        const y0Self = extendList(this, solAnn.order);
        const y0Other = extendList(other, solAnn.order);
        const y0 = [mul(first(y0Self), first(y0Other))];
        for (let i = 1; i < Math.min(y0Self.length, y0Other.length); i++) {
          let s: Expr = S.Zero;
          for (let j = 0; j <= i; j++) s = add(s, mul(binomial(i, j), at(y0Self, j), at(y0Other, i - j)));
          y0.push(s);
        }
        return new HolonomicFunction(solAnn, this.x, this.x0, y0);
      }
      const selfat0 = this.annihilator.isSingular(0);
      const otherat0 = other.annihilator.isSingular(0);
      if (zeroE(this.x0) && !selfat0 && !otherat0) return this.mul(other.changeIcs(0));
      if (zeroE(other.x0) && !selfat0 && !otherat0) return this.changeIcs(0).mul(other);
      const selfatx0 = this.annihilator.isSingular(this.x0);
      const otheratx0 = other.annihilator.isSingular(this.x0);
      if (!selfatx0 && !otheratx0) return this.mul(other.changeIcs(this.x0));
      return this.changeIcs(other.x0).mul(other);
    }
    if (this.x0.key !== other.x0.key) return new HolonomicFunction(solAnn, this.x);
    const [y1, y2] = this.singularPair(other);
    const y0 = new ExprMap<Expr[]>();
    for (const [i, ci] of y1) {
      for (const [j, cj] of y2) {
        const k = Math.min(ci.length, cj.length);
        const c: Expr[] = [];
        for (let p = 0; p < k; p++) {
          let s: Expr = S.Zero;
          for (let q = 0; q <= p; q++) s = add(s, mul(at(ci, q), at(cj, p - q)));
          c.push(s);
        }
        const key = add(i, j);
        const old = y0.get(key);
        y0.set(key, old ? c.slice(0, Math.min(c.length, old.length)).map((u, t) => add(u, at(old, t))) : c);
      }
    }
    return new HolonomicFunction(solAnn, this.x, this.x0, y0);
  }
  /** self - other (SymPy __sub__). */
  sub(other: HolonomicFunction): HolonomicFunction {
    return this.add(other.mul(-1));
  }
  /** -self (SymPy __neg__). */
  neg(): HolonomicFunction {
    return this.mul(-1);
  }
  /** self/other for a constant other (SymPy __truediv__). */
  div(other: ExprLike): HolonomicFunction {
    return this.mul(pow(other, -1));
  }
  /**
   * self**n (SymPy __pow__): any exponent (also symbolic) for an annihilator
   * of order 1, otherwise an integer n >= 0.
   */
  pow(nIn: ExprLike): HolonomicFunction {
    const n = sympify(nIn);
    if (this.annihilator.order <= 1) {
      const ann = this.annihilator;
      const parent = ann.parent;
      let y0: InitialConditions | undefined;
      if (this.y0 instanceof ExprMap) {
        // SymPy raises the first exponent to the power; the series c*x**r*(1 + ...) has the power c**n*x**(r*n)*(1 + ...)
        const [r, c] = first([...this.y0.entries()]);
        y0 = new ExprMap([[mul(r, n), [pow(first(c), n)]]]);
      } else if (this.y0 !== undefined) y0 = [pow(first(this.y0), n)];
      const p0 = first(ann.listofpoly).mulGround(n);
      const p1 = at(ann.listofpoly, 1);
      const dd = new DifferentialOperator([p0, p1], parent);
      return new HolonomicFunction(dd, this.x, this.x0, y0);
    }
    const k = n instanceof Rational ? n : undefined;
    if (!k?.isInteger) throw new NotImplementedError('only integer powers of a holonomic function of order > 1');
    if (k.p < 0n) throw new NotHolonomicError('Negative Power on a Holonomic Function');
    const Dx = this.annihilator.parent.derivativeOperator;
    let result = new HolonomicFunction(Dx, this.x, S.Zero, [S.One]);
    if (k.p === 0n) return result;
    let x: HolonomicFunction = this;
    let e = k.p;
    for (;;) {
      if (e % 2n) result = result.mul(x);
      e /= 2n;
      if (!e) break;
      x = x.mul(x);
    }
    return result;
  }
  /** The highest power of x in the annihilator (SymPy degree). */
  degree(): number {
    return Math.max(...this.annihilator.listofpoly.map((i) => i.degree()));
  }
  /**
   * The composition with a rational function (SymPy composition); initial
   * conditions of the result can be given as x0 and y0.
   */
  composition(exprIn: ExprLike, x0?: ExprLike, y0?: InitialConditionsLike): HolonomicFunction {
    const expr = sympify(exprIn);
    const R = this.annihilator.parent;
    const a = this.annihilator.order;
    const base = R.base.getField();
    // SymPy composes with expressions: algebraic coefficients (sqrt(2)*I*x) are computed in EX(x)
    let K = base;
    let e: DMF;
    try {
      e = K.fromSympy(expr);
    } catch {
      // (CoercionFailed: the only error of the conversion)
      K = EX.oldPolyRing(this.x).getField();
      e = K.fromSympy(expr);
    }
    const de = K.fromSympy(diffExpr(expr, this.x));
    // p(expr) for each coefficient
    const atExpr = (p: DMP): DMF => {
      let s = K.zero;
      for (const c of p.rep) s = s.mul(e).add(K.new([K.dom.fromSympy(p.dom.toSympy(c))]));
      return s;
    };
    const listofpoly = this.annihilator.listofpoly;
    const r = atExpr(at(listofpoly, a));
    const subsList = listofpoly.slice(0, a).map((p) => atExpr(p).neg().div(r));
    let coeffs = Array.from({ length: a }, (_, i) => (i === 0 ? K.one : K.zero));
    const system = [coeffs];
    let sol: DMF[];
    for (;;) {
      const next = coeffs.map((p) => p.diff());
      for (let i = 0; i < a - 1; i++) next[i + 1] = at(next, i + 1).add(at(coeffs, i).mul(de));
      for (let i = 0; i < a; i++) next[i] = at(next, i).add(last(coeffs).mul(at(subsList, i)).mul(de));
      coeffs = next;
      system.push(coeffs);
      const rows: DMF[][] = [];
      for (let i = 0; i < a; i++) rows.push(system.map((c) => at(c, i)));
      // SymPy gauss_jordan_solve with the first parameter 1 (the others 0)
      const vs = nullVectors(K, rows, system.length);
      if (vs.length) {
        sol = first(vs);
        break;
      }
    }
    // (SymPy _normalize converts the coefficients to the base field and fails with CoercionFailed outside it)
    const ann = normalize(K === base ? sol : sol.map((c) => base.fromSympy(c.toSympy())), R, false);
    if (x0 !== undefined) return new HolonomicFunction(ann, this.x, x0, y0);
    return new HolonomicFunction(ann, this.x);
  }
  /**
   * The recurrence of the series coefficients about x0 (SymPy to_sequence):
   * [(R, n0)] at an ordinary point, [(R, p, n0), ...] for the roots p of the
   * indicial equation at a regular singular point; n0 is left out when `lb`
   * is false. Unknown initial values are symbols C_j.
   */
  toSequence(lb = true): SequenceSolution[] {
    return this.recurrences().map((r): SequenceSolution => {
      if (r.singular) return lb ? [r.seq, r.p, r.n0] : [r.seq, r.p];
      return lb ? [r.seq, r.n0] : r.seq;
    });
  }
  /** The recurrences of to_sequence with their exponents and starting n. */
  private recurrences(): Recur[] {
    if (!zeroE(this.x0)) return this.shiftX(this.x0).recurrences();
    if (this.annihilator.isSingular(this.x0)) return this.frobenius();
    const dict1 = new PairDict();
    const dom = this.annihilator.parent.base.dom;
    for (const [i, j] of this.annihilator.listofpoly.entries()) {
      const listofdmp = j.allCoeffs();
      const degree = listofdmp.length - 1;
      for (let k = 0; k <= degree; k++) {
        const coeff = at(listofdmp, degree - k);
        if (dom.isZero(coeff)) continue;
        dict1.add([i - k, k], mul(dom.toSympy(coeff), risingFactorial(add(nSym, -k + 1), i)));
      }
    }
    const [sol, lower, maxRoot] = recurrenceFrom(dict1, dom);
    const degree = this.degree();
    const smallestN = Math.max(maxRoot, lower + degree);
    const order = sol.order + smallestN;
    const y0 = extendList(this, order);
    let u0 = y0.map((j, i) => mul(j, pow(factorial(i), -1)));
    if (u0.length < order) [u0] = seriesConditions(dict1, u0, order, [0, degree], 'C');
    return [{ seq: new HolonomicSequence(sol, u0), p: S.Zero, n0: smallestN, singular: false }];
  }
  /** The recurrences at a regular singular point (SymPy _frobenius). */
  private frobenius(): Recur[] {
    const indicialroots = this.indicial();
    const reals: Expr[] = [];
    const compl: [Expr, number, number][] = [];
    for (const i of ordered([...indicialroots.keys()])) {
      const m = getOrThrow(indicialroots, i);
      if (isRealNumber(i)) for (let k = 0; k < m; k++) reals.push(i);
      else {
        const [re, im] = asRealImag(i);
        for (let k = 0; k < m; k++) compl.push([i, realValue(re), realValue(im)]);
      }
    }
    compl.sort((u, v) => u[1] - v[1]);
    compl.sort((u, v) => u[2] - v[2]);
    reals.sort((u, v) => realValue(u) - realValue(v));
    const grp: Expr[][] = [];
    for (const i of reals) {
      const g = grp.find((j) => intValued(add(first(j), neg(i))));
      if (g) g.push(i);
      else grp.push([i]);
    }
    const independent = grp.every((i) => i.length === 1);
    const allpos = reals.every((i) => realValue(i) >= 0);
    const allint = reals.every(intValued);
    // (reals is sorted)
    const minOf = (l: readonly Expr[]): Expr => first(l);
    let rootstoconsider: Expr[];
    if (this.y0 instanceof ExprMap) {
      rootstoconsider = [];
      for (const i of ordered([...this.y0.keys()])) for (const j of ordered([...indicialroots.keys()])) if (equalValued(j, i)) rootstoconsider.push(i);
    } else if (allpos && allint) rootstoconsider = [minOf(reals)];
    else if (independent) rootstoconsider = [...grp.map((i) => first(i)), ...compl.map((j) => j[0])];
    else if (!allint) rootstoconsider = reals.filter((i) => !intValued(i));
    else if (!Array.isArray(this.y0) || !this.haveInitCond() || finiteness(first(this.y0)) === false) rootstoconsider = [minOf(reals)];
    else rootstoconsider = [minOf(reals.filter((i) => realValue(i) >= 0))];
    const dom = this.annihilator.parent.base.dom;
    const finalsol: Recur[] = [];
    let char = 'C'.charCodeAt(0);
    for (const p of rootstoconsider) {
      const dict1 = new PairDict();
      for (const [i, j] of this.annihilator.listofpoly.entries()) {
        const listofdmp = j.allCoeffs();
        const degree = listofdmp.length - 1;
        for (let k = 0; k <= degree; k++) {
          const coeff = at(listofdmp, degree - k);
          if (dom.isZero(coeff)) continue;
          dict1.add([i - k, k - i], mul(dom.toSympy(coeff), risingFactorial(add(nSym, -k + 1, p), i)));
        }
      }
      const [sol, lower, maxRoot] = recurrenceFrom(dict1, dom);
      const degree = Math.max(...dict1.keys.map((i) => i[1]));
      const degree2 = Math.min(...dict1.keys.map((i) => i[1]));
      const smallestN = Math.max(maxRoot, lower + degree);
      const order = sol.order + smallestN;
      let u0: Expr[] = [];
      const pInt = p instanceof Rational ? p : undefined;
      if (this.y0 instanceof ExprMap) u0 = [...getOrThrow(this.y0, p)];
      else if (this.ordinary() && pInt !== undefined && pInt.isInteger && pInt.p >= 0n && rootstoconsider.length === 1) {
        const k = Number(pInt.p);
        const y0 = extendList(this, order + k);
        if (y0.length > k) u0 = y0.slice(k).map((v, i) => mul(v, pow(factorial(i + k), -1)));
      }
      let solved = false;
      if (u0.length < order) [u0, solved] = seriesConditions(dict1, u0, order, [degree2, degree], String.fromCharCode(char));
      const seq = new HolonomicSequence(sol, u0);
      finalsol.push({ seq, p, n0: smallestN, singular: true });
      // SymPy keeps the letter after a system solved for a dict of values
      if (!solved) char += 1;
    }
    return finalsol;
  }
  /**
   * The power series about x0 up to (x - x0)**n (SymPy series); a list of
   * series for several roots of the indicial equation. With `coefficient`
   * the list of coefficients, with `order: false` no O term.
   */
  series(n = 6, opts: { coefficient?: boolean; order?: boolean } = {}): Expr | Expr[] {
    const recs = this.recurrences();
    // SymPy expands each of several series with the default arguments
    if (recs.length !== 1) return recs.map((r) => this.seriesExpr(r, 6, true));
    const r = first(recs);
    return opts.coefficient ? this.seriesCoeffs(r, n) : this.seriesExpr(r, n, opts.order ?? true);
  }
  /** The first coefficients of the series of one recurrence. */
  private seriesCoeffs(r: Recur, n: number): Expr[] {
    const rec = r.seq;
    const nn = n - Math.trunc(realValue(r.p));
    const l = rec.u0.length - 1;
    const k = rec.recurrence.order;
    const K = rec.recurrence.parent.base.getField();
    const seq = rec.recurrence.listofpoly.map((j) => K.new(j));
    const sub = seq.slice(0, k).map((s) => s.neg().div(at(seq, k)));
    const sol = [...rec.u0];
    for (let i = l + 1 - k; i < nn - k; i++) {
      let coeff: Expr = S.Zero;
      for (let j = 0; j < k; j++) coeff = add(coeff, mul(DMFsubs(at(sub, j), i), at(sol, i + j)));
      sol.push(coeff);
    }
    return sol;
  }
  /** The series of one recurrence. */
  private seriesExpr(r: Recur, n: number, order: boolean): Expr {
    const x = this.x;
    const t = zeroE(this.x0) ? x : add(x, neg(this.x0));
    const ser = add(...this.seriesCoeffs(r, n).map((j, i) => mul(pow(t, add(i, r.p)), j)));
    // (SymPy substitutes x - x0 for x in the series, which moves the O term to x0)
    return order ? add(ser, O(pow(t, n), x, this.x0)) : ser;
  }
  /** The roots of the indicial equation (SymPy _indicial). */
  indicial(): ExprMap<number> {
    if (!zeroE(this.x0)) return this.shiftX(this.x0).indicial();
    const listCoeff = this.annihilator.listofpoly;
    const R = this.annihilator.parent.base;
    const x = this.x;
    let s = R.zero;
    let y = R.one;
    // the multiplicity of the root 0
    const poleDegree = (p: DMP): number => {
      let k = 0;
      while (k < p.rep.length && R.dom.isZero(at(p.rep, p.rep.length - 1 - k))) k++;
      return k;
    };
    const degree = Math.max(...listCoeff.map((j) => j.degree()));
    const inf = 10 * (Math.max(1, degree) + Math.max(1, this.annihilator.order));
    const deg = (q: DMP): number => (q.isZero ? inf : poleDegree(q));
    const b = Math.min(...listCoeff.map((q, j) => deg(q) - j));
    for (const [i, j] of listCoeff.entries()) {
      const listofdmp = j.allCoeffs();
      const d = listofdmp.length - 1;
      if (i + b >= 0 && i + b <= d) s = s.add(y.mulGround(at(listofdmp, d - i - b)));
      y = y.mul(R.fromSympy(add(x, -i)));
    }
    return rootsOf(s.toSympy(), x);
  }
  /**
   * Numerical values by integration along a path of points (SymPy evalf):
   * RK4 (default) or 'Euler'. For a single point the path goes from x0 in
   * steps of h and the value at the point is returned.
   */
  evalf(point: ExprLike, opts?: EvalfOptions & { derivatives?: false }): Expr;
  evalf(point: ExprLike, opts: EvalfOptions & { derivatives: true }): Expr[];
  evalf(points: readonly ExprLike[], opts?: EvalfOptions & { derivatives?: false }): Expr[];
  evalf(points: readonly ExprLike[], opts: EvalfOptions & { derivatives: true }): Expr[][];
  evalf(points: ExprLike | readonly ExprLike[], opts: EvalfOptions & { derivatives?: boolean } = {}): Expr | Expr[] | Expr[][] {
    const method = opts.method ?? 'RK4';
    const derivatives = opts.derivatives ?? false;
    let h = opts.h ?? 0.05;
    let path: Expr[];
    const single = !isPointList(points);
    let atX0 = false;
    if (!isPointList(points)) {
      const b = sympify(points);
      atX0 = this.x0.key === b.key;
      if (atX0) path = [b];
      else {
        if (!b.isNumber) throw new NotImplementedError('evalf of a holonomic function at a symbolic point');
        const a = this.x0;
        const [av, bv] = [realValue(a), realValue(b)];
        if (av > bv) h = -h;
        const n = Math.trunc((bv - av) / h);
        path = [add(a, new Float(h))];
        for (let i = 0; i < n - 1; i++) path.push(add(last(path), new Float(h)));
      }
    } else path = points.map((p) => sympify(p));
    if (!atX0) {
      const lead = last(this.annihilator.listofpoly).toSympy();
      for (const i of [this.x0, ...path]) if (vanishesAt(lead, this.x, i)) throw new SingularityError(this, i);
    }
    const r = evalfHolonomic(this, path, method);
    if (derivatives) return single ? last(r) : r;
    const values = r.map((v) => first(v));
    return single ? last(values) : values;
  }
  /** evalf at one point (the value). */
  private evalfAt(b: Expr): Expr {
    return this.evalf(b);
  }
  /** The same function of another variable (SymPy change_x). */
  changeX(z: Sym): HolonomicFunction {
    const dom = this.annihilator.parent.base.dom;
    const R = dom.oldPolyRing(z);
    const [parent] = DifferentialOperators(R, 'Dx');
    const sol = new DifferentialOperator(
      this.annihilator.listofpoly.map((j) => new DMP(j.rep, R)),
      parent,
    );
    return new HolonomicFunction(sol, z, this.x0, this.y0);
  }
  /** Substitute x + a for x (SymPy shift_x). */
  shiftX(aIn: ExprLike): HolonomicFunction {
    const a = sympify(aIn);
    const x = this.x;
    const sol = new DifferentialOperator(
      this.annihilator.listofpoly.map((i) => i.shift(a)),
      this.annihilator.parent,
    );
    const x0 = add(this.x0, neg(a));
    if (!this.haveInitCond()) return new HolonomicFunction(sol, x);
    return new HolonomicFunction(sol, x, x0, this.y0);
  }
  /**
   * A hypergeometric function (or a linear combination of them) representing
   * the function (SymPy to_hyper); with `asList` the terms as pairs
   * (coefficient*x**k, hyper) or singletons for polynomial terms.
   */
  toHyper(asList: true): HyperTerm[];
  toHyper(asList?: false): Expr;
  toHyper(asList = false): Expr | HyperTerm[] {
    const recs = this.recurrences();
    const parts = recs.map((r) => this.hyperOf(r, asList));
    if (asList) return parts.flatMap((t) => t[1]);
    return add(...parts.map((t) => t[0]));
  }
  /** to_hyper of one recurrence: the expression and the list of terms. */
  private hyperOf(rr: Recur, asList: boolean): [Expr, HyperTerm[]] {
    const rec = rr.seq;
    const smallestN = rr.n0;
    const constantpower = rr.p;
    const u0 = rec.u0;
    const r = rec.recurrence;
    const x = this.x;
    const x0 = this.x0;
    const shift = (e: Expr): Expr => (zeroE(x0) ? e : subs(e, [[x, add(x, neg(x0))]]));
    const m = r.order;
    if (m === 0) {
      const nonzeroterms = ordered([...rootsOf(first(r.listofpoly).toSympy(), rec.n).keys()].filter(isRealNumber));
      let sol: Expr = S.Zero;
      for (const i of nonzeroterms) {
        if (realValue(i) < 0 || !intValued(i)) continue;
        const k = Math.round(realValue(i));
        // (SymPy uses a symbol C_j for k >= len(u0), which cannot happen: n0 exceeds the integer roots)
        sol = add(sol, mul(at(u0, k), pow(x, k)));
      }
      sol = shift(mul(sol, pow(x, constantpower)));
      return [sol, [[sol]]];
    }
    // (u0 has at least smallestN + m values: to_sequence completes it with symbols C_j)
    if (r.listofpoly.slice(1, -1).some((i) => !i.isZero)) throw new NotHyperSeriesError(this, this.x0);
    const a = first(r.listofpoly);
    const b = last(r.listofpoly);
    const c = neg(mul(a.LC(), pow(m, a.degree()), pow(mul(b.LC(), pow(m, b.degree())), -1)));
    let sol: Expr = S.Zero;
    // over RR the roots are floats (SymPy solves the polynomial with float coefficients)
    const numeric = a.dom.ground === 'RR';
    const arg1 = numeric ? floatRoots(a.toSympy(), rec.n) : rootsOf(a.toSympy(), rec.n);
    const arg2 = numeric ? floatRoots(b.toSympy(), rec.n) : rootsOf(b.toSympy(), rec.n);
    const listofsol: HyperTerm[] = [];
    for (let i = 0; i < smallestN + m; i++) {
      const ui = at(u0, i);
      if (i < smallestN) {
        if (asList) listofsol.push([subs(mul(ui, pow(x, add(i, constantpower))), [[x, add(x, neg(x0))]])]);
        else sol = add(sol, mul(ui, pow(x, i)));
        continue;
      }
      if (zeroE(ui)) continue;
      const ap: Expr[] = [];
      const bq: Expr[] = [];
      for (const k of ordered([...arg1.keys()])) for (let t2 = 0; t2 < getOrThrow(arg1, k); t2++) ap.push(nsimplify(mul(add(i, neg(k)), pow(m, -1))));
      for (const k of ordered([...arg2.keys()])) for (let t2 = 0; t2 < getOrThrow(arg2, k); t2++) bq.push(nsimplify(mul(add(i, neg(k)), pow(m, -1))));
      const one = bq.findIndex((v) => v instanceof Rational && v.isOne);
      if (one >= 0) bq.splice(one, 1);
      else ap.push(S.One);
      const h = hyper(ap, bq, mul(c, pow(x, m)));
      if (asList) listofsol.push([subs(mul(ui, pow(x, add(i, constantpower))), [[x, add(x, neg(x0))]]), subs(h, [[x, add(x, neg(x0))]])]);
      else sol = add(sol, mul(ui, h, pow(x, i)));
    }
    return [shift(mul(sol, pow(x, constantpower))), listofsol];
  }
  /** The function as an expression: hyperexpand of to_hyper, simplified (SymPy to_expr). */
  toExpr(): Expr {
    return simplify(hyperexpand(this.toHyper()));
  }
  /** The same function with initial conditions at b (SymPy change_ics). */
  changeIcs(bIn: ExprLike, lenicsIn?: number): HolonomicFunction {
    const b = sympify(bIn);
    let lenics = lenicsIn;
    const ys = defined(this.y0, 'initial conditions');
    const n = ys instanceof ExprMap ? ys.size : ys.length;
    if (lenics === undefined && n > this.annihilator.order) lenics = n;
    const dom = this.annihilator.parent.base.dom;
    let sol: HolonomicFunction | undefined;
    try {
      sol = exprToHolonomic(this.toExpr(), { x: this.x, x0: b, lenics, domain: dom });
    } catch (e) {
      // (NotPowerSeriesError and NotHyperSeriesError, as in SymPy)
      if (!(e instanceof SeriesExpansionError)) throw e;
    }
    if (sol?.x0.key === b.key) return sol;
    const y0 = this.evalf(b, { derivatives: true });
    return new HolonomicFunction(this.annihilator, this.x, b, y0);
  }
  /** A linear combination of Meijer G-functions representing the function (SymPy to_meijerg). */
  toMeijerg(): Expr {
    let sol: Expr = S.Zero;
    for (const i of this.toHyper(true)) {
      if (i.length === 1) sol = add(sol, i[0]);
      else sol = add(sol, mul(i[0], hyperToMeijerg(cast(i[1], Hyper))));
    }
    return sol;
  }
}

function icsEqual(a: InitialConditions, b: InitialConditions): boolean {
  if (a instanceof ExprMap || b instanceof ExprMap) {
    if (!(a instanceof ExprMap && b instanceof ExprMap) || a.size !== b.size) return false;
    return [...a.entries()].every(([k, v]) => {
      const w = b.get(k);
      return w !== undefined && w.length === v.length && v.every((u, i) => u.key === at(w, i).key);
    });
  }
  return a.length === b.length && a.every((u, i) => u.key === at(b, i).key);
}

/** SymPy equal_valued: equal numbers (a Float equal to an integer counts). */
function equalValued(a: Expr, b: Expr): boolean {
  if (a.key === b.key) return true;
  if ((a instanceof Float || a instanceof Rational) && (b instanceof Float || b instanceof Rational)) return realValue(a) === realValue(b);
  return false;
}

/** i.is_real for a root of the indicial equation. */
function isRealNumber(e: Expr): boolean {
  if (e instanceof Rational || e instanceof Float) return true;
  return ask(Q.real(e)) === true;
}

// ---------------------------------------------------------------------------
// conversions
// ---------------------------------------------------------------------------

/** The (single) symbol of the argument of a hypergeometric or Meijer G-function. */
function argSymbol(z: Expr): Sym {
  const syms = [...freeSymbols(z)];
  return first(syms);
}

/**
 * A hypergeometric function as a holonomic function (SymPy from_hyper); x0
 * is the point for the initial conditions, `evalf` evaluates them
 * numerically when the function has no closed form.
 */
export function fromHyper(funcIn: ExprLike, x0In: ExprLike = 0, evalf = false): HolonomicFunction {
  const func = sympify(funcIn);
  if (!(func instanceof Hyper)) throw new TypeError('fromHyper: expected a hyper function');
  const a = func.ap;
  const b = func.bq;
  const z = func.argument;
  const x = argSymbol(z);
  const [, Dx] = DifferentialOperators(QQ.oldPolyRing(x), 'Dx');
  const xDx = Dx.rmul(x);
  let r1 = new DifferentialOperator([S.One], Dx.parent);
  for (const ai of a) r1 = r1.mul(xDx.add(ai));
  const xDx1 = xDx.sub(1);
  let r2 = Dx;
  for (const bi of b) r2 = r2.mul(xDx1.add(bi));
  const sol = r1.sub(r2);
  const simp = hyperexpand(func);
  if (!(simp instanceof Hyper)) {
    const [x0, y0] = findConditionsFrom(simp, x, sympify(x0In), sol.order, false, false);
    return new HolonomicFunction(sol, x).composition(z, x0, y0);
  }
  const [x0, y0] = findConditionsFrom(simp, x, S.One, sol.order, evalf, false);
  return new HolonomicFunction(sol, x).composition(z, x0, y0);
}

/**
 * A Meijer G-function as a holonomic function (SymPy from_meijerg); x0 is
 * the point for the initial conditions, `evalf` evaluates them numerically
 * when the function has no closed form, `initcond: false` leaves them out.
 */
export function fromMeijerg(funcIn: ExprLike, opts: { x0?: ExprLike; evalf?: boolean; initcond?: boolean; domain?: Domain } = {}): HolonomicFunction {
  const func = sympify(funcIn);
  if (!(func instanceof MeijerG)) throw new TypeError('fromMeijerg: expected a meijerg function');
  const a = func.ap;
  const b = func.bq;
  const n = func.an.length;
  const m = func.bm.length;
  const p = a.length;
  const z = func.argument;
  const x = argSymbol(z);
  const [, Dx] = DifferentialOperators((opts.domain ?? QQ).oldPolyRing(x), 'Dx');
  const xDx = Dx.rmul(x);
  const xDx1 = xDx.add(1);
  let r1 = new DifferentialOperator([mul(x, pow(-1, m + n - p))], Dx.parent);
  for (const ai of a) r1 = r1.mul(xDx1.sub(ai));
  let r2 = new DifferentialOperator([S.One], Dx.parent);
  for (const bi of b) r2 = r2.mul(xDx.sub(bi));
  const sol = r1.sub(r2);
  if (opts.initcond === false) return new HolonomicFunction(sol, x).composition(z);
  const simp = hyperexpand(func);
  if (!(simp instanceof MeijerG)) {
    const [x0, y0] = findConditionsFrom(simp, x, sympify(opts.x0 ?? 0), sol.order, false, false);
    return new HolonomicFunction(sol, x).composition(z, x0, y0);
  }
  const [x0, y0] = findConditionsFrom(simp, x, S.One, sol.order, opts.evalf ?? false, false);
  return new HolonomicFunction(sol, x).composition(z, x0, y0);
}

/** The dummy variable of the table. */
const x1 = new Sym('x_1');

function hasFloat(e: Expr): boolean {
  return e instanceof Float || e.args.some(hasFloat);
}

/** The functions of the lookup table by name (SymPy _create_table), per domain. */
const tables = new Map<string, Map<string, HolonomicFunction>>();

function createTable(domain: Domain): Map<string, HolonomicFunction> {
  const table = new Map<string, HolonomicFunction>();
  const R = domain.oldPolyRing(x1);
  const [, Dx] = DifferentialOperators(R, 'Dx');
  const D2 = Dx.pow(2);
  const D3 = Dx.pow(3);
  const addT = (name: string, ann: DifferentialOperator, x0: ExprLike = 0, y0?: readonly ExprLike[]) => {
    table.set(name, new HolonomicFunction(ann, x1, x0, y0));
  };
  const twoSqrtPi = mul(2, pow(sqrt(S.Pi), -1));
  addT('sin', D2.add(1), 0, [0, 1]);
  addT('cos', D2.add(1), 0, [1, 0]);
  addT('exp', Dx.sub(1), 0, [1]);
  addT('log', Dx.add(D2.rmul(x1)), 1, [0, 1]);
  addT('erf', Dx.rmul(mul(2, x1)).add(D2), 0, [0, twoSqrtPi]);
  addT('erfc', Dx.rmul(mul(2, x1)).add(D2), 0, [1, neg(twoSqrtPi)]);
  addT('erfi', Dx.rmul(mul(-2, x1)).add(D2), 0, [0, twoSqrtPi]);
  addT('sinh', D2.sub(1), 0, [0, 1]);
  addT('cosh', D2.sub(1), 0, [1, 0]);
  addT('sinc', D2.rmul(x1).add(Dx.rmul(2)).add(x1));
  addT('Si', Dx.rmul(x1).add(D2.rmul(2)).add(D3.rmul(x1)));
  addT('Ci', Dx.rmul(x1).add(D2.rmul(2)).add(D3.rmul(x1)));
  addT('Shi', Dx.rmul(neg(x1)).add(D2.rmul(2)).add(D3.rmul(x1)));
  return table;
}

function lookupTable(domain: Domain): Map<string, HolonomicFunction> {
  const k = domain.toString();
  let t = tables.get(k);
  if (!t) {
    t = createTable(domain);
    tables.set(k, t);
  }
  return t;
}

/** The function name and argument of an application (exp is a power of E in symjs). */
function functionParts(e: Expr): [string, Expr] | undefined {
  if (e instanceof Pow && e.base instanceof Constant && e.base.name === 'E') return ['exp', e.exp];
  if (e instanceof Fn) return [e.name, first(e.args)];
  if (e instanceof UndefFn) return [e.name, first(e.args)];
  if (e instanceof ExtensionExpr) return [e.name, last(e.args)];
  return undefined;
}

/** Options of exprToHolonomic. */
export interface ExprToHolonomicOptions {
  /** The variable (the only free symbol by default). */
  x?: Sym;
  /** The point of the initial conditions. */
  x0?: ExprLike;
  /** Initial conditions to use. */
  y0?: InitialConditionsLike;
  /** The number of initial conditions (the order of the annihilator by default). */
  lenics?: number;
  /** The ground domain of the coefficients (QQ, RR for Floats, with the other symbols as a fraction field). */
  domain?: Domain;
  /** false: no initial conditions. */
  initcond?: boolean;
}

/**
 * An expression as a holonomic function (SymPy expr_to_holonomic): built
 * from polynomials, rational and algebraic functions, the functions of a
 * table (sin, cos, exp, log, erf, ...) and Meijer G-function
 * representations, by sums, products, powers and composition.
 */
export function exprToHolonomic(funcIn: ExprLike, opts: ExprToHolonomicOptions = {}): HolonomicFunction {
  const func = sympify(funcIn);
  const syms = ordered([...freeSymbols(func)]).filter((s): s is Sym => s instanceof Sym);
  let x = opts.x;
  if (!x) {
    if (syms.length === 1) x = first(syms);
    else throw new TypeError('Specify the variable for the function');
  }
  const xv = x;
  const extraSyms = syms.filter((s) => s.key !== xv.key);
  let domain = opts.domain;
  if (!domain) {
    domain = hasFloat(func) ? RR : QQ;
    if (extraSyms.length) domain = domain.polyRing(...extraSyms).getField();
  }
  const initcond = opts.initcond ?? true;
  let x0 = sympify(opts.x0 ?? 0);
  const y0 = toIcs(opts.y0);
  let lenics = opts.lenics;
  const solpoly = convertPolyRatAlg(func, xv, x0, y0, lenics, domain, initcond);
  if (solpoly) return solpoly;
  const parts = functionParts(func);
  if (parts) {
    const table = lookupTable(domain);
    const entry = table.get(parts[0]);
    if (!entry) {
      const sol = convertMeijerint(func, xv, false, domain);
      if (!sol) throw new NotImplementedError(`expr_to_holonomic: cannot convert ${str(func)}`);
      if (y0) sol.y0 = y0;
      if (y0 || !initcond) {
        sol.x0 = x0;
        return sol;
      }
      lenics ??= sol.annihilator.order;
      const [p, ys] = findConditionsFrom(func, xv, x0, lenics);
      return new HolonomicFunction(sol.annihilator, xv, p, ys);
    }
    const sol = entry.changeX(xv);
    if (y0 || !initcond) {
      const c = sol.composition(parts[1]);
      if (y0) c.y0 = y0;
      c.x0 = x0;
      return c;
    }
    lenics ??= sol.annihilator.order;
    const [p, ys] = findConditionsFrom(func, xv, x0, lenics);
    return sol.composition(parts[1], p, ys);
  }
  const sub = (e: Expr) => exprToHolonomic(e, { x: xv, initcond: false, domain });
  let sol: HolonomicFunction;
  if (func instanceof Add) sol = func.args.slice(1).reduce((s, a) => s.add(sub(a)), sub(first(func.args)));
  else if (func instanceof Mul) sol = func.args.slice(1).reduce((s, a) => s.mul(sub(a)), sub(first(func.args)));
  else if (func instanceof Pow) sol = sub(func.base).pow(func.exp);
  else throw new NotImplementedError(`expr_to_holonomic: cannot convert ${str(func)}`);
  sol.x0 = x0;
  if (y0) sol.y0 = y0;
  if (y0 || !initcond) return sol;
  if (sol.haveInitCond()) return sol;
  lenics ??= sol.annihilator.order;
  if (sol.annihilator.isSingular(x0)) {
    const r = sol.indicial();
    const l = [...r.keys()];
    // a single root of multiplicity 1
    if ([...r.values()].join(',') === '1') {
      const p = first(l);
      const g = mul(func, pow(add(xv, neg(x0)), neg(p)));
      const singularIcs = defined(findConditions(g, xv, x0, lenics), 'singular initial conditions').map((j, i) => mul(j, pow(factorial(i), -1)));
      return new HolonomicFunction(sol.annihilator, xv, x0, new ExprMap([[p, singularIcs]]));
    }
  }
  [x0, sol.y0] = findConditionsFrom(func, xv, x0, lenics);
  return new HolonomicFunction(sol.annihilator, xv, x0, sol.y0);
}

/** Polynomials, rational and algebraic functions as holonomic functions (SymPy _convert_poly_rat_alg), undefined for others. */
function convertPolyRatAlg(
  func: Expr,
  x: Sym,
  x0In: Expr,
  y0In: InitialConditions | undefined,
  lenicsIn: number | undefined,
  domain: Domain,
  initcond: boolean,
): HolonomicFunction | undefined {
  let x0 = x0In;
  let y0 = y0In;
  const ispoly = isPolynomial(func);
  const israt = ispoly || isRationalFunction(func);
  let basepoly: Expr = S.Zero;
  let ratexp: Expr = S.Zero;
  let isAlg = true;
  if (!israt) {
    [basepoly, ratexp] = asBaseExp(func);
    if (isPolynomial(basepoly) && (ratexp instanceof Rational || ratexp instanceof Float)) {
      if (ratexp instanceof Float) ratexp = nsimplify(ratexp);
    } else isAlg = false;
  }
  if (!isAlg) return undefined;
  const R = domain.oldPolyRing(x);
  const [, Dx] = DifferentialOperators(R, 'Dx');
  if (!func.has(x)) return new HolonomicFunction(Dx, x, 0, [func]);
  let sol: DifferentialOperator;
  if (ispoly) {
    sol = normalize(Dx.rmul(func).sub(diffExpr(func, x)).listofpoly, Dx.parent, false);
    if (y0 === undefined && zeroE(x0) && sol.isSingular(x0)) {
      const rep = [...R.fromSympy(func).toList()].reverse();
      const i = rep.findIndex((j) => !domain.isZero(j));
      y0 = new ExprMap([[intE(i), rep.slice(i).map((c) => domain.toSympy(c))]]);
    }
  } else if (israt) {
    const [p, q] = fraction(together(func));
    sol = normalize(
      Dx.rmul(mul(p, q))
        .add(mul(p, diffExpr(q, x)))
        .sub(mul(q, diffExpr(p, x))).listofpoly,
      Dx.parent,
      false,
    );
  } else {
    const r = expectType(ratexp, (u: unknown): u is Rational => u instanceof Rational, 'a rational exponent');
    const op = Dx.rmul(mul(Rational.of(r.q), x, pow(Rational.of(r.p), -1))).sub(1);
    sol = new HolonomicFunction(op, x).composition(basepoly).annihilator;
    if (y0 === undefined && zeroE(x0) && sol.isSingular(x0) && (lenicsIn === undefined || lenicsIn <= 1)) {
      const rep = [...R.fromSympy(basepoly).toList()].reverse();
      const i = rep.findIndex((j) => !domain.isZero(j));
      const coeff = pow(domain.toSympy(at(rep, i)), ratexp);
      y0 = new ExprMap([[mul(intE(i), ratexp), [coeff]]]);
    }
  }
  if (y0 || !initcond) return new HolonomicFunction(sol, x, x0, y0);
  const lenics = lenicsIn ?? sol.order;
  if (sol.isSingular(x0)) {
    // the annihilator has order 1 and a regular singular point here: the indicial equation has a single root
    const p = first([...new HolonomicFunction(sol, x, x0).indicial().keys()]);
    const g = mul(func, pow(add(x, neg(x0)), neg(p)));
    const singularIcs = defined(findConditions(g, x, x0, lenics), 'singular initial conditions').map((j, i) => mul(j, pow(factorial(i), -1)));
    return new HolonomicFunction(sol, x, x0, new ExprMap([[p, singularIcs]]));
  }
  let ys: Expr[];
  [x0, ys] = findConditionsFrom(func, x, x0, lenics);
  return new HolonomicFunction(sol, x, x0, ys);
}

/** A function by its Meijer G-function representation (SymPy _convert_meijerint), undefined when there is none. */
function convertMeijerint(func: Expr, x: Sym, initcond: boolean, domain: Domain): HolonomicFunction | undefined {
  const args = rewrite1(func, x);
  if (!args) return undefined;
  const [fac, po, g] = args;
  const facList = g.map((i) => mul(fac, i[0]));
  // po is 1 for a function application (SymPy: the exponent of x in po, if any)
  void po;
  const poList = g.map((i) => i[1]);
  const GList = g.map((i) => i[2]);
  // x**s * meijerg(a, b, z) as one Meijer G-function
  const shift = (f: MeijerG, s2: Expr): [Expr, Expr] => {
    let z = f.argument;
    if (z.has(S.I)) z = mapBottomUp(z, (e) => (e instanceof Fn && e.name === 'exp_polar' ? exp(first(e.args)) : e));
    const [a, b0] = getCoeffExp(z, x);
    const r = mul(s2, pow(b0, -1));
    const sh = (l: readonly Expr[]) => l.map((i) => add(i, r));
    return [pow(a, neg(r)), meijerg(sh(f.an), sh(f.aother), sh(f.bm), sh(f.bother), z)];
  };
  let sol: HolonomicFunction | undefined;
  for (const [i, G] of GList.entries()) {
    const [coeff, m] = shift(G, at(poList, i));
    const t = fromMeijerg(m, { initcond, domain }).mul(mul(at(facList, i), coeff));
    sol = sol ? sol.add(t) : t;
  }
  return sol;
}
