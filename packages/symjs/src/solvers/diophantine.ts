// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Diophantine equations (port of SymPy 1.14
 * sympy/solvers/diophantine/diophantine.py, BSD 3-Clause, Copyright (c)
 * SymPy Development Team): `diophantine`, `classify_diop`, `diop_solve`, the
 * equation types (`Linear`, `BinaryQuadratic`, ...), `DiophantineSolutionSet`
 * and the number-theoretic helpers they use (`diop_DN`, `cornacchia`,
 * `descent`, `sum_of_squares`, ...).
 *
 * Integers are bigints. Where SymPy returns `None` for "no solution" symjs
 * returns `EmptySet`; where a function is given an equation of another type
 * (SymPy returns `None` implicitly) it returns `NoMatch`.
 */

import type { ExprLike, Substitution } from '../core/nodes';
import { Add, Expr, Mul, Pow, Rational, Rel, S, Sym } from '../core/nodes';
import { Lt } from '../core/logic';
import { abs } from '../functions/elementary';
import { at, defined, expectType, first, getOrThrow, pair } from '../core/guard';
import { add, couldExtractMinusSign, mul, neg, pow, sqrt, sub, sympify } from '../core/ops';
import { NotImplementedError } from '../core/errors';
import { ExprMap } from '../core/exprmap';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { asCoeffAdd, asContentPrimitive, asIndependent, asNumerDenom, asCoefficientsDict, isPolynomial } from '../core/methods';
import { ask, Q } from '../core/refine';
import { igcd, ilcm, integerNthroot } from '../core/numberutils';
import { compareKeys, sortKey } from '../printing/sortkey';
import { str } from '../printing/str';
import { babs, divmod, fdiv, gcdext, invert, iroot, isSquare, isqrt, jacobi, powmod, remove } from '../ntheory/intutil';
import { divisors, factorint, perfectPower } from '../ntheory/factor';
import { nextprime } from '../ntheory/generate';
import { isprime } from '../ntheory/primetest';
import { symmetricResidue } from '../ntheory/modular';
import { sqrtMod, sqrtModIter } from '../ntheory/residue';
import { continuedFractionPeriodic } from '../ntheory/continued';
import { numberedSymbols, orderedPartitions, permuteSigns, signedPermutations } from '../utilities/iterables';
import { EmptySet } from '../sets/sets';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients } from '../polys/poly';
import { Poly, factorListExpr } from '../polys/sympoly';
import { expand } from '../simplify/expand';
import { factorTerms, signsimp } from '../simplify/exprtools';
import { mexpand } from '../simplify/fu';

// ---------------------------------------------------------------------------
// small helpers
// ---------------------------------------------------------------------------

const R = (n: bigint | number): Rational => Rational.of(BigInt(n));
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;
/** SymPy is_number: no free symbols. */
const isConst = (e: Expr): boolean => freeSymbols(e).size === 0;
const bsign = (n: bigint): bigint => (n > 0n ? 1n : n < 0n ? -1n : 0n);
const symbolsRange = (prefix: string, start: number, end: number): Sym[] =>
  Array.from({ length: Math.max(0, end - start) }, (_, i) => new Sym(`${prefix}${start + i}`, { integer: true }));

/** The integer value of e (SymPy as_int); a RangeError when e is not an integer. */
function asBig(e: ExprLike | bigint): bigint {
  if (typeof e === 'bigint') return e;
  const v = sympify(e);
  if (!isInt(v)) throw new RangeError(`${str(v)} is not an integer`);
  return v.p;
}

/** Symbols sorted like SymPy default_sort_key. */
const sortedSymbols = (e: Expr): Sym[] => [...freeSymbols(e)].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

/** Order of solution tuples of the same size: element by element (SymPy ordered). */
const compareTuples = (a: readonly Expr[], b: readonly Expr[]): number => compareKeys(a.map(sortKey), b.map(sortKey));

const tupleKey = (t: readonly Expr[]): string => t.map((e) => e.key).join('|');

/** A set of solution tuples compared structurally. */
class TupleSet {
  readonly items = new Map<string, Expr[]>();
  add(t: readonly Expr[]): void {
    this.items.set(tupleKey(t), [...t]);
  }
  has(t: readonly Expr[]): boolean {
    return this.items.has(tupleKey(t));
  }
  values(): Expr[][] {
    return [...this.items.values()];
  }
  sorted(): Expr[][] {
    return this.values().sort(compareTuples);
  }
}

/** A numeric coefficient (Rational part) and the rest of a product (SymPy as_coeff_Mul). */
function coeffMul(e: Expr): [Rational, Expr] {
  const a0 = e instanceof Mul ? first(e.args) : undefined;
  if (e instanceof Mul && a0 instanceof Rational) return [a0, mul(...e.args.slice(1))];
  return [S.One, e];
}

/** The rational constant term and the rest of a sum (SymPy as_coeff_Add(rational=True)). */
function coeffAdd(e: Expr): [Rational, Expr] {
  const [c, rest] = asCoeffAdd(e);
  return [expectType(c, (w): w is Rational => w instanceof Rational, 'rational constant term'), add(...rest)];
}

/** The integers dividing out the gcd (SymPy _remove_gcd for integers). */
function removeGcd<T extends bigint[]>(...xs: T): T {
  const g = igcd(...xs);
  if (g === 1n || g === 0n) return xs;
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- map keeps the length of the tuple
  return xs.map((x) => x / g) as T;
}

/** The first three elements. */
const triple = <T>(xs: readonly T[]): [T, T, T] => [at(xs, 0), at(xs, 1), at(xs, 2)];

/** SymPy _remove_gcd for expressions: the gcd of the rational contents is divided out. */
function removeGcdExpr(...xs: Expr[]): Expr[] {
  if (xs.every(isInt)) return removeGcd(...xs.map((x) => x.p)).map(R);
  // the solutions passed here have at least two nonzero values
  const fx = xs.filter((x) => !(x instanceof Rational && x.isZero));
  const g = igcd(...fx.map((x) => asContentPrimitive(x)[0].p));
  if (g === 1n) return xs;
  return xs.map((x) => mul(x, Rational.of(1n, g)));
}

/** (numer, denom) of a/b with the sign in numer and the gcd removed (SymPy _rational_pq). */
const rationalPq = (a: bigint, b: bigint): [bigint, bigint] => pair(removeGcd(bsign(b) * a, babs(b)));

/** The nearest integer to p/q, the floor in case of a tie (SymPy _nint_or_floor). */
function nintOrFloor(p: bigint, q: bigint): bigint {
  const [w, r] = divmod(p, q);
  return babs(r) <= babs(q) / 2n ? w : w + 1n;
}

const isOdd = (i: bigint): boolean => i % 2n !== 0n;

/** Three integers. */
type Int3 = [bigint, bigint, bigint];

/** SymPy check_assumptions(val, **sym.assumptions0) is False. */
function contradictsAssumptions(val: Expr, s: Sym): boolean {
  const a = s.assumptions;
  const checks: [boolean | undefined, Expr][] = [
    [a.integer, Q.integer(val)],
    [a.positive, Q.positive(val)],
    [a.negative, Q.negative(val)],
    [a.nonnegative, Q.nonnegative(val)],
    [a.nonpositive, Q.nonpositive(val)],
    [a.real, Q.real(val)],
  ];
  if (a.zero === false && ask(Q.zero(val)) === true) return true;
  return checks.some(([want, prop]) => want === true && ask(prop) === false);
}

// ---------------------------------------------------------------------------
// DiophantineSolutionSet
// ---------------------------------------------------------------------------

/**
 * SymPy `DiophantineSolutionSet`: a set of solution tuples of a Diophantine
 * equation, with the symbols of the equation and the parameters of the
 * solutions. Tuples are compared structurally.
 */
export class DiophantineSolutionSet implements Iterable<Expr[]> {
  readonly symbols: readonly Expr[];
  readonly parameters: readonly Expr[];
  readonly #items = new TupleSet();

  constructor(symbolsSeq: readonly Expr[], parameters: readonly Expr[]) {
    this.symbols = [...symbolsSeq];
    this.parameters = [...parameters];
  }

  /** Adds a solution, made canonical with respect to sign (no -x unless x is also present). */
  add(solutionIn: readonly ExprLike[]): void {
    if (solutionIn.length !== this.symbols.length) {
      throw new RangeError(`Solution should have a length of ${this.symbols.length}, not ${solutionIn.length}`);
    }
    let solution = solutionIn.map((v) => sympify(v));
    const args = new Set(solution.map((e) => e.key));
    for (let i = 0; i < solution.length; i++) {
      const x = at(solution, i);
      const nx = neg(x);
      if (nx instanceof Sym && !args.has(nx.key)) solution = solution.map((e) => subs(e, [[nx, x]]));
    }
    this.#items.add(solution);
  }

  /** Adds several solutions. */
  update(...solutions: readonly (readonly ExprLike[])[]): void {
    for (const s of solutions) this.add(s);
  }

  /** The solutions as Maps from the symbols to their values, in sorted order. */
  *dictIterator(): Generator<ExprMap<Expr>, void, undefined> {
    for (const sol of this.#items.sorted()) yield new ExprMap(this.symbols.map((s, i) => [s, at(sol, i)] as const));
  }

  /** The solutions with a substitution applied (`subs(old, new)` or `subs(mapping)`). */
  subs(s: Substitution | Expr, v?: ExprLike): DiophantineSolutionSet {
    const rep: Substitution = s instanceof Expr ? [[s, defined(v, 'the new value')]] : s;
    const result = new DiophantineSolutionSet(this.symbols, this.parameters);
    for (const sol of this) result.add(sol.map((e) => subs(e, rep)));
    return result;
  }

  /** The solutions evaluated at values of the parameters, in order; `null` keeps a parameter (SymPy `__call__`). */
  call(...args: (ExprLike | null)[]): DiophantineSolutionSet {
    if (args.length > this.parameters.length) {
      throw new RangeError(`Evaluation should have at most ${this.parameters.length} values, not ${args.length}`);
    }
    const rep: [Expr, ExprLike][] = [];
    args.forEach((v, i) => {
      if (v !== null) rep.push([at(this.parameters, i), v]);
    });
    return this.subs(rep);
  }

  get size(): number {
    return this.#items.items.size;
  }

  has(solution: readonly ExprLike[]): boolean {
    return this.#items.has(solution.map((v) => sympify(v)));
  }

  *[Symbol.iterator](): Generator<Expr[], void, undefined> {
    for (const t of this.#items.values()) yield [...t];
  }

  /** Python's repr of the set: `DiophantineSolutionSet({(2, 3)})`. */
  toString(): string {
    if (!this.size) return 'DiophantineSolutionSet()';
    const tup = (t: readonly Expr[]) => (t.length === 1 ? `(${str(first(t))},)` : `(${t.map(str).join(', ')})`);
    return `DiophantineSolutionSet({${[...this].map(tup).join(', ')}})`;
  }
}

// ---------------------------------------------------------------------------
// Equation types
// ---------------------------------------------------------------------------

/** Coefficients keyed by monomial (SymPy as_coefficients_dict as a defaultdict(int)). */
class Coeffs {
  readonly map = new ExprMap<bigint>();
  get(k: ExprLike): bigint {
    return this.map.get(k) ?? 0n;
  }
  /** The equation sum(coefficient*monomial). */
  expr(): Expr {
    return add(...[...this.map].map(([k, c]) => mul(c, k)));
  }
  static of(entries: Iterable<readonly [ExprLike, bigint]>): Coeffs {
    const c = new Coeffs();
    for (const [k, v] of entries) c.map.set(k, v);
    return c;
  }
}

/** The coefficients of the terms keyed by their monomials: number factors such as sqrt(2) belong to the coefficient (SymPy as_coefficients_dict). */
function numericCoefficients(e: Expr): ExprMap<Expr> {
  const out = new ExprMap<Expr>();
  for (const term of e instanceof Add ? e.args : [e]) {
    const factors = term instanceof Mul ? term.args : [term];
    const c = mul(...factors.filter((f) => isConst(f)));
    const m = mul(...factors.filter((f) => !isConst(f)));
    out.set(m, add(out.get(m) ?? S.Zero, c));
  }
  return out;
}

/** Options of `solve` of the equation types. */
export interface DiophantineSolveOptions {
  /** The parameters of the solution (default `t_0, t_1, ...`). */
  parameters?: readonly Expr[] | null;
  /** The maximum number of solutions (sums of squares and powers). */
  limit?: number;
}

/**
 * SymPy `DiophantineEquationType`: the internal representation of a
 * Diophantine equation of a particular type.
 */
export class DiophantineEquationType {
  readonly name: string = 'diophantine';
  readonly equation: Expr;
  readonly freeSymbols: readonly Sym[];
  /** Coefficients keyed by monomial (the constant term by 1). */
  readonly coeff: ExprMap<Expr>;
  /** The maximum of the degrees of the terms. */
  readonly totalDegree: number;
  /** The equation has no constant term. */
  readonly homogeneous: boolean;
  /** No term is linear in a symbol being solved for. */
  readonly homogeneousOrder: boolean;
  /** The number of symbols being solved for. */
  readonly dimension: number;
  protected c: Coeffs;
  protected params: readonly Expr[] | null = null;

  constructor(equation: ExprLike, freeSymbolsIn?: readonly Sym[]) {
    this.equation = expand(sympify(equation), { force: true });
    this.freeSymbols = freeSymbolsIn ? [...freeSymbolsIn] : sortedSymbols(this.equation);
    if (!this.freeSymbols.length) throw new RangeError('equation should have 1 or more free symbols');
    this.c = new Coeffs();
    for (const [k, v] of numericCoefficients(this.equation)) {
      if (!isInt(v)) throw new TypeError('Coefficients should be Integers');
      this.c.map.set(k, v.p);
    }
    this.coeff = new ExprMap([...this.c.map].map(([k, v]) => [k, R(v)] as const));
    this.totalDegree = Poly.from(this.equation).totalDegree();
    this.homogeneous = !this.c.map.has(1);
    const syms = new Set(this.freeSymbols.map((s) => s.key));
    this.homogeneousOrder = ![...this.c.map.keys()].some((k) => syms.has(k.key));
    this.dimension = this.freeSymbols.length;
  }

  /** The equation is of this type. */
  matches(): boolean {
    return false;
  }

  get nParameters(): number {
    return this.dimension;
  }

  get parameters(): readonly Expr[] {
    this.params ??= symbolsRange('t_', 0, this.nParameters);
    return this.params;
  }

  /** The solutions of the equation. */
  solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    void opts;
    throw new NotImplementedError(`No solver has been written for ${this.name}.`);
  }

  protected preSolve(parameters: readonly Expr[] | null | undefined): void {
    if (!this.matches()) throw new RangeError(`This equation does not match the ${this.name} equation type.`);
    if (parameters && parameters.length !== this.nParameters) {
      throw new RangeError(`Expected ${this.nParameters} parameter(s) but got ${parameters.length}`);
    }
    this.params = parameters ?? null;
  }

  /** The monomial keys of the coefficients. */
  protected get keys(): Expr[] {
    return [...this.c.map.keys()];
  }
}

/** SymPy `Univariate`: a polynomial equation in one integer variable. */
export class Univariate extends DiophantineEquationType {
  override readonly name: string = 'univariate';

  override matches(): boolean {
    return this.dimension === 1;
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const result = new DiophantineSolutionSet(this.freeSymbols, this.parameters);
    for (const i of integerRoots(this.equation, first(this.freeSymbols))) result.add([R(i)]);
    return result;
  }
}

/** The integer roots of a polynomial with integer coefficients, sorted (SymPy solveset_real(...).intersect(Integers)). */
function integerRoots(eq: Expr, x: Sym): bigint[] {
  const out = new Set<bigint>();
  for (const [f] of factorListExpr(eq, [x])[1]) {
    const pc = defined(polyCoefficients(f, x), 'polynomial factor');
    if (pc.size > 2 || !pc.has(1)) continue;
    const a = asBig(defined(pc.get(1)));
    const b = asBig(pc.get(0) ?? S.Zero);
    if (b % a === 0n) out.add(-b / a);
  }
  return [...out].sort((p, q) => (p < q ? -1 : 1));
}

/** SymPy `Linear`: `a_1*x_1 + ... + a_n*x_n + c = 0`. */
export class Linear extends DiophantineEquationType {
  override readonly name: string = 'linear';

  override matches(): boolean {
    return this.totalDegree === 1;
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const coeff = this.c;
    const v = this.freeSymbols;
    // the equation a*x + b*y + c == 0 is used as a*x + b*y == -c
    let c: Expr = R(-coeff.get(1));
    const result = new DiophantineSolutionSet(v, this.parameters);
    const params = result.parameters;
    if (v.length === 1) {
      const [q, r] = divmod(asBig(c), coeff.get(first(v)));
      if (r === 0n) result.add([R(q)]);
      return result;
    }
    // a_0*x_0 + ... + a_n*x_n == c is broken into the bivariate equations
    // A[i]*x_i + B[i]*y_i == c_i (see SymPy for the derivation)
    const A = v.map((s) => coeff.get(s));
    const B: bigint[] = [];
    if (v.length > 2) {
      B.push(igcd(at(A, -2), at(A, -1)));
      A[A.length - 2] = at(A, -2) / first(B);
      A[A.length - 1] = at(A, -1) / first(B);
      for (let i = A.length - 3; i > 0; i--) {
        const g = igcd(first(B), at(A, i));
        B[0] = first(B) / g;
        A[i] = at(A, i) / g;
        B.unshift(g);
      }
    }
    B.push(at(A, -1));
    const solutions: Expr[] = [];
    for (let i = 0; i < B.length; i++) {
      const Ai = at(A, i);
      const Bi = at(B, i);
      const totX: Expr[] = [];
      const totY: Expr[] = [];
      for (const arg of c instanceof Add ? c.args : [c]) {
        let k: Rational;
        let p: Expr;
        let pnew: Expr;
        if (isInt(arg)) {
          [k, p, pnew] = [arg, S.One, first(params)];
        } else {
          // 3*t_1 -> k = 3, t_0 -> k = 1
          [k, p] = coeffMul(arg);
          pnew = at(params, params.findIndex((q) => q.key === p.key) + 1);
        }
        const sol = baseSolutionLinearImpl(k.p, Ai, Bi, pnew);
        if (sol === null) return result;
        let [sx, sy] = sol;
        if (p !== S.One) {
          // a + b*pnew -> a*p + b*pnew
          const [cx, rx] = coeffAdd(sx);
          const [cy, ry] = coeffAdd(sy);
          sx = add(mul(cx, p), rx);
          sy = add(mul(cy, p), ry);
        }
        totX.push(sx);
        totY.push(sy);
      }
      solutions.push(add(...totX));
      c = add(...totY);
    }
    solutions.push(c);
    result.add(solutions);
    return result;
  }
}

/** SymPy `BinaryQuadratic`: `A*x**2 + B*x*y + C*y**2 + D*x + E*y + F = 0`. */
export class BinaryQuadratic extends DiophantineEquationType {
  override readonly name: string = 'binary_quadratic';

  override matches(): boolean {
    return this.totalDegree === 2 && this.dimension === 2;
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    const parameters = opts.parameters;
    this.preSolve(parameters);
    const v = this.freeSymbols;
    const coeff = this.c;
    const [x, y] = pair(v);
    const [A, B, C, D, E, F] = removeGcd(coeff.get(pow(x, 2)), coeff.get(mul(x, y)), coeff.get(pow(y, 2)), coeff.get(x), coeff.get(y), coeff.get(1));
    const result = new DiophantineSolutionSet(v, this.parameters);
    const [t, u] = pair(result.parameters);
    const discr = B ** 2n - 4n * A * C;
    if (A === 0n && C === 0n && B !== 0n) {
      // (1) simple hyperbolic case: (B*x + E)*(B*y + D) = D*E - B*F
      if (D * E - B * F === 0n) {
        let [q, r] = divmod(E, B);
        if (r === 0n) result.add([R(-q), t]);
        [q, r] = divmod(D, B);
        if (r === 0n) result.add([t, R(-q)]);
      } else {
        const div = divisors(D * E - B * F);
        for (const d of [...div, ...div.map((s) => -s)]) {
          const [x0, r] = divmod(d - E, B);
          if (r !== 0n) continue;
          // d divides D*E - B*F
          const [y0, r3] = divmod((D * E - B * F) / d - D, B);
          if (r3 === 0n) result.add([R(x0), R(y0)]);
        }
      }
    } else if (discr === 0n) {
      // (2) parabolic case
      if (A === 0n) {
        const s = new BinaryQuadratic(this.equation, [y, x]).solve({ parameters: [t, u] });
        for (const soln of s) result.add([at(soln, 1), at(soln, 0)]);
      } else {
        const g = bsign(A) * igcd(A, C);
        const a = A / g;
        const c = C / g;
        // sign(B/A)
        const e = bsign(B) * bsign(A);
        const sqa = isqrt(a);
        const sqc = isqrt(c);
        const cc = e * sqc * D - sqa * E;
        if (cc === 0n) {
          const z = new Sym('z', { real: true });
          const eq = add(mul(sqa * g, pow(z, 2)), mul(D, z), sqa * F);
          for (const root of integerRoots(eq, z)) {
            const ans = diopSolveImpl(add(mul(sqa, x), mul(e * sqc, y), -root), DEFAULT_PARAM);
            const sol = first(asSolutionList(ans));
            result.add([at(sol, 0), at(sol, 1)]);
          }
        } else {
          const solveX = (z0: bigint): Expr =>
            add(mul(-e * sqc * g * cc, pow(t, 2)), mul(-(E + 2n * e * sqc * g * z0), t), -fdiv(e * sqc * g * z0 ** 2n + E * z0 + e * sqc * F, cc));
          const solveY = (z0: bigint): Expr => add(mul(sqa * g * cc, pow(t, 2)), mul(D + 2n * sqa * g * z0, t), fdiv(sqa * g * z0 ** 2n + D * z0 + sqa * F, cc));
          for (let z0 = 0n; z0 < babs(cc); z0++) {
            if ((sqa * g * z0 ** 2n + D * z0 + sqa * F) % cc === 0n && (e * sqc * g * z0 ** 2n + E * z0 + e * sqc * F) % cc === 0n) {
              result.add([solveX(z0), solveY(z0)]);
            }
          }
        }
      }
    } else if (isSquare(discr)) {
      // (3) B**2 - 4*A*C is a square (J. P. Robertson, p. 6)
      if (A !== 0n) {
        const r = isqrt(discr);
        const [uu, vv] = [new Sym('u', { integer: true }), new Sym('v', { integer: true })];
        const eq = mexpand(
          add(
            mul(4n * A * r, uu, vv),
            mul(4n * A * D, add(mul(B, vv), mul(r, uu), mul(r, vv), mul(-B, uu))),
            mul(2n * A * 4n * A * E, sub(uu, vv)),
            4n * A * r * 4n * A * F,
          ),
        );
        for (const [s0, t0] of asSolutionList(diopSolveImpl(eq, t)).map((s) => pair(s))) {
          const num = add(mul(B, t0), mul(r, s0), mul(r, t0), mul(-B, s0));
          const x0 = mul(num, Rational.of(1n, 4n * A * r));
          const y0 = mul(sub(s0, t0), Rational.of(1n, 2n * r));
          if (s0 instanceof Sym || t0 instanceof Sym) {
            const ans = checkParam(x0, y0, parameters ?? null);
            result.update(...ans);
          } else if (isInt(x0) && isInt(y0) && isSolutionQuad(v, coeff, x0, y0)) {
            result.add([x0, y0]);
          }
        }
      } else {
        // interchange x and y
        const s = new BinaryQuadratic(this.equation, [y, x]).solve({ parameters: [t, u] });
        for (const sol of s) result.add([...sol].reverse());
      }
    } else {
      // (4) B**2 - 4*A*C > 0 not a square, or B**2 - 4*A*C < 0
      const [P, Qv] = transformationToDNImpl(A, B, C, D, E, F);
      const [Dn, N] = findDNImpl(v, coeff);
      const solnsPell = diopDNInt(Dn, N);
      const transform = (X: Expr, Y: Expr): Expr[] => [
        add(mul(at(P, 0), X), mul(at(P, 1), Y), at(Qv, 0)),
        add(mul(at(P, 2), X), mul(at(P, 3), Y), at(Qv, 1)),
      ];
      if (Dn < 0n) {
        for (const [x0, y0] of solnsPell) {
          for (const xs of [-x0, x0]) {
            for (const ys of [-y0, y0]) {
              const s = transform(R(xs), R(ys));
              if (s.every(isInt)) result.add(s);
            }
          }
        }
      } else {
        // the equation is transformed into a Pell equation
        const pell = new Map<string, [bigint, bigint]>();
        for (const [X, Y] of solnsPell) {
          pell.set(`${X},${Y}`, [X, Y]);
          pell.set(`${-X},${-Y}`, [-X, -Y]);
        }
        const [T, U] = first(diopDNInt(Dn, 1n));
        const sD = sqrt(Dn);
        if ([...P, ...Qv].every(isInt)) {
          for (const [r, s] of pell.values()) {
            const a = mul(add(r, mul(s, sD)), pow(add(T, mul(U, sD)), t));
            const b = mul(sub(r, mul(s, sD)), pow(sub(T, mul(U, sD)), t));
            const xn = mexpand(mul(add(a, b), Rational.of(1n, 2n)));
            const yn = mexpand(mul(sub(a, b), pow(mul(2, sD), -1)));
            result.add(transform(xn, yn));
          }
        } else {
          const L = ilcm(...[...P, ...Qv].map((e) => e.q));
          let k = 1;
          let [Tk, Uk] = [T, U];
          while ((Tk - 1n) % L !== 0n || Uk % L !== 0n) {
            [Tk, Uk] = [Tk * T + Dn * Uk * U, Tk * U + Uk * T];
            k++;
          }
          for (const [X0, Y0] of pell.values()) {
            let [X, Y] = [X0, Y0];
            for (let i = 0; i < k; i++) {
              if (transform(R(X), R(Y)).every(isInt)) {
                const a = mul(add(X, mul(sD, Y)), pow(add(Tk, mul(sD, Uk)), t));
                const b = mul(sub(X, mul(sD, Y)), pow(sub(Tk, mul(sD, Uk)), t));
                const Xt = mul(add(a, b), Rational.of(1n, 2n));
                const Yt = mul(sub(a, b), pow(mul(2, sD), -1));
                result.add(transform(Xt, Yt));
              }
              [X, Y] = [X * T + Dn * U * Y, X * U + Y * T];
            }
          }
        }
      }
    }
    return result;
  }
}

/** SymPy `InhomogeneousTernaryQuadratic` (no solver is implemented for this type). */
export class InhomogeneousTernaryQuadratic extends DiophantineEquationType {
  override readonly name: string = 'inhomogeneous_ternary_quadratic';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension === 3)) return false;
    if (!this.homogeneous) return false;
    return !this.homogeneousOrder;
  }
}

/** The equation has exactly the three squares of its variables as terms. */
function isNormalTernary(t: DiophantineEquationType, keys: readonly Expr[], coeff: Coeffs): boolean {
  const nonzero = new Set(keys.filter((k) => coeff.get(k) !== 0n).map((k) => k.key));
  return nonzero.size === 3 && t.freeSymbols.every((i) => nonzero.has(pow(i, 2).key));
}

/** SymPy `HomogeneousTernaryQuadraticNormal`: `a*x**2 + b*y**2 + c*z**2 = 0`. */
export class HomogeneousTernaryQuadraticNormal extends DiophantineEquationType {
  override readonly name: string = 'homogeneous_ternary_quadratic_normal';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension === 3)) return false;
    if (!this.homogeneous) return false;
    if (!this.homogeneousOrder) return false;
    return isNormalTernary(this, this.keys, this.c);
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const v = this.freeSymbols;
    const [x, y, z] = triple(v);
    const a = this.c.get(pow(x, 2));
    const b = this.c.get(pow(y, 2));
    const c = this.c.get(pow(z, 2));
    const [[sqfA, sqfB, sqfC], [a1, b1, c1], [a2, b2, c2]] = sqfNormalSteps(a, b, c);
    const A = -a2 * c2;
    const B = -b2 * c2;
    const result = new DiophantineSolutionSet(v, this.parameters);
    // no solutions in these cases
    if (A < 0n && B < 0n) return result;
    if (isNoMatch(sqrtMod(-b2 * c2, a2)) || isNoMatch(sqrtMod(-c2 * a2, b2)) || isNoMatch(sqrtMod(-a2 * b2, c2))) return result;
    let [z0, x0, y0] = descentImpl(A, B);
    let q: bigint;
    [z0, q] = rationalPq(z0, babs(c2));
    x0 *= q;
    y0 *= q;
    [x0, y0, z0] = removeGcd(x0, y0, z0);
    // Holzer reduction
    if (bsign(a) === bsign(b)) [x0, y0, z0] = holzerImpl(x0, y0, z0, babs(a2), babs(b2), babs(c2));
    else if (bsign(a) === bsign(c)) [x0, z0, y0] = holzerImpl(x0, z0, y0, babs(a2), babs(c2), babs(b2));
    else [y0, z0, x0] = holzerImpl(y0, z0, x0, babs(b2), babs(c2), babs(a2));
    x0 = reconstruct(b1, c1, x0);
    y0 = reconstruct(a1, c1, y0);
    z0 = reconstruct(a1, b1, z0);
    const sqLcm = ilcm(sqfA, sqfB, sqfC);
    x0 = babs(fdiv(x0 * sqLcm, sqfA));
    y0 = babs(fdiv(y0 * sqLcm, sqfB));
    z0 = babs(fdiv(z0 * sqLcm, sqfC));
    result.add(removeGcd(x0, y0, z0).map(R));
    return result;
  }
}

/** SymPy `HomogeneousTernaryQuadratic`: `a*x**2 + b*y**2 + c*z**2 + d*x*y + e*y*z + f*x*z = 0`. */
export class HomogeneousTernaryQuadratic extends DiophantineEquationType {
  override readonly name: string = 'homogeneous_ternary_quadratic';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension === 3)) return false;
    if (!this.homogeneous) return false;
    if (!this.homogeneousOrder) return false;
    return !isNormalTernary(this, this.keys, this.c);
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const vIn = this.freeSymbols;
    const coeff = this.c;
    const [x, y, z] = triple(vIn);
    const v: Sym[] = [x, y, z];
    const result = new DiophantineSolutionSet(v, this.parameters);
    type V3 = [Expr | null, Expr | null, Expr | null];
    const unpack = (sol: DiophantineSolutionSet): V3 => {
      for (const s of sol) return triple(s);
      return [null, null, null];
    };
    let x0: Expr | null;
    let y0: Expr | null;
    let z0: Expr | null;
    const sq = (s: Sym) => coeff.get(pow(s, 2));
    if (!v.some((i) => sq(i) !== 0n)) {
      // B*x*y + C*z*x + E*y*z = 0: set y = -C and solve B*x + E*z = x*z,
      // choosing the solution that minimizes |x| + |z|
      if (coeff.get(mul(x, z)) !== 0n) {
        const sols = diophantine(sub(add(mul(coeff.get(mul(x, y)), x), mul(coeff.get(mul(y, z)), z)), mul(x, z)));
        const size = (r: readonly Expr[]): Expr => add(abs(at(r, 0)), abs(at(r, 1)));
        // the sizes compare: a parametric solution is the other one with an offset
        const less = (a: readonly Expr[], b: readonly Expr[]): boolean => Lt(size(a), size(b)) === S.true;
        const s = sols.reduce((m, r) => (less(r, m) ? r : m));
        result.add(removeGcdExpr(at(s, 0), R(-coeff.get(mul(x, z))), at(s, 1)));
        return result;
      }
      [v[0], v[1]] = [y, x];
      [y0, x0, z0] = unpack(diopTernaryQuadraticSet(v, coeff));
    } else if (sq(x) === 0n) {
      // change the variables when the coefficient of x**2 is zero
      if (sq(y) === 0n) {
        [v[0], v[2]] = [z, x];
        [z0, y0, x0] = unpack(diopTernaryQuadraticSet(v, coeff));
      } else {
        [v[0], v[1]] = [y, x];
        [y0, x0, z0] = unpack(diopTernaryQuadraticSet(v, coeff));
      }
    } else if (coeff.get(mul(x, y)) !== 0n || coeff.get(mul(x, z)) !== 0n) {
      // the transformation x --> X - (B*y + C*z)/(2*A)
      const A = sq(x);
      const B = coeff.get(mul(x, y));
      const C = coeff.get(mul(x, z));
      const D = sq(y);
      const E = coeff.get(mul(y, z));
      const F = sq(z);
      const c2 = Coeffs.of([
        [pow(x, 2), 4n * A ** 2n],
        [pow(y, 2), 4n * A * D - B ** 2n],
        [pow(z, 2), 4n * A * F - C ** 2n],
        [mul(y, z), 4n * A * E - 2n * B * C],
        [mul(x, y), 0n],
        [mul(x, z), 0n],
      ]);
      const [x1, y1, z1] = unpack(diopTernaryQuadraticSet(v, c2));
      if (x1 === null || y1 === null || z1 === null) return result;
      const [X1, Y1, Z1] = [asBig(x1), asBig(y1), asBig(z1)];
      const [p, q] = rationalPq(B * Y1 + C * Z1, 2n * A);
      [x0, y0, z0] = [R(X1 * q - p), R(Y1 * q), R(Z1 * q)];
    } else if (sq(y) === 0n) {
      // the coefficient of y*z is nonzero (with only squares the equation would be normal)
      if (sq(z) === 0n) {
        // A*x**2 + E*y*z = 0
        const [b, a] = rationalPq(-coeff.get(mul(y, z)), sq(x));
        [x0, y0, z0] = [R(b), R(a), R(b)];
      } else {
        // A*x**2 + E*y*z + F*z**2 = 0
        [v[0], v[2]] = [z, x];
        [z0, y0, x0] = unpack(diopTernaryQuadraticSet(v, coeff));
      }
    } else {
      // A*x**2 + D*y**2 + E*y*z + F*z**2 = 0
      [v[0], v[1]] = [y, x];
      [y0, x0, z0] = unpack(diopTernaryQuadraticSet(v, coeff));
    }
    if (x0 === null || y0 === null || z0 === null) return result;
    result.add(removeGcdExpr(x0, y0, z0));
    return result;
  }
}

/** SymPy `InhomogeneousGeneralQuadratic` (no solver is implemented for this type). */
export class InhomogeneousGeneralQuadratic extends DiophantineEquationType {
  override readonly name: string = 'inhomogeneous_general_quadratic';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension >= 3)) return false;
    if (!this.homogeneousOrder) return true;
    return this.keys.some((k) => k instanceof Mul) && !this.homogeneous;
  }
}

/** SymPy `HomogeneousGeneralQuadratic` (no solver is implemented for this type). */
export class HomogeneousGeneralQuadratic extends DiophantineEquationType {
  override readonly name: string = 'homogeneous_general_quadratic';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension >= 3)) return false;
    if (!this.homogeneousOrder) return false;
    return this.keys.some((k) => k instanceof Mul) && this.homogeneous;
  }
}

/** The signs of the variables: -1 for those assumed nonpositive. */
const varSigns = (v: readonly Sym[]): bigint[] => v.map((s) => (s.assumptions.nonpositive === true ? -1n : 1n));

/** SymPy `GeneralSumOfSquares`: `x_1**2 + ... + x_n**2 - k = 0`. */
export class GeneralSumOfSquares extends DiophantineEquationType {
  override readonly name: string = 'general_sum_of_squares';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension >= 3)) return false;
    if (!this.homogeneousOrder) return false;
    if (this.keys.some((k) => k instanceof Mul)) return false;
    return this.keys.every((k) => k.key === S.One.key || this.c.get(k) === 1n);
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const limit = opts.limit ?? 1;
    const v = this.freeSymbols;
    const k = -this.c.get(1);
    const result = new DiophantineSolutionSet(v, this.parameters);
    if (k < 0n || limit < 1) return result;
    const signs = varSigns(v);
    let took = 0;
    for (const t of sumOfSquares(k, this.dimension, { zeros: true })) {
      result.add(t.map((j, i) => R(at(signs, i) * j)));
      took++;
      if (took === limit) break;
    }
    return result;
  }
}

/** SymPy `GeneralPythagorean`: `a_1**2*x_1**2 + ... + a_n**2*x_n**2 - a_{n+1}**2*x_{n+1}**2 = 0`. */
export class GeneralPythagorean extends DiophantineEquationType {
  override readonly name: string = 'general_pythagorean';

  override matches(): boolean {
    if (!(this.totalDegree === 2 && this.dimension >= 3)) return false;
    if (!this.homogeneousOrder) return false;
    const keys = this.keys;
    if (keys.some((k) => k instanceof Mul)) return false;
    if (keys.every((k) => k.key === S.One.key || this.c.get(k) === 1n)) return false;
    if (!keys.every((k) => isSquare(babs(this.c.get(k))))) return false;
    // all but one have the same sign
    const total = keys.reduce((s, k) => s + bsign(this.c.get(k)), 0n);
    return babs(total) === BigInt(this.dimension - 2);
  }

  override get nParameters(): number {
    return this.dimension - 1;
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const v = this.freeSymbols;
    const n = this.dimension;
    const sq = new Map(v.map((s) => [s.key, this.c.get(pow(s, 2))]));
    const cof = (s: Sym): bigint => getOrThrow(sq, s.key);
    if (bsign(cof(at(v, 0))) + bsign(cof(at(v, 1))) + bsign(cof(at(v, 2))) < 0n) for (const s of v) sq.set(s.key, -cof(s));
    const result = new DiophantineSolutionSet(v, this.parameters);
    let index = 0;
    v.forEach((s, i) => {
      if (bsign(cof(s)) === -1n) index = i;
    });
    const m = result.parameters;
    const ith = add(...m.map((mi) => pow(mi, 2)));
    const L: Expr[] = [sub(ith, mul(2, pow(at(m, n - 2), 2))), ...Array.from({ length: n - 2 }, (_, i) => mul(2, at(m, i), at(m, n - 2)))];
    const sol = [...L.slice(0, index), ith, ...L.slice(index)];
    let lcm = 1n;
    v.forEach((s, i) => {
      const r = isqrt(babs(cof(s)));
      if (i === index || (index > 0 && i === 0) || (index === 0 && i === 1)) lcm = ilcm(lcm, r);
      else lcm = ilcm(lcm, isOdd(r) ? r : r / 2n);
    });
    result.add(v.map((s, i) => mul(lcm, at(sol, i), Rational.of(1n, isqrt(babs(cof(s)))))));
    return result;
  }
}

/** SymPy `CubicThue`: `f(x, y) = r` of degree 3 (no solver is implemented for this type). */
export class CubicThue extends DiophantineEquationType {
  override readonly name: string = 'cubic_thue';

  override matches(): boolean {
    return this.totalDegree === 3 && this.dimension === 2;
  }
}

/** SymPy `GeneralSumOfEvenPowers`: `x_1**e + ... + x_n**e - k = 0` for an even `e`. */
export class GeneralSumOfEvenPowers extends DiophantineEquationType {
  override readonly name: string = 'general_sum_of_even_powers';

  override matches(): boolean {
    if (!(this.totalDegree > 3)) return false;
    if (this.totalDegree % 2 !== 0) return false;
    const keys = this.keys.filter((k) => k.key !== S.One.key);
    if (!keys.every((k) => k instanceof Pow && k.exp.key === R(this.totalDegree).key)) return false;
    return keys.every((k) => this.c.get(k) === 1n);
  }

  override solve(opts: DiophantineSolveOptions = {}): DiophantineSolutionSet {
    this.preSolve(opts.parameters);
    const limit = opts.limit ?? 1;
    const v = this.freeSymbols;
    const pw = this.keys.find((k): k is Pow => k instanceof Pow);
    const p = asBig(defined(pw).exp);
    const n = -this.c.get(1);
    const result = new DiophantineSolutionSet(v, this.parameters);
    if (n < 0n || limit < 1) return result;
    const signs = varSigns(v);
    let took = 0;
    for (const t of powerRepresentation(n, p, v.length)) {
      result.add(t.map((j, i) => R(at(signs, i) * j)));
      took++;
      if (took === limit) break;
    }
    return result;
  }
}

type EquationClass = new (eq: ExprLike, freeSymbols?: readonly Sym[]) => DiophantineEquationType;

/** The known equation types, in the order they are tried. */
const ALL_DIOP_CLASSES: readonly EquationClass[] = [
  Linear,
  Univariate,
  BinaryQuadratic,
  InhomogeneousTernaryQuadratic,
  HomogeneousTernaryQuadraticNormal,
  HomogeneousTernaryQuadratic,
  InhomogeneousGeneralQuadratic,
  HomogeneousGeneralQuadratic,
  GeneralSumOfSquares,
  GeneralPythagorean,
  CubicThue,
  GeneralSumOfEvenPowers,
];

/** The matching equation type of eq (SymPy classify_diop with _dict=False). */
function classify(eq: ExprLike): DiophantineEquationType {
  for (const C of ALL_DIOP_CLASSES) {
    const t = new C(eq);
    if (t.matches()) return t;
  }
  throw new NotImplementedError('This equation is not yet recognized or else has not been simplified sufficiently to put it in a form recognized by diop_classify().');
}

/**
 * SymPy `classify_diop(eq)`: the variables, the coefficients (keyed by
 * monomial, the constant term by 1) and the type of the Diophantine equation.
 */
export function classifyDiop(eq: ExprLike): [Sym[], ExprMap<Expr>, string] {
  const t = classify(eq);
  return [[...t.freeSymbols], t.coeff, t.name];
}

// ---------------------------------------------------------------------------
// diophantine and diop_solve
// ---------------------------------------------------------------------------

const DEFAULT_PARAM = new Sym('t', { integer: true });

/** Options of {@link diophantine}. */
export interface DiophantineOptions {
  /** The parameter of the solutions (default `t`, integer). */
  param?: Sym;
  /** The order of the symbols in the solution tuples. */
  syms?: readonly Sym[];
  /** Also return the permutations of the values and/or signs where applicable. */
  permute?: boolean;
}

/**
 * SymPy `diophantine(eq)`: the integer solutions of a polynomial equation
 * (an expression assumed to be zero, or an equation), found by factoring it
 * and solving each factor with {@link diopSolve}. The result is the list of
 * solution tuples (a set in SymPy), in the alphabetic order of the variables.
 */
export function diophantine(eqIn: ExprLike, opts: DiophantineOptions = {}): Expr[][] {
  const param = opts.param ?? DEFAULT_PARAM;
  const permute = opts.permute ?? false;
  let eq = sympify(eqIn);
  if (eq instanceof Rel && eq.op === 'Eq') eq = sub(eq.lhs, eq.rhs);
  const notPoly = () => new TypeError('Equation should be a polynomial with Rational coefficients.');
  const v = sortedSymbols(expand(eq, { force: true }));
  if (opts.syms) {
    const varKeys = new Set(v.map((s) => s.key));
    const syms = opts.syms.filter((s) => varKeys.has(s.key));
    if (tupleKey(syms) !== tupleKey(v)) {
      const index = new Map(syms.map((s, i) => [s.key, i]));
      const out = new TupleSet();
      for (const t of diophantine(eq, { param, permute })) out.add(v.map((s) => at(t, defined(index.get(s.key)))));
      return out.sorted();
    }
  }
  const [n, d] = asNumerDenom(eq);
  if (isConst(n)) return [];
  if (!isConst(d)) {
    const dsol = new TupleSet();
    for (const s of diophantine(d)) dsol.add(s);
    const out = new TupleSet();
    for (const s of diophantine(n)) {
      if (dsol.has(s)) continue;
      const dv = mexpand(subs(d, v.map((sy, i) => [sy, at(s, i)] as [Expr, Expr])));
      if (!(dv instanceof Rational && dv.isZero)) out.add(s);
    }
    return out.sorted();
  }
  const p = Poly.from(asIndependent(factorTerms(n), v, { asAdd: false })[1]);
  if (p.gens.some((g) => isConst(g))) throw notPoly();
  eq = p.asExpr();
  if (!isPolynomial(eq)) throw notPoly();

  // permute only signs / signs and values / a few signs
  let doPermuteSigns = false;
  let doPermuteSignsVar = false;
  let permuteFewSigns = false;
  let terms: [Expr, Expr][];
  let t: DiophantineEquationType | undefined;
  try {
    t = classify(eq);
  } catch {
    t = undefined;
  }
  if (t && permute) {
    const tv = t.freeSymbols;
    const c = t.coeff;
    if (['general_sum_of_squares', 'general_sum_of_even_powers'].includes(t.name)) {
      doPermuteSignsVar = true;
    } else if (['homogeneous_ternary_quadratic', 'homogeneous_ternary_quadratic_normal', 'binary_quadratic'].includes(t.name) && (tv.length === 2 || tv.length === 3)) {
      // xyCoeff: every product of two variables has a coefficient; xCoeff: every variable has one
      const nz = (k: Expr) => {
        const cv = c.get(k);
        return cv !== undefined && !(cv instanceof Rational && cv.isZero);
      };
      const pairs: Expr[] = [];
      for (let i = 0; i < tv.length; i++) for (let j = i + 1; j < tv.length; j++) pairs.push(mul(at(tv, i), at(tv, j)));
      const xyCoeff = pairs.every(nz);
      const xCoeff = tv.every(nz);
      if (!xyCoeff && !xCoeff) doPermuteSigns = true;
      else if (!xCoeff) permuteFewSigns = true;
    }
  }
  if (t?.name === 'general_sum_of_squares') {
    // factoring such expressions sometimes hangs
    terms = [[eq, S.One]];
  } else {
    const fl = factorListExpr(eq);
    const [content] = fl;
    if (content instanceof Rational && content.key !== S.One.key) return diophantine(mul(eq, pow(content, -1)), opts);
    terms = fl[1];
  }

  const sols = new TupleSet();
  for (const [base0] of terms) {
    const tt = classify(base0);
    const base = coeffMul(signsimp(base0, false))[1];
    const solution = diopSolveImpl(base, param);
    if ('tuple' in solution) {
      const m = mergeSolution(v, tt.freeSymbols, solution.tuple);
      if (m.length) sols.add(m);
    } else {
      for (const s of solution.list) {
        const m = mergeSolution(v, tt.freeSymbols, s);
        if (m.length) sols.add(m);
      }
    }
  }
  const nul = v.map(() => S.Zero as Expr);
  // if there is no solution, return the trivial solution
  if (!sols.items.size) {
    const z = mexpand(subs(eq, v.map((s) => [s, S.Zero] as [Expr, Expr])));
    if (z instanceof Rational && z.isZero && v.every((s) => !contradictsAssumptions(S.Zero, s))) sols.add(nul);
  }
  const final = new TupleSet();
  for (const sol of sols.values()) {
    if (sol.every(isInt)) {
      if (doPermuteSigns) for (const s of permuteSigns(sol)) final.add(s);
      else if (permuteFewSigns) {
        const prod = mul(at(sol, 0), at(sol, 1)).key;
        for (const s of permuteSigns(sol)) if (mul(at(s, 0), at(s, 1)).key === prod) final.add(s);
      } else if (doPermuteSignsVar) for (const s of signedPermutations(sol)) final.add(s);
      else final.add(sol);
    } else final.add(sol);
  }
  return final.sorted();
}

/**
 * The full solution from the solution of a factor: variables that do not
 * occur in the factor get new integer parameters n1, n2, ... (SymPy
 * merge_solution); empty when there is no solution.
 */
function mergeSolution(v: readonly Sym[], varT: readonly Sym[], solution: readonly (Expr | null)[]): Expr[] {
  if (solution.some((s) => s === null)) return [];
  const it = solution[Symbol.iterator]();
  const params = numberedSymbols('n', { integer: true, start: 1 });
  const tk = new Set(varT.map((s) => s.key));
  const sol: Expr[] = v.map((s): Expr => (tk.has(s.key) ? defined(it.next().value) : params.next().value));
  if (sol.some((val, i) => contradictsAssumptions(val, at(v, i)))) return [];
  return sol;
}

/** The result of diop_solve: one parametric tuple (null entries for "no solution") or a list of solutions. */
type DiopResult = { tuple: (Expr | null)[] } | { list: Expr[][] };

/** diop_solve (internal). */
function diopSolveImpl(eq: Expr, param: Expr): DiopResult {
  const t = classify(eq);
  switch (t.name) {
    case 'linear':
      return { tuple: diopLinearImpl(eq, param) };
    case 'binary_quadratic':
      return { list: diopQuadraticImpl(eq, param) };
    case 'homogeneous_ternary_quadratic':
    case 'homogeneous_ternary_quadratic_normal':
      return { tuple: parametrizeTernary(firstOrNulls(diopTernaryQuadraticSet(t.freeSymbols, tCoeffs(t))), t.freeSymbols, tCoeffs(t)) };
    case 'general_pythagorean':
      return { tuple: diopGeneralPythagoreanImpl(eq, param) };
    case 'univariate':
      return { list: [...new Univariate(eq).solve()] };
    case 'general_sum_of_squares':
      return { list: [...new GeneralSumOfSquares(eq).solve({ limit: Infinity })] };
    case 'general_sum_of_even_powers':
      return { list: [...new GeneralSumOfEvenPowers(eq).solve({ limit: Infinity })] };
    default:
      throw new NotImplementedError(`No solver has been written for ${t.name}.`);
  }
}

/** The coefficients of an equation type (internal). */
const tCoeffs = (t: DiophantineEquationType): Coeffs => Coeffs.of([...t.coeff].map(([k, c]) => [k, asBig(c)] as const));

/** The solution list of a diop_solve result (a tuple is a list of one solution). */
const asSolutionList = (s: DiopResult): Expr[][] => ('list' in s ? s.list : [s.tuple.map((e) => defined(e))]);

/** A null tuple as EmptySet (the public form of "no solution"). */
const tupleOrEmpty = (s: readonly (Expr | null)[]): Expr[] | typeof EmptySet => (s.some((e) => e === null) ? EmptySet : s.map((e) => defined(e)));

/**
 * SymPy `diop_solve(eq, param)`: the solutions of a Diophantine equation
 * without factoring it. Linear, ternary quadratic and Pythagorean equations
 * give one parametric tuple (EmptySet when there is no solution); the other
 * types give the list of solution tuples.
 */
export function diopSolve(eq: ExprLike, param: Sym = DEFAULT_PARAM): Expr[] | Expr[][] | typeof EmptySet {
  const e = sympify(eq);
  const r = diopSolveImpl(e, param);
  return 'list' in r ? r.list : tupleOrEmpty(r.tuple);
}

function diopLinearImpl(eq: Expr, param: Expr | null): (Expr | null)[] {
  const v = classify(eq).freeSymbols;
  const parameters = param === null ? null : symbolsRange(`${str(param)}_`, 0, v.length);
  let result = new Linear(eq).solve({ parameters });
  if (param === null) result = result.call(...result.parameters.map(() => 0));
  for (const s of result) return s;
  return result.parameters.map(() => null);
}

/**
 * SymPy `diop_linear(eq, param)`: the parametric solution of a linear
 * Diophantine equation, in the sorted order of the variables; with `param`
 * null, the solution at parameters 0. EmptySet when there is no solution,
 * NoMatch when the equation is not linear.
 */
export function diopLinear(eq: ExprLike, param: Sym | null = DEFAULT_PARAM): Expr[] | typeof EmptySet | NoMatchResult {
  const e = sympify(eq);
  if (classify(e).name !== 'linear') return NoMatch;
  return tupleOrEmpty(diopLinearImpl(e, param));
}

/** baseSolutionLinear with null for "no solution" (internal). */
function baseSolutionLinearImpl(cIn: bigint, aIn: bigint, bIn: bigint, tIn: Expr | null): [Expr, Expr] | null {
  const [a, b, c] = removeGcd(aIn, bIn, cIn);
  if (c === 0n) {
    if (tIn === null) return [S.Zero, S.Zero];
    const t = b < 0n ? neg(tIn) : tIn;
    return [mul(b, t), mul(-a, t)];
  }
  const [d, x, y] = gcdext(babs(a), babs(b));
  const x0 = x * bsign(a);
  const y0 = y * bsign(b);
  if (c % d !== 0n) return null;
  if (tIn === null) return [R(c * x0), R(c * y0)];
  const t = b < 0n ? neg(tIn) : tIn;
  return [add(c * x0, mul(b, t)), sub(c * y0, mul(a, t))];
}

/**
 * SymPy `base_solution_linear(c, a, b, t)`: the base solution of
 * `a*x + b*y = c`, parametrized by `t` when given; EmptySet when there is none.
 */
export function baseSolutionLinear(c: ExprLike | bigint, a: ExprLike | bigint, b: ExprLike | bigint, t?: Expr): [Expr, Expr] | typeof EmptySet {
  return baseSolutionLinearImpl(asBig(c), asBig(a), asBig(b), t ?? null) ?? EmptySet;
}

/** SymPy `diop_univariate(eq)`: the integer roots of a univariate polynomial, as 1-tuples. */
export function diopUnivariate(eq: ExprLike): Expr[][] | NoMatchResult {
  const e = sympify(eq);
  const t = classify(e);
  if (t.name !== 'univariate') return NoMatch;
  return integerRoots(t.equation, first(t.freeSymbols)).map((i) => [R(i)]);
}

function diopQuadraticImpl(eq: Expr, param: Expr | null): Expr[][] {
  const parameters = param === null ? null : [param, new Sym('u', { integer: true })];
  return [...new BinaryQuadratic(eq).solve({ parameters })].sort(compareTuples);
}

/** SymPy `diop_quadratic(eq, param)`: the solutions of a binary quadratic Diophantine equation. */
export function diopQuadratic(eq: ExprLike, param: Sym | null = DEFAULT_PARAM): Expr[][] | NoMatchResult {
  const e = sympify(eq);
  if (classify(e).name !== 'binary_quadratic') return NoMatch;
  return diopQuadraticImpl(e, param);
}

/** The pair (u, v) solves the binary quadratic with the coefficients coeff (SymPy is_solution_quad). */
function isSolutionQuad(v: readonly Sym[], coeff: Coeffs, u: Expr, w: Expr): boolean {
  const reps: [Expr, Expr][] = [
    [at(v, 0), u],
    [at(v, 1), w],
  ];
  const e = mexpand(add(...[...coeff.map].map(([k, c]) => mul(c, xreplace(k, reps)))));
  return e instanceof Rational && e.isZero;
}

// ---------------------------------------------------------------------------
// The generalized Pell equation x**2 - D*y**2 = N
// ---------------------------------------------------------------------------

/** diop_DN for D < 0 or D > 0 not a square (internal; integers only). */
function diopDNInt(D: bigint, N: bigint): [bigint, bigint][] {
  if (D < 0n) {
    if (N === 0n) return [[0n, 0n]];
    if (N < 0n) return [];
    const sol: [bigint, bigint][] = [];
    for (const d of divisors(squareFactorInt(N))) {
      for (const [x, y] of cornacchiaImpl(1n, -D, N / d ** 2n)) {
        sol.push([d * x, d * y]);
        if (D === -1n) sol.push([d * y, d * x]);
      }
    }
    return sol;
  }
  const sD = isqrt(D);
  // much faster for small N
  if (1n < N ** 2n && N ** 2n < D) return specialDiopDN(D, N);
  if (N === 0n) return [[0n, 0n]];
  const sol: [bigint, bigint][] = [];
  if (babs(N) === 1n) {
    const pqa = PQa(0n, 1n, D);
    let [, , , , prevB, prevG] = defined(pqa.next().value);
    let j = 0;
    let brk: [bigint, bigint, bigint, bigint, bigint, bigint];
    for (;;) {
      brk = defined(pqa.next().value);
      if (brk[2] === 2n * sD) break;
      [prevB, prevG] = [brk[4], brk[5]];
      j++;
    }
    if (j % 2) {
      if (N === 1n) sol.push([prevG, prevB]);
      return sol;
    }
    if (N === -1n) return [[prevG, prevB]];
    // the values of the iteration that ended the loop, followed by j more
    let last = brk;
    for (let i = 0; i < j; i++) last = defined(pqa.next().value);
    return [[last[5], last[4]]];
  }
  for (const f of divisors(squareFactorInt(N))) {
    const m = N / f ** 2n;
    const am = babs(m);
    for (const sqm of sqrtMod(D, am, true)) {
      const z = symmetricResidue(sqm, am);
      const pqa = PQa(z, am, D);
      let [, , , , prevB, prevG] = defined(pqa.next().value);
      const len = lengthCF(z, am, D);
      for (let i = 0; i < len - 1; i++) {
        const [, q, , , B, G] = defined(pqa.next().value);
        if (babs(q) === 1n) {
          if (prevG ** 2n - D * prevB ** 2n === m) sol.push([f * prevG, f * prevB]);
          else {
            const a = diopDNInt(D, -1n);
            if (a.length) {
              const [a0, a1] = first(a);
              sol.push([f * (prevG * a0 + prevB * D * a1), f * (prevG * a1 + prevB * a0)]);
            }
          }
          break;
        }
        [prevB, prevG] = [B, G];
      }
    }
  }
  return sol;
}

/**
 * SymPy `diop_DN(D, N, t)`: one solution `(x, y)` of `x**2 - D*y**2 = N` for
 * each class of solutions (the LMM algorithm). When `D` is zero or a perfect
 * square with `N = 0` the solutions are parametrized by `t`.
 */
export function diopDN(DIn: ExprLike | bigint, NIn: ExprLike | bigint, t: Expr = DEFAULT_PARAM): Expr[][] {
  const D = asBig(DIn);
  const N = asBig(NIn);
  const ints = (xs: [bigint, bigint][]) => xs.map(([a, b]) => [R(a), R(b)]);
  if (D === 0n) {
    if (N < 0n) return [];
    if (N === 0n) return [[S.Zero, t]];
    const [sN, exact] = integerNthroot(N, 2);
    return exact ? [[R(sN), t]] : [];
  }
  if (D > 0n) {
    const [sD, exact] = integerNthroot(D, 2);
    if (exact) {
      if (N === 0n) return [[mul(sD, t), t]];
      const sol: Expr[][] = [];
      const top = fdiv(bsign(N) * (N - 1n), 2n * sD);
      for (let y = 0n; y <= top; y++) {
        const w = D * y ** 2n + N;
        if (w < 0n) continue;
        const [sq, ex] = integerNthroot(w, 2);
        if (ex) sol.push([R(sq), R(y)]);
      }
      return sol;
    }
  }
  return ints(diopDNInt(D, N));
}

/** x**2 - D*y**2 = N for 1 < N**2 < D and D not a square (SymPy _special_diop_DN). */
function specialDiopDN(D: bigint, N: bigint): [bigint, bigint][] {
  const sqrtD = isqrt(D);
  const F = new Map<bigint, bigint>();
  for (const f of divisors(squareFactorInt(babs(N)))) F.set(N / f ** 2n, f);
  let P = 0n;
  let Qn = 1n;
  let [G0, G1] = [0n, 1n];
  let [B0, B1] = [1n, 0n];
  const solutions: [bigint, bigint][] = [];
  for (;;) {
    for (let i = 0; i < 2; i++) {
      const a = fdiv(P + sqrtD, Qn);
      P = a * Qn - P;
      Qn = fdiv(D - P ** 2n, Qn);
      [G0, G1] = [G1, a * G1 + G0];
      [B0, B1] = [B1, a * B1 + B0];
      const f = F.get(G1 ** 2n - D * B1 ** 2n);
      if (f !== undefined) solutions.push([f * G1, f * B1]);
    }
    if (Qn === 1n) break;
  }
  return solutions;
}

function cornacchiaImpl(a: bigint, b: bigint, m: bigint): [bigint, bigint][] {
  const sols = new Map<string, [bigint, bigint]>();
  const put = (r: bigint, s: bigint) => sols.set(`${r},${s}`, [r, s]);
  if (a + b > m) {
    // xy = 0 must hold if there is a solution
    if (a === 1n) {
      const [s, exact] = iroot(m / a, 2n);
      if (exact) put(s, 0n);
      // only keep one solution
      if (a === b) return [...sols.values()];
    }
    if (m % b === 0n) {
      const [s, exact] = iroot(m / b, 2n);
      if (exact) put(0n, s);
    }
    return [...sols.values()];
  }
  for (const t of sqrtModIter(-b * invert(a, m), m)) {
    if (t < m / 2n) continue;
    let [u, r] = [m, t];
    let m1: bigint;
    while ((m1 = m - a * r ** 2n) <= 0n) [u, r] = [r, u % r];
    const [m2, rr] = divmod(m1, b);
    if (rr !== 0n) continue;
    const [s, exact] = iroot(m2, 2n);
    if (exact) {
      // with a == b only the solution with x >= y is kept
      const [hi, lo] = sortBig([r, s]).reverse();
      put(...(a === b ? [defined(hi), defined(lo)] as const : [r, s] as const));
    }
  }
  return [...sols.values()];
}

/**
 * SymPy `cornacchia(a, b, m)`: the primitive solutions of
 * `a*x**2 + b*y**2 = m` for `gcd(a, b) = gcd(a, m) = 1` and `a, b > 0`
 * (Cornacchia's algorithm); when `a = b` only those with `x >= y`.
 */
export function cornacchia(a: ExprLike | bigint, b: ExprLike | bigint, m: ExprLike | bigint): [bigint, bigint][] {
  return cornacchiaImpl(asBig(a), asBig(b), asBig(m));
}

/**
 * SymPy `PQa(P_0, Q_0, D)`: the sequences (P_i, Q_i, a_i, A_i, B_i, G_i) of
 * the continued fraction of `(P_0 + sqrt(D))/Q_0`.
 */
export function* PQa(P0: bigint, Q0: bigint, D: bigint): Generator<[bigint, bigint, bigint, bigint, bigint, bigint], never, undefined> {
  const sqD = isqrt(D);
  let [A2, B1] = [0n, 0n];
  let [A1, B2] = [1n, 1n];
  let G1 = Q0;
  let G2 = -P0;
  let Pi = P0;
  let Qi = Q0;
  for (;;) {
    const ai = fdiv(Pi + sqD, Qi);
    [A1, A2] = [ai * A1 + A2, A1];
    [B1, B2] = [ai * B1 + B2, B1];
    [G1, G2] = [ai * G1 + G2, G1];
    yield [Pi, Qi, ai, A1, B1, G1];
    Pi = ai * Qi - Pi;
    Qi = fdiv(D - Pi ** 2n, Qi);
  }
}

/**
 * SymPy `diop_bf_DN(D, N, t)`: the solutions of `x**2 - D*y**2 = N` by
 * brute force (for small `sqrt(|N|*(t +- 1)/(2*D))`).
 */
export function diopBfDN(DIn: ExprLike | bigint, NIn: ExprLike | bigint, t: Expr = DEFAULT_PARAM): Expr[][] {
  const D = asBig(DIn);
  const N = asBig(NIn);
  if (N === 0n) {
    if (D < 0n) return [[S.Zero, S.Zero]];
    if (D === 0n) return [[S.Zero, t]];
    const [sD, exact] = integerNthroot(D, 2);
    if (exact) return [[mul(sD, t), t], [mul(-sD, t), t]];
    return [[S.Zero, S.Zero]];
  }
  if (babs(N) === 1n) return diopDN(D, N);
  const u = asBig(first(first(diopDN(D, 1n))));
  let L1: bigint;
  let L2: bigint;
  // int(N*(u - 1)/(2*D)) truncates toward zero
  if (N > 1n) {
    L1 = 0n;
    L2 = integerNthroot((N * (u - 1n)) / (2n * D), 2)[0] + 1n;
  } else {
    let exact: boolean;
    [L1, exact] = integerNthroot(-(N / D), 2);
    if (!exact) L1 += 1n;
    L2 = integerNthroot(-((N * (u + 1n)) / (2n * D)), 2)[0] + 1n;
  }
  const sol: Expr[][] = [];
  for (let y = L1; y < L2; y++) {
    const w = N + D * y ** 2n;
    if (w < 0n) continue;
    const [x, exact] = integerNthroot(w, 2);
    if (exact) {
      sol.push([R(x), R(y)]);
      if (!equivalent(x, y, -x, y, D, N)) sol.push([R(-x), R(y)]);
    }
  }
  return sol;
}

/** The solutions (u, v) and (r, s) of x**2 - D*y**2 = N are in the same class (SymPy equivalent). */
function equivalent(u: bigint, v: bigint, r: bigint, s: bigint, D: bigint, N: bigint): boolean {
  return (u * r - D * v * s) % N === 0n && (u * s - v * r) % N === 0n;
}

/** The length of the aperiodic plus the periodic part of the continued fraction of (P + sqrt(D))/Q (SymPy length). */
function lengthCF(P: bigint, Qn: bigint, D: bigint): number {
  const v = continuedFractionPeriodic(P, Qn, D);
  // a quadratic irrational: the last element is the period
  const period = expectType(at(v, -1), (w): w is unknown[] => Array.isArray(w), 'period');
  return period.length + v.length - 1;
}

type RMat = [Rational, Rational, Rational, Rational];
type RVec = [Rational, Rational];
const rm = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.p, a.q * b.q);
const ra = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
const matMul = (m: RMat, n: RMat): RMat => [
  ra(rm(m[0], n[0]), rm(m[1], n[2])),
  ra(rm(m[0], n[1]), rm(m[1], n[3])),
  ra(rm(m[2], n[0]), rm(m[3], n[2])),
  ra(rm(m[2], n[1]), rm(m[3], n[3])),
];
const matVec = (m: RMat, v: RVec): RVec => [ra(rm(m[0], v[0]), rm(m[1], v[1])), ra(rm(m[2], v[0]), rm(m[3], v[1]))];

/** SymPy _transformation_to_DN on the coefficients a, b, c, d, e, f: [A, B] with (x, y) = A*(X, Y) + B. */
function transformationToDNImpl(a0: bigint, b0: bigint, c0: bigint, d0: bigint, e0: bigint, f0: bigint): [RMat, RVec] {
  const [a, b, c, d, e, f] = removeGcd(a0, b0, c0, d0, e0, f0);
  const one = S.One;
  if (b !== 0n) {
    const [B, C] = rationalPq(2n * a, b);
    const [A, T] = rationalPq(a, B ** 2n);
    // A*B*X**2 + B*(c*T - A*C**2)*Y**2 + d*T*X + (B*e*T - d*T*C)*Y + f*T*B
    const [A0, B0] = transformationToDNImpl(A * B, 0n, B * (c * T - A * C ** 2n), d * T, B * e * T - d * T * C, f * T * B);
    const M: RMat = [Rational.of(1n, B), Rational.of(-C, B), S.Zero, one];
    return [matMul(M, A0), matVec(M, B0)];
  }
  if (d !== 0n) {
    const [B, C] = rationalPq(2n * a, d);
    const [A, T] = rationalPq(a, B ** 2n);
    // A*X**2 + c*T*Y**2 + e*T*Y + f*T - A*C**2
    const [A0, B0] = transformationToDNImpl(A, 0n, c * T, 0n, e * T, f * T - A * C ** 2n);
    const M: RMat = [Rational.of(1n, B), S.Zero, S.Zero, one];
    const v = matVec(M, B0);
    return [matMul(M, A0), [ra(v[0], Rational.of(-C, B)), v[1]]];
  }
  if (e !== 0n) {
    const [B, C] = rationalPq(2n * c, e);
    const [A, T] = rationalPq(c, B ** 2n);
    // a*T*X**2 + A*Y**2 + f*T - A*C**2
    const [A0, B0] = transformationToDNImpl(a * T, 0n, A, 0n, 0n, f * T - A * C ** 2n);
    const M: RMat = [one, S.Zero, S.Zero, Rational.of(1n, B)];
    const v = matVec(M, B0);
    return [matMul(M, A0), [v[0], ra(v[1], Rational.of(-C, B))]];
  }
  return [[Rational.of(1n, a), S.Zero, S.Zero, one], [S.Zero, S.Zero]];
}

/** The binary quadratic type of eq with its six coefficients (internal). */
type Int6 = [bigint, bigint, bigint, bigint, bigint, bigint];

function binaryQuadraticCoeffs(eq: ExprLike): [BinaryQuadratic, Int6] | NoMatchResult {
  const t = classify(eq);
  if (!(t instanceof BinaryQuadratic)) return NoMatch;
  const [x, y] = pair(t.freeSymbols);
  const c = tCoeffs(t);
  return [t, [c.get(pow(x, 2)), c.get(mul(x, y)), c.get(pow(y, 2)), c.get(x), c.get(y), c.get(1)]];
}

/**
 * SymPy `transformation_to_DN(eq)`: matrices `A` (2x2) and `B` (2x1) such
 * that `(x, y) = A*(X, Y) + B` transforms the binary quadratic `eq` into
 * `X**2 - D*Y**2 = N`; NoMatch when `eq` is not a binary quadratic.
 */
export function transformationToDN(eq: ExprLike): [Matrix, Matrix] | NoMatchResult {
  const bq = binaryQuadraticCoeffs(eq);
  if (isNoMatch(bq)) return bq;
  const [A, B] = transformationToDNImpl(...(bq[1]));
  return [
    Matrix.of([
      [A[0], A[1]],
      [A[2], A[3]],
    ]),
    Matrix.of([[B[0]], [B[1]]]),
  ];
}

/** SymPy _find_DN: (D, N) of the equation X**2 - D*Y**2 = N equivalent to the binary quadratic. */
function findDNImpl(v: readonly Sym[], coeff: Coeffs): [bigint, bigint] {
  const [x, y] = pair(v);
  const X = new Sym('X', { integer: true });
  const Y = new Sym('Y', { integer: true });
  const [A, B] = transformationToDNImpl(coeff.get(pow(x, 2)), coeff.get(mul(x, y)), coeff.get(pow(y, 2)), coeff.get(x), coeff.get(y), coeff.get(1));
  const u = add(mul(A[0], X), mul(A[1], Y), B[0]);
  const w = add(mul(A[2], X), mul(A[3], Y), B[1]);
  const simplified = mexpand(subs(coeff.expr(), [[x, u], [y, w]], { simultaneous: true }));
  const cd = asCoefficientsDict(simplified);
  const cx = defined(cd.get(pow(X, 2)));
  const D = mul(neg(defined(cd.get(pow(Y, 2)))), pow(cx, -1));
  const N = mul(neg(cd.get(1) ?? S.Zero), pow(cx, -1));
  return [asBig(D), asBig(N)];
}

/**
 * SymPy `find_DN(eq)`: `(D, N)` of the equation `X**2 - D*Y**2 = N` the
 * binary quadratic `eq` is transformed into by {@link transformationToDN}.
 */
export function findDN(eq: ExprLike): [Rational, Rational] | NoMatchResult {
  const bq = binaryQuadraticCoeffs(eq);
  if (isNoMatch(bq)) return bq;
  const [D, N] = findDNImpl(bq[0].freeSymbols, tCoeffs(bq[0]));
  return [R(D), R(N)];
}

/**
 * The parametric solutions x, y in t made integral (SymPy check_param):
 * empty when no residue of t modulo a makes both integers.
 */
function checkParam(x: Expr, y: Expr, params: readonly Expr[] | null): DiophantineSolutionSet {
  if (isConst(x) && !isInt(x)) return new DiophantineSolutionSet([x, y], params ?? []);
  const m = new Sym('m', { integer: true });
  const n = new Sym('n', { integer: true });
  // the denominators of x and y divide 4*A*r: SymPy's test that some residue modulo it makes both integral always passes
  // clear_coefficients(m*x + b, R)[1] -> (R - b)/m
  const eq = sub(clearCoefficients(x, m), clearCoefficients(y, n));
  return classify(asContentPrimitive(eq)[1]).solve({ parameters: params });
}

/** The right-hand side after the rational coefficients of expr are moved over (SymPy clear_coefficients(expr, rhs)[1]). */
function clearCoefficients(exprIn: Expr, rhsIn: Expr): Expr {
  let expr = exprIn;
  let rhs = rhsIn;
  if (expr instanceof Rational) return sub(rhs, expr);
  let was: Expr | undefined;
  // expr has a free symbol, so it never becomes 0
  while (was?.key !== expr.key) {
    was = expr;
    const [m, e1] = asContentPrimitive(expr);
    rhs = mul(rhs, pow(m, -1));
    const [c, e2] = coeffAdd(e1);
    expr = e2;
    rhs = sub(rhs, c);
  }
  expr = signsimp(expr, false);
  return couldExtractMinusSign(expr) ? neg(rhs) : rhs;
}

// ---------------------------------------------------------------------------
// Ternary quadratic forms
// ---------------------------------------------------------------------------

/** The solution of a homogeneous ternary quadratic with the given variable order (SymPy _diop_ternary_quadratic). */
function diopTernaryQuadraticSet(v: readonly Sym[], coeff: Coeffs): DiophantineSolutionSet {
  const eq = coeff.expr();
  const H = new HomogeneousTernaryQuadratic(eq);
  if (H.matches()) return new HomogeneousTernaryQuadratic(eq, v).solve();
  const N = new HomogeneousTernaryQuadraticNormal(eq);
  if (N.matches()) return new HomogeneousTernaryQuadraticNormal(eq, v).solve();
  // SymPy fails here with a TypeError (the transformed equation has fewer variables)
  throw new NotImplementedError(`no solver for the ternary form ${str(eq)}`);
}

const firstOrNulls = (s: DiophantineSolutionSet): (Expr | null)[] => {
  for (const t of s) return t;
  return [null, null, null];
};

/** The ternary type of eq (internal). */
function ternaryType(eq: ExprLike, normalOnly = false): DiophantineEquationType | NoMatchResult {
  const t = classify(eq);
  const names = normalOnly ? ['homogeneous_ternary_quadratic_normal'] : ['homogeneous_ternary_quadratic', 'homogeneous_ternary_quadratic_normal'];
  return names.includes(t.name) ? t : NoMatch;
}

/**
 * SymPy `diop_ternary_quadratic(eq, parameterize)`: a base solution
 * `(x, y, z)` of `a*x**2 + b*y**2 + c*z**2 + d*x*y + e*y*z + f*x*z = 0`
 * (EmptySet when there is none); with `parameterize`, the parametrized
 * solution.
 */
export function diopTernaryQuadratic(eq: ExprLike, parameterize = false): Expr[] | typeof EmptySet | NoMatchResult {
  const t = ternaryType(eq);
  if (isNoMatch(t)) return t;
  const sol = firstOrNulls(diopTernaryQuadraticSet(t.freeSymbols, tCoeffs(t)));
  return tupleOrEmpty(parameterize ? parametrizeTernary(sol, t.freeSymbols, tCoeffs(t)) : sol);
}

/**
 * SymPy `parametrize_ternary_quadratic(eq)`: the parametrized general
 * solution (in the integer parameters p, q, r) of a homogeneous ternary
 * quadratic equation; EmptySet when it has only the trivial solution.
 */
export function parametrizeTernaryQuadratic(eq: ExprLike): Expr[] | typeof EmptySet | NoMatchResult {
  const t = ternaryType(eq);
  if (isNoMatch(t)) return t;
  return tupleOrEmpty(parametrizeTernary(firstOrNulls(diopTernaryQuadraticSet(t.freeSymbols, tCoeffs(t))), t.freeSymbols, tCoeffs(t)));
}

/** SymPy _parametrize_ternary_quadratic. */
function parametrizeTernary(solution: readonly (Expr | null)[], vIn: readonly Sym[], coeff: Coeffs): (Expr | null)[] {
  const [x0, y0, z0] = triple(solution);
  if (x0 === null || y0 === null || z0 === null) return [null, null, null];
  // with two zeros the equation reduces to k*X**2 == 0: only the trivial solution
  if (solution.filter((s) => s instanceof Rational && s.isZero).length >= 2) return [null, null, null];
  const v = [...vIn];
  if (x0 instanceof Rational && x0.isZero) {
    [v[0], v[1]] = [at(v, 1), at(v, 0)];
    const [yp, xp, zp] = triple(parametrizeTernary([y0, x0, z0], v, coeff));
    return [xp, yp, zp];
  }
  const [x, y, z] = triple(v);
  const r = new Sym('r', { integer: true });
  const p = new Sym('p', { integer: true });
  const q = new Sym('q', { integer: true });
  const eq = coeff.expr();
  const eq1 = mexpand(
    subs(
      eq,
      [
        [x, mul(r, x0)],
        [y, add(mul(r, y0), p)],
        [z, add(mul(r, z0), q)],
      ],
      { simultaneous: true },
    ),
  );
  const [A, B] = asIndependent(eq1, [r], { asAdd: true });
  const xs = mul(A, x0);
  const ys = sub(mul(A, y0), mexpand(mul(B, pow(r, -1), p)));
  const zs = sub(mul(A, z0), mexpand(mul(B, pow(r, -1), q)));
  return removeGcdExpr(xs, ys, zs);
}

/**
 * SymPy `diop_ternary_quadratic_normal(eq, parameterize)`: a solution of
 * `a*x**2 + b*y**2 + c*z**2 = 0` (EmptySet when there is none).
 */
export function diopTernaryQuadraticNormal(eq: ExprLike, parameterize = false): Expr[] | typeof EmptySet | NoMatchResult {
  const t = ternaryType(eq, true);
  if (isNoMatch(t)) return t;
  const sol = firstOrNulls(new HomogeneousTernaryQuadraticNormal(tCoeffs(t).expr(), t.freeSymbols).solve());
  return tupleOrEmpty(parameterize ? parametrizeTernary(sol, t.freeSymbols, tCoeffs(t)) : sol);
}

/** sqf_normal with steps (internal). */
function sqfNormalSteps(a: bigint, b: bigint, c: bigint): [Int3, Int3, Int3] {
  const ABC = removeGcd(a, b, c);
  const sq = triple(ABC.map(squareFactorInt));
  const sqf = triple(ABC.map((i, k) => i / at(sq, k) ** 2n));
  let [A, B, C] = sqf;
  const pc = igcd(A, B);
  A /= pc;
  B /= pc;
  const pa = igcd(B, C);
  B /= pa;
  C /= pa;
  const pb = igcd(A, C);
  // SymPy divides B (not C) by pb and multiplies it back: B is unchanged
  A /= pb;
  A *= pa;
  C *= pc;
  return [sq, sqf, [A, B, C]];
}

/**
 * SymPy `sqf_normal(a, b, c, steps)`: the pairwise prime square-free
 * coefficients of the normal form of `a*x**2 + b*y**2 + c*z**2 = 0`; with
 * `steps`, also the square factors and the square-free parts.
 */
export function sqfNormal(a: ExprLike | bigint, b: ExprLike | bigint, c: ExprLike | bigint, steps = false): Int3 | [Int3, Int3, Int3] {
  const r = sqfNormalSteps(asBig(a), asBig(b), asBig(c));
  return steps ? r : r[2];
}

const isFactorMap = (a: unknown): a is ReadonlyMap<bigint | number, bigint | number> => a instanceof Map;

function squareFactorInt(a: bigint): bigint {
  let r = 1n;
  for (const [p, e] of factorint(a)) r *= p ** (e / 2n);
  return r;
}

/**
 * SymPy `square_factor(a)`: the integer `c` with `a = c**2*k` for a
 * square-free `k`; `a` may be given by its factorization.
 */
export function squareFactor(a: ExprLike | bigint | ReadonlyMap<bigint | number, bigint | number>): bigint {
  if (isFactorMap(a)) {
    let r = 1n;
    for (const [p, e] of a) r *= BigInt(p) ** (BigInt(e) / 2n);
    return r;
  }
  return squareFactorInt(asBig(a));
}

/** SymPy reconstruct(A, B, z): z multiplied by the primes of gcd(A, B), which must be square-free. */
function reconstruct(A: bigint, B: bigint, zIn: bigint): bigint {
  let z = zIn;
  // A and B are square-free
  for (const p of factorint(igcd(A, B)).keys()) z *= p;
  return z;
}

function ldescentImpl(A: bigint, B: bigint): [bigint, bigint, bigint] | null {
  if (A === 0n || B === 0n) throw new RangeError('A and B must be non-zero integers');
  if (babs(A) > babs(B)) {
    const r = ldescentImpl(B, A);
    if (r === null) return null;
    const [w, y, x] = r;
    return [w, x, y];
  }
  if (A === 1n) return [1n, 1n, 0n];
  if (B === 1n) return [1n, 0n, 1n];
  // A == -1 as well
  if (B === -1n) return null;
  const r = sqrtMod(A, B);
  if (isNoMatch(r)) return null;
  const Qv = fdiv(r ** 2n - A, B);
  if (Qv === 0n) return [r, -1n, 0n];
  // the last divisor |Q| gives a square quotient
  const i = defined(divisors(Qv).find((k) => integerNthroot(babs(Qv) / k, 2)[1]));
  const d = integerNthroot(babs(Qv) / i, 2)[0];
  const B0 = bsign(Qv) * i;
  const sub0 = ldescentImpl(A, B0);
  // SymPy fails here with a TypeError
  if (sub0 === null) throw new NotImplementedError(`ldescent(${A}, ${B}): the descent to ldescent(${A}, ${B0}) found no solution`);
  const [W, X, Y] = sub0;
  return removeGcd(-A * X + r * W, r * X - W, Y * B0 * d);
}

/**
 * SymPy `ldescent(A, B)`: a non-trivial solution `(w, x, y)` of
 * `w**2 = A*x**2 + B*y**2` by Lagrange's method; EmptySet when there is none.
 */
export function ldescent(A: ExprLike | bigint, B: ExprLike | bigint): [bigint, bigint, bigint] | typeof EmptySet {
  return ldescentImpl(asBig(A), asBig(B)) ?? EmptySet;
}

function descentImpl(A: bigint, B: bigint): [bigint, bigint, bigint] {
  if (babs(A) > babs(B)) {
    const [x, y, z] = descentImpl(B, A);
    return [x, z, y];
  }
  if (B === 1n) return [1n, 0n, 1n];
  if (A === 1n) return [1n, 1n, 0n];
  if (B === -A) return [0n, 1n, 1n];
  if (B === A) {
    const [x, z, y] = descentImpl(-1n, A);
    return [A * y, z, x];
  }
  const w = sqrtMod(A, B);
  if (isNoMatch(w)) throw new RangeError(`no solution of x**2 = ${A}*y**2 + ${B}*z**2`);
  const [x0, z0] = gaussianReduceImpl(w, A, B);
  const t = fdiv(x0 ** 2n - A * z0 ** 2n, B);
  const t2 = squareFactorInt(t);
  const t1 = t / t2 ** 2n;
  const [x1, z1, y1] = descentImpl(A, t1);
  return removeGcd(x0 * x1 + A * z0 * z1, z0 * x1 + x0 * z1, t1 * t2 * y1);
}

/**
 * SymPy `descent(A, B)`: a non-trivial solution `(x, y, z)` of
 * `x**2 = A*y**2 + B*z**2` by Lagrange's descent with lattice reduction
 * (`A` and `B` must admit a solution).
 */
export function descent(A: ExprLike | bigint, B: ExprLike | bigint): [bigint, bigint, bigint] {
  return descentImpl(asBig(A), asBig(B));
}

function gaussianReduceImpl(w: bigint, aIn: bigint, b: bigint): [bigint, bigint] {
  const a = babs(aIn);
  const dot = (u: [bigint, bigint], v: [bigint, bigint]) => u[0] * v[0] + a * u[1] * v[1];
  let u: [bigint, bigint] = [b, 0n];
  let v: [bigint, bigint] = b * w >= 0n ? [w, 1n] : [-w, -1n];
  if (b ** 2n < w ** 2n + a) [u, v] = [v, u];
  let dv: bigint;
  while (dot(u, u) > (dv = dot(v, v))) {
    const k = fdiv(dot(u, v), dv);
    [u, v] = [v, [u[0] - k * v[0], u[1] - k * v[1]]];
  }
  const c: [bigint, bigint] = [v[0] - u[0], v[1] - u[1]];
  if (dot(c, c) <= dot(u, u) && dot(u, u) <= 2n * dot(u, v)) return c;
  return u;
}

/**
 * SymPy `gaussian_reduce(w, a, b)`: a reduced solution `(x, z)` of
 * `X**2 - a*Z**2 = 0 (mod b)` with `x**2 + |a|*z**2` small, where
 * `w**2 = a (mod b)`.
 */
export function gaussianReduce(w: ExprLike | bigint, a: ExprLike | bigint, b: ExprLike | bigint): [bigint, bigint] {
  return gaussianReduceImpl(asBig(w), asBig(a), asBig(b));
}

function holzerImpl(xIn: bigint, yIn: bigint, zIn: bigint, a: bigint, b: bigint, c: bigint): [bigint, bigint, bigint] {
  const k = isOdd(c) ? 2n * c : c / 2n;
  const small = a * b * c;
  let [x, y, z] = [xIn, yIn, zIn];
  let [x0, y0, z0] = [x, y, z];
  for (let step = 0; ; step++) {
    const [t1, t2, t3] = [a * x ** 2n, b * y ** 2n, c * z ** 2n];
    // check that it is a solution
    if (t1 + t2 !== t3) {
      if (step === 0) throw new RangeError('bad starting solution');
      break;
    }
    [x0, y0, z0] = [x, y, z];
    // Holzer condition
    if (t1 <= small && t2 <= small && t3 <= small) break;
    const uv = baseSolutionLinearImpl(k, y0, -x0, null);
    if (uv === null) break;
    const [u, v] = [asBig(uv[0]), asBig(uv[1])];
    const [p, q] = [-(a * u * x0 + b * v * y0), c * z0];
    let w: bigint;
    if (!isOdd(c)) w = nintOrFloor(p, q);
    else {
      w = fdiv(p, q);
      if (isOdd(a * u + b * v + c * w)) w += 1n;
    }
    const A = a * u ** 2n + b * v ** 2n + c * w ** 2n;
    const B = a * u * x0 + b * v * y0 + c * w * z0;
    [x, y, z] = [(x0 * A - 2n * u * B) / k, (y0 * A - 2n * v * B) / k, (z0 * A - 2n * w * B) / k];
  }
  return [x0, y0, z0];
}

/**
 * SymPy `holzer(x, y, z, a, b, c)`: the solution `(x, y, z)` of
 * `a*x**2 + b*y**2 = c*z**2` (`a, b, c > 0`) reduced to one with
 * `z**2 <= |a*b|` (Mordell's reduction).
 */
export function holzer(
  x: ExprLike | bigint,
  y: ExprLike | bigint,
  z: ExprLike | bigint,
  a: ExprLike | bigint,
  b: ExprLike | bigint,
  c: ExprLike | bigint,
): [bigint, bigint, bigint] {
  return holzerImpl(asBig(x), asBig(y), asBig(z), asBig(a), asBig(b), asBig(c));
}

// ---------------------------------------------------------------------------
// Pythagorean equations and sums of powers
// ---------------------------------------------------------------------------

function diopGeneralPythagoreanImpl(eq: Expr, param: Expr | null): Expr[] {
  const v = classify(eq).freeSymbols;
  const params = param === null ? null : symbolsRange(str(param), 1, v.length);
  return first([...new GeneralPythagorean(eq).solve({ parameters: params })]);
}

/**
 * SymPy `diop_general_pythagorean(eq, param)`: a parametrized solution of
 * `a_1**2*x_1**2 + ... + a_n**2*x_n**2 - a_{n+1}**2*x_{n+1}**2 = 0` in the
 * parameters `m1, m2, ...`.
 */
export function diopGeneralPythagorean(eq: ExprLike, param: Sym | null = new Sym('m', { integer: true })): Expr[] | NoMatchResult {
  const e = sympify(eq);
  if (classify(e).name !== 'general_pythagorean') return NoMatch;
  return diopGeneralPythagoreanImpl(e, param);
}

/** SymPy `diop_general_sum_of_squares(eq, limit)`: at most `limit` solutions of `x_1**2 + ... + x_n**2 - k = 0`. */
export function diopGeneralSumOfSquares(eq: ExprLike, limit = 1): Expr[][] | NoMatchResult {
  const e = sympify(eq);
  if (classify(e).name !== 'general_sum_of_squares') return NoMatch;
  return [...new GeneralSumOfSquares(e).solve({ limit })].sort(compareTuples);
}

/** SymPy `diop_general_sum_of_even_powers(eq, limit)`: at most `limit` solutions of `x_1**e + ... + x_n**e - k = 0`. */
export function diopGeneralSumOfEvenPowers(eq: ExprLike, limit = 1): Expr[][] | NoMatchResult {
  const e = sympify(eq);
  if (classify(e).name !== 'general_sum_of_even_powers') return NoMatch;
  return [...new GeneralSumOfEvenPowers(e).solve({ limit })].sort(compareTuples);
}

/** The partitions of n into k parts, padded with leading zeros when `zeros` (SymPy partition). */
function* partition(n: number, k: number, zeros: boolean): Generator<bigint[], void, undefined> {
  if (!zeros) {
    for (const i of orderedPartitions(n, k)) yield i.map(BigInt);
    return;
  }
  for (let m = 1; m <= k; m++) {
    for (const i of orderedPartitions(n, m)) yield [...Array.from({ length: k - i.length }, () => 0n), ...i.map(BigInt)];
  }
}

function primeAsSumOfTwoSquaresImpl(p: bigint): [bigint, bigint] | null {
  if (p % 4n !== 1n) return null;
  if (!isprime(p)) throw new RangeError('p should be a prime number');
  let b: bigint;
  // a quadratic non-residue b
  if (p % 8n === 5n) b = 2n;
  else if (p % 12n === 5n) b = 3n;
  else if (p % 5n === 2n || p % 5n === 3n) b = 5n;
  else {
    b = 7n;
    while (jacobi(b, p) === 1) b = nextprime(b);
  }
  b = powmod(b, p >> 2n, p);
  let a = p;
  while (b ** 2n > p) [a, b] = [b, a % b];
  return [a % b, b];
}

/**
 * SymPy `prime_as_sum_of_two_squares(p)`: the positive integers `(x, y)` with
 * `x**2 + y**2 = p` for a prime `p = 1 (mod 4)`; EmptySet for other primes.
 */
export function primeAsSumOfTwoSquares(p: ExprLike | bigint): [bigint, bigint] | typeof EmptySet {
  return primeAsSumOfTwoSquaresImpl(asBig(p)) ?? EmptySet;
}

const SPECIAL_THREE_SQUARES = new Map<bigint, [bigint, bigint, bigint]>(
  (
    [
      [1, [0, 0, 1]],
      [2, [0, 1, 1]],
      [3, [1, 1, 1]],
      [10, [0, 1, 3]],
      [34, [3, 3, 4]],
      [58, [0, 3, 7]],
      [85, [0, 6, 7]],
      [130, [0, 3, 11]],
      [214, [3, 6, 13]],
      [226, [8, 9, 9]],
      [370, [8, 9, 15]],
      [526, [6, 7, 21]],
      [706, [15, 15, 16]],
      [730, [0, 1, 27]],
      [1414, [6, 17, 33]],
      [1906, [13, 21, 36]],
      [2986, [21, 32, 39]],
      [9634, [56, 57, 57]],
    ] as const
  ).map(([n, t]) => [BigInt(n), [BigInt(t[0]), BigInt(t[1]), BigInt(t[2])]]),
);

const sortBig = (xs: bigint[]): bigint[] => xs.sort((p, q) => (p < q ? -1 : p > q ? 1 : 0));
const sort3 = (a: bigint, b: bigint, c: bigint): Int3 => triple(sortBig([a, b, c]));

function sumOfThreeSquaresImpl(nIn: bigint): [bigint, bigint, bigint] | null {
  if (nIn < 0n) throw new RangeError('n should be a non-negative integer');
  if (nIn === 0n) return [0n, 0n, 0n];
  const [n, e] = remove(nIn, 4n);
  const v = 1n << e;
  if (n % 8n === 7n) return null;
  const sp = SPECIAL_THREE_SQUARES.get(n);
  if (sp) return [v * sp[0], v * sp[1], v * sp[2]];
  let [s, exact] = integerNthroot(n, 2);
  if (exact) return [0n, 0n, v * s];
  if (n % 8n === 3n) {
    if (s % 2n === 0n) s -= 1n;
    for (let x = s; x >= 0n; x -= 2n) {
      const N = (n - x ** 2n) / 2n;
      if (isprime(N)) {
        // n % 8 == 3 and x odd => N % 4 == 1
        const [y, z] = defined(primeAsSumOfTwoSquaresImpl(N));
        return sort3(v * x, v * (y + z), v * babs(y - z));
      }
    }
  }
  // n % 4 in (1, 2)
  if ((n % 2n) === (s % 2n)) s -= 1n;
  for (let x = s; ; x -= 2n) {
    const N = n - x ** 2n;
    if (isprime(N)) {
      const [y, z] = defined(primeAsSumOfTwoSquaresImpl(N));
      return sort3(v * x, v * y, v * z);
    }
  }
}

/**
 * SymPy `sum_of_three_squares(n)`: sorted non-negative `(a, b, c)` with
 * `a**2 + b**2 + c**2 = n`; EmptySet when `n = 4**a*(8*m + 7)`.
 */
export function sumOfThreeSquares(n: ExprLike | bigint): [bigint, bigint, bigint] | typeof EmptySet {
  return sumOfThreeSquaresImpl(asBig(n)) ?? EmptySet;
}

/** SymPy `sum_of_four_squares(n)`: sorted non-negative `(a, b, c, d)` with `a**2 + b**2 + c**2 + d**2 = n`. */
export function sumOfFourSquares(nIn: ExprLike | bigint): [bigint, bigint, bigint, bigint] {
  const n0 = asBig(nIn);
  if (n0 < 0n) throw new RangeError('n should be a non-negative integer');
  if (n0 === 0n) return [0n, 0n, 0n, 0n];
  // factors of 4 are removed to select d
  let [n, e] = remove(n0, 4n);
  const v = 1n << e;
  let d: bigint;
  if (n % 8n === 7n) {
    d = 2n;
    n -= 4n;
  } else if (n % 8n === 2n || n % 8n === 6n) {
    d = 1n;
    n -= 1n;
  } else d = 0n;
  const [x, y, z] = defined(sumOfThreeSquaresImpl(n));
  const [a, b, c, e4] = sortBig([v * d, v * x, v * y, v * z]);
  return [defined(a), defined(b), defined(c), defined(e4)];
}

/** Options of {@link powerRepresentation} and {@link sumOfSquares}. */
export interface PowerRepresentationOptions {
  /** Allow zeros in the solutions (generated after those without zeros). */
  zeros?: boolean;
}

/**
 * SymPy `power_representation(n, p, k, zeros)`: the k-tuples of integers
 * `(n_1, ..., n_k)` with `n = n_1**p + ... + n_k**p`.
 */
export function* powerRepresentation(nIn: ExprLike | bigint, pIn: ExprLike | bigint, kIn: ExprLike | bigint | number, opts: PowerRepresentationOptions = {}): Generator<bigint[], void, undefined> {
  const zeros = opts.zeros ?? false;
  const n = asBig(nIn);
  const p = asBig(pIn);
  const k = typeof kIn === 'number' ? BigInt(kIn) : asBig(kIn);
  if (n < 0n) {
    if (isOdd(p)) for (const t of powerRepresentation(-n, p, k, opts)) yield t.map((i) => -i);
    return;
  }
  if (p < 1n || k < 1n) throw new RangeError(`Expecting positive integers for \`(p, k)\`, but got \`(${p}, ${k})\``);
  if (n === 0n) {
    if (zeros) yield Array.from({ length: Number(k) }, () => 0n);
    return;
  }
  if (k === 1n) {
    if (p === 1n) yield [n];
    else if (n === 1n) yield [1n];
    else {
      const be = perfectPower(n);
      if (be !== false) {
        const [b, e] = be;
        const [d, r] = divmod(e, p);
        if (r === 0n) yield [b ** d];
      }
    }
    return;
  }
  if (p === 1n) {
    yield* partition(Number(n), Number(k), zeros);
    return;
  }
  if (p === 2n) {
    if (k === 3n) {
      const [n1, e] = remove(n, 4n);
      if (e) {
        const v = 1n << e;
        for (const t of powerRepresentation(n1, p, k, opts)) yield t.map((i) => i * v);
        return;
      }
    }
    const feasible = canDoSumOfSquares(n, k);
    if (feasible === false) return;
    if (!zeros) {
      // Todd G. Will, "When Is n^2 a Sum of k Squares?"
      if (n > 33n && k >= 5n && k <= n && [13n, 10n, 7n, 5n, 4n, 2n, 1n].includes(n - k)) return;
      // A000534
      if (k === 4n && ([1n, 3n, 5n, 9n, 11n, 17n, 29n, 41n].includes(n) || [2n, 6n, 14n].includes(remove(n, 4n)[0]))) return;
      // A051952
      if (k === 3n && [1n, 2n, 5n, 10n, 13n, 25n, 37n, 58n, 85n, 130n].includes(n)) return;
    }
    // n is prime and k == 2
    if (feasible === 1) {
      yield defined(primeAsSumOfTwoSquaresImpl(n));
      return;
    }
  }
  if (k === 2n && p > 2n) {
    // Fermat: a**n + b**n = c**n has no solution for n > 2
    const be = perfectPower(n);
    if (be !== false && be[1] % p === 0n) return;
  }
  if (n >= k) {
    const a = integerNthroot(n - (k - 1n), Number(p))[0];
    for (const t of powRepRecursive(a, k, n, [], p)) yield [...t].reverse();
  }
  if (zeros) {
    const a = integerNthroot(n, Number(p))[0];
    for (let i = 1n; i < k; i++) {
      for (const t of powRepRecursive(a, i, n, [], p)) yield [...t, ...Array.from({ length: Number(k - i) }, () => 0n)].reverse();
    }
  }
}

function* powRepRecursive(ni: bigint, k: bigint, nRemaining: bigint, terms: readonly bigint[], p: bigint): Generator<bigint[], void, undefined> {
  // no solutions (ni and k are positive)
  if (nRemaining < k) return;
  if (k * ni ** p < nRemaining) return;
  if (k === 1n) {
    // the next term**p must equal nRemaining
    const [next, exact] = integerNthroot(nRemaining, Number(p));
    if (exact && next <= ni) yield [...terms, next];
    return;
  }
  for (let next = 1n; next <= ni; next++) {
    const residual = nRemaining - next ** p;
    if (residual < 0n) break;
    yield* powRepRecursive(next, k - 1n, residual, [...terms, next], p);
  }
}

/**
 * SymPy `sum_of_squares(n, k, zeros)`: the sorted k-tuples of non-negative
 * integers whose squares sum to `n`.
 */
export function* sumOfSquares(n: ExprLike | bigint, k: ExprLike | bigint | number, opts: PowerRepresentationOptions = {}): Generator<bigint[], void, undefined> {
  yield* powerRepresentation(n, 2n, k, opts);
}

/**
 * n is a sum of k squares (zeros allowed): true, false, or 1 when k == 2 and
 * n is a prime (SymPy _can_do_sum_of_squares).
 */
function canDoSumOfSquares(n: bigint, k: bigint): boolean | 1 {
  // n > 0 and k > 1 here
  if (k === 2n) {
    if (n === 1n || n === 2n) return true;
    if (isprime(n)) return n % 4n === 1n ? 1 : false;
    // no prime factor 4*k + 3 with an odd multiplicity
    return [...factorint(n)].every(([q, m]) => q % 4n !== 3n || m % 2n === 0n);
  }
  if (k === 3n) return remove(n, 4n)[0] % 8n !== 7n;
  // every number is a sum of 4 squares; for k > 4 the parts can be 0
  return true;
}
