// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy RootSum (sum of a function over the roots of a polynomial) and
 * Bronstein's full partial fraction decomposition (apart(full=True),
 * apart_list, assemble_partfrac_list).
 */

import { at, cast, defined, first, pair } from '../core/guard';
import type { ExprLike, Substitution } from '../core/nodes';
import { Add, Dummy, Expr, ExtensionExpr, Mul, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { subs, xreplace } from '../core/traverse';
import { asIndependent } from '../core/methods';
import { Lambda, LambdaNode } from '../core/lambda';
import { SymFunction } from '../core/undef';
import { diff } from '../calculus/diff';
import { cancel, fraction, together } from '../simplify/rational';
import { expandMul } from '../simplify/expand';
import { roots } from './poly';
import { Poly, PolificationFailed, factor, factorListExpr, preprocessRoots } from './sympoly';
import { NotImplementedError, NotInvertible } from '../core/errors';
import { NoMatch, isNoMatch, type NoMatchResult } from '../core/truth';

/**
 * A symbolic sum of a function evaluated at each root of a polynomial.
 *
 * @see SymPy `sympy.polys.rootoftools.RootSum`
 */
export class RootSumNode extends ExtensionExpr {
  /**
   * Construct a symbolic sum over polynomial roots.
   *
   * @param args - Polynomial expression, function and bound polynomial variable, in that order.
   * @param auto - Enable automatic simplification when rebuilding or differentiating the sum.
   */
  constructor(args: readonly Expr[],
    /** Whether automatic root-sum simplification is enabled. @see SymPy `sympy.polys.rootoftools.RootSum.auto` */
    readonly auto = false) {
    super('RootSum', args);
  }
  /**
   * Identifies the polynomial whose roots are summed over.
   *
   * @returns The defining polynomial expression.
   * @see SymPy `sympy.polys.rootoftools.RootSum.poly`
   */
  get poly(): Expr {
    return at(this.args, 0);
  }
  /**
   * Identifies the function summed over the polynomial's roots.
   *
   * @returns The root-sum lambda.
   * @see SymPy `sympy.polys.rootoftools.RootSum.fun`
   */
  get fun(): LambdaNode {
    return cast(at(this.args, 1), LambdaNode, 'RootSum function');
  }
  /**
   * Identifies the indeterminate bound by the root sum.
   *
   * @returns The polynomial variable.
   */
  get variable(): Expr {
    return at(this.args, 2);
  }
  /**
   * Rebuild the root sum with replacement arguments.
   *
   * @param args - Polynomial expression, function and bound polynomial variable, in that order.
   * @returns A root sum with the new arguments and the same simplification setting.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new RootSumNode(args, this.auto);
  }
  /**
   * Describes the scope of each variable bound in the root sum.
   *
   * @returns The variable bindings.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [2], scope: [0] };
  }
  /** The printed arguments: the polynomial, and the function unless it is the identity (SymPy). */
  private printArgs(print: (e: Expr) => string): string {
    const f = this.fun;
    return f.expr.key === first(f.variables).key ? print(this.poly) : `${print(this.poly)}, ${print(f)}`;
  }
  /**
   * Format the root sum as a string.
   *
   * @param print - Printer for the expression's arguments.
   * @returns The printed root sum.
   */
  override printStr(print: (e: Expr) => string): string {
    return `RootSum(${this.printArgs(print)})`;
  }
  /**
   * Format the root sum in LaTeX.
   *
   * @param print - Printer for the expression's arguments.
   * @returns The LaTeX representation of the root sum.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{RootSum} {\\left(${this.printArgs(print)}\\right)}`;
  }
  /**
   * Evaluates the function at roots expressible in radicals and sums the contributions.
   *
   * @returns The evaluated root sum.
   */
  override doitSelf(): Expr {
    try {
      return add(...roots(this.poly, cast(this.variable, Sym, 'RootSum variable')).map((r) => this.fun.call(r)));
    } catch (error) {
      if (error instanceof NotImplementedError) return this;
      throw error;
    }
  }
  /**
   * Differentiates the sum of the function values over the polynomial roots.
   *
   * @param x - Variable of differentiation.
   * @param d - Function for differentiating a subexpression with respect to a variable.
   * @returns The root-sum derivative.
   * @see SymPy `sympy.polys.rootoftools.RootSum._eval_derivative`
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (this.poly.has(x) && this.variable.key !== x.key) return undefined;
    const fun = this.fun;
    return RootSum(this.poly, cast(this.variable, Sym), Lambda(first(fun.variables), d(fun.expr, x)), { auto: this.auto });
  }
  /**
   * Apply the indicated substitutions to the root sum.
   *
   * @param s - Substitutions to apply to the root sum.
   * @returns The expression after substitution.
   * @throws TypeError when the replacement expression is absent.
   * @see SymPy `sympy.polys.rootoftools.RootSum.subs`
   */
  override subs(s: Substitution): Expr;
  /**
   * Apply the indicated substitutions to the root sum.
   *
   * @param from - Expression to replace.
   * @param to - Replacement expression.
   * @returns The expression after substitution.
   * @throws TypeError when the replacement expression is absent.
   * @see SymPy `sympy.polys.rootoftools.RootSum.subs`
   */
  override subs(from: Expr | string, to: ExprLike): Expr;
  override subs(from: Substitution | Expr | string, to?: ExprLike): Expr {
    if (typeof from === 'string') return this.subs(new Sym(from), defined(to, 'subs replacement'));
    if (!(from instanceof Expr)) return super.subs(from);
    if (to === undefined) throw new TypeError('subs(from, to) requires a replacement');
    const replacement = sympify(to);
    if (from.key === this.variable.key && replacement instanceof Sym) {
      return new RootSumNode([xreplace(this.poly, [[from, replacement]]), subs(this.fun, [[from, replacement]]), replacement], this.auto);
    }
    return super.subs(from, replacement);
  }
}


/**
 * Sums a function over the polynomial's roots, evaluating linear factors and extracting constant parts.
 *
 * @param polyIn - Polynomial to represent or transform.
 * @param x - Polynomial generator.
 * @param fun - Function to evaluate at each root.
 * @param opts - Controls `auto` (automatic simplification), `quadratic` (evaluation of quadratic root sums).
 * @returns The sum of the function values over the roots, simplified when possible.
 * @see SymPy `sympy.polys.rootoftools.RootSum`
 */
export function RootSum(polyIn: ExprLike, x: Sym, fun: LambdaNode, opts: { auto?: boolean; quadratic?: boolean } = {}): Expr {
  const poly = sympify(polyIn);
  const P = Poly.from(poly, [x]);
  const deg = P.degree();
  const v = first(fun.variables);
  if (deg <= 0) return S.Zero;
  const [scale, normalized] = opts.auto ? preprocessRoots(P) : [S.One, P];
  let body = scale.equals(S.One) ? fun.expr : fun.call(mul(v, scale));
  if (!body.has(v)) return mul(deg, body);
  let addConst: Expr = S.Zero;
  if (body.kind === 'Add') {
    const [ind, dep] = asIndependent(body, [v], { asAdd: true });
    addConst = ind;
    body = dep;
  }
  let mulConst: Expr = S.One;
  if (body instanceof Mul) {
    const [ind, dep] = asIndependent(body, [v]);
    mulConst = ind;
    body = dep;
  }
  const f = Lambda(v, body);
  const terms: Expr[] = [];
  // the factors over the integers in all symbols (SymPy factors over ZZ[t]); those free of x have no roots
  for (const [ge, k] of factorListExpr(normalized.asExpr())[1]) {
    if (!ge.has(x)) continue;
    const g = Poly.from(ge, [x]);
    if (g.degree() === 1) {
      const [c1, c0] = pair(g.allCoeffs());
      terms.push(mul(k, f.call(mul(-1, c0, pow(c1, -1)))));
    } else if (g.degree() === 2 && opts.quadratic) {
      terms.push(mul(k, add(...roots(g.asExpr(), x).map((r) => f.call(r)))));
    } else {
      const sum = opts.auto ? rationalRootSum(g, f) : NoMatch;
      terms.push(mul(k, isNoMatch(sum) ? new RootSumNode([g.asExpr(), f, x], opts.auto === true) : sum));
    }
  }
  return add(mul(mulConst, add(...terms)), mul(deg, addConst));
}

/** Trace of the rational function in the polynomial quotient algebra. */
function rationalRootSum(g: Poly, fun: LambdaNode): Expr | NoMatchResult {
  const t = new Dummy('r');
  const [numerator, denominator] = fraction(together(fun.call(t)));
  const asPoly = (e: Expr): Poly => Poly.from(e, [t], { domain: 'EX' });
  let value: Poly;
  const f = asPoly(xreplace(g.asExpr(), [[g.gen, t]])).monic();
  try {
    const p = asPoly(numerator), q = asPoly(denominator);
    value = q.isGround ? p.mulGround(pow(q.TC(), -1)).rem(f) : p.mul(q.invert(f)).rem(f);
  } catch (error) {
    if (error instanceof PolificationFailed || error instanceof NotInvertible) return NoMatch;
    throw error;
  }
  const n = f.degree();
  const sums: Expr[] = [Rational.of(n)];
  for (let k = 1; k < n; k++) {
    const terms = [mul(k, f.nth(n - k))];
    for (let j = 1; j < k; j++) terms.push(mul(f.nth(n - j), at(sums, k - j)));
    sums.push(cancel(mul(-1, add(...terms))));
  }
  return cancel(add(...value.terms().map(([m, c]) => mul(c, at(sums, first(m))))));
}

/** A fraction with integer coefficients in numerator and denominator: -t/(2*(t - 1/4)) -> -2*t/(4*t - 1). */
function clearedFraction(c: Expr): Expr {
  const [n, d] = fraction(cancel(c));
  if (!d.freeSymbols().size) return cancel(c);
  const ne = expandMul(n);
  const de = expandMul(d);
  let l = 1n;
  const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
  for (const t of [...(ne.kind === 'Add' ? ne.args : [ne]), ...(de.kind === 'Add' ? de.args : [de])]) {
    const k = t instanceof Rational ? t : t instanceof Mul && t.args[0] instanceof Rational ? t.args[0] : undefined;
    if (k) l = (l * k.q) / g(l, k.q);
  }
  return mul(expandMul(mul(ne, l)), pow(expandMul(mul(de, l)), -1));
}

/** One term of apart_list: [D(w) or the explicit roots, numerator Lambda, denominator Lambda, exponent]. */
export type PartfracTerm = [Expr | Expr[], LambdaNode, LambdaNode, number];

/**
 * Decomposes a rational function into Bronstein's structured partial fractions.
 *
 * @param fIn - Polynomial to operate on.
 * @param x - Polynomial generator.
 * @returns The common factor, polynomial part, rational terms, and variable.
 * @see SymPy `sympy.polys.partfrac.apart_list`
 * @example
 * ```ts
 * import { apartList, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * apartList(ex`(2*x**3 - 2*x)/(x - 1)**2`, x)[1].asExpr(); // => 2*x + 4
 * ```
 */
export function apartList(fIn: ExprLike, x: Sym): [Expr, Poly, PartfracTerm[], Sym] {
  const f = cancel(together(sympify(fIn)));
  const [num, den] = fraction(f);
  const numerator = Poly.from(num, [x]);
  // Poly.cancel extracts the sign of the numerator's leading coefficient
  // into the ground-field coefficient of the structured decomposition.
  const lc = numerator.LC();
  const common = lc instanceof Rational && lc.isNegative ? S.NegOne : S.One;
  const P0 = Poly.from(mul(common, num), [x]);
  const Q = Poly.from(den, [x]);
  const [polyPart, P] = P0.divAuto(Q);
  const w = new Dummy('w');
  const a = new Dummy('a');
  const u = SymFunction('u')(x);
  const U = (k: number): Expr => (k === 0 ? u : diff(u, x, k));
  const out: PartfracTerm[] = [];
  for (const [d, n] of Q.sqfListInclude()) {
    if (d.degree() < 1) continue;
    const b = d.asExpr();
    const h = mul(cancel(mul(P.asExpr(), pow(Q.quo(d.pow(n)).asExpr(), -1))), pow(u, -n));
    const H: Expr[] = [h];
    for (let j = 1; j < n; j++) H.push(mul(diff(at(H, j - 1), x), Rational.of(1, j)));
    const subs: [Expr, Expr][] = [];
    for (let j = 1; j <= n; j++) subs.push([U(j - 1), mul(diff(b, x, j), Rational.of(1, j))]);
    for (let j = 0; j < n; j++) {
      let [p, q] = fraction(cancel(at(H, j)));
      for (let i = 0; i <= j; i++) p = p.subs([at(subs, j - i)]);
      q = q.subs([at(subs, 0)]);
      const Pp = Poly.from(p, [x]);
      const Qp = Poly.from(q, [x]);
      const G = Pp.gcd(d);
      const D = d.quo(G);
      const [B, g] = Qp.halfGcdex(D);
      const bb = Pp.mul(B.quo(g)).rem(D);
      const Dw = xreplace(D.asExpr(), [[x, w]]);
      // coefficients as cancelled fractions (SymPy's ground field of rational functions)
      const numer = add(...bb.terms().map(([m, c]) => mul(clearedFraction(c), pow(a, first(m)))));
      out.push([Dw, Lambda(a, numer), Lambda(a, add(x, mul(-1, a))), n - j]);
    }
  }
  return [common, polyPart, out, w];
}

/**
 * Reconstructs a rational expression from its structured partial fractions.
 *
 * @param list - Partial fraction decomposition from `apartList`.
 * @returns The assembled expression.
 * @see SymPy `sympy.polys.partfrac.assemble_partfrac_list`
 * @example
 * ```ts
 * import { apartList, assemblePartfracList, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * assemblePartfracList(apartList(ex`(2*x**3 - 2*x)/(x - 1)**2`, x)); // => 2*x + 4 + 4/(x - 1)
 * ```
 */
export function assemblePartfracList(list: [Expr, Poly, PartfracTerm[], Sym]): Expr {
  const [common, polyPart, terms, w] = list;
  const parts: Expr[] = [polyPart.asExpr()];
  for (const [r, nf, df, ex] of terms) {
    const a = first(nf.variables);
    const de = xreplace(df.expr, [[first(df.variables), a]]);
    const fun = Lambda(a, mul(nf.expr, pow(de, -ex)));
    if (Array.isArray(r)) parts.push(...r.map((root) => fun.call(root)));
    else parts.push(RootSum(r, w, fun));
  }
  return mul(common, add(...parts));
}

const hasRootSum = (e: Expr): boolean => e instanceof RootSumNode || e.args.some(hasRootSum);

/** SymPy apart(f, x, full=True): the terms without a RootSum are factored (as one fraction, like SymPy's factor). */
export function apartFull(f: ExprLike, x: Sym): Expr {
  const r = assemblePartfracList(apartList(f, x));
  return add(...(r instanceof Add ? r.args : [r]).map((t) => (hasRootSum(t) ? t : factor(together(t)))));
}
