// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy RootSum (sum of a function over the roots of a polynomial) and
 * Bronstein's full partial fraction decomposition (apart(full=True),
 * apart_list, assemble_partfrac_list).
 */

import { at, cast, first, pair } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, ExtensionExpr, Mul, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { asIndependent } from '../core/methods';
import { Lambda, LambdaNode } from '../core/lambda';
import { SymFunction } from '../core/undef';
import { diff } from '../calculus/diff';
import { cancel, fraction, together } from '../simplify/rational';
import { expandMul } from '../simplify/expand';
import { roots } from './poly';
import { Poly, factor, factorListExpr } from './sympoly';

/** RootSum(poly, Lambda): args are [poly expression, Lambda, polynomial variable]. */
export class RootSumNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('RootSum', args);
  }
  get poly(): Expr {
    return at(this.args, 0);
  }
  get fun(): LambdaNode {
    return cast(at(this.args, 1), LambdaNode, 'RootSum function');
  }
  get variable(): Expr {
    return at(this.args, 2);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new RootSumNode(args);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [2], scope: [0] };
  }
  /** The printed arguments: the polynomial, and the function unless it is the identity (SymPy). */
  private printArgs(print: (e: Expr) => string): string {
    const f = this.fun;
    return f.expr.key === first(f.variables).key ? print(this.poly) : `${print(this.poly)}, ${print(f)}`;
  }
  override printStr(print: (e: Expr) => string): string {
    return `RootSum(${this.printArgs(print)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{RootSum} {\\left(${this.printArgs(print)}\\right)}`;
  }
  /** The sum over the roots (in radicals). */
  override doitSelf(): Expr {
    return add(...roots(this.poly, cast(this.variable, Sym, 'RootSum variable')).map((r) => this.fun.call(r)));
  }
}

/**
 * SymPy RootSum(poly, func, auto=False): linear factors of the polynomial are
 * evaluated, constant parts of the function are taken out.
 */
export function RootSum(polyIn: ExprLike, x: Sym, fun: LambdaNode): Expr {
  const poly = sympify(polyIn);
  const P = Poly.from(poly, [x]);
  const deg = P.degree();
  const v = first(fun.variables);
  let body = fun.expr;
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
  for (const [ge, k] of factorListExpr(poly)[1]) {
    if (!ge.has(x)) continue;
    const g = Poly.from(ge, [x]);
    if (g.degree() === 1) {
      const [c1, c0] = pair(g.allCoeffs());
      terms.push(mul(k, f.call(mul(-1, c0, pow(c1, -1)))));
    } else {
      terms.push(mul(k, new RootSumNode([g.asExpr(), f, x])));
    }
  }
  return add(mul(mulConst, add(...terms)), mul(deg, addConst));
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

/** SymPy apart_list(f, x): [common factor, polynomial part, rational terms] (Bronstein). */
export function apartList(fIn: ExprLike, x: Sym): [Expr, Poly, PartfracTerm[], Sym] {
  const f = cancel(together(sympify(fIn)));
  const [num, den] = fraction(f);
  const P0 = Poly.from(num, [x]);
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
  return [S.One, polyPart, out, w];
}

/** SymPy assemble_partfrac_list: the expression from an apart_list result. */
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
