// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Partial fraction decomposition (SymPy apart, undetermined
 * coefficients method).
 */

import { NotImplementedError } from '../core/errors';
import { at, defined, first } from '../core/guard';
import { apartFull } from './rootsum';
import type { Expr, ExprLike } from '../core/nodes';
import { Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { linearEqToMatrix, linsolve } from '../matrices/linsys';
import { rebuild as impl_rebuild } from '../core/traverse';
import { expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { Poly, factor, factorListInt, polyConstructionHooks, sortGens } from './sympoly';
import { ddmIrref } from './matrices/dense';

/** Options of apart: Bronstein's full decomposition, or the coefficient domain of the factorization. */
export interface ApartOptions {
  /** Bronstein's full decomposition over the algebraic closure (RootSum). */
  full?: boolean;
  /** The domain the denominator is factored over (QQ_I, QQ<sqrt(2)>, ...). */
  domain?: string;
  /** An algebraic extension to factor the denominator over. */
  extension?: readonly Expr[];
  /** Factor over the Gaussian rationals. */
  gaussian?: boolean;
}

/** The factors of the denominator over the requested domain, [content, [factor, multiplicity][]]. */
function domainFactors(Q: Expr, opts: ApartOptions): [Expr, [Expr, number][]] {
  const factored = factor(Q, { ...(opts.domain === undefined ? {} : { domain: opts.domain }), ...(opts.extension === undefined ? {} : { extension: opts.extension }), ...(opts.gaussian === undefined ? {} : { gaussian: opts.gaussian }) });
  let content: Expr = S.One;
  const factors: [Expr, number][] = [];
  for (const f of factored instanceof Mul ? factored.args : [factored]) {
    const [base, k] = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger ? [f.base, Number(f.exp.p)] : [f, 1];
    if (base.isNumber) content = mul(content, f);
    else factors.push([base, k]);
  }
  return [content, factors];
}

/** Partial fraction decomposition of a rational function in x. */
export function apart(fIn: ExprLike, xIn?: Sym, opts: ApartOptions = {}): Expr {
  const f = cancel(together(sympify(fIn)));
  let x = xIn;
  if (x === undefined) {
    const syms = [...f.freeSymbols()].filter((s) => s instanceof Sym);
    if (syms.length > 1) throw new NotImplementedError('multivariate partial fraction decomposition');
    // a constant is its own decomposition
    if (!syms.length) return f;
    x = first(syms);
  }
  // Bronstein's full decomposition over the algebraic closure (RootSum)
  if (opts.full) return apartFull(f, x);
  const [P, Q] = fraction(f);
  if (!Q.has(x)) return f;
  const Pp = Poly.from(P, [x]);
  const Qp = Poly.from(Q, [x]);
  // the remainder is nonzero: f is cancelled and Q depends on x
  const [qPoly, rPoly] = Pp.div(Qp);
  const quotient = qPoly.asExpr();
  const r = rPoly.asExpr();
  const gens = sortGens([...Q.freeSymbols()].filter((s) => s instanceof Sym));
  const overDomain = opts.domain !== undefined || opts.extension !== undefined || opts.gaussian !== undefined;
  const [content, factors0] = overDomain ? domainFactors(expandMul(Q), opts) : factorListInt(expandMul(Q), gens);
  let c: Expr = content;
  const factors: [Expr, number][] = [];
  for (const [g, k] of factors0) {
    if (g.has(x)) factors.push([g, k]);
    else c = mul(c, pow(g, k));
  }
  const Qx = mul(...factors.map(([g, k]) => pow(g, k)));
  const coefficientOptions = { domain: opts.domain, extension: opts.extension, gaussian: opts.gaussian };
  const denominator = overDomain ? Poly.from(Qx, [x], coefficientOptions) : undefined;
  // unknown numerators A_ij of degree deg(g) - 1
  const unknowns: Sym[] = [];
  const terms: [Expr, Expr][] = []; // [numerator, denominator]
  let rhs: Expr = S.Zero;
  let idx = 0;
  for (const [g, k] of factors) {
    const d = Poly.from(g, [x]).degree();
    for (let j = 1; j <= k; j++) {
      const coeffs: Sym[] = [];
      for (let m = 0; m < d; m++) coeffs.push(new Sym(`_apart${idx++}`));
      unknowns.push(...coeffs);
      const A = add(...coeffs.map((a, m) => mul(a, pow(x, m))));
      terms.push([A, pow(g, j)]);
      const cofactor = denominator === undefined ? cancel(mul(Qx, pow(pow(g, j), -1))) : denominator.exquo(Poly.from(pow(g, j), [x], coefficientOptions)).asExpr();
      rhs = add(rhs, mul(A, cofactor));
    }
  }
  const lhs = mul(r, pow(c, -1));
  const diffPoly = Poly.from(expandMul(add(rhs, mul(-1, lhs))), [x]);
  const eqs = diffPoly.coeffs();
  // the partial fraction decomposition exists and is unique
  let sol: Expr[];
  if (overDomain) {
    const [A, b] = defined(linearEqToMatrix(eqs, unknowns), 'linear partial fraction system');
    const rows = A.hstack(b).toArray();
    const K = defined(polyConstructionHooks.domain, 'polynomial domain construction')(rows.flat(), { extension: true }).getField();
    const pivots = ddmIrref(rows, false, K);
    const solution = new Map(pivots.map((column, i) => [column, at(at(rows, i), unknowns.length)]));
    sol = unknowns.map((_, i) => defined(solution.get(i), 'partial fraction coefficient'));
  } else sol = defined(linsolve(eqs, unknowns), 'partial fraction coefficients');
  const reps = new Map(unknowns.map((u, i) => [u.key, at(sol, i)]));
  const sub = (e: Expr): Expr => {
    const rep = e instanceof Sym ? reps.get(e.key) : undefined;
    if (rep !== undefined) return rep;
    if (e.args.length === 0) return e;
    return impl_rebuild(e, e.args.map(sub));
  };
  // SymPy: each partial fraction is factored
  const parts = terms.map(([A, D]) => factor(mul(cancel(sub(A)), pow(D, -1))));
  return add(quotient, ...parts);
}

