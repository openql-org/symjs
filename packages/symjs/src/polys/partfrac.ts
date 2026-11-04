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
import { S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { linsolve } from '../matrices/linsys';
import { rebuild as impl_rebuild } from '../core/traverse';
import { expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { Poly, factor, factorListInt, sortGens } from './sympoly';

/** Partial fraction decomposition of a rational function in x. */
export function apart(fIn: ExprLike, xIn?: Sym, opts: { full?: boolean } = {}): Expr {
  const f = cancel(together(sympify(fIn)));
  let x = xIn;
  if (x === undefined) {
    const syms = [...f.freeSymbols()];
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
  const gens = sortGens([...Q.freeSymbols()]);
  const [content, factors0] = factorListInt(expandMul(Q), gens);
  let c: Expr = content;
  const factors: [Expr, number][] = [];
  for (const [g, k] of factors0) {
    if (g.has(x)) factors.push([g, k]);
    else c = mul(c, pow(g, k));
  }
  const Qx = mul(...factors.map(([g, k]) => pow(g, k)));
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
      rhs = add(rhs, mul(A, cancel(mul(Qx, pow(pow(g, j), -1)))));
    }
  }
  const lhs = mul(r, pow(c, -1));
  const diffPoly = Poly.from(expandMul(add(rhs, mul(-1, lhs))), [x]);
  const eqs = diffPoly.coeffs();
  // the partial fraction decomposition exists and is unique
  const sol = defined(linsolve(eqs, unknowns), 'partial fraction coefficients');
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

