// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Systems of linear first-order ODEs with constant coefficients
 * (SymPy dsolve for systems, the linear constant-coefficient case):
 * x' = A*x + b(t). The homogeneous solutions come from the Jordan form of A
 * (real solutions Re/Im for complex eigenvalue pairs), the particular
 * solution from variation of parameters.
 */

import { Derivative, Dummy, Expr, ExprLike, I, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { Eq } from '../core/logic';
import { cos, im, re, sin } from '../functions/elementary';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { jordanForm } from '../matrices/linalg';
import { linearEqToMatrix } from './solve';

const isZero = (e: Expr) => e instanceof Rational && e.isZero;

/** SymPy dsolve([eq1, eq2, ...], [f(t), g(t), ...]) for x' = A*x + b(t) with constant A. */
export function dsolveSystem(eqsIn: readonly ExprLike[], funcsIn?: readonly UndefFn[]): Expr[] {
  const eqs = eqsIn.map((e) => {
    const x = sympify(e);
    return x instanceof Rel && x.op === 'Eq' ? add(x.lhs, mul(-1, x.rhs)) : x;
  });
  const funcs = funcsIn ?? findFunctions(eqs);
  const n = funcs.length;
  if (n === 0 || eqs.length !== n) throw new Error('dsolve: as many equations as functions are needed');
  const t = funcs[0]!.args[0] as Sym;
  // replace derivatives and functions by symbols, then read the coefficients
  const ds = funcs.map((_, i) => new Dummy(`d${i}`));
  const us = funcs.map((_, i) => new Dummy(`u${i}`));
  const reps: [Expr, Expr][] = [
    ...funcs.map((f, i) => [new Derivative([f, t, S.One]), ds[i]!] as [Expr, Expr]),
    ...funcs.map((f, i) => [f, us[i]!] as [Expr, Expr]),
  ];
  const sub = eqs.map((e) => xreplace(e, reps));
  const lin = linearEqToMatrix(sub, [...ds, ...us]);
  if (!lin) throw new Error('dsolve: only linear first-order systems are supported');
  const [M, rhs] = lin;
  const Md = Matrix.fromFunction(n, n, (i, j) => M.get(i, j));
  const Mu = Matrix.fromFunction(n, n, (i, j) => M.get(i, n + j));
  if (Md.det().key === S.Zero.key) throw new Error('dsolve: the system is not of first order in every function');
  // d = A*u + b
  const MdInv = Md.inv();
  const A = MdInv.mul(Mu).scale(-1).map((e) => simplify(e));
  const b = MdInv.mul(rhs).map((e) => simplify(e));
  if (A.data.some((e) => e.has(t))) throw new Error('dsolve: only constant-coefficient systems are supported');
  const fundamental = fundamentalSolutions(A, t);
  const Phi = fundamental.reduce((acc, c) => acc.hstack(c));
  const Cs = Array.from({ length: n }, (_, i) => new Sym(`C${i + 1}`));
  let sol = Phi.mul(Matrix.col(...Cs));
  if (b.data.some((e) => !isZero(e))) {
    // variation of parameters: Phi * Integral(Phi**-1 * b)
    const g = Phi.inv().mul(b).map((e) => simplify(e));
    const part = Phi.mul(g.map((e) => integrate(e, t))).map((e) => simplify(expand(e)));
    sol = sol.add(part);
  }
  return funcs.map((f, i) => Eq(f, expand(sol.get(i, 0))));
}

/** n real fundamental solutions (columns) of x' = A*x. */
function fundamentalSolutions(A: Matrix, t: Sym): Matrix[] {
  const n = A.rows;
  const [P, J] = jordanForm(A);
  const out: Matrix[] = [];
  let i = 0;
  while (i < n) {
    const lam = J.get(i, i);
    // block size
    let k = 1;
    while (i + k < n && J.get(i + k - 1, i + k).key === S.One.key && J.get(i + k, i + k).key === lam.key) k++;
    const c = lam.toComplex();
    const complexPair = Math.abs(c.im) > 1e-14;
    for (let j = 0; j < k; j++) {
      // the j-th chain solution: e^(lam*t) * sum_{m<=j} t**(j-m)/(j-m)! * P_col(i+m)
      let v = Matrix.zeros(n, 1);
      for (let m = 0; m <= j; m++) {
        let fact = 1n;
        for (let q = 2n; q <= BigInt(j - m); q++) fact *= q;
        v = v.add(P.col(i + m).scale(mul(pow(t, j - m), Rational.of(1n, fact))));
      }
      if (!complexPair) out.push(v.scale(exp(mul(lam, t))).map((e) => simplify(e)));
      else if (c.im < 0) {
        // the pair is represented by the eigenvalue with negative imaginary part:
        // e^(lam*t) = e^(a*t)*(cos(b*t) + I*sin(b*t)), real solutions Re and Im (t real)
        const a = simplify(re(lam));
        const bb = simplify(im(lam));
        const tr = new Dummy('t', { real: true });
        const w = v.map((e) => xreplace(e, [[t, tr]])).scale(mul(exp(mul(a, tr)), add(cos(mul(bb, tr)), mul(I, sin(mul(bb, tr))))));
        const ex = w.map((e) => expand(e, { complex: true } as never));
        const back = (e: Expr) => simplify(xreplace(expand(e, { complex: true } as never), [[tr, t]]));
        out.push(ex.map((e) => back(re(e))), ex.map((e) => back(im(e))));
      }
    }
    i += k;
  }
  if (out.length !== n) throw new Error('dsolve: could not build the fundamental solutions');
  return out;
}

/** The unknown functions, in the order of the derivatives in the equations. */
function findFunctions(eqs: readonly Expr[]): UndefFn[] {
  const seen = new Map<string, UndefFn>();
  for (const e of eqs) {
    const ds: UndefFn[] = [];
    const walk = (x: Expr) => {
      if (x instanceof Derivative && x.expr instanceof UndefFn) ds.push(x.expr);
      x.args.forEach(walk);
    };
    walk(e);
    const f = ds.find((d) => !seen.has(d.key));
    if (f) seen.set(f.key, f);
  }
  return [...seen.values()];
}

