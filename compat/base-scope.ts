// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Base-scope checks: behaviors the base module is meant to guarantee
 * (assumption-dependent rewriting, non-commutativity, bound variables,
 * unevaluated objects, extension nodes, ...). Each check compares symjs
 * with the output of SymPy 1.14 for the same input. These complement the
 * doctest-based behavior compatibility and are reported separately in
 * compat/REPORT.md ("Base scope checks").
 */

import * as sj from '../packages/symjs/src';
import { Expr, Sym } from '../packages/symjs/src';

export type BaseCheck = { area: string; name: string; expected: string; run: () => unknown };

const x = new Sym('x');
const y = new Sym('y');
const xr = new Sym('x', { real: true });
const xp = new Sym('x', { positive: true });
const p = new Sym('p', { positive: true });
const q = new Sym('q', { positive: true });
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });
const P = sj.parse;

/** A minimal node defined only through the public extension API. */
class Ket extends sj.ExtensionExpr {
  constructor(label: Expr) {
    super('Ket', [label]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Ket(args[0]!);
  }
  override get isCommutative(): boolean {
    return false;
  }
  override printStr(print: (e: Expr) => string): string {
    return `|${print(this.args[0]!)}>`;
  }
}

const integral = () => new sj.Integral([sj.mul(x, y), x, sj.S.Zero, y]);
const sum = () => sj.Sum(sj.mul(x, y), [x, 0, y]);

export const BASE_CHECKS: BaseCheck[] = [
  // assumptions: rewriting depends on what is known about the symbols
  { area: 'assumptions', name: 'sqrt(x**2), no assumptions', expected: 'sqrt(x**2)', run: () => sj.sqrt(sj.pow(x, 2)) },
  { area: 'assumptions', name: 'sqrt(x**2), x real', expected: 'Abs(x)', run: () => sj.sqrt(sj.pow(xr, 2)) },
  { area: 'assumptions', name: 'sqrt(x**2), x positive', expected: 'x', run: () => sj.sqrt(sj.pow(xp, 2)) },
  { area: 'assumptions', name: 'expand_log(log(x*y)), no assumptions', expected: 'log(x*y)', run: () => sj.expand_log(sj.log(sj.mul(x, y))) },
  { area: 'assumptions', name: 'expand_log(log(p*q)), p, q positive', expected: 'log(p) + log(q)', run: () => sj.expand_log(sj.log(sj.mul(p, q))) },
  { area: 'assumptions', name: 'log(exp(x)), no assumptions', expected: 'log(exp(x))', run: () => sj.log(sj.exp(x)) },
  { area: 'assumptions', name: 'log(exp(x)), x real', expected: 'x', run: () => sj.log(sj.exp(xr)) },
  { area: 'assumptions', name: '(x**y)**2', expected: 'x**(2*y)', run: () => sj.pow(sj.pow(x, y), 2) },
  // non-commutative products
  { area: 'noncommutative', name: 'A*B differs from B*A', expected: 'false', run: () => sj.mul(A, B).equals(sj.mul(B, A)) },
  { area: 'noncommutative', name: 'expand((A + B)**2)', expected: 'A*B + A**2 + B*A + B**2', run: () => sj.expand(sj.pow(sj.add(A, B), 2)) },
  { area: 'noncommutative', name: 'exp(A)*exp(B) stays apart', expected: 'exp(A)*exp(B)', run: () => sj.mul(sj.exp(A), sj.exp(B)) },
  { area: 'noncommutative', name: 'A**(-1) prints as a power', expected: 'A**(-1)', run: () => sj.pow(A, -1) },
  { area: 'noncommutative', name: 'adjoint(x*A*B)', expected: 'conjugate(x)*adjoint(B)*adjoint(A)', run: () => sj.adjoint(sj.mul(x, A, B)) },
  { area: 'noncommutative', name: 'transpose(A*B)', expected: 'transpose(B)*transpose(A)', run: () => sj.transpose(sj.mul(A, B)) },
  // bound variables
  { area: 'bound variables', name: 'Integral(x*y, (x, 0, y)).subs(x, 2)', expected: 'Integral(x*y, (x, 0, y))', run: () => sj.subs(integral(), [[x, 2]]) },
  { area: 'bound variables', name: 'Integral(x*y, (x, 0, y)).subs(y, 2)', expected: 'Integral(2*x, (x, 0, 2))', run: () => sj.subs(integral(), [[y, 2]]) },
  { area: 'bound variables', name: 'Integral(x*y, (x, 0, y)).free_symbols', expected: 'y', run: () => [...sj.freeSymbols(integral())].map(String).join(', ') },
  { area: 'bound variables', name: 'Sum(x*y, (x, 0, y)).subs(x, 2)', expected: 'Sum(x*y, (x, 0, y))', run: () => sj.subs(sum(), [[x, 2]]) },
  { area: 'bound variables', name: 'Sum(x*y, (x, 0, y)).free_symbols', expected: 'y', run: () => [...sj.freeSymbols(sum())].map(String).join(', ') },
  // unevaluated objects: "cannot compute" is not "no solution"
  { area: 'unevaluated', name: 'integrate(exp(-x**2)*sin(x), x)', expected: 'Integral(exp(-x**2)*sin(x), x)', run: () => sj.integrate(sj.mul(sj.exp(sj.mul(-1, sj.pow(x, 2))), sj.sin(x)), x) },
  { area: 'unevaluated', name: 'Limit(sin(x)/x, x, 0) is kept', expected: "Limit(sin(x)/x, x, 0, dir='+')", run: () => new sj.Limit([sj.mul(sj.sin(x), sj.pow(x, -1)), x, sj.S.Zero]) },
  { area: 'unevaluated', name: 'solveset(x**2 + 1, x, Reals)', expected: 'EmptySet', run: () => sj.solveset(sj.add(sj.pow(x, 2), 1), x, sj.Reals) },
  // extension nodes defined outside the base module
  { area: 'extension nodes', name: 'print a custom node in a product', expected: '2*|psi>', run: () => sj.mul(2, new Ket(new Sym('psi'))) },
  { area: 'extension nodes', name: 'subs inside a custom node', expected: 'x*|x>', run: () => sj.subs(sj.mul(x, new Ket(new Sym('psi'))), [[new Sym('psi'), x]]) },
  { area: 'extension nodes', name: 'custom node keeps product order', expected: '|psi>*A', run: () => sj.mul(new Ket(new Sym('psi')), A) },
  // exact polynomial arithmetic
  { area: 'polynomials', name: 'div(x**3 + 2*x + 1, x**2 - 3) reconstructs', expected: 'x**3 + 2*x + 1', run: () => { const [qq, r] = sj.polyDiv(P('x**3 + 2*x + 1'), P('x**2 - 3')); return sj.expand(sj.add(sj.mul(qq, P('x**2 - 3')), r)); } },
  { area: 'polynomials', name: 'factor(x**4 - 1)', expected: '(x - 1)*(x + 1)*(x**2 + 1)', run: () => sj.factor(P('x**4 - 1')) },
  // numerics with explicit precision
  { area: 'numerics', name: 'N(pi, 30)', expected: '3.14159265358979323846264338328', run: () => sj.evalf(sj.S.Pi, 30) },
  { area: 'numerics', name: 'N(1/3, 50)', expected: '0.33333333333333333333333333333333333333333333333333', run: () => sj.evalf(sj.Rational.of(1, 3), 50) },
  // linear algebra
  { area: 'linear algebra', name: 'Matrix([[x, y], [1, 2]]).inv()', expected: 'Matrix([[2/(2*x - y), -y/(2*x - y)], [-1/(2*x - y), x/(2*x - y)]])', run: () => sj.Matrix.of([[x, y], [1, 2]]).inv() },
  { area: 'linear algebra', name: 'linsolve([x + y - 3, x - y - 1], [x, y])', expected: '2, 1', run: () => sj.linsolve([P('x + y - 3'), P('x - y - 1')], [x, y])?.map(String).join(', ') },
];

export type BaseCheckResult = { area: string; name: string; expected: string; got: string; pass: boolean };

export function runBaseChecks(): BaseCheckResult[] {
  return BASE_CHECKS.map((c) => {
    let got: string;
    try {
      got = String(c.run());
    } catch (e) {
      got = `error: ${(e as Error).message}`;
    }
    return { area: c.area, name: c.name, expected: c.expected, got, pass: got === c.expected };
  });
}
