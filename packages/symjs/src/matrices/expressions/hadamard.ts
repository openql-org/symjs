// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy HadamardProduct and HadamardPower (sympy.matrices.expressions.
 * hadamard): the elementwise product and power of matrices.
 */

import { callableClass } from '../../core/callable';
import type { ExprLike } from '../../core/nodes';
import type { Expr } from '../../core/nodes';
import { mul, pow, sympify } from '../../core/ops';
import { Matrix } from '../matrix';
import type { DoitHints, EntryContext, MatArg } from './matexpr';
import {
  ImmutableMatrixNode,
  MatrixExpr,
  OneMatrixNode,
  ZeroMatrixNode,
  doitArg,
  matSortKey,
  parenLatex,
  toExpr,
  transposeOf,
  validateMatAdd,
} from './matexpr';
import { compareKeys } from '../../printing/sortkey';
import { PRECEDENCE, same } from './util';
import { latexPrecedence } from './matexpr';
import { at, cast, first, pair } from '../../core/guard';

/** SymPy HadamardProduct(*args): the elementwise product of matrices of the same shape. */
export class HadamardProductNode extends MatrixExpr {
  constructor(args: readonly Expr[]) {
    super('HadamardProduct', args);
  }
  /** SymPy HadamardProduct(*args): validated, unevaluated (evaluate: doit(deep=False)). */
  static create(argsIn: readonly MatArg[], evaluate = false): Expr {
    const args = argsIn.map(toExpr);
    if (!args.length) throw new RangeError('HadamardProduct needs at least one argument');
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    validateMatAdd(args);
    const obj = new HadamardProductNode(args);
    return evaluate ? obj.doit({ deep: false }) : obj;
  }
  get shape(): [Expr, Expr] {
    return cast(first(this.args), MatrixExpr).shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new HadamardProductNode(args);
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    return mul(...this.args.map((a) => cast(a, MatrixExpr).entry(i, j, ctx)));
  }
  override evalTranspose(): Expr {
    return new HadamardProductNode(this.args.map(transposeOf));
  }
  override doit(hints: DoitHints = {}): Expr {
    // SymPy evaluates the arguments also for deep=False (self.func(*(i.doit(**hints) for i in self.args)))
    const args = this.args.map((a) => doitArg(a, hints));
    let expr: Expr = new HadamardProductNode(args);
    const explicit = args.filter((a): a is ImmutableMatrixNode => a instanceof ImmutableMatrixNode);
    if (explicit.length) {
      const remainder = args.filter((a) => !(a instanceof ImmutableMatrixNode));
      const m0 = first(explicit).matrix;
      const m = Matrix.fromFunction(m0.rows, m0.cols, (i, j) => mul(...explicit.map((x) => x.matrix.get(i, j))));
      expr = new HadamardProductNode([new ImmutableMatrixNode(m), ...remainder]);
    }
    return canonicalize(expr);
  }
  override strPrecedence(): number {
    return PRECEDENCE.Mul;
  }
  override printLatex(): string {
    return this.args.map((a) => parenLatex(a, PRECEDENCE.Pow, true)).join(' \\circ ');
  }
}

/** SymPy HadamardProduct(*args): an unevaluated elementwise product. */
export const HadamardProduct = /* @__PURE__ */ callableClass(HadamardProductNode, (...args: MatArg[]): Expr => HadamardProductNode.create(args));
export type HadamardProduct = HadamardProductNode;

/** SymPy hadamard_product(*matrices): the evaluated elementwise product. */
export function hadamardProduct(...matrices: MatArg[]): Expr {
  if (!matrices.length) throw new TypeError('Empty Hadamard product is undefined');
  if (matrices.length === 1) return toExpr(first(matrices));
  return cast(HadamardProductNode.create(matrices), MatrixExpr).doit();
}

/**
 * SymPy hadamard.canonicalize: associativity, OneMatrix as identity,
 * ZeroMatrix absorbing, repeated factors as HadamardPower, commutativity
 * (sorted factors) and unpacking.
 */
export function canonicalize(x0: Expr): Expr {
  let x = x0;
  // associativity
  for (;;) {
    if (!(x instanceof HadamardProductNode)) break;
    const flat = x.args.flatMap((a) => (a instanceof HadamardProductNode ? a.args : [a]));
    if (flat.length === x.args.length) break;
    x = new HadamardProductNode(flat);
  }
  if (x instanceof HadamardProductNode) {
    // identity
    const ids = x.args.map((a) => a instanceof OneMatrixNode);
    const n = ids.filter(Boolean).length;
    if (n && n !== ids.length) x = new HadamardProductNode(x.args.filter((_, k) => !ids[k]));
    else if (n) x = new HadamardProductNode([first(x.args)]);
  }
  // absorbing by the zero matrix
  if (x instanceof HadamardProductNode && x.args.some((a) => a instanceof ZeroMatrixNode)) {
    const [r, c] = x.shape;
    x = new ZeroMatrixNode(r, c);
  }
  // repeated factors as HadamardPower
  if (x instanceof HadamardProductNode) {
    const tally = new Map<string, { base: Expr; n: number }>();
    for (const a of x.args) {
      const t = tally.get(a.key);
      if (t) t.n++;
      else tally.set(a.key, { base: a, n: 1 });
    }
    x = new HadamardProductNode([...tally.values()].map(({ base, n }) => (n === 1 ? base : new HadamardPowerNode(base, sympify(n)))));
  }
  // commutativity
  if (x instanceof HadamardProductNode) {
    x = new HadamardProductNode(
      x.args
        .map((a) => ({ a, k: matSortKey(a) }))
        .sort((p, q) => compareKeys(p.k, q.k))
        .map((p) => p.a),
    );
  }
  // unpacking
  if (x instanceof HadamardProductNode && x.args.length === 1) return first(x.args);
  return x;
}

/** SymPy HadamardPower(base, exp): the elementwise power. */
export class HadamardPowerNode extends MatrixExpr {
  constructor(base: Expr, exp: Expr) {
    super('HadamardPower', [base, exp]);
  }
  /** SymPy HadamardPower(base, exp): base**exp for scalars, validated otherwise. */
  static create(baseIn: MatArg, expIn: MatArg): Expr {
    const base = toExpr(baseIn);
    const exp = toExpr(expIn);
    if (!(base instanceof MatrixExpr) && !(exp instanceof MatrixExpr)) return pow(base, exp);
    if (base instanceof MatrixExpr && exp instanceof MatrixExpr) validateMatAdd([base, exp]);
    return new HadamardPowerNode(base, exp);
  }
  /** The base. */
  get base(): Expr {
    return at(this.args, 0);
  }
  /** The exponent. */
  get exp(): Expr {
    return at(this.args, 1);
  }
  get shape(): [Expr, Expr] {
    return this.base instanceof MatrixExpr ? this.base.shape : cast(this.exp, MatrixExpr).shape;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new HadamardPowerNode(...pair(args));
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const a = this.base instanceof MatrixExpr ? this.base.entry(i, j, ctx) : this.base;
    const b = this.exp instanceof MatrixExpr ? this.exp.entry(i, j, ctx) : this.exp;
    return pow(a, b);
  }
  override evalTranspose(): Expr {
    return new HadamardPowerNode(transposeOf(this.base), this.exp);
  }
  override strPrecedence(): number {
    return PRECEDENCE.Pow;
  }
  override printLatex(print: (e: Expr) => string): string {
    const e = print(this.exp);
    const base = parenLatex(this.base, PRECEDENCE.Pow);
    return latexPrecedence(this.exp) < PRECEDENCE.Mul ? `${base}^{\\circ \\left({${e}}\\right)}` : `${base}^{\\circ {${e}}}`;
  }
}

/** SymPy HadamardPower(base, exp). */
export const HadamardPower = /* @__PURE__ */ callableClass(HadamardPowerNode, (base: MatArg, exp: MatArg): Expr => HadamardPowerNode.create(base, exp));
export type HadamardPower = HadamardPowerNode;

/** SymPy hadamard_power(base, exp): the elementwise power (base for exp = 1, base**exp for scalars). */
export function hadamardPower(baseIn: MatArg, expIn: ExprLike): Expr {
  const base = toExpr(baseIn);
  const exp = sympify(expIn);
  if (same(exp, sympify(1))) return base;
  if (!(base instanceof MatrixExpr)) return pow(base, exp);
  if (exp instanceof MatrixExpr) throw new RangeError('cannot raise expression to a matrix');
  return new HadamardPowerNode(base, exp);
}
