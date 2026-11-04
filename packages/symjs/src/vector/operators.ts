// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/operators.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.operators: the differential operators of vector
 * calculus, unevaluated (Gradient, Divergence, Curl, Laplacian) and as
 * functions (gradient, divergence, curl), in the coordinate system of the
 * field with its Lame coefficients.
 */

import { Add, ExtensionExpr, Mul, S } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, defined } from '../core/guard';
import { derivative } from '../core/undef';
import { doit as doitAll } from '../calculus/doit';
import { prettyHooks } from '../printing/pretty/pretty';
import { PrettyForm } from '../printing/pretty/stringpict';
import type { CoordSysBase} from './basisdependent';
import { basisAdd, expressHook, vectorHooks } from './basisdependent';
import { Cross, CrossNode, Dot, Vector, connected, VectorAddNode, VectorMulNode, coordSystems, parenMul, vectorFamily } from './vector';

/** The options of the operators (SymPy keyword arguments). */
export interface OperatorOptions {
  /**
   * Evaluate the derivatives (SymPy doit; true by default for the
   * functions, false for the methods of Del).
   */
  readonly doit?: boolean;
}

/** An unevaluated operator applied to one expression (SymPy Gradient, Divergence, Curl, Laplacian). */
abstract class VectorOperator extends ExtensionExpr {
  /** SymPy doit: the operator applied to the operand as it is (not deep). */
  override get doitDeep(): boolean {
    return false;
  }
  /** The operand (SymPy _expr). */
  get expr(): Expr {
    return at(this.args, 0);
  }
}

/** SymPy Gradient(expr): the unevaluated gradient of a scalar field. */
export class GradientNode extends VectorOperator {
  constructor(expr: ExprLike) {
    super('Gradient', [sympify(expr)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new GradientNode(at(args, 0));
  }
  /** A gradient is a vector. */
  override get isScalar(): boolean {
    return false;
  }
  override doitSelf(): Expr {
    return gradient(this.expr, { doit: true });
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla ${parenMul(this.expr, print)}`;
  }
}

/** SymPy Divergence(expr): the unevaluated divergence of a vector field. */
export class DivergenceNode extends VectorOperator {
  constructor(expr: ExprLike) {
    super('Divergence', [sympify(expr)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DivergenceNode(at(args, 0));
  }
  override doitSelf(): Expr {
    return divergence(this.expr, { doit: true });
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla\\cdot ${parenMul(this.expr, print)}`;
  }
}

/** SymPy Curl(expr): the unevaluated curl of a vector field. */
export class CurlNode extends VectorOperator {
  constructor(expr: ExprLike) {
    super('Curl', [sympify(expr)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CurlNode(at(args, 0));
  }
  /** A curl is a vector. */
  override get isScalar(): boolean {
    return false;
  }
  override doitSelf(): Expr {
    return curl(this.expr, { doit: true });
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla\\times ${parenMul(this.expr, print)}`;
  }
}

/** SymPy Laplacian(expr): the unevaluated Laplacian of a field. */
export class LaplacianNode extends VectorOperator {
  constructor(expr: ExprLike) {
    super('Laplacian', [sympify(expr)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new LaplacianNode(at(args, 0));
  }
  override doitSelf(): Expr {
    return defined(vectorHooks.laplacian, 'laplacian')(this.expr);
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\Delta ${parenMul(this.expr, print)}`;
  }
}

/** SymPy Gradient(expr). */
export const Gradient = /* @__PURE__ */ callableClass(GradientNode, (expr: ExprLike): GradientNode => new GradientNode(expr));
export type Gradient = GradientNode;
/** SymPy Divergence(expr). */
export const Divergence = /* @__PURE__ */ callableClass(DivergenceNode, (expr: ExprLike): DivergenceNode => new DivergenceNode(expr));
export type Divergence = DivergenceNode;
/** SymPy Curl(expr). */
export const Curl = /* @__PURE__ */ callableClass(CurlNode, (expr: ExprLike): CurlNode => new CurlNode(expr));
export type Curl = CurlNode;
/** SymPy Laplacian(expr). */
export const Laplacian = /* @__PURE__ */ callableClass(LaplacianNode, (expr: ExprLike): LaplacianNode => new LaplacianNode(expr));
export type Laplacian = LaplacianNode;

/** The vector-valued factors SymPy recognizes in a product (Vector, Cross, Gradient). */
const isVectorFactor = (e: Expr): boolean => e instanceof Vector || e instanceof GradientNode;
/** The unevaluated vector-valued operands (Cross, Curl, Gradient). */
const isUnevaluatedVector = (e: Expr): boolean => e instanceof CrossNode || e instanceof CurlNode || e instanceof GradientNode;

/** The terms of a sum (SymPy isinstance(e, (Add, VectorAdd))). */
const sumTerms = (e: Expr): readonly Expr[] | undefined => (e instanceof Add || e instanceof VectorAddNode ? e.args : undefined);
/** The factors of a product (SymPy isinstance(e, (Mul, VectorMul))). */
const productFactors = (e: Expr): readonly Expr[] | undefined => (e instanceof Mul || e instanceof VectorMulNode ? e.args : undefined);

/** The vector factor and the scalar rest of a product. */
function splitProduct(factors: readonly Expr[]): [Expr, Expr] {
  const vector = defined(
    factors.find((f) => isVectorFactor(f)),
    'vector factor',
  );
  return [vector, mul(...factors.filter((f) => !isVectorFactor(f)))];
}

const only = (systems: CoordSysBase[]): CoordSysBase => defined(systems[0], 'coordinate system');

/** The sum of vectors (SymPy VectorAdd.fromiter). */
const vectorSum = (terms: readonly Expr[]): Expr => basisAdd(vectorFamily, terms);

/**
 * SymPy curl(vect, doit=True): the curl of a vector field in the base
 * scalars of its coordinate system (with Derivative instances unless doit).
 */
export function curl(vectIn: ExprLike, opts: OperatorOptions = {}): Expr {
  const vect = sympify(vectIn);
  const doit = opts.doit ?? true;
  const systems = coordSystems(vect);
  if (systems.length === 0) return Vector.zero;
  if (systems.length === 1) {
    const cs = only(systems);
    const [i, j, k] = cs.baseVectors();
    const [x, y, z] = cs.baseScalars();
    const [h1, h2, h3] = cs.lameCoefficients();
    const vx = dotOf(vect, i);
    const vy = dotOf(vect, j);
    const vz = dotOf(vect, k);
    const d = (e: Expr, v: Expr): Expr => derivative(e, [[v, 1]]);
    let out: Expr = Vector.zero;
    out = add(out, mul(add(d(mul(vz, h3), y), mul(-1, d(mul(vy, h2), z))), i, mul(h2, h3).pow(-1)));
    out = add(out, mul(add(d(mul(vx, h1), z), mul(-1, d(mul(vz, h3), x))), j, mul(h1, h3).pow(-1)));
    out = add(out, mul(add(d(mul(vy, h2), x), mul(-1, d(mul(vx, h1), y))), k, mul(h2, h1).pow(-1)));
    return doit ? doitAll(out) : out;
  }
  const terms = sumTerms(vect);
  if (terms) {
    const cs = only(systems);
    // (SymPy catches the ValueError of express for systems without a connecting path)
    const args = systems.every((s) => connected(s, cs)) ? terms.map((t) => expressHook(t, cs, undefined, { variables: true })) : terms;
    return vectorSum(args.map((t) => curl(t, opts)));
  }
  const factors = productFactors(vect);
  if (factors) {
    const [vector, scalar] = splitProduct(factors);
    const res = add(doitAll(Cross(gradient(scalar), vector)), mul(scalar, curl(vector, opts)));
    return doit ? doitAll(res) : res;
  }
  if (isUnevaluatedVector(vect)) return new CurlNode(vect);
  throw new RangeError('Invalid argument for curl');
}

/** v.dot(e) of a vector field. */
function dotOf(v: Expr, e: Expr): Expr {
  if (!(v instanceof Vector)) throw new TypeError(`${String(v)} is not a vector`);
  return v.dot(e);
}

/**
 * SymPy _diff_conditional: the derivative of coeff1*coeff2*expr (expr
 * re-expressed in the system of the base scalar) with respect to the base
 * scalar, or 0.
 */
function diffConditional(expr: Expr, baseScalar: Expr, coeff1: Expr, coeff2: Expr, system: CoordSysBase): Expr {
  const e = expressHook(expr, system, undefined, { variables: true });
  const arg = mul(coeff1, coeff2, e);
  return arg.key === S.Zero.key ? S.Zero : derivative(arg, [[baseScalar, 1]]);
}

/**
 * SymPy divergence(vect, doit=True): the divergence of a vector field in
 * the base scalars of its coordinate system.
 */
export function divergence(vectIn: ExprLike, opts: OperatorOptions = {}): Expr {
  const vect = sympify(vectIn);
  const doit = opts.doit ?? true;
  const systems = coordSystems(vect);
  if (systems.length === 0) return S.Zero;
  if (systems.length === 1) {
    if (isUnevaluatedVector(vect)) return new DivergenceNode(vect);
    const cs = only(systems);
    const [i, j, k] = cs.baseVectors();
    const [x, y, z] = cs.baseScalars();
    const [h1, h2, h3] = cs.lameCoefficients();
    const den = mul(h1, h2, h3).pow(-1);
    const vx = mul(diffConditional(dotOf(vect, i), x, h2, h3, cs), den);
    const vy = mul(diffConditional(dotOf(vect, j), y, h3, h1, cs), den);
    const vz = mul(diffConditional(dotOf(vect, k), z, h1, h2, cs), den);
    const res = add(vx, vy, vz);
    return doit ? doitAll(res) : res;
  }
  const terms = sumTerms(vect);
  if (terms) return add(...terms.map((t) => divergence(t, opts)));
  const factors = productFactors(vect);
  if (factors) {
    const [vector, scalar] = splitProduct(factors);
    const res = add(Dot(vector, gradient(scalar)), mul(scalar, divergence(vector, opts)));
    return doit ? doitAll(res) : res;
  }
  if (isUnevaluatedVector(vect)) return new DivergenceNode(vect);
  throw new RangeError('Invalid argument for divergence');
}

/**
 * SymPy _split_mul_args_wrt_coordsys: the factors of a product grouped by
 * the coordinate systems they depend on.
 */
function splitMulArgs(factors: readonly Expr[]): Expr[] {
  const groups = new Map<string, Expr>();
  for (const f of factors) {
    const key = coordSystems(f)
      .map((s) => s.key)
      .sort()
      .join('|');
    groups.set(key, mul(groups.get(key) ?? S.One, f));
  }
  return [...groups.values()];
}

/**
 * SymPy gradient(scalar_field, doit=True): the gradient of a scalar field
 * in the base scalars of its coordinate system.
 */
export function gradient(fieldIn: ExprLike, opts: OperatorOptions = {}): Expr {
  const field = sympify(fieldIn);
  const doit = opts.doit ?? true;
  const systems = coordSystems(field);
  if (systems.length === 0) return Vector.zero;
  if (systems.length === 1) {
    const cs = only(systems);
    const [h1, h2, h3] = cs.lameCoefficients();
    const [i, j, k] = cs.baseVectors();
    const [x, y, z] = cs.baseScalars();
    const d = (v: Expr, h: Expr): Expr => mul(derivative(field, [[v, 1]]), h.pow(-1));
    const out = add(mul(d(x, h1), i), mul(d(y, h2), j), mul(d(z, h3), k));
    return doit ? doitAll(out) : out;
  }
  const terms = sumTerms(field);
  if (terms) return vectorSum(terms.map((t) => gradient(t)));
  if (field instanceof Mul) return vectorSum(splitMulArgs(field.args).map((g) => mul(field, g.pow(-1), gradient(g))));
  return new GradientNode(field);
}

// SymPy _print_Gradient, _print_Divergence, _print_Curl and _print_Laplacian: the operator before the operand in parentheses
for (const [name, op] of [
  ['Gradient', '\u2207'],
  ['Divergence', '\u2207\u22c5'],
  ['Curl', '\u2207\u00d7'],
  ['Laplacian', '\u2206'],
] as const) {
  prettyHooks.extension.set(name, (e, printer) => PrettyForm.of(PrettyForm.of(printer.print(at(e.args, 0)).parens()).left(op)));
}
