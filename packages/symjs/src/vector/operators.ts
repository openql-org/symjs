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
import { Cross, CrossNode, Dot, OPERATOR_PRECEDENCE, Vector, connected, VectorAddNode, VectorMulNode, coordSystems, parenMul, vectorFamily } from './vector';

/** The options of the operators. */
export interface OperatorOptions {
  /**
   * Evaluate the derivatives (SymPy doit; true by default for the functions, false for the methods
   * of Del).
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
  /** SymPy PRECEDENCE_TRADITIONAL of the operators: just below a product. */
  latexPrecedence(): number {
    return OPERATOR_PRECEDENCE;
  }
}

/**
 * The unevaluated gradient of a scalar field.
 *
 * @see SymPy `sympy.vector.operators.Gradient`
 * @example
 * ```ts
 * import { CoordSys3D, Gradient } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * Gradient(R.x.mul(R.y).mul(R.z)); // => Gradient(R.x*R.y*R.z)
 * ```
 */
export class GradientNode extends VectorOperator {
  /**
   * Constructs an instance of `GradientNode`.
   *
   * @param expr - Symbolic expression on which to operate.
   */
  constructor(expr: ExprLike) {
    super('Gradient', [sympify(expr)]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new GradientNode(at(args, 0));
  }
  /**
   * Identifies a gradient as vector-valued.
   *
   * @returns `false`.
   * @see SymPy `sympy.vector.operators.Gradient.is_scalar`
   */
  override get isScalar(): boolean {
    return false;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return gradient(this.expr, { doit: true });
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla ${parenMul(this.expr, print)}`;
  }
}

/**
 * The unevaluated divergence of a vector field.
 *
 * @see SymPy `sympy.vector.operators.Divergence`
 * @example
 * ```ts
 * import { CoordSys3D, Divergence } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const field = R.i.mul(R.y.mul(R.z)).add(R.j.mul(R.x.mul(R.z))).add(R.k.mul(R.x.mul(R.y)));
 * Divergence(field); // => Divergence(R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k)
 * ```
 */
export class DivergenceNode extends VectorOperator {
  /**
   * Constructs an instance of `DivergenceNode`.
   *
   * @param expr - Symbolic expression on which to operate.
   */
  constructor(expr: ExprLike) {
    super('Divergence', [sympify(expr)]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DivergenceNode(at(args, 0));
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return divergence(this.expr, { doit: true });
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla\\cdot ${parenMul(this.expr, print)}`;
  }
}

/**
 * The unevaluated curl of a vector field.
 *
 * @see SymPy `sympy.vector.operators.Curl`
 * @example
 * ```ts
 * import { CoordSys3D, Curl } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const field = R.i.mul(R.y.mul(R.z)).add(R.j.mul(R.x.mul(R.z))).add(R.k.mul(R.x.mul(R.y)));
 * Curl(field); // => Curl(R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k)
 * ```
 */
export class CurlNode extends VectorOperator {
  /**
   * Constructs an instance of `CurlNode`.
   *
   * @param expr - Symbolic expression on which to operate.
   */
  constructor(expr: ExprLike) {
    super('Curl', [sympify(expr)]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new CurlNode(at(args, 0));
  }
  /**
   * Identifies a curl as vector-valued.
   *
   * @returns `false`.
   * @see SymPy `sympy.vector.operators.Curl.is_scalar`
   */
  override get isScalar(): boolean {
    return false;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return curl(this.expr, { doit: true });
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\nabla\\times ${parenMul(this.expr, print)}`;
  }
}

/**
 * The unevaluated Laplacian of a field.
 *
 * @see SymPy `sympy.vector.operators.Laplacian`
 * @example
 * ```ts
 * import { CoordSys3D, Laplacian } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * Laplacian(R.x.pow(3).mul(R.y.pow(2)).mul(R.z.pow(3)).mul(3)); // => Laplacian(3*R.x**3*R.y**2*R.z**3)
 * ```
 */
export class LaplacianNode extends VectorOperator {
  /**
   * Constructs an instance of `LaplacianNode`.
   *
   * @param expr - Symbolic expression on which to operate.
   */
  constructor(expr: ExprLike) {
    super('Laplacian', [sympify(expr)]);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new LaplacianNode(at(args, 0));
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return defined(vectorHooks.laplacian, 'laplacian')(this.expr);
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\Delta ${parenMul(this.expr, print)}`;
  }
}

/**
 * Constructs an unevaluated gradient of a scalar field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The resulting `Gradient` expression.
 * @see SymPy `sympy.vector.operators.Gradient`
 * @example
 * ```ts
 * import { CoordSys3D, Gradient } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * Gradient(R.x.mul(R.y).mul(R.z)); // => Gradient(R.x*R.y*R.z)
 * ```
 */
export const Gradient = /* @__PURE__ */ callableClass(GradientNode, (expr: ExprLike): GradientNode => new GradientNode(expr));
export type Gradient = GradientNode;
/**
 * Constructs an unevaluated divergence of a vector field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The resulting `Divergence` expression.
 * @see SymPy `sympy.vector.operators.Divergence`
 * @example
 * ```ts
 * import { CoordSys3D, Divergence } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const field = R.i.mul(R.y.mul(R.z)).add(R.j.mul(R.x.mul(R.z))).add(R.k.mul(R.x.mul(R.y)));
 * Divergence(field); // => Divergence(R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k)
 * ```
 */
export const Divergence = /* @__PURE__ */ callableClass(DivergenceNode, (expr: ExprLike): DivergenceNode => new DivergenceNode(expr));
export type Divergence = DivergenceNode;
/**
 * Constructs an unevaluated curl of a vector field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The resulting `Curl` expression.
 * @see SymPy `sympy.vector.operators.Curl`
 * @example
 * ```ts
 * import { CoordSys3D, Curl } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * const field = R.i.mul(R.y.mul(R.z)).add(R.j.mul(R.x.mul(R.z))).add(R.k.mul(R.x.mul(R.y)));
 * Curl(field); // => Curl(R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k)
 * ```
 */
export const Curl = /* @__PURE__ */ callableClass(CurlNode, (expr: ExprLike): CurlNode => new CurlNode(expr));
export type Curl = CurlNode;
/**
 * Constructs an unevaluated Laplacian of a scalar or vector field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The resulting `Laplacian` expression.
 * @see SymPy `sympy.vector.operators.Laplacian`
 * @example
 * ```ts
 * import { CoordSys3D, Laplacian } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * Laplacian(R.x.pow(3).mul(R.y.pow(2)).mul(R.z.pow(3)).mul(3)); // => Laplacian(3*R.x**3*R.y**2*R.z**3)
 * ```
 */
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
 * Computes the curl in the field's base coordinates, retaining derivative expressions unless evaluation
 * is requested.
 *
 * @param vectIn - Vector field to which the operator is applied.
 * @param opts - Settings described by {@link OperatorOptions}.
 * @returns The curl vector.
 * @throws RangeError when the operand is unsuitable for the vector differential operator.
 * @see SymPy `sympy.vector.operators.curl`
 * @example
 * ```ts
 * import { CoordSys3D, curl } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * curl(R.i.mul(R.x.mul(R.y).mul(R.z))); // => R.x*R.y*R.j + (-R.x*R.z)*R.k
 * ```
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
 * Computes the divergence in the field's base coordinates.
 *
 * @param vectIn - Vector field to which the operator is applied.
 * @param opts - Settings described by {@link OperatorOptions}.
 * @returns The scalar divergence.
 * @throws RangeError when the operand is unsuitable for the vector differential operator.
 * @see SymPy `sympy.vector.operators.divergence`
 * @example
 * ```ts
 * import { CoordSys3D, divergence } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * divergence(R.j.mul(R.y.mul(R.z).mul(2))); // => 2*R.z
 * ```
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
 * Computes the gradient in the field's base coordinates.
 *
 * @param fieldIn - Scalar or vector field on the region.
 * @param opts - Settings described by {@link OperatorOptions}.
 * @returns The gradient vector.
 * @see SymPy `sympy.vector.operators.gradient`
 * @example
 * ```ts
 * import { CoordSys3D, gradient } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * gradient(R.x.mul(R.y).mul(R.z)); // => R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k
 * ```
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
