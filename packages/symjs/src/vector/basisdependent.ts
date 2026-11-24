// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/basisdependent.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.basisdependent: BasisDependent, the base class of
 * vectors and dyadics, whose representation depends on the basis they are
 * expressed in, and the rules of their sums and scalar multiples (SymPy
 * BasisDependentAdd and BasisDependentMul).
 *
 * Vectors and dyadics are expression nodes. `add`, `mul` and the fluent
 * operators build VectorAdd/VectorMul (DyadicAdd/DyadicMul) through the
 * arithmetic registered here (SymPy _op_priority). The modules of the
 * vector package import each other only downwards; the operations that
 * SymPy imports locally to avoid cycles (express, the dyadic products,
 * laplacian) are registered in `vectorHooks` by the modules that define
 * them.
 */

import { ExtensionExpr, Integral, Mul, Add, Rational, S, isNum, registerArithmetic } from '../core/nodes';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { ExprMap } from '../core/exprmap';
import { defined } from '../core/guard';
import { Matrix } from '../matrices/matrix';
import { factor } from '../polys/sympoly';
import { trigsimp } from '../simplify/trigsimp';
import type { TrigsimpOptions } from '../simplify/trigsimp';
import { doit } from '../calculus/doit';

/** The classes of one kind of basis-dependent quantity, vectors or dyadics. */
export interface BasisFamily {
  /** Symbolic name. */
  readonly name: 'Vector' | 'Dyadic';
  /**
   * Tests whether the expression belongs to this vector or dyadic family.
   *
   * @param e - Expression to inspect.
   * @returns True for a family member.
   */
  is(e: Expr): e is BasisDependent;
  /**
   * Tests whether the expression is a basis vector or basis dyadic of this family.
   *
   * @param e - Expression to inspect.
   * @returns True for a basis element.
   */
  isBase(e: Expr): boolean;
  /**
   * Recognizes a scalar multiple of one of the family's basis elements.
   *
   * @param e - Expression to inspect.
   * @returns True for a product node.
   */
  isMul(e: Expr): boolean;
  /**
   * Recognizes an additive combination in this family.
   *
   * @param e - Expression to inspect.
   * @returns True for a sum node.
   */
  isAdd(e: Expr): boolean;
  /**
   * Tests whether the expression is the additive identity of the family.
   *
   * @param e - Expression to inspect.
   * @returns True for the zero element.
   */
  isZero(e: Expr): boolean;
  /** The zero instance (Vector.zero, Dyadic.zero). */
  readonly zero: BasisDependent;
  /**
   * Constructs an unevaluated sum from at least two terms and their known components.
   *
   * @param terms - Terms of the sum.
   * @param components - Coefficients indexed by basis elements.
   * @returns The family sum node.
   */
  addNode(terms: readonly Expr[], components: ExprMap<Expr>): BasisDependent;
  /**
   * Constructs an unevaluated scalar multiple of a basis element.
   *
   * @param measure - Scalar coefficient.
   * @param base - Base points of the permutation group.
   * @returns The family product node.
   */
  mulNode(measure: Expr, base: BasisDependent): BasisDependent;
}

const families: BasisFamily[] = [];

/** Registers the classes of vectors or dyadics (vector.ts and dyadic.ts). */
export function registerFamily(f: BasisFamily): void {
  families.push(f);
}

/**
 * The super class of vectors and dyadics, an expression node that is not a scalar.
 *
 * @see SymPy `sympy.vector.basisdependent.BasisDependent`
 */
export abstract class BasisDependent extends ExtensionExpr {
  /**
   * Identifies whether the quantity belongs to the vector or dyadic family.
   *
   * @returns The family descriptor.
   */
  abstract get family(): BasisFamily;

  /**
   * Associates each basis vector or dyadic with its scalar measure number.
   *
   * @returns The scalar coefficients keyed by basis element.
   */
  abstract get components(): ExprMap<Expr>;

  /**
   * Supplies the label used in pretty-printed expressions.
   *
   * @returns The display label.
   */
  get prettyForm(): string {
    return String(this);
  }

  /**
   * Indicates whether the expression represents a scalar.
   *
   * @returns The scalar flag.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.is_scalar`
   */
  override get isScalar(): boolean {
    return false;
  }

  /**
   * Applies the function to each component and recombines the results with their basis elements.
   *
   * @param f - Function applied to each scalar coefficient.
   * @returns The transformed quantity.
   */
  mapComponents(f: (v: Expr) => Expr): Expr {
    return basisAdd(
      this.family,
      [...this.components].map(([k, v]) => basisMul(this.family, [f(v), k])),
    );
  }

  /**
   * Applies trigonometric simplification to each component.
   *
   * @param opts - Settings described by {@link TrigsimpOptions}.
   * @returns The vector or dyadic with its coefficients trigonometrically simplified.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.trigsimp`
   */
  trigsimp(opts: TrigsimpOptions = {}): Expr {
    return this.mapComponents((v) => trigsimp(v, opts));
  }

  /**
   * Factors each scalar coefficient.
   *
   * @param opts - Polynomial factorization options passed to {@link factor} for each coefficient.
   * @returns The vector or dyadic with factored coefficients.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.factor`
   */
  factor(opts: Parameters<typeof factor>[1] = {}): Expr {
    return this.mapComponents((v) => factor(v, opts));
  }

  /**
   * Evaluates each component with `doit`.
   *
   * @returns The vector or dyadic with its coefficients evaluated.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.doit`
   */
  doit(): Expr {
    return doit(this);
  }

  /**
   * Represents the quantity as a fraction with unit denominator.
   *
   * @returns The pair `[quantity, 1]`.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.as_numer_denom`
   */
  asNumerDenom(): [Expr, Expr] {
    return [this, S.One];
  }

  /**
   * Splits off a unit scalar coefficient from the quantity.
   *
   * @returns The pair `[1, quantity]`.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.as_coeff_mul`
   */
  asCoeffMul(): [Expr, Expr] {
    return [S.One, this];
  }

  /**
   * Separates the additive constant and the terms in the basis expansion.
   *
   * @returns Zero and the list of scalar multiples of individual basis elements.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.as_coeff_add`
   */
  asCoeffAdd(): [Expr, Expr[]] {
    return [S.Zero, [...this.components].map(([k, v]) => basisMul(this.family, [k, v]))];
  }

  /**
   * Divides the quantity by a scalar.
   *
   * @param o - Divisor.
   * @returns The vector or dyadic with its coefficients divided by the scalar.
   * @throws RangeError when the scalar divisor is zero.
   * @throws TypeError when the divisor is a vector or dyadic of the same family.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent.__truediv__`
   */
  override div(o: ExprLike): Expr {
    const other = sympify(o);
    if (other instanceof BasisDependent) throw new TypeError(`Cannot divide two ${this.family.name.toLowerCase()}s`);
    if (isNum(other) && other.isZero) throw new RangeError(`Cannot divide a ${this.family.name.toLowerCase()} by zero`);
    return basisMul(this.family, [this, other.pow(-1)]);
  }

  /**
   * Differentiates the scalar coefficient of every basis component.
   *
   * @param x - Variable of differentiation.
   * @param d - Derivative function for individual operands.
   * @returns The specialized result when the hook handles the operands.
   * @throws TypeError when a differentiation argument is invalid.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_derivative`
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    if (x instanceof BasisDependent) throw new TypeError('Invalid arg for differentiation');
    return this.mapComponents((v) => d(v, x));
  }

  /**
   * Applies trigonometric simplification to each component.
   *
   * @param trigsimp - Trigonometric simplification function for individual components.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_trigsimp`
   */
  override trigsimpSelf(trigsimp: (e: Expr) => Expr): Expr | undefined {
    return this.mapComponents(trigsimp);
  }

  /**
   * Simplifies the coefficients in the basis expansion.
   *
   * @param simplify - Simplification function for individual components.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_simplify`
   */
  override simplifySelf(simplify: (e: Expr) => Expr): Expr | undefined {
    return this.mapComponents(simplify);
  }

  /**
   * Forms the unevaluated integral of each component.
   *
   * @param x - Variable of integration.
   * @param limits - Bound variables and their inclusive limits.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_Integral`
   */
  override integrateSelf(x: Sym, limits: readonly [Expr, Expr] | undefined): Expr | undefined {
    return this.mapComponents((v) => new Integral(limits ? [v, x, ...limits] : [v, x]));
  }

  /**
   * Evaluates the scalar components to the requested numerical precision.
   *
   * @param evalfArg - Function that evaluates an operand numerically.
   * @returns The numerically evaluated expression.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_evalf`
   */
  override evalfSelf(evalfArg: (e: Expr) => Expr): Expr | undefined {
    return this.mapComponents(evalfArg);
  }

  /**
   * Conjugates each component, retaining the real basis elements.
   *
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.vector.basisdependent.BasisDependent._eval_conjugate`
   */
  override conjugateSelf(): Expr | undefined {
    return this.mapComponents((v) => v.conjugate());
  }

  /**
   * Evaluates the components of the quantity.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr | undefined {
    return this.mapComponents((v) => v);
  }
}

/** The measure number and base instance of a base instance or a product (SymPy _measure_number, _base_instance). */
export interface ScaledBase {
  readonly measureNumber: Expr;
  readonly baseInstance: BasisDependent;
}

const isScaledBase = (e: Expr): e is BasisDependent & ScaledBase => e instanceof BasisDependent && 'measureNumber' in e && 'baseInstance' in e;

/** The unevaluated vector-valued operators that multiply only as plain products (SymPy Cross, Curl, Gradient). */
export const vectorOperatorNames: ReadonlySet<string> = new Set(['Cross', 'Curl', 'Gradient']);

const isZeroNumber = (e: Expr): boolean => isNum(e) && e.isZero;

/**
 * SymPy BasisDependentAdd.__new__: the sum of the arguments, collecting the
 * components; a sum of one term is that term, an empty sum the zero.
 */
export function basisAdd(f: BasisFamily, args: readonly Expr[]): Expr {
  const components = new ExprMap<Expr>();
  for (const a0 of args) {
    let a = a0;
    if (!f.is(a)) {
      if (a instanceof Mul) a = basisMul(f, a.args);
      else if (a instanceof Add) a = basisAdd(f, a.args);
    }
    if (!f.is(a) || !(f.isZero(a) || f.isBase(a) || f.isMul(a) || f.isAdd(a))) throw new TypeError(`${String(a0)} cannot be interpreted correctly`);
    for (const [k, v] of a.components) components.set(k, add(components.get(k) ?? S.Zero, v));
  }
  for (const [k, v] of [...components]) if (isZeroNumber(v)) components.delete(k);
  const terms = [...components].map(([k, v]) => basisMul(f, [v, k]));
  if (terms.length === 0) return f.zero;
  if (terms.length === 1) return defined(terms[0], 'term');
  return f.addNode(terms, components);
}

/**
 * SymPy BasisDependentMul._new: the product of scalars and one base
 * instance, product or sum (distributed over the sum). Two quantities
 * cannot be multiplied; without any, the product is a plain Mul.
 */
export function basisMul(f: BasisFamily, args: readonly Expr[]): Expr {
  let count = 0;
  let measure: Expr = S.One;
  let zero = false;
  let target: BasisDependent | undefined;
  let operator = false;
  for (const a of args) {
    if (f.isZero(a)) {
      count++;
      zero = true;
    } else if (isZeroNumber(a)) zero = true;
    else if (isScaledBase(a) && (f.isBase(a) || f.isMul(a))) {
      count++;
      target = a.baseInstance;
      measure = mul(measure, a.measureNumber);
    } else if (a instanceof BasisDependent && f.isAdd(a)) {
      count++;
      target = a;
    } else if (a instanceof BasisDependent || (a instanceof ExtensionExpr && vectorOperatorNames.has(a.name))) operator = true;
    else measure = mul(measure, a);
  }
  if (count > 1) throw new RangeError('Invalid multiplication');
  if (count === 0) return mul(...args);
  if (zero) return f.zero;
  // (SymPy keeps Cross, Curl and Gradient as extra factors of a product it cannot represent)
  if (operator) throw new TypeError('Invalid multiplication');
  const t = defined(target, 'base instance');
  if (f.isAdd(t)) return basisAdd(f, t.args.map((x) => basisMul(f, [measure, x])));
  if (measure instanceof Rational && measure.isOne) return t;
  return f.mulNode(measure, t);
}

/** The family of the first argument that is a base instance, product, sum or zero of a family. */
function familyOf(args: readonly Expr[]): BasisFamily | undefined {
  for (const a of args) {
    for (const f of families) if (f.isBase(a) || f.isMul(a) || f.isAdd(a) || f.isZero(a)) return f;
  }
  return undefined;
}

// SymPy _op_priority: sums, products and powers of vectors and dyadics use their own rules
registerArithmetic((op, args) => {
  const f = familyOf(args);
  if (f === undefined) return undefined;
  switch (op) {
    case 'add':
      // (SymPy's Add postprocessor drops the scalar terms, Expr.__add__ raises TypeError; an exact zero is dropped)
      return basisAdd(
        f,
        args.filter((a) => !isZeroNumber(a)),
      );
    case 'mul':
      if (args.some((a) => a instanceof BasisDependent && a.family !== f)) throw new TypeError('Invalid multiplication');
      return basisMul(f, args);
    case 'sub':
      return undefined;
    case 'pow': {
      const [b, e] = args;
      if (e instanceof Rational && e.isOne) return b;
      // (SymPy leaves Pow(v, n) unevaluated and returns a TypeError object for 1/v)
      throw new TypeError(`Invalid power involving a ${f.name.toLowerCase()}`);
    }
  }
});

/**
 * A coordinate system as the lower vector modules see it (implemented by
 * CoordSys3D in coordsysrect.ts).
 */
export abstract class CoordSysBase extends ExtensionExpr {
  /** The name of the system (SymPy _name). */
  abstract get sysName(): string;
  /** The names of the base vectors (SymPy _vector_names). */
  abstract get vectorNames(): readonly string[];
  /** The names of the base scalars (SymPy _variable_names). */
  abstract get variableNames(): readonly string[];
  /** The base vectors i, j, k. */
  abstract baseVectors(): readonly [BasisDependent, BasisDependent, BasisDependent];
  /** The base scalars x, y, z. */
  abstract baseScalars(): readonly [Sym, Sym, Sym];
  /** The system this one is defined with respect to (SymPy _parent), or undefined for a root. */
  abstract get parentSystem(): CoordSysBase | undefined;
  /** The root of the tree of systems (SymPy _root). */
  abstract get rootSystem(): CoordSysBase;
  /** The origin of the system (a vector Point). */
  abstract get originPoint(): Expr;
  /** SymPy rotation_matrix(other): the direction cosine matrix with respect to other. */
  abstract rotationMatrix(other: CoordSysBase): Matrix;
  /** SymPy scalar_map(other): the base scalars of this system in terms of those of other. */
  abstract scalarMap(other: CoordSysBase): ExprMap<Expr>;
  /** SymPy lame_coefficients. */
  abstract lameCoefficients(): readonly [Expr, Expr, Expr];
  /** The position of this system's origin with respect to a point or system. */
  abstract positionWrt(other: Expr): Expr;
}

/** The options of express. */
export interface ExpressOptions {
  /** Also substitute the base scalars of other systems. */
  readonly variables?: boolean;
}

/**
 * The operations the lower vector modules call and higher ones define (SymPy
 * imports them locally): set by functions.ts and dyadic.ts when loaded.
 */
export const vectorHooks: {
  /** SymPy express(expr, system, system2, variables). */
  express?: (expr: Expr, system: CoordSysBase, system2?: CoordSysBase, opts?: ExpressOptions) => Expr;
  /** SymPy laplacian(expr). */
  laplacian?: (expr: Expr) => Expr;
  /** SymPy BaseDyadic(v1, v2) of two base vectors. */
  baseDyadic?: (v1: Expr, v2: Expr) => Expr;
  /** SymPy directional_derivative(field, direction_vector). */
  directionalDerivative?: (field: Expr, direction: Expr) => Expr;
} = {};

/**
 * SymPy Del, as the lower vector modules see it (implemented by Del in
 * deloperator.ts): `v.dot(delop)` is the directional derivative operator.
 */
export abstract class DelBase extends ExtensionExpr {
  /** Marks the Del operator (SymPy isinstance(other, Del)). */
  readonly isDelOperator = true as const;
}

/** SymPy express (registered by functions.ts). */
export function expressHook(expr: Expr, system: CoordSysBase, system2?: CoordSysBase, opts?: ExpressOptions): Expr {
  return defined(vectorHooks.express, 'express')(expr, system, system2, opts);
}

/**
 * The matrix product as SymPy computes it: each entry is the sum of the
 * products, not expanded (Matrix.mul of @symjs/symjs/matrices expands it).
 */
export function matMul(a: Matrix, b: Matrix): Matrix {
  return Matrix.fromFunction(a.rows, b.cols, (r, c) => add(...Array.from({ length: a.cols }, (_, k) => mul(a.get(r, k), b.get(k, c)))));
}
