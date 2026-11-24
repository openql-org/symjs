// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's base classes as constructors and instanceof checks
 * (Number, RealNumber, Atom, AtomicExpr, FunctionClass), UnevaluatedExpr
 * and DeferredVector.
 */

import type { ExprLike } from './nodes';
import { Expr, ExtensionExpr, Float, Rational, Sym, type Assumptions } from './nodes';
import { sympify } from './ops';
import { BasicNode } from './basic';
import { SymFunction as undefinedFunction } from './undef';
import { str } from '../printing/str';
import { at } from './guard';

/** A callable with a custom instanceof check. */
function withInstanceCheck<F extends (...args: never[]) => unknown>(f: F, check: (v: unknown) => boolean): F {
  Object.defineProperty(f, Symbol.hasInstance, { value: check });
  return f;
}

/**
 * Converts a numeric value to a symbolic number. Its instances include both rationals and floats.
 *
 * @param x - The argument of the function.
 * @returns The numeric expression.
 * @throws TypeError when the input cannot be converted to a number.
 * @see SymPy `sympy.core.numbers.Number`
 */
export const SymNumber = /* @__PURE__ */ withInstanceCheck(
  (x: ExprLike | string): Expr => {
    if (typeof x === 'string') {
      const t = x.trim();
      if (/^[-+]?\d+$/.test(t)) return Rational.of(BigInt(t));
      const m = /^([-+]?\d+)\/(\d+)$/.exec(t);
      if (m) return Rational.of(BigInt(at(m, 1)), BigInt(at(m, 2)));
      const v = globalThis.Number(t);
      if (Number.isNaN(v)) throw new TypeError(`Number: cannot convert ${x}`);
      return new Float(v);
    }
    const e = sympify(x);
    if (!(e instanceof Rational || e instanceof Float)) throw new TypeError(`Number: ${str(e)} is not a number`);
    return e;
  },
  (v) => v instanceof Rational || v instanceof Float,
);

/**
 * An alias of Float.
 *
 * @see SymPy `sympy.core.numbers.Float`
 * @example
 * ```ts
 * import { RealNumber } from '@symjs/symjs';
 *
 * new RealNumber(1.5); // => 1.50000000000000
 * ```
 */
export const RealNumber = Float;

const generic = (head: string) => (...args: ExprLike[]): Expr => new BasicNode(args.map(sympify), head);

/**
 * Atom() is a generic atom; `x instanceof Atom` holds for nodes without arguments.
 *
 * @param args - The arguments in positional order.
 * @returns The constructed symbolic node.
 * @see SymPy `sympy.core.basic.Atom`
 */
export const Atom = /* @__PURE__ */ withInstanceCheck(generic('Atom'), (v) => v instanceof Expr && v.args.length === 0);
/**
 * like Atom, for expressions.
 *
 * @param args - The arguments in positional order.
 * @returns The constructed symbolic node.
 * @see SymPy `sympy.core.expr.AtomicExpr`
 */
export const AtomicExpr = /* @__PURE__ */ withInstanceCheck(generic('AtomicExpr'), (v) => v instanceof Expr && v.args.length === 0);
/**
 * A generic Expr(*args) node (SymPy Expr(...) called directly).
 *
 * @param args - The arguments in positional order.
 * @returns The constructed symbolic node.
 * @see SymPy `sympy.core.expr.Expr`
 */
export const genericExpr = generic('Expr');

/**
 * FunctionClass(name) creates an undefined function;
 * `f instanceof FunctionClass` holds for function constructors.
 *
 * @param name - The symbolic name or names.
 * @returns The callable function head.
 * @see SymPy `sympy.core.function.FunctionClass`
 */
export const FunctionClass = /* @__PURE__ */ withInstanceCheck(
  (name: string) => undefinedFunction(name),
  (v) => typeof v === 'function' && 'functionName' in v && typeof v.functionName === 'string',
);

/**
 * keeps its argument from combining with the rest
 * (x*UnevaluatedExpr(1/x) stays x*1/x); doit removes it.
 *
 * @see SymPy `sympy.core.expr.UnevaluatedExpr`
 * @example
 * ```ts
 * import { UnevaluatedExpr, doit, ex } from '@symjs/symjs';
 *
 * doit(new UnevaluatedExpr(ex`1/x`)); // => 1/x
 * ```
 */
export class UnevaluatedExpr extends ExtensionExpr {
  /**
   * Creates an `UnevaluatedExpr`.
   *
   * @param arg - The expression held unevaluated.
   */
  constructor(arg: ExprLike) {
    super('UnevaluatedExpr', [sympify(arg)]);
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new UnevaluatedExpr(at(args, 0));
  }
  /**
   * Formats the node using the expression printer for its arguments.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printStr(print: (e: Expr) => string): string {
    return print(at(this.args, 0));
  }
  /**
   * Formats the node in LaTeX using the supplied child printer.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printLatex(print: (e: Expr) => string): string {
    return print(at(this.args, 0));
  }
  /**
   * Evaluates the held expression.
   *
   * @returns The wrapped expression.
   */
  override doitSelf(): Expr {
    return at(this.args, 0);
  }
  /**
   * Computes the derivative using the node's differentiation rule.
   *
   * @param x - The differentiation variable.
   * @param d - The callback for differentiating a subexpression.
   * @returns The derivative using the node's differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return d(at(this.args, 0), x);
  }
}

/**
 * A symbol standing for a vector; X.at(i) is the
 * symbol X[i], and lambdify takes an array for it.
 *
 * @see SymPy `sympy.matrices.matrixbase.DeferredVector`
 * @example
 * ```ts
 * import { DeferredVector } from '@symjs/symjs';
 *
 * new DeferredVector('X'); // => X
 * ```
 */
export class DeferredVector extends Sym {
  /**
   * Creates a `DeferredVector`.
   *
   * @param name - The symbolic name or names.
   * @param assumptions - The facts to assume.
   */
  constructor(name: string, assumptions: Assumptions = {}) {
    super(name, assumptions);
  }
  /**
   * The component symbol X[i].
   *
   * @param i - The zero-based index.
   * @returns The component symbol X[i].
   * @throws RangeError when the component index is negative.
   */
  at(i: number): Sym {
    if (i < 0) throw new RangeError('DeferredVector index out of range');
    return new Sym(`${this.name}[${i}]`);
  }
}
