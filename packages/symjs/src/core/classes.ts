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
import { Function as undefinedFunction } from './undef';
import { str } from '../printing/str';

/** A callable with a custom instanceof check. */
function withInstanceCheck<F extends (...args: never[]) => unknown>(f: F, check: (v: unknown) => boolean): F {
  Object.defineProperty(f, Symbol.hasInstance, { value: check });
  return f;
}

/**
 * SymPy Number: Number(3) is the Integer 3, Number(1.5) a Float;
 * `x instanceof Number` holds for Rationals and Floats.
 */
export const SymNumber = /* @__PURE__ */ withInstanceCheck(
  (x: ExprLike | string): Expr => {
    if (typeof x === 'string') {
      const t = x.trim();
      if (/^[-+]?\d+$/.test(t)) return Rational.of(BigInt(t));
      const m = /^([-+]?\d+)\/(\d+)$/.exec(t);
      if (m) return Rational.of(BigInt(m[1]!), BigInt(m[2]!));
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

/** SymPy RealNumber: an alias of Float. */
export const RealNumber = Float;

const generic = (head: string) => (...args: ExprLike[]): Expr => new BasicNode(args.map(sympify), head);

/** SymPy Atom: Atom() is a generic atom; `x instanceof Atom` holds for nodes without arguments. */
export const Atom = /* @__PURE__ */ withInstanceCheck(generic('Atom'), (v) => v instanceof Expr && v.args.length === 0);
/** SymPy AtomicExpr: like Atom, for expressions. */
export const AtomicExpr = /* @__PURE__ */ withInstanceCheck(generic('AtomicExpr'), (v) => v instanceof Expr && v.args.length === 0);
/** A generic Expr(*args) node (SymPy Expr(...) called directly). */
export const genericExpr = generic('Expr');

/**
 * SymPy FunctionClass: FunctionClass(name) creates an undefined function;
 * `f instanceof FunctionClass` holds for function constructors.
 */
export const FunctionClass = /* @__PURE__ */ withInstanceCheck(
  (name: string) => undefinedFunction(name),
  (v) => typeof v === 'function' && typeof (v as { functionName?: unknown }).functionName === 'string',
);

/**
 * SymPy UnevaluatedExpr: keeps its argument from combining with the rest
 * (x*UnevaluatedExpr(1/x) stays x*1/x); doit removes it.
 */
export class UnevaluatedExpr extends ExtensionExpr {
  constructor(arg: ExprLike) {
    super('UnevaluatedExpr', [sympify(arg)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new UnevaluatedExpr(args[0]!);
  }
  override printStr(print: (e: Expr) => string): string {
    return print(this.args[0]!);
  }
  override printLatex(print: (e: Expr) => string): string {
    return print(this.args[0]!);
  }
  override doitSelf(): Expr {
    return this.args[0]!;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return d(this.args[0]!, x);
  }
}

/**
 * SymPy DeferredVector: a symbol standing for a vector; X.at(i) is the
 * symbol X[i], and lambdify takes an array for it.
 */
export class DeferredVector extends Sym {
  constructor(name: string, assumptions: Assumptions = {}) {
    super(name, assumptions);
  }
  /** The component symbol X[i]. */
  at(i: number): Sym {
    if (i < 0) throw new RangeError('DeferredVector index out of range');
    return new Sym(`${this.name}[${i}]`);
  }
}
