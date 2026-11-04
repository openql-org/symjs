// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/sets/fancysets.py: ComplexRegion, normalize_theta_set),
// Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file SymPy ComplexRegion: a region of the complex plane given by a
 * product (or a union of products) of real sets, in rectangular form
 * (CartesianComplexRegion, x + I*y) or polar form (PolarComplexRegion,
 * r*(cos(theta) + I*sin(theta)) with theta normalized to [0, 2*pi)).
 */

import { NotImplementedError } from '../core/errors';
import type { Expr } from '../core/nodes';
import type { Truth } from '../core/truth';
import { Rational, S, impl } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, cast, first } from '../core/guard';
import { TupleNode } from '../core/containers';
import { fn } from '../functions/elementary';
import { isReal } from '../core/assumptions';
import { Mod } from '../functions/mod';
import { ratMod } from '../core/num';
import { Complexes, EmptySet, FiniteSet, Interval, ProductSetNode, Reals, SetExpr, SetOp, cmpReal, containsQ, finiteSet, interval, isSubset, productSet, union } from './sets';

const TWO_PI = (): Expr => mul(2, S.Pi);

/** The products of a region's sets: the set itself, or the arguments of a union of products. */
function productsOf(sets: SetExpr): ProductSetNode[] {
  const parts = sets instanceof ProductSetNode ? [sets] : sets instanceof SetOp && sets.op === 'Union' ? sets.args : [sets];
  return parts.map((p) => cast(p, ProductSetNode, 'ComplexRegion: a product of two sets'));
}

/** The base class of CartesianComplexRegion and PolarComplexRegion (SymPy ComplexRegion). */
export abstract class ComplexRegionNode extends SetExpr {
  readonly args: readonly Expr[];
  constructor(readonly sets: SetExpr) {
    super();
    this.args = [sets];
  }
  /** Is the region in polar form? */
  abstract get polar(): boolean;
  /** SymPy ComplexRegion.from_real(sets): the real set sets as a region (sets x {0}); sets must be real. */
  static fromReal(sets: SetExpr): SetExpr {
    if (isSubset(sets, Reals) !== true) throw new RangeError('sets must be a subset of the real line');
    return complexRegion(productSet(sets, finiteSet(0)));
  }
  /** SymPy ComplexRegion.psets: the products the region is made of. */
  get psets(): ProductSetNode[] {
    return productsOf(this.sets);
  }
  /** SymPy a_interval: the union of the first factors (x or r). */
  get aInterval(): SetExpr {
    return union(...this.psets.map((p) => at(p.args, 0)));
  }
  /** SymPy b_interval: the union of the second factors (y or theta). */
  get bInterval(): SetExpr {
    return union(...this.psets.map((p) => at(p.args, 1)));
  }
  protected computeKey(): string {
    return `${this.className}(${this.sets.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `${this.className}(${p(this.sets)})`;
  }
  /** SymPy LatexPrinter._print_ComplexRegion. */
  printLatex(p: (e: Expr) => string): string {
    const head = this.polar ? 'r \\left(i \\sin{\\left(\\theta \\right)} + \\cos{\\left(\\theta \\right)}\\right)\\; \\middle|\\; r, \\theta' : 'x + y i\\; \\middle|\\; x, y';
    return `\\left\\{${head} \\in ${p(this.sets)} \\right\\}`;
  }
  override withArgs(args: readonly Expr[]): Expr {
    return complexRegion(cast(first(args), SetExpr, 'ComplexRegion sets'), this.polar);
  }
  /** SymPy ComplexRegion._contains: a number (or a Tuple of its two coordinates) in one of the products. */
  override elementOf(x: Expr): Truth {
    const isTuple = x instanceof TupleNode;
    if (isTuple && x.args.length !== 2) throw new RangeError('expecting Tuple of length 2');
    if (x.kind === 'Set') return false;
    const anyOf = (f: (p: ProductSetNode) => (boolean | undefined)[]): Truth => {
      const vs = this.psets.map((p) => {
        const cs = f(p);
        return cs.every((c) => c === true) ? true : cs.some((c) => c === false) ? false : undefined;
      });
      return vs.some((v) => v === true) ? true : vs.every((v) => v === false) ? false : 'unknown';
    };
    const [a, b] = isTuple ? [at(x.args, 0), at(x.args, 1)] : this.polar ? [fn('abs', [x]), fn('arg', [x])] : [fn('re', [x]), fn('im', [x])];
    if (!this.polar) return anyOf((p) => [containsQ(at(p.args, 0), a), containsQ(at(p.args, 1), b)]);
    // the argument of 0 is undefined: only the radius counts
    if (!isTuple && x instanceof Rational && x.isZero) return anyOf((p) => [containsQ(at(p.args, 0), S.Zero)]);
    if (b.freeSymbols().size || isReal(b) !== true) return 'unknown';
    // the angles are normalized to [0, 2*pi)
    const theta = Mod(b, TWO_PI());
    return anyOf((p) => [containsQ(at(p.args, 0), a), containsQ(at(p.args, 1), theta)]);
  }
}

/** A region in rectangular form: {x + I*y : (x, y) in sets} (SymPy CartesianComplexRegion). */
export class CartesianComplexRegion extends ComplexRegionNode {
  get className(): string {
    return 'CartesianComplexRegion';
  }
  get polar(): boolean {
    return false;
  }
}

/** A region in polar form: {r*(cos(theta) + I*sin(theta)) : (r, theta) in sets} (SymPy PolarComplexRegion). */
export class PolarComplexRegion extends ComplexRegionNode {
  get className(): string {
    return 'PolarComplexRegion';
  }
  get polar(): boolean {
    return true;
  }
}

/** SymPy _pi_coeff(x): k in [0, 2) with x = k*pi modulo 2*pi for a rational k, or undefined. */
function piCoeff(x: Expr): Rational | undefined {
  const k = mul(x, pow(S.Pi, -1));
  if (!(k instanceof Rational)) return undefined;
  return ratMod(k, Rational.of(2n));
}

/**
 * SymPy normalize_theta_set(theta): the angles of theta in [0, 2*pi) (an
 * interval, finite set or union of them whose ends are rational multiples
 * of pi).
 */
export function normalizeThetaSet(theta: SetExpr): SetExpr {
  if (theta instanceof Interval) {
    const len = add(theta.end, mul(-1, theta.start));
    const c = cmpReal(len, TWO_PI());
    if (c !== undefined && c >= 0) {
      if (c === 0 && theta.leftOpen && theta.rightOpen) {
        const k = piCoeff(theta.start);
        if (!k) throw new NotImplementedError('Normalizing theta without pi as coefficient is not yet implemented');
        return union(interval(0, mul(k, S.Pi), false, true), interval(mul(k, S.Pi), TWO_PI(), true, true));
      }
      return interval(0, TWO_PI(), false, true);
    }
    const ks = piCoeff(theta.start);
    const ke = piCoeff(theta.end);
    if (!ks || !ke) throw new NotImplementedError('Normalizing theta without pi as coefficient is not yet implemented');
    const start = mul(ks, S.Pi);
    const end = mul(ke, S.Pi);
    if (cmpReal(start, end) === 1) return union(interval(0, end, false, theta.rightOpen), interval(start, TWO_PI(), theta.leftOpen, true));
    return interval(start, end, theta.leftOpen, theta.rightOpen);
  }
  if (theta instanceof FiniteSet) {
    return finiteSet(
      ...theta.args.map((e) => {
        const k = piCoeff(e);
        if (!k) throw new NotImplementedError('Normalizing theta without pi as coefficient, is not Implemented.');
        return mul(k, S.Pi);
      }),
    );
  }
  if (theta instanceof SetOp && theta.op === 'Union') return union(...theta.args.map(normalizeThetaSet));
  if (theta === EmptySet) return theta;
  if (isSubset(theta, Reals) === true) throw new NotImplementedError(`Normalizing theta when, it is of type ${theta.className} is not implemented`);
  throw new RangeError(`${impl.str(theta)} is not a real set`);
}

/**
 * SymPy ComplexRegion(sets, polar=False): the region of the complex plane;
 * Reals x Reals is Complexes, and a product of two finite sets in
 * rectangular form is the finite set of its points.
 */
export function complexRegion(sets: SetExpr, polar = false): SetExpr {
  if (polar) return new PolarComplexRegion(union(...productsOf(sets).map((p) => productSet(at(p.args, 0), normalizeThetaSet(at(p.args, 1))))));
  if (sets instanceof ProductSetNode && sets.args.length === 2 && sets.args.every((a) => a === Reals)) return Complexes;
  if (sets instanceof ProductSetNode && sets.args.length === 2 && sets.args.every((a) => a instanceof FiniteSet)) {
    const [xs, ys] = [at(sets.args, 0), at(sets.args, 1)];
    return finiteSet(...xs.args.flatMap((x) => ys.args.map((y) => add(x, mul(S.I, y)))));
  }
  return new CartesianComplexRegion(sets);
}

/** SymPy ComplexRegion(sets, polar=false), with ComplexRegion.fromReal(sets). */
export const ComplexRegion = /* @__PURE__ */ callableClass(ComplexRegionNode, complexRegion);
export type ComplexRegion = ComplexRegionNode;
