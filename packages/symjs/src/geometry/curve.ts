// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/curve.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.curve: parametric curves (x(t), y(t)) for t in
 * an interval [a, b].
 */

import { Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, subs } from '../core/traverse';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { diff } from '../calculus/diff';
import { integrate } from '../integrals/integrate';
import { Matrix } from '../matrices/matrix';
import { rotAxis3 } from '../matrices/linalg';
import { GeometrySet } from './entity';
import type { PointInput } from './entity';
import type { PointNode} from './point';
import { toPoint } from './point';

const asTuple = (e: Expr | undefined): TupleNode => cast(e, TupleNode, 'Tuple');

/**
 * SymPy _symbol(name, parameter, real=True): the parameter itself when it
 * has that name, else a real symbol of that name.
 */
function symbolLike(name: string | Sym, parameter: Sym): Sym {
  if (name instanceof Sym) return name;
  return name === parameter.name ? parameter : new Sym(name, { real: true });
}

/**
 * The parametric curve (x(t), y(t)) for t in [a, b].
 *
 * @see SymPy `sympy.geometry.curve.Curve`
 * @example
 * ```ts
 * import { Curve, cos, ex, sin } from '@symjs/symjs';
 *
 * const curve = Curve([ex`sin(t)`, ex`cos(t)`], [ex`t`, 0, 2]);
 * curve.parameter; // => t
 * curve.at(0); // => Point2D(0, 1)
 * ```
 */
export class CurveNode extends GeometrySet {
  /**
   * Constructs an instance of `CurveNode`.
   *
   * @param functions - Coordinate functions in parameter order.
   * @param limits - Bound variables and their inclusive limits.
   */
  constructor(functions: TupleNode, limits: TupleNode) {
    super('Curve', [functions, limits]);
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return newCurve(asTuple(args[0]).args, asTuple(args[1]).args);
  }

  /**
   * The coordinate functions.
   *
   * @returns The coordinate functions.
   * @see SymPy `sympy.geometry.curve.Curve.functions`
   */
  get functions(): TupleNode {
    return asTuple(this.args[0]);
  }

  /**
   * The limits (t, a, b).
   *
   * @returns The limits (t, a, b).
   * @see SymPy `sympy.geometry.curve.Curve.limits`
   */
  get limits(): TupleNode {
    return asTuple(this.args[1]);
  }

  /**
   * The parameter t.
   *
   * @returns The parameter t.
   * @see SymPy `sympy.geometry.curve.Curve.parameter`
   */
  get parameter(): Sym {
    return cast(this.limits.at(0), Sym, 'the parameter');
  }

  /**
   * The number of coordinates in the surrounding space.
   *
   * @returns The number of coordinates in the surrounding space.
   * @see SymPy `sympy.geometry.curve.Curve.ambient_dimension`
   */
  get ambientDimension(): number {
    return this.functions.length;
  }

  /**
   * The free symbols other than the parameter.
   *
   * @returns The free symbols other than the parameter.
   * @see SymPy `sympy.geometry.curve.Curve.free_symbols`
   */
  override freeSymbols(): Set<Expr> {
    const free = new Set<Expr>();
    for (const a of [...this.functions.args, ...this.limits.args.slice(1)]) for (const s of freeSymbols(a)) free.add(s);
    for (const s of free) if (s.key === this.parameter.key) free.delete(s);
    return free;
  }

  /**
   * The point of the curve at the value f of the parameter.
   *
   * @param f - Parameter value at which to evaluate the curve.
   * @returns The point on the curve at `f`.
   * @see SymPy `sympy.geometry.curve.Curve.__call__`
   */
  at(f: ExprLike): PointNode {
    return toPoint(this.functions.args.map((g) => subs(g, [[this.parameter, f]])));
  }

  /**
   * Substituting the parameter gives the point of the curve.
   *
   * @param old - Expression to replace.
   * @param nw - Expression to substitute in its place.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.geometry.curve.Curve._eval_subs`
   */
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (old.key === this.parameter.key) return this.at(nw);
    return undefined;
  }

  /**
   * The functions and limits evaluated numerically.
   *
   * @param evalfArg - Function that evaluates an operand numerically.
   * @param _dps - Decimal digits of numerical precision.
   * @returns The numerically evaluated expression.
   * @see SymPy `sympy.geometry.curve.Curve._eval_evalf`
   */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    const [t, a, b] = this.limits.args;
    return newCurve(this.functions.args.map(evalfArg), [defd(t), evalfArg(defd(a)), evalfArg(defd(b))]);
  }

  /**
   * The point of the curve in terms of a parameter (the curve's own one by default; null keeps the
   * functions as they are).
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The point of the curve in terms of a parameter (the curve's own one by default; null keeps the functions as they are).
   * @throws RangeError when the requested parameter name already occurs in the entity.
   * @see SymPy `sympy.geometry.curve.Curve.arbitrary_point`
   */
  override arbitraryPoint(parameter: string | Sym | null = 't'): PointNode {
    if (parameter === null) return toPoint(this.functions.args);
    const tnew = symbolLike(parameter, this.parameter);
    const t = this.parameter;
    if (tnew.name !== t.name && [...this.freeSymbols()].filter((s) => s instanceof Sym).some((f) => f.name === tnew.name)) {
      throw new RangeError(`Symbol ${tnew.name} already appears in object and cannot be used as a parameter.`);
    }
    return toPoint(this.functions.args.map((w) => subs(w, [[t, tnew]])));
  }

  /**
   * The arc length.
   *
   * @returns The arc length.
   * @see SymPy `sympy.geometry.curve.Curve.length`
   */
  get length(): Expr {
    const t = this.parameter;
    const integrand = sqrt(add(...this.functions.args.map((f) => pow(diff(f, t), 2))));
    const [, a, b] = this.limits.args;
    return integrate(integrand, t, [defd(a), defd(b)]);
  }

  /**
   * The parameter interval [t, a, b] used for plotting.
   *
   * @param parameter - Symbol or name used for the parametrization.
   * @returns The parameter interval [t, a, b] used for plotting.
   * @see SymPy `sympy.geometry.curve.Curve.plot_interval`
   */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    const t = symbolLike(parameter, this.parameter);
    const [, a, b] = this.limits.args;
    return [t, defd(a), defd(b)];
  }

  /**
   * The curve rotated counterclockwise by angle about pt.
   *
   * @param angle - Rotation angle in radians.
   * @param pt - Center of rotation, defaulting to the origin.
   * @returns The curve rotated counterclockwise by angle about pt.
   * @see SymPy `sympy.geometry.curve.Curve.rotate`
   */
  override rotate(angle: ExprLike = 0, pt?: PointInput | null): CurveNode {
    const p = pt !== undefined && pt !== null ? toPoint(pt, { dim: 2 }).neg() : toPoint([0, 0]);
    const rv = this.translate(...pair(p.args));
    const f = Matrix.of([[...rv.functions.args, 0]]).mul(rotAxis3(sympify(angle)));
    const moved = newCurve([f.get(0, 0), f.get(0, 1)], this.limits.args);
    const back = p.neg();
    return moved.translate(...pair(back.args));
  }

  /**
   * The curve scaled by x and y about pt.
   *
   * @param x - Scale factor along the x axis.
   * @param y - Scale factor along the y axis.
   * @param pt - Fixed point of the scaling, defaulting to the origin.
   * @returns The curve scaled by x and y about pt.
   * @see SymPy `sympy.geometry.curve.Curve.scale`
   */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): CurveNode {
    if (pt !== undefined && pt !== null) {
      const p = toPoint(pt, { dim: 2 });
      return this.translate(...pair(p.neg().args)).scale(x, y).translate(...pair(p.args));
    }
    const [fx, fy] = this.functions.args;
    return newCurve([mul(defd(fx), x), mul(defd(fy), y)], this.limits.args);
  }

  /**
   * The curve shifted by x and y.
   *
   * @param x - Displacement along the x axis.
   * @param y - Displacement along the y axis.
   * @returns The curve shifted by x and y.
   * @see SymPy `sympy.geometry.curve.Curve.translate`
   */
  override translate(x: ExprLike = 0, y: ExprLike = 0): CurveNode {
    const [fx, fy] = this.functions.args;
    return newCurve([add(defd(fx), x), add(defd(fy), y)], this.limits.args);
  }
}

const defd = <T>(e: T | undefined): T => defined(e, 'value');
const pair = (xs: readonly Expr[]): [Expr, Expr] => [at(xs, 0), at(xs, 1)];

/** SymPy Curve.__new__(function, limits). */
function newCurve(fs: readonly ExprLike[] | TupleNode, ls: readonly ExprLike[] | TupleNode): CurveNode {
  const f = fs instanceof TupleNode ? fs.args : Array.isArray(fs) ? fs.map(sympify) : undefined;
  if (f?.length !== 2) throw new RangeError(`Function argument should be (x(t), y(t)) but got ${String(fs)}`);
  const l = ls instanceof TupleNode ? ls.args : Array.isArray(ls) ? ls.map(sympify) : undefined;
  if (l?.length !== 3) throw new RangeError(`Limit argument should be (t, tmin, tmax) but got ${String(ls)}`);
  return new CurveNode(new TupleNode(f), new TupleNode(l));
}

/**
 * A plane curve specified by two coordinate functions over a parameter interval.
 *
 * @param functions - Coordinate functions in parameter order.
 * @param limits - Bound variables and their inclusive limits.
 * @returns The resulting `Curve` expression.
 * @throws RangeError when the coordinate functions are not a pair or the parameter limits are not a triple.
 * @see SymPy `sympy.geometry.curve.Curve`
 * @example
 * ```ts
 * import { Curve, cos, ex, sin } from '@symjs/symjs';
 *
 * const curve = Curve([ex`sin(t)`, ex`cos(t)`], [ex`t`, 0, 2]);
 * curve.parameter; // => t
 * curve.at(0); // => Point2D(0, 1)
 * ```
 */
export const Curve = /* @__PURE__ */ callableClass(
  CurveNode,
  (functions: readonly ExprLike[] | TupleNode, limits: readonly ExprLike[] | TupleNode): CurveNode => newCurve(functions, limits),
);
export type Curve = CurveNode;

