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

/** SymPy Curve: the parametric curve (x(t), y(t)) for t in [a, b]. */
export class CurveNode extends GeometrySet {
  constructor(functions: TupleNode, limits: TupleNode) {
    super('Curve', [functions, limits]);
  }

  override withArgs(args: readonly Expr[]): Expr {
    return newCurve(asTuple(args[0]).args, asTuple(args[1]).args);
  }

  /** The coordinate functions (SymPy functions). */
  get functions(): TupleNode {
    return asTuple(this.args[0]);
  }

  /** The limits (t, a, b) (SymPy limits). */
  get limits(): TupleNode {
    return asTuple(this.args[1]);
  }

  /** The parameter t (SymPy parameter). */
  get parameter(): Sym {
    return cast(this.limits.at(0), Sym, 'the parameter');
  }

  get ambientDimension(): number {
    return this.functions.length;
  }

  /** The free symbols other than the parameter (SymPy free_symbols). */
  override freeSymbols(): Set<Sym> {
    const free = new Set<Sym>();
    for (const a of [...this.functions.args, ...this.limits.args.slice(1)]) for (const s of freeSymbols(a)) free.add(s);
    for (const s of free) if (s.key === this.parameter.key) free.delete(s);
    return free;
  }

  /** The point of the curve at the value f of the parameter (SymPy Curve.__call__). */
  at(f: ExprLike): PointNode {
    return toPoint(this.functions.args.map((g) => subs(g, [[this.parameter, f]])));
  }

  /** SymPy Curve._eval_subs: substituting the parameter gives the point of the curve. */
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (old.key === this.parameter.key) return this.at(nw);
    return undefined;
  }

  /** The functions and limits evaluated numerically (SymPy _eval_evalf). */
  override evalfSelf(evalfArg: (e: Expr) => Expr, _dps: number): Expr {
    const [t, a, b] = this.limits.args;
    return newCurve(this.functions.args.map(evalfArg), [defd(t), evalfArg(defd(a)), evalfArg(defd(b))]);
  }

  /**
   * The point of the curve in terms of a parameter (the curve's own one by
   * default; null keeps the functions as they are) (SymPy arbitrary_point).
   */
  override arbitraryPoint(parameter: string | Sym | null = 't'): PointNode {
    if (parameter === null) return toPoint(this.functions.args);
    const tnew = symbolLike(parameter, this.parameter);
    const t = this.parameter;
    if (tnew.name !== t.name && [...this.freeSymbols()].some((f) => f.name === tnew.name)) {
      throw new RangeError(`Symbol ${tnew.name} already appears in object and cannot be used as a parameter.`);
    }
    return toPoint(this.functions.args.map((w) => subs(w, [[t, tnew]])));
  }

  /** The arc length (SymPy length). */
  get length(): Expr {
    const t = this.parameter;
    const integrand = sqrt(add(...this.functions.args.map((f) => pow(diff(f, t), 2))));
    const [, a, b] = this.limits.args;
    return integrate(integrand, t, [defd(a), defd(b)]);
  }

  /** The parameter interval [t, a, b] used for plotting (SymPy plot_interval). */
  plotInterval(parameter: string | Sym = 't'): [Sym, Expr, Expr] {
    const t = symbolLike(parameter, this.parameter);
    const [, a, b] = this.limits.args;
    return [t, defd(a), defd(b)];
  }

  /** The curve rotated counterclockwise by angle about pt (SymPy rotate). */
  override rotate(angle: ExprLike = 0, pt?: PointInput | null): CurveNode {
    const p = pt !== undefined && pt !== null ? toPoint(pt, { dim: 2 }).neg() : toPoint([0, 0]);
    const rv = this.translate(...pair(p.args));
    const f = Matrix.of([[...rv.functions.args, 0]]).mul(rotAxis3(sympify(angle)));
    const moved = newCurve([f.get(0, 0), f.get(0, 1)], this.limits.args);
    const back = p.neg();
    return moved.translate(...pair(back.args));
  }

  /** The curve scaled by x and y about pt (SymPy scale). */
  override scale(x: ExprLike = 1, y: ExprLike = 1, pt?: PointInput | null): CurveNode {
    if (pt !== undefined && pt !== null) {
      const p = toPoint(pt, { dim: 2 });
      return this.translate(...pair(p.neg().args)).scale(x, y).translate(...pair(p.args));
    }
    const [fx, fy] = this.functions.args;
    return newCurve([mul(defd(fx), x), mul(defd(fy), y)], this.limits.args);
  }

  /** The curve shifted by x and y (SymPy translate). */
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

/** SymPy Curve((x(t), y(t)), (t, a, b)). */
export const Curve = /* @__PURE__ */ callableClass(
  CurveNode,
  (functions: readonly ExprLike[] | TupleNode, limits: readonly ExprLike[] | TupleNode): CurveNode => newCurve(functions, limits),
);
export type Curve = CurveNode;

