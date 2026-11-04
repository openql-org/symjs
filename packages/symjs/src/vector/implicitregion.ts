// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/implicitregion.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.implicitregion: ImplicitRegion, a region of
 * space given by an implicit equation, with its points (regular and
 * singular), the multiplicity of a point and the rational parametrization
 * of a monoid (conics, cubics with a double point, quadrics).
 */

import { Add, ExtensionExpr, Float, Rational, Rel, S, Sym, isNum } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sqrt, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { at, cast, defined } from '../core/guard';
import { TupleNode } from '../core/containers';
import { coeff } from '../core/methods';
import { freeSymbols, subs } from '../core/traverse';
import { ordered } from '../core/match';
import { NotImplementedError } from '../core/errors';
import { gcd } from '../core/numbers';
import { limitDenominator } from '../core/numberutils';
import { toRational } from '../numeric/mpf';
import { diff } from '../calculus/diff';
import { expand } from '../simplify/expand';
import { Poly } from '../polys/sympoly';
import { factorint } from '../ntheory/factor';
import type { SetExpr} from '../sets/sets';
import { EmptySet, FiniteSet, Reals, finiteSet } from '../sets/sets';
import { solveset } from '../solvers/inequalities';
import { nonlinsolve } from '../solvers/solve';
import { diophantine } from '../solvers/diophantine';
import { GeometryEntity } from '../geometry/entity';
import { realSymbol } from '../geometry/entity';

/** SymPy total_degree(expr): the total degree in the free symbols (0 for a constant). */
export function totalDegree(e: Expr): number {
  const gens = ordered([...freeSymbols(e)]);
  return gens.length === 0 ? 0 : Poly.from(e, gens).totalDegree();
}

/** The elements of a finite set of solutions, in the set's order. */
function elements(s: SetExpr): Expr[] {
  if (!(s instanceof FiniteSet)) throw new NotImplementedError(`the solutions ${String(s)} are not a finite set`);
  return [...s.args];
}

const isZero = (e: Expr): boolean => isNum(e) && e.isZero;

/** SymPy conic_coeff(variables, equation): the coefficients a, b, c, d, e, f of a*x**2 + b*x*y + c*y**2 + d*x + e*y + f. */
export function conicCoeff(variables: readonly Expr[], equationIn: Expr): [Expr, Expr, Expr, Expr, Expr, Expr] {
  if (totalDegree(equationIn) !== 2) throw new RangeError('the equation of a conic has degree 2');
  const [x, y] = [at(variables, 0), at(variables, 1)];
  const eq = expand(equationIn);
  const c0 = (e: Expr, v: Expr): Expr => coeff(e, v, 0);
  return [coeff(eq, x.pow(2)), coeff(eq, mul(x, y)), coeff(eq, y.pow(2)), c0(coeff(eq, x, 1), y), c0(coeff(eq, y, 1), x), c0(c0(eq, x), y)];
}

/** SymPy core(n, 2): the square-free part of a positive integer. */
function squareFree(n: bigint): bigint {
  let r = 1n;
  for (const [p, e] of factorint(n)) if (e % 2n === 1n) r *= p;
  return r;
}

/** An exact rational value of a coefficient (SymPy Rational(K).limit_denominator(10**12)). */
function rationalOf(e: Expr): Rational {
  if (e instanceof Rational) return limitDenominator(e, 10n ** 12n);
  if (e instanceof Float) {
    const [p, q] = toRational(e.mpf);
    return limitDenominator(Rational.of(p, q), 10n ** 12n);
  }
  throw new TypeError(`${String(e)} is not a number`);
}

/** The n-th integer in SymPy's order of S.Integers: 0, 1, -1, 2, -2, ... */
const integerAt = (n: number): number => (n % 2 === 1 ? (n + 1) / 2 : -n / 2);

/** The first integer (in the order of S.Integers) at which e does not vanish (SymPy next(iter(Complement(Integers, roots)))). */
function firstNonRoot(e: Expr, p: Sym): number | undefined {
  // a polynomial that is not identically zero has finitely many roots
  if (expand(e).key === S.Zero.key) return undefined;
  for (let n = 0; ; n++) if (!isZero(subs(e, [[p, integerAt(n)]]))) return integerAt(n);
}

/** SymPy ImplicitRegion(variables, equation): the region where equation vanishes. */
export class ImplicitRegionNode extends ExtensionExpr {
  constructor(variables: readonly ExprLike[] | TupleNode, equation: ExprLike) {
    const vars = variables instanceof TupleNode ? variables : new TupleNode(variables.map(sympify));
    const eq = sympify(equation);
    super('ImplicitRegion', [vars, eq instanceof Rel && eq.op === 'Eq' ? add(eq.lhs, mul(-1, eq.rhs)) : eq]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ImplicitRegionNode(cast(at(args, 0), TupleNode, 'variables'), at(args, 1));
  }
  /** SymPy variables: the variables that map to the base scalars. */
  get variables(): Sym[] {
    return at(this.args, 0).args.map((v) => cast(v, Sym, 'variable'));
  }
  /** SymPy equation (lhs - rhs of an Eq). */
  get equation(): Expr {
    return at(this.args, 1);
  }
  /** SymPy degree: the total degree of the equation. */
  get degree(): number {
    return totalDegree(this.equation);
  }

  /** SymPy regular_point: a point on the region. */
  regularPoint(): Expr[] {
    const eq = this.equation;
    const vars = this.variables;
    if (vars.length === 1) return [defined(elements(solveset(eq, at(vars, 0), Reals))[0], 'point')];
    if (vars.length === 2 && this.degree === 2) {
      const cs = conicCoeff(vars, eq);
      const [a, b, c] = cs;
      return b.pow(2).key === mul(4, a, c).key ? regularPointParabola(...cs) : regularPointEllipse(...cs);
    }
    if (vars.length === 3) {
      const [x, y, z] = vars;
      for (let xr = -10; xr < 10; xr++) {
        for (let yr = -10; yr < 10; yr++) {
          const e = subs(eq, [
            [defined(x, 'x'), xr],
            [defined(y, 'y'), yr],
          ]);
          if (solveset(e, defined(z, 'z'), Reals) !== EmptySet) {
            const [only] = [...freeSymbols(e)];
            return [sympify(xr), sympify(yr), defined(elements(solveset(e, defined(only, 'variable')))[0], 'point')];
          }
        }
      }
    }
    // (SymPy returns list[self.singular_points()][0], which is not a point)
    const sp = this.singularPoints();
    if (sp instanceof FiniteSet) return [...at(sp.args, 0).args];
    throw new NotImplementedError('no regular point of the region is known');
  }

  /** SymPy singular_points: the points of the region where all partial derivatives vanish. */
  singularPoints(): SetExpr {
    const eq = this.equation;
    const vars = this.variables;
    const sols = nonlinsolve([eq, ...vars.map((v) => diff(eq, v))], vars);
    return sols.length === 0 ? EmptySet : finiteSet(...sols.map((s) => new TupleNode(s)));
  }

  /**
   * SymPy multiplicity(point): the multiplicity of a point of the region (the
   * lowest total degree of the equation shifted to the point).
   */
  multiplicity(pointIn: GeometryEntity | readonly ExprLike[] | TupleNode): number {
    const point = pointIn instanceof GeometryEntity || pointIn instanceof TupleNode ? pointIn.args : pointIn.map(sympify);
    let modified = this.equation;
    this.variables.forEach((v, i) => {
      modified = subs(modified, [[v, add(v, at(point, i))]]);
    });
    modified = expand(modified);
    // (SymPy takes the args of a single term as the terms: multiplicity((0, 0)) of x*y is 1 there, not 2)
    return Math.min(...(modified instanceof Add ? modified.args : [modified]).map(totalDegree));
  }

  /**
   * SymPy rational_parametrization(parameters=('t', 's'), reg_point=None): a
   * rational parametrization of the region, from a regular point of a conic
   * (`regPoint` when none is found) or a point of multiplicity degree - 1.
   */
  rationalParametrization(parametersIn?: string | Sym | readonly (string | Sym)[], opts: { regPoint?: readonly ExprLike[] } = {}): Expr[] {
    const equation = this.equation;
    const degree = this.degree;
    const vars = this.variables;
    if (degree === 1) {
      if (vars.length === 1) return [equation];
      if (vars.length === 2) return [at(vars, 0), defined(elements(solveset(equation, at(vars, 1)))[0], 'solution')];
      throw new NotImplementedError('rational parametrization of a linear region in 3 variables');
    }
    let point: readonly Expr[] = [];
    const singular = this.singularPoints();
    const hasSingular = singular instanceof FiniteSet;
    if (degree === 2) {
      if (opts.regPoint !== undefined) point = opts.regPoint.map(sympify);
      else point = hasSingular ? at(singular.args, 0).args : this.regularPoint();
    }
    if (hasSingular) {
      for (const sp of singular.args) {
        const syms = [...freeSymbols(sp)];
        const spoint = syms.length ? sp.args.map((s) => subs(s, syms.map((x): [Expr, Expr] => [x, S.Two]))) : sp.args;
        if (this.multiplicity(spoint) === degree - 1) {
          point = spoint;
          break;
        }
      }
    }
    // the region is not a monoid
    if (point.length === 0) throw new NotImplementedError('the region is not a monoid');
    let modified = equation;
    vars.forEach((v, i) => {
      modified = subs(modified, [[v, add(v, at(point, i))]]);
    });
    modified = expand(modified);
    let hn: Expr = S.Zero;
    let hn1: Expr = S.Zero;
    for (const term of modified instanceof Add ? modified.args : [modified]) {
      if (totalDegree(term) === degree) hn = add(hn, term);
      else hn1 = add(hn1, term);
    }
    hn1 = mul(-1, hn1);
    const parameters = parametersIn === undefined ? ['t', 's'] : typeof parametersIn === 'string' || parametersIn instanceof Sym ? [parametersIn] : parametersIn;
    const ratio = (): Expr => mul(hn1, hn.pow(-1));
    if (vars.length === 2) {
      const p1 = defined(parameters[0], 'parameter');
      const s = realSymbol(p1 === 's' ? 's_' : 's');
      const t = realSymbol(p1);
      const sub = [
        [at(vars, 0), s],
        [at(vars, 1), t],
      ] as const;
      hn = subs(hn, sub);
      hn1 = subs(hn1, sub);
      const r = ratio();
      return [add(subs(mul(s, r), [[s, 1]]), at(point, 0)), add(subs(mul(t, r), [[s, 1]]), at(point, 1))];
    }
    if (vars.length === 3) {
      const [p1, p2] = [defined(parameters[0], 'parameter'), defined(parameters[1], 'parameter')];
      const r = realSymbol(parameters.includes('r') ? 'r_' : 'r');
      const s = realSymbol(p2);
      const t = realSymbol(p1);
      const sub = [
        [at(vars, 0), r],
        [at(vars, 1), s],
        [at(vars, 2), t],
      ] as const;
      hn = subs(hn, sub);
      hn1 = subs(hn1, sub);
      const q = ratio();
      return [add(subs(mul(r, q), [[r, 1]]), at(point, 0)), add(subs(mul(s, q), [[r, 1]]), at(point, 1)), add(subs(mul(t, q), [[r, 1]]), at(point, 2))];
    }
    throw new NotImplementedError('rational parametrization in more than 3 variables');
  }
}

/** SymPy _regular_point_parabola: a rational point of a parabola. */
function regularPointParabola(a: Expr, b: Expr, c: Expr, d: Expr, e: Expr, f: Expr): Expr[] {
  const z = (v: Expr): boolean => v.key === S.Zero.key;
  const ok = !(z(a) && z(d)) && !(z(c) && z(e)) && b.pow(2).key === mul(4, a, c).key && !(z(a) && z(c));
  const fail = (): never => {
    throw new RangeError('Rational Point on the conic does not exist');
  };
  if (!ok) fail();
  if (!z(a)) {
    const dd = add(mul(4, a, e), mul(-2, b, d));
    const fd = add(mul(4, a, f), mul(-1, d.pow(2)));
    if (z(dd)) fail();
    const y = mul(-1, fd, dd.pow(-1));
    return [mul(-1, add(d, mul(b, y)), mul(2, a).pow(-1)), y];
  }
  // a = 0, so b = 0 and d is not zero: 4*c*d - 2*b*e is not zero
  const dd = add(mul(4, c, d), mul(-2, b, e));
  const fd = add(mul(4, c, f), mul(-1, e.pow(2)));
  const x = mul(-1, fd, dd.pow(-1));
  return [x, mul(-1, add(e, mul(b, x)), mul(2, c).pow(-1))];
}

const absBig = (n: bigint): bigint => (n < 0n ? -n : n);
// (the numbers are not zero)
const signBig = (n: bigint): bigint => (n < 0n ? -1n : 1n);

/** SymPy _regular_point_ellipse: a rational point of an ellipse or a hyperbola (Hillgarter). */
function regularPointEllipse(a: Expr, b: Expr, c: Expr, d: Expr, e: Expr, f: Expr): Expr[] {
  const fail = (): never => {
    throw new RangeError('Rational Point on the conic does not exist');
  };
  const z = (v: Expr): boolean => isZero(v);
  // (D = 4*a*c - b**2 is not zero: the conic is not a parabola)
  const D = add(mul(4, a, c), mul(-1, b.pow(2)));
  let K: Expr;
  let L: Expr;
  if (z(a) && z(c)) {
    K = S.NegOne;
    L = mul(4, add(mul(d, e), mul(-1, b, f)));
  } else if (!z(c)) {
    K = D;
    L = add(mul(4, c.pow(2), d.pow(2)), mul(-4, b, c, d, e), mul(4, a, c, e.pow(2)), mul(4, b.pow(2), c, f), mul(-16, a, c.pow(2), f));
  } else {
    K = D;
    L = add(mul(4, a.pow(2), e.pow(2)), mul(-4, b, a, d, e), mul(4, b.pow(2), a, f));
  }
  const kr = rationalOf(K);
  const lr = rationalOf(L);
  if (lr.isZero || (kr.isPositive && lr.isNegative)) fail();
  const [k1, k2, l1, l2] = [kr.p, kr.q, lr.p, lr.q];
  const g0 = gcd(k2, l2);
  const a1 = (l2 * k2) / g0;
  const b1 = (k1 * l2) / g0;
  const c1 = -(l1 * k2) / g0;
  let a2 = signBig(a1) * squareFree(absBig(a1));
  const r1 = sqrt(Rational.of(a1, a2));
  let b2 = signBig(b1) * squareFree(absBig(b1));
  const r2 = sqrt(Rational.of(b1, b2));
  let c2 = signBig(c1) * squareFree(absBig(c1));
  const r3 = sqrt(Rational.of(c1, c2));
  const g = gcd(gcd(a2, b2), c2);
  [a2, b2, c2] = [a2 / g, b2 / g, c2 / g];
  const g1 = gcd(a2, b2);
  [a2, b2, c2] = [a2 / g1, b2 / g1, c2 * g1];
  const g2 = gcd(a2, c2);
  [a2, b2, c2] = [a2 / g2, b2 * g2, c2 / g2];
  const g3 = gcd(b2, c2);
  [a2, b2, c2] = [a2 * g3, b2 / g3, c2 / g3];
  const [xs, ys, zs] = [new Sym('x'), new Sym('y'), new Sym('z')];
  const solutions = diophantine(add(mul(a2, xs.pow(2)), mul(b2, ys.pow(2)), mul(c2, zs.pow(2))));
  let found: Expr[] | undefined;
  for (const sol of solutions) {
    const solZ = at(sol, 2);
    if (isZero(solZ)) continue;
    const rep = new Map<string, [Sym, Expr]>();
    for (const s of freeSymbols(new TupleNode(sol))) rep.set(s.key, [s, sympify(3)]);
    // the parametric solution of a ternary quadratic form has two parameters p, q: the first integers (in the
    // order of S.Integers) at which z does not vanish
    const [p, q] = ordered([...freeSymbols(solZ)]).map((x) => cast(x, Sym, 'parameter'));
    const [pp, qq] = [defined(p, 'parameter'), defined(q, 'parameter')];
    for (let n = 0; ; n++) {
      const i = integerAt(n);
      const qv = firstNonRoot(subs(solZ, [[pp, i]]), qq);
      if (qv !== undefined) {
        rep.set(pp.key, [pp, sympify(i)]);
        rep.set(qq.key, [qq, sympify(qv)]);
        break;
      }
    }
    found = sol.map((s) => subs(s, [...rep.values()]));
    break;
  }
  if (found === undefined) fail();
  const [x0, y0, z0] = defined(found, 'solution');
  const xz = mul(defined(x0, 'x'), g3, r1.pow(-1));
  const yz = mul(defined(y0, 'y'), g2, r2.pow(-1));
  const zz = mul(defined(z0, 'z'), g1, r3.pow(-1));
  const x = mul(xz, zz.pow(-1));
  const y = mul(yz, zz.pow(-1));
  if (z(a) && z(c)) return [mul(add(x, y, mul(-2, e)), mul(2, b).pow(-1)), mul(add(x, mul(-1, y), mul(-2, d)), mul(2, b).pow(-1))];
  if (!z(c)) {
    const xr = mul(add(x, mul(-2, d, c), mul(b, e)), K.pow(-1));
    return [xr, mul(add(y, mul(-1, b, xr), mul(-1, e)), mul(2, c).pow(-1))];
  }
  const yr = mul(add(x, mul(-2, e, a), mul(b, d)), K.pow(-1));
  return [mul(add(y, mul(-1, b, yr), mul(-1, d)), mul(2, a).pow(-1)), yr];
}

/** SymPy ImplicitRegion(variables, equation); an Eq is taken as lhs - rhs. */
export const ImplicitRegion = /* @__PURE__ */ callableClass(
  ImplicitRegionNode,
  (variables: readonly ExprLike[] | TupleNode, equation: ExprLike): ImplicitRegionNode => new ImplicitRegionNode(variables, equation),
);
export type ImplicitRegion = ImplicitRegionNode;
