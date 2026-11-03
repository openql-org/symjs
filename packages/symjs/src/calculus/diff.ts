// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Symbolic differentiation.
 */

import { NotImplementedError } from '../core/errors';
import { at, first, last } from '../core/guard';
import { isReal } from '../core/assumptions';
import { piecewise } from '../core/logic';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, ExtensionExpr, Constant, Derivative, Dummy, Fn, Integral, Mul, Order, Piecewise, Pow, S, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { derivative } from '../core/undef';
import { SubsNode } from '../core/subsnode';
import { Concrete } from '../core/concrete';
import { Indexed } from '../core/indexed';
import { add, mul, pow, sympify } from '../core/ops';
import { rebuild, xreplace } from '../core/traverse';
import { abs, conjugate, cos, cosh, fn, im as fnIm, log, re as fnRe, sin, sinh, tan, tanh } from '../functions/elementary';

/**
 * Partial derivatives of multi-argument functions: fnPartials[name](args, i)
 * is d f(args) / d args[i]. special.ts registers entries.
 */
export const fnPartials: Partial<Record<Fn['name'], (args: readonly Expr[], i: number) => Expr>> = {};

/** Late-bound pieces of higher layers: the reduction of an Order to its leading term (set by series/series.ts). */
export const diffHooks: { order: (e: Expr, variables: readonly Sym[], point: Expr) => Expr } = { order: orderUnreduced };

/** The Order of e without the reduction to its leading term (when series/series.ts is not loaded). */
export function orderUnreduced(e: Expr, variables: readonly Sym[], point: Expr): Expr {
  return new Order(variables.length ? [e, ...variables, point] : [e]);
}

/** Derivative of f(u) with respect to u, for each known function. */
const fnDerivative: Partial<Record<Fn['name'], (u: Expr) => Expr>> = {
  sin: (u) => cos(u),
  cos: (u) => mul(-1, sin(u)),
  tan: (u) => add(1, pow(tan(u), 2)),
  asin: (u) => pow(add(1, mul(-1, pow(u, 2))), S.NegHalf),
  acos: (u) => mul(-1, pow(add(1, mul(-1, pow(u, 2))), S.NegHalf)),
  atan: (u) => pow(add(1, pow(u, 2)), -1),
  sinh: (u) => cosh(u),
  cosh: (u) => sinh(u),
  tanh: (u) => add(1, mul(-1, pow(tanh(u), 2))),
  log: (u) => pow(u, -1),
};

/**
 * A matrix element X[i, j] as the variable (told apart by name: the matrix
 * module builds on this one). An expression depends on it through X, as
 * Trace(X) does, so it is not replaced by a dummy.
 */
const isMatrixElement = (x: Expr): x is ExtensionExpr => x instanceof ExtensionExpr && x.name === 'MatrixElement';

/** e may depend on x: it contains x, or the matrix of a matrix element x. */
const dependsOn = (e: Expr, x: Expr): boolean => e.has(x) || (isMatrixElement(x) && e.has(first(x.args)));

function d(e: Expr, x: Expr): Expr {
  if (e.key === x.key) return S.One;
  if (isNum(e) || e instanceof Constant || e instanceof Sym) return S.Zero;
  if (!dependsOn(e, x)) return S.Zero;

  if (e instanceof Add) return add(...e.args.map((a) => d(a, x)));
  if (e instanceof ExtensionExpr) {
    const r = e.diffSelf(x, d);
    if (r !== undefined) return r;
    // SymPy keeps Derivative(Determinant(X), X[0, 0]) unevaluated
    if (isMatrixElement(x)) return derivative(e, [[x, 1]]);
    throw new NotImplementedError(`diff: ${e.name} does not define a derivative`);
  }

  if (e instanceof Mul) {
    const terms: Expr[] = [];
    for (const [i, ai] of e.args.entries()) {
      const di = d(ai, x);
      if (di.key === S.Zero.key) continue;
      terms.push(mul(...e.args.map((a, j) => (j === i ? di : a))));
    }
    return add(...terms);
  }

  if (e instanceof Pow) {
    const [b, n] = e.args;
    const db = d(b, x);
    const dn = d(n, x);
    // d(b^n) = b^n * (n' log b + n b'/b)
    if (dn.key === S.Zero.key) return mul(n, pow(b, add(n, -1)), db);
    if (b instanceof Constant && b.name === 'E') return mul(e, dn);
    return mul(e, add(mul(dn, log(b)), mul(n, db, pow(b, -1))));
  }

  if (e instanceof Fn) {
    const partial = fnPartials[e.name];
    if (partial) {
      const terms: Expr[] = [];
      e.args.forEach((a, i) => {
        const da = d(a, x);
        if (da.key !== S.Zero.key) terms.push(mul(partial(e.args, i), da));
      });
      return add(...terms);
    }
    const u = first(e.args);
    if (e.name === 'conjugate' || e.name === 're' || e.name === 'im') {
      // linear, but not holomorphic: the derivative is taken inside only for a real variable (SymPy keeps Derivative(conjugate(x), x))
      if (isReal(x) !== true) return derivative(e, [[x, 1]]);
      const du = d(u, x);
      return e.name === 'conjugate' ? conjugate(du) : e.name === 're' ? fnRe(du) : fnIm(du);
    }
    const du = d(u, x);
    if (e.name === 'abs') {
      if (isReal(u)) return mul(u, pow(abs(u), -1), du);
      throw new NotImplementedError('diff: derivative of abs() of a non-real argument is not supported');
    }
    // arg(u)' = 0 for a real u
    if (e.name === 'arg' && isReal(u)) return S.Zero;
    const f = fnDerivative[e.name];
    // no derivative known (floor, ceiling, sign of a complex argument): SymPy keeps Derivative(floor(x), x);
    // floor and ceiling of another argument follow the chain rule (x*Subs(Derivative(floor(xi), xi), xi, x*y))
    if (!f) {
      if ((e.name === 'floor' || e.name === 'ceiling') && u.key !== x.key) {
        const xi = new Dummy('xi_1');
        return mul(new SubsNode([derivative(fn(e.name, [xi]), [[xi, 1]]), xi, u]), du);
      }
      return derivative(e, [[x, 1]]);
    }
    return mul(f(u), du);
  }
  if (e instanceof UndefFn) {
    // chain rule over the arguments; only direct dependence is represented
    const terms: Expr[] = [];
    for (const [i, a] of e.args.entries()) {
      if (!a.has(x)) continue;
      if (a.key === x.key) terms.push(derivative(e, [[x, 1]], true));
      // f(g(x)): Derivative(f(g(x)), g(x))*Derivative(g(x), x) like SymPy
      else if (a instanceof UndefFn) terms.push(mul(derivative(e, [[a, 1]]), d(a, x)));
      else {
        // f(x + 1): Subs(Derivative(f(xi), xi), xi, x + 1)*d(x + 1)/dx like SymPy
        const xi = new Dummy(`xi_${i + 1}`);
        const at = rebuild(e, e.args.map((b, j) => (j === i ? xi : b)));
        terms.push(mul(new SubsNode([derivative(at, [[xi, 1]]), xi, a]), d(a, x)));
      }
    }
    return add(...terms);
  }
  if (e instanceof Order) {
    // SymPy Order._eval_derivative: O(diff(expr, x), *variables, point), reduced to its leading term
    const de = d(e.expr, x);
    if (de.key === S.Zero.key) return S.Zero;
    const vars = e.args.slice(1, -1).filter((v): v is Sym => v instanceof Sym);
    const point = e.args.length > 1 ? last(e.args) : S.Zero;
    return diffHooks.order(de, vars, point);
  }
  if (e instanceof Derivative) {
    if (e.expr instanceof UndefFn && e.expr.args.some((a) => a.key === x.key)) return derivative(e, [[x, 1]], true);
    // otherwise x enters through the expression: evaluate the inner derivative first, like SymPy
    // (diff(Derivative(f(x*y), y), x) = x*y*Subs(Derivative(f(xi), (xi, 2)), xi, x*y) + Subs(Derivative(f(xi), xi), xi, x*y))
    const inner = e.variableCount.reduce((acc, [v, k]) => diff(acc, v, k), e.expr);
    // a derivative that stays unevaluated (Derivative(floor(x*y), y)) gets x appended
    return inner.key === e.key ? derivative(e, [[x, 1]]) : d(inner, x);
  }
  if (e instanceof Concrete && e.kind2 === 'Sum') {
    // SymPy Sum._eval_derivative: the sum of the derivatives when the limits do not depend on x
    const limits = e.limits;
    if (limits.every(([k, a, b]) => k.key !== x.key && !dependsOn(a, x) && !dependsOn(b, x))) return new Concrete('Sum', [d(e.function, x), ...e.args.slice(1)]);
    throw new NotImplementedError('diff: derivative of a sum whose limits depend on the variable is not supported');
  }
  if (e instanceof Piecewise) return piecewise(...e.pairs.map(([v, c]) => [d(v, x), c] as const));
  if (e instanceof Integral) return diffIntegral(e, x);
  // SymPy Product._eval_derivative gives a Sum of products of the factors
  if (e instanceof Concrete) throw new NotImplementedError('diff: derivative of a product is not supported');
  // relations, limits and other objects without a derivative rule stay unevaluated (SymPy Derivative(x < 1, x))
  return derivative(e, [[x, 1]]);
}

/**
 * Derivative of an integral (SymPy Integral._eval_derivative): the integrand
 * for its own variable, and the Leibniz rule f(b)*b' - f(a)*a' +
 * Integral(df/dx) otherwise. A bound variable is not free.
 */
function diffIntegral(e: Integral, x: Expr): Expr {
  const f = e.integrand;
  const v = e.variable;
  const [, , a, b] = e.args;
  if (![...impl.freeSymbols(e)].some((s) => s.key === x.key)) return S.Zero;
  if (a === undefined && v.key === x.key) return f;
  const terms: Expr[] = [];
  // an inner indefinite integral in v at p is the antiderivative there: Integral(g, (v, p))
  const at = (p: Expr) => (f instanceof Integral && f.args.length === 2 && f.variable.key === v.key ? new Integral([f.integrand, v, p]) : impl.subs(f, [[v, p]]));
  // (v, b): the antiderivative at b; (v, a, b): limits a and b
  const upper = b ?? a;
  const lower = b === undefined ? undefined : a;
  if (upper !== undefined) {
    const du = d(upper, x);
    if (du.key !== S.Zero.key) terms.push(mul(at(upper), du));
  }
  if (lower !== undefined) {
    const dl = d(lower, x);
    if (dl.key !== S.Zero.key) terms.push(mul(-1, at(lower), dl));
  }
  if (v.key !== x.key) {
    const df = d(f, x);
    if (df.key !== S.Zero.key) terms.push(new Integral([df, ...e.args.slice(1)]));
  }
  return add(...terms);
}

/** The derivative with respect to a subexpression t, which is treated as a symbol. */
function diffWrtTerm(e: Expr, t: Expr, n: number): Expr {
  const xi = new Dummy('xi');
  return xreplace(diff(xreplace(e, [[t, xi]]), xi, n), [[xi, t]]);
}

/** The distinct indexed objects with the given base in e. */
function indexedTerms(e: Expr, base: Expr, out = new Map<string, Indexed>()): Map<string, Indexed> {
  if (e instanceof Indexed && e.base.key === base.key) out.set(e.key, e);
  for (const a of e.args) indexedTerms(a, base, out);
  return out;
}

/**
 * SymPy Indexed._eval_derivative: d A[i]/d A[j] = KroneckerDelta(i, j), so the
 * derivative with respect to A[j] adds up d e/d A[k] * KroneckerDelta(k, j) over
 * the A[k] in e.
 */
function diffIndexed(e: Expr, x: Indexed): Expr {
  const terms: Expr[] = [];
  for (const t of indexedTerms(e, x.base).values()) {
    if (t.indices.length !== x.indices.length) throw new RangeError(`diff: different number of indices: d(${t.toString()})/d(${x.toString()})`);
    const delta = mul(...t.indices.map((i, k) => fn('KroneckerDelta', [i, at(x.indices, k)])));
    terms.push(mul(diffWrtTerm(e, t, 1), delta));
  }
  return add(...terms);
}

/** n-th derivative of e with respect to x. */
export function diff(ex: ExprLike, x: Expr, n = 1): Expr {
  if (!Number.isInteger(n) || n < 0) throw new RangeError('diff: order must be a non-negative integer');
  let e = sympify(ex);
  if (x instanceof Indexed) {
    for (let i = 0; i < n; i++) e = diffIndexed(e, x);
    return e;
  }
  // SymPy: a variable that is not a scalar (is_scalar = False) keeps the derivative unevaluated
  if (x instanceof ExtensionExpr && !x.isScalar && n > 0 && e.has(x)) return derivative(e, [[x, n]]);
  // differentiate with respect to an expression such as f(x): treat it as a symbol
  if (!(x instanceof Sym) && !isMatrixElement(x)) return diffWrtTerm(e, x, n);
  for (let i = 0; i < n; i++) e = d(e, x);
  return e;
}

impl.diff = diff;
