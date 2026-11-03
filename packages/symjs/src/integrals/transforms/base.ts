// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Shared machinery of the integral transforms (SymPy
 * sympy.integrals.transforms.IntegralTransform, IntegralTransformError,
 * _simplify and the helpers used by every transform).
 */

import { Add, BoolAtom, Dummy, Expr, Sym, ExtensionExpr, Mul, Pow, Rel, S, UndefFn, Wild } from '../../core/nodes';
import { Max } from '../../functions/special';
import { diff } from '../../calculus/diff';
import { BoolOp } from '../../core/boolalg';
import { isNegative, isNonNegative, isNonZero, isPositive, isZero } from '../../core/assumptions';
import { NotImplementedError } from '../../core/errors';
import { at, cast, getOrThrow } from '../../core/guard';
import { add, mul, sub } from '../../core/ops';
import { asCoeffMul, isPolynomial } from '../../core/methods';
import { Poly } from '../../polys/sympoly';
import { match } from '../../core/match';
import { and } from '../../core/boolalg';
import { mapBottomUp, some, xreplace } from '../../core/traverse';
import { derivative } from '../../core/undef';
import { expandMul } from '../../simplify/expand';
import { simplify as simplifyExpr } from '../../simplify/simplify';

/**
 * A transform could not be computed (SymPy IntegralTransformError). Raised
 * with the hint `needeval: true` instead of returning an unevaluated
 * transform object.
 */
export class IntegralTransformError extends NotImplementedError {
  constructor(
    transform: string,
    /** The function whose transform failed (undefined when unknown). */
    readonly fn: Expr | undefined,
    msg: string,
  ) {
    super(`${transform} Transform could not be computed: ${msg}.`);
    this.name = 'IntegralTransformError';
  }
}

/** Hints of the transforms (SymPy keyword arguments of doit). */
export interface TransformHints {
  /** Simplify the result (default depends on the transform). */
  simplify?: boolean;
  /** Return only the transformed expression, without convergence conditions. */
  noconds?: boolean;
  /** Throw IntegralTransformError instead of returning an unevaluated transform. */
  needeval?: boolean;
}

/**
 * A computed transform with its extra data: [F, cond] (Fourier, sine,
 * cosine, Hankel), [F, plane, cond] (Laplace) or [F, [a, b], cond] (Mellin).
 */
export type TransformTuple = readonly [Expr, ...(Expr | readonly [Expr, Expr])[]];

/** The result of a transform: an expression or a tuple with conditions. */
export type TransformResult = Expr | TransformTuple;

/** True when a transform result carries conditions (a tuple rather than a bare expression). */
export const isTransformTuple = (r: TransformResult): r is TransformTuple => Array.isArray(r);

/** The terms of a sum. */
export const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
/** The factors of a product. */
export const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);

/** True when e is SymPy's false. */
export const isFalseExpr = (e: Expr): boolean => e.key === S.false.key;

/**
 * Decide a condition (relational or boolean combination) as SymPy's
 * automatic evaluation of relationals does: true or false when it is
 * settled by the numeric values or the assumptions, undefined otherwise.
 */
export function decide(c: Expr): boolean | undefined {
  if (c instanceof BoolAtom) return c.value;
  if (c instanceof BoolOp) {
    const vs = c.args.map(decide);
    if (c.op === 'And') return vs.includes(false) ? false : vs.every((v) => v === true) ? true : undefined;
    if (c.op === 'Or') return vs.includes(true) ? true : vs.every((v) => v === false) ? false : undefined;
    if (c.op === 'Not') return vs[0] === undefined ? undefined : !vs[0];
    return undefined;
  }
  if (!(c instanceof Rel)) return undefined;
  const d = sub(c.lhs, c.rhs);
  if (d.key === S.NaN.key || d.key === S.ComplexInfinity.key) return undefined;
  const neg = isNegative(d);
  const pos = isPositive(d);
  const zero = c.lhs.key === c.rhs.key ? true : isZero(d);
  switch (c.op) {
    case 'Eq':
      return zero === true ? true : isNonZero(d) === true ? false : undefined;
    case 'Ne':
      return zero === true ? false : isNonZero(d) === true ? true : undefined;
    case 'Lt':
      return neg === true ? true : isNonNegative(d) === true ? false : undefined;
    case 'Le':
      return neg === true || zero === true || isNonNegative(mul(-1, d)) === true ? true : pos === true ? false : undefined;
    case 'Gt':
      return pos === true ? true : neg === true || zero === true || isNonNegative(mul(-1, d)) === true ? false : undefined;
    case 'Ge':
      return pos === true || zero === true || isNonNegative(d) === true ? true : neg === true ? false : undefined;
  }
}

/** True when the condition is decided true. */
export const holds = (c: Expr): boolean => decide(c) === true;

/** A Wild symbol excluding the given expressions. */
export const wild = (name: string, ...exclude: Expr[]): Wild => new Wild(name, { exclude });

/** Match with the result keyed by Wild name (SymPy expr.match(pattern)). */
export function matchByName(e: Expr, pattern: Expr): Map<string, Expr> | undefined {
  const m = match(e, pattern);
  if (!m) return undefined;
  const out = new Map<string, Expr>();
  for (const [k, v] of m) out.set(k.name, v);
  return out;
}

/** Get a matched value (the pattern guarantees its presence). */
export function mget(m: ReadonlyMap<string, Expr>, name: string): Expr {
  return getOrThrow(m, name);
}

/** True when e is a polynomial in x (nodes depending on x other than powers are not). */
export function isPolyIn(e: Expr, x: Expr): boolean {
  if (!isPolynomial(e, [x])) return false;
  return !some(e, (n) => n.has(x) && !(n instanceof Add || n instanceof Mul || n instanceof Pow) && n.key !== x.key);
}

/** The coefficients of a polynomial in x, highest first, or undefined. */
export function polyCoeffs(e: Expr, x: Expr): Expr[] | undefined {
  if (!isPolyIn(e, x)) return undefined;
  // a polynomial in x with coefficients free of x: Poly.from accepts it
  return Poly.from(e, [x]).allCoeffs();
}

/** p + q for convergence abscissas, keeping -oo and oo (SymPy -oo + re(a) is -oo). */
export function planeAdd(p: Expr, q: Expr): Expr {
  if (p.key === S.NegativeInfinity.key || p.key === S.Infinity.key) return p;
  return add(p, q);
}

/** Max of convergence abscissas without the arguments that another one dominates. */
export function maxPlane(planes: readonly Expr[]): Expr {
  const uniq: Expr[] = [];
  for (const p of planes) if (!uniq.some((q) => q.key === p.key)) uniq.push(p);
  const kept = uniq.filter((p, i) => !uniq.some((q, j) => j !== i && (p.key === S.NegativeInfinity.key || decide(new Rel('Ge', q, p)) === true) && !(decide(new Rel('Ge', p, q)) === true && j > i)));
  // the first of the greatest planes is never dominated, so kept is not empty
  return Max(...kept);
}

/**
 * Differentiate n times when e contains unevaluated transforms of x: each
 * transform depending on x is differentiated as an unknown function
 * (Derivative(LaplaceTransform(f(t), t, s), (s, 2))).
 */
export function diffTransforms(e: Expr, x: Expr, n: number): Expr {
  const reps: [Expr, Expr][] = [];
  let i = 0;
  const masked = mapBottomUp(e, (node) => {
    if (node instanceof IntegralTransform && [...node.freeSymbols()].some((v) => v.key === x.key)) {
      const ph = new UndefFn(`_transform${i++}`, [x]);
      reps.push([ph, node]);
      return ph;
    }
    return node;
  });
  let r = masked;
  for (let j = 0; j < n; j++) r = diff(r, x);
  return xreplace(r, reps);
}

/** True when an undefined function applied to an expression containing x occurs in e. */
export const hasUndefOf = (e: Expr, x: Expr): boolean => some(e, (n) => n instanceof UndefFn && n.has(x));

/**
 * Base class of the unevaluated integral transforms (SymPy
 * IntegralTransform). The arguments are (function, function variable,
 * transform variable, extra arguments...); the function variable is bound.
 */
export abstract class IntegralTransform extends ExtensionExpr {
  /** The function to be transformed. */
  get function(): Expr {
    return at(this.args, 0);
  }
  /** The dependent variable of the function to be transformed. */
  get functionVariable(): Expr {
    return at(this.args, 1);
  }
  /** The independent transform variable. */
  get transformVariable(): Expr {
    return at(this.args, 2);
  }
  /** The descriptive name of the transform (SymPy _name, e.g. 'Laplace'). */
  abstract get transformName(): string;
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [1], scope: [0] };
  }
  /** The integral that defines the transform (SymPy as_integral). */
  abstract get asIntegral(): Expr;
  /** Evaluate the transform (SymPy doit). */
  abstract doit(hints?: TransformHints): TransformResult;
  override diffSelf(x: Expr): Expr | undefined {
    if (![...this.freeSymbols()].some((v) => v.key === x.key)) return S.Zero;
    return derivative(this, [[x, 1]]);
  }
  override doitSelf(): Expr {
    const r = this.doit();
    return isTransformTuple(r) ? r[0] : r;
  }
  /** The LaTeX symbol of the transform (SymPy _print_IntegralTransform), or undefined for the generic form. */
  protected get latexName(): string | undefined {
    return undefined;
  }
  override printLatex(print: (e: Expr) => string): string {
    const name = this.latexName;
    // SymPy's _print_Function form for the transforms without a symbol of their own
    if (name === undefined) return `\\operatorname{${this.name}}{\\left(${this.args.map(print).join(',')} \\right)}`;
    return `${name}_{${print(this.functionVariable)}}\\left[${print(this.function)}\\right]\\left(${print(this.transformVariable)}\\right)`;
  }
  override rewriteSelf(target: string): Expr | undefined {
    return target === 'Integral' ? this.asIntegral : undefined;
  }
}

/**
 * An integral transform evaluated by SymPy's generic IntegralTransform.doit:
 * the transform is computed directly, then term by term, and otherwise
 * constant factors are pulled out of an unevaluated transform.
 */
export abstract class GenericIntegralTransform extends IntegralTransform {
  /** Compute the transform; throws IntegralTransformError on failure (SymPy _compute_transform). */
  protected abstract computeTransform(f: Expr, x: Sym, s: Sym, hints: Required<Pick<TransformHints, 'simplify'>> & TransformHints): TransformResult;
  /** A transform of the same class with another function. */
  protected abstract withFunction(f: Expr): IntegralTransform;
  /** Combine the extra data of the terms (SymPy _collapse_extra). */
  protected collapseExtra(extra: readonly (readonly (Expr | readonly [Expr, Expr])[])[]): readonly (Expr | readonly [Expr, Expr])[] {
    const cond = and(...extra.map((x) => cast(at(x, 0), Expr, 'condition')));
    if (isFalseExpr(cond)) throw new IntegralTransformError(this.transformName, undefined, '');
    return [cond];
  }
  /** The default of the noconds hint. */
  protected get defaultNoconds(): boolean {
    return false;
  }

  doit(hints: TransformHints = {}): TransformResult {
    const needeval = hints.needeval ?? false;
    const simplify = hints.simplify ?? true;
    const noconds = hints.noconds ?? this.defaultNoconds;
    const f = this.function;
    const x = this.functionVariable;
    // a bound variable that is not a symbol: nothing to integrate over
    if (!(x instanceof Sym)) return this;
    let T: TransformResult | undefined;
    if (!hasUndefOf(f, x)) {
      try {
        const s = asSymbolVariable(this.transformVariable);
        T = mapTransformResult(this.computeTransform(f, x, s.sym, { ...hints, simplify, noconds }), s.back);
      } catch (e) {
        if (!(e instanceof IntegralTransformError)) throw e;
      }
    }
    if (T !== undefined) return T;
    const fn = f instanceof Add ? f : expandMul(f);
    if (fn instanceof Add) {
      const res = fn.args.map((term) => this.withFunctionDoit(term, { ...hints, simplify, needeval, noconds }));
      const extra: (readonly (Expr | readonly [Expr, Expr])[])[] = [];
      const ress: Expr[] = [];
      for (const r of res) {
        // a tuple always carries its conditions after the transform
        if (isTransformTuple(r)) {
          ress.push(r[0]);
          extra.push(r.slice(1));
        } else ress.push(r);
      }
      const sum = simplify ? simplifyExpr(add(...ress)) : add(...ress);
      if (extra.length === 0) return sum;
      try {
        const collapsed = this.collapseExtra(extra);
        const tup: TransformTuple = [sum, ...collapsed];
        return tup;
      } catch (e) {
        if (!(e instanceof IntegralTransformError)) throw e;
      }
    }
    if (needeval) throw new IntegralTransformError(this.transformName, f, 'needeval');
    const [coeff, rest] = asCoeffMul(fn, [x]);
    return mul(coeff, this.withFunction(mul(...rest)));
  }

  private withFunctionDoit(term: Expr, hints: TransformHints): TransformResult {
    return this.withFunction(term).doit(hints);
  }
}

/** The (function, function variable, transform variable) arguments of a transform rebuilt from its args. */
export function transformArgs(args: readonly Expr[]): [Expr, Expr, Expr] {
  return [at(args, 0), at(args, 1), at(args, 2)];
}

/**
 * A transform variable as a symbol. SymPy accepts any expression in that
 * position (substituting s = 2 gives LaplaceTransform(f, t, 2)); such an
 * expression is replaced by a Dummy for the computation, and `back` puts it
 * back into the results.
 */
export function asSymbolVariable(e: Expr): { sym: Sym; back: (r: Expr) => Expr } {
  if (e instanceof Sym) return { sym: e, back: (r) => r };
  const d = new Dummy('s');
  return { sym: d, back: (r) => xreplace(r, [[d, e]]) };
}

/** Apply f to every expression of a transform result. */
export function mapTransformResult(r: TransformResult, f: (e: Expr) => Expr): TransformResult {
  if (r instanceof Expr) return f(r);
  const [head, ...rest] = r;
  return [f(head), ...rest.map((x): Expr | readonly [Expr, Expr] => (x instanceof Expr ? f(x) : [f(x[0]), f(x[1])]))];
}
