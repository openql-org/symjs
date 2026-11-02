// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Shared machinery of the integral transforms (SymPy
 * sympy.integrals.transforms.IntegralTransform, IntegralTransformError,
 * _simplify and the helpers used by every transform).
 */

import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { Add, BoolAtom, Derivative, ExtensionExpr, Integral, Mul, Pow, Rational, Rel, S, UndefFn, Wild } from '../../core/nodes';
import { Max } from '../../functions/special';
import { diff } from '../../calculus/diff';
import { BoolOp } from '../../core/boolalg';
import { isNegative, isNonNegative, isNonZero, isPositive, isZero } from '../../core/assumptions';
import { NotImplementedError } from '../../core/errors';
import { add, mul, sub, sympify } from '../../core/ops';
import { asCoeffMul, isPolynomial } from '../../core/methods';
import { Poly } from '../../polys/sympoly';
import { match } from '../../core/match';
import { and } from '../../core/boolalg';
import { mapBottomUp, some, xreplace } from '../../core/traverse';
import { derivative } from '../../core/undef';
import { expandMul } from '../../simplify/expand';
import { simplify as simplifyExpr } from '../../simplify/simplify';
import { powdenest } from '../../simplify/powsimp';

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

/** The terms of a sum. */
export const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
/** The factors of a product. */
export const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);

/** True when e is SymPy's true. */
export const isTrueExpr = (e: Expr): boolean => e.key === S.true.key;
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
  if (d.freeSymbols().size === 0 && d.isNumber) {
    let v: { re: number; im: number };
    try {
      v = d.toComplex();
    } catch {
      return undefined;
    }
    if (Number.isNaN(v.re) || Number.isNaN(v.im)) return undefined;
    if (c.op === 'Eq') return v.re === 0 && v.im === 0 ? true : Math.abs(v.re) + Math.abs(v.im) > 1e-12 ? false : undefined;
    if (c.op === 'Ne') return v.re === 0 && v.im === 0 ? false : Math.abs(v.re) + Math.abs(v.im) > 1e-12 ? true : undefined;
    if (Math.abs(v.im) > 1e-12) return undefined;
    const x = v.re;
    switch (c.op) {
      case 'Lt':
        return x < 0;
      case 'Le':
        return x <= 0;
      case 'Gt':
        return x > 0;
      case 'Ge':
        return x >= 0;
    }
  }
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
  const v = m.get(name);
  if (v === undefined) throw new RangeError(`missing match for ${name}`);
  return v;
}

/** True when e is a polynomial in x (nodes depending on x other than powers are not). */
export function isPolyIn(e: Expr, x: Expr): boolean {
  if (!isPolynomial(e, [x])) return false;
  return !some(e, (n) => n.has(x) && !(n instanceof Add || n instanceof Mul || n instanceof Pow) && n.key !== x.key);
}

/** The coefficients of a polynomial in x, highest first, or undefined. */
export function polyCoeffs(e: Expr, x: Expr): Expr[] | undefined {
  if (!isPolyIn(e, x)) return undefined;
  try {
    return Poly.from(e, [x]).allCoeffs();
  } catch {
    return undefined;
  }
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
  return Max(...(kept.length ? kept : uniq));
}

/**
 * Differentiate n times when e contains unevaluated transforms of x: each
 * transform depending on x is differentiated as an unknown function
 * (Derivative(LaplaceTransform(f(t), t, s), (s, 2))).
 */
export function diffTransforms(e: Expr, x: Expr, n: Expr | number): Expr {
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
  let r: Expr;
  if (typeof n === 'number' || n instanceof Rational) {
    const k = typeof n === 'number' ? n : Number(n.p);
    r = masked;
    for (let j = 0; j < k; j++) r = diff(r, x);
  } else {
    // symbolic order: Derivative(e, (x, n))
    return new Derivative([e, x, n]);
  }
  return xreplace(r, reps);
}

/** True when an undefined function applied to an expression containing x occurs in e. */
export const hasUndefOf = (e: Expr, x: Expr): boolean => some(e, (n) => n instanceof UndefFn && n.has(x));

/** True when an unevaluated integral occurs in e. */
export const hasIntegral = (e: Expr): boolean => some(e, (n) => n instanceof Integral);

/** SymPy transforms._simplify: simplify(powdenest(expr)) when doit is true. */
export function simplifyTransform(expr: Expr, doit: boolean): Expr {
  if (!doit) return expr;
  return simplifyExpr(powdenest(expr));
}

/**
 * Base class of the unevaluated integral transforms (SymPy
 * IntegralTransform). The arguments are (function, function variable,
 * transform variable, extra arguments...); the function variable is bound.
 */
export abstract class IntegralTransform extends ExtensionExpr {
  /** The function to be transformed. */
  get function(): Expr {
    return this.args[0]!;
  }
  /** The dependent variable of the function to be transformed. */
  get functionVariable(): Sym {
    return this.args[1] as Sym;
  }
  /** The independent transform variable. */
  get transformVariable(): Sym {
    return this.args[2] as Sym;
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
    return Array.isArray(r) ? (r as TransformTuple)[0] : (r as Expr);
  }
  /** The LaTeX symbol of the transform (SymPy _print_IntegralTransform), or undefined for the generic form. */
  protected get latexName(): string | undefined {
    return undefined;
  }
  override printLatex(print: (e: Expr) => string): string {
    const name = this.latexName;
    if (name === undefined) return super.printLatex(print);
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
    const cond = and(...extra.map((x) => x[0] as Expr));
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
    let T: TransformResult | undefined;
    if (!hasUndefOf(f, x)) {
      try {
        T = this.computeTransform(f, x, this.transformVariable, { ...hints, simplify, noconds });
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
        if (Array.isArray(r)) {
          const tup = r as TransformTuple;
          ress.push(tup[0]);
          if (tup.length >= 2) extra.push(tup.slice(1));
        } else ress.push(r as Expr);
      }
      const sum = simplify ? simplifyExpr(add(...ress)) : add(...ress);
      if (extra.length === 0) return sum;
      try {
        const collapsed = this.collapseExtra(extra);
        return [sum, ...collapsed] as TransformTuple;
      } catch (e) {
        if (!(e instanceof IntegralTransformError)) throw e;
      }
    }
    if (needeval) throw new IntegralTransformError(this.transformName, f, 'needeval');
    const [coeff, rest] = asCoeffMul(fn, [x]);
    return mul(coeff, this.withFunction(mul(...rest)));
  }

  private withFunctionDoit(term: Expr, hints: TransformHints): TransformResult {
    const t = this.withFunction(term);
    return t instanceof IntegralTransform ? t.doit(hints) : t;
  }
}

/** sympify for transform arguments. */
export const toExpr = (e: ExprLike): Expr => sympify(e);
