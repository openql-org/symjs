// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/delta_functions.py and
// sympy/functions/special/singularity_functions.py), BSD 3-Clause License,
// Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The Heaviside step function, the Dirac delta distribution and the
 * singularity functions (SymPy sympy.functions.special.delta_functions and
 * singularity_functions). They live in one module because each rewrites into
 * the others.
 */

import type { DefinedFunction, FunctionDefinition } from '../../core/defun';
import type { Expr, ExprLike, RelOp } from '../../core/nodes';
import { DefinedFunctionCall, defineFunction } from '../../core/defun';
import { Add, Dummy, Mul, Rational, S, Sym, impl } from '../../core/nodes';
import { isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from '../../core/assumptions';
import { add, couldExtractMinusSign, mul, neg, pow, splitCoeff, sub } from '../../core/ops';
import { at, first, getOrThrow } from '../../core/guard';
import { piecewise, rel } from '../../core/logic';
import { freeSymbols, subs } from '../../core/traverse';
import { derivative } from '../../core/undef';
import { SubsNode } from '../../core/subsnode';
import { abs, fn, im } from '../../functions/elementary/elementary';
import { sign } from '../../functions/special/special';
import { registerRewrite } from '../../simplify/rewrite';
import { diff, fnPartials, unavailablePartials } from '../../calculus/diff';
import { polyCoefficients, rootsDict } from '../../polys/poly';

const isNaN = (e: Expr): boolean => e.key === S.NaN.key;

const FLIP: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };

/**
 * The relation `lhs op 0` in the canonical form Piecewise gives its conditions
 * (SymPy Relational.canonical followed by _canonical_coeff): x - 5 < 0 -> x < 5,
 * Eq(x**2 - 5, 0) -> Eq(x**2, 5), 3 - x < 0 -> x > 3.
 */
export function canonicalCondition(op: RelOp, lhs: Expr): Expr {
  const terms = lhs instanceof Add ? lhs.args : [lhs];
  const b = add(...terms.filter((t) => t instanceof Rational));
  const l = sub(lhs, b);
  if (l.key === S.Zero.key) return rel(op, lhs, 0);
  if (l instanceof Add) {
    // several terms: the sign SymPy's minus-sign extraction gives, the constant on the right
    const minus = couldExtractMinusSign(lhs);
    return rel(minus ? FLIP[op] : op, minus ? neg(l) : l, minus ? b : neg(b));
  }
  // one term c*t: t op -b/c, reversed for c < 0
  const [m, rest] = splitCoeff(l);
  return rel(isNegative(m) === true ? FLIP[op] : op, rest, mul(neg(b), pow(m, -1)));
}

/** The coefficients [c1, c0] of an argument c1*x + c0 linear in x, else undefined. */
function linear(arg: Expr, x: Expr): [Expr, Expr] | undefined {
  const c = polyCoefficients(arg, x);
  if (!c || Math.max(-1, ...c.keys()) !== 1) return undefined;
  return [getOrThrow(c, 1), c.get(0) ?? S.Zero];
}

/** The only free symbol of e (SymPy free_symbols.pop()); a TypeError like SymPy's otherwise. */
function onlySymbol(e: Expr, what: string): Sym {
  const free = [...freeSymbols(e)].filter((s) => s instanceof Sym);
  if (free.length !== 1) throw new TypeError(`rewrite(SingularityFunction) does not support ${what} arguments with more than one variable`);
  return first(free);
}

/**
 * SymPy Function.fdiff without a closed form: Derivative(f(x), x) for a symbol that no
 * other argument contains, else Subs(Derivative(f(xi), xi), xi, a).
 */
function unevaluatedPartial(f: DefinedFunction, args: readonly Expr[], i: number): Expr {
  const a = at(args, i);
  if (a instanceof Sym && !args.some((v, j) => j !== i && v.has(a))) return derivative(f(...args), [[a, 1]]);
  const xi = new Dummy(`xi_${i + 1}`);
  return new SubsNode([derivative(f(...args.map((b, j) => (j === i ? xi : b))), [[xi, 1]]), xi, a]);
}

/** Real distributions are unchanged by conjugation and adjunction. */
class RealDistributionCall extends DefinedFunctionCall {
  override conjugateSelf(): Expr {
    return this;
  }
  override adjointSelf(): Expr {
    return this;
  }
  /** Arguments excluding the default value at the step's discontinuity. */
  get pargs(): readonly Expr[] {
    return this.name === 'Heaviside' && at(this.args, 1).key === S.Half.key ? this.args.slice(0, 1) : this.args;
  }
  override printStr(print: (e: Expr) => string): string {
    return `${this.name}(${this.pargs.map(print).join(', ')})`;
  }
}

const heavisideDefinition: FunctionDefinition = {
  nargs: [1, 2],
  eval: (x: Expr, h0?: Expr) => {
    const H0 = h0 ?? S.Half;
    if (isNaN(x)) return S.NaN;
    if (isNegative(x) === true) return S.Zero;
    if (isPositive(x) === true) return S.One;
    if (isZero(x) === true) return H0;
    if (isNonZero(im(x)) === true) throw new RangeError('Heaviside is defined only for real arguments');
    return new RealDistributionCall('Heaviside', [x, H0], heavisideDefinition);
  },
  fdiff: (args, i) => {
    if (i !== 0) throw new RangeError('Heaviside has a derivative only in its first argument');
    return DiracDelta(at(args, 0));
  },
  rewrite: {
    Piecewise: (arg: Expr, H0: Expr) => {
      if (H0.key === S.Zero.key) return piecewise([0, canonicalCondition('Le', arg)], [1, true]);
      if (H0.key === S.One.key) return piecewise([0, canonicalCondition('Lt', arg)], [1, true]);
      return piecewise([0, canonicalCondition('Lt', arg)], [H0, canonicalCondition('Eq', arg)], [1, true]);
    },
    sign: (arg: Expr, H0: Expr) => {
      if (isReal(arg) !== true) return undefined;
      const half = mul(add(sign(arg), 1), S.Half);
      const atZero = Heaviside(0, H0);
      const pw1 = piecewise([half, rel('Ne', arg, 0)], [atZero, true]);
      return piecewise([half, rel('Eq', atZero, S.Half)], [pw1, true]);
    },
    SingularityFunction: (arg: Expr) => {
      // Heaviside(c*(x - a)) is SingularityFunction(x, a, 0) only for c > 0; SymPy also
      // rewrites c < 0 (Heaviside(2 - x) -> SingularityFunction(x, 2, 0)), which is wrong
      const x = onlySymbol(arg, 'Heaviside');
      const l = linear(arg, x);
      if (!l || isPositive(l[0]) !== true) return undefined;
      return SingularityFunction(x, neg(mul(l[1], pow(l[0], -1))), 0);
    },
  },
};
const heavisideDef: DefinedFunction = defineFunction('Heaviside', heavisideDefinition);

const diracDefinition: FunctionDefinition = {
  nargs: [1, 2],
  eval: (x: Expr, k?: Expr) => {
    const kk = k ?? S.Zero;
    if (!(kk instanceof Rational) || !kk.isInteger || kk.isNegative) {
      throw new RangeError(`the second argument of DiracDelta must be a non-negative integer, ${String(kk)} given instead`);
    }
    if (isNaN(x)) return S.NaN;
    if (isNonZero(im(x)) === true) throw new RangeError('DiracDelta is defined only for real arguments');
    if (isNonZero(x) === true) return S.Zero;
    if (x instanceof Mul && isNegative(first(x.args)) === true) {
      const odd = kk.p % 2n === 1n;
      const positive = neg(x);
      const d = kk.isZero ? diracDef(positive) : diracDef(positive, kk);
      return odd ? neg(d) : d;
    }
    // DiracDelta(x, 0) is stored as DiracDelta(x)
    if (k !== undefined && kk.isZero) return diracDef(x);
    return new RealDistributionCall('DiracDelta', k === undefined ? [x] : [x, kk], diracDefinition);
  },
  fdiff: (args) => {
    const k = args[1] ?? S.Zero;
    return diracDef(at(args, 0), mul(1, k).add(1));
  },
  rewrite: {
    Piecewise: (arg: Expr, k?: Expr) => (k === undefined ? piecewise([diracDef(0), canonicalCondition('Eq', arg)], [0, true]) : undefined),
    SingularityFunction: (arg: Expr, k0?: Expr) => {
      const k = k0 ?? S.Zero;
      const n = sub(-1, k);
      // SingularityFunction is not defined below the exponent -4
      if (isNegative(add(n, 4)) === true) return undefined;
      if (arg.key === S.Zero.key) return SingularityFunction(0, 0, n);
      const x = onlySymbol(arg, 'DiracDelta');
      // DiracDelta(c*(x - a), k) = c**(-k)/|c| * DiracDelta(x - a, k); SymPy drops the factor
      // and also rewrites nonlinear arguments by one root only, both of which are wrong
      const l = linear(arg, x);
      if (!l) return undefined;
      const [c1, c0] = l;
      return mul(SingularityFunction(x, neg(mul(c0, pow(c1, -1))), n), pow(c1, neg(k)), pow(abs(c1), -1));
    },
  },
  expand: {
    diracdelta: (self: Expr, hints) => expandDiracDelta(self, hints['wrt']),
  },
};
const diracDef: DefinedFunction = defineFunction('DiracDelta', diracDefinition);

/**
 * SymPy DiracDelta._eval_expand_diracdelta: DiracDelta(g(x)) as the sum of
 * DiracDelta(x - r)/|g'(r)| over the simple real roots r of a polynomial g.
 */
function expandDiracDelta(self: Expr, wrt0: unknown): Expr {
  let wrt = wrt0;
  if (wrt === undefined) {
    const free = [...freeSymbols(self)].filter((s) => s instanceof Sym);
    if (free.length !== 1) throw new TypeError("when there is more than 1 free symbol or variable in the expression, the 'wrt' keyword is required as a hint to expand when using the DiracDelta hint");
    wrt = first(free);
  }
  if (!(wrt instanceof Sym)) throw new TypeError('the wrt hint of the DiracDelta expansion must be a symbol');
  const arg = at(self.args, 0);
  if (!arg.has(wrt) || self.args.length > 1) return self;
  let rs;
  try {
    rs = rootsDict(arg, wrt);
  } catch {
    // not a polynomial (PolynomialError) or roots not in radicals (NotImplementedError): kept,
    // where SymPy gives 0 for roots it cannot find (DiracDelta(x**5 - x - 1)), which is wrong
    return self;
  }
  const darg = abs(diff(arg, wrt));
  const terms: Expr[] = [];
  for (const [r, m] of rs) {
    // non-real roots are not handled; a multiple root is a zero of the derivative
    if (isReal(r) === false || m !== 1) return self;
    terms.push(mul(DiracDelta(sub(wrt, r)), pow(subs(darg, [[wrt, r]]), -1)));
  }
  return add(...terms);
}

const NEGATIVE_ORDERS = new Set(['-1', '-2', '-3', '-4']);
const isNegativeOrder = (n: Expr): n is Rational => n instanceof Rational && NEGATIVE_ORDERS.has(String(n));

unavailablePartials.SingularityFunction = [2, 3];

const singularityDef: DefinedFunction = defineFunction('SingularityFunction', {
  nargs: 3,
  eval: (x: Expr, a: Expr, n: Expr) => {
    const shift = sub(x, a);
    if (isNaN(shift) || isNaN(n)) return S.NaN;
    if (isReal(shift) === false) throw new RangeError('Singularity Functions are defined only for Real Numbers.');
    if (isReal(n) === false) throw new RangeError('Singularity Functions are not defined for imaginary exponents.');
    if (isNegative(add(n, 4)) === true) throw new RangeError('Singularity Functions are not defined for exponents less than -4.');
    if (isNegative(shift) === true) return S.Zero;
    if (isNonNegative(n) === true) {
      if (isZero(shift) === true) return pow(S.Zero, n);
      if (isNonNegative(shift) === true) return pow(shift, n);
    }
    if (isNegativeOrder(n)) {
      if (isPositive(shift) === true) return S.Zero;
      if (isZero(shift) === true) return S.Infinity;
    }
    return undefined;
  },
  fdiff: (args, i) => {
    const [x, a, n] = [at(args, 0), at(args, 1), at(args, 2)];
    if (i === 0) {
      if (n instanceof Rational && ['0', '-1', '-2', '-3'].includes(String(n))) return singularityDef(x, a, sub(n, 1));
      if (isPositive(n) === true) return mul(n, singularityDef(x, a, sub(n, 1)));
    }
    // SymPy raises for the offset, the exponent and an exponent of unknown sign
    return unevaluatedPartial(singularityDef, args, i);
  },
  rewrite: {
    Piecewise: (x: Expr, a: Expr, n: Expr) => {
      const shift = sub(x, a);
      if (isNegativeOrder(n)) return piecewise([S.Infinity, canonicalCondition('Eq', shift)], [0, true]);
      if (isNonNegative(n) === true) return piecewise([pow(shift, n), canonicalCondition('Ge', shift)], [0, true]);
      return undefined;
    },
    Heaviside: (x: Expr, a: Expr, n: Expr) => singularityAsHeaviside(x, a, n),
    DiracDelta: (x: Expr, a: Expr, n: Expr) => singularityAsHeaviside(x, a, n),
    HeavisideDiracDelta: (x: Expr, a: Expr, n: Expr) => singularityAsHeaviside(x, a, n),
  },
});

/** SymPy SingularityFunction._eval_rewrite_as_Heaviside (also as DiracDelta). */
function singularityAsHeaviside(x: Expr, a: Expr, n: Expr): Expr | undefined {
  if (isNegativeOrder(n)) {
    const v = [...freeSymbols(x)].filter((s) => s instanceof Sym)[0];
    // SymPy raises KeyError for a variable without free symbols
    if (v === undefined) return undefined;
    const shift = sub(x, a), order = -Number(n.p);
    if (order % 2 === 0 && couldExtractMinusSign(shift)) return neg(diff(Heaviside(neg(shift)), v, order));
    return diff(Heaviside(shift), v, order);
  }
  if (isNonNegative(n) === true) return mul(pow(sub(x, a), n), Heaviside(sub(x, a), 1));
  return undefined;
}

/**
 * The Heaviside step function: 0 for negative, 1 for
 * positive arguments and `H0` (default 1/2) at 0.
 *
 * @param x - The argument whose sign determines the step value.
 * @param H0 - The value of the step function at zero.
 * @returns The step value or symbolic step function.
 * @see SymPy `sympy.functions.special.delta_functions.Heaviside`
 * @example
 * ```ts
 * import { Heaviside } from '@symjs/symjs';
 * Heaviside(9); // => 1
 * ```
 */
export function Heaviside(x: ExprLike, H0?: ExprLike): Expr {
  return H0 === undefined ? heavisideDef(x) : heavisideDef(x, H0);
}

/**
 * The Dirac delta distribution and its k-th derivative.
 *
 * @param x - The argument of the delta distribution.
 * @param k - The nonnegative derivative order.
 * @returns The delta distribution or its indicated derivative.
 * @see SymPy `sympy.functions.special.delta_functions.DiracDelta`
 * @example
 * ```ts
 * import { DiracDelta } from '@symjs/symjs';
 * DiracDelta(1); // => 0
 * ```
 */
export function DiracDelta(x: ExprLike, k?: ExprLike): Expr {
  return k === undefined ? diracDef(x) : diracDef(x, k);
}

/**
 * The singularity function <x - a>^n: (x - a)**n
 * for x >= a and 0 for x < a when n >= 0; for n = -1, -2, -3, -4 the derivatives
 * of the Dirac delta (oo at x = a, 0 elsewhere).
 *
 * @param variable - The independent variable of the singularity function.
 * @param offset - The point at which the singularity occurs.
 * @param exponent - The exponent of the power.
 * @returns The value or symbolic singularity function.
 * @see SymPy `sympy.functions.special.singularity_functions.SingularityFunction`
 * @example
 * ```ts
 * import { SingularityFunction } from '@symjs/symjs';
 * SingularityFunction(4, 1, 5); // => 243
 * ```
 */
export function SingularityFunction(variable: ExprLike, offset: ExprLike, exponent: ExprLike): Expr {
  return singularityDef(variable, offset, exponent);
}

/**
 * True when e is an application of Heaviside.
 *
 * @param e - The expression to evaluate.
 * @returns Whether the expression is an application of this function.
 */
export const isHeaviside = (e: Expr): boolean => heavisideDef.isApplied(e);

impl.heaviside = (x) => Heaviside(x);

/**
 * True when e is an application of DiracDelta.
 *
 * @param e - The expression to evaluate.
 * @returns Whether the expression is an application of this function.
 */
export const isDiracDelta = (e: Expr): boolean => diracDef.isApplied(e);

/**
 * True when e is an application of SingularityFunction.
 *
 * @param e - The expression to evaluate.
 * @returns Whether the expression is an application of this function.
 */
export const isSingularityFunction = (e: Expr): boolean => singularityDef.isApplied(e);

/**
 * Tests whether the argument of a Dirac delta is linear in the selected variable.
 *
 * @param delta - The delta distribution to inspect.
 * @param x - The variable in which to test linearity.
 * @returns Whether the delta argument is linear in the selected variable.
 * @see SymPy `sympy.functions.special.delta_functions.DiracDelta.is_simple`
 * @example
 * ```ts
 * import { DiracDelta, ex, isSimple, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * isSimple(DiracDelta(ex`x*y`), x); // => True
 * ```
 */
export function isSimple(delta: Expr, x: Expr): boolean {
  if (!isDiracDelta(delta)) throw new TypeError(`isSimple: ${String(delta)} is not a DiracDelta`);
  return linear(at(delta.args, 0), x) !== undefined;
}

/** The underlying defined functions (for code that needs the function objects). */
export const HeavisideFunction: DefinedFunction = heavisideDef;
/** The underlying defined function of DiracDelta. */
export const DiracDeltaFunction: DefinedFunction = diracDef;

// SymPy sign._eval_rewrite_as_Heaviside: a real argument
registerRewrite('sign', 'Heaviside', (args) => (isReal(first(args)) === true ? sub(mul(2, Heaviside(first(args))), 1) : undefined));
// SymPy Max and Min _eval_rewrite_as_Heaviside: each argument times the steps on which it is the extreme one
registerRewrite('Max', 'Heaviside', (args) => add(...args.map((j) => mul(j, ...args.filter((i) => i.key !== j.key).map((i) => Heaviside(sub(j, i)))))));
registerRewrite('Min', 'Heaviside', (args) => add(...args.map((j) => mul(j, ...args.filter((i) => i.key !== j.key).map((i) => Heaviside(sub(i, j)))))));
// SymPy sign.fdiff: 2*DiracDelta(x) for a real argument, 2*DiracDelta(-I*x) for an imaginary one
fnPartials.sign = (args) => {
  const a = first(args);
  if (isReal(a) === true) return mul(2, DiracDelta(a));
  const ia = mul(-1, S.I, a);
  return isReal(ia) === true ? mul(2, DiracDelta(ia)) : undefined;
};
// SymPy MinMaxBase.fdiff: the step where the argument exceeds (Max) or falls below (Min) the extreme of the others
for (const name of ['Max', 'Min'] as const) {
  fnPartials[name] = (args, i) => {
    const rest = args.filter((_, j) => j !== i);
    const other = rest.length === 1 ? at(rest, 0) : fn(name, rest);
    const ai = at(args, i);
    return Heaviside(name === 'Max' ? sub(ai, other) : sub(other, ai));
  };
}
