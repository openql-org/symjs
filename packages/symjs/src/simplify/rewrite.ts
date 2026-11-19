// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expr.rewrite(target): rewrite functions in terms of others
 * (SymPy Basic.rewrite and the `_eval_rewrite_as_*` methods).
 */

import type { Expr, ExprLike, RewriteRule } from '../core/nodes';
import { Add, Constant, Dummy, ExtensionExpr, Fn, Integral, Mul, Piecewise, Pow, Rational, Rel, S, UndefFn, impl, registerRewrite as addRewrite, rewriteRules } from '../core/nodes';
import { Eq, Ge, Gt, Lt, Ne, piecewise, rel } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { Mod } from '../functions/mod';
import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from '../core/assumptions';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { isFunctionOf } from '../core/match';
import { rebuild } from '../core/traverse';
import { abs, acos, arg, asin, atan, conjugate, cos, cosh, fn, im, log, re, sin, sinh, tan, tanh } from '../functions/elementary/elementary';
import { acot, acsc, asec, asinh, atanh, acosh, cot, coth, csc, sec } from '../functions/elementary/trigext';
import { Chi, Ci, Ei, Li, Shi, Si, binomial, factorial, gamma, harmonic, li, polygamma, sign, uppergamma, zeta } from '../functions/special/special';
import { factorial2Gamma, factorialRewrites, ff } from '../functions/combinatorial/factorials';
import { Sum } from '../core/concrete';
import { at, first, pair } from '../core/guard';

export type { RewriteRule };
export { rewriteRules };

/** @experimental May change in a minor release. */
export function registerRewrite(fnName: string, target: string, rule: RewriteRule): void {
  addRewrite(fnName, target, rule);
}

/** A rule on the first argument (a missing argument is an invariant violation). */
const unary =
  (f: (a: Expr, self: Expr) => Expr | undefined): RewriteRule =>
  (args, self) =>
    f(first(args), self);
/** A rule on the first two arguments. */
const binary =
  (f: (a: Expr, b: Expr, self: Expr) => Expr | undefined): RewriteRule =>
  (args, self) => {
    const [a, b] = pair(args);
    return f(a, b, self);
  };
const reg1 = (fnName: string, target: string, f: (a: Expr, self: Expr) => Expr | undefined): void => registerRewrite(fnName, target, unary(f));
const reg2 = (fnName: string, target: string, f: (a: Expr, b: Expr, self: Expr) => Expr | undefined): void =>
  registerRewrite(fnName, target, binary(f));

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const I = S.I;
const pi = S.Pi;
const half = Rational.of(1, 2);
const neg = (e: Expr): Expr => mul(-1, e);
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
/** An unevaluated function application (SymPy evaluate=False). */
const raw = (name: Fn['name'], ...args: Expr[]): Expr => new Fn(name, args);

/** SymPy class name of a node, used to look up rules and patterns. */
export function className(e: Expr): string {
  if (isExp(e)) return 'exp';
  if (e instanceof Constant && e.name === 'E') return 'Exp1';
  if (e instanceof Constant && (e.name === 'GoldenRatio' || e.name === 'TribonacciConstant')) return e.name;
  if (e instanceof Rel && e.op === 'Eq') return 'Equality';
  if (e instanceof Fn) return ({ abs: 'Abs', ff: 'FallingFactorial', rf: 'RisingFactorial' } as Record<string, string>)[e.name] ?? e.name;
  if (e instanceof UndefFn) return e.name;
  if (e instanceof BoolOp) return e.className;
  if (e instanceof ExtensionExpr) return e.name;
  if (e instanceof Add) return 'Add';
  if (e instanceof Mul) return 'Mul';
  if (e instanceof Pow) return 'Pow';
  return e.kind;
}

const fnArgs = (e: Expr): Expr[] => (isExp(e) && e instanceof Pow ? [e.exp] : [...e.args]);

/** Rebuild with new arguments (exp keeps its Function form). */
function withArgs(e: Expr, args: Expr[]): Expr {
  if (isExp(e)) return exp(first(args));
  return rebuild(e, args);
}

/**
 * Rewrite in terms of `target` (a SymPy function or class name such as
 * 'exp', 'cos', 'gamma', 'Piecewise'). With `pattern`, only nodes of those
 * functions are rewritten.
 */
export function rewrite(exprIn: ExprLike, target: string, opts: { pattern?: readonly string[]; deep?: boolean; hints?: Readonly<Record<string, Expr>> } = {}): Expr {
  const expr = sympify(exprIn);
  const t = target === 'abs' ? 'Abs' : target;
  let pattern = opts.pattern ?? [];
  if (pattern.length) {
    pattern = pattern.filter((p) => hasClass(expr, p));
    if (!pattern.length) return expr;
  }
  return rw(expr, pattern, t, opts.deep ?? true, opts.hints ?? {});
}

function hasClass(e: Expr, name: string): boolean {
  if (className(e) === name || isFunctionOf(e, name)) return true;
  return fnArgs(e).some((a) => hasClass(a, name));
}

function rw(e: Expr, pattern: readonly string[], target: string, deep: boolean, hints: Readonly<Record<string, Expr>>): Expr {
  const args = deep ? fnArgs(e).map((a) => rw(a, pattern, target, deep, hints)) : fnArgs(e);
  const cls = className(e);
  if (e instanceof ExtensionExpr && (!pattern.length || pattern.includes(e.name))) {
    const r = e.rewriteSelf(target, args);
    if (r !== undefined) return r;
  }
  if (!pattern.length || pattern.includes(cls)) {
    const rule = rewriteRules[cls]?.[target];
    if (rule) {
      const r = rule(args, e, hints);
      if (r !== undefined) return r;
    }
  }
  if (!args.length) return e;
  const orig = fnArgs(e);
  const changed = args.some((a, i) => a.key !== orig[i]?.key);
  return changed ? withArgs(e, args) : e;
}

impl.rewrite = (e, target, opts) => rewrite(e, target, opts);

// ---------------------------------------------------------------------------
// Trigonometric and hyperbolic functions
// ---------------------------------------------------------------------------

const TRIG_HYP = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
/** A trig/hyperbolic argument is itself rewritten in terms of exp first. */
const expArg = (a: Expr): Expr => (a instanceof Fn && TRIG_HYP.has(a.name) ? rewrite(raw(a.name, first(a.args)), 'exp') : a);
const logArg = (a: Expr): Expr | undefined => (a instanceof Fn && a.name === 'log' && a.args.length === 1 ? a.args[0] : undefined);

reg1('sin', 'exp', (a) => {
  const x = expArg(a);
  return div(add(exp(mul(x, I)), neg(exp(mul(neg(x), I)))), mul(2, I));
});
reg1('sin', 'cos', (a) => raw('cos', add(a, neg(div(pi, 2)))));
reg1('sin', 'tan', (a) => {
  const t = tan(mul(half, a));
  return div(mul(2, t), add(1, pow(t, 2)));
});
reg1('sin', 'Pow', (a) => {
  const x = logArg(a);
  return x === undefined ? undefined : add(div(mul(I, pow(x, neg(I))), 2), neg(div(mul(I, pow(x, I)), 2)));
});
reg1('sin', 'sincos', (a) => div(mul(sin(a), cos(a)), cos(a)));
reg1('sin', 'sinc', (a) => mul(a, fn('sinc', [a])));

reg1('cos', 'exp', (a) => {
  const x = expArg(a);
  return div(add(exp(mul(x, I)), exp(mul(neg(x), I))), 2);
});
reg1('cos', 'sin', (a) => raw('sin', add(a, div(pi, 2))));
reg1('cos', 'tan', (a) => {
  const t = pow(tan(mul(half, a)), 2);
  return div(add(1, neg(t)), add(1, t));
});
reg1('cos', 'Pow', (a) => {
  const x = logArg(a);
  return x === undefined ? undefined : add(div(pow(x, I), 2), div(pow(x, neg(I)), 2));
});
reg1('cos', 'sincos', (a) => div(mul(sin(a), cos(a)), sin(a)));

reg1('tan', 'exp', (a) => {
  const x = expArg(a);
  const ne = exp(mul(neg(x), I));
  const pe = exp(mul(x, I));
  return div(mul(I, add(ne, neg(pe))), add(ne, pe));
});
reg1('tan', 'cos', (a) => div(raw('cos', add(a, neg(div(pi, 2)))), cos(a)));
reg1('tan', 'sin', (a) => div(mul(2, pow(sin(a), 2)), sin(mul(2, a))));
reg1('tan', 'sincos', (a) => div(sin(a), cos(a)));
reg1('tan', 'Pow', (a) => {
  const x = logArg(a);
  if (x === undefined) return undefined;
  return div(mul(I, add(pow(x, neg(I)), neg(pow(x, I)))), add(pow(x, neg(I)), pow(x, I)));
});

reg1('exp', 'cos', (a) => add(cos(mul(I, a)), mul(I, cos(add(mul(I, a), div(pi, 2))))));
reg1('exp', 'sin', (a) => add(sin(add(mul(I, a), div(pi, 2))), neg(mul(I, sin(mul(I, a))))));
reg1('exp', 'tanh', (a) => {
  const t = tanh(div(a, 2));
  return div(add(1, t), add(1, neg(t)));
});
reg1('exp', 'Pow', (a) => {
  if (!(a instanceof Mul)) return undefined;
  const l = a.args.find((t) => t instanceof Fn && t.name === 'log' && t.args.length === 1);
  if (!l) return undefined;
  return pow(first(l.args), div(a, l));
});
/**
 * SymPy Pow._eval_rewrite_as_exp: b**e as exp(e*log(b)), with log(Abs(b)) + I*arg(b) for a base
 * without symbols. For a symbolic base, keep the exponential form when evaluation would restore the power.
 */
reg2('Pow', 'exp', (base, expo) => {
  const hasExp = (x: Expr): boolean => isExp(x) || x.args.some(hasExp);
  if (isZero(base) === true || hasExp(base) || hasExp(expo)) return pow(base, expo);
  if (base.freeSymbols().size === 0) return exp(mul(add(log(abs(base)), mul(I, arg(base))), expo));
  return new Pow(S.E, mul(log(base), expo));
});
reg1('exp', 'sqrt', (a) => {
  if (!(a instanceof Mul)) return undefined;
  const c = div(a, mul(pi, I));
  if (c.freeSymbols().size || c.has(pi) || c.has(I)) return undefined;
  const cs = cos(mul(pi, c));
  const sn = sin(mul(pi, c));
  if (isFunctionOf(cs, 'cos') || isFunctionOf(sn, 'sin')) return undefined;
  return add(cs, mul(I, sn));
});

reg2('Equality', 'Add', (left, right) => add(left, neg(right)));
registerRewrite('GoldenRatio', 'sqrt', () => mul(half, add(1, sqrt(5))));
registerRewrite('TribonacciConstant', 'sqrt', () => {
  const delta = mul(3, sqrt(33));
  const cubeRoot = Rational.of(1n, 3n);
  return mul(cubeRoot, add(1, pow(add(19, neg(delta)), cubeRoot), pow(add(19, delta), cubeRoot)));
});

// SymPy Exp1._eval_rewrite_as_cos and _eval_rewrite_as_sin
registerRewrite('Exp1', 'cos', () => add(cos(I), mul(I, cos(add(I, div(pi, 2))))));
registerRewrite('Exp1', 'sin', () => add(sin(add(I, div(pi, 2))), neg(mul(I, sin(I)))));

reg1('sinh', 'exp', (a) => div(add(exp(a), neg(exp(neg(a)))), 2));
reg1('sinh', 'cosh', (a) => neg(mul(I, cosh(add(a, div(mul(pi, I), 2))))));
reg1('sinh', 'sin', (a) => neg(mul(I, sin(mul(I, a)))));
reg1('sinh', 'tanh', (a) => {
  const t = tanh(mul(half, a));
  return div(mul(2, t), add(1, neg(pow(t, 2))));
});
reg1('cosh', 'exp', (a) => div(add(exp(a), exp(neg(a))), 2));
reg1('cosh', 'cos', (a) => raw('cos', mul(I, a)));
reg1('cosh', 'sinh', (a) => neg(mul(I, raw('sinh', add(a, div(mul(pi, I), 2))))));
reg1('cosh', 'tanh', (a) => {
  const t = pow(tanh(mul(half, a)), 2);
  return div(add(1, t), add(1, neg(t)));
});
reg1('tanh', 'exp', (a) => {
  const ne = exp(neg(a));
  const pe = exp(a);
  return div(add(pe, neg(ne)), add(pe, ne));
});
for (const target of ['exp', 'tractable']) {
  reg1('coth', target, (a) => div(add(exp(a), exp(neg(a))), add(exp(a), neg(exp(neg(a))))));
}
reg1('tanh', 'cosh', (a) => div(mul(I, raw('cosh', add(div(mul(pi, I), 2), neg(a)))), cosh(a)));
reg1('tanh', 'sinh', (a) => div(mul(I, sinh(a)), raw('sinh', add(div(mul(pi, I), 2), neg(a)))));
reg1('tanh', 'tan', (a) => neg(mul(I, raw('tan', mul(I, a)))));

// reciprocal functions (SymPy cot, sec, csc, coth, sech and csch rewrites)
/** 1/t for the rewrite t of the reciprocal function, when that rewrite changes it (SymPy _rewrite_reciprocal). */
const reciprocalRule = (name: Fn['name'], of: Fn['name'], target: string): void =>
  reg1(name, target, (a) => {
    const self = fn(of, [a]);
    const t = rewriteRules[of]?.[target]?.([a], self, {});
    return t === undefined || t.key === self.key ? undefined : div(1, t);
  });
const cosForm = (a: Expr, target: string): Expr => rewrite(cos(a), target);
const sinForm = (a: Expr, target: string): Expr => rewrite(sin(a), target);
reg1('sin', 'cot', (a) => {
  const c = cot(mul(half, a));
  return piecewise([0, and(Eq(im(a), 0), Eq(Mod(a, pi), 0))], [div(mul(2, c), add(1, pow(c, 2))), true]);
});
reg1('sin', 'csc', (a) => div(1, csc(a)));
reg1('sin', 'sec', (a) => div(1, raw('sec', add(a, neg(div(pi, 2))))));
reg1('cos', 'cot', (a) => {
  const c = pow(cot(mul(half, a)), 2);
  return piecewise([1, and(Eq(im(a), 0), Eq(Mod(a, mul(2, pi)), 0))], [div(add(c, -1), add(c, 1)), true]);
});
reg1('cos', 'sec', (a) => div(1, sec(a)));
reg1('cos', 'csc', (a) => div(1, rewrite(sec(a), 'csc')));
reg1('tan', 'cot', (a) => div(1, cot(a)));
reg1('tan', 'sec', (a) => div(sinForm(a, 'sec'), cosForm(a, 'sec')));
reg1('tan', 'csc', (a) => div(sinForm(a, 'csc'), cosForm(a, 'csc')));
reg1('cot', 'exp', (a) => {
  const x = expArg(a);
  const ne = exp(mul(neg(x), I));
  const pe = exp(mul(x, I));
  return div(mul(I, add(pe, ne)), add(pe, neg(ne)));
});
reg1('cot', 'Pow', (a) => {
  const x = logArg(a);
  return x === undefined ? undefined : div(mul(neg(I), add(pow(x, neg(I)), pow(x, I))), add(pow(x, neg(I)), neg(pow(x, I))));
});
reg1('cot', 'sin', (a) => div(sin(mul(2, a)), mul(2, pow(sin(a), 2))));
reg1('cot', 'cos', (a) => div(cos(a), raw('cos', add(a, neg(div(pi, 2))))));
for (const [name, inverse] of [['tan', false], ['cot', true]] as const) {
  reg1(name, 'sqrt', (a) => {
    const sine = sin(a);
    const cosine = cos(a);
    if ([sine, cosine].some((value) => value instanceof Fn && (value.name === 'sin' || value.name === 'cos'))) return undefined;
    return inverse ? div(cosine, sine) : div(sine, cosine);
  });
}
reg1('cot', 'sincos', (a) => div(cos(a), sin(a)));
reg1('cot', 'tan', (a) => div(1, tan(a)));
reg1('cot', 'sec', (a) => div(cosForm(a, 'sec'), sinForm(a, 'sec')));
reg1('cot', 'csc', (a) => div(cosForm(a, 'csc'), sinForm(a, 'csc')));
reg1('sec', 'cot', (a) => {
  const c = pow(cot(div(a, 2)), 2);
  return div(add(c, 1), add(c, -1));
});
reg1('sec', 'cos', (a) => div(1, cos(a)));
reg1('sec', 'sincos', (a) => div(sin(a), mul(cos(a), sin(a))));
reg1('sec', 'sin', (a) => div(1, cosForm(a, 'sin')));
reg1('sec', 'tan', (a) => div(1, cosForm(a, 'tan')));
reg1('sec', 'csc', (a) => raw('csc', add(div(pi, 2), neg(a))));
reg1('csc', 'sin', (a) => div(1, sin(a)));
reg1('csc', 'sincos', (a) => div(cos(a), mul(sin(a), cos(a))));
reg1('csc', 'cot', (a) => {
  const c = cot(div(a, 2));
  return div(add(1, pow(c, 2)), mul(2, c));
});
reg1('csc', 'cos', (a) => div(1, sinForm(a, 'cos')));
reg1('csc', 'sec', (a) => raw('sec', add(div(pi, 2), neg(a))));
reg1('csc', 'tan', (a) => div(1, sinForm(a, 'tan')));
for (const target of ['exp', 'Pow']) {
  reciprocalRule('sec', 'cos', target);
  reciprocalRule('csc', 'sin', target);
}
reg1('sinh', 'coth', (a) => {
  const c = coth(mul(half, a));
  return div(mul(2, c), add(pow(c, 2), -1));
});
reg1('cosh', 'coth', (a) => {
  const c = pow(coth(mul(half, a)), 2);
  return div(add(c, 1), add(c, -1));
});
reg1('tanh', 'coth', (a) => div(1, coth(a)));
reg1('coth', 'sinh', (a) => div(mul(neg(I), raw('sinh', add(div(mul(pi, I), 2), neg(a)))), sinh(a)));
reg1('coth', 'cosh', (a) => div(mul(neg(I), cosh(a)), raw('cosh', add(div(mul(pi, I), 2), neg(a)))));
reg1('coth', 'tanh', (a) => div(1, tanh(a)));
reg1('csch', 'cosh', (a) => div(I, raw('cosh', add(a, div(mul(I, pi), 2)))));
reg1('sech', 'sinh', (a) => div(I, raw('sinh', add(a, div(mul(I, pi), 2)))));
for (const target of ['exp', 'tanh', 'coth']) {
  reciprocalRule('sech', 'cosh', target);
  reciprocalRule('csch', 'sinh', target);
}
reg1('sinc', 'sin', (a) => piecewise([div(sin(a), a), Ne(a, 0)], [1, true]));

// inverse trigonometric
reg1('asin', 'acot', (x) => mul(2, acot(div(add(1, sqrt(add(1, neg(pow(x, 2))))), x))));
reg1('asin', 'asec', (x) => add(div(pi, 2), neg(asec(div(1, x)))));
reg1('asin', 'acsc', (x) => acsc(div(1, x)));
reg1('acos', 'acot', (x) => add(div(pi, 2), mul(-2, acot(div(add(1, sqrt(add(1, neg(pow(x, 2))))), x)))));
reg1('acos', 'asec', (x) => asec(div(1, x)));
reg1('acos', 'acsc', (x) => add(div(pi, 2), neg(acsc(div(1, x)))));
reg1('atan', 'acot', (x) => acot(div(1, x)));
reg1('atan', 'asec', (x) => mul(div(sqrt(pow(x, 2)), x), asec(sqrt(add(1, pow(x, 2))))));
reg1('atan', 'acsc', (x) => mul(div(sqrt(pow(x, 2)), x), add(div(pi, 2), neg(acsc(sqrt(add(1, pow(x, 2))))))));
/** x*sqrt(1/x**2), the sign of a real x. */
const signOf = (x: Expr): Expr => mul(x, sqrt(pow(x, -2)));
reg1('acot', 'asin', (x) => mul(signOf(x), add(div(pi, 2), neg(asin(div(sqrt(neg(pow(x, 2))), sqrt(add(neg(pow(x, 2)), -1))))))));
reg1('acot', 'acos', (x) => mul(signOf(x), acos(div(sqrt(neg(pow(x, 2))), sqrt(add(neg(pow(x, 2)), -1))))));
reg1('acot', 'atan', (x) => atan(div(1, x)));
reg1('acot', 'asec', (x) => mul(signOf(x), asec(sqrt(div(add(1, pow(x, 2)), pow(x, 2))))));
reg1('acot', 'acsc', (x) => mul(signOf(x), add(div(pi, 2), neg(acsc(sqrt(div(add(1, pow(x, 2)), pow(x, 2))))))));
reg1('asec', 'asin', (x) => add(div(pi, 2), neg(asin(div(1, x)))));
reg1('asec', 'acos', (x) => acos(div(1, x)));
reg1('asec', 'atan', (x) => {
  const s = div(sqrt(pow(x, 2)), x);
  return add(mul(div(pi, 2), add(1, neg(s))), mul(s, atan(sqrt(add(pow(x, 2), -1)))));
});
reg1('asec', 'acot', (x) => {
  const s = div(sqrt(pow(x, 2)), x);
  return add(mul(div(pi, 2), add(1, neg(s))), mul(s, acot(div(1, sqrt(add(pow(x, 2), -1))))));
});
reg1('asec', 'acsc', (x) => add(div(pi, 2), neg(acsc(x))));
reg1('acsc', 'asin', (x) => asin(div(1, x)));
reg1('acsc', 'acos', (x) => add(div(pi, 2), neg(acos(div(1, x)))));
reg1('acsc', 'atan', (x) => mul(div(sqrt(pow(x, 2)), x), add(div(pi, 2), neg(atan(sqrt(add(pow(x, 2), -1)))))));
reg1('acsc', 'acot', (x) => mul(div(sqrt(pow(x, 2)), x), add(div(pi, 2), neg(acot(div(1, sqrt(add(pow(x, 2), -1))))))));
reg1('acsc', 'asec', (x) => add(div(pi, 2), neg(asec(x))));

reg1('asin', 'log', (x) => mul(neg(I), log(add(mul(I, x), sqrt(add(1, neg(pow(x, 2))))))));
reg1('asin', 'acos', (x) => add(div(pi, 2), neg(acos(x))));
reg1('asin', 'atan', (x) => mul(2, atan(div(x, add(1, sqrt(add(1, neg(pow(x, 2)))))))));
reg1('acos', 'log', (x) => add(div(pi, 2), mul(I, log(add(mul(I, x), sqrt(add(1, neg(pow(x, 2)))))))));
reg1('acos', 'asin', (x) => add(div(pi, 2), neg(asin(x))));
reg1('acos', 'atan', (x) => add(atan(div(sqrt(add(1, neg(pow(x, 2)))), x)), mul(div(pi, 2), add(1, neg(mul(x, sqrt(pow(x, -2))))))));
reg1('atan', 'log', (x) => mul(div(I, 2), add(log(add(1, neg(mul(I, x)))), neg(log(add(1, mul(I, x)))))));
reg1('atan', 'asin', (x) => mul(div(sqrt(pow(x, 2)), x), add(div(pi, 2), neg(asin(div(1, sqrt(add(1, pow(x, 2)))))))));
reg1('atan', 'acos', (x) => mul(div(sqrt(pow(x, 2)), x), acos(div(1, sqrt(add(1, pow(x, 2)))))));
reg2('atan2', 'log', (y, x) => mul(neg(I), log(div(add(x, mul(I, y)), sqrt(add(pow(x, 2), pow(y, 2)))))));
reg1('acot', 'log', (x) => mul(div(I, 2), add(log(add(1, neg(div(I, x)))), neg(log(add(1, div(I, x)))))));
reg1('asec', 'log', (x) => add(div(pi, 2), mul(I, log(add(div(I, x), sqrt(add(1, neg(pow(x, -2)))))))));
reg1('acsc', 'log', (x) => mul(neg(I), log(add(div(I, x), sqrt(add(1, neg(pow(x, -2))))))));

// inverse hyperbolic (SymPy _eval_rewrite_as_log)
reg1('asinh', 'log', (x) => log(add(x, sqrt(add(pow(x, 2), 1)))));
reg1('acosh', 'log', (x) => log(add(x, mul(sqrt(add(x, 1)), sqrt(add(x, -1))))));
reg1('atanh', 'log', (x) => div(add(log(add(1, x)), neg(log(add(1, neg(x))))), 2));
reg1('acoth', 'log', (x) => div(add(log(add(1, div(1, x))), neg(log(add(1, neg(div(1, x)))))), 2));
reg1('asech', 'log', (x) => log(add(div(1, x), mul(sqrt(add(div(1, x), -1)), sqrt(add(div(1, x), 1))))));
reg1('acsch', 'log', (x) => log(add(div(1, x), sqrt(add(pow(x, -2), 1)))));
reg1('asinh', 'atanh', (x) => atanh(div(x, sqrt(add(1, pow(x, 2))))));
reg1('asinh', 'asin', (x) => mul(neg(I), raw('asin', mul(I, x))));
reg1('asinh', 'acos', (x) => add(mul(I, raw('acos', mul(I, x))), neg(div(mul(I, pi), 2))));
reg1('acosh', 'asin', (x) => mul(div(sqrt(add(x, -1)), sqrt(add(1, neg(x)))), add(div(pi, 2), neg(asin(x)))));
reg1('acosh', 'asinh', (x) => mul(div(sqrt(add(x, -1)), sqrt(add(1, neg(x)))), add(div(pi, 2), mul(I, raw('asinh', mul(I, x))))));
reg1('acosh', 'atanh', (x) => {
  const sxm1 = sqrt(add(x, -1));
  const sx2m1 = sqrt(add(pow(x, 2), -1));
  return add(mul(div(pi, 2), div(sxm1, sqrt(add(1, neg(x)))), add(1, neg(mul(x, sqrt(pow(x, -2)))))), mul(div(mul(sxm1, sqrt(add(x, 1))), sx2m1), atanh(div(sx2m1, x))));
});
reg1('atanh', 'asinh', (x) => {
  const f = sqrt(div(1, add(pow(x, 2), -1)));
  return add(div(mul(pi, x), mul(2, sqrt(neg(pow(x, 2))))), neg(mul(div(mul(sqrt(neg(x)), sqrt(add(1, neg(pow(x, 2))))), sqrt(x)), f, asinh(f))));
});
reg1('acoth', 'atanh', (x) => atanh(div(1, x)));
reg1('acoth', 'asinh', (x) =>
  add(
    mul(div(mul(pi, I), 2), add(mul(sqrt(div(add(x, -1), x)), sqrt(div(x, add(x, -1)))), neg(mul(sqrt(add(1, div(1, x))), sqrt(div(x, add(x, 1))))))),
    mul(signOf(x), asinh(sqrt(div(1, add(pow(x, 2), -1))))),
  ),
);
reg1('asech', 'acosh', (x) => acosh(div(1, x)));
reg1('asech', 'asinh', (x) => mul(div(sqrt(add(div(1, x), -1)), sqrt(add(1, neg(div(1, x))))), add(mul(I, raw('asinh', div(I, x))), div(pi, 2))));
reg1('asech', 'atanh', (x) =>
  add(
    mul(I, pi, add(1, neg(mul(sqrt(x), sqrt(div(1, x)))), mul(div(neg(I), 2), div(sqrt(neg(x)), sqrt(x))), mul(div(neg(I), 2), div(sqrt(pow(x, 2)), sqrt(neg(pow(x, 2))))))),
    mul(sqrt(div(1, add(x, 1))), sqrt(add(x, 1)), atanh(sqrt(add(1, neg(pow(x, 2)))))),
  ),
);
reg1('acsch', 'asinh', (x) => asinh(div(1, x)));
reg1('acsch', 'atanh', (x) => {
  const x2p1 = add(pow(x, 2), 1);
  return mul(div(sqrt(neg(pow(x, 2))), x), add(div(pi, 2), neg(mul(div(sqrt(neg(pow(x2p1, 2))), x2p1), atanh(sqrt(x2p1))))));
});
reg2('atan2', 'atan', (y, x) =>
  piecewise([mul(2, atan(div(y, add(x, sqrt(add(pow(x, 2), pow(y, 2))))))), Ne(y, 0)], [pi, Lt(re(x), 0)], [0, Ne(x, 0)], [S.NaN, true]),
);

// SymPy atan2._eval_rewrite_as_arg
reg2('atan2', 'arg', (y, x) => {
  const n = add(x, mul(I, y));
  if (isReal(x) === true && isReal(y) === true) return fn('arg', [n]);
  const d = add(pow(x, 2), pow(y, 2));
  return add(fn('arg', [div(n, sqrt(d))]), neg(mul(I, log(div(fn('abs', [n]), sqrt(fn('abs', [d])))))));
});
// complex functions
reg1('arg', 'atan2', (a) => fn('atan2', [im(a), re(a)]));
registerRewrite('Piecewise', 'ITE', (args, self) => {
  if (!(self instanceof Piecewise) || args.at(-1) !== S.true) return undefined;
  const boolean = (value: Expr): boolean => value === S.true || value === S.false || value.kind === 'Rel' || value.kind === 'BoolOp';
  let result = at(args, -2);
  if (!boolean(result)) return undefined;
  for (let i = args.length - 4; i >= 0; i -= 2) {
    const value = at(args, i);
    if (!boolean(value)) return undefined;
    result = new BoolOp('ITE', [at(args, i + 1), value, result]);
  }
  return result;
});
reg1('re', 'im', (a) => add(a, mul(-1, I, im(a))));
reg1('im', 're', (a) => mul(neg(I), add(a, neg(re(a)))));
/** SymPy _minmax_as_Piecewise: each argument with the conditions against the later ones. */
const minMaxPiecewise = (op: '>=' | '<='): RewriteRule => (args) =>
  piecewise(...args.map((a, i): [Expr, Expr] => [a, and(...args.slice(i + 1).map((b) => rel(op === '>=' ? 'Ge' : 'Le', a, b)))]));
registerRewrite('Max', 'Piecewise', minMaxPiecewise('>='));
registerRewrite('Min', 'Piecewise', minMaxPiecewise('<='));
reg1('Abs', 'sign', (a) => div(a, sign(a)));
reg1('Abs', 'conjugate', (a) => sqrt(mul(a, conjugate(a))));
reg1('Abs', 'Piecewise', (a) => {
  const r = isReal(a);
  if (r) return piecewise([a, Ge(a, 0)], [neg(a), true]);
  // an imaginary argument (SymPy Abs._eval_rewrite_as_Piecewise)
  if (isReal(mul(I, a)) === true) return piecewise([mul(I, a), Ge(mul(I, a), 0)], [mul(-1, I, a), true]);
  return undefined;
});
reg1('sign', 'Abs', (a) => piecewise([0, Eq(a, 0)], [div(a, abs(a)), true]));
reg1('sign', 'Piecewise', (a) => {
  if (!isReal(a)) return undefined;
  return piecewise([1, Gt(a, 0)], [-1, Lt(a, 0)], [0, true]);
});

// ---------------------------------------------------------------------------
// Combinatorial and gamma functions
// ---------------------------------------------------------------------------

reg1('factorial', 'gamma', (n) => gamma(add(n, 1)));
for (const [head, rules] of Object.entries(factorialRewrites)) {
  for (const [target, rule] of Object.entries(rules)) registerRewrite(head, target, rule);
}
reg1('factorial2', 'gamma', (n) => factorial2Gamma(n, Mod(n, 2)));
reg1('gamma', 'factorial', (z) => factorial(add(z, -1)));
reg2('beta', 'gamma', (a, b) => div(mul(gamma(a), gamma(b)), gamma(add(a, b))));
const incompleteBetaIntegral = (args: readonly Expr[]): Expr => {
  const [a, b] = pair(args), [x1, x2] = pair(args.slice(2));
  const t = new Dummy('t');
  return new Integral([mul(pow(t, add(a, -1)), pow(add(1, neg(t)), add(b, -1))), t, x1, x2]);
};
registerRewrite('betainc', 'Integral', incompleteBetaIntegral);
registerRewrite('betainc_regularized', 'Integral', (args) => {
  const [x1, x2] = pair(args.slice(2));
  return x1.equals(0) && x2.equals(1) ? S.One : div(incompleteBetaIntegral(args), incompleteBetaIntegral([...pair(args), S.Zero, S.One]));
});
reg1('loggamma', 'intractable', (z) => log(gamma(z)));
reg2('lowergamma', 'uppergamma', (s, z) => add(gamma(s), neg(uppergamma(s, z))));
reg2('uppergamma', 'lowergamma', (s, z) => add(gamma(s), neg(fn('lowergamma', [s, z]))));
const gammaExpint = (s: Expr, z: Expr): Expr => mul(pow(z, s), fn('expint', [add(1, neg(s)), z]));
reg2('uppergamma', 'expint', gammaExpint);
reg2('lowergamma', 'expint', (s, z) =>
  isIntegerQ(s) && isNonNegative(neg(s)) === true ? undefined : add(gamma(s), neg(gammaExpint(s, z))));
reg2('polygamma', 'zeta', (n, z) => isIntegerQ(n) && isPositive(n) ? mul(pow(-1, add(n, 1)), factorial(n), zeta(add(n, 1), z)) : undefined);
reg1('trigamma', 'zeta', (z) => zeta(2, z));
reg1('digamma', 'polygamma', (z) => polygamma(0, z));
reg1('trigamma', 'polygamma', (z) => polygamma(1, z));
reg1('digamma', 'harmonic', (z) => add(harmonic(add(z, -1)), neg(S.EulerGamma)));
reg1('trigamma', 'harmonic', (z) => add(zeta(2), neg(harmonic(add(z, -1), 2))));
registerRewrite('zeta', 'bernoulli', (args) => {
  const s = first(args), a = args[1] ?? S.One;
  if (a.key === S.One.key && isIntegerQ(mul(half, s)) === true && isNonNegative(s) === true) {
    return div(neg(mul(pow(mul(2, I, pi), s), fn('bernoulli', [s]))), mul(2, factorial(s)));
  }
  return div(fn('bernoulli', [add(1, neg(s)), a]), add(s, -1));
});
reg2('binomial', 'factorial', (n, k) => div(factorial(n), mul(factorial(k), factorial(add(n, neg(k))))));
reg2('binomial', 'gamma', (n, k) => div(gamma(add(n, 1)), mul(gamma(add(k, 1)), gamma(add(n, neg(k), 1)))));
reg2('binomial', 'FallingFactorial', (n, k) => (isIntegerQ(k) ? div(ff(n, k), factorial(k)) : undefined));
reg1('catalan', 'binomial', (n) => div(binomial(mul(2, n), n), add(n, 1)));
reg1('catalan', 'factorial', (n) => div(factorial(mul(2, n)), mul(factorial(add(n, 1)), factorial(n))));
reg1('catalan', 'gamma', (n) => div(mul(pow(4, n), gamma(add(n, half))), mul(gamma(half), gamma(add(n, 2)))));
registerRewrite('harmonic', 'Sum', (args) => {
  const n = first(args);
  const m = args[1] ?? S.One;
  const k = new Dummy('k', { integer: true });
  return Sum(pow(k, neg(m)), [k, 1, n]);
});
const harmonicPolygamma: RewriteRule = (args) => {
  const n = first(args);
  const mm = args[1] ?? S.One;
  if (!(isIntegerQ(mm) && isPositive(mm))) return undefined;
  return piecewise(
    [add(polygamma(0, add(n, 1)), S.EulerGamma), Eq(mm, 1)],
    [div(mul(pow(-1, mm), add(mul(pow(-1, mm), factorial(add(mm, -1)), zeta(mm)), neg(polygamma(add(mm, -1), add(n, 1))))), gamma(mm)), true],
  );
};
registerRewrite('harmonic', 'polygamma', harmonicPolygamma);
registerRewrite('harmonic', 'digamma', harmonicPolygamma);
registerRewrite('harmonic', 'trigamma', harmonicPolygamma);
registerRewrite('harmonic', 'tractable', (args, self) => {
  const pg = harmonicPolygamma(args, self);
  const m = args[1] ?? S.One;
  if (pg !== undefined) return rewrite(pg, 'tractable');
  if (isNonZero(add(m, -1)) === true) return rewrite(add(zeta(m), neg(zeta(m, add(first(args), 1)))), 'tractable');
  return undefined;
});
registerRewrite('harmonic', 'zeta', (args) => {
  const n = add(first(args), 1);
  const m = args[1] ?? S.One;
  return piecewise([add(polygamma(0, n), S.EulerGamma), Eq(m, 1)], [add(zeta(m), neg(zeta(m, n))), true]);
});
reg2('polygamma', 'harmonic', (n, z) => {
  if (!isIntegerQ(n)) return undefined;
  if (n instanceof Rational && n.isZero) return add(harmonic(add(z, -1)), neg(S.EulerGamma));
  return mul(pow(-1, add(n, 1)), factorial(n), add(zeta(add(n, 1)), neg(harmonic(add(z, -1), add(n, 1)))));
});

// exponential integrals
const lz = (z: Expr) => log(z);
reg1('li', 'Ei', (z) => Ei(log(z)));
reg1('li', 'Li', (z) => add(Li(z), li(2)));
const liShi: RewriteRule = unary((z) => add(Chi(lz(z)), neg(Shi(lz(z))), neg(mul(half, add(log(div(1, lz(z))), neg(log(lz(z))))))));
const liSi: RewriteRule = unary((z) =>
  add(Ci(mul(I, lz(z))), neg(mul(I, Si(mul(I, lz(z))))), neg(mul(half, add(log(div(1, lz(z))), neg(log(lz(z)))))), neg(log(mul(I, lz(z))))),
);
registerRewrite('li', 'Shi', liShi);
registerRewrite('li', 'Chi', liShi);
registerRewrite('li', 'Si', liSi);
registerRewrite('li', 'Ci', liSi);
reg1('Li', 'li', (z) => add(li(z), neg(li(2))));
const eiShi: RewriteRule = unary((z) => (isNegative(z) ? add(Shi(z), Chi(z), neg(mul(I, pi))) : add(Shi(z), Chi(z))));
for (const t of ['Shi', 'Chi', 'Si', 'Ci']) registerRewrite('Ei', t, eiShi);
reg1('Ei', 'li', (z) => (z instanceof Fn && z.name === 'log' && z.args.length === 1 ? li(first(z.args)) : li(exp(z))));

reg2('expint', 'uppergamma', (nu, z) => mul(pow(z, add(nu, -1)), uppergamma(add(1, neg(nu)), z)));

// exponential integrals in terms of expint (SymPy E1 = expint(1, .))
const E1 = (z: Expr) => fn('expint', [1, z]);
const plI = () => fn('polar_lift', [I]);
const plNegI = () => fn('polar_lift', [neg(I)]);
const ePi = () => fn('exp_polar', [mul(I, pi)]);
reg1('Ei', 'expint', (z) => add(neg(E1(mul(fn('polar_lift', [-1]), z))), neg(mul(I, pi))));
reg1('Ci', 'expint', (z) => neg(div(add(E1(mul(plI(), z)), E1(mul(plNegI(), z))), 2)));
reg1('Si', 'expint', (z) => add(div(pi, 2), div(div(add(E1(mul(plI(), z)), neg(E1(mul(plNegI(), z)))), 2), I)));
reg1('Shi', 'expint', (z) => add(div(add(E1(z), neg(E1(mul(ePi(), z)))), 2), neg(div(mul(I, pi), 2))));
reg1('Chi', 'expint', (z) => add(neg(div(mul(I, pi), 2)), neg(div(add(E1(z), E1(mul(ePi(), z))), 2))));

// floor / ceiling / frac (SymPy _eval_rewrite_as_*)
reg1('frac', 'floor', (x) => add(x, neg(raw('floor', x))));
reg1('frac', 'ceiling', (x) => add(x, raw('ceiling', neg(x))));
reg1('floor', 'ceiling', (x) => neg(raw('ceiling', neg(x))));
reg1('ceiling', 'floor', (x) => neg(raw('floor', neg(x))));
reg1('floor', 'frac', (x) => add(x, neg(raw('frac', x))));
reg1('ceiling', 'frac', (x) => add(x, raw('frac', neg(x))));

// integral representations (SymPy Si/Ei rewrite(Integral) and Si rewrite(sinc))
const siIntegral = unary((z) => {
  const t = new Dummy('t');
  return new Integral([raw('sinc', t), t, S.Zero, z]);
});
registerRewrite('Si', 'sinc', siIntegral);
registerRewrite('Si', 'Integral', siIntegral);
reg1('Ei', 'Integral', (z) => {
  const t = new Dummy('t');
  return new Integral([mul(exp(t), pow(t, -1)), t, S.NegativeInfinity, z]);
});
