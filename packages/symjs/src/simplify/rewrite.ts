// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expr.rewrite(target): rewrite functions in terms of others
 * (SymPy Basic.rewrite and the `_eval_rewrite_as_*` methods).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Dummy, ExtensionExpr, Fn, Integral, Mul, Pow, Rational, S, UndefFn, impl } from '../core/nodes';
import { Eq, Ge, Gt, Lt, Ne, piecewise } from '../core/logic';
import { isIntegerQ, isNegative, isPositive, isReal } from '../core/assumptions';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { isFunctionOf } from '../core/match';
import { rebuild } from '../core/traverse';
import { abs, acos, asin, atan, conjugate, cos, cosh, fn, log, re, sin, sinh, tan, tanh } from '../functions/elementary';
import { Chi, Ci, Ei, Li, Shi, Si, binomial, factorial, ff, gamma, harmonic, li, polygamma, sign, uppergamma, zeta } from '../functions/special';
import { Sum } from '../core/concrete';
import { first, pair } from '../core/guard';

/** A rewrite rule: the (already rewritten) arguments and the original node. */
export type RewriteRule = (args: Expr[], self: Expr) => Expr | undefined;

/** rewriteRules[functionName][target] (SymPy class names, e.g. 'Abs', 'exp'). */
export const rewriteRules: Record<string, Record<string, RewriteRule>> = {};

/** @experimental May change in a minor release. */
export function registerRewrite(fnName: string, target: string, rule: RewriteRule): void {
  (rewriteRules[fnName] ??= {})[target] = rule;
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
  if (e instanceof Fn) return ({ abs: 'Abs', ff: 'FallingFactorial', rf: 'RisingFactorial' } as Record<string, string>)[e.name] ?? e.name;
  if (e instanceof UndefFn) return e.name;
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
export function rewrite(exprIn: ExprLike, target: string, opts: { pattern?: readonly string[]; deep?: boolean } = {}): Expr {
  const expr = sympify(exprIn);
  const t = target === 'abs' ? 'Abs' : target;
  let pattern = opts.pattern ?? [];
  if (pattern.length) {
    pattern = pattern.filter((p) => hasClass(expr, p));
    if (!pattern.length) return expr;
  }
  return rw(expr, pattern, t, opts.deep ?? true);
}

function hasClass(e: Expr, name: string): boolean {
  if (className(e) === name || isFunctionOf(e, name)) return true;
  return fnArgs(e).some((a) => hasClass(a, name));
}

function rw(e: Expr, pattern: readonly string[], target: string, deep: boolean): Expr {
  const args = deep ? fnArgs(e).map((a) => rw(a, pattern, target, deep)) : fnArgs(e);
  const cls = className(e);
  if (e instanceof ExtensionExpr && (!pattern.length || pattern.includes(e.name))) {
    const r = e.rewriteSelf(target, args);
    if (r !== undefined) return r;
  }
  if (!pattern.length || pattern.includes(cls)) {
    const rule = rewriteRules[cls]?.[target];
    if (rule) {
      const r = rule(args, e);
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
reg1('exp', 'sqrt', (a) => {
  if (!(a instanceof Mul)) return undefined;
  const c = div(a, mul(pi, I));
  if (c.freeSymbols().size || c.has(pi) || c.has(I)) return undefined;
  const cs = cos(mul(pi, c));
  const sn = sin(mul(pi, c));
  if (isFunctionOf(cs, 'cos') || isFunctionOf(sn, 'sin')) return undefined;
  return add(cs, mul(I, sn));
});

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
reg1('tanh', 'cosh', (a) => div(mul(I, raw('cosh', add(div(mul(pi, I), 2), neg(a)))), cosh(a)));
reg1('tanh', 'sinh', (a) => div(mul(I, sinh(a)), raw('sinh', add(div(mul(pi, I), 2), neg(a)))));
reg1('tanh', 'tan', (a) => neg(mul(I, raw('tan', mul(I, a)))));

// inverse trigonometric
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
reg2('atan2', 'atan', (y, x) =>
  piecewise([mul(2, atan(div(y, add(x, sqrt(add(pow(x, 2), pow(y, 2))))))), Ne(y, 0)], [pi, Lt(re(x), 0)], [0, Ne(x, 0)], [S.NaN, true]),
);

// complex functions
reg1('Abs', 'sign', (a) => div(a, sign(a)));
reg1('Abs', 'conjugate', (a) => sqrt(mul(a, conjugate(a))));
reg1('Abs', 'Piecewise', (a) => {
  const r = isReal(a);
  if (r) return piecewise([a, Ge(a, 0)], [neg(a), true]);
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
reg1('gamma', 'factorial', (z) => factorial(add(z, -1)));
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
    [div(mul(pow(-1, mm), add(polygamma(add(mm, -1), 1), neg(polygamma(add(mm, -1), add(n, 1))))), gamma(mm)), true],
  );
};
registerRewrite('harmonic', 'polygamma', harmonicPolygamma);
registerRewrite('harmonic', 'digamma', harmonicPolygamma);
registerRewrite('harmonic', 'trigamma', harmonicPolygamma);
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
