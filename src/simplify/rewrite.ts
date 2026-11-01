// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expr.rewrite(target): rewrite functions in terms of others
 * (SymPy Basic.rewrite and the `_eval_rewrite_as_*` methods).
 */

import { Add, Constant, Dummy, Expr, ExprLike, Fn, Mul, Pow, Rational, S, UndefFn, impl } from '../core/nodes';
import { Eq, Ge, Gt, Lt, Ne, piecewise } from '../core/logic';
import { isIntegerQ, isNegative, isPositive, isReal } from '../core/assumptions';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { isFunctionOf } from '../core/match';
import { rebuild } from '../core/traverse';
import { abs, acos, asin, atan, conjugate, cos, cosh, log, re, sin, sinh, tan, tanh } from '../functions/elementary';
import { Chi, Ci, Ei, Li, Shi, Si, binomial, factorial, ff, gamma, harmonic, li, polygamma, sign, uppergamma, zeta } from '../functions/special';
import { Sum } from '../concrete/summations';

/** A rewrite rule: the (already rewritten) arguments and the original node. */
export type RewriteRule = (args: Expr[], self: Expr) => Expr | undefined;

/** rewriteRules[functionName][target] (SymPy class names, e.g. 'Abs', 'exp'). */
export const rewriteRules: Record<string, Record<string, RewriteRule>> = {};

export function registerRewrite(fnName: string, target: string, rule: RewriteRule): void {
  (rewriteRules[fnName] ??= {})[target] = rule;
}

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
  if (e instanceof Add) return 'Add';
  if (e instanceof Mul) return 'Mul';
  if (e instanceof Pow) return 'Pow';
  return e.kind;
}

const fnArgs = (e: Expr): Expr[] => (isExp(e) ? [(e as Pow).exp] : [...e.args]);

/** Rebuild with new arguments (exp keeps its Function form). */
function withArgs(e: Expr, args: Expr[]): Expr {
  if (isExp(e)) return exp(args[0]!);
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
  if (!pattern.length || pattern.includes(cls)) {
    const rule = rewriteRules[cls]?.[target];
    if (rule) {
      const r = rule(args, e);
      if (r !== undefined) return r;
    }
  }
  if (!args.length) return e;
  const changed = args.some((a, i) => a.key !== fnArgs(e)[i]!.key);
  return changed ? withArgs(e, args) : e;
}

impl.rewrite = (e, target, opts) => rewrite(e, target, opts);

// ---------------------------------------------------------------------------
// Trigonometric and hyperbolic functions
// ---------------------------------------------------------------------------

const TRIG_HYP = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
/** A trig/hyperbolic argument is itself rewritten in terms of exp first. */
const expArg = (a: Expr): Expr => (a instanceof Fn && TRIG_HYP.has(a.name) ? rewrite(raw(a.name, a.args[0]!), 'exp') : a);
const logArg = (a: Expr): Expr | undefined => (a instanceof Fn && a.name === 'log' && a.args.length === 1 ? a.args[0] : undefined);

registerRewrite('sin', 'exp', ([a]) => {
  const x = expArg(a!);
  return div(add(exp(mul(x, I)), neg(exp(neg(mul(x, I))))), mul(2, I));
});
registerRewrite('sin', 'cos', ([a]) => raw('cos', add(a!, neg(div(pi, 2)))));
registerRewrite('sin', 'tan', ([a]) => {
  const t = tan(mul(half, a!));
  return div(mul(2, t), add(1, pow(t, 2)));
});
registerRewrite('sin', 'Pow', ([a]) => {
  const x = logArg(a!);
  return x === undefined ? undefined : add(div(mul(I, pow(x, neg(I))), 2), neg(div(mul(I, pow(x, I)), 2)));
});
registerRewrite('sin', 'sincos', ([a]) => div(mul(sin(a!), cos(a!)), cos(a!)));

registerRewrite('cos', 'exp', ([a]) => {
  const x = expArg(a!);
  return div(add(exp(mul(x, I)), exp(neg(mul(x, I)))), 2);
});
registerRewrite('cos', 'sin', ([a]) => raw('sin', add(a!, div(pi, 2))));
registerRewrite('cos', 'tan', ([a]) => {
  const t = pow(tan(mul(half, a!)), 2);
  return div(add(1, neg(t)), add(1, t));
});
registerRewrite('cos', 'Pow', ([a]) => {
  const x = logArg(a!);
  return x === undefined ? undefined : add(div(pow(x, I), 2), div(pow(x, neg(I)), 2));
});
registerRewrite('cos', 'sincos', ([a]) => div(mul(sin(a!), cos(a!)), sin(a!)));

registerRewrite('tan', 'exp', ([a]) => {
  const x = expArg(a!);
  const ne = exp(neg(mul(x, I)));
  const pe = exp(mul(x, I));
  return div(mul(I, add(ne, neg(pe))), add(ne, pe));
});
registerRewrite('tan', 'cos', ([a]) => div(raw('cos', add(a!, neg(div(pi, 2)))), cos(a!)));
registerRewrite('tan', 'sin', ([a]) => div(mul(2, pow(sin(a!), 2)), sin(mul(2, a!))));
registerRewrite('tan', 'sincos', ([a]) => div(sin(a!), cos(a!)));
registerRewrite('tan', 'Pow', ([a]) => {
  const x = logArg(a!);
  if (x === undefined) return undefined;
  return div(mul(I, add(pow(x, neg(I)), neg(pow(x, I)))), add(pow(x, neg(I)), pow(x, I)));
});

registerRewrite('exp', 'cos', ([a]) => add(cos(mul(I, a!)), mul(I, cos(add(mul(I, a!), div(pi, 2))))));
registerRewrite('exp', 'sin', ([a]) => add(sin(add(mul(I, a!), div(pi, 2))), neg(mul(I, sin(mul(I, a!))))));
registerRewrite('exp', 'tanh', ([a]) => {
  const t = tanh(div(a!, 2));
  return div(add(1, t), add(1, neg(t)));
});
registerRewrite('exp', 'Pow', ([a]) => {
  if (!(a instanceof Mul)) return undefined;
  const l = a.args.find((t) => t instanceof Fn && t.name === 'log' && t.args.length === 1);
  if (!l) return undefined;
  return pow(l.args[0]!, div(a, l));
});
registerRewrite('exp', 'sqrt', ([a]) => {
  if (!(a instanceof Mul)) return undefined;
  const c = div(a, mul(pi, I));
  if (c.freeSymbols().size || c.has(pi) || c.has(I)) return undefined;
  const cs = cos(mul(pi, c));
  const sn = sin(mul(pi, c));
  if (isFunctionOf(cs, 'cos') || isFunctionOf(sn, 'sin')) return undefined;
  return add(cs, mul(I, sn));
});

registerRewrite('sinh', 'exp', ([a]) => div(add(exp(a!), neg(exp(neg(a!)))), 2));
registerRewrite('sinh', 'cosh', ([a]) => neg(mul(I, cosh(add(a!, div(mul(pi, I), 2))))));
registerRewrite('sinh', 'sin', ([a]) => neg(mul(I, sin(mul(I, a!)))));
registerRewrite('sinh', 'tanh', ([a]) => {
  const t = tanh(mul(half, a!));
  return div(mul(2, t), add(1, neg(pow(t, 2))));
});
registerRewrite('cosh', 'exp', ([a]) => div(add(exp(a!), exp(neg(a!))), 2));
registerRewrite('cosh', 'cos', ([a]) => raw('cos', mul(I, a!)));
registerRewrite('cosh', 'sinh', ([a]) => neg(mul(I, raw('sinh', add(a!, div(mul(pi, I), 2))))));
registerRewrite('cosh', 'tanh', ([a]) => {
  const t = pow(tanh(mul(half, a!)), 2);
  return div(add(1, t), add(1, neg(t)));
});
registerRewrite('tanh', 'exp', ([a]) => {
  const ne = exp(neg(a!));
  const pe = exp(a!);
  return div(add(pe, neg(ne)), add(pe, ne));
});
registerRewrite('tanh', 'cosh', ([a]) => div(mul(I, raw('cosh', add(div(mul(pi, I), 2), neg(a!)))), cosh(a!)));
registerRewrite('tanh', 'sinh', ([a]) => div(mul(I, sinh(a!)), raw('sinh', add(div(mul(pi, I), 2), neg(a!)))));
registerRewrite('tanh', 'tan', ([a]) => neg(mul(I, raw('tan', mul(I, a!)))));

// inverse trigonometric
registerRewrite('asin', 'log', ([x]) => mul(neg(I), log(add(mul(I, x!), sqrt(add(1, neg(pow(x!, 2))))))));
registerRewrite('asin', 'acos', ([x]) => add(div(pi, 2), neg(acos(x!))));
registerRewrite('asin', 'atan', ([x]) => mul(2, atan(div(x!, add(1, sqrt(add(1, neg(pow(x!, 2)))))))));
registerRewrite('acos', 'log', ([x]) => add(div(pi, 2), mul(I, log(add(mul(I, x!), sqrt(add(1, neg(pow(x!, 2)))))))));
registerRewrite('acos', 'asin', ([x]) => add(div(pi, 2), neg(asin(x!))));
registerRewrite('acos', 'atan', ([x]) =>
  add(atan(div(sqrt(add(1, neg(pow(x!, 2)))), x!)), mul(div(pi, 2), add(1, neg(mul(x!, sqrt(pow(x!, -2))))))),
);
registerRewrite('atan', 'log', ([x]) => mul(div(I, 2), add(log(add(1, neg(mul(I, x!)))), neg(log(add(1, mul(I, x!)))))));
registerRewrite('atan', 'asin', ([x]) => mul(div(sqrt(pow(x!, 2)), x!), add(div(pi, 2), neg(asin(div(1, sqrt(add(1, pow(x!, 2)))))))));
registerRewrite('atan', 'acos', ([x]) => mul(div(sqrt(pow(x!, 2)), x!), acos(div(1, sqrt(add(1, pow(x!, 2)))))));
registerRewrite('atan2', 'log', ([y, x]) => mul(neg(I), log(div(add(x!, mul(I, y!)), sqrt(add(pow(x!, 2), pow(y!, 2)))))));
registerRewrite('atan2', 'atan', ([y, x]) =>
  piecewise(
    [mul(2, atan(div(y!, add(x!, sqrt(add(pow(x!, 2), pow(y!, 2))))))), Ne(y!, 0)],
    [pi, Lt(re(x!), 0)],
    [0, Ne(x!, 0)],
    [S.NaN, true],
  ),
);

// complex functions
registerRewrite('Abs', 'sign', ([a]) => div(a!, sign(a!)));
registerRewrite('Abs', 'conjugate', ([a]) => sqrt(mul(a!, conjugate(a!))));
registerRewrite('Abs', 'Piecewise', ([a]) => {
  const r = isReal(a!);
  if (r) return piecewise([a!, Ge(a!, 0)], [neg(a!), true]);
  return undefined;
});
registerRewrite('sign', 'Abs', ([a]) => piecewise([0, Eq(a!, 0)], [div(a!, abs(a!)), true]));
registerRewrite('sign', 'Piecewise', ([a]) => {
  if (!isReal(a!)) return undefined;
  return piecewise([1, Gt(a!, 0)], [-1, Lt(a!, 0)], [0, true]);
});

// ---------------------------------------------------------------------------
// Combinatorial and gamma functions
// ---------------------------------------------------------------------------

registerRewrite('factorial', 'gamma', ([n]) => gamma(add(n!, 1)));
registerRewrite('gamma', 'factorial', ([z]) => factorial(add(z!, -1)));
registerRewrite('binomial', 'factorial', ([n, k]) => div(factorial(n!), mul(factorial(k!), factorial(add(n!, neg(k!))))));
registerRewrite('binomial', 'gamma', ([n, k]) => div(gamma(add(n!, 1)), mul(gamma(add(k!, 1)), gamma(add(n!, neg(k!), 1)))));
registerRewrite('binomial', 'FallingFactorial', ([n, k]) => (isIntegerQ(k!) ? div(ff(n!, k!), factorial(k!)) : undefined));
registerRewrite('catalan', 'binomial', ([n]) => div(binomial(mul(2, n!), n!), add(n!, 1)));
registerRewrite('catalan', 'factorial', ([n]) => div(factorial(mul(2, n!)), mul(factorial(add(n!, 1)), factorial(n!))));
registerRewrite('catalan', 'gamma', ([n]) => div(mul(pow(4, n!), gamma(add(n!, half))), mul(gamma(half), gamma(add(n!, 2)))));
registerRewrite('harmonic', 'Sum', ([n, m]) => {
  const k = new Dummy('k', { integer: true });
  return Sum(pow(k, neg(m ?? S.One)), [k, 1, n!]);
});
const harmonicPolygamma: RewriteRule = ([n, m]) => {
  const mm = m ?? S.One;
  if (!(isIntegerQ(mm) && isPositive(mm))) return undefined;
  return piecewise(
    [add(polygamma(0, add(n!, 1)), S.EulerGamma), Eq(mm, 1)],
    [div(mul(pow(-1, mm), add(polygamma(add(mm, -1), 1), neg(polygamma(add(mm, -1), add(n!, 1))))), gamma(mm)), true],
  );
};
registerRewrite('harmonic', 'polygamma', harmonicPolygamma);
registerRewrite('harmonic', 'digamma', harmonicPolygamma);
registerRewrite('harmonic', 'trigamma', harmonicPolygamma);
registerRewrite('polygamma', 'harmonic', ([n, z]) => {
  if (!isIntegerQ(n!)) return undefined;
  if (n instanceof Rational && n.isZero) return add(harmonic(add(z!, -1)), neg(S.EulerGamma));
  return mul(pow(-1, add(n!, 1)), factorial(n!), add(zeta(add(n!, 1)), neg(harmonic(add(z!, -1), add(n!, 1)))));
});

// exponential integrals
const lz = (z: Expr) => log(z);
registerRewrite('li', 'Ei', ([z]) => Ei(log(z!)));
registerRewrite('li', 'Li', ([z]) => add(Li(z!), li(2)));
const liShi: RewriteRule = ([z]) =>
  add(Chi(lz(z!)), neg(Shi(lz(z!))), neg(mul(half, add(log(div(1, lz(z!))), neg(log(lz(z!)))))));
const liSi: RewriteRule = ([z]) =>
  add(
    Ci(mul(I, lz(z!))),
    neg(mul(I, Si(mul(I, lz(z!))))),
    neg(mul(half, add(log(div(1, lz(z!))), neg(log(lz(z!)))))),
    neg(log(mul(I, lz(z!)))),
  );
registerRewrite('li', 'Shi', liShi);
registerRewrite('li', 'Chi', liShi);
registerRewrite('li', 'Si', liSi);
registerRewrite('li', 'Ci', liSi);
registerRewrite('Li', 'li', ([z]) => add(li(z!), neg(li(2))));
const eiShi: RewriteRule = ([z]) => (isNegative(z!) ? add(Shi(z!), Chi(z!), neg(mul(I, pi))) : add(Shi(z!), Chi(z!)));
for (const t of ['Shi', 'Chi', 'Si', 'Ci']) registerRewrite('Ei', t, eiShi);
registerRewrite('Ei', 'li', ([z]) => (z instanceof Fn && z.name === 'log' && z.args.length === 1 ? li(z.args[0]!) : li(exp(z!))));

registerRewrite('expint', 'uppergamma', ([nu, z]) => mul(pow(z!, add(nu!, -1)), uppergamma(add(1, neg(nu!)), z!)));
