// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import {
  And,
  CBooleanFunction,
  CFunction,
  Cbrt,
  Eq,
  Float,
  I,
  Implies,
  Lt,
  Mod,
  NoMatch,
  Not,
  Q,
  Rational,
  S,
  Sqrt,
  Sym,
  add,
  ask,
  asSet,
  diff,
  evalf,
  exp2,
  expand,
  expandFunc,
  expandLog,
  fma,
  hypot,
  isReal,
  isinf,
  isnan,
  kindOf,
  lambdify,
  latex,
  log,
  log10,
  log1p,
  log2,
  expm1,
  mul,
  neg,
  pi,
  pow,
  pretty,
  rewrite,
  srepr,
  str,
  subs,
  symbols,
  Wild,
  countOps,
  asLeadingTerm,
  limit,
  series,
  sin,
  sqrt,
  taylorTerm,
} from '../../src';
import type { Expr } from '../../src';
import { impl } from '../../src/core/nodes';
import { NotLoadedError } from '../../src/core/errors';

const [x, y, z] = symbols('x y z') as [Sym, Sym, Sym];
const r = new Sym('r', { real: true });
const s = (e: Expr): string => str(e);

describe('evaluation', () => {
  it('expm1 evaluates where exp does', () => {
    expect(s(expm1(0))).toBe('0');
    expect(s(expm1(log(3)))).toBe('2');
    expect(s(expm1(mul(I, pi)))).toBe('-2');
    expect(s(expm1(S.Infinity))).toBe('oo');
    expect(s(expm1(x))).toBe('expm1(x)');
    expect(s(expm1(2))).toBe('expm1(2)');
    expect(s(expm1(add(x, new Float(0.5))))).toBe('1.64872127070013*exp(x) - 1');
  });

  it('Float arguments evaluate at their precision without cancellation', () => {
    expect(s(expm1(new Float(1e-10)))).toBe('1.00000000005000e-10');
    expect(s(expm1(new Float(0.5)))).toBe('0.648721270700128');
    expect(s(expm1(add(new Float(1), mul(new Float(2), I))))).toBe('-2.13120438375681 + 2.47172667200482*I');
    expect(s(expm1(add(new Float(1), mul(2, I))))).toBe('-1 + 2.71828182845905*exp(2*I)');
    expect(s(expm1(add(1, mul(new Float(2), I))))).toBe('expm1(1 + 2.0*I)');
    expect(s(expm1(add(new Float(1), mul(2, x))))).toBe('2.71828182845905*exp(2*x) - 1');
    expect(s(log1p(add(new Float(1), x, y)))).toBe('log1p(x + y + 1.0)');
    expect(s(Sqrt(new Float(2)))).toBe('Sqrt(2.0)');
    expect(s(hypot(new Float(3), new Float(4)))).toBe('5.00000000000000');
    expect(s(hypot(new Float(3), 4))).toBe('hypot(3.0, 4)');
    expect(s(hypot(mul(new Float(3), I), new Float(4)))).toBe('hypot(3.0*I, 4.0)');
  });

  it('log1p evaluates rationals, Floats exactly and logarithms that evaluate', () => {
    expect(s(log1p(0))).toBe('0');
    expect(s(log1p(2))).toBe('log(3)');
    expect(s(log1p(-1))).toBe('zoo');
    expect(s(log1p(I))).toBe('log(sqrt(2)) + I*pi/4');
    expect(s(log1p(new Float(0.5)))).toBe('log(3/2)');
    expect(s(log1p(pi))).toBe('log1p(pi)');
    expect(s(log1p(x))).toBe('log1p(x)');
    expect(s(evalf(expandLog(log1p(new Float(1e-99)))))).toBe('1.00000000000000e-99');
  });

  it('exp2, log2 and log10', () => {
    expect(s(exp2(2))).toBe('4');
    expect(s(exp2(Rational.of(1n, 2n)))).toBe('sqrt(2)');
    expect(s(exp2(new Float(2.5)))).toBe('5.65685424949238');
    expect(s(exp2(x))).toBe('exp2(x)');
    expect(s(log2(8))).toBe('3');
    expect(s(log2(Rational.of(1n, 4n)))).toBe('-2');
    expect(s(log2(0))).toBe('zoo');
    expect(s(log2(S.Infinity))).toBe('oo');
    expect(s(log2(3))).toBe('log2(3)');
    expect(s(log2(-8))).toBe('log2(-8)');
    expect(s(log2(new Float(4)))).toBe('2.00000000000000');
    expect(s(log2(pow(2, x)))).toBe('x');
    expect(s(log2(pow(3, x)))).toBe('log2(3**x)');
    expect(s(log2(x))).toBe('log2(x)');
    expect(s(log10(100))).toBe('2');
    expect(s(log10(new Float(0.1)))).toBe('-1.00000000000000');
    expect(s(log10(pow(10, x)))).toBe('x');
  });

  it('fma, Sqrt, Cbrt and hypot stay unevaluated', () => {
    expect(s(fma(1, 2, 3))).toBe('fma(1, 2, 3)');
    expect(s(Sqrt(4))).toBe('Sqrt(4)');
    expect(s(Cbrt(8))).toBe('Cbrt(8)');
    expect(s(hypot(3, 4))).toBe('hypot(3, 4)');
  });

  it('isnan and isinf', () => {
    expect(isnan(S.NaN)).toBe(S.true);
    expect(isnan(1)).toBe(S.false);
    expect(isnan(S.ComplexInfinity)).toBe(S.false);
    expect(s(isnan(x))).toBe('isnan(x)');
    expect(isinf(S.Infinity)).toBe(S.true);
    expect(isinf(S.NegativeInfinity)).toBe(S.true);
    expect(isinf(S.ComplexInfinity)).toBe(S.true);
    expect(isinf(pi)).toBe(S.false);
    expect(isinf(r)).toBe(S.false);
    expect(s(isinf(x))).toBe('isinf(x)');
    expect(s(isinf(S.NaN))).toBe('isinf(nan)');
  });

  it('checks the number of arguments', () => {
    expect(() => expm1(x, y)).toThrow(new TypeError('expm1 takes exactly 1 argument (2 given)'));
    expect(() => hypot(x)).toThrow(new TypeError('hypot takes exactly 2 arguments (1 given)'));
  });
});

describe('numeric evaluation', () => {
  it('evaluates to any precision', () => {
    expect(s(evalf(expm1(pi), 30))).toBe('22.1406926327792690057290863679');
    expect(s(evalf(expm1(Rational.of(1n, 10n ** 30n)), 20))).toBe('1.0000000000000000000e-30');
    expect(s(evalf(log1p(mul(pi, Rational.of(1n, 10n ** 40n))), 20))).toBe('3.1415926535897932385e-40');
    expect(s(evalf(log2(3), 30))).toBe('1.58496250072115618145373894395');
    expect(s(evalf(log10(3)))).toBe('0.477121254719662');
    expect(s(evalf(log2(I)))).toBe('2.2661800709136*I');
    expect(s(evalf(hypot(3, 4), 30))).toBe('5.00000000000000000000000000000');
    expect(s(evalf(add(expm1(1), 1)))).toBe('2.71828182845905');
  });

  it('keeps applications without a numeric value', () => {
    expect(s(evalf(Sqrt(2)))).toBe('Sqrt(2)');
    expect(s(evalf(fma(1, 2, 3)))).toBe('fma(1, 2, 3)');
    expect(s(evalf(hypot(I, 1)))).toBe('hypot(I, 1)');
    expect(s(evalf(expm1(add(x, 2))))).toBe('expm1(x + 2)');
    expect(s(evalf(log2(add(x, 1))))).toBe('1.44269504088896*log(x + 1)');
    expect(s(evalf(expm1(x), { x: 2 }))).toBe('6.38905609893065');
    expect(s(evalf(Sqrt(x), { x: 2 }))).toBe('Sqrt(2)');
  });
});

describe('calculus and rewriting', () => {
  it('differentiates', () => {
    expect(s(diff(expm1(x), x))).toBe('exp(x)');
    expect(s(diff(log1p(x), x))).toBe('1/(x + 1)');
    expect(s(diff(exp2(x), x))).toBe('log(2)*exp2(x)');
    expect(s(diff(log2(x), x))).toBe('1/(x*log(2))');
    expect(s(diff(log10(x), x))).toBe('1/(x*log(10))');
    expect(s(diff(Sqrt(x), x))).toBe('1/(2*sqrt(x))');
    expect(s(diff(Cbrt(x), x))).toBe('1/(3*x**(2/3))');
    expect(s(diff(hypot(x, y), x))).toBe('x/hypot(x, y)');
    expect(s(diff(hypot(x, y), y))).toBe('y/hypot(x, y)');
    expect(s(diff(fma(x, y, z), x))).toBe('y');
    expect(s(diff(fma(x, y, z), y))).toBe('x');
    expect(s(diff(fma(x, y, z), z))).toBe('1');
    expect(s(diff(expm1(mul(42, x)), x))).toBe('42*exp(42*x)');
    expect(() => diff(isnan(x), x)).toThrow();
  });

  it('fdiff', () => {
    const e = hypot(x, y);
    if (!(e instanceof CFunction)) throw new TypeError('not an application');
    expect(s(e.fdiff())).toBe('x/hypot(x, y)');
    expect(s(e.fdiff(2))).toBe('y/hypot(x, y)');
    expect(() => e.fdiff(3)).toThrow(RangeError);
    expect(() => e.fdiff(0)).toThrow(RangeError);
    expect(() => e.fdiff(1.5)).toThrow(RangeError);
    const b = isnan(x);
    if (!(b instanceof CBooleanFunction)) throw new TypeError('not an application');
    expect(() => b.fdiff()).toThrow(new RangeError('Invalid operation with argument number 1 for Function isnan(x)'));
  });

  it('expands and rewrites', () => {
    expect(s(expand(expm1(x), { func: true }))).toBe('exp(x) - 1');
    expect(s(expandFunc(log1p(x)))).toBe('log(x + 1)');
    expect(s(expandFunc(exp2(x)))).toBe('2**x');
    expect(s(expandFunc(log2(x)))).toBe('log(x)/log(2)');
    expect(s(expandFunc(log10(x)))).toBe('log(x)/log(10)');
    expect(s(expandFunc(fma(x, y, z)))).toBe('x*y + z');
    expect(s(expandFunc(Sqrt(x)))).toBe('sqrt(x)');
    expect(s(expandFunc(Cbrt(x)))).toBe('x**(1/3)');
    expect(s(expandFunc(hypot(x, y)))).toBe('sqrt(x**2 + y**2)');
    expect(s(rewrite(expm1(x), 'exp'))).toBe('exp(x) - 1');
    expect(s(rewrite(expm1(x), 'tractable'))).toBe('exp(x) - 1');
    expect(s(rewrite(log1p(x), 'log'))).toBe('log(x + 1)');
    expect(s(rewrite(log1p(x), 'tractable'))).toBe('log(x + 1)');
    expect(s(rewrite(exp2(x), 'Pow'))).toBe('2**x');
    expect(s(rewrite(exp2(x), 'tractable'))).toBe('2**x');
    expect(s(rewrite(exp2(x), 'exp'))).toBe('exp2(x)');
    expect(s(rewrite(log2(x), 'log'))).toBe('log(x)/log(2)');
    expect(s(rewrite(log10(x), 'tractable'))).toBe('log(x)/log(10)');
    expect(s(rewrite(fma(x, y, z), 'tractable'))).toBe('x*y + z');
    expect(s(rewrite(Sqrt(x), 'Pow'))).toBe('sqrt(x)');
    expect(s(rewrite(Cbrt(x), 'Pow'))).toBe('x**(1/3)');
    expect(s(rewrite(hypot(x, y), 'Pow'))).toBe('sqrt(x**2 + y**2)');
    expect(s(rewrite(isnan(x), 'Pow'))).toBe('isnan(x)');
  });

  it('substitutes and rebuilds', () => {
    expect(s(subs(Sqrt(x), [[x, 4]]))).toBe('Sqrt(4)');
    expect(s(subs(exp2(x), [[x, 3]]))).toBe('8');
    expect(s(subs(isnan(x), [[x, 1]]))).toBe('False');
  });
});

describe('assumptions', () => {
  it('expm1 is real and finite with its argument', () => {
    expect(isReal(expm1(r))).toBe(true);
    expect(isReal(expm1(x))).toBe('unknown');
    expect(isReal(expm1(I))).toBe(false);
    expect(isReal(Sqrt(r))).toBe('unknown');
    const e = expm1(r);
    if (!(e instanceof CFunction)) throw new TypeError('not an application');
    expect(e.isReal).toBe(true);
    expect(e.isFinite).toBe(true);
  });

  it('log1p', () => {
    const app = (a: Expr): CFunction => {
      const e = log1p(a);
      if (!(e instanceof CFunction)) throw new TypeError('not an application');
      return e;
    };
    expect(app(neg(pow(2, Rational.of(-1n, 2n)))).isReal).toBe(true);
    expect(app(pi).isFinite).toBe(true);
    expect(app(add(new Sym('zz', { zero: true }), -1)).isFinite).toBe(false);
    expect(app(r).isPositive).toBe('unknown');
    expect(app(new Sym('p', { positive: true })).isPositive).toBe(true);
    expect(app(new Sym('zz', { zero: true })).isZero).toBe(true);
    expect(app(r).isZero).toBe('unknown');
    expect(app(new Sym('o', { nonnegative: true })).isNonnegative).toBe(true);
    expect(app(new Sym('o', { nonnegative: true })).isNonNegative).toBe(true);
    expect(app(r).isNonnegative).toBe('unknown');
    expect(ask(Q.positive(log1p(x)), Q.positive(x))).toBe(true);
  });

  it('kinds', () => {
    expect(String(kindOf(isnan(x)))).toBe('BooleanKind');
    expect(String(kindOf(expm1(x)))).toBe('NumberKind');
  });
});

describe('printing', () => {
  it('prints like SymPy', () => {
    expect(latex(expm1(x))).toBe('\\operatorname{expm}_{1}{\\left(x \\right)}');
    expect(latex(log1p(x))).toBe('\\operatorname{log1p}{\\left(x \\right)}');
    expect(latex(log2(x))).toBe('\\operatorname{log}_{2}{\\left(x \\right)}');
    expect(latex(log10(x))).toBe('\\operatorname{log}_{10}{\\left(x \\right)}');
    expect(latex(hypot(x, y))).toBe('\\operatorname{hypot}{\\left(x,y \\right)}');
    expect(latex(isnan(x))).toBe('\\operatorname{isnan}\\left(x\\right)');
    expect(pretty(expm1(x))).toBe('expm₁(x)');
    expect(pretty(isnan(x))).toBe('isnan(x)');
    expect(pretty(hypot(x, y))).toBe('hypot(x, y)');
    expect(srepr(expm1(x))).toBe("expm1(Symbol('x'))");
    expect(s(mul(2, Sqrt(x)))).toBe('2*Sqrt(x)');
  });

  it('works in boolean expressions', () => {
    expect(s(And(isinf(x), isnan(y)))).toBe('isinf(x) & isnan(y)');
    expect(s(Not(isnan(x)))).toBe('~isnan(x)');
  });
});

describe('lambdify', () => {
  const at = (f: (...a: number[]) => { re: number; im: number }, ...a: number[]): number => f(...a).re;
  it('real arguments', () => {
    expect(at(lambdify(expm1(x), [x]), 1e-10)).toBe(Math.expm1(1e-10));
    expect(at(lambdify(log1p(x), [x]), 1e-10)).toBe(Math.log1p(1e-10));
    expect(at(lambdify(exp2(x), [x]), 3)).toBe(8);
    expect(at(lambdify(log2(x), [x]), 8)).toBe(3);
    expect(at(lambdify(log10(x), [x]), 100)).toBe(2);
    expect(at(lambdify(fma(x, y, z), [x, y, z]), 1, 2, 3)).toBe(5);
    expect(at(lambdify(Sqrt(x), [x]), 4)).toBeCloseTo(2, 14);
    expect(at(lambdify(Cbrt(x), [x]), 8)).toBeCloseTo(2, 14);
    expect(at(lambdify(hypot(x, y), [x, y]), 3, 4)).toBe(5);
  });

  it('complex arguments', () => {
    const i = { re: 0, im: 1 };
    const close = (v: { re: number; im: number }, re: number, im: number): void => {
      expect(v.re).toBeCloseTo(re, 12);
      expect(v.im).toBeCloseTo(im, 12);
    };
    close(lambdify(expm1(x), [x])(i), Math.cos(1) - 1, Math.sin(1));
    close(lambdify(log1p(x), [x])(i), Math.log(Math.SQRT2), Math.PI / 4);
    close(lambdify(exp2(x), [x])(i), Math.cos(Math.LN2), Math.sin(Math.LN2));
    close(lambdify(log2(x), [x])(i), 0, Math.PI / 2 / Math.LN2);
    close(lambdify(log10(x), [x])(i), 0, Math.PI / 2 / Math.LN10);
    close(lambdify(Sqrt(x), [x])(-1), 0, 1);
    close(lambdify(hypot(x, y), [x, y])(i, 1), 0, 0);
    close(lambdify(hypot(x, y), [x, y])(1, i), 0, 0);
  });
});

describe('class members', () => {
  it('are callable classes with SymPy class attributes', () => {
    expect(expm1(x)).toBeInstanceOf(expm1);
    expect(expm1(x)).toBeInstanceOf(CFunction);
    expect(expm1(x)).not.toBeInstanceOf(log1p);
    expect(isnan(x)).toBeInstanceOf(CBooleanFunction);
    expect(expm1.functionName).toBe('expm1');
    expect(isinf.name).toBe('isinf');
    expect(expm1.eval(0)).toEqual(S.Zero);
    expect(expm1.eval(x)).toBe(NoMatch);
    expect(fma.eval(x, y, z)).toBe(NoMatch);
    expect(isnan.eval(S.NaN)).toBe(S.true);
    expect(s(expm1.nargs)).toBe('{1}');
    expect(s(fma.nargs)).toBe('{3}');
    expect(expm1.isSingular(0)).toBe('unknown');
    expect(expm1.defaultAssumptions.size).toBe(0);
    const e = isinf(x);
    if (!(e instanceof CBooleanFunction)) throw new TypeError('not an application');
    expect(e.func).toBe(isinf);
    expect(e.args).toEqual([x]);
  });

  it('binaryCheckAndSimplify', () => {
    const [a, b] = symbols('a b') as [Sym, Sym];
    expect(isnan.binaryCheckAndSimplify(a, Eq(a, 1)).map(s)).toEqual(['a', 'False']);
    expect(isnan.binaryCheckAndSimplify(a, Eq(a, S.true), Eq(b, 1)).map(s)).toEqual(['a', 'Eq(a, True)', 'Eq(b, 1)']);
    expect(isnan.binaryCheckAndSimplify(And(a, Eq(b, 2))).map(s)).toEqual(['a & Eq(b, 2)']);
    expect(() => isnan.binaryCheckAndSimplify(a, Lt(a, 1))).toThrow(TypeError);
  });

  it('flags, assumptions and Basic attributes of an application', () => {
    const e = expm1(r);
    if (!(e instanceof CFunction)) throw new TypeError('not an application');
    const flags = ['isAdd', 'isAlgebraicNumber', 'isBoolean', 'isDerivative', 'isDummy', 'isEquality', 'isFloat', 'isIndexed', 'isMatAdd', 'isMatMul', 'isMatrix', 'isMul', 'isNot', 'isNumberSymbol', 'isOrder', 'isPiecewise', 'isPoint', 'isPoly', 'isPow', 'isRelational', 'isSymbol', 'isVector', 'isWild'] as const;
    for (const f of flags) expect(e[f], f).toBe(false);
    const b = isnan(x);
    if (!(b instanceof CBooleanFunction)) throw new TypeError('not an application');
    expect(b.isBoolean).toBe(true);
    const queries = {
      isAlgebraic: 'algebraic', isAntihermitian: 'antihermitian', isComplex: 'complex', isComposite: 'composite', isEven: 'even',
      isExtendedNegative: 'extended_negative', isExtendedNonnegative: 'extended_nonnegative', isExtendedNonpositive: 'extended_nonpositive',
      isExtendedNonzero: 'extended_nonzero', isExtendedPositive: 'extended_positive', isExtendedReal: 'extended_real', isFinite: 'finite',
      isHermitian: 'hermitian', isImaginary: 'imaginary', isInfinite: 'infinite', isInteger: 'integer', isIrrational: 'irrational',
      isNegative: 'negative', isNoninteger: 'noninteger', isNonnegative: 'nonnegative', isNonpositive: 'nonpositive', isNonzero: 'nonzero',
      isNonZero: 'nonzero', isOdd: 'odd', isPositive: 'positive', isPrime: 'prime', isRational: 'rational', isReal: 'real',
      isTranscendental: 'transcendental', isZero: 'zero',
    } as const;
    for (const [q, p] of Object.entries(queries)) expect(e[q as keyof typeof queries], q).toBe(ask(Q[p](e)));
    expect([e.isReal, e.isFinite, e.isInfinite, e.isImaginary, e.isPolar]).toEqual([true, true, false, false, 'unknown']);
    expect(e.assumptions0.size).toBe(0);
    expect(e.canonicalVariables.size).toBe(0);
    expect(e.defaultAssumptions.size).toBe(0);
    expect([...e.exprFreeSymbols]).toEqual([r]);
    expect(s(e.floordiv(2))).toBe('floor(expm1(r)/2)');
    expect(e.mod(2)).toEqual(Mod(e, 2));
  });

  it('Basic methods as aliases of the public functions', () => {
    const e = hypot(x, 2);
    if (!(e instanceof CFunction)) throw new TypeError('not an application');
    const w = new Wild('w');
    expect(s(e.asContentPrimitive()[1])).toBe('hypot(x, 2)');
    expect(s(e.asDummy())).toBe('hypot(x, 2)');
    expect(e.atoms().map(s).sort()).toEqual(['2', 'x']);
    expect(e.classKey()).toBeDefined();
    expect(e.compare(e)).toBe(0);
    expect(e.copy()).toBe(e);
    expect(e.couldExtractMinusSign()).toBe(false);
    expect(e.count(x)).toBe(1);
    expect(e.countOps()).toBe(countOps(e));
    expect(s(e.doit())).toBe('hypot(x, 2)');
    expect(e.dummyEq(hypot(x, 2))).toBe(true);
    expect(e.find(x).map(s)).toEqual(['x']);
    expect(e.hasFree(x)).toBe(true);
    expect(e.hasXfree([y])).toBe(false);
    expect(e.isHypergeometric(x)).toBe(false);
    expect(e.isSame(hypot(x, 2))).toBe(true);
    const m = e.match(hypot(w, 2));
    expect(m instanceof Map ? s(m.get(w) ?? S.Zero) : m).toBe('x');
    const m2 = hypot(w, 2) instanceof CFunction ? (hypot(w, 2) as CFunction).matches(e) : NoMatch;
    expect(m2 instanceof Map ? s(m2.get(w) ?? S.Zero) : m2).toBe('x');
    expect(s(e.rcall(y))).toBe('hypot(x, 2)');
    expect(s(e.refine(Q.positive(x)))).toBe('hypot(x, 2)');
    expect(e.replace(x, y)).toEqual(hypot(y, 2));
    expect(e.sortKey()).toBeDefined();
    expect(s(e.xreplace([[x, y]]))).toBe('hypot(y, 2)');
  });

  it('boolean methods', () => {
    const b = isinf(x);
    if (!(b instanceof CBooleanFunction)) throw new TypeError('not an application');
    expect(b.binarySymbols.size).toBe(0);
    expect(s(b.toNnf())).toBe('isinf(x)');
    expect(s(b.toAnf())).toBe('isinf(x)');
    expect(b.rshift(y)).toEqual(Implies(b, y));
    expect(b.lshift(y)).toEqual(Implies(y, b));
    expect(() => b.asSet()).toThrow();
    expect(() => asSet(b)).toThrow();
  });

  it('late-bound methods name the entry point when it is not loaded', () => {
    const b = isinf(x);
    if (!(b instanceof CBooleanFunction)) throw new TypeError('not an application');
    const saved = Object.fromEntries((['asSet', 'doit', 'isHypergeometric'] as const).map((k) => [k, Reflect.get(impl, k)]));
    try {
      delete impl.asSet;
      delete impl.doit;
      delete impl.isHypergeometric;
      expect(() => b.asSet()).toThrow(NotLoadedError);
      expect(() => b.doit()).toThrow("doit is not available: import '@symjs/symjs/calculus' (or '@symjs/symjs')");
      expect(() => b.isHypergeometric(x)).toThrow(NotLoadedError);
    } finally {
      Object.assign(impl, saved);
    }
  });
});

describe('series, leading terms and limits', () => {
  const ser = (e: Expr, x0: Expr | number = 0, n = 6): string => s(series(e, x, x0, n));
  const xp1 = add(x, 1);

  it('Taylor series from the derivatives at the point (SymPy Function._eval_nseries)', () => {
    expect(ser(expm1(x))).toBe('x + x**2/2 + x**3/6 + x**4/24 + x**5/120 + O(x**6)');
    expect(ser(expm1(x), 1, 3)).toBe('E - 1 + E*(x - 1) + E*(x - 1)**2/2 + O((x - 1)**3, (x, 1))');
    expect(ser(log1p(x), 0, 3)).toBe('x - x**2/2 + O(x**3)');
    expect(ser(log1p(x), 1, 3)).toBe('log(2) - 1/2 - (x - 1)**2/8 + x/2 + O((x - 1)**3, (x, 1))');
    expect(ser(exp2(x), 0, 3)).toBe('1 + x*log(2) + x**2*log(2)**2/2 + O(x**3)');
    expect(ser(exp2(x), 1, 3)).toBe('2 + 2*(x - 1)*log(2) + (x - 1)**2*log(2)**2 + O((x - 1)**3, (x, 1))');
    expect(ser(log2(x), 1, 3)).toBe('(x - 1)/log(2) - (x - 1)**2/(2*log(2)) + O((x - 1)**3, (x, 1))');
    expect(ser(log10(xp1), 1, 3)).toBe('log10(2) + (x - 1)/(2*log(10)) - (x - 1)**2/(8*log(10)) + O((x - 1)**3, (x, 1))');
    expect(ser(log2(xp1), 0, 3)).toBe('x/log(2) - x**2/(2*log(2)) + O(x**3)');
  });

  it('keeps the unevaluated values of Sqrt, Cbrt, hypot and fma at the point', () => {
    expect(ser(Sqrt(xp1))).toBe('Sqrt(1) + x/2 - x**2/8 + x**3/16 - 5*x**4/128 + 7*x**5/256 + O(x**6)');
    expect(ser(Sqrt(x), 1, 3)).toBe('-1/2 + Sqrt(1) - (x - 1)**2/8 + x/2 + O((x - 1)**3, (x, 1))');
    expect(ser(Cbrt(xp1), 1, 3)).toBe('Cbrt(2) + 2**(1/3)*(x - 1)/6 - 2**(1/3)*(x - 1)**2/36 + O((x - 1)**3, (x, 1))');
    expect(ser(hypot(x, y))).toBe('hypot(0, y) + x**2/(2*hypot(0, y)) - x**4/(8*hypot(0, y)**3) + O(x**6)');
    expect(ser(hypot(x, y), 1, 3)).toBe('hypot(1, y) + (x - 1)/hypot(1, y) + (x - 1)**2*(1/(2*hypot(1, y)) - 1/(2*hypot(1, y)**3)) + O((x - 1)**3, (x, 1))');
    expect(ser(fma(x, y, 3))).toBe('fma(0, y, 3) + x*y + O(x**6)');
    // several arguments depending on x: the Taylor series in x
    expect(ser(fma(x, x, 1), 0, 4)).toBe('fma(0, 0, 1) + x**2 + O(x**4)');
    expect(ser(mul(exp2(pow(x, 2)), Sqrt(xp1)), 0, 4)).toBe('Sqrt(1) + x/2 + x**2*(log(2)*Sqrt(1) - 1/8) + x**3*(1/16 + log(2)/2) + O(x**4)');
  });

  it('composes with other series', () => {
    expect(ser(expm1(sin(x)), 0, 4)).toBe('x + x**2/2 + O(x**4)');
    expect(ser(log1p(sqrt(x)), 0, 4)).toBe('-x/2 - x**2/4 - x**3/6 + sqrt(x) + x**(3/2)/3 + x**(5/2)/5 + x**(7/2)/7 + O(x**4)');
    expect(ser(add(expm1(mul(2, x)), mul(-2, expm1(x))), 0, 4)).toBe('x**2 + x**3 + O(x**4)');
  });

  it('expands the rewrite at a singular point, where SymPy gives nan', () => {
    expect(ser(log2(x))).toBe('log(x)/log(2)');
    expect(ser(log10(x), 0, 3)).toBe('log(x)/log(10)');
    expect(ser(Sqrt(x))).toBe('sqrt(x)');
    expect(ser(Cbrt(x))).toBe('x**(1/3)');
    expect(ser(log1p(x), S.Infinity, 3)).toBe('-1/(2*x**2) + 1/x - log(1/x) + O(x**(-3), (x, oo))');
    expect(ser(hypot(x, 1), S.Infinity, 3)).toBe('1/(2*x) + x + O(x**(-3), (x, oo))');
    expect(() => series(expm1(x), x, S.Infinity, 3)).toThrow('essential singularity');
  });

  it('leading terms come from the series (SymPy raises NotImplementedError or keeps the application)', () => {
    expect(s(asLeadingTerm(expm1(x), x))).toBe('x');
    expect(s(asLeadingTerm(log2(xp1), x))).toBe('x/log(2)');
    expect(s(asLeadingTerm(Sqrt(xp1), x))).toBe('Sqrt(1)');
    expect(s(asLeadingTerm(hypot(x, y), x))).toBe('hypot(0, y)');
    expect(s(asLeadingTerm(mul(Sqrt(x), pow(x, -1)), x))).toBe('1/sqrt(x)');
  });

  it('limits rewrite the functions in terms of tractable ones', () => {
    expect(s(limit(expm1(x), x, 0))).toBe('0');
    expect(s(limit(expm1(x), x, S.Infinity))).toBe('oo');
    expect(s(limit(mul(expm1(x), pow(x, -1)), x, 0))).toBe('1');
    expect(s(limit(mul(log1p(x), pow(x, -1)), x, 0))).toBe('1');
    expect(s(limit(exp2(x), x, S.Infinity))).toBe('oo');
    expect(s(limit(mul(exp2(x), pow(x, -1)), x, 0))).toBe('oo');
    expect(s(limit(log2(x), x, 0))).toBe('-oo');
    expect(s(limit(mul(log10(xp1), pow(x, -1)), x, 0))).toBe('1/log(10)');
    expect(s(limit(Sqrt(xp1), x, 0))).toBe('1');
    expect(s(limit(Cbrt(x), x, S.Infinity))).toBe('oo');
    expect(s(limit(hypot(x, 1), x, 0))).toBe('1');
    expect(s(limit(fma(x, y, 3), x, 0))).toBe('3');
  });

  it('Taylor terms of a pole are complex infinity', () => {
    expect(s(taylorTerm(expm1(x), 3, x))).toBe('x**3/6');
    expect(s(taylorTerm(log2(x), 3, x))).toBe('zoo*x**3');
    expect(s(taylorTerm(Cbrt(xp1), 3, x))).toBe('5*x**3/81');
  });
});
