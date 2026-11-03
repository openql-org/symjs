// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/ops.ts.
// The canonicalizing constructors add/mul/pow: floats, infinities, Order terms, AccumBounds
// operands, noncommutative factors and the root functions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_arit / test_numbers / test_power).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { E, I, Sym, add, exp, log, mul, pi, pow, rational, sqrt, symbol, symbols } from '../../src';
import { SympifyError } from '../../src/core/errors';
import { Add, Float, Order, Pow, Rational, S } from '../../src/core/nodes';
import { sympify } from '../../src/core/ops';

const [x, y, a, z] = symbols('x y a z');

const theta = symbol('theta', { real: true });

const R = (p: bigint, q = 1n): sj.Rational => sj.Rational.of(p, q);
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y, a } } as never);

const f = sj.SymFunction('f');
const P2 = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y }, functions: { f } } as never);

const { oo, zoo, nan } = sj;

const p = new sj.Sym('p', { positive: true });
const n = new sj.Sym('n', { negative: true });
const r = new sj.Sym('r', { real: true });

const s = (e: sj.Expr): string => e.toString();
const R2 = (a: number, b = 1) => Rational.of(a, b);
const negOo = mul(-1, oo);

const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });

describe('canonicalization', () => {
  it('collects like terms and folds constants', () => {
    expect(add(x, x, 1, 2).toString()).toBe('2*x + 3');
    expect(x.add(y).sub(x).toString()).toBe('y');
    expect(mul(x, x, y).toString()).toBe('x**2*y');
    expect(mul(x, pow(x, -1)).toString()).toBe('1');
  });

  it('is order independent', () => {
    expect(add(x, y).equals(add(y, x))).toBe(true);
    expect(mul(x, y, 2).equals(mul(2, y, x))).toBe(true);
  });

  it('handles exact rationals', () => {
    expect(rational(1, 2).add(rational(1, 3)).toString()).toBe('5/6');
    expect(mul(x, rational(1, 2)).toString()).toBe('x/2');
    expect(add(x, 0.5).toString()).toBe('x + 0.5');
  });

  it('simplifies radicals', () => {
    expect(sqrt(8).toString()).toBe('2*sqrt(2)');
    expect(pow(2, rational(-1, 2)).toString()).toBe('sqrt(2)/2');
    expect(mul(sqrt(2), sqrt(2)).toString()).toBe('2');
    expect(mul(sqrt(2), sqrt(3)).toString()).toBe('sqrt(6)');
    expect(sqrt(-4).toString()).toBe('2*I');
    expect(pow(rational(1, 4), rational(1, 2)).toString()).toBe('1/2');
    expect(mul(sqrt(2), pow(sqrt(2), -1)).toString()).toBe('1');
  });

  it('handles the imaginary unit', () => {
    expect(mul(I, I).toString()).toBe('-1');
    expect(pow(I, 3).toString()).toBe('-I');
    expect(add(I, mul(2, I)).toString()).toBe('3*I');
  });

  it('combines exponentials', () => {
    expect(mul(exp(x), exp(y)).toString()).toBe('exp(x)*exp(y)');
    expect(mul(exp(x), exp(mul(2, x))).toString()).toBe('exp(3*x)');
    expect(mul(exp(mul(I, theta)), exp(mul(-1, I, theta))).toString()).toBe('1');
    expect(exp(mul(I, pi)).toString()).toBe('-1');
    expect(exp(mul(rational(1, 2), I, pi)).toString()).toBe('I');
    expect(exp(log(x)).toString()).toBe('x');
    expect(pow(E, add(x, mul(I, pi))).toString()).toBe('-exp(x)');
  });

  it('distributes numeric coefficients', () => {
    expect(mul(2, add(x, 1)).toString()).toBe('2*x + 2');
  });
});

describe('numeric radicals in a product', () => {
  it('an unevaluated integer power is multiplied out: Mul(Pow(2, 3, evaluate=False), x)', () => {
    expect(String(sj.mul(new sj.Pow(R(2n), R(3n)), x))).toBe('8*x');
  });
  it('bases sharing an exponent after the common factors are pulled out', () => {
    expect(String(P('6**(1/6)*10**(1/3)*7**(1/2)'))).toBe('sqrt(14)*3**(1/6)*5**(1/3)');
  });
  it('the same in one product: bases with equal exponents after the common factors are pulled out', () => {
    const third = R(1n, 3n);
    const r = sj.mul(sj.pow(6, R(1n, 6n)), sj.pow(10, third), sj.pow(7, R(1n, 2n)));
    expect(String(r)).toBe('sqrt(14)*3**(1/6)*5**(1/3)');
  });
  it('a common factor whose exponents add up to an integer', () => {
    expect(String(P('2**(1/3)*6**(2/3)'))).toBe('2*3**(2/3)');
    expect(String(P('2**(1/3)*6**(1/2)'))).toBe('2**(5/6)*sqrt(3)');
  });
});

describe('numeric radicals (SymPy Integer._eval_power, Mul.flatten)', () => {
  const cases: [string, string][] = [
    ['12**(2/3)', '2*18**(1/3)'],
    ['(12*x)**(2/3)', '2*18**(1/3)*x**(2/3)'],
    ['(12*x*y)**(2/3)', '2*18**(1/3)*(x*y)**(2/3)'],
    ['(24*x)**(1/3)', '2*3**(1/3)*x**(1/3)'],
    ['72**(1/3)', '2*3**(2/3)'],
    ['12**(5/6)', '2*2**(2/3)*3**(5/6)'],
    ['(1/12)**(2/3)', '12**(1/3)/12'],
    ['(-12)**(2/3)', '2*(-1)**(2/3)*18**(1/3)'],
    ['2**(-1/3)', '2**(2/3)/2'],
    ['(3/2)**(1/3)', '2**(2/3)*3**(1/3)/2'],
    ['(2/3)**(1/2)', 'sqrt(6)/3'],
    ['sqrt(8/9)', '2*sqrt(2)/3'],
    ['2**(1/3)*3**(2/3)', '2**(1/3)*3**(2/3)'],
    ['2**(2/3)*3**(2/3)', '6**(2/3)'],
    ['2**(1/3)*5**(2/3)*7**(1/3)', '14**(1/3)*5**(2/3)'],
    ['2**(3/4)*3**(1/4)', '2**(3/4)*3**(1/4)'],
    ['sqrt(6)*2**(1/3)', '2**(5/6)*sqrt(3)'],
    ['sqrt(2)*sqrt(6)', '2*sqrt(3)'],
    ['2**(1/3)*4**(1/3)', '2'],
    ['sqrt(12)*3**(1/3)', '2*3**(5/6)'],
    ['6**(1/2)*6**(1/3)', '6**(5/6)'],
    ['sqrt(2)*2**(1/3)', '2**(5/6)'],
    ['(12*(x + y))**(2/3)', '(12*x + 12*y)**(2/3)'],
  ];
  it.each(cases)('%s', (src, expected) => {
    expect(String(P2(src))).toBe(expected);
  });
});

describe('sympify', () => {
  it('rejects a value that is not a number', () => {
    expect(() => sympify('x' as unknown as number)).toThrow(SympifyError);
  });
});

describe('Float powers (SymPy Float._eval_power)', () => {
  it('evaluates a number raised to a Float', () => {
    // SymPy: Integer(2)**Float(0.5) = 1.41421356237310; Float(2)**Float(0.5) likewise
    expect(s(pow(2, 0.5))).toBe('1.41421356237310');
    expect(s(pow(new Float(2), 0.5))).toBe('1.41421356237310');
    // SymPy: S(0)**Float(0.5) = 0, S(0)**Float(-0.5) = zoo
    expect(s(pow(0, 0.5))).toBe('0');
    expect(pow(0, -0.5)).toBe(zoo);
    // SymPy: Float(0)**Float(0.5) = Float(0)**Rational(1, 2) = 0.0, Float(0)**Float(-0.5) = zoo
    expect(s(pow(new Float(0), 0.5))).toBe('0.0');
    expect(s(pow(new Float(0), R2(1, 2)))).toBe('0.0');
    expect(pow(new Float(0), -0.5)).toBe(zoo);
  });
  it('takes odd roots of a negative Float through (-1)**(1/q)', () => {
    // SymPy: Float(-8)**Rational(1, 3) = 2.0*(-1)**(1/3)
    expect(s(pow(new Float(-8), R2(1, 3)))).toBe('2.0*(-1)**(1/3)');
  });
  it('gives a complex value for other powers of a negative Float', () => {
    // SymPy: Float(-2)**Rational(2, 3) = -0.7937005259841 + 1.3747296369986*I
    const v = pow(new Float(-2), R2(2, 3)).toComplex();
    expect(v.re).toBeCloseTo(-0.7937005259841, 12);
    expect(v.im).toBeCloseTo(1.3747296369986, 12);
    // SymPy: Float(-2)**Float(0.5) = 1.4142135623731*I (real part below the precision)
    const w = pow(new Float(-2), 0.5).toComplex();
    expect(Math.abs(w.re)).toBeLessThan(1e-15);
    expect(w.im).toBeCloseTo(Math.SQRT2, 14);
  });
});

describe('sums with infinities', () => {
  it('keeps a constant that cannot be evaluated beside oo', () => {
    // SymPy: oo + f(1) = f(1) + oo
    const e = add(oo, f(1));
    expect(e).toBeInstanceOf(Add);
    expect(s(e)).toBe('f(1) + oo');
  });
  it('gives nan for zoo + oo', () => {
    expect(add(zoo, oo)).toBe(nan);
  });
  it('drops symbolic terms that cancel', () => {
    // SymPy: (x + oo) - x = oo
    expect(add(add(x, oo), mul(-1, x))).toBe(oo);
  });
});

describe('sums with Order terms', () => {
  it('measures a product with a sum factor by its lowest power', () => {
    // SymPy: x*(1 + x) + O(x**3) = x*(x + 1) + O(x**3); x**3*(1 + x) + O(x**2) = O(x**2)
    expect(s(add(mul(x, add(1, x)), sj.O(pow(x, 3))))).toBe('x*(x + 1) + O(x**3)');
    expect(s(add(mul(pow(x, 3), add(1, x)), sj.O(pow(x, 2))))).toBe('O(x**2)');
    // SymPy: x*(sin(x) + 1) + O(x**3) keeps the term
    expect(s(add(mul(x, add(sj.sin(x), 1)), sj.O(pow(x, 3))))).toBe('x*(sin(x) + 1) + O(x**3)');
  });
  it('keeps the weakest of several Orders', () => {
    // SymPy: O(x**2) + O(x) + O(x**3) = O(x); x**3 + O(x**2) = O(x**2)
    expect(s(add(sj.O(pow(x, 2)), sj.O(x), sj.O(pow(x, 3))))).toBe('O(x)');
    expect(s(add(sj.O(x), sj.O(pow(x, 3)), sj.O(pow(x, 2))))).toBe('O(x)');
    expect(s(add(pow(x, 3), sj.O(pow(x, 2))))).toBe('O(x**2)');
  });
  it('leaves Orders in different variables apart', () => {
    // SymPy: O(x) + O(y) = O(y) + O(x) (both kept)
    const e = add(sj.O(x), sj.O(y));
    expect(e).toBeInstanceOf(Add);
    expect(new Set(e.args.map(s))).toEqual(new Set(['O(x)', 'O(y)']));
  });
  it('absorbs into an Order with a symbolic exponent', () => {
    // SymPy: x + O(x**y) = O(1, x, y), absorbing x
    const e = add(x, sj.O(pow(x, y)));
    expect(e).toBeInstanceOf(Order);
  });
  it('recognizes powers of a shifted base', () => {
    const o = sj.O(pow(add(x, -1), 2), x, 1);
    // SymPy: (x - 1)**3 + O((x - 1)**2, (x, 1)) = O((x - 1)**2, (x, 1))
    expect(s(add(pow(add(x, -1), 3), o))).toBe('O((x - 1)**2, (x, 1))');
    // SymPy: (x - 1)**sqrt(2) + O((x - 1)**2, (x, 1)) keeps the term
    expect(add(pow(add(x, -1), sj.sqrt(2)), o).args.length).toBe(2);
  });
});

describe('AccumBounds in sums and products', () => {
  const ab = sj.AccumBounds(1, 2);
  it('absorbs the numeric term of a sum (SymPy x + AccumBounds(1, 2) + 1 = x + AccumBounds(2, 3))', () => {
    expect(s(add(add(x, ab), 1))).toBe('x + AccumBounds(2, 3)');
    expect(s(add(x, 1, ab))).toBe('x + AccumBounds(2, 3)');
    expect(s(add(x, ab))).toBe('x + AccumBounds(1, 2)');
  });
  it('keeps a symbolic factor beside the interval', () => {
    // SymPy: x*AccumBounds(1, 3)
    expect(s(mul(x, sj.AccumBounds(1, 3)))).toBe('x*AccumBounds(1, 3)');
  });
  it('raises a number to an interval', () => {
    // SymPy: Rational(1, 2)**AccumBounds(0, 1) = AccumBounds(1/2, 1); 2**AccumBounds(0, 1) = AccumBounds(1, 2)
    expect(s(pow(R2(1, 2), sj.AccumBounds(0, 1)))).toBe('AccumBounds(1/2, 1)');
    expect(s(pow(2, sj.AccumBounds(0, 1)))).toBe('AccumBounds(1, 2)');
  });
});

describe('products with infinities', () => {
  it('uses the sign of the remaining factor', () => {
    // SymPy: oo*n = -oo for negative n; oo*(-p) = -oo for positive p
    expect(mul(oo, n)).toBe(negOo);
    expect(mul(oo, mul(-1, p))).toBe(negOo);
  });
});

describe('products combining powers', () => {
  it('splits the result of combined exponentials', () => {
    // SymPy: exp(x + I*pi/4)*exp(x + I*pi/4) = I*exp(2*x)
    const e = sj.exp(add(x, mul(I, pi, R2(1, 4))));
    expect(s(mul(e, e))).toBe('I*exp(2*x)');
  });
});

describe('pow', () => {
  it('evaluates zero to a symbolic power of known sign', () => {
    // SymPy: 0**p = 0, 0**n = zoo
    expect(pow(0, p)).toBe(S.Zero);
    expect(pow(0, n)).toBe(zoo);
  });
  it('inverts a + b*I', () => {
    // SymPy: 1/(3/5 + 4*I/5) = 3/5 - 4*I/5; 1/(0.6 + 0.8*I) = 1.0*(0.6 - 0.8*I)
    expect(s(pow(add(R2(3, 5), mul(R2(4, 5), I)), -1))).toBe('3/5 - 4*I/5');
    expect(s(pow(add(0.6, mul(0.8, I)), -1))).toBe('1.0*(0.6 - 0.8*I)');
    // SymPy: 1/(2 + I) = (2 - I)/5
    expect(s(pow(add(2, I), -1))).toBe('(2 - I)/5');
    // SymPy: 1/(x + I) stays
    expect(s(pow(add(x, I), -1))).toBe('1/(x + I)');
  });
  it('keeps the power of an exponential whose exponent cannot be evaluated', () => {
    // SymPy: sqrt(exp(f(1))) stays
    expect(s(sj.sqrt(sj.exp(f(1))))).toBe('sqrt(exp(f(1)))');
  });
  it('rewrites exp of products and sums of logarithms', () => {
    // SymPy: exp(log(x)*log(y)) stays; exp(x + 2*log(exp(z))) = exp(x + 2*z)
    expect(s(sj.exp(mul(sj.log(x), sj.log(y))))).toBe('exp(log(x)*log(y))');
    expect(s(sj.exp(add(x, mul(2, sj.log(sj.exp(z))))))).toBe('exp(x + 2*z)');
  });
});

describe('powers with infinities and nan (SymPy Infinity/NegativeInfinity/ComplexInfinity._eval_power)', () => {
  it('propagates nan', () => {
    expect(pow(nan, 2)).toBe(nan);
    expect(pow(2, nan)).toBe(nan);
  });
  it('raises oo to a power', () => {
    expect(s(pow(oo, x))).toBe('oo**x');
    expect(pow(oo, p)).toBe(oo);
    expect(pow(oo, n)).toBe(S.Zero);
    expect(pow(oo, oo)).toBe(oo);
    expect(pow(oo, negOo)).toBe(S.Zero);
    expect(pow(oo, zoo)).toBe(nan);
    // a real exponent of unknown sign is decided numerically: oo**(pi - 3) = oo, oo**(3 - pi) = 0
    expect(pow(oo, add(pi, -3))).toBe(oo);
    expect(pow(oo, add(3, mul(-1, pi)))).toBe(S.Zero);
    // SymPy: oo**(-1 + sin(pi/7)**2 + cos(pi/7)**2) stays (the exponent is 0 numerically)
    const tiny = add(-1, pow(sj.sin(mul(pi, R2(1, 7))), 2), pow(sj.cos(mul(pi, R2(1, 7))), 2));
    expect(pow(oo, tiny)).toBeInstanceOf(Pow);
    // SymPy: oo**I = nan, oo**(1 + I) = zoo, oo**(-1 + I) = 0
    expect(pow(oo, I)).toBe(nan);
    expect(pow(oo, add(1, I))).toBe(zoo);
    expect(pow(oo, add(-1, I))).toBe(S.Zero);
  });
  it('raises zoo to a power', () => {
    // SymPy: zoo**zoo = nan, zoo**-oo = 0, zoo**2 = zoo, zoo**x stays
    expect(pow(zoo, zoo)).toBe(nan);
    expect(pow(zoo, negOo)).toBe(S.Zero);
    expect(pow(zoo, 2)).toBe(zoo);
    expect(s(pow(zoo, x))).toBe('zoo**x');
    // SymPy gives zoo**oo = 0; |zoo|**oo is infinite, so zoo**oo = zoo
    expect(pow(zoo, oo)).toBe(zoo);
  });
  it('raises -oo to a power', () => {
    // SymPy: (-oo)**oo = (-oo)**(-oo) = (-oo)**zoo = nan
    expect(pow(negOo, oo)).toBe(nan);
    expect(pow(negOo, negOo)).toBe(nan);
    expect(pow(negOo, zoo)).toBe(nan);
    // SymPy: (-oo)**3 = -oo, (-oo)**(-2) = 0
    expect(pow(negOo, 3)).toBe(negOo);
    expect(pow(negOo, -2)).toBe(S.Zero);
    // SymPy: (-oo)**(1/2) = oo*I, (-oo)**(2/3) = oo*(-1)**(2/3), (-oo)**(pi - 3) = oo*(-1)**(-3 + pi)
    expect(s(pow(negOo, R2(1, 2)))).toBe('oo*I');
    expect(s(pow(negOo, R2(2, 3)))).toBe('oo*(-1)**(2/3)');
    expect(s(pow(negOo, add(pi, -3)))).toBe('oo*(-1)**(-3 + pi)');
    // SymPy: (-oo)**(-1/2) = 0, (-oo)**I = nan, (-oo)**(1 - I) = zoo
    expect(pow(negOo, R2(-1, 2))).toBe(S.Zero);
    expect(pow(negOo, I)).toBe(nan);
    expect(pow(negOo, add(1, mul(-1, I)))).toBe(zoo);
    // SymPy: (-oo)**x and (-oo)**p stay; a negative symbolic exponent gives 0 ((-oo)**n -> 0)
    expect(s(pow(negOo, x))).toBe('(-oo)**x');
    expect(s(pow(negOo, p))).toBe('(-oo)**p');
    expect(pow(negOo, n)).toBe(S.Zero);
    // SymPy: (-oo)**Float(0.5) = oo*I; a Float exponent stays unevaluated here
    expect(pow(negOo, 0.5)).toBeInstanceOf(Pow);
  });
  it('raises a number to oo and -oo', () => {
    // SymPy: 0**oo = 0, 0**-oo = zoo, (1/2)**-oo = oo, (-1/2)**oo = 0, (-2)**oo = zoo, (-2)**-oo = 0
    expect(pow(0, oo)).toBe(S.Zero);
    expect(pow(0, negOo)).toBe(zoo);
    expect(pow(R2(1, 2), negOo)).toBe(oo);
    expect(pow(R2(-1, 2), oo)).toBe(S.Zero);
    expect(pow(-2, oo)).toBe(zoo);
    expect(pow(-2, negOo)).toBe(S.Zero);
    // SymPy gives (-1/2)**-oo = nan but (-2)**oo = zoo; both have modulus oo, so zoo here
    expect(pow(R2(-1, 2), negOo)).toBe(zoo);
    // SymPy: Float(0.5)**oo = 0
    expect(pow(0.5, oo)).toBe(S.Zero);
    // SymPy: (1 + I)**oo, (I/2)**oo and f(1)**oo stay
    expect(pow(add(1, I), oo)).toBeInstanceOf(Pow);
    expect(pow(mul(I, R2(1, 2)), oo)).toBeInstanceOf(Pow);
    expect(s(pow(f(1), oo))).toBe('f(1)**oo');
  });
});

describe('root, cbrt and realRoot (SymPy root, cbrt, real_root)', () => {
  it('takes principal and other roots', () => {
    expect(s(sj.root(8, 3))).toBe('2');
    expect(s(sj.root(x, 3, 1))).toBe('(-1)**(2/3)*x**(1/3)');
    expect(s(sj.root(-8, 3, 1))).toBe('-2');
    expect(s(sj.root(16, 4, 2))).toBe('-2');
    expect(s(sj.cbrt(27))).toBe('3');
    expect(s(sj.cbrt(x))).toBe('x**(1/3)');
  });
  it('takes the real root of a real number', () => {
    expect(s(sj.realRoot(-8, 3))).toBe('-2');
    expect(s(sj.realRoot(-8, -3))).toBe('-1/2');
    expect(s(sj.realRoot(r, 3))).toBe('Abs(r)**(1/3)*sign(r)');
    expect(s(sj.realRoot(r, -3))).toBe('sign(r)/Abs(r)**(1/3)');
    expect(s(sj.realRoot(r, 2))).toBe('sqrt(r)');
    expect(s(sj.realRoot(x, 1))).toBe('x');
    // SymPy: real_root(x, y) is a Piecewise in y; symjs gives the principal root
    expect(s(sj.realRoot(x, y))).toBe('x**(1/y)');
  });
  it('keeps the principal root when x is not known to be real', () => {
    // SymPy: real_root(x, 3) = Piecewise((Abs(x)**(1/3)*sign(x), Eq(im(x), 0)), (x**(1/3), True)); symjs gives x**(1/3)
    expect(s(sj.realRoot(x, 3))).toBe('x**(1/3)');
  });
});

describe('the exponential function', () => {
  it('is E raised to the argument', () => {
    expect(sj.exp(1)).toBe(E);
  });
});

describe('non-commutative printing matches SymPy', () => {
  it('exp(A)*exp(B) does not combine', () => {
    expect(mul(exp(A), exp(B)).toString()).toBe('exp(A)*exp(B)');
    expect(mul(pow(A, x), pow(A, new Sym('y'))).toString()).toBe('A**x*A**y');
    expect(mul(pow(A, 2), pow(A, 3)).toString()).toBe('A**5');
  });
});
