import { describe, expect, it } from 'vitest';
import {
  E,
  I,
  Rational,
  add,
  cos,
  diff,
  exp,
  expand,
  log,
  mul,
  pi,
  pow,
  rational,
  sin,
  sqrt,
  symbol,
  symbols,
} from '../src';

const [x, y] = symbols('x y');
const theta = symbol('theta', { real: true });

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
    expect(add(x, 0.5).toString()).toBe('x + 0.500000000000000');
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

describe('functions', () => {
  it('evaluates special values', () => {
    expect(sin(pi).toString()).toBe('0');
    expect(cos(pi).toString()).toBe('-1');
    expect(sin(mul(rational(1, 4), pi)).toString()).toBe('sqrt(2)/2');
    expect(cos(mul(rational(1, 3), pi)).toString()).toBe('1/2');
    expect(sin(mul(rational(5, 6), pi)).toString()).toBe('1/2');
    expect(cos(mul(rational(7, 6), pi)).toString()).toBe('-sqrt(3)/2');
  });

  it('uses parity and shifts', () => {
    expect(sin(mul(-1, x)).toString()).toBe('-sin(x)');
    expect(cos(mul(-1, x)).toString()).toBe('cos(x)');
    expect(sin(add(x, pi)).toString()).toBe('-sin(x)');
    expect(cos(add(x, mul(rational(1, 2), pi))).toString()).toBe('-sin(x)');
    expect(sin(add(x, mul(2, pi))).toString()).toBe('sin(x)');
  });

  it('conjugates', () => {
    expect(exp(mul(I, theta)).conjugate().toString()).toBe('exp(-I*theta)');
    expect(add(1, mul(2, I)).conjugate().toString()).toBe('1 - 2*I');
    expect(x.conjugate().toString()).toBe('conjugate(x)');
    expect(cos(theta).conjugate().toString()).toBe('cos(theta)');
  });
});

describe('expand', () => {
  it('expands products and powers', () => {
    expect(expand(pow(add(x, 1), 2)).toString()).toBe('x**2 + 2*x + 1');
    expect(expand(mul(add(x, y), add(x, mul(-1, y)))).toString()).toBe('x**2 - y**2');
    expect(expand(pow(add(1, I), 2)).toString()).toBe('2*I');
  });
});

describe('diff', () => {
  it('differentiates', () => {
    expect(diff(pow(x, 3), x).toString()).toBe('3*x**2');
    expect(diff(sin(mul(2, x)), x).toString()).toBe('2*cos(2*x)');
    expect(diff(exp(mul(I, x)), x).toString()).toBe('I*exp(I*x)');
    expect(diff(mul(x, log(x)), x).toString()).toBe('log(x) + 1');
    expect(diff(pow(x, 4), x, 2).toString()).toBe('12*x**2');
    expect(diff(pow(2, x), x).toString()).toBe('2**x*log(2)');
  });
});

describe('numeric', () => {
  it('evaluates numerically', () => {
    expect(sqrt(2).toNumber()).toBeCloseTo(Math.SQRT2);
    const v = exp(mul(I, theta)).toComplex({ theta: Math.PI / 3 });
    expect(v.re).toBeCloseTo(0.5);
    expect(v.im).toBeCloseTo(Math.sqrt(3) / 2);
    expect(add(x, sqrt(2)).evalf().toString()).toBe('x + 1.41421356237310');
  });

  it('rational objects', () => {
    expect(Rational.of(6, -4).toString()).toBe('-3/2');
  });
});
