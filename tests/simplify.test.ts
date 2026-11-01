import { describe, expect, it } from 'vitest';
import {
  I,
  Poly,
  add,
  cancel,
  cos,
  exp,
  ex,
  factorPoly,
  latex,
  mul,
  parse,
  pow,
  rational,
  roots,
  simplify,
  sin,
  solve,
  sqrt,
  symbol,
  symbols,
  together,
  trigsimp,
} from '../src';

const [x, y] = symbols('x y');
const [a, b, theta] = symbols('a b theta', { real: true });

describe('simplify', () => {
  it('proves sin^2 + cos^2 = 1', () => {
    expect(simplify(add(pow(sin(x), 2), pow(cos(x), 2))).toString()).toBe('1');
    expect(simplify(add(pow(sin(mul(rational(1, 2), theta)), 2), pow(cos(mul(rational(1, 2), theta)), 2))).toString()).toBe('1');
  });

  it('collapses angle addition', () => {
    const e = add(mul(cos(a), cos(b)), mul(-1, sin(a), sin(b)));
    expect(simplify(e).toString()).toBe('cos(a + b)');
    const f = add(mul(sin(a), cos(b)), mul(cos(a), sin(b)));
    expect(simplify(f).toString()).toBe('sin(a + b)');
  });

  it('rewrites Euler form', () => {
    expect(simplify(add(cos(theta), mul(I, sin(theta)))).toString()).toBe('exp(I*theta)');
    expect(trigsimp(exp(mul(I, theta))).toString()).toBe('I*sin(theta) + cos(theta)');
  });

  it('keeps already simple expressions', () => {
    expect(simplify(pow(cos(x), 2)).toString()).toBe('cos(x)^2');
    expect(simplify(add(x, 1)).toString()).toBe('x + 1');
  });

  it('cancels rational functions', () => {
    const e = mul(add(pow(x, 2), -1), pow(add(x, -1), -1));
    expect(cancel(e).toString()).toBe('x + 1');
    expect(simplify(e).toString()).toBe('x + 1');
    expect(together(add(pow(x, -1), pow(y, -1))).toString()).toBe('(x + y)/(x*y)');
    // regression: denominators with non-rational exponents (found by fuzzing)
    const e2 = add(rational(1, 2), mul(2, exp(mul(-3, I))));
    expect(together(e2).toComplex().re).toBeCloseTo(e2.toComplex().re);
  });
});

describe('polynomials', () => {
  it('finds roots', () => {
    expect(roots(add(pow(x, 2), -1), x).map(String)).toEqual(['-1', '1']);
    expect(roots(add(pow(x, 2), -2), x).map(String)).toEqual(['-sqrt(2)', 'sqrt(2)']);
    expect(roots(add(pow(x, 2), 1), x).map(String)).toEqual(['-I', 'I']);
    expect(solve(add(pow(x, 3), mul(-6, pow(x, 2)), mul(11, x), -6), x).map(String)).toEqual(['1', '2', '3']);
    expect(solve(add(mul(a, pow(x, 2)), mul(-1, a)), x).map(String)).toEqual(['-1', '1']);
  });

  it('computes gcd and factors', () => {
    const p = Poly.fromExpr(add(pow(x, 2), -1), x)!;
    const q = Poly.fromExpr(add(pow(x, 2), mul(2, x), 1), x)!;
    expect(p.gcd(q).toExpr(x).toString()).toBe('x + 1');
    expect(factorPoly(add(pow(x, 3), mul(-1, x)), x).toString()).toBe('x*(x - 1)*(x + 1)');
  });
});

describe('parser', () => {
  it('parses expressions', () => {
    expect(parse('x^2 + 2*x + 1').toString()).toBe('x^2 + 2*x + 1');
    expect(parse('-x^2').toString()).toBe('-x^2');
    expect(parse('2^3^2').toString()).toBe('512');
    expect(parse('sqrt(8)/2').toString()).toBe('sqrt(2)');
    expect(parse('exp(I*pi)').toString()).toBe('-1');
    expect(parse('x ** 2').equals(pow(x, 2))).toBe(true);
    expect(() => parse('2x')).toThrow(/implicit multiplication/);
  });

  it('supports the ex template tag', () => {
    const t = symbol('t', { real: true });
    const e = ex`cos(${t}/2)^2 + sin(${t}/2)^2`;
    expect(simplify(e).toString()).toBe('1');
    expect(ex`${t} + t`.toString()).toBe('2*t');
  });
});

describe('latex', () => {
  it('prints LaTeX', () => {
    expect(latex(mul(rational(1, 2), sqrt(2)))).toBe('\\frac{\\sqrt{2}}{2}');
    expect(latex(exp(mul(I, theta)))).toBe('e^{i \\theta}');
    expect(latex(pow(sin(x), 2))).toBe('\\sin^{2}\\left(x\\right)');
    expect(latex(symbol('phi_1'))).toBe('\\phi_{1}');
  });
});
