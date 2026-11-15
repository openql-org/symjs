import { describe, expect, it } from 'vitest';
import { symbols, rootsQuintic, Poly, parseExpr, symbol } from '../src';
import { equivalent } from './sympy-equivalent';

describe('mathematical equivalence checks', () => {
  it.each([
    ['x', 'y'], ['x-y', '0'], ['ab', 'cd'], ['x**2', 'y**2'],
    ['x+y', '2*x'], ['x*y', 'x**2'], ['[1,2]', '[2,1]'],
    ['(1,2)', '(2,1)'], ['Integral(x, x)', 'x**2/2'],
    ['()', '[1]'], ['{x: ()}', '{x: [1]}'],
  ])('rejects %s == %s', (a, b) => expect(equivalent(a, b)).toBe(false));
  it.each([
    ['x+x', '2*x'], ['(x+1)**2', 'x**2+2*x+1'],
    ['sin(x)**2+cos(x)**2', '1'], ['{1,2}', '{2,1}'],
    ['[x+x, 1]', '[2*x, 1]'], ['()', '[]'],
    ['{x: (), y: (1,)}', '{y: [1], x: []}'],
  ])('accepts %s == %s', (a, b) => expect(equivalent(a, b)).toBe(true));
  it('preserves independence with symbol assumptions', () => {
    for (const assumptions of [{ real: true }, { positive: true }, { negative: true }, { integer: true }, { integer: true, nonpositive: true }]) {
      expect(equivalent('x', 'y', symbols('x y', assumptions))).toBe(false);
    }
    expect(equivalent('Abs(x)', 'x', symbols('x', { positive: true }))).toBe(true);
    expect(equivalent('Abs(x)', 'x', symbols('x', { real: true }))).toBe(false);
  });
  it('allows unordered solution lists explicitly', () => {
    expect(equivalent('[1,2]', '[2,1]', [], { fn: 'solve' })).toBe(true);
    expect(equivalent('[1,1]', '[1,2]', [], { fn: 'solve' })).toBe(false);
  });
  it('compares algebraic roots with radical solutions and rejects different roots', () => {
    expect(equivalent('-sqrt(2)', 'CRootOf(x**2-2, 0)')).toBe(true);
    expect(equivalent('sqrt(2)', 'ComplexRootOf(x**2-2, 0)')).toBe(false);
    expect(equivalent('sqrt(2)', 'CRootOf(x**2-2, x)')).toBe(false);
    const polynomial = 'x**5-6*x**3-6*x**2+x-6';
    const roots = rootsQuintic(Poly.from(parseExpr(polynomial), [symbol('x')]));
    const expected = `[${Array.from({ length: 5 }, (_, i) => `CRootOf(${polynomial}, ${i})`).join(', ')}]`;
    expect(equivalent(`[${roots.join(', ')}]`, expected, [], { fn: 'solve' })).toBe(true);
    expect(equivalent(`[${Array.from({ length: 5 }, () => roots[0]).join(', ')}]`, expected, [], { fn: 'solve' })).toBe(false);
  });
});
