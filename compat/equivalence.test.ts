import { describe, expect, it } from 'vitest';
import { symbols } from '../packages/symjs/src';
import { equivalent } from './equivalence';

describe('mathematical equivalence checks', () => {
  it.each([
    ['x', 'y'], ['x-y', '0'], ['ab', 'cd'], ['x**2', 'y**2'],
    ['x+y', '2*x'], ['x*y', 'x**2'], ['[1,2]', '[2,1]'],
    ['(1,2)', '(2,1)'], ['Integral(x, x)', 'x**2/2'],
  ])('rejects %s == %s', (a, b) => expect(equivalent(a, b)).toBe(false));
  it.each([
    ['x+x', '2*x'], ['(x+1)**2', 'x**2+2*x+1'],
    ['sin(x)**2+cos(x)**2', '1'], ['{1,2}', '{2,1}'],
    ['[x+x, 1]', '[2*x, 1]'],
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
});
