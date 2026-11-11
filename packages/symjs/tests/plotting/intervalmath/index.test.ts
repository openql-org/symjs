import { expect, it } from 'vitest';
import * as intervalmath from '../../../src/plotting/intervalmath/index';
it('exports the interval types and elementary functions from one namespace', () => { expect(intervalmath.sin(new intervalmath.interval(0)).start).toBe(0); expect(Object.keys(intervalmath)).toContain('intervalMembership'); });
it('corrects scalar cosine, sqrt(0), and even-numerator powers across zero in SymPy 1.14', () => { expect(intervalmath.cos(0).start).toBe(1); expect(intervalmath.sqrt(0).isValid).toBe(true); expect(new intervalmath.interval(-8, 64).pow(2 / 3).start).toBe(0); });
it('checks validity propagation and interval API boundaries', () => {
  const { interval: I, intervalMembership: M } = intervalmath;
  expect(() => new I(NaN)).toThrow(TypeError); expect(() => new I(1).pow(Infinity)).toThrow(RangeError);
  expect(new I(1, 2).toString()).toBe('[1.000000, 2.000000]'); expect(new I(2).pow(0).start).toBe(1); expect(new I(2).pow(-1).start).toBe(0.5);
  expect(() => new M('bad' as never, true)).toThrow(TypeError); expect(() => new M(true, 'bad' as never)).toThrow(TypeError); expect(new M(true, true).length).toBe(2); expect(new M('unknown', false).toString()).toBe('intervalMembership(None, False)');
  expect(intervalmath.ceil(new I(0, 1, { isValid: false })).isValid).toBe(false);
  expect(() => intervalmath.imin()).toThrow(RangeError);
  expect(intervalmath.imin(new I(0, 1, { isValid: false })).isValid).toBe(false);
  expect(intervalmath.imax(new I(0, 1, { isValid: 'unknown' })).isValid).toBe('unknown');
  expect(intervalmath.And(new M(true, true)).value).toBe(true);
});
