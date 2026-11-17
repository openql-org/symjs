// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import * as sj from '../../src';
import { Fn, headName } from '../../src/core/nodes';

it('returns callable public inverse heads for elementary and error functions', () => {
  const x = sj.symbol('x');
  expect(() => sj.inverse(x.pow(2))).toThrow(TypeError);
  const pairs = {
    exp: 'log', log: 'exp', conjugate: 'conjugate',
    sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot',
    asin: 'sin', acos: 'cos', atan: 'tan', acot: 'cot',
    sinh: 'asinh', tanh: 'atanh', coth: 'acoth',
    asinh: 'sinh', acosh: 'cosh', atanh: 'tanh', acoth: 'coth',
    asech: 'sech', acsch: 'csch',
    erf: 'erfinv', erfc: 'erfcinv', erfinv: 'erf', erfcinv: 'erfc',
  } as const;
  for (const [name, target] of Object.entries(pairs)) {
    const inverse = sj.inverse(sj.parse(`${name}(x)`));
    expect(headName(inverse)).toBe(target);
    expect(String(inverse(x))).toBe(`${target}(x)`);
  }
});

it('rejects nonfunctions, invalid argument indices and unavailable inverse heads', () => {
  expect(() => sj.inverse(1)).toThrow(TypeError);
  const x = sj.symbol('x');
  expect(() => sj.inverse(sj.exp(x), 2)).toThrow(RangeError);
  expect(() => sj.inverse(sj.exp(x), 1.5)).toThrow(RangeError);
  expect(() => sj.inverse(new Fn('gamma', [x]))).toThrow(sj.NotImplementedError);
});
