// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { _linsolve, _linearEqToDict, _linEq2dict, sympyDictToDm, EmptySet, Eq, ExprMap, linsolve, parse, symbols, S, Mul, Rel } from '../../../src';
import { at } from '../../../src/core/guard';
const syms = symbols('x y z');
const [x, y, z] = [at(syms, 0), at(syms, 1), at(syms, 2)];
const show = (result: ReturnType<typeof _linsolve>) => result instanceof Map ? [...result].map(([k, v]) => [String(k), String(v)]) : String(result);

describe('sparse domain linear solving', () => {
  it('solves unique, underdetermined, zero and inconsistent systems', () => {
    expect(show(_linsolve([Eq(x.add(y), 1), Eq(x.sub(y), 2)], [x, y]))).toEqual([['x', '3/2'], ['y', '-1/2']]);
    expect(show(_linsolve([x.add(y)], [x, y, z]))).toEqual([['x', '-y'], ['y', 'y'], ['z', 'z']]);
    expect(show(_linsolve([x, y], [x, y]))).toEqual([['x', '0'], ['y', '0']]);
    expect(show(_linsolve([], [x]))).toEqual([['x', 'x']]);
    expect(_linsolve([x, x.add(1)], [x])).toBe(EmptySet);
    expect(show(_linsolve([], []))).toEqual([]);
    expect(_linsolve([1], [])).toBe(EmptySet);
    expect(linsolve([x.add(1)], [x]).toString()).toBe('-1');
    expect(linsolve([x, x.add(1)], [x])).toBe(EmptySet);
  });
  it('preserves sparse shape and combines equality sides after linearity checks', () => {
    const [coefficients, constants] = _linearEqToDict([Eq(x.add(y), x.add(z)), S.Zero, Eq(x, 2)], syms);
    expect([...at(coefficients, 0)].map(([s, c]) => [String(s), String(c)])).toEqual([['y', '1'], ['z', '-1']]);
    const matrix = sympyDictToDm(coefficients, constants, syms);
    expect(matrix.shape).toEqual([3, 4]);
    expect(matrix.data.size).toBe(2);
    expect(_linEq2dict(parse('2*(x+y+3)'), new Set([x, y]))[0].toString()).toBe('6');
    expect(_linEq2dict(new Mul([parse('a'), parse('b')]), new Set([x]))[0].toString()).toBe('a*b');
    expect(_linEq2dict(parse('x+x*y'), new Set([x]))[1].get(x)?.toString()).toBe('y + 1');
    expect(() => _linsolve([parse('x*y')], [x, y])).toThrow('cross-term');
    expect(() => _linsolve([parse('x**2')], [x])).toThrow('nonlinear term');
    expect(() => _linsolve([new Rel('Eq', parse('x**2+x'), parse('x**2'))], [x])).toThrow('nonlinear');
    expect(_linEq2dict(parse('a'), new Set([x]))[1]).toBeInstanceOf(ExprMap);
  });
  it('solves over rational functions, algebraic and floating coefficient fields', () => {
    expect(show(_linsolve([parse('a*x-y')], [x, y]))).toEqual([['x', 'y/a'], ['y', 'y']]);
    expect(show(_linsolve([parse('sqrt(2)*x-1')], [x]))).toEqual([['x', 'sqrt(2)/2']]);
    const real = _linsolve([parse('0.5*x+y-1.0'), parse('x-y')], [x, y]);
    expect(real instanceof Map).toBe(true);
    if (real instanceof Map) expect(Number(real.get(x)?.evalf().toString())).toBeCloseTo(2/3);
    const complex = _linsolve([parse('(1.0+I)*x-1')], [x]);
    if (!(complex instanceof Map)) throw new TypeError('expected a solution');
    expect(complex.get(x)?.toString()).toBe('0.5 - 0.5*I');
  });
});

it('solves a large sparse diagonal system and preserves exact zeros in floating systems', () => {
  const variables = symbols('v0:256');
  const equations = variables.map((s, i) => s.mul(i + 1).sub(1));
  const solution = _linsolve(equations, variables);
  if (!(solution instanceof Map)) throw new TypeError('expected a solution');
  variables.forEach((s, i) => expect(solution.get(s)?.mul(i + 1).equals(1)).toBe(true));
  expect(show(_linsolve([parse('y-x'), parse('y-0.0216*x')], [x, y]))).toEqual([['x', '0'], ['y', '0']]);
  expect(_linsolve([parse('2*I')], [x])).toBe(EmptySet);
});
