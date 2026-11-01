// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Wild, add, countOps, cos, find, log, match, mul, pow, replace, sin, str, symbols, tan } from '../src';

const [x, y, z] = symbols('x y z');
const fmt = (m: Map<unknown, unknown> | undefined) =>
  m === undefined
    ? 'None'
    : `{${[...m]
        .map(([k, v]) => `${str(k as never)}: ${str(v as never)}`)
        .sort()
        .join(', ')}}`;

describe('match (SymPy Basic.match)', () => {
  const a = new Wild('a');
  const b = new Wild('b', { exclude: [x] });
  const p = new Wild('p');
  const q = new Wild('q');
  const r = new Wild('r');
  it('matches products and powers', () => {
    expect(fmt(match(mul(3, pow(x, 2)), mul(a, x)))).toBe('{a_: 3*x}');
    expect(fmt(match(mul(3, pow(x, 2)), mul(b, x)))).toBe('None');
    expect(fmt(match(mul(4, pow(x, 2)), mul(p, pow(q, r))))).toBe('{p_: 4, q_: x, r_: 2}');
    expect(fmt(match(pow(add(x, y), add(x, y)), pow(p, p)))).toBe('{p_: x + y}');
  });
  it('matches sums', () => {
    expect(fmt(match(add(2, mul(3, y)), add(mul(a, x), mul(b, y))))).toBe('{a_: 2/x, b_: 3}');
  });
});

describe('replace / find / count_ops', () => {
  const a = new Wild('a');
  const f = add(log(sin(x)), tan(sin(pow(x, 2))));
  it('replaces functions and patterns', () => {
    expect(str(replace(f, { fn: 'sin' }, { fn: 'cos' }, { apply: (_n, args) => cos(args[0]!) }) as never)).toBe('log(cos(x)) + tan(cos(x**2))');
    expect(str(replace(f, sin(a), tan(a)) as never)).toBe('log(tan(x)) + tan(tan(x**2))');
    expect(str(replace(f, sin(a), a) as never)).toBe('log(x) + tan(x**2)');
    expect(str(replace(mul(x, y), mul(a, x), a) as never)).toBe('y');
  });
  it('finds and counts', () => {
    expect(find(f, { fn: 'sin' }).map(str).sort()).toEqual(['sin(x)', 'sin(x**2)']);
    expect(countOps(add(x, mul(2, y), sin(z)))).toBe(4);
  });
});

describe('rewrite', () => {
  it('rewrites trigonometric functions like SymPy', async () => {
    const { rewrite, sin, cos, tan, mul, add, I, str, symbols: syms } = await import('../src');
    const [t] = syms('t');
    expect(str(rewrite(add(cos(t!), mul(I, sin(t!))), 'exp'))).toBe('exp(I*t)');
    expect(str(rewrite(tan(t!), 'sin'))).toBe('2*sin(t)**2/sin(2*t)');
    expect(str(rewrite(sin(t!), 'cos'))).toBe('cos(t - pi/2)');
  });
});
