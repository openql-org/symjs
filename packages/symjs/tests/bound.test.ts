import { describe, expect, it } from 'vitest';
import { Integral, Sum, Sym, freeSymbols, mul, subs } from '../src';

const x = new Sym('x');
const y = new Sym('y');

describe('bound variables', () => {
  const I = new Integral([mul(x, y), x, mul(0), y]);
  const S = Sum(mul(x, y), [x, 0, y]);

  it('are not free', () => {
    expect([...freeSymbols(I)].map(String)).toEqual(['y']);
    expect([...freeSymbols(S)].map(String)).toEqual(['y']);
    // the variable of an indefinite integral stays free (SymPy)
    expect([...freeSymbols(new Integral([mul(x, y), x]))].map(String).sort()).toEqual(['x', 'y']);
  });

  it('are not substituted', () => {
    expect(subs(I, [[x, 2]]).toString()).toBe('Integral(x*y, (x, 0, y))');
    expect(subs(S, [[x, 2]]).toString()).toBe('Sum(x*y, (x, 0, y))');
    expect(subs(I, [[y, 2]]).toString()).toBe('Integral(2*x, (x, 0, 2))');
    expect(subs(S, [[y, 2]]).toString()).toBe('Sum(2*x, (x, 0, 2))');
  });
});
