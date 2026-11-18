// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { Add, Eq, Mul, S, Sym, parseExpr as P, pow } from '../../src';
import { ZZ } from '../../src/polys/domains';
import { dictFromExpr, parallelDictFromExpr } from '../../src/polys/polyutils';

const x = new Sym('x'), y = new Sym('y');
const result = (input: Parameters<typeof dictFromExpr>[0], options?: Parameters<typeof dictFromExpr>[1]) => {
  const [rep, gens] = dictFromExpr(input, options);
  return [[...rep].map(([m, c]) => [m, String(c)]), gens.map(String)];
};

describe('multinomial dictionaries', () => {
  it('discovers generators jointly and keeps constant terms', () => {
    const [polys, gens] = parallelDictFromExpr([P('x*y'), P('2*z'), 3]);
    expect(gens.map(String)).toEqual(['x', 'y', 'z']);
    expect(polys.map((p) => [...p].map(([m, c]) => [m, String(c)]))).toEqual([
      [[[1, 1, 0], '1']], [[[0, 0, 1], '2']], [[[0, 0, 0], '3']],
    ]);
    expect(result(P('x**3 + 1/x + sqrt(x)'))[1]).toEqual(['x', '1/x', 'sqrt(x)']);
    expect(result(0)).toEqual([[[[], '0']], []]);
    expect(parallelDictFromExpr([])).toEqual([[], []]);
  });
  it('uses explicit generators with symbolic coefficients and expands products', () => {
    expect(result(P('(x + 1)**2'), { gens: [x] })).toEqual([[[[2], '1'], [[1], '2'], [[0], '1']], ['x']]);
    expect(result(P('x + 2*y'), { gens: [x] })).toEqual([[[[1], '1'], [[0], '2*y']], ['x']]);
    expect(result(Eq(x, 1))).toEqual([[[[0], '-1'], [[1], '1']], ['x']]);
  });
  it('distinguishes algebraic, numeric and domain coefficients', () => {
    expect(result(P('3*sqrt(2)*pi*x*y'), { extension: true })).toEqual([[[[1, 1, 1], '3*sqrt(2)']], ['x', 'y', 'pi']]);
    expect(result(P('sqrt(2)'), { greedy: false })).toEqual([[[[], 'sqrt(2)']], []]);
    expect(result(P('I*x + 1.5'))).toEqual([[[[0], '1.50000000000000'], [[1], 'I']], ['x']]);
    expect(result(P('x*y'), { domain: ZZ.polyRing(x) })).toEqual([[[[1], 'x']], ['y']]);
    expect(result(P('x*y'), { domain: ZZ.polyRing(y) })).toEqual([[[[1], 'y']], ['x']]);
    expect(result(P('sqrt(2)'), { extension: null })[1]).toEqual(['sqrt(2)']);
  });
  it('combines repeated powers and coefficients without requiring expansion', () => {
    const square = pow(x, 2);
    expect(result(new Mul([x, square]), { expand: false })).toEqual([[[[3], '1']], ['x']]);
    expect(result(new Add([x, x]), { expand: false })).toEqual([[[[1], '2']], ['x']]);
  });
  it('rejects booleans, inequalities and noncommutative expressions', () => {
    expect(() => dictFromExpr(S.true)).toThrow('commutative polynomial');
    expect(() => dictFromExpr(P('x > 1'))).toThrow('commutative polynomial');
    const a = new Sym('a', { commutative: false });
    expect(() => parallelDictFromExpr([a])).toThrow('commutative polynomial');
  });
});
