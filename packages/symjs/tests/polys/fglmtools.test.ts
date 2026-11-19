// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { groebner, matrixFglm, PolyRing, QQ, GF, ZZ, symbols, parse, grevlex, lex } from '../../src';
import { at } from '../../src/core/guard';

const [x, y, z] = symbols('x y z');
describe('matrix FGLM', () => {
  it('converts quotient-space multiplication matrices in every global order', () => {
    const gens = [x!, y!, z!];
    for (const input of [
      ['x**2-y', 'y**2-z', 'z**2-1'],
      ['x**2-x-3*y+1', 'y**2+y-2*x-1', 'z'],
      ['x**2', 'x*y', 'y**2', 'z'],
      ['x-y', 'y-z', 'z-1'],
    ]) {
      for (const from of ['lex', 'grlex', 'grevlex'] as const) {
        const G = groebner(input.map((s) => parse(s)), gens, from);
        const R = new PolyRing(gens, QQ, from);
        for (const to of ['lex', 'grlex', 'grevlex'] as const) {
          const result = matrixFglm(G.exprs.map((e) => R.fromExpr(e).monic()), R, to);
          const expected = groebner(input.map((s) => parse(s)), gens, to);
          expect(result.map((p) => p.asExpr().key)).toEqual(expected.exprs.map((e) => R.clone({ order: to }).fromExpr(e).monic().asExpr().key));
        }
      }
    }
  });
  it('handles finite fields, the unit ideal and rings without generators', () => {
    const R = new PolyRing('x,y', GF(5), grevlex);
    const result = matrixFglm([R.fromExpr(parse('y**2-x')), R.fromExpr(parse('x**2-y'))], R, lex);
    expect(result.map((p) => p.asExpr().key)).toEqual(['x-y**2', 'y**4-y'].map((e) => R.clone({ order: lex }).fromExpr(parse(e)).asExpr().key));
    // SymPy 1.14 returns the variable ideal here; the unit ideal has reduced Groebner basis [1].
    expect(matrixFglm([R.zero, R.one], R, lex)[0]?.equals(R.clone({ order: lex }).one)).toBe(true);
    expect(matrixFglm([], new PolyRing([], QQ), lex)).toEqual([]);
  });
  it('rejects positive-dimensional ideals, coefficient rings and local orders', () => {
    const R = new PolyRing('x,y', QQ);
    expect(() => matrixFglm([], R, 'lex')).toThrow('zero-dimensional');
    expect(() => matrixFglm([R.fromExpr(parse('x*y'))], R, 'lex')).toThrow('zero-dimensional');
    expect(() => matrixFglm([], new PolyRing('x', ZZ), 'lex')).toThrow('coefficient field');
    expect(() => matrixFglm([], new PolyRing('x', QQ, 'ilex'), 'lex')).toThrow('global');
    expect(() => matrixFglm([at(R.gens, 0)], R, 'ilex')).toThrow('global');
  });
});

it('rejects mixed product orders in FGLM', async () => {
  const { ProductOrder, ilex } = await import('../../src');
  const order = new ProductOrder([lex, [0]], [ilex, [1]]);
  expect(() => matrixFglm([], new PolyRing('x y', QQ, order), 'lex')).toThrow('global');
});
