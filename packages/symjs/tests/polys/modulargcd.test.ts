// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { passingModuleCases, runTestCase } from '../../../../tools/sympy-corpus/tests-harness';
import { PolyRing } from '../../src/polys/rings';
import { modgcdUnivariate, modgcdBivariate, modgcdMultivariate, funcFieldModgcd } from '../../src/polys/modulargcd';
import { QQ, ZZ } from '../../src/polys/domains';
import { AlgebraicField } from '../../src/polys/domains/algebraicfield';
import { parse } from '../../src/parsing/parser';
import { DomainError } from '../../src/core/errors';
import { first, pair } from '../../src/core/guard';

for (const c of passingModuleCases('polys', 'sympy.polys.tests.test_modulargcd')) {
  it(`${c.test}:${c.line}`, () => {
    const o = runTestCase(c);
    expect(o, c.src).toEqual({ status: 'pass' });
  });
}

it('skips bad primes, replaces unlucky bounds, and rejects false reconstructions', () => {
  const R = new PolyRing('x', ZZ);
  const x = first(R.gens);
  for (const [h, a, b] of [
    [x.mulGround(65537).add(1), x.add(2), x.add(3)],
    [x.add(2), x.add(1), x.add(65538)],
    [x.add(2), x.add(1), x.add(65540)],
    [x.add(65537n * 65539n), x.add(1), x.add(2)],
    [x.sub(65537n * 65539n), x.add(1), x.add(2)],
  ] as const) {
    const [g, p, q] = modgcdUnivariate(h.mul(a), h.mul(b));
    expect(g.equals(h)).toBe(true);
    expect(p.equals(a)).toBe(true);
    expect(q.equals(b)).toBe(true);
  }
});

it('normalizes zero inputs and rejects incompatible coefficient rings', () => {
  const R = new PolyRing('x,y', ZZ);
  const x = first(R.gens);
  for (const fn of [modgcdBivariate, modgcdMultivariate]) {
    expect(fn(R.zero, x.neg()).map(String)).toEqual(['x', '0', '-1']);
    expect(fn(x.neg(), R.zero).map(String)).toEqual(['x', '-1', '0']);
    expect(() => fn(x, new PolyRing('z', ZZ).one)).toThrow(DomainError);
    expect(() => fn(new PolyRing('x', QQ).one, new PolyRing('x', QQ).one)).toThrow(DomainError);
  }
  expect(() => funcFieldModgcd(x, x)).toThrow(DomainError);
  const K = new AlgebraicField(QQ, parse('sqrt(2)'));
  const A = new PolyRing('x,y', K);
  const y = A.gens[1]!;
  const f = y.add(parse('sqrt(2)'));
  expect(funcFieldModgcd(A.zero, A.zero).map((p) => p.isZero)).toEqual([true, true, true]);
  expect(funcFieldModgcd(A.zero, f.mulGround(2)).map((p) => String(p.asExpr()))).toEqual(['y + sqrt(2)', '0', '2']);
  expect(funcFieldModgcd(f.mulGround(2), A.zero).map((p) => String(p.asExpr()))).toEqual(['y + sqrt(2)', '2', '0']);
});

it('falls back to modular reconstruction when the certificate prime drops a leading term', () => {
  const R = new PolyRing('x y', ZZ);
  const [x, y] = pair(R.gens);
  const a = x.mulGround(65537).add(y), b = x.add(y).add(1);
  const h = x.add(y.mulGround(2));
  const result = modgcdMultivariate(h.mul(a), h.mul(b));
  expect(result.map(String)).toEqual([h, a, b].map(String));
});
