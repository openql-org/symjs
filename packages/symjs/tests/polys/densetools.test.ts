// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { runTestCase } from '../../../../compat/tests-harness';
import type { TestCase } from '../../../../compat/tests-harness';
import {
  DomainError, EX, Float, I, RR, MultivariatePolynomialError, mul, NotReversible, PythonMPQ, QQ, QQ_I, Sym, ZZ, ZZ_I, add, dmpAlgInject, dmpClearDenoms,
  dmpEval, dmpRevert, dmpShift, dmpToDict, dupClearDenoms, dupDiff, dupExtract, dupRealImag, dupRevert, dupSignVariations, pow, sqrt, str,
} from '../../src';
import type { Expr } from '../../src';
it('injects extension coefficients before the existing polynomial generators', () => {
  const K = QQ.algebraicField(sqrt(2));
  const [f, level, domain] = dmpAlgInject([K.convert(sqrt(2)), K.zero, K.one], 0, K);
  expect(level).toBe(1); expect(domain).toBe(QQ);
  expect([...dmpToDict(f, level)].map(([m, c]) => [m, String(c)])).toEqual([[[0, 0], '1'], [[1, 2], '1']]);
  expect(dmpAlgInject([], 0, K)[0]).toEqual([[]]);
  const [g] = dmpAlgInject([[K.new([1, 1]), K.new(2)]], 1, K);
  expect([...dmpToDict(g, 2)].length).toBe(3);
});
it('handles Gaussian integer and rational domains, including purely real coefficients', () => {
  for (const K of [ZZ_I, QQ_I]) {
    const [f, u, domain] = dmpAlgInject([K.new(2, 3), K.new(0, 1), K.new(4)], 0, K);
    expect(domain).toBe(K.dom);
    expect([...dmpToDict(f, u)].map(([m, c]) => [m, String(c)])).toEqual([[[0, 0], '4'], [[0, 2], '2'], [[1, 1], '1'], [[1, 2], '3']]);
  }
  expect(() => dmpAlgInject([1], 0, ZZ)).toThrow('only in an algebraic domain');
});

it('replays every measured SymPy densetools assertion', () => {
  const cases: TestCase[] = JSON.parse(readFileSync(new URL('../../../../compat/tests-corpus/polys.json', import.meta.url), 'utf8'));
  const failures = cases.filter((c) => c.module === 'sympy.polys.tests.test_densetools').flatMap((c) => {
    const o = runTestCase(c);
    return o.status === 'pass' || o.status === 'equivalent' ? [] : [{ src: c.src, fn: c.fn, ...o }];
  });
  expect(failures).toEqual([]);
});

it('validates levels and integer arguments', () => {
  expect(() => dmpEval([1, 2], 1, 1, ZZ)).toThrow(TypeError);
  expect(() => dupDiff([1], 0.5, ZZ)).toThrow(RangeError);
  expect(() => dmpRevert([[1]], 2, 1, QQ)).toThrow(MultivariatePolynomialError);
  expect(() => dupRevert([2n, 3n], 2, ZZ)).toThrow(NotReversible);
  expect(dupRevert([1n, -1n], 4, ZZ)).toEqual([-1n, -1n, -1n, -1n]);
});

it('extracts a unit content and shifts inner variables only', () => {
  expect(dupExtract([1, 2], [3], ZZ)).toEqual([1n, [1, 2], [3]]);
  expect(dmpShift([[1, 0], [2]], [0, 1], 1, ZZ)).toEqual([[1, 1n], [2]]);
  expect(dupRealImag([1, 0, 0], ZZ)).toEqual([[[1n], [], [-1n, 0n, 0n]], [[2n, 0n], []]]);
});

it('counts sign variations over real algebraic fields only', () => {
  const K = QQ.algebraicField(sqrt(2));
  expect(dupSignVariations([K.convert(sqrt(2)), K.zero, K.convert(-1)], K)).toBe(1);
  expect(() => dupSignVariations([], QQ.algebraicField(I))).toThrow(DomainError);
  expect(() => dupSignVariations([], EX)).toThrow(DomainError);
});

it('clears denominators over rings, fraction fields and expressions', () => {
  const x = new Sym('x');
  expect(dupClearDenoms([1, 2], ZZ)).toEqual([1n, [1, 2]]);
  expect(dupClearDenoms([new Float(1.5), 2], RR)[1]).toEqual([new Float(1.5), 2]);
  const F = QQ.fracField(x);
  const [common, g] = dupClearDenoms([F.convert(pow(x, -1)), F.convert(pow(add(x, 1), -1))], F);
  expect(str(common as Expr)).toBe('x**2 + x');
  expect(g.map((c) => str(c as Expr))).toEqual(['x + 1', 'x']);
  const [c2, h] = dmpClearDenoms([[new PythonMPQ(1n, 2n)], [new PythonMPQ(1n, 3n)]], 1, QQ, ZZ, true);
  expect(c2).toBe(6n);
  expect(h).toEqual([[3n], [2n]]);
  const [c3, k] = dupClearDenoms([QQ_I.new(1, 2), QQ_I.new(new PythonMPQ(1n, 3n), 1)], QQ_I);
  expect(String(c3)).toBe(String(ZZ_I.new(3)));
  expect(k.map(String)).toEqual([String(QQ_I.new(3, 6)), String(QQ_I.new(1, 3))]);
  expect(dmpShift([[1], [2]], [1, 0], 1, ZZ)).toEqual([[1], [3n]]);
});

it('takes the monic lcm of the denominators over a field of coefficients (SymPy K1.lcm)', () => {
  const x = new Sym('x');
  const R = RR.fracField(x);
  const [common, g] = dupClearDenoms([R.convert(mul(new Float(8.48717), pow(add(mul(new Float(8.0089), x), new Float(2.83)), -1))), R.convert(new Float(0))], R);
  expect(str(common as Expr)).toBe('1.0*x + 0.353356890459364');
  expect(g.map((c) => str(c as Expr))).toEqual(['1.05971731448763', '0']);
  const F = QQ.fracField(x);
  const [c2, h] = dupClearDenoms([F.convert(pow(add(mul(3, x), 1), -1)), F.convert(0)], F);
  expect(str(c2 as Expr)).toBe('x + 1/3');
  expect(h.map((c) => str(c as Expr))).toEqual(['1/3', '0']);
  const Z = ZZ.fracField(x);
  expect(str(dupClearDenoms([Z.convert(pow(add(mul(3, x), 1), -1))], Z)[0] as Expr)).toBe('3*x + 1');
  const E = EX.fracField(x);
  expect(str(dupClearDenoms([E.convert(pow(add(mul(3, x), 1), -1))], E)[0] as Expr)).toBe('3*x + 1');
});
