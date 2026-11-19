// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { symbol, dupCauchyUpperBound, dupCauchyLowerBound, dupMignotteSepBoundSquared, ZZ, QQ, ZZ_I, Rational, DomainError, PolynomialError } from '../../src';
const x = symbol('x');
it('computes exact Cauchy and Mignotte bounds over ZZ and QQ', () => {
  expect(String(dupCauchyUpperBound([1,0,-2],QQ))).toBe('3');
  expect(String(dupCauchyUpperBound([-2,1,-4],ZZ))).toBe('3');
  expect(String(dupCauchyUpperBound([1,0,0],QQ))).toBe('0');
  expect(String(dupCauchyLowerBound([1,0,-2,0],QQ))).toBe('2/3');
  expect(String(dupMignotteSepBoundSquared([1,0,-2],QQ))).toBe('3/5');
  expect(String(dupMignotteSepBoundSquared([1,0,1],ZZ))).toBe('3/4');
  expect(String(dupMignotteSepBoundSquared([Rational.of(1,2),0,-1],QQ))).toBe('3/5');
  for (const f of [[],[1]]) {
    expect(() => dupCauchyUpperBound(f,QQ)).toThrow(PolynomialError);
    expect(() => dupCauchyLowerBound(f,QQ)).toThrow(PolynomialError);
    expect(() => dupMignotteSepBoundSquared(f,QQ)).toThrow(PolynomialError);
  }
  expect(() => dupCauchyLowerBound([1,0,0],QQ)).toThrow(PolynomialError);
  for (const bound of [dupCauchyUpperBound,dupCauchyLowerBound,dupMignotteSepBoundSquared]) expect(() => bound([1,0,1],ZZ_I)).toThrow(DomainError);
  expect(() => dupCauchyUpperBound([x,1],QQ)).toThrow('unexpected type');
  expect(() => dupMignotteSepBoundSquared([x,0,1],QQ)).toThrow('unexpected type');
});
