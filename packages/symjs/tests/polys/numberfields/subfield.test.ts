// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values from SymPy 1.14 polys.numberfields.subfield.
import { expect, it } from 'vitest';
import { symbols, sqrt, add, mul, S, AlgebraicNumber, fieldIsomorphism, primitiveElement, toNumberField, isNoMatch, expand } from '../../../src';
const [x] = symbols('x'), a = sqrt(2), b = sqrt(3), theta = add(a, b);
it('finds and exactly reconstructs embeddings into a radical power basis', () => {
  expect(String(fieldIsomorphism(a, theta))).toBe('1/2,0,-9/2,0');
  expect(String(fieldIsomorphism(b, theta))).toBe('-1/2,0,11/2,0');
  expect(String(fieldIsomorphism(add(1, a), a))).toBe('1,1');
  expect(String(fieldIsomorphism(S.I, add(a, S.I)))).toBe('1/6,0,1/6,0');
  expect(String(fieldIsomorphism(0, theta))).toBe('0');
  expect(String(fieldIsomorphism(new AlgebraicNumber(a), new AlgebraicNumber(a)))).toBe('1,0');
  expect(isNoMatch(fieldIsomorphism(a, b))).toBe(true);
  expect(() => fieldIsomorphism(x, a)).toThrow('over QQ');
  expect(() => fieldIsomorphism(S.Pi, a)).toThrow();
});
it('constructs primitive elements and representations of every generator', () => {
  const [p, coeffs, reps] = primitiveElement([a, b], x, { ex: true });
  expect(String(p)).toBe('x**4 - 10*x**2 + 1'); expect(coeffs).toEqual([1, 1]);
  expect(reps.map(String)).toEqual(['1/2,0,-9/2,0', '-1/2,0,11/2,0']);
  expect(primitiveElement([a, mul(-1, a)], x)[1]).toEqual([1, 0]);
  expect(primitiveElement([1, 2], x, { ex: true }).map(String)).toEqual(['x', '0,0', '1,2']);
  expect(() => primitiveElement([])).toThrow('At least');
});
it('embeds values into an explicit field without numerical approximations', () => {
  const result = toNumberField(a, theta);
  expect(String(result.coeffs())).toBe('1/2,0,-9/2,0');
  expect(expand(add(result.asExpr(), mul(-1, a))).equals(0)).toBe(true);
  expect(toNumberField([a, b]).root.equals(theta)).toBe(true);
  expect(toNumberField(2).asExpr().equals(2)).toBe(true);
  expect(() => toNumberField([])).toThrow('At least');
  expect(() => toNumberField(a, b)).toThrow('embedding');
});

it('bounds primitive-element search and retries a nonprimitive first candidate', () => {
  const first = add(a, b), second = add(mul(-1, a), sqrt(5));
  expect(() => primitiveElement([first, second], x, { maxCandidates: 1 })).toThrow('within 1 candidates');
  const [, coefficients] = primitiveElement([first, second], x, { maxCandidates: 2 });
  expect(coefficients).toEqual([1, 2]);
  expect(() => primitiveElement([a], x, { maxCandidates: 0 })).toThrow('positive integer');
});
