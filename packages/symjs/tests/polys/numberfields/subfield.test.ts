// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values from SymPy 1.14 polys.numberfields.subfield.
import { expect, it, vi } from 'vitest';
import { symbols, sqrt, add, mul, S, AlgebraicNumber, fieldIsomorphism, primitiveElement, toNumberField, isNoMatch, expand, CRootOf, Dummy, parseExpr } from '../../../src';
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

it('maps a into Q(b) through a root of its minimal polynomial when expansions do not determine it', () => {
  const X = new Dummy('X');
  const root = (f: string, i: number): AlgebraicNumber => new AlgebraicNumber(CRootOf(parseExpr(f).subs(parseExpr('x'), X), i));
  expect(String(fieldIsomorphism(root('x**2 - 2', 1), root('x**2 - 6*x + 7', 1)))).toBe('1,-3');
  expect(isNoMatch(fieldIsomorphism(root('x**3 - 2', 0), root('x**3 - 6*x**2 + 12*x - 10', 1)))).toBe(true);
  expect(isNoMatch(fieldIsomorphism(parseExpr('2**(1/3)'), parseExpr('2**(1/3)*(-1 + sqrt(3)*I)/2')))).toBe(true);
  expect(String(fieldIsomorphism(root('x**2 - 2', 1), root('x**4 - 10*x**2 + 1', 3)))).toMatch(/^-?1\/2,0,-?9\/2,0$/);
  expect(isNoMatch(fieldIsomorphism(root('x**4 + 1', 3), root('x**4 + 4*x**2 + 2', 1)))).toBe(true);
  expect(isNoMatch(fieldIsomorphism(root('x**3 - 2', 0), root('x**2 - 2', 1)))).toBe(true);
  expect(String(fieldIsomorphism(root('x**2 - 2', 1), root('x**2 - 8', 1)))).toMatch(/^-?1\/2,0$/);
});

it('preserves the selected embedding of general RootOf generators',()=>{
  const r=CRootOf(parseExpr('x**3-x-1'),0),shift=CRootOf(parseExpr('x**3-6*x**2+11*x-7'),0);
  expect(String(fieldIsomorphism(r,shift))).toBe('1,-2');
  expect(String(toNumberField(r,shift).coeffs())).toBe('1,-2');
  const field=new AlgebraicNumber(r);
  expect(String(toNumberField(mul(r,r,r),field).coeffs())).toBe('1,1');
  expect(primitiveElement([add(a,b),add(mul(-1,a),sqrt(5))],x)[1]).toEqual([1,2]);
});

import * as enclosureModule from '../../../src/polys/numberfields/interval';
it('refines unresolved embedding enclosures and preserves evaluation errors',()=>{
  const r=CRootOf(parseExpr('x**3-x-1'),0),s=CRootOf(parseExpr('x**3-6*x**2+11*x-7'),0),spy=vi.spyOn(enclosureModule,'algebraicEnclosure');
  try {
    spy.mockImplementationOnce(()=>{throw new RangeError('precision insufficient');});
    expect(String(fieldIsomorphism(r,s))).toBe('1,-2');
    spy.mockImplementationOnce(()=>{throw new TypeError('invalid algebraic interval');});
    expect(()=>fieldIsomorphism(r,s)).toThrow(TypeError);
  } finally {spy.mockRestore();}
});
it('resolves an embedding whose root-separation bound requires higher precision',()=>{
  const a=CRootOf(parseExpr('x**3-x-1'),0),b=CRootOf(parseExpr('x**3-3000*x**2+2999999*x-999999001'),0);
  expect(String(fieldIsomorphism(a,b))).toBe('1,-1000');
});
