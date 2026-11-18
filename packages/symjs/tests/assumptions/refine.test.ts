// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import * as s from '../../src';
const x = new s.Sym('x'), y = new s.Sym('y'), z = new s.Sym('z');
const { Q } = s;
it('refines powers, including the parity of separate exponent terms', () => {
  expect(s.refinePow(x)).toBe(s.NoMatch);
  expect(s.refinePow(x.pow(2))).toBe(s.NoMatch);
  expect(s.refinePow(s.pow(-1, x), Q.real(x))).toBe(s.NoMatch);
  expect(s.refinePow(s.pow(-1, x), Q.even(x))).toBe(s.S.One);
  expect(s.refinePow(s.pow(-1, x), Q.odd(x))).toBe(s.S.NegOne);
  for (const [e, a, out] of [
    [x.add(y), Q.even(x), '(-1)**y'],
    [s.add(x, y, z), s.And(Q.odd(x), Q.odd(z)), '(-1)**y'],
    [s.add(x, y, 2), Q.odd(x), '(-1)**(y + 1)'],
    [x.add(3), s.S.true, '(-1)**(x + 1)'],
  ] as const) expect(String(s.refinePow(s.pow(-1, e), a))).toBe(out);
  expect(s.refinePow(s.pow(-1, x.add(y)))).toBe(s.NoMatch);
  expect(String(s.refinePow(s.sqrt(x.pow(2)), Q.positive(x)))).toBe('x');
});
it('refines abs, arg, and real and imaginary parts', () => {
  expect(s.refineAbs(s.Abs(x))).toBe(s.NoMatch);
  expect(String(s.refineAbs(s.Abs(x), Q.positive(x)))).toBe('x');
  expect(String(s.refineAbs(s.Abs(x), Q.negative(x)))).toBe('-x');
  expect(s.refineArg(s.arg(x))).toBe(s.NoMatch);
  expect(s.refineArg(s.arg(x), Q.positive(x))).toBe(s.S.Zero);
  expect(s.refineArg(s.arg(x), Q.negative(x))).toBe(s.S.Pi);
  expect(s.refineRe(s.re(x), Q.real(x))).toBe(x);
  expect(s.refineRe(s.re(x), Q.imaginary(x))).toBe(s.S.Zero);
  expect(String(s.refineRe(s.re(x)))).toBe('re(x)');
  expect(s.refineIm(s.im(x), Q.real(x))).toBe(s.S.Zero);
  expect(String(s.refineIm(s.im(x), Q.imaginary(x)))).toBe('-I*x');
  expect(String(s.refineIm(s.im(x)))).toBe('im(x)');
});
it('selects atan2 quadrants, axes, and an undecidable result', () => {
  const e = s.atan2(y, x);
  for (const [a, out] of [
    [s.And(Q.real(y), Q.positive(x)), 'atan(y/x)'],
    [s.And(Q.negative(y), Q.negative(x)), 'atan(y/x) - pi'],
    [s.And(Q.positive(y), Q.negative(x)), 'atan(y/x) + pi'],
    [s.And(Q.zero(y), Q.negative(x)), 'pi'],
    [s.And(Q.positive(y), Q.zero(x)), 'pi/2'],
    [s.And(Q.negative(y), Q.zero(x)), '-pi/2'],
    [s.And(Q.zero(y), Q.zero(x)), 'nan'],
  ] as const) expect(String(s.refineAtan2(e, a))).toBe(out);
  for (const a of [true, Q.positive(x), Q.negative(x), Q.zero(x)]) expect(s.refineAtan2(e, a)).toBe(e);
});
it('refines signs on both axes', () => {
  const e = s.sign(x);
  expect(s.refineSign(e)).toBe(e);
  expect(s.refineSign(e, Q.zero(x))).toBe(s.S.Zero);
  expect(s.refineSign(e, Q.positive(x))).toBe(s.S.One);
  expect(s.refineSign(e, Q.negative(x))).toBe(s.S.NegOne);
  // Positive -I*x proves x is imaginary even without an intrinsic symbol assumption.
  expect(s.refineSign(e, Q.positive(s.mul(-1, s.S.I, x)))).toBe(s.S.I);
  const u = new s.Sym('u');
  expect(s.refineSign(s.sign(u), s.And(Q.imaginary(u), Q.positive(s.im(u))))).toBe(s.S.I);
  expect(String(s.refineSign(s.sign(u), s.And(Q.imaginary(u), Q.negative(s.im(u)))))).toBe('-I');
});
it('refines symmetric matrix entries without loading a matrix dependency into the handler', () => {
  const X = s.MatrixSymbol('X', 3, 3);
  expect(s.refineMatrixelement(x)).toBe(s.NoMatch);
  expect(s.refineMatrixelement(s.Basic(x))).toBe(s.NoMatch);
  expect(s.refineMatrixelement(s.MatrixElement(X, 1, 0))).toBe(s.NoMatch);
  for (const [i, j] of [[0, 1], [1, 0], [0, 0]]) {
    expect(String(s.refineMatrixelement(s.MatrixElement(X, i!, j!), Q.symmetric(X)))).toBe(i === j ? 'X[0, 0]' : 'X[0, 1]');
  }
});
it('refines unevaluated real and imaginary parts and preserves undecidable parts', () => {
  const assumptions = s.And(Q.real(x), Q.imaginary(y));
  expect(String(s.refine(new s.Fn('re', [s.add(x, y)]), assumptions))).toBe('x');
  expect(String(s.refine(new s.Fn('im', [s.add(x, y)]), assumptions))).toBe('-I*y');
  expect(String(s.refine(new s.Fn('re', [s.mul(x, y)]), assumptions))).toBe('0');
  expect(String(s.refine(new s.Fn('im', [s.mul(x, y)]), assumptions))).toBe('-I*x*y');
  expect(String(s.refine(new s.Fn('im', [s.mul(x, y)]), Q.imaginary(y)))).toBe('im(x*y)');
  expect(String(s.refine(new s.Fn('re', [x])))).toBe('re(x)');
  expect(String(s.refine(new s.Fn('im', [x])))).toBe('im(x)');
  expect(String(s.refine(s.arg(x)))).toBe('arg(x)');
  const matrix = s.MatrixSymbol('M', 2, 2);
  expect(String(s.refine(s.MatrixElement(matrix, 1, 0)))).toBe('M[1, 0]');
});
it('restricts nested parity identities to complete half-integer exponents', () => {
  const nested = s.pow(-1, x);
  for (const [coefficient, constant, extra] of [
    [s.S.Half, s.S.Half, y], [s.S.Half, s.Rational.of(1, 3), s.S.Zero],
    [s.Rational.of(3, 2), s.S.Half, s.S.Zero], [s.Rational.of(1, 3), s.S.Half, s.S.Zero],
  ]) {
    const e = s.pow(-1, s.add(s.mul(coefficient!, nested), constant!, extra!));
    expect(s.refine(e, Q.integer(x)).equals(e)).toBe(true);
  }
  const negativeHalf = s.pow(-1, s.add(s.mul(s.Rational.of(-1, 2), nested), s.S.Half));
  expect(String(s.refine(negativeHalf, Q.integer(x)))).toBe('(-1)**x');
  const unknownInteger = s.pow(-1, s.add(s.mul(s.S.Half, nested), s.S.Half));
  expect(s.refine(unknownInteger).equals(unknownInteger)).toBe(true);
  const unrelated = s.pow(-1, s.add(s.mul(x, y), s.S.Half));
  expect(s.refine(unrelated, Q.integer(x)).equals(unrelated)).toBe(true);
});
it('preserves the principal square root of an inverse across the negative real axis', () => {
  const root = new s.Pow(new s.Pow(x, s.S.NegOne), s.S.Half);
  expect(s.refine(root, Q.real(x))).toBe(root);
  expect(String(s.refine(root, Q.positive(x)))).toBe('1/sqrt(x)');
});
