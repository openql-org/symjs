// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Matrix, S, Sym, Integral, add, mul, pow, diff, simplify, subs, linodesolve, NonSquareMatrixError } from '../../src';
import type { LinodesolveOptions } from '../../src';

const t = new Sym('t');
const check = (A: Matrix, opts: LinodesolveOptions = {}) => {
  const sol = linodesolve(A, t, opts);
  const rhs = A.mul(Matrix.col(...sol)).add(opts.b ?? Matrix.zeros(A.rows, 1));
  sol.forEach((e, i) => expect(simplify(add(diff(e, t), mul(-1, rhs.get(i, 0)))).equals(S.Zero)).toBe(true));
  return sol;
};

it('solves constant, variable and defective homogeneous systems', () => {
  expect(check(Matrix.of([[2]])).map(String)).toEqual(['C1*exp(2*t)']);
  check(Matrix.of([[1, 1, 0], [0, 1, 1], [0, 0, 1]]));
  check(Matrix.of([[t, 0], [0, mul(2, t)]]));
  check(Matrix.of([[t]]), { B: Matrix.of([[mul(S.Half, pow(t, 2))]]), type: 'type3' });
  check(Matrix.of([[0, 1], [-1, 0]]));
});

it('uses variation of parameters with evaluated or unevaluated forcing', () => {
  check(Matrix.of([[1]]), { b: Matrix.col(t), doit: true });
  check(Matrix.of([[t]]), { b: Matrix.col(t), type: 'type4', doit: true });
  expect(linodesolve(Matrix.of([[0]]), t, { b: Matrix.col(1) })[0]?.has(new Integral([S.One, t]))).toBe(true);
  check(Matrix.of([[0, 0], [0, 0]]), { b: Matrix.col(0, 1), doit: true });
  const A = Matrix.of([[2]]);
  expect(linodesolve(A, t, { tau: pow(t, 2) })).toEqual(linodesolve(A, t).map((e) => subs(e, [[t, pow(t, 2)]])));
  check(A, { type: 'type2' });
});

it('validates dimensions, argument types and commutativity', () => {
  const A = Matrix.eye(2);
  expect(() => linodesolve(S.One as unknown as Matrix, t)).toThrow(TypeError);
  expect(() => linodesolve(Matrix.col(1, 2), t)).toThrow(NonSquareMatrixError);
  expect(() => linodesolve(A, t, { b: S.One as unknown as Matrix })).toThrow(RangeError);
  expect(() => linodesolve(A, t, { b: Matrix.col(1) })).toThrow(RangeError);
  expect(() => linodesolve(A, t, { b: A })).toThrow(RangeError);
  expect(() => linodesolve(A, t, { B: S.One as unknown as Matrix })).toThrow(TypeError);
  expect(() => linodesolve(A, t, { B: Matrix.col(1, 2) })).toThrow(NonSquareMatrixError);
  expect(() => linodesolve(A, t, { B: Matrix.eye(3) })).toThrow(RangeError);
  expect(() => linodesolve(A, t, { type: 'invalid' as LinodesolveOptions['type'] })).toThrow(RangeError);
  const variable = Matrix.of([[t, 1], [0, 0]]);
  expect(() => linodesolve(variable, t)).toThrow('commute');
  expect(() => linodesolve(variable, t, { type: 'type3' })).toThrow('noncommuting');
});

it('keeps integration constants distinct from equation parameters', () => {
  const C1 = new Sym('C1'), C2 = new Sym('C2');
  const sol = check(Matrix.of([[C1]]), { b: Matrix.col(C2) });
  expect(sol[0]?.has(new Sym('C3'))).toBe(true);
  expect(sol[0]?.has(C1)).toBe(true);
});

it('keeps substitution parameters distinct from integration constants', () => {
  const C1 = new Sym('C1');
  expect(linodesolve(Matrix.of([[1]]), t, { tau: C1 }).map(String)).toEqual(['C2*exp(C1)']);
});
