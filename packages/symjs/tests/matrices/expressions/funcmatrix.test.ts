// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/funcmatrix.ts.
//
// FunctionMatrix. Expected values are SymPy 1.14 results (explicit matrices printed on one line).

import { describe, expect, it } from 'vitest';
import { type Expr, KroneckerDelta, Lambda, latex, sstr, symbol, symbols, SymFunction as UFunction } from '../../../src';
import { DFT, FunctionMatrix, IDFT, Inverse, MatPow, type MatrixExpr, trace } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [n, i, j] = symbols('n i j k', { integer: true });

describe('fourier', () => {
  it('DFT and IDFT', () => {
    const n = symbol('n');
    expect(s(DFT(3))).toBe('DFT(3)');
    expect(String(DFT(3).asExplicit())).toBe(
      'Matrix([[sqrt(3)/3, sqrt(3)/3, sqrt(3)/3], [sqrt(3)/3, sqrt(3)*exp(-2*I*pi/3)/3, sqrt(3)*exp(2*I*pi/3)/3], [sqrt(3)/3, sqrt(3)*exp(2*I*pi/3)/3, sqrt(3)*exp(-2*I*pi/3)/3]])',
    );
    expect(DFT(n).shape.map(s)).toEqual(['n', 'n']);
    expect(s(IDFT(3))).toBe('IDFT(3)');
    expect(s(IDFT(4).mul(DFT(4)))).toBe('I');
    expect(String(DFT(2).asExplicit())).toBe('Matrix([[sqrt(2)/2, sqrt(2)/2], [sqrt(2)/2, -sqrt(2)/2]])');
    expect(s(DFT(n).I)).toBe('IDFT(n)');
    expect(L(IDFT(3))).toBe('\\text{IDFT}_{3}');
    expect(s(DFT(4).at(3, 3))).toBe('-I/2');
  });
});

describe('funcmatrix', () => {
  const [i, j, n, m] = symbols('i j n m');
  it('FunctionMatrix', () => {
    expect(s(FunctionMatrix(n, m, Lambda([i, j], i.add(j))))).toBe('FunctionMatrix(n, m, Lambda((i, j), i + j))');
    const X = FunctionMatrix(3, 3, (a, b) => KroneckerDelta(a, b));
    expect(String(X.asExplicit())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    const f = UFunction('f');
    const Xf = FunctionMatrix(3, 3, (a, b) => f(a, b));
    expect(String(Xf.asExplicit())).toBe('Matrix([[f(0, 0), f(0, 1), f(0, 2)], [f(1, 0), f(1, 1), f(1, 2)], [f(2, 0), f(2, 1), f(2, 2)]])');
    expect(s(Xf)).toBe('FunctionMatrix(3, 3, Lambda((_i, _j), f(_i, _j)))');
    expect(s(FunctionMatrix(n, m, 'lambda i, j: i + j'))).toBe('FunctionMatrix(n, m, Lambda((i, j), i + j))');
    const Y = FunctionMatrix(1000, 1000, Lambda([i, j], i.add(j)));
    expect(Y.mul(Y)).toBeInstanceOf(MatPow);
    expect(s(M(Y.pow(2)).at(10, 10))).toBe('342923500');
  });
  it('trace and entries', () => {
    expect(s(trace(FunctionMatrix(3, 3, Lambda([i, j], i.add(j)))))).toBe('6');
    expect(s(trace(FunctionMatrix(n, n, Lambda([i, j], i.mul(j)))))).toBe('n**3/3 - n**2/2 + n/6');
    expect(s(FunctionMatrix(2, 2, Lambda([i, j], i.add(j))).at(1, 1))).toBe('2');
    expect(s(FunctionMatrix(n, n, Lambda([i, j], i.mul(j))).T)).toBe('FunctionMatrix(n, n, Lambda((i, j), i*j)).T');
  });
});

describe('more SymPy cases', () => {
  const [n] = symbols('n m k');
  it('DFT LaTeX', () => {
    expect(L(DFT(n))).toBe('\\text{DFT}_{n}');
  });
});

describe('FunctionMatrix and DFT', () => {
  it('FunctionMatrix', () => {
    expect(() => FunctionMatrix(2, 2, Lambda([i], i))).toThrow('should be able to accept 2 arguments.');
    expect(() => FunctionMatrix(2, 2, 'foo')).toThrow('foo should be compatible with SymPy function classes.');
    expect(s(FunctionMatrix(n, 2, Lambda([i, j], i.add(j))).subs(n, 3))).toBe('FunctionMatrix(3, 2, Lambda((i, j), i + j))');
  });
  it('DFT and IDFT', () => {
    expect(s(DFT(n).at(i, j))).toBe('exp(-2*I*pi*i*j/n)/sqrt(n)');
    expect(s(DFT(n).subs(n, 3))).toBe('DFT(3)');
    expect(s(IDFT(n).subs(n, 3))).toBe('IDFT(3)');
    expect(s(IDFT(3).at(1, 2))).toBe('sqrt(3)*exp(-2*I*pi/3)/3');
    expect(s(IDFT(n).I)).toBe('DFT(n)');
    expect(s(M(Inverse(IDFT(n))).doit())).toBe('DFT(n)');
  });
});

describe('remaining branches (SymPy 1.14)', () => {
  it('DFT entries with non-integer indices', () => {
    const [a, b] = symbols('a b');
    expect(s(DFT(n).at(a, b))).toBe('exp(-2*I*pi/n)**(a*b)/sqrt(n)');
  });
});
