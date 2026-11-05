// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/sathandlers.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { allargs, anyarg, exactlyonearg } from '../../src/assumptions';

const { Q } = sj;
const [x, y] = sj.symbols('x y');

describe('facts about the arguments', () => {
  it('allargs, anyarg, exactlyonearg', () => {
    const xy = sj.mul(x!, y!);
    expect(String(allargs(x!, sj.Or(Q.negative(x!), Q.positive(x!)), xy))).toBe('(Q.negative(x) | Q.positive(x)) & (Q.negative(y) | Q.positive(y))');
    expect(String(anyarg(x!, sj.And(Q.negative(x!), Q.positive(x!)), xy))).toBe('(Q.negative(x) & Q.positive(x)) | (Q.negative(y) & Q.positive(y))');
    expect(String(exactlyonearg(x!, Q.positive(x!), xy))).toBe('(Q.positive(x) & ~Q.positive(y)) | (Q.positive(y) & ~Q.positive(x))');
  });
});

describe('the class fact registry', () => {
  it('doctest', async () => {
    const { ClassFactRegistry, classFactRegistry, isClassInstance } = await import('../../src/assumptions');
    const reg = new ClassFactRegistry();
    reg.register('Abs', (e) => Q.nonnegative(e));
    reg.register('Abs', (e) => sj.Equivalent(sj.not(Q.zero(e.args[0]!)), sj.not(Q.zero(e))));
    expect(reg.call(sj.abs(x!)).map(String)).toEqual(['Q.nonnegative(Abs(x))', 'Equivalent(~Q.zero(x), ~Q.zero(Abs(x)))']);
    const reg2 = new ClassFactRegistry();
    reg2.multiregister('Abs', (e) => [sj.Implies(Q.even(e.args[0]!), Q.even(e)), sj.Implies(Q.odd(e.args[0]!), Q.odd(e))]);
    expect(reg2.call(sj.abs(x!)).map(String)).toEqual(['Implies(Q.even(x), Q.even(Abs(x)))', 'Implies(Q.odd(x), Q.odd(Abs(x)))']);
    expect(reg2.handlers(x!)).toEqual([[], []]);
    expect(classFactRegistry.call(sj.pow(x!, y!)).length).toBe(4);
    expect(classFactRegistry.call(sj.mul(x!, y!)).length).toBe(11);
    expect(classFactRegistry.call(sj.S.NaN).length).toBe(0);
    const A = new sj.MatrixSymbol('A', 2, 2) as unknown as sj.Expr;
    const B = new sj.MatrixSymbol('B', 2, 2) as unknown as sj.Expr;
    const AB = (sj as unknown as { MatMul: (...a: sj.Expr[]) => sj.Expr }).MatMul(A, B);
    expect(isClassInstance(AB, 'MatMul')).toBe(true);
    expect(isClassInstance(AB, 'Mul')).toBe(true);
    expect(isClassInstance(sj.add(x!, 1), 'Add')).toBe(true);
    expect(isClassInstance(sj.sin(x!), 'sin')).toBe(true);
    expect(isClassInstance(sj.pi, 'NumberSymbol')).toBe(true);
    expect(classFactRegistry.call(AB).map(String)).toContain('Implies(Q.square(A) & Q.square(B), Equivalent(Q.invertible(A*B), Q.invertible(A) & Q.invertible(B)))');
  });
});
