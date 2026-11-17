// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Relational, Rel, isEq, isNeq, isGe, isLe, isGt, isLt, Q, Sym, S, reversed, reversedSign, negated } from '../../src';
const x = new Sym('x');
it('constructs all relational operators and validates their names', () => {
  expect(String(Relational(x, 1))).toBe('Eq(x, 1)');
  for (const [op, aliases] of [['Eq', ['==', 'eq']], ['Ne', ['!=', '<>', 'ne']], ['Gt', ['>', 'gt']], ['Lt', ['<', 'lt']], ['Ge', ['>=', 'ge']], ['Le', ['<=', 'le']]] as const) {
    for (const alias of aliases) expect(Relational(x, 1, alias).kind).toBe('Rel');
    expect(Relational(1, 1, aliases[0])).toBe(['Eq', 'Ge', 'Le'].includes(op) ? S.true : S.false);
  }
  expect(() => Relational(x, 1, 'bad')).toThrow(RangeError);
  expect(String(Relational(1, x, '<'))).toBe('1 < x');
});
it('preserves relation structure when transforming every comparison', () => {
  const y = new Sym('y');
  for (const [op, reversedOp, negatedOp] of [
    ['Eq', 'Eq', 'Ne'], ['Ne', 'Ne', 'Eq'], ['Lt', 'Gt', 'Ge'],
    ['Le', 'Ge', 'Gt'], ['Gt', 'Lt', 'Le'], ['Ge', 'Le', 'Lt'],
  ] as const) {
    const relation = new Rel(op, x, y);
    expect(reversed(relation).key).toBe(new Rel(reversedOp, y, x).key);
    expect(reversedSign(relation).key).toBe(new Rel(reversedOp, x.neg(), y.neg()).key);
    expect(negated(relation).key).toBe(new Rel(negatedOp, x, y).key);
    expect(reversed(reversed(relation)).key).toBe(relation.key);
    expect(negated(negated(relation)).key).toBe(relation.key);
    const numeric = new Rel(op, S.One, S.One);
    expect(reversed(numeric)).toBeInstanceOf(Rel);
    expect(reversedSign(numeric)).toBeInstanceOf(Rel);
    expect(negated(numeric)).toBeInstanceOf(Rel);
  }
  for (const [lhs, rhs] of [[S.true, x], [x, S.false], [S.true, S.false]] as const) {
    const relation = new Rel('Eq', lhs, rhs);
    expect(reversedSign(relation)).toBe(relation);
  }
  expect(Relational(1, 1, '==', { evaluate: false }).key).toBe(new Rel('Eq', S.One, S.One).key);
  expect(Relational(1, 1, '==', { evaluate: true })).toBe(S.true);
});
it('compares values using three-valued logic and explicit assumptions', () => {
  expect(isEq(0, 0)).toBe(true); expect(isEq(0, 2)).toBe(false);
  expect(isNeq(0, 0)).toBe(false); expect(isNeq(0, 2)).toBe(true);
  expect(isEq(x, 0)).toBe('unknown'); expect(isNeq(x, 0)).toBe('unknown');
  expect(isEq(x, 0, Q.zero(x))).toBe(true);
  expect(isGe(2, 0)).toBe(true); expect(isGe(0, 2)).toBe(false);
  expect(isLe(0, 2)).toBe(true); expect(isGt(0, 2)).toBe(false); expect(isLt(2, 0)).toBe(false);
  expect(isGe(x, 0)).toBe('unknown'); expect(isGe(x, 0, Q.positive(x))).toBe(true);
});
