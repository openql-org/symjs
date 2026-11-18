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

it('normalizes linear relations without cancelling unknown symbolic signs', async () => {
  const { simplify, add, mul, pow, sin, relationalEquals } = await import('../../src');
  const y = new Sym('y');
  for (const op of ['Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge'] as const) {
    expect(simplify(new Rel(op, add(mul(2, x), -1), x)).key).toBe(new Rel(op, x, S.One).key);
  }
  expect(String(simplify(new Rel('Le', x.neg(), S.One)))).toBe('x >= -1');
  expect(String(simplify(new Rel('Ge', add(x, y), add(x, y.neg()))))).toBe('y >= 0');
  expect(String(simplify(new Rel('Eq', add(x, y), S.Zero)))).toBe('Eq(x, -y)');
  expect(simplify(new Rel('Eq', sin(x), y))).toBeInstanceOf(Rel);
  expect(simplify(new Rel('Eq', pow(x, 2), y))).toBeInstanceOf(Rel);
  expect(simplify(new Rel('Eq', new Sym('z', { real: false }), y))).toBeInstanceOf(Rel);
  expect(simplify(new Rel('Eq', S.One, S.One))).toBe(S.true);
  expect(simplify(new Rel('Eq', add(x, S.One), x))).toBe(S.false);
  expect(simplify(new Rel('Eq', S.true, x))).toBeInstanceOf(Rel);
  const eq = new Rel('Eq', x, S.One);
  expect(relationalEquals(eq, x)).toBe('unknown');
  expect(relationalEquals(eq, eq)).toBe(true);
  expect(relationalEquals(eq, new Rel('Eq', S.One, x))).toBe(true);
  expect(relationalEquals(eq, new Rel('Ne', x, S.One))).toBe(false);
  expect(relationalEquals(eq, new Rel('Eq', x, S.Zero))).toBe(false);
  expect(relationalEquals(eq, new Rel('Eq', y, S.One))).toBe(false);
  expect(relationalEquals(eq, new Rel('Eq', S.Zero, x))).toBe(false);
  expect(relationalEquals(eq, new Rel('Eq', S.One, y))).toBe(false);
  expect(relationalEquals(new Rel('Eq', S.One, S.Zero), new Rel('Eq', S.NegOne, S.Half))).toBe(false);
  expect(relationalEquals(new Rel('Eq', x, y), new Rel('Eq', S.One, S.Zero), true)).toBe(false);
  expect(relationalEquals(new Rel('Eq', x, y), new Rel('Eq', S.One, S.Zero))).toBe(false);
  const lt = new Rel('Lt', x, S.One);
  expect(relationalEquals(lt, new Rel('Gt', S.One, x))).toBe(true);
  expect(relationalEquals(lt, new Rel('Le', x, S.One))).toBe(false);
  expect(relationalEquals(lt, new Rel('Lt', S.Zero, S.One))).toBe(false);
  expect(relationalEquals(lt, new Rel('Lt', x, S.Zero))).toBe(false);
  expect(relationalEquals(new Rel('Lt', S.One, x), new Rel('Lt', S.Zero, x))).toBe(false);
  expect(relationalEquals(lt, new Rel('Lt', add(x, 0), y))).toBe(false);
});

it('returns undecided functional differences when requested', async () => {
  const { SymFunction, relationalEquals } = await import('../../src');
  const f = SymFunction('f');
  const a = f(1), b = f(2), c = f(3), d = f(4);
  const y = new Sym('y');
  for (const [left, right] of [
    [new Rel('Eq', x, a), new Rel('Eq', x, b)],
    [new Rel('Eq', a, x), new Rel('Eq', b, x)],
    [new Rel('Eq', x, a), new Rel('Eq', b, x)],
    [new Rel('Eq', a, x), new Rel('Eq', x, b)],
    [new Rel('Eq', a, c), new Rel('Eq', b, d)],
    [new Rel('Lt', x, a), new Rel('Lt', x, b)],
    [new Rel('Lt', a, x), new Rel('Lt', b, x)],
  ] as const) {
    expect(relationalEquals(left, right)).toBe('unknown');
    expect(String(relationalEquals(left, right, true))).toBe(String(a.sub(b)));
  }
  expect(relationalEquals(new Rel('Lt', a, x), new Rel('Gt', y, b))).toBe(false);
});

it('decides identities that become constant after expanding the difference', async () => {
  const { simplifyRelation } = await import('../../src/core/relational');
  const { add, mul } = await import('../../src');
  const y = new Sym('y');
  const lhs = mul(x, add(y, 1));
  const rhs = add(mul(x, y), x);
  expect(simplifyRelation(new Rel('Eq', lhs, rhs), (e) => e)).toBe(S.true);
});

it('orders linear symbols by the symbolic sort key', async () => {
  const { simplify, add } = await import('../../src');
  const a = new Sym('a'), B = new Sym('B');
  expect(String(simplify(new Rel('Ge', add(a, B), S.Zero)))).toBe('B >= -a');
});

it('rejects ordering of a generic Basic object', async () => {
  const { Basic } = await import('../../src');
  expect(() => isLt(Basic(), S.One)).toThrow(TypeError);
});
