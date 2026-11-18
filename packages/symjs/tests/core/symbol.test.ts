// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { disambiguate, uniquelyNamedSymbol, Dummy, Sym, SymFunction } from '../../src';
const x = new Sym('x');
it('creates unique names, including existing suffixes and custom naming rules', () => {
  expect(String(uniquelyNamedSymbol('x', x))).toBe('x0');
  expect(String(uniquelyNamedSymbol('x', [x, new Sym('x0')]))).toBe('x1');
  expect(String(uniquelyNamedSymbol('x0', [new Sym('x1'), new Sym('x0')]))).toBe('x2');
  expect(String(uniquelyNamedSymbol(x))).toBe('x');
  expect(String(uniquelyNamedSymbol('x', x, { modify: (s) => s + s }))).toBe('xx');
  expect(String(uniquelyNamedSymbol('X', x, { compare: (s) => s.toLowerCase() }))).toBe('x0');
  expect(String(uniquelyNamedSymbol('f', SymFunction('f')(x).add(1)))).toBe('f0');
  expect(uniquelyNamedSymbol('x', 1, { positive: true }).assumptions.positive).toBe(true);
  const real = new Sym('x', { real: true });
  expect(uniquelyNamedSymbol(['x', real])).toBe(real);
  expect(uniquelyNamedSymbol([x, real])).toBe(real);
  expect(String(uniquelyNamedSymbol(['x', real], x))).toBe('x0');
});
it('disambiguates symbols and dummies without colliding with existing suffixes', () => {
  expect(String(disambiguate(x.add(new Sym('x', { integer: true }))))).toBe('(x + x_1,)');
  const result = disambiguate(new Dummy('x'), new Dummy('x'), new Sym('x_1'));
  expect(result.freeSymbols().size).toBe(3);
  expect([...result.freeSymbols()].every((s) => !(s instanceof Dummy))).toBe(true);
  expect(String(result)).toContain('x_2');
  expect(String(disambiguate())).toBe('()');
  expect(String(disambiguate(new Sym('_x'), new Dummy('x'), new Dummy('x')))).toBe('(x_2, x, x_1)');
});
