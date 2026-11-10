// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Free groups and their words (SymPy 1.14 combinatorics/free_groups.py and its doctests).
import { describe, expect, it } from 'vitest';
import { Rational, S, Sym, str } from '../../src';
import { FreeGroup, FreeGroupElement, freeGroup, vfreeGroup, xfreeGroup } from '../../src/combinatorics';

const [F, x, y, z] = freeGroup('x, y, z') as [FreeGroup, FreeGroupElement, FreeGroupElement, FreeGroupElement];

describe('FreeGroup', () => {
  it('construction, caching and printing', () => {
    expect(new FreeGroup('x, y, z')).toBe(F);
    expect(new FreeGroup([new Sym('x'), new Sym('y'), new Sym('z')])).toBe(F);
    expect(new FreeGroup(['x', 'y', 'z'])).toBe(F);
    expect(new FreeGroup(new Sym('x')).rank).toBe(1);
    expect(() => new FreeGroup(['x', new Sym('y')])).toThrow(RangeError);
    expect(String(F)).toBe('<free group on the generators (x, y, z)>');
    expect(String(new FreeGroup('x'))).toBe('<free group on the generators (x,)>');
    expect(String(new FreeGroup('a:31'))).toBe('<free group with 31 generators>');
    const [G, gens] = xfreeGroup('a, b');
    expect(gens.map(String)).toEqual(['a', 'b']);
    expect(vfreeGroup('a, b')).toBe(G);
  });
  it('the group structure', () => {
    expect(F.length).toBe(3);
    expect(F.clone()).toBe(F);
    expect(F.clone('')).toBe(F);
    expect(F.clone([])).toBe(F);
    expect(String(F.clone('a'))).toBe('<free group on the generators (a,)>');
    expect(String(F.getItem(1))).toBe('<free group on the generators (y,)>');
    expect(String(F.getItem(-1))).toBe('<free group on the generators (z,)>');
    expect(String(F.slice(1))).toBe('<free group on the generators (y, z)>');
    expect(String(F.slice(-2, -1))).toBe('<free group on the generators (y,)>');
    expect(F.index(y)).toBe(1);
    expect(() => F.index(x.mul(y))).toThrow(RangeError);
    expect(() => F.index(new FreeGroup('u').generators[0]!)).toThrow(RangeError);
    expect(F.order()).toBe(S.Infinity);
    const E = new FreeGroup('');
    expect(E.order()).toBe(S.One);
    expect([...E.elements].map(String)).toEqual(['<identity>']);
    expect(() => F.elements).toThrow(RangeError);
    expect(F.isAbelian).toBe(false);
    expect(new FreeGroup('x').isAbelian).toBe(true);
    expect([...F.center()].map(String)).toEqual(['<identity>']);
    expect(F.contains(x)).toBe(true);
    expect(F.contains(1)).toBe(false);
    expect(F.contains(new FreeGroup('u').identity)).toBe(false);
    expect(String(F.dtype([[new Sym('x'), 2], [new Sym('y'), 0n], [new Sym('z'), -1]]))).toBe('x**2*z**-1');
    expect(() => F.dtype([[new Sym('u'), 1]])).toThrow(RangeError);
  });
});

describe('FreeGroupElement', () => {
  const w = x.pow(2).mul(y.inverse()).mul(x.pow(3));
  it('access', () => {
    expect(String(w)).toBe('x**2*y**-1*x**3');
    expect(w.arrayForm.map(([s, e]) => `${str(s)}^${e}`)).toEqual(['x^2', 'y^-1', 'x^3']);
    expect(w.letterForm.map(str)).toEqual(['x', 'x', '-y', 'x', 'x', 'x']);
    expect(String(w.getItem(2))).toBe('y**-1');
    expect(String(w.getItem(-1))).toBe('x');
    expect(() => w.getItem(9)).toThrow(RangeError);
    expect(w.index(y.inverse())).toBe(2);
    expect(() => w.index(x.mul(y))).toThrow(RangeError);
    expect(() => w.index(z)).toThrow(RangeError);
    expect(String(w.new([[new Sym('y'), 3]]))).toBe('y**3');
    expect(w.copy().equals(w)).toBe(true);
    expect(w.has(y)).toBe(true);
    expect(w.has(z)).toBe(false);
    expect(w.numberSyllables()).toBe(3);
    expect(w.exponentSyllable(-1)).toBe(3);
    expect(str(w.generatorSyllable(1))).toBe('y');
    expect(str(w.generatorSyllable(-1))).toBe('x');
    expect(String(w.subSyllables(1, 2))).toBe('y**-1');
    expect(String(w.subSyllables(-2, 3))).toBe('y**-1*x**3');
    expect(String(w.subSyllables(2, 2))).toBe('<identity>');
    expect(() => w.subSyllables(0.5, 2)).toThrow(RangeError);
    expect([...w.containsGenerators()].map(String)).toEqual(['x', 'y']);
  });
  it('arithmetic', () => {
    expect(String(x.pow(0))).toBe('<identity>');
    expect(String(x.pow(Rational.of(3)))).toBe('x**3');
    expect(String(x.pow(3n))).toBe('x**3');
    expect(() => x.pow(0.5)).toThrow(RangeError);
    expect(String(x.mul(y).pow(3))).toBe('x*y*x*y*x*y');
    expect(String(x.mul(y).pow(-2))).toBe('y**-1*x**-1*y**-1*x**-1');
    expect(String(x.mul(y).pow(1))).toBe('x*y');
    expect(String(x.mul(y).pow(-1))).toBe('y**-1*x**-1');
    expect(String(F.identity.mul(x))).toBe('x');
    expect(String(x.mul(x.inverse()))).toBe('<identity>');
    expect(String(x.mul(y).mul(y.inverse()).mul(x))).toBe('x**2');
    expect(() => x.mul(new FreeGroup('u').generators[0]!)).toThrow(TypeError);
    expect(String(x.div(y))).toBe('x*y**-1');
    expect(F.identity.order()).toBe(S.One);
    expect(x.order()).toBe(S.Infinity);
    expect(String(x.commutator(y))).toBe('x**-1*y**-1*x*y');
    expect(() => x.commutator(new FreeGroup('u').generators[0]!)).toThrow(RangeError);
  });
  it('comparison', () => {
    expect(x.lt(y)).toBe(true);
    expect(x.inverse().lt(x)).toBe(true);
    expect(x.pow(2).lt(y)).toBe(false);
    expect(x.le(x)).toBe(true);
    expect(y.gt(x)).toBe(true);
    expect(x.ge(x)).toBe(true);
    expect(x.equals(1)).toBe(false);
    expect(() => x.lt(new FreeGroup('u').generators[0]!)).toThrow(TypeError);
    expect(() => x.gt(new FreeGroup('u').generators[0]!)).toThrow(TypeError);
    expect([y, x.pow(2), x].sort((a, b) => FreeGroupElement.compare(a, b)).map(String)).toEqual(['x', 'y', 'x**2']);
    expect(FreeGroupElement.compare(x, x)).toBe(0);
  });
  it('subwords and elimination', () => {
    expect(() => w.exponentSum(x.mul(y))).toThrow(RangeError);
    expect(() => w.generatorCount(x.inverse())).toThrow(RangeError);
    expect(String(w.subword(1, 4))).toBe('x*y**-1*x');
    expect(String(w.subword(-1, 99, false))).toBe('x**2*y**-1*x**3');
    expect(String(w.subword(3, 2))).toBe('<identity>');
    expect(() => w.subword(-1, 2)).toThrow(RangeError);
    expect(w.subwordIndex(x.mul(y.inverse()))).toBe(1);
    expect(w.subwordIndex(x, 3)).toBe(3);
    expect(() => w.subwordIndex(y)).toThrow(RangeError);
    expect(w.isIndependent(z)).toBe(true);
    expect(String(w.eliminateWord(w))).toBe('<identity>');
    expect(String(w.eliminateWord(z))).toBe(String(w));
    expect(String(w.eliminateWord(y, y))).toBe(String(w));
    expect(String(w.eliminateWord(x, x.inverse(), true))).toBe('x**-2*y**-1*x**-3');
    expect(String(w.eliminateWord(y))).toBe('x**5');
    expect(String(w.eliminateWord(x.mul(y), y, false, false))).toBe(String(w));
    expect(String(w.eliminateWords(new Map([[y.inverse(), z]])))).toBe('x**2*z*x**3');
    expect(String(w.substitutedWord(0, 6, z))).toBe('z');
    expect(String(w.substitutedWord(0, 2, z))).toBe('z*y**-1*x**3');
    expect(String(w.substitutedWord(3, 6, z))).toBe('x**2*y**-1*z');
    expect(String(w.substitutedWord(2, 3, z))).toBe('x**2*z*x**3');
    expect(() => w.substitutedWord(3, 3, z)).toThrow(RangeError);
    expect(F.identity.isCyclicallyReduced()).toBe(true);
    expect(String(F.identity.identityCyclicReduction())).toBe('<identity>');
    expect(String(x.mul(y).mul(x.inverse()).identityCyclicReduction())).toBe('y');
    expect(x.isCyclicConjugate(x.mul(y))).toBe(false);
    expect(x.mul(y).isCyclicConjugate(y.mul(x))).toBe(true);
  });
  it('powers', () => {
    expect(F.identity.powerOf(x)).toBe(true);
    expect(x.pow(3).powerOf(x)).toBe(true);
    expect(x.pow(-3).powerOf(x)).toBe(true);
    expect(x.mul(y).powerOf(x)).toBe(false);
    expect(x.mul(y).pow(2).powerOf(x.mul(y))).toBe(true);
    expect(x.mul(y).pow(2).mul(x).powerOf(x.mul(y))).toBe(false);
    expect(x.mul(y).mul(x).powerOf(y.mul(x))).toBe(false);
    expect(x.mul(y).powerOf(y.mul(z))).toBe(false);
    const c = z.inverse().mul(x).mul(y).mul(z);
    expect(c.pow(3).powerOf(c)).toBe(true);
    expect(c.pow(3).powerOf(y.inverse().mul(x).mul(y).mul(z).mul(y))).toBe(false);
  });
});
