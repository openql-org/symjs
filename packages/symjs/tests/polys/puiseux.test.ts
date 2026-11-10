// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { Rational, Sym, parse, str } from '../../src/core';
import { at, first } from '../../src/core/guard';
import { NotImplementedError } from '../../src/core/errors';
import { CoercionFailed, QQ, ZZ } from '../../src/polys/domains';
import { PolyRing } from '../../src/polys/rings';
import { PuiseuxPoly, PuiseuxRing, puiseuxRing } from '../../src/polys/puiseux';

const R = new PuiseuxRing('x y', QQ), x = first(R.gens), y = at(R.gens, 1);
const P = (e: string): PuiseuxPoly => R.fromExpr(parse(e));
const references: { puiseux: { expr: string; expected: string; asExpr: string; dx: string; dy: string }[] } = JSON.parse(readFileSync(new URL('./ringseries.references.json', import.meta.url), 'utf8'));

describe('SymPy 1.14 Puiseux polynomials', () => {
  for (const r of references.puiseux) it(r.expr, () => {
    const p = P(r.expr);
    expect(String(p)).toBe(r.expected);
    expect(str(p.asExpr())).toBe(r.asExpr);
    expect(String(p.diff(x))).toBe(r.dx);
    expect(String(p.diff(y))).toBe(r.dy);
  });
  it('constructs rings, generators, constants and term maps', () => {
    const [r, ...gens] = puiseuxRing('x y', QQ);
    expect(r.equals(R)).toBe(true);
    expect(String(r)).toBe('PuiseuxRing((x, y), QQ)');
    expect(String(new PuiseuxRing('x', ZZ))).toBe('PuiseuxRing((x,), ZZ)');
    expect(r.equals(QQ)).toBe(false);
    expect(r.equals(new PuiseuxRing('x y', ZZ))).toBe(false);
    expect(gens.map(String)).toEqual(['x', 'y']);
    expect(r.index(at(gens, 1))).toBe(1);
    expect(String(r.fromInt(3))).toBe('3');
    expect(str(r.domainNew(3))).toBe('3');
    expect(String(r.groundNew(3))).toBe('3');
    const terms = new Map([[ [Rational.of(1, 2), 0], 3 ]]);
    expect(String(r.ringNew(terms))).toBe('3*x**(1/2)');
    expect(String(PuiseuxPoly.fromDict(terms, r))).toBe('3*x**(1/2)');
    const p = new PolyRing('x y', QQ).fromExpr(parse('x**2'));
    expect(String(r.ringNew(p))).toBe('x**2');
    expect(String(r.fromPoly(p))).toBe('x**2');
    expect(() => Reflect.apply(r.ringNew.bind(r), r, ['3'])).toThrow(NotImplementedError);
    expect(String(r.ringNew(3n))).toBe('3');
    expect(r.ringNew(x)).toBe(x);
  });
  it('combines equal exact exponent vectors and removes zero coefficients', () => {
    const p = R.fromDict([[[Rational.of(1, 3), 0], 2], [[Rational.of(2, 6), 0], -2], [[0, 0], 0], [[0, 1], 3]]);
    expect(String(p)).toBe('3*y');
    expect(p.length).toBe(1);
    expect(p.isTerm).toBe(true);
    expect(p.isZero).toBe(false);
    expect(R.zero.isZero).toBe(true);
    expect(R.one.isOne).toBe(true);
    expect(p.isOne).toBe(false);
    expect(str(p.get([0, 1]))).toBe('3');
    expect(str(p.get([1, 0]))).toBe('0');
    expect(R.fromDict(p.toDict()).equals(p)).toBe(true);
    expect(p.equals(R.one)).toBe(false);
    expect(p.equals(3)).toBe(false);
    expect(R.fromInt(3).equals(3)).toBe(true);
    expect(R.fromInt(3).equals(3n)).toBe(true);
    expect(R.fromInt(3).equals(Rational.of(3))).toBe(true);
    expect(R.zero.equals(0)).toBe(true);
    expect(x.equals(0)).toBe(false);
    expect(x.add(y).equals(0)).toBe(false);
    expect(x.equals(null)).toBe(false);
    expect(x.equals(first(new PolyRing('x y', QQ).gens))).toBe(true);
    expect(x.equals(first(new PolyRing('z', QQ).gens))).toBe(false);
    expect(p.equals(new PuiseuxRing('z', QQ).one)).toBe(false);
    expect(P('x+y').equals(P('x+2*y'))).toBe(false);
  });
  it('performs exact arithmetic, including rational and negative powers', () => {
    expect(String(x.add(y).pow(2))).toBe('y**2 + 2*x*y + x**2');
    expect(String(x.add(1).pow(3))).toBe('1 + 3*x + 3*x**2 + x**3');
    expect(String(x.pow(0))).toBe('1');
    expect(String(x.pow(Rational.of(1, 3)).pow(3))).toBe('x');
    expect(String(x.pow(-2))).toBe('x**(-2)');
    expect(String(x.pow(Rational.of(-1, 3)))).toBe('x**(-1/3)');
    expect(String(x.mul(2).pow(-1))).toBe('1/2*x**(-1)');
    expect(String(x.sub(y))).toBe('-1*y + x');
    expect(String(x.neg())).toBe('-1*x');
    expect(String(x.truediv(y))).toBe('x*y**(-1)');
    expect(String(x.truediv(2))).toBe('1/2*x');
    expect(x.add(y).sub(y).equals(x)).toBe(true);
    expect(x.mul(y).truediv(y).equals(x)).toBe(true);
    // Exponent denominators are exact even beyond Number.MAX_SAFE_INTEGER.
    const e = Rational.of(1, 9007199254740993n);
    expect(x.pow(e).mul(x.pow(e)).monoms()[0]?.[0]?.key).toBe('2/9007199254740993');
  });
  it('rejects invalid exponents, generators, coefficient domains and ring combinations', () => {
    expect(() => R.fromDict([[[1], 1]])).toThrow(RangeError);
    expect(() => x.pow(new Sym('a'))).toThrow(TypeError);
    expect(() => x.add(y).pow(-1)).toThrow(RangeError);
    expect(() => x.add(y).pow(Rational.of(1, 2))).toThrow(RangeError);
    expect(() => x.mul(2).pow(Rational.of(1, 2))).toThrow(RangeError);
    expect(() => x.truediv(x.add(y))).toThrow(RangeError);
    expect(() => x.truediv(0)).toThrow(RangeError);
    expect(() => R.index(x.add(y))).toThrow(RangeError);
    expect(() => x.add(new PuiseuxRing('z', QQ).one)).toThrow(RangeError);
    expect(() => R.fromExpr(parse('sin(x)'))).toThrow(CoercionFailed);
    expect(() => Reflect.apply(R.ringNew.bind(R), R, [null])).toThrow(TypeError);
    const Z = new PuiseuxRing('x', ZZ), z = first(Z.gens);
    expect(String(z.pow(-1))).toBe('x**(-1)');
    expect(String(z.truediv(z))).toBe('1');
    expect(() => z.mul(2).pow(-1)).toThrow(RangeError);
    expect(() => z.truediv(2)).toThrow(CoercionFailed);
    expect(() => z.mul(2).truediv(2)).toThrow(CoercionFailed);
    expect(() => z.truediv(z.mul(2))).toThrow(RangeError);
  });
});
