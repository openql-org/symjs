// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { at } from '../../src/core/guard';
import { Expr, Pow, Rational, Sym } from '../../src/core/nodes';
import { NotImplementedError } from '../../src/core/errors';
import { parse } from '../../src/parsing/parser';
import { str } from '../../src/printing/str';
import { cancel } from '../../src/simplify/rational';
import { expand } from '../../src/simplify/expand';
import { diff } from '../../src/calculus/diff';
import { FracElement, FracField, field, sfield, vfield, xfield } from '../../src/polys/fields';
import { QQ, ZZ } from '../../src/polys/domains';
import { GF } from '../../src/polys/domains/finitefield';
import { AlgebraicField } from '../../src';
import { PolyRing } from '../../src/polys/rings';
import refs from './fields.references.json';

const p = parse;
const F = new FracField('x y z');
const [x, y, z] = [at(F.gens, 0), at(F.gens, 1), at(F.gens, 2)];
const f = x.pow(2).add(y.mul(3)).div(z);
function same(value: FracElement | Expr, expected: string): void {
  expect(value instanceof Expr ? str(value) : String(value)).toBe(expected);
}

describe('SymPy sparse rational function field references', () => {
  it('constructs and identifies fields and generators', () => {
    expect(String(F)).toBe(refs.field);
    expect(F.ngens).toBe(3);
    expect(F.equals(new FracField('x,y,z', ZZ))).toBe(true);
    expect(F.equals(new FracField('x y z', QQ))).toBe(false);
    expect(F.equals(1)).toBe(false);
    expect(F.isElement(x)).toBe(true);
    expect(F.isElement(new FracField('w').one)).toBe(false);
    expect(F.isElement(1)).toBe(false);
    expect(F.index(y)).toBe(1);
    expect(F.toRing()).toBe(F.ring);
    expect(String(F.toDomain())).toBe(refs.domain);
    expect(String(x.parent())).toBe(refs.domain);
    same(F.zero, refs.zero); same(F.one, refs.one);
    expect(F.zero.isZero).toBe(true);
    expect(F.one.isZero).toBe(false);
    expect(F.domainNew(2)).toEqual(Rational.of(2));
    const [K, ...gens] = field('x y');
    expect(gens.map(String)).toEqual(['x', 'y']);
    expect(K.equals(vfield('x y'))).toBe(true);
    expect(xfield('x y')[1].map(String)).toEqual(['x', 'y']);
    expect(String(field('t', QQ, 'grlex')[0])).toContain('over QQ with grlex order');
    expect(String(xfield('t', 'QQ', 'grlex')[0])).toContain('over QQ with grlex order');
    expect(String(vfield('t', 'QQ', 'grlex'))).toContain('over QQ with grlex order');
  });

  for (const c of refs.operations) it(`${c.domain}: ${c.lhs} ${c.op} ${c.rhs}`, () => {
    const K = new FracField('x y', c.domain === 'GF(5)' ? GF(5) : c.domain);
    const a = K.fromExpr(p(c.lhs)), b = K.fromExpr(p(c.rhs));
    let result: FracElement;
    switch (c.op) {
      case 'add': result = a.add(b); break;
      case 'sub': result = a.sub(b); break;
      case 'mul': result = a.mul(b); break;
      case 'div': result = a.div(b); break;
      default: throw new TypeError('unknown reference operation');
    }
    same(result, c.result);
    expect(String(result.numer)).toBe(c.numer);
    expect(String(result.denom)).toBe(c.denom);
    // An independent polynomial identity checks the value before cancellation.
    const n = c.op === 'add' ? a.numer.mul(b.denom).add(b.numer.mul(a.denom))
      : c.op === 'sub' ? a.numer.mul(b.denom).sub(b.numer.mul(a.denom))
      : c.op === 'mul' ? a.numer.mul(b.numer) : a.numer.mul(b.denom);
    const d = c.op === 'div' ? a.denom.mul(b.numer) : a.denom.mul(b.denom);
    expect(result.numer.mul(d).sub(n.mul(result.denom)).isZero).toBe(true);
  });

  it('cancels signs and factors while preserving explicit raw construction', () => {
    same(F.new(x.numer.pow(2).mul(2).sub(2), x.numer.mul(-4).add(4)), refs.cancel_sign);
    same(F.rawNew(x.numer.pow(2).sub(1), x.numer.sub(1)), refs.raw);
    same(F.rawNew(F.ring.zero, x.numer), refs.raw_zero);
    same(F.rawNew(x.numer, F.ring.one.neg()), refs.negative_denominator);
    same(x.div(y.mul(2)), refs.compound_denominator);
    same(x.div(y.pow(2)), refs.power_denominator);
    same(x.neg().pow(-2), refs.negative_power);
    same(x.neg().pow(-1), refs.negative_odd_power);
    same(F.groundNew(Rational.of(2,3)), refs.ground_rational);
    same(F.fieldNew([x.numer.pow(2).sub(1), x.numer.sub(1)]), 'x + 1');
    same(F.fieldNew(x.numer), 'x');
    same(F.fieldNew(2n), '2');
    same(F.fieldNew(p('x**2/z')), 'x**2/z');
    expect(F.fieldNew(x)).toBe(x);
    expect(x.toPoly()).toBe(x.numer);
    expect(x.rawNew(x.numer).equals(x)).toBe(true);
    expect(new FracElement(F, x.numer).equals(x)).toBe(true);
    expect(f.copy()).not.toBe(f);
    expect(f.copy().equals(f)).toBe(true);
    expect(F.one.equals(1)).toBe(true);
    expect(F.zero.equals(0)).toBe(true);
    expect(f.equals(1)).toBe(false);
    expect(x.equals(y)).toBe(false);
    expect(x.equals(new FracField('x', QQ).one)).toBe(false);
    expect(x.setField(F)).toBe(x);
    same(f.setField(new FracField('z y x', QQ)), refs.reordered);
    same(f, refs.fraction);
    expect(str(f.asExpr(new Sym('a'), new Sym('b'), new Sym('c')))).toBe('(a**2 + 3*b)/c');
  });

  it('differentiates reduced fractions by the quotient rule', () => {
    same(x.pow(2).add(y).div(z.add(1)).diff(x), refs.derivative);
    const h = x.add(1).div(x.pow(2).add(1));
    same(h.diff(x), refs.quotient_derivative);
    expect(str(cancel(h.diff(x).asExpr().sub(diff(h.asExpr(), new Sym('x')))))).toBe('0');
    same(h.diff(y), '0');
    const G = new FracField('t', GF(5)), t = at(G.gens, 0);
    same(t.pow(5).add(1).diff(t), refs.positive_characteristic_derivative);
  });

  it('uses real and expression coefficient arithmetic', () => {
    const R = new FracField('t', 'RR'), t = at(R.gens, 0);
    same(t.add(1).div(t.sub(1)).add(Rational.of(1,2)), refs.real_arithmetic);
    const E = new FracField('t', 'EX'), u = at(E.gens, 0);
    same(u.add(1).div(u.sub(1)).add(Rational.of(1,2)), refs.expression_arithmetic);
  });

  it('preserves field identities for multivariate fractions with common factors', () => {
    for (const K of [ZZ, QQ, GF(5)]) {
      const G = new FracField('a b', K), a = at(G.gens, 0), b = at(G.gens, 1);
      for (let i = 1; i <= 4; i++) {
        const common = a.add(b).add(i), n = a.pow(i).add(b), d = a.sub(b).add(i);
        const h = n.mul(common).div(d.mul(common));
        expect(h.sub(n.div(d)).isZero).toBe(true);
        expect(h.add(b).sub(b).sub(h).isZero).toBe(true);
        expect(h.div(h).equals(1)).toBe(true);
        const derivative = h.diff(a);
        const quotientNumerator = h.numer.diff(0).mul(h.denom).sub(h.numer.mul(h.denom.diff(0)));
        expect(derivative.numer.mul(h.denom.pow(2)).sub(quotientNumerator.mul(derivative.denom)).isZero).toBe(true);
      }
    }
  });

  it('distinguishes evaluation from substitution and rejects poles', () => {
    same(f.evaluate(x, 0), refs.evaluate);
    same(f.evaluate([[z,2],[x,1]]), refs.evaluate_reordered);
    same(f.subs(x,0), refs.subs);
    same(f.subs([[x,1],[y,2]]), refs.subs_list);
    same(f.call(0), refs.evaluate);
    same(f.call(1,1,2), refs.evaluate_all);
    same(f.evaluate([]), refs.fraction);
    same(f.subs([]), refs.fraction);
    expect(() => f.evaluate(z,0)).toThrow(RangeError);
    expect(() => f.subs(z,0)).toThrow(RangeError);
    expect(() => f.call(1,1,0)).toThrow(RangeError);
    expect(() => f.call()).toThrow(RangeError);
    expect(() => f.call(1,2,3,4)).toThrow(RangeError);
    expect(() => f.subs(x)).toThrow(TypeError);
  });

  for (const c of refs.inferred) it(`infers a field for ${c.input}`, () => {
    const [K, value] = sfield(p(c.input), ...c.gens.map((g) => p(g)), c.options);
    expect(String(K)).toBe(c.field);
    same(value, c.result);
    expect(str(cancel(expand(value.asExpr().sub(p(c.input)))))).toBe('0');
  });

  it('infers common and constant fields from lists', () => {
    const [K, values] = sfield([p('x/2'), p('(x+1)/(y-1)')]);
    expect(String(K)).toBe(refs.inferred_list_field);
    expect(`[${values.map(String).join(', ')}]`).toBe(refs.inferred_list);
    const [C, c] = sfield(Rational.of(1,2));
    expect(String(C)).toBe(refs.inferred_constant_field);
    same(c, refs.inferred_constant);
    const [E, empty] = sfield([]);
    expect(String(E)).toBe(refs.inferred_empty_field);
    expect(empty).toEqual([]);
  });

  it('converts compatible coefficient rings and non-symbol generators', () => {
    const Q = new PolyRing('x y z', QQ);
    same(F.fieldNew(Q.fromExpr(p('x/2+1/3'))), '(3*x + 2)/6');
    const N = new FracField('t', 'ZZ(x,y,z)');
    expect(str(N.fieldNew(f).asExpr())).toBe(str(f.asExpr()));
    const A = new FracField([p('sqrt(x)'), p('y**(-1)')]);
    expect(str(A.fromExpr(p('x**(3/2)+y')).asExpr())).toBe(refs.non_symbol_expression);
    expect(() => A.fromExpr(p('x**(1/3)'))).toThrow(RangeError);
    expect(() => A.fromExpr(p('z**(1/3)'))).toThrow(RangeError);
  });

  it('throws typed errors for invalid inputs and explicit remaining limitations', () => {
    expect(() => F.new(F.ring.zero, F.ring.zero)).toThrow(RangeError);
    expect(() => F.rawNew(F.ring.one, F.ring.zero)).toThrow(RangeError);
    // A nonzero denominator can become zero on conversion to a finite field.
    expect(() => new FracField('x y z', GF(5)).new(F.ring.zero, F.ring.groundNew(5))).toThrow(RangeError);
    expect(() => x.div(0)).toThrow(RangeError);
    expect(() => F.zero.pow(-1)).toThrow(RangeError);
    expect(() => x.pow(Rational.of(1,2))).toThrow(TypeError);
    expect(() => x.div(y).toPoly()).toThrow(RangeError);
    expect(() => F.index(F.one)).toThrow(RangeError);
    expect(() => F.index(new FracField('w').one)).toThrow(RangeError);
    expect(() => F.fromExpr(p('sin(x)'))).toThrow(RangeError);
    expect(() => F.fromExpr(new Pow(Rational.of(0), Rational.of(-1)))).toThrow(RangeError);
    expect(() => new FracField('x', QQ).fromExpr(p('sin(x)'))).toThrow(RangeError);
    expect(() => F.fieldNew(new FracField('t').one)).toThrow(NotImplementedError);
    expect(() => F.fieldNew('x')).toThrow(NotImplementedError);
    expect(() => f.compose(x,y)).toThrow(NotImplementedError);
    expect(String(new FracField('x', GF(5)).toDomain())).toBe('GF(5)(x)');
    expect(String(new FracField('x', 'EX').toDomain())).toBe('EX(x)');
    expect(() => new FracField([p('sqrt(x)')]).toDomain()).toThrow(NotImplementedError);
  });
});

it('preserves coefficient domains in fraction-field wrappers (SymPy 1.14)', () => {
  const t = new Sym('t'), X = new Sym('x');
  for (const K of [GF(5), new AlgebraicField(QQ, p('sqrt(2)')), QQ.fracField(t), QQ.polyRing(t)]) {
    const F = new FracField([X], K), D = F.toDomain();
    expect(String(D)).toBe(`${String(K)}(x)`);
    expect(String(D.toSympy(D.fromSympy(p('x + 1'))))).toBe('x + 1');
    const a = F.fromExpr(p('(x**2-1)/(x-1)'));
    expect(a.equals(F.fromExpr(p('x+1')))).toBe(true);
    expect(F.fromExpr(D.toSympy(D.fromSympy(a.asExpr()))).equals(a)).toBe(true);
  }
  expect(String(new FracField('x', GF(5)).one.parent())).toBe('GF(5)(x)');
});

it('cancels multivariate factors over finite, algebraic and nested coefficient fields',()=>{
  const t=new Sym('t');
  for(const [K,c] of [[GF(5),'2'],[new AlgebraicField(QQ,p('sqrt(2)')),'sqrt(2)'],[QQ.fracField(t),'1/(t+1)']] as const){
    const F=new FracField('x y',K);
    const a=F.fromExpr(p(`((x+${c}*y)*(x+y+1))/((x+${c}*y)*(y+1))`));
    expect(a.equals(F.fromExpr(p('(x+y+1)/(y+1)')))).toBe(true);
    expect(a.numer.gcd(a.denom).isOne).toBe(true);
  }
});
