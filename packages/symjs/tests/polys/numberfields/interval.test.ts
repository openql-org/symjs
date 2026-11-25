// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { algebraicEnclosure, compareAlgebraicReal } from '../../../src/polys/numberfields/interval';
import { parse, Rational, rootOf, Sym, Fn, Pow, S, NotImplementedError } from '../../../src';
import refs from '../continuation.references.json';

for(const row of refs.boxes) it(`certifies the complex rectangle for ${row.expr}`,()=>{
  const coarse=algebraicEnclosure(parse(row.expr),20), fine=algebraicEnclosure(parse(row.expr),48);
  for(const [i,expected] of [row.re,row.im].entries()) {
    const q=parse(expected);if(!(q instanceof Rational))throw new TypeError('rational fixture');
    for(const box of [coarse,fine]) {
      const iv=box[i];if(!iv)throw new RangeError('coordinate');
      expect(iv[0].p*q.q<=q.p*iv[0].q).toBe(true);
      expect(iv[1].p*q.q>=q.p*iv[1].q).toBe(true);
    }
    const iv=fine[i];if(!iv)throw new RangeError('coordinate');
    expect(Number(iv[1].p)/Number(iv[1].q)-Number(iv[0].p)/Number(iv[0].q)).toBeLessThan(1e-10);
  }
});
it('compares arbitrarily close real values without rounding their difference',()=>{
  expect(compareAlgebraicReal(parse('sqrt(2)'),parse('sqrt(2+1/10**60)'))).toBe(-1);
  expect(compareAlgebraicReal(parse('sqrt(2+1/10**60)'),parse('sqrt(2)'))).toBe(1);
  expect(compareAlgebraicReal(parse('2'),parse('2'))).toBe(0);
  expect(compareAlgebraicReal(parse('1'),parse('2'))).toBe(-1);
  expect(compareAlgebraicReal(parse('2'),parse('1'))).toBe(1);
});
it('encloses indexed real and complex roots and their projections',()=>{
  for(const i of [0,1,2]){
    const r=rootOf(parse('x**3-x-1'),i,{radicals:false}),box=algebraicEnclosure(r,24);
    for(const [name,coordinate] of [['re',0],['im',1]] as const) expect(algebraicEnclosure(new Fn(name,[r]),24)[0]).toEqual(box[coordinate]);
    expect(algebraicEnclosure(new Fn('conjugate',[r]),24)[0]).toEqual(box[0]);
  }
});
it('rejects unsupported expressions and undecidable denominators at the requested precision',()=>{
  expect(()=>algebraicEnclosure(new Sym('x'),20)).toThrow(NotImplementedError);
  expect(()=>compareAlgebraicReal(new Sym('x'),S.Zero)).toThrow(NotImplementedError);
  for(const e of [new Fn('sin',[S.One]),new Fn('sin',[new Sym('x')]),new Pow(S.E,S.One),new Pow(S.E,new Sym('x'))])expect(()=>algebraicEnclosure(e,20)).toThrow(NotImplementedError);
  expect(()=>algebraicEnclosure(new Pow(S.Zero,S.NegOne),20)).toThrow(RangeError);
});

it('rounds outward near branch cuts and rejects boxes that need refinement',()=>{
  for(const e of ['1/(sqrt(2)-1414213/1000000+I/100)','(sqrt(2)-1414213/1000000+I)**(1/3)']){
    const b=algebraicEnclosure(parse(e),12);
    expect(b.every(([a,c])=>a.p*c.q<=c.p*a.q)).toBe(true);
  }
  expect(()=>algebraicEnclosure(parse('(sqrt(2)-1414213/1000000)**(1/3)'),4)).toThrow(RangeError);
  expect(()=>algebraicEnclosure(parse('(-2+I*(sqrt(2)-1414213/1000000))**(1/3)'),4)).toThrow(RangeError);
  expect(()=>algebraicEnclosure(new Pow(S.E,parse('I*pi*x')),20)).toThrow(NotImplementedError);
});

import { Add, CRootOf, Mul } from '../../../src';
it('refines reciprocals near zero and preserves exact degenerate root intervals',()=>{
  const b=algebraicEnclosure(parse('1/(sqrt(2)+I/100)'),20);
  expect(b[0][0].p).toBeGreaterThan(0n);
  expect(algebraicEnclosure(new CRootOf(parse('x-1'),0),20)[0].map(String)).toEqual(['1','1']);
  expect(algebraicEnclosure(parse('tan(pi/7)'),20)[0][0].p).toBeGreaterThan(0n);
  expect(algebraicEnclosure(new Pow(S.E,parse('-I*pi/7')),20)[1][1].p).toBeLessThan(0n);
  const cancelImaginary=new Add([S.Two,S.I,new Mul([S.NegOne,S.I])]);
  expect(algebraicEnclosure(new Pow(cancelImaginary,Rational.of(1,3)),20)[1]).toEqual([S.Zero,S.Zero]);
  expect(compareAlgebraicReal(parse('1/(sqrt(2)-1414213562373095048801688724209698/10**33)'),S.Zero)).toBe(1);
});
it('encloses sines and cosines of rational multiples of atan2(y, x)',()=>{
  const angle=new Fn('atan2',[S.One,Rational.of(2n)]),half=Rational.of(1n,2n);
  // cos(atan2(1, 2)/2) = sqrt((1 + 2/sqrt(5))/2) ~ 0.97325, sin(atan2(1, 2)/2) ~ 0.22975
  for(const [name,value] of [['cos',0.9732489894677302],['sin',0.2297529205473612],['tan',0.2360679774997897]] as const){
    const [re,im]=algebraicEnclosure(new Fn(name,[new Mul([half,angle])]),24);
    expect(Number(re[0].p)/Number(re[0].q)).toBeLessThanOrEqual(value);
    expect(Number(re[1].p)/Number(re[1].q)).toBeGreaterThanOrEqual(value);
    expect(im[0].p).toBe(0n);
  }
  expect(()=>algebraicEnclosure(new Fn('sin',[new Mul([S.Pi,angle])]),24)).toThrow(NotImplementedError);
});
