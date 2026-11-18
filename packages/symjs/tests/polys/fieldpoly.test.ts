// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { FieldPoly } from '../../src/polys/fieldpoly';
import { GF, QQ, ZZ, Sym, Poly, parseExpr, ExactQuotientFailed, DomainError, AlgebraicField } from '../../src';
const x = new Sym('x'), y = new Sym('y'), z = new Sym('z');
const show = (p: FieldPoly) => String(p.asExpr([x,y,z].slice(0,p.nvars)));
for (const K of [QQ,GF(2),GF(5),new AlgebraicField(QQ,parseExpr('sqrt(2)')),QQ.fracField(new Sym('a'))]) {
  const P = (e: string,n = 2): FieldPoly => {
    const p = Poly.from(parseExpr(e),[x,y,z].slice(0,n));
    return new FieldPoly(K,n,p.terms());
  };
  it(`primitive PRS and division over ${String(K)}`, () => {
    const a = P('(x+y)*(x+y+1)'), b = P('(x+y)*(y+1)');
    const g = a.gcd(b);
    expect(show(g)).toBe('x + y');
    expect(a.exquo(g).mul(g).sub(a).isZero).toBe(true);
    expect(b.exquo(g).mul(g).sub(b).isZero).toBe(true);
    expect(a.gcd(a.zero).sub(a.monic()).isZero).toBe(true);
    expect(a.zero.gcd(a).sub(a.monic()).isZero).toBe(true);
    expect(a.zero.gcd(a.zero).isZero).toBe(true);
    expect(show(P('x*y+y').gcd(P('x*y**2+y**2')))).toBe('x*y + y');
    expect(show(P('(x+y)*(y+z)',3).gcd(P('(x+y)*(y+z+1)',3)))).toBe('x + y');
    const [q,r] = P('x+y').div(P('x+1'));
    expect(q.mul(P('x+1')).add(r).sub(P('x+y')).isZero).toBe(true);
    const [pq,pr] = a.pseudoDiv(b);
    const lc = P('y+1').pow(2);
    expect(pq.mul(b).add(pr).sub(a.mul(lc)).isZero).toBe(true);
    expect(show(P('x+1',1).gcd(P('x**2-1',1)))).toBe('x + 1');
    expect(show(P('x+y').pow(0))).toBe('1');
    expect(show(P('x+y').pow(3).diff(0))).toBe(show(P('3*x**2+6*x*y+3*y**2')));
    expect(() => a.exquo(P('x'))).toThrow(ExactQuotientFailed);
    expect(() => a.div(a.zero)).toThrow(RangeError);
    expect(() => a.pseudoDiv(a.zero)).toThrow(RangeError);
    expect(() => a.pow(-1)).toThrow(RangeError);
    expect(() => a.asExpr([x])).toThrow(RangeError);
    expect(() => a.add(P('x',1))).toThrow(DomainError);
  });
}
it('validates coefficient fields and monomials and combines repeated terms', () => {
  expect(() => new FieldPoly(ZZ,1,[])).toThrow(DomainError);
  expect(() => new FieldPoly(QQ,1,[[[1,0],1]])).toThrow(RangeError);
  expect(() => new FieldPoly(QQ,1,[[[-1],1]])).toThrow(RangeError);
  expect(show(new FieldPoly(QQ,1,[[[1],2],[[1],-2],[[0],0]]))).toBe('0');
  expect(() => new FieldPoly(QQ,1,[]).add(new FieldPoly(GF(5),1,[]))).toThrow(DomainError);
});

it('computes subresultants with degree gaps and native algebraic coefficients',()=>{
  const K=new AlgebraicField(QQ,parseExpr('sqrt(2)'));
  const P=(e:string):FieldPoly=>new FieldPoly(K,2,Poly.from(parseExpr(e),[x,y]).terms());
  const f=P('x**4+sqrt(2)*y*x+1'),g=P('x**2+y');
  const rs=f.subresultants(g);
  expect(rs.map((p)=>p.degree())).toEqual([4,2,1,0]);
  expect(f.gcd(g).sub(f.one).isZero).toBe(true);
  expect(g.subresultants(f).map(show)).toEqual(rs.map(show));
  expect(f.zero.subresultants(f.zero)).toEqual([]);
  expect(f.subresultants(f.zero)).toEqual([f]);
  const c=new FieldPoly(K,0,[[[],K.convert(2)]]);
  expect(c.gcd(c).asExpr([]).equals(1)).toBe(true);
});
it('normalizes a subresultant sequence with a noninitial degree drop greater than one',()=>{
  const P=(e:string)=>new FieldPoly(QQ,1,Poly.from(parseExpr(e),[x]).terms());
  expect(P('x**5+x**2+x').subresultants(P('x**3+1')).map((p)=>p.degree())).toEqual([5,3,1,0]);
});
it('translates only polynomial generators and checks translation arity',()=>{
  const f=new FieldPoly(QQ,2,Poly.from(parseExpr('x**2+x*y+1'),[x,y]).terms());
  expect(show(f.shift([1,-1]))).toBe('x**2 + x*y + x + y + 1');
  expect(()=>f.shift([1])).toThrow(RangeError);
});
