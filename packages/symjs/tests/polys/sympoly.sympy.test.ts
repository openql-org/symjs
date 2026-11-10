// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Finite-field cases generated independently with SymPy 1.14.0.

import { describe, expect, it } from 'vitest';
import { Expr, Sym, Rational } from '../../src/core/nodes';
import { at } from '../../src/core/guard';
import { parse } from '../../src/parsing/parser';
import { str } from '../../src/printing/str';
import { Poly, factor, polyGcd, polyLcm } from '../../src/polys/sympoly';
import { GF } from '../../src/polys/domains/finitefield';
import { CoercionFailed, QQ, ZZ } from '../../src/polys/domains';
import { ExactQuotientFailed, InvariantError, NotImplementedError, NotInvertible, PolynomialError } from '../../src/core/errors';
import { OptionError, UnificationFailed } from '../../src/polys/polyerrors';
import { cancel } from '../../src/simplify/rational';
import refs from './sympoly.finite.references.json';

const x=new Sym('x'), y=new Sym('y');
const P=(e:string,p:number,gens:readonly Expr[]=[x])=>Poly.from(parse(e),gens,{modulus:p});
function show(value: unknown, tuple=true): string {
  if (Array.isArray(value)) return tuple ? `(${value.map((v)=>show(v,false)).join(', ')})` : `[${value.map((v)=>show(v,true)).join(', ')}]`;
  return value instanceof Expr ? str(value) : String(value);
}
function check(call:()=>unknown, reference:{result?:string;error?:string}):void {
  if (reference.error) {
    const errors:Record<string,new (...args:never[])=>Error>={CoercionFailed,ExactQuotientFailed,NotInvertible,ZeroDivisionError:RangeError,AssertionError:InvariantError,TypeError};
    const error=errors[reference.error];
    expect(error,reference.error).toBeDefined();
    expect(call).toThrow(error);
  } else expect(show(call())).toBe(reference.result);
}

describe('SymPy finite-field polynomial results',()=>{
  for(const c of refs.construct) it(`construct ${c.input} mod ${c.p}`,()=>check(()=>P(c.input,c.p,c.gens.map((g)=>new Sym(g))),c));
  for(const c of refs.unary) it(`${c.op} ${c.input} mod ${c.p}`,()=>{
    const f=P(c.input,c.p);
    const calls:Record<string,()=>unknown>={construct:()=>f,neg:()=>f.neg(),diff:()=>f.diff(),monic:()=>f.monic(),primitive:()=>f.primitive(),content:()=>f.content(),factorList:()=>f.factorList(),sqfList:()=>f.sqfList(),integrate:()=>f.integrate(),eval:()=>f.eval(3),pow:()=>f.pow(3)};
    check(calls[c.op]!,c);
  });
  for(const c of refs.binary) it(`${c.a} ${c.op} ${c.b} mod ${c.p}`,()=>{
    const f=P(c.a,c.p),g=P(c.b,c.p);
    const calls:Record<string,()=>unknown>={add:()=>f.add(g),sub:()=>f.sub(g),mul:()=>f.mul(g),div:()=>f.div(g),gcd:()=>f.gcd(g),lcm:()=>f.lcm(g),exquo:()=>f.exquo(g),gcdex:()=>f.gcdex(g)};
    check(calls[c.op]!,c);
    if(c.op==='div'&&!c.error){const [q,r]=f.div(g);expect(q.mul(g).add(r).equals(f)).toBe(true);expect(r.isZero||r.degree()<g.degree()).toBe(true);}
    if(c.op==='gcdex'&&!c.error){const [s,t,h]=f.gcdex(g);expect(s.mul(f).add(t.mul(g)).equals(h)).toBe(true);}
    if((c.op==='gcd'||c.op==='lcm')&&!c.error){const h=c.op==='gcd'?f.gcd(g):f.lcm(g);expect(h.domain).toBe(f.domain);}
  });
  for(const c of refs.ground) it(`${c.op} ${c.c} mod ${c.p}`,()=>{
    const f=P('3*x**2+4*x+2',c.p);
    const calls:Record<string,()=>unknown>={addGround:()=>f.addGround(c.c),subGround:()=>f.subGround(c.c),mulGround:()=>f.mulGround(c.c),quoGround:()=>f.quoGround(c.c),exquoGround:()=>f.exquoGround(c.c)};
    check(calls[c.op]!,c);
  });
  it('preserves the coefficient field through multivariate arithmetic',()=>{
    const f=P('x**2*y+x*y**2+y+1',5,[x,y]),g=P('2*x*y+1',5,[x,y]);
    expect(show(f.div(g))).toBe(refs.multi_div);
    const [q,r]=f.div(g);expect(q.mul(g).add(r).equals(f)).toBe(true);
    expect(show(P('x+1',5).add(P('y',5,[y])))).toBe(refs.multi_add);
    expect(show(f.eval(2,x))).toBe(refs.multi_eval);
    expect(show(f.diff(y))).toBe(refs.multi_diff);
    expect(show(f.integrate(y))).toBe(refs.multi_integrate);
    expect(P('x+1',5).add(y).gens.map(str)).toEqual(['x','y']);
  });
  it('accepts the public domain option on construction, factor, gcd and lcm',()=>{
    expect(String(Poly.from(parse('x**2+1'),[x],{domain:GF(2)}))).toBe(String(P('x**2+1',2)));
    expect(str(factor(parse('x**2+1'),{domain:GF(2)}))).toBe(refs.factor_domain);
    expect(str(factor(parse('x**2+1'),{domain:'GF(2)'}))).toBe(refs.factor_domain);
    expect(str(polyGcd(parse('x**2+1'),parse('x+1'),{domain:GF(2)}))).toBe(refs.gcd_domain);
    expect(str(polyLcm(parse('x**2+1'),parse('x+1'),{modulus:2}))).toBe(refs.lcm_domain);
    expect(str(polyGcd(P('x**2+1',2),P('x+1',2)))).toBe(refs.gcd_domain);
    expect(str(polyLcm(P('x**2+1',2),P('x+1',2)))).toBe(refs.lcm_domain);
    expect(String(Poly.from(parse('x/2'),[x],{domain:QQ}))).toBe("Poly(1/2*x, x, domain='QQ')");
    expect(str(factor(parse('x**2-1'),{domain:ZZ}))).toBe('(x - 1)*(x + 1)');
    expect(str(factor(parse('x**2+1'),{domain:'ZZ_I'}))).toBe('(x - I)*(x + I)');
    expect(str(factor(parse('x**2/4+1'),{domain:'QQ_I'}))).toBe('(x - 2*I)*(x + 2*I)/4');
    expect(str(factor(parse('x**2-2'),{domain:'QQ<sqrt(2)>'}))).toBe('(x - sqrt(2))*(x + sqrt(2))');
  });
  it('rejects incompatible coefficient domains and invalid finite coefficients',()=>{
    const f=P('x+1',5),q=Poly.from(x,[x]);
    expect(()=>f.add(q)).toThrow(UnificationFailed);
    expect(()=>q.add(f)).toThrow(UnificationFailed);
    expect(()=>f.mul(P('x',7))).toThrow(UnificationFailed);
    expect(()=>f.add(Rational.of(1,2))).toThrow(UnificationFailed);
    expect(()=>f.add(parse('sin(x)'))).toThrow(PolynomialError);
    expect(f.equals(q)).toBe(false);expect(q.equals(f)).toBe(false);
    // SymPy coerces expressions into the coefficient field for equality.
    expect(f.equals(parse('x+6'))).toBe(true);
    expect(f.equals(parse('x+1/2'))).toBe(false);
    expect(f.equals(parse('x+y'))).toBe(false);
    expect(f.equals(parse('sin(x)'))).toBe(false);
    expect(()=>Poly.from(x,[x],{domain:ZZ,modulus:5})).toThrow(OptionError);
    expect(()=>Poly.from(x,[x],{modulus:0})).toThrow(RangeError);
    expect(()=>Poly.from(x,[x],{modulus:-3})).toThrow(RangeError);
    expect(()=>P('x+1',6).factorList()).toThrow(NotImplementedError);
    expect(()=>P('x*y+1',5,[x,y]).gcd(P('x+y',5,[x,y]))).toThrow(NotImplementedError);
    expect(()=>P('x*y+1',5,[x,y]).div(P('0',5,[x,y]))).toThrow(RangeError);
    expect(()=>factor(x,{domain:'EX'})).toThrow(NotImplementedError);
  });
  it('reconstructs every finite-field factorization and square-free decomposition',()=>{
    for(const p of [2,3,5,7]){
      const f=P('(x+1)**6*(x+2)**3',p);
      for(const [c,factors] of [f.factorList(),f.sqfList()]){
        let product=Poly.from(c,[x],{modulus:p});
        for(const [g,k] of factors){expect(g.domain).toBe(f.domain);product=product.mul(g.pow(k));}
        expect(product.equals(f)).toBe(true);
      }
    }
    expect(P('x**5+1',5).diff().isZero).toBe(true);
    expect(P('x**5+1',5).sqfList()[1].map(([,k])=>k)).toEqual([5]);
  });
  it('keeps the domain for rem, quo, inverses and scalar arithmetic',()=>{
    const f=P('x**2+1',5),g=P('x+1',5);
    expect(f.rem(g).domain).toBe('GF(5)');expect(f.quo(g).domain).toBe('GF(5)');
    expect(f.divAuto(g,false).map((r)=>r.domain)).toEqual(['GF(5)','GF(5)']);
    const inverse=g.invert(f);expect(inverse.mul(g).rem(f).equals(1)).toBe(true);
    expect(f.add(2).sub(2).equals(f)).toBe(true);
    expect(f.mul(2).exquoGround(2).equals(f)).toBe(true);
    expect(at(f.gens,0)).toEqual(x);
  });
  it('rejects nonunits even in zero dense coefficients during integration',()=>{
    // SymPy divides the missing x coefficient by 2 in Z/6Z as well.
    expect(()=>P('x**2',6).integrate()).toThrow(NotInvertible);
  });
  it('recurses through three generators in polynomial division',()=>{
    const z=new Sym('z'),gens=[x,y,z];
    // SymPy 1.14 Poly.div over GF(5), including exact and lower-degree dividends.
    for(const [a,b,q,r] of [
      ['x*y+1','x*y+1','1','0'],
      ['x*y+1','x**2*y+1','0','x*y+1'],
      ['x**2*y**2+x*y','x*y','x*y+1','0'],
      ['x*y*z+1','x*y+1','z','1-z'],
    ]){
      const f=P(a!,5,gens),g=P(b!,5,gens),[quot,rem]=f.div(g);
      expect(quot.equals(P(q!,5,gens))).toBe(true);
      expect(rem.equals(P(r!,5,gens))).toBe(true);
      expect(quot.mul(g).add(rem).equals(f)).toBe(true);
    }
  });
});

describe('SymPy finite-field cancellation',()=>{
  for(const c of refs.cancel)it(`${c.input} mod ${c.p}`,()=>check(()=>cancel(parse(c.input),{domain:GF(c.p)}),c));
  it('handles the zero ring and explicit rational coefficient domains',()=>{
    expect(str(cancel(parse('x/(x+1)'),{modulus:1}))).toBe('nan');
    for(const domain of [ZZ,QQ])expect(str(cancel(parse('(x**2-1)/(x-1)'),{domain}))).toBe('x + 1');
    // General expression-domain cancellation is not implemented yet.
    expect(()=>cancel(x,{domain:'EX'})).toThrow(NotImplementedError);
  });
});
