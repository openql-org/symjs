// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References generated independently with SymPy 1.14.0 polys.dispersion.
import { expect, it } from 'vitest';
import { Sym } from '../../src/core/nodes';
import { parse } from '../../src/parsing/parser';
import { str } from '../../src/printing/str';
import { Poly } from '../../src/polys/sympoly';
import { dispersion, dispersionset } from '../../src/polys/dispersion';
import refs from './dispersion.references.json';
const x=new Sym('x'), y=new Sym('y');
for(const r of refs) it(`dispersion of ${r.a} against ${r.b ?? 'itself'}`,()=>{
  const f=Poly.from(parse(r.a),[x]),g=r.b === null ? undefined : Poly.from(parse(r.b),[x]);
  const shifts=[...dispersionset(f,g)].sort((a,b)=>a<b?-1:a>b?1:0);
  expect(shifts.map(String)).toEqual(r.shifts);
  expect(str(dispersion(f,g))).toBe(r.dispersion);
  for(const k of shifts) if(f.degree()>0 && (g??f).degree()>0) expect(f.gcd((g??f).shift(k)).degree()).toBeGreaterThan(0);
});
it('accepts expression inputs and checks the generators',()=>{
  expect(str(dispersion(parse('x**2-9')))).toBe('6');
  expect(str(dispersion(parse('x'),parse('x+2'),x))).toBe('-oo');
  expect(()=>dispersion(parse('x*y'))).toThrow(RangeError);
  expect(()=>dispersion(Poly.from(x,[x]),Poly.from(y,[y]))).toThrow(RangeError);
});

import continuationRefs from './continuation.references.json';
import '../../src/polys';
for(const row of continuationRefs.dispersion) it(`dispersion over QQ<${row.extension}>`,()=>{
  const extension=row.extension.map((e)=>parse(e)),f=Poly.from(parse(row.a),[x],{extension}),g=Poly.from(parse(row.b),[x],{extension});
  expect([...dispersionset(f,g)].map(Number).sort((a,b)=>a-b)).toEqual(row.shifts);
});

import { CRootOf, AlgebraicField, QQ, add, mul } from '../../src';
it('computes dispersion with indexed coefficients sharing the polynomial variable name',()=>{
  const r=CRootOf(parse('x**3-x-1'),0),K=new AlgebraicField(QQ,r),f=Poly.from(mul(add(x,mul(-1,r)),add(x,mul(-1,r),-3)),[x],{domain:K});
  expect([...dispersionset(f,f.shift(-2))].map(Number).sort((a,b)=>a-b)).toEqual([2,5]);
});
