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
