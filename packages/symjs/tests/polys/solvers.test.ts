// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References generated independently with SymPy 1.14.0 polys.solvers.
import { expect, it } from 'vitest';
import { Sym } from '../../src/core/nodes';
import { NonlinearError, InvariantError } from '../../src/core/errors';
import { isNoMatch } from '../../src/core/truth';
import { xreplace } from '../../src/core/traverse';
import { parse } from '../../src/parsing/parser';
import { str } from '../../src/printing/str';
import { QQ, ZZ } from '../../src/polys/domains';
import { GF } from '../../src/polys/domains/finitefield';
import { PolyRing } from '../../src/polys/rings';
import { eqsToMatrix, solveLinSys } from '../../src/polys/solvers';
import refs from './solvers.references.json';
const x=new Sym('x'),y=new Sym('y'),z=new Sym('z'),a=new Sym('a');
for(const r of refs) it(`solves ${r.inputs.join(', ')} over ${r.domain}`,()=>{
  const K=r.domain==='QQ'?QQ:r.domain==='GF(5)'?GF(5):ZZ.fracField(a);
  const R=new PolyRing([x,y,z],K),eqs=r.inputs.map((s)=>R.fromExpr(parse(s))),result=solveLinSys(eqs,R);
  if(r.result===null){expect(isNoMatch(result)).toBe(true);return;}
  expect(isNoMatch(result)).toBe(false);
  if(isNoMatch(result))return;
  expect(Object.fromEntries([...result].map(([k,v])=>[str(k),str(v)]))).toEqual(r.result);
  for(const eq of eqs)expect(R.fromExpr(xreplace(eq.asExpr(),[...result])).isZero).toBe(true);
});
it('builds domain matrices and validates linear systems',()=>{
  const A=eqsToMatrix([new Map([[x,1n],[y,1n]]),new Map([[x,1n],[y,-1n]])],[0n,-1n],[x,y],ZZ);
  expect(String(A)).toBe('DomainMatrix([[1, 1, 0], [1, -1, 1]], (2, 3), ZZ)');
  expect(()=>eqsToMatrix([new Map()],[],[x],QQ)).toThrow(RangeError);
  expect(()=>eqsToMatrix([new Map([[y,1n]])],[0n],[x],QQ)).toThrow(RangeError);
  const R=new PolyRing([x,y],QQ);
  expect(()=>solveLinSys([R.fromExpr(parse('x*y'))],R)).toThrow(NonlinearError);
  expect(()=>solveLinSys([],new PolyRing([x],ZZ))).toThrow(InvariantError);
});
