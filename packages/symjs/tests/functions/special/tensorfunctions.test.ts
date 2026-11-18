// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special/tensorfunctions.ts.
// The Levi-Civita symbol. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Eijk, KroneckerDelta, LeviCivita, adjoint, conjugate, doit, isIntegerValued, latex, symbols } from '../../../src';

describe('LeviCivita', () => {
  const [i, j, k, x, y, a] = symbols('i j k x y a');
  it('evaluates integer arguments to the sign of the permutation', () => {
    expect(String(LeviCivita(1, 2, 3))).toBe('1');
    expect(String(LeviCivita(1, 3, 2))).toBe('-1');
    expect(String(LeviCivita(1, 2, 2))).toBe('0');
    expect(String(LeviCivita(3, 1, 2))).toBe('1');
    expect(String(LeviCivita(1, 2, 3, 4))).toBe('1');
    expect(String(LeviCivita(2, 1, 3, 4))).toBe('-1');
    // SymPy's product formula also for arguments that are not a permutation
    expect(String(LeviCivita(0, 2))).toBe('2');
    expect(String(LeviCivita(5))).toBe('1');
    expect(String(LeviCivita())).toBe('1');
  });
  it('is 0 for a repeated index and unevaluated otherwise', () => {
    expect(String(LeviCivita(i, j, k))).toBe('LeviCivita(i, j, k)');
    expect(String(LeviCivita(i, j, i))).toBe('0');
    expect(String(LeviCivita(1, x, x))).toBe('0');
    expect(String(LeviCivita(x, 1, 2))).toBe('LeviCivita(x, 1, 2)');
    expect(latex(LeviCivita(x, y, a))).toBe('\\varepsilon_{x y a}');
  });
  it('Eijk is LeviCivita', () => {
    expect(String(Eijk(1, 3, 2))).toBe('-1');
    expect(String(Eijk(i, j, k))).toBe('LeviCivita(i, j, k)');
  });
  it('evaluates the Vandermonde product and keeps both discrete symbols real under conjugation', () => {
    const symbol = LeviCivita(i, j, k);
    expect(String(doit(symbol))).toBe('(-i + j)*(-i + k)*(-j + k)/2');
    for (const expression of [symbol, KroneckerDelta(i, j)]) {
      expect(isIntegerValued(expression)).toBe(true);
      expect(conjugate(expression).equals(expression)).toBe(true);
      expect(adjoint(expression).equals(expression)).toBe(true);
    }
    expect(symbol.subs([[k, j]]).equals(0)).toBe(true);
  });
});

it('preserves Fermi restrictions when eliminating delta indices', async () => {
  const a = await import('../../../src');
  const p = new a.Sym('p'), q = new a.Sym('q');
  const i = new a.Sym('i',{belowFermi:true}), j = new a.Sym('j',{belowFermi:true});
  const u = new a.Sym('u',{aboveFermi:true}), v = new a.Sym('v',{aboveFermi:true});
  for (const [left,right,above,below,equal,preferred] of [
    [p,q,true,true,true,p], [p,i,false,true,false,i], [i,p,false,true,false,i],
    [p,u,true,false,false,u], [u,p,true,false,false,u], [i,j,false,true,true,i], [u,v,true,false,true,u],
    [p,a.add(q,1),true,true,true,p],
  ] as const) {
    const delta = new a.Fn('KroneckerDelta',[left,right]);
    expect(a.isAboveFermi(delta)).toBe(above);
    expect(a.isBelowFermi(delta)).toBe(below);
    expect(a.isOnlyAboveFermi(delta)).toBe(!below);
    expect(a.isOnlyBelowFermi(delta)).toBe(!above);
    expect(a.indicesContainEqualInformation(delta)).toBe(equal);
    expect(a.preferredIndex(delta)).toBe(preferred);
    expect(a.killableIndex(delta)).toBe(preferred === left ? right : left);
  }
  expect(() => a.isAboveFermi(p)).toThrow(TypeError);
  expect(() => a.isBelowFermi(a.sin(p))).toThrow(TypeError);
  expect(i.assumptions0.get('below_fermi')).toBe(true);
  expect(u.assumptions0.get('above_fermi')).toBe(true);
  expect(i.equals(new a.Sym('i'))).toBe(false);
  expect(u.equals(new a.Sym('u'))).toBe(false);
});

it('gives the Levi-Civita application its symbolic head and default assumptions', async () => {
  const sj = await import('../../../src');
  const [i, j] = symbols('i j');
  const e = LeviCivita(i, j);
  if (!(e instanceof sj.ExtensionExpr)) throw new TypeError('Levi-Civita application required');
  expect(e.func(1, 2).equals(1)).toBe(true);
  expect(e.isRealSelf()).toBe(true);
  expect(e.printLatex(String)).toBe('\\varepsilon_{i j}');
});
