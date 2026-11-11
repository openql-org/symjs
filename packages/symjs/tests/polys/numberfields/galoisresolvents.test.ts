// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { getResolventByLookup, Poly, Sym, parseExpr as p } from '../../../src';
const x = new Sym('x');
it('evaluates rational resolvents and validates monicity', () => {
  expect(getResolventByLookup(Poly.from(p('x**4+1'), [x]), 1).map(String)).toEqual(['1','0','-4','0']);
  expect(() => getResolventByLookup(Poly.from(p('2*x**4+1'), [x]), 0)).toThrow('monic');
});
