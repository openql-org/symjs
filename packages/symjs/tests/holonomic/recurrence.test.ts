// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// The cases are SymPy 1.14.0's holonomic/tests/test_recurrence.py and the
// doctests of holonomic/recurrence.py, with the values SymPy 1.14.0 prints.

import { describe, expect, it } from 'vitest';
import { Sym, parseExpr as P, pow } from '../../src/index';
import { QQ, ZZ } from '../../src/polys/domains';
import { HolonomicSequence, RecurrenceOperator, RecurrenceOperators } from '../../src/holonomic';

const n = new Sym('n', { integer: true });
const [R, Sn] = RecurrenceOperators(QQ.oldPolyRing(n), 'Sn');
const n2 = pow(n, 2);

describe('RecurrenceOperators', () => {
  it('the algebra (doctests)', () => {
    const [RZ] = RecurrenceOperators(ZZ.oldPolyRing(n), 'Sn');
    expect(RZ.toString()).toBe('Univariate Recurrence Operator Algebra in intermediate Sn over the base ring ZZ[n]');
    expect(new RecurrenceOperator([0, 1, n2], R).toString()).toBe('(1)Sn + (n**2)Sn**2');
    expect(Sn.mul(n).toString()).toBe('(n + 1)Sn');
    expect(Sn.rmul(n).mul(n).add(1).sub(Sn.pow(2).mul(n)).toString()).toBe('(1) + (n**2 + n)Sn + (-n - 2)Sn**2');
    // the generator as a symbol, or the default Sn
    const S2 = new Sym('Sn', { commutative: false });
    expect(RecurrenceOperators(QQ.oldPolyRing(n), S2)[0].genSymbol).toBe(S2);
    expect(RecurrenceOperators(QQ.oldPolyRing(n))[0].equals(R)).toBe(true);
    expect(RZ.equals(R)).toBe(false);
  });
  it('test_RecurrenceOperator', () => {
    expect(Sn.mul(n).equals(Sn.rmul(P('n + 1').subs(new Sym('n'), n)))).toBe(true);
    expect(Sn.mul(n2).toString()).toBe('(n**2 + 2*n + 1)Sn');
    expect(Sn.pow(2).mul(n2).toString()).toBe('(n**2 + 4*n + 4)Sn**2');
    const p = Sn.pow(3).mul(n2).add(Sn.mul(n)).pow(2);
    expect(p.toString()).toBe('(n**2 + 3*n + 2)Sn**2 + (2*n**3 + 19*n**2 + 57*n + 52)Sn**4 + (n**4 + 18*n**3 + 117*n**2 + 324*n + 324)Sn**6');
  });
  it('test_RecurrenceOperatorEqPoly', () => {
    const rr = new RecurrenceOperator([n2, 0, 0], R);
    const rr2 = new RecurrenceOperator([n2, 1, n], R);
    expect(rr.equals(rr2)).toBe(false);
    expect(rr2.equals(rr2.listofpoly[0] ?? 0)).toBe(false);
    // SymPy compares the zero coefficients by identity and answers False (see its comment on PR 15799)
    expect(rr.equals(rr.listofpoly[0] ?? 0)).toBe(true);
    expect(rr.equals(n2)).toBe(true);
  });
  it('test_RecurrenceOperatorPow', () => {
    const rr = new RecurrenceOperator([n2, 0, 0], R);
    let a = new RecurrenceOperator([R.base.one], R);
    for (let m = 0; m < 10; m++) {
      expect(a.equals(rr.pow(m))).toBe(true);
      a = a.mul(rr);
    }
  });
  it('arithmetic with polynomials and expressions', () => {
    expect(Sn.add(Sn.parent.base.fromSympy(n)).toString()).toBe('(n) + (1)Sn');
    expect(Sn.sub(Sn.pow(2)).toString()).toBe('(1)Sn + (-1)Sn**2');
    expect(Sn.sub(n).toString()).toBe('(-n) + (1)Sn');
    expect(Sn.rsub(1).toString()).toBe('(1) + (-1)Sn');
    expect(Sn.neg().toString()).toBe('(-1)Sn');
    expect(Sn.pow(1)).toBe(Sn);
    expect(Sn.pow(0).toString()).toBe('(1)');
    expect(Sn.order).toBe(1);
  });
});

describe('HolonomicSequence', () => {
  it('printing and equality', () => {
    const r = Sn.rmul(P('n + 1').subs(new Sym('n'), n)).sub(1);
    const s = new HolonomicSequence(r, 1);
    expect(s.toString()).toBe('HolonomicSequence((-1) + (n + 1)Sn, n), u(0) = 1');
    expect(new HolonomicSequence(r).toString()).toBe('HolonomicSequence((-1) + (n + 1)Sn, n)');
    expect(s.equals(new HolonomicSequence(r, [1]))).toBe(true);
    expect(s.equals(new HolonomicSequence(r, [2]))).toBe(false);
    expect(s.equals(new HolonomicSequence(r, [1, 2]))).toBe(false);
    expect(s.equals(new HolonomicSequence(r))).toBe(true);
    expect(s.equals(new HolonomicSequence(Sn, 1))).toBe(false);
    const [, Sm] = RecurrenceOperators(QQ.oldPolyRing(new Sym('m')), 'Sn');
    expect(new HolonomicSequence(Sm).equals(new HolonomicSequence(Sn))).toBe(false);
  });
});
