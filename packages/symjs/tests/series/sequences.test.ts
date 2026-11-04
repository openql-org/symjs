// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/sequences.ts.
// Sequences (SymPy sympy.series.sequences). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

const P = (s: string): Expr => sj.parseExpr(s);
const [n, x, y] = [new sj.Sym('n'), new sj.Sym('x'), new sj.Sym('y')];
const oo = sj.S.Infinity;
const moo = sj.S.NegativeInfinity;
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v instanceof NoMatchResult ? 'None' : String(v));
const yf = sj.SymFunction('y');
const fib = (): sj.SeqBase => sj.RecursiveSeq(sj.add(yf(sj.sub(n, 1)), yf(sj.sub(n, 2))), yf(n), n, [0, 1]);

describe('SeqFormula and SeqPer', () => {
  it('build sequences like SymPy', () => {
    expect(show(sj.sequence(P('n**2'), [n, 0, 5]))).toBe('SeqFormula(n**2, (n, 0, 5))');
    expect(show(sj.sequence([1, 2, 3], [n, 0, 5]))).toBe('SeqPer((1, 2, 3), (n, 0, 5))');
    expect(show(sj.SeqFormula(P('n**2'), [0, 5]))).toBe('SeqFormula(n**2, (n, 0, 5))');
    expect(show(sj.SeqFormula(5))).toBe('SeqFormula(5, (_k, 0, oo))');
    expect(show(sj.SeqPer([1, 2]))).toBe('SeqPer((1, 2), (_k, 0, oo))');
    expect(show(sj.SeqPer([x, y], [n, 0, 3]))).toBe('SeqPer((x, y), (n, 0, 3))');
    expect(show(sj.SeqPer([P('n')], [n, 0, 3]))).toBe('SeqPer((n,), (n, 0, 3))');
    expect(show(sj.SeqPer([P('n'), 1], [0, 3]))).toBe('SeqPer((n, 1), (n, 0, 3))');
    expect(show(sj.SeqFormula(P('n**2'), [n, 5, 0]))).toBe('EmptySequence');
    expect(show(sj.SeqPer([1, 2], [n, 5, 0]))).toBe('EmptySequence');
    expect(() => sj.SeqFormula(P('m*n**2'))).toThrow('specify dummy variables for m*n**2');
    expect(() => sj.SeqFormula(P('n**2'), [n, moo, oo])).toThrow('Both the start and end value cannot be unbounded');
    expect(() => sj.SeqFormula(P('n**2'), [P('2*n'), 0, oo] as never)).toThrow('Invalid limits given');
  });

  it('give terms', () => {
    const s = sj.SeqFormula(P('n**2'), [n, 0, 5]);
    expect(show(s.coeff(3))).toBe('9');
    expect(() => s.coeff(7)).toThrow('Index 7 out of bounds Interval(0, 5)');
    expect(() => s.coeff(-1)).toThrow('out of bounds');
    expect(show(sj.SeqPer([1, 2, 3], [0, 5]).coeff(3))).toBe('1');
    expect(show(sj.SeqFormula(P('n**2')).slice(0, 5))).toBe('[0, 1, 4, 9, 16]');
    expect(show([...sj.SeqFormula(P('n**2'), [n, 0, 3])])).toBe('[0, 1, 4, 9]');
    expect(show(sj.SeqFormula(P('n**2'), [n, 0, 3]).slice())).toBe('[0, 1, 4, 9]');
    expect(show(sj.SeqFormula(P('n'), [n, 0, 9]).slice(6, 0, -2))).toBe('[6, 4, 2]');
    // unbounded below: counted back from the stop
    const back = sj.SeqPer([1, 2, 3], [n, moo, 0]);
    expect(show(back.slice(0, 5))).toBe('[1, 2, 3, 1, 2]');
    expect(show(back.coeff(-1))).toBe('2');
    expect(show(back.getItem(1))).toBe('2');
    const first: Expr[] = [];
    for (const t of sj.SeqFormula(P('n'))) {
      first.push(t);
      if (first.length === 3) break;
    }
    expect(show(first)).toBe('[0, 1, 2]');
    expect(show(sj.SeqFormula(P('n')).length)).toBe('oo');
    expect(show(sj.SeqFormula(P('n'), [n, 2, 5]).length)).toBe('4');
    expect(() => sj.SeqPer([1, 2]).coeff(P('1/2'))).toThrow('sequence index must be an integer');
    // a symbolic point is not checked against the bounds
    expect(show(sj.SeqFormula(P('n**2')).coeff(x))).toBe('x**2');
  });

  it('combine term-wise', () => {
    expect(show(sj.SeqFormula(P('n**2')).coeffMul(2))).toBe('SeqFormula(2*n**2, (n, 0, oo))');
    expect(show(sj.SeqFormula(P('n**2'), [n, 0, 5]).add(sj.SeqFormula(P('n'), [n, 3, oo])))).toBe('SeqFormula(n**2 + n, (n, 3, 5))');
    expect(show(sj.SeqFormula(P('n**2'), [n, 0, 5]).sub(sj.SeqFormula(P('n'), [n, 3, oo])))).toBe('SeqFormula(n**2 - n, (n, 3, 5))');
    expect(show(sj.SeqFormula(P('n**2')).neg())).toBe('SeqFormula(-n**2, (n, 0, oo))');
    expect(show(sj.SeqFormula(P('n**2')).mul(sj.SeqFormula(P('n'))))).toBe('SeqFormula(n**3, (n, 0, oo))');
    expect(show(sj.SeqPer([1, 2], [n, 0, oo]).coeffMul(3))).toBe('SeqPer((3, 6), (n, 0, oo))');
    expect(show(sj.SeqAdd(sj.SeqPer([1, 2, 3], [n, 0, oo]), sj.SeqPer([1, 2], [n, 0, oo])))).toBe('SeqPer((2, 4, 4, 3, 3, 5), (n, 0, oo))');
    expect(show(sj.SeqMul(sj.SeqPer([1, 2, 3], [n, 0, oo]), sj.SeqPer([1, 2], [n, 0, oo])))).toBe('SeqPer((1, 4, 3, 2, 2, 6), (n, 0, oo))');
    expect(show((sj.SeqFormula(P('(n + 1)**2')) as sj.SeqFormulaNode).expand())).toBe('SeqFormula(n**2 + 2*n + 1, (n, 0, oo))');
    expect(() => sj.SeqFormula(P('n')).add(1)).toThrow('cannot add sequence and 1');
    expect(() => sj.SeqFormula(P('n')).sub(1)).toThrow('cannot subtract sequence and 1');
    expect(() => sj.SeqFormula(P('n')).mul(1)).toThrow('cannot multiply sequence and 1');
  });

  it('are expressions with a bound variable', () => {
    const s = sj.SeqFormula(P('n**2 + x'), [n, 0, 5]);
    expect(show([...sj.freeSymbols(s)])).toBe('[x]');
    expect(show(sj.subs(s, [[x, 1]]))).toBe('SeqFormula(n**2 + 1, (n, 0, 5))');
    expect(show(sj.subs(sj.SeqPer([x, 2], [n, 0, 5]), [[x, 1]]))).toBe('SeqPer((1, 2), (n, 0, 5))');
    expect(show(s.variables)).toBe('[n]');
    expect(show(s.interval)).toBe('Interval(0, 5)');
  });
});

describe('SeqAdd, SeqMul and EmptySequence', () => {
  it('reduce like SymPy', () => {
    expect(show(sj.EmptySequence.coeffMul(-1))).toBe('EmptySequence');
    expect(show(sj.SeqAdd(sj.SeqFormula(P('n**3')), sj.SeqFormula(P('n**2'))))).toBe('SeqFormula(n**3 + n**2, (n, 0, oo))');
    expect(show(sj.SeqAdd(sj.SeqPer([1, 2], [n, 0, 5]), sj.SeqPer([1, 2], [n, 6, 10])))).toBe('EmptySequence');
    expect(show(sj.SeqAdd(sj.SeqPer([1, 2], [n, 0, oo]), sj.EmptySequence))).toBe('SeqPer((1, 2), (n, 0, oo))');
    expect(show(sj.SeqAdd(sj.SeqPer([1, 2], [n, 0, oo]), sj.SeqFormula(P('n**2'), [n, 0, oo])))).toBe('SeqAdd(SeqFormula(n**2, (n, 0, oo)), SeqPer((1, 2), (n, 0, oo)))');
    expect(show(sj.SeqMul(sj.SeqFormula(P('n**3')), sj.SeqFormula(P('n**2'))))).toBe('SeqFormula(n**5, (n, 0, oo))');
    expect(show(sj.SeqMul(sj.SeqPer([1, 2], [n, 0, 5]), sj.SeqPer([1, 2], [n, 6, 10])))).toBe('EmptySequence');
    expect(show(sj.SeqMul(sj.SeqPer([1, 2], [n, 0, oo]), sj.EmptySequence))).toBe('EmptySequence');
    expect(show(sj.SeqMul(sj.SeqPer([1, 2], [n, 0, oo]), sj.SeqFormula(P('n**2'))))).toBe('SeqMul(SeqFormula(n**2, (n, 0, oo)), SeqPer((1, 2), (n, 0, oo)))');
    expect(show(sj.SeqAdd(sj.SeqFormula(P('n**2')), sj.SeqFormula(P('n**3')), sj.SeqPer([1, 2])))).toBe('SeqAdd(SeqPer((1, 2), (_k, 0, oo)), SeqFormula(n**3 + n**2, (n, 0, oo)))');
    expect(show(sj.SeqAdd(sj.SeqAdd(sj.SeqFormula(P('n**2')), sj.SeqPer([1, 2])), sj.SeqFormula(P('n'))))).toBe('SeqAdd(SeqPer((1, 2), (_k, 0, oo)), SeqFormula(n**2 + n, (n, 0, oo)))');
    expect(show(sj.SeqAdd([sj.SeqFormula(P('n**2'), [n, 0, 4]), sj.SeqPer([1, 2], [n, 2, 9])]))).toBe('SeqAdd(SeqFormula(n**2, (n, 0, 4)), SeqPer((1, 2), (n, 2, 9)))');
    expect(show(sj.SeqAdd())).toBe('EmptySequence');
    expect(show(sj.SeqMul())).toBe('EmptySequence');
    // ties broken by the printed form
    expect(show(sj.SeqAdd(sj.SeqPer([2, 1], [n, 0, oo]), sj.SeqFormula(P('n**2'), [n, 0, oo]), sj.SeqFormula(P('n**3'), [n, 0, oo]).mul(sj.SeqPer([1, 3], [n, 0, oo]))))).toBe(
      'SeqAdd(SeqFormula(n**2, (n, 0, oo)), SeqPer((2, 1), (n, 0, oo)), SeqMul(SeqFormula(n**3, (n, 0, oo)), SeqPer((1, 3), (n, 0, oo))))',
    );
  });

  it('give terms', () => {
    const a = sj.SeqAdd(sj.SeqFormula(P('n**2')), sj.SeqPer([1, 2]));
    const m = sj.SeqMul(sj.SeqFormula(P('n**2')), sj.SeqPer([1, 2]));
    expect(show(a.coeff(3))).toBe('11');
    expect(show(m.coeff(3))).toBe('18');
    expect(show(a.length)).toBe('oo');
    expect(show(a.start)).toBe('0');
    expect(show(a.variables)).toBe('[n, _k]');
    expect(show(sj.subs(a, [[x, 1]]))).toBe(show(a));
    expect(show(sj.subs(m, [[x, 1]]))).toBe(show(m));
    // coeff_mul is not defined for a sum or product of sequences: SymPy raises (AttributeError from
    // Mul(seq, coeff)) for a.coeff_mul(2), -a and SeqFormula(n**2) - a
    expect(() => a.coeffMul(2)).toThrow('cannot multiply SeqAdd and 2');
    expect(() => m.coeffMul(2)).toThrow('cannot multiply SeqMul and 2');
    expect(() => a.neg()).toThrow('cannot multiply SeqAdd and -1');
    expect(() => sj.SeqFormula(P('n**2')).sub(a)).toThrow(TypeError);
  });

  it('EmptySequence has no terms', () => {
    const e = sj.EmptySequence;
    expect(show(e.length)).toBe('0');
    expect(show([...e])).toBe('[]');
    expect(show(e.interval)).toBe('EmptySet');
    expect(show(e.start)).toBe('oo');
    expect(show(e.stop)).toBe('-oo');
    expect(() => e.coeff(0)).toThrow('out of bounds');
    expect(show(sj.subs(e, [[x, 1]]))).toBe('EmptySequence');
    // SymPy fails on EmptySequence + seq (a Singleton class is not a sequence)
    expect(show(e.add(sj.SeqFormula(P('n'))))).toBe('SeqFormula(n, (n, 0, oo))');
  });
});

describe('RecursiveSeq', () => {
  it('computes the terms of a recurrence', () => {
    const f = fib();
    expect(show(f.coeff(3))).toBe('2');
    expect(show(f)).toBe('RecursiveSeq(y(n - 2) + y(n - 1), y(n), n, (0, 1), 0)');
    expect(show(f.slice(0, 6))).toBe('[0, 1, 1, 2, 3, 5]');
    expect(show(f.coeff(7))).toBe('13');
    expect((f as sj.RecursiveSeqNode).degree).toBe(2);
    expect(show((f as sj.RecursiveSeqNode).recurrence)).toBe('y(n - 2) + y(n - 1)');
    expect(show((f as sj.RecursiveSeqNode).initial)).toBe('[0, 1]');
    expect(show(f.interval)).toBe('Interval(0, oo)');
    const g = sj.RecursiveSeq(sj.add(yf(sj.sub(n, 1)), 1), yf(n), n);
    expect(show(g)).toBe('RecursiveSeq(y(n - 1) + 1, y(n), n, (_c_0,), 0)');
    expect(show(g.slice(0, 3))).toBe('[_c_0, _c_0 + 1, _c_0 + 2]');
    // SymPy 1.14 gives [3, 24, 12, 24] (its cache is indexed from 0, not from the start 2): 3, 6, 12, 24 is y(n) = 2*y(n - 1)
    const h = sj.RecursiveSeq(sj.mul(2, yf(sj.sub(n, 1))), yf(n), n, [3], 2);
    expect(show(h.slice(0, 4))).toBe('[3, 6, 12, 24]');
    expect(show(h.coeff(4))).toBe('12');
    expect(show(sj.subs(h, [[x, 1]]))).toBe(show(h));
  });

  it('combines with other sequences by the general rules', () => {
    const f = fib();
    expect(show(f.variables)).toBe('[]');
    // SymPy raises for coeff_mul and negation of a RecursiveSeq (AttributeError from Mul(seq, coeff))
    expect(() => f.coeffMul(2)).toThrow('cannot multiply RecursiveSeq and 2');
    expect(show(sj.SeqMul(f, sj.SeqFormula(P('n'))).slice(0, 5))).toBe('[0, 1, 2, 6, 12]');
    expect(show(sj.SeqAdd(f, sj.SeqFormula(P('n'))).slice(0, 5))).toBe('[0, 2, 3, 5, 7]');
    // ordered by start, then by size, then by printed form
    const g = sj.RecursiveSeq(sj.add(yf(sj.sub(n, 1)), yf(sj.sub(n, 2))), yf(n), n, [1, 1]);
    expect(show(sj.SeqAdd(f, g))).toBe(show(sj.SeqAdd(g, f)));
    expect(show(sj.SeqAdd(f, f).slice(0, 4))).toBe('[0, 2, 2, 4]');
    expect(show(sj.SeqAdd(g, f))).toBe('SeqAdd(RecursiveSeq(y(n - 2) + y(n - 1), y(n), n, (0, 1), 0), RecursiveSeq(y(n - 2) + y(n - 1), y(n), n, (1, 1), 0))');
    expect(show(sj.SeqAdd(sj.SeqMul(f, sj.SeqFormula(P('n'))), sj.SeqPer([1, 2], [n, 0, oo])))).toBe(
      'SeqAdd(SeqPer((1, 2), (n, 0, oo)), SeqMul(SeqFormula(n, (n, 0, oo)), RecursiveSeq(y(n - 2) + y(n - 1), y(n), n, (0, 1), 0)))',
    );
    expect(show(sj.SeqAdd(sj.SeqFormula(P('n'), [n, 3, oo]), sj.SeqPer([1, 2], [n, 1, oo]), sj.SeqMul(f, sj.SeqFormula(P('n'), [n, 2, oo]))))).toBe(
      'SeqAdd(SeqPer((1, 2), (n, 1, oo)), SeqMul(RecursiveSeq(y(n - 2) + y(n - 1), y(n), n, (0, 1), 0), SeqFormula(n, (n, 2, oo))), SeqFormula(n, (n, 3, oo)))',
    );
    expect(show(sj.subs(sj.RecursiveSeq(sj.mul(x, yf(sj.sub(n, 1))), yf(n), n, [x]), [[x, 2]]))).toBe('RecursiveSeq(2*y(n - 1), y(n), n, (2,), 0)');
    expect(show(sj.subs(sj.SeqAdd(sj.SeqFormula(P('n**2 + x'), [n, 0, oo]), sj.SeqPer([1, 2])), [[x, 1]]))).toBe('SeqAdd(SeqPer((1, 2), (_k, 0, oo)), SeqFormula(n**2 + 1, (n, 0, oo)))');
    expect(show(sj.subs(sj.SeqMul(sj.SeqFormula(P('n**2 + x'), [n, 0, oo]), sj.SeqPer([1, 2])), [[x, 1]]))).toBe('SeqMul(SeqPer((1, 2), (_k, 0, oo)), SeqFormula(n**2 + 1, (n, 0, oo)))');
    expect(show((sj.EmptySequence as sj.EmptySequenceNode).withArgs())).toBe('EmptySequence');
  });

  it('rejects malformed recurrences', () => {
    expect(() => sj.RecursiveSeq(yf(sj.sub(n, 1)), n, n)).toThrow('recurrence sequence must be an applied undefined function, found `n`');
    expect(() => sj.RecursiveSeq(yf(sj.sub(n, 1)), yf(n), sj.mul(x, n))).toThrow('recurrence variable must be a symbol, found `n*x`');
    expect(() => sj.RecursiveSeq(yf(sj.sub(n, 1)), yf(x), n)).toThrow('recurrence sequence does not match symbol');
    expect(() => sj.RecursiveSeq(yf(sj.add(n, 1)), yf(n), n)).toThrow('Recurrence should have constant, negative, integer shifts (found y(n + 1))');
    expect(() => sj.RecursiveSeq(yf(n, 1), yf(n), n)).toThrow('Recurrence should be in a single variable');
    expect(() => sj.RecursiveSeq(yf(sj.sub(n, 1)), yf(n), n, [1, 2])).toThrow('Number of initial terms must equal degree');
  });
});

describe('find_linear_recurrence', () => {
  it('finds the recurrences of SymPy', () => {
    expect(show(sj.sequence(P('n**2')).findLinearRecurrence(10, 2))).toBe('[]');
    expect(show(sj.sequence(P('n**2')).findLinearRecurrence(10))).toBe('[3, -3, 1]');
    expect(show(sj.sequence(P('2**n')).findLinearRecurrence(10))).toBe('[2]');
    expect(show(sj.sequence(P('2**n')).findLinearRecurrence(2))).toBe('[2]');
    expect(show(sj.sequence(P('23*n**4+91*n**2')).findLinearRecurrence(10))).toBe('[5, -10, 10, -5, 1]');
    expect(show(sj.sequence(P('sqrt(5)*(((1 + sqrt(5))/2)**n - (-(1 + sqrt(5))/2)**(-n))/5')).findLinearRecurrence(10))).toBe('[1, 1]');
    expect(show(sj.sequence(P('x+y*(-2)**(-n)'), [n, 0, oo]).findLinearRecurrence(30))).toBe('[1/2, 1/2]');
    expect(show(sj.sequence(P('factorial(n)')).findLinearRecurrence(8))).toBe('[16, -72, 96, -24]');
    expect(show(sj.sequence(sj.lucas(n)).findLinearRecurrence(15, undefined, x))).toBe('[[1, 1], (x - 2)/(x**2 + x - 1)]');
    expect(show(sj.sequence(sj.fibonacci(n)).findLinearRecurrence(10, undefined, x))).toBe('[[1, 1], -x/(x**2 + x - 1)]');
    expect(show(sj.sequence(P('n**2')).findLinearRecurrence(10, 1, x))).toBe('[[], None]');
    expect(show(sj.SeqPer([1, 0, 0]).findLinearRecurrence(9, undefined, x))).toBe('[[0, 0, 1], -1/(x**3 - 1)]');
  });
});
