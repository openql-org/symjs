// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/rischbase.ts (derivation, splitting factorization, Hermite reduction and the
// resultant reduction of the Risch algorithm), from SymPy's sympy/integrals/tests/test_risch.py.
// Expected values are SymPy 1.14's; where SymPy normalizes a polynomial over a ring and symjs over the
// field, the quotient (a fraction) is compared.

import { describe, expect, it } from 'vitest';
import { Lambda, Sym, parse, str } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { NotImplementedError } from '../../src/core/errors';
import { cancel } from '../../src/simplify/rational';
import { DifferentialExtension } from '../../src/integrals/risch';
import {
  DiffExtension,
  asPoly1t,
  canonicalRepresentation,
  derivation,
  derivationBasic,
  gcdexDiophantine,
  getCase,
  hermiteReduce,
  polynomialReduce,
  residueReduce,
  residueReduceDerivation,
  residueReduceToBasic,
  rootSumRational,
  splitfactor,
  splitfactorSqf,
} from '../../src/integrals/rischbase';
import { KPoly } from '../../src/integrals/rischpoly';

const [x, t, z, t1] = [new Sym('x'), new Sym('t'), new Sym('z'), new Sym('t1')];
const i = new Sym('i');
const P = (s: string, g: Sym = t): KPoly => KPoly.of(parse(s), g);
const E = (p: KPoly | Expr): string => str(p instanceof KPoly ? p.asExpr() : p);
const F = ([a, b]: readonly [KPoly, KPoly]): string => str(cancel(a.asExpr().div(b.asExpr())));
const DE = (...D: KPoly[]): DifferentialExtension => new DifferentialExtension({ D });

describe('gcdex_diophantine', () => {
  it('solves s*a + t*b = c (SymPy test_gcdex_diophantine)', () => {
    const [s1, t1_] = gcdexDiophantine(P('x**4 - 2*x**3 - 6*x**2 + 12*x + 15', x), P('x**3 + x**2 - 4*x - 4', x), P('x**2 - 1', x));
    expect([E(s1), E(t1_)]).toEqual(['-x**2/5 + 4*x/5 - 3/5', 'x**3/5 - 7*x**2/5 + 16*x/5 - 2']);
    const [s2, t2] = gcdexDiophantine(P('x**3 + 6*x + 7', x), P('x**2 + 3*x + 2', x), P('x + 1', x));
    expect([E(s2), E(t2)]).toEqual(['1/13', '3/13 - x/13']);
  });
});

describe('as_poly_1t', () => {
  it('splits an element of K[t, 1/t] (SymPy test_as_poly_1t)', () => {
    expect(asPoly1t(parse('2/t + t'), t, z).map(E)).toEqual(['t', '2*z']);
    expect(asPoly1t(parse('2/t + 3/t**2'), t, z).map(E)).toEqual(['0', '3*z**2 + 2*z']);
    expect(asPoly1t(parse('2/((exp(2) + 1)*t) + t'), t, z).map(E)).toEqual(['t', '2*z/(1 + exp(2))']);
    expect(asPoly1t(parse('0'), t, z).map(E)).toEqual(['0', '0']);
    expect(() => asPoly1t(parse('1/(t + 1)'), t, z)).toThrow(NotImplementedError);
  });
});

describe('derivation', () => {
  it('SymPy test_derivation', () => {
    const de = DE(P('1', x), P('-t**2 - 3/(2*x)*t + 1/(2*x)'));
    const p = P('4*x**4*t**5 + (-4*x**3 - 4*x**4)*t**4 + (-3*x**2 + 2*x**3)*t**3 + (2*x + 7*x**2 + 2*x**3)*t**2 + (1 - 4*x - 4*x**2)*t - 1 + 2*x');
    expect(derivation(p, de).equals(P('-20*x**4*t**6 + (2*x**3 + 16*x**4)*t**5 + (21*x**2 + 12*x**3)*t**4 + (7*x/2 - 25*x**2 - 12*x**3)*t**3 + (-5 - 15*x/2 + 7*x**2)*t**2 - (3 - 8*x - 10*x**2 - 4*x**3)/(2*x)*t + (1 - 4*x**2)/(2*x)'))).toBe(true);
    expect(derivation(P('1'), de).isZero).toBe(true);
    expect(derivation(P('t'), de).equals(de.d)).toBe(true);
    const de2 = new DifferentialExtension({ D: [P('1', x), P('1/x', t1), P('t')] });
    expect(E(derivation(P('x*t*t1'), de2))).toBe('t*(t1*x + t1 + 1)');
    expect(E(derivation(P('x*t*t1'), de2, true))).toBe('t*(t1 + 1)');
    const de3 = DE(P('1', x));
    expect(E(derivation(P('x', x), de3))).toBe('1');
    expect(E(derivation(P('x', x), de3, true))).toBe('0');
    expect(E(derivationBasic(parse('(x + 1)/(x - 1)'), de3))).toBe('-2/(x**2 - 2*x + 1)');
    expect(E(derivationBasic(parse('x'), de3, true))).toBe('0');
    const de4 = DE(P('1', x), P('t'));
    expect(E(derivationBasic(parse('(t + 1)/(t - 1)'), de4))).toBe('-2*t/(t**2 - 2*t + 1)');
    expect(E(derivationBasic(P('t + 1'), de4))).toBe('t');
    expect(E(derivationBasic(parse('x*t'), de4, true))).toBe('t');
  });
});

describe('splitfactor', () => {
  it('SymPy test_splitfactor', () => {
    const de = DE(P('1', x), P('-t**2 - 3/(2*x)*t + 1/(2*x)'));
    const p = P('4*x**4*t**5 + (-4*x**3 - 4*x**4)*t**4 + (-3*x**2 + 2*x**3)*t**3 + (2*x + 7*x**2 + 2*x**3)*t**2 + (1 - 4*x - 4*x**2)*t - 1 + 2*x');
    const [n, s] = splitfactor(p, de);
    expect(E(s)).toBe('t**2 + t/x + (1 - 2*x)/(4*x**2)');
    expect(n.mul(s).equals(p)).toBe(true);
    expect(splitfactor(P('x'), de).map(E)).toEqual(['x', '1']);
  });
  it('SymPy test_splitfactor with the coefficient derivation', () => {
    const r = KPoly.of(parse('-4*x**4*z**2 + 4*x**6*z**2 - z*x**3 - 4*x**5*z**3 + 4*x**3*z**3 + x**4 + z*x**5 - x**6'), t);
    const de2 = DE(P('1', x), P('1/x'));
    const [rn, rs] = splitfactor(r, de2, true);
    expect([E(rn), E(rs)]).toEqual(['x**4 - x**3*z - x**2 + x*z', '4*x**2*z**2 - x**2']);
    expect(splitfactor(P('0'), de2).map(E)).toEqual(['0', '1']);
    expect(splitfactorSqf(P('0'), de2)).toEqual([[[P('0'), 1]], []]);
    // the special part of a polynomial whose derivative is zero (Dt = 0)
    expect(splitfactor(P('t**2 + 1'), DE(P('1', x), P('0'))).map(E)).toEqual(['t**2 + 1', '1']);
  });
  it('splitfactor_sqf in z and over the monomials', () => {
    const de2 = DE(P('1', x), P('1/x'));
    const r = KPoly.of(parse('(z**2 - 1/4)*(x*z - 1)'), z);
    const [N, S] = splitfactorSqf(r, de2, true, z);
    expect(N.map(([p, k]) => `${E(p)}:${k}`)).toEqual(['x*z - 1:1']);
    expect(S.map(([p, k]) => `${E(p)}:${k}`)).toEqual(['z**2 - 1/4:1']);
    const [N2, S2] = splitfactorSqf(P('x*(t**2 + 1)'), de2);
    expect([N2.map(([p]) => E(p)), S2.map(([p]) => E(p))]).toEqual([['t**2*x + x'], []]);
  });
});

describe('canonical_representation and hermite_reduce', () => {
  it('SymPy test_canonical_representation', () => {
    const de = DE(P('1', x), P('1 + t**2'));
    const [q, s, n] = canonicalRepresentation(P('x - t'), P('t**2'), de);
    expect([E(q), F(s), F(n)]).toEqual(['0', '0', '(-t + x)/t**2']);
    const [q2, s2, n2] = canonicalRepresentation(P('t**5 + t**3 + x**2*t + 1'), P('(t**2 + 1)**3'), de);
    expect([E(q2), F(s2), F(n2)]).toEqual(['0', '(t**5 + t**3 + t*x**2 + 1)/(t**6 + 3*t**4 + 3*t**2 + 1)', '0']);
  });
  it('SymPy test_hermite_reduce', () => {
    const de = DE(P('1', x), P('t**2 + 1'));
    expect(hermiteReduce(P('x - t'), P('t**2'), de).map(F)).toEqual(['-x/t', '0', '-x']);
    const den = new DifferentialExtension({ D: [P('1', x), P('-t**2 - t/x - (1 - nu**2/x**2)')] });
    const r = hermiteReduce(P('x**2*t**5 + x*t**4 - nu**2*t**3 - x*(x**2 + 1)*t**2 - (x**2 - nu**2)*t - x**5/4'), P('x**2*t**4 + x**2*(x**2 + 2)*t**2 + x**2 + x**4 + x**6/4'), den);
    expect(r.map(F)).toEqual(['(-x**2 - 4)/(4*t**2 + 2*x**2 + 4)', '(-2*nu**2*t - t*x**4 - 2*x**3 - 2*x)/(2*t**2*x**2 + x**4 + 2*x**2)', '(t*x + 1)/x']);
  });
  it('SymPy test_hermite_reduce, primitive case', () => {
    const dp = DE(P('1', x), P('1/x'));
    const r2 = hermiteReduce(P('(-2 + 3*x)*t**3 + (-1 + x)*t**2 + (-4*x + 2*x**2)*t + x**2'), P('x*t**6 - 4*x**2*t**5 + 6*x**3*t**4 - 4*x**4*t**3 + x**5*t**2'), dp);
    expect(r2.map(([p, q]) => [E(p), E(q)])).toEqual([
      ['3*t**2 + t + 3*x', '3*t**4 - 9*t**3*x + 9*t**2*x**2 - 3*t*x**3'],
      ['0', '1'],
      ['0', '1'],
    ]);
    expect(hermiteReduce(P('-t**2 + 2*t + 2'), P('-x*t**2 + 2*x*t - x'), dp).map(F)).toEqual(['3/(t - 1)', '0', '1/x']);
  });
  it('SymPy test_hermite_reduce, a repeated cubic factor', () => {
    const dp = DE(P('1', x), P('1/x'));
    const r3 = hermiteReduce(P('-x**2*t**6 + (-1 - 2*x**3 + x**4)*t**3 + (-3 - 3*x**4)*t**2 - 2*x*t - x - 3*x**2'), P('x**4*t**6 - 2*x**2*t**3 + 1'), dp);
    expect(r3.map(F)).toEqual(['(t*x**3 + x**4 + 1)/(t**3*x**3 - x)', '0', '-1/x**2']);
  });
  it('SymPy test_polynomial_reduce', () => {
    const de = DE(P('1', x), P('1 + t**2'));
    expect(polynomialReduce(P('1 + x*t + t**2'), de).map(E)).toEqual(['t', 't*x']);
    expect(polynomialReduce(P('0'), de).map(E)).toEqual(['0', '0']);
  });
});

describe('residue_reduce', () => {
  it('SymPy test_residue_reduce', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('1/x')], Tfuncs: [Lambda(i, parse('log(i)', { symbols: [i] }))] });
    const show = ([H, b]: [[KPoly, KPoly][], boolean]) => [H.map(([s, h]) => [E(s), E(h)]), b];
    const a = P('2*t**2 - t - x**2');
    const d = P('t**3 - x**2*t');
    const noinv = residueReduce(a, d, de, z, false);
    expect(noinv[1]).toBe(false);
    expect(E(noinv[0][0]![0])).toBe('z**2 - 1/4');
    expect(show(residueReduce(a, d, de, z, true))).toEqual([[['z**2 - 1/4', 't + 2*x*z']], false]);
    const ans = residueReduce(P('-2/x'), P('t**2 - 1'), de, z, true);
    expect(show(ans)).toEqual([[['z**2 - 1', 't + z']], true]);
    expect(E(residueReduceToBasic(ans[0], de, z))).toBe('-log(log(x) - 1) + log(log(x) + 1)');
    // sum of z*D(t + z)/(t + z) over z = 1, -1 = -2/(x*(t**2 - 1))
    expect(E(residueReduceDerivation(ans[0], de, z))).toBe('-2/(t**2*x - x)');
    const den = new DifferentialExtension({ D: [P('1', x), P('-t**2 - t/x - (1 - nu**2/x**2)')] });
    expect(show(residueReduce(P('(-2*nu**2 - x**4)/(2*x**2)*t - (1 + x**2)/x'), P('t**2 + 1 + x**2/2'), den, z))).toEqual([[['z + 1/2', 't**2 + x**2/2 + 1']], true]);
    const dt = DE(P('1', x), P('1 + t**2'));
    expect(show(residueReduce(P('-2*x*t + 1 - x**2'), P('t**2 + 2*x*t + 1 + x**2'), dt, z))).toEqual([[['z**2 + 1/4', 't + x + 2*z']], true]);
    const de2 = DE(P('1', x), P('t'));
    expect(show(residueReduce(P('t'), P('t + sqrt(2)'), de2, z))).toEqual([[['z - 1', 't + sqrt(2)']], true]);
    expect(show(residueReduce(P('0'), P('t + 1'), de2, z))).toEqual([[], true]);
  });
  it('rootSumRational sums a rational function over the roots', () => {
    // the roots of z**3 - 2: sum of r**2 is 0, of 1/r is 0, of r**3 is 6
    const s = KPoly.of(parse('z**3 - 2'), z);
    expect(E(rootSumRational(s, KPoly.of(parse('z**2'), z), KPoly.one(z)))).toBe('0');
    expect(E(rootSumRational(s, KPoly.one(z), KPoly.of(parse('z'), z)))).toBe('0');
    expect(E(rootSumRational(KPoly.of(parse('z**2 - 3*z + 2'), z), KPoly.of(parse('z'), z), KPoly.one(z)))).toBe('3');
  });
});

describe('the differential extension state', () => {
  it('get_case', () => {
    expect([getCase(P('1', x), x), getCase(P('1/x'), t), getCase(P('t'), t), getCase(P('t**2 + 1'), t), getCase(P('t**3 + 2'), t), getCase(P('t + 1'), t)]).toEqual(['base', 'primitive', 'exp', 'tan', 'other_nonlinear', 'other_linear']);
  });
  it('a manual extension with monomials and kinds', () => {
    const de = new DiffExtension({ D: [P('1', x), P('t')], T: [x, t], x, exts: ['none', 'exp'], extargs: [parse('0'), x] });
    expect([de.indices('exp'), de.lower.map((s) => s.name), de.backSubstitution()]).toEqual([[1], ['x'], []]);
  });
});

describe('more residue reductions', () => {
  it('a residue of multiplicity 2 (SymPy agrees)', () => {
    const dp = DE(P('1', x), P('1/x'));
    const [H, b] = residueReduce(P('t*(3*(t**2 - 3) + 2*(t**2 - 2))'), P('3*x*(t**2 - 2)*(t**2 - 3)'), dp, z);
    expect([H.map(([s, h]) => [E(s), E(h)]), b]).toEqual([[['z**2 - 5*z/6 + 1/6', 't**2 + 6*z - 5']], true]);
  });
  it('derivations of expressions and polynomials by the coefficient derivation', () => {
    const de = DE(P('1', x), P('t'));
    expect(E(derivation(parse('x*t'), de, true))).toBe('t');
    expect(E(derivationBasic(P('x*t'), de, true))).toBe('t');
  });
  it('rootSumRational with a polynomial of degree 4', () => {
    // roots of z**4 - 1: the sum of r**3 is 0, of r**2 is 0, of 1 is 4
    expect(E(rootSumRational(KPoly.of(parse('z**4 - 1'), z), KPoly.of(parse('z**3 + z**2 + 1'), z), KPoly.one(z)))).toBe('4');
    expect(E(rootSumRational(KPoly.of(parse('z**4 - 10*z**2 + 1'), z), KPoly.of(parse('z**2'), z), KPoly.one(z)))).toBe('20');
  });
});
