// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/rde.ts (the Risch differential equation), from SymPy's
// sympy/integrals/tests/test_rde.py (examples of Bronstein's book). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Sym, parse, str } from '../../src';
import { NotImplementedError } from '../../src/core/errors';
import { DifferentialExtension } from '../../src/integrals/risch';
import {
  boundDegree,
  cancelExp,
  cancelPrimitive,
  noCancelBLarge,
  noCancelBSmall,
  noCancelEqual,
  normalDenom,
  num,
  orderAt,
  orderAtOo,
  rischDE,
  rischDEOrNone,
  solvePolyRde,
  spde,
  specialDenom,
  weakNormalizer,
} from '../../src/integrals/rde';
import { NonElementaryIntegralException } from '../../src/integrals/rischbase';
import { KPoly } from '../../src/integrals/rischpoly';

const [x, t, z, t0, t1s] = [new Sym('x'), new Sym('t'), new Sym('z'), new Sym('t0'), new Sym('t1')];
const P = (s: string, g: Sym = t): KPoly => KPoly.of(parse(s), g);
const E = (p: KPoly): string => str(p.asExpr());
const DE = (...D: KPoly[]): DifferentialExtension => new DifferentialExtension({ D });

describe('order_at', () => {
  it('orders at t, at t**2 + 1 and at infinity', () => {
    const a = P('t**4');
    const b = P('(t**2 + 1)**3*t');
    const c = P('(t**2 + 1)**6*t');
    const d = P('(t**2 + 1)**10*t**10');
    const e = P('(t**2 + 1)**100*t**37');
    const p1 = P('t');
    const p2 = P('1 + t**2');
    expect([a, b, c, d, e].map((f) => orderAt(f, p1, t))).toEqual([4, 1, 1, 10, 37]);
    expect([a, b, c, e].map((f) => orderAt(f, p2, t))).toEqual([0, 3, 6, 100]);
    expect(orderAt(P('0'), p1, t)).toBe(Infinity);
    expect(orderAtOo(P('t**2 - 1'), P('t + 1'))).toBe(-1);
    expect(orderAtOo(P('t - 1'), P('1'))).toBe(-1);
    expect(orderAtOo(P('0'), P('1'))).toBe(Infinity);
  });
});

describe('weak_normalizer', () => {
  it('finds the weak normalizer (exp case)', () => {
    const de = DE(P('1', x), P('t'));
    const r = weakNormalizer(P('(1 + x)*t**5 + 4*t**4 + (-1 - 3*x)*t**3 - 4*t**2 + (-2 + 2*x)*t'), P('t**4 - 3*t**2 + 2'), de, z);
    expect(E(r[0])).toBe('t**5 - t**4 - 4*t**3 + 4*t**2 + 4*t - 4');
    expect([E(r[1][0]), E(r[1][1])]).toEqual(['t**2*(x + 1) + t*x', 't + 1']);
    const r2 = weakNormalizer(r[1][0], r[1][1], de);
    expect(r2[0].isOne).toBe(true);
    const r3 = weakNormalizer(P('1 + t**2'), P('t**2 - 1'), de, z);
    expect([E(r3[0]), E(r3[1][0]), E(r3[1][1])]).toEqual(['t**4 - 2*t**2 + 1', '1 - 3*t**2', 't**2 - 1']);
    expect(weakNormalizer(r3[1][0], r3[1][1], de, z)[0].isOne).toBe(true);
  });
  it('finds the weak normalizer (tan case)', () => {
    const de = DE(P('1', x), P('1 + t**2'));
    const r = weakNormalizer(P('1 + t**2'), P('t'), de, z);
    expect([E(r[0]), E(r[1][0]), E(r[1][1])]).toEqual(['t', '0', '1']);
    expect(weakNormalizer(r[1][0], r[1][1], de, z)[0].isOne).toBe(true);
  });
  it('uses only the positive integer roots of the resultant', () => {
    const de = DE(P('1', x), P('t'));
    // the root z = x is not an integer
    expect(weakNormalizer(P('x*t'), P('t - 1'), de, z).flat().map(E)).toEqual(['1', 't*x', 't - 1']);
    expect(weakNormalizer(P('t'), P('t - 1'), de, z).flat().map(E)).toEqual(['t - 1', '0', '1']);
  });
});

describe('normal_denom', () => {
  it('raises when there is no solution and splits the denominator', () => {
    expect(() => normalDenom(P('1', x), P('1', x), P('1', x), P('x', x), DE(P('1', x)))).toThrow(NonElementaryIntegralException);
    const [a, [ba, bd], [ca, cd], h] = normalDenom(P('t**2 + 1'), P('1'), P('1'), P('t**2'), DE(P('1', x), P('t**2 + 1')));
    expect([E(a), E(ba), E(bd), E(ca), E(cd), E(h)]).toEqual(['t', 't**3 - t**2 + t - 1', '1', '1', '1', 't']);
  });
});

describe('special_denom', () => {
  it('exp case', () => {
    const r = specialDenom(P('1'), P('t**2'), P('1'), P('t**2 - 1'), P('t'), DE(P('1', x), P('t')));
    expect(r.map(E)).toEqual(['1', 't**2 - 1', 't**2 - 1', 't']);
  });
  it('exp case with nb = 0 (parametric logarithmic derivative)', () => {
    const t1 = new Sym('t1');
    const de = DE(P('1', x), P('-2*x*t0', t0), KPoly.of(parse('I*k*t1'), t1));
    de.decrementLevel();
    const r = specialDenom(P('1', t0), P('I*k', t0), P('1', t0), P('t0', t0), P('1', t0), de);
    expect(r.map(E)).toEqual(['1', 'I*k', 't0', '1']);
  });
  it('primitive and base cases, tan and unknown cases', () => {
    const de = DE(P('1', x), P('1/x'));
    expect(specialDenom(P('1'), P('t**2'), P('t'), P('t**2 - 1'), P('t'), de).map(E)).toEqual(['1', 't', 't', '1']);
    expect(() => specialDenom(P('1'), P('t**2'), P('1'), P('t**2 - 1'), P('t'), de, 'tan')).toThrow(NotImplementedError);
    expect(() => specialDenom(P('1'), P('t**2'), P('1'), P('t**2 - 1'), P('t'), de, 'unrecognized_case')).toThrow(RangeError);
  });
});

describe('bound_degree', () => {
  it('bounds the degree in the base, tan, primitive and exp cases', () => {
    expect(boundDegree(P('1', x), P('-2*x', x), P('1', x), DE(P('1', x)))).toBe(0);
    expect(boundDegree(P('x', x), P('-2', x), P('x**3', x), DE(P('1', x)))).toBe(3);
    expect(boundDegree(P('t'), P('(t - 1)*(t**2 + 1)'), P('1'), DE(P('1', x), P('t**2 + 1')))).toBe(0);
    expect(boundDegree(P('t'), P('-2*t**2'), P('t**5'), DE(P('1', x), P('t**2 + 1')))).toBe(3);
    const t1 = new Sym('t');
    expect(boundDegree(P('t**2'), P('-(1/x**2*t**2 + 1/x)'), P('(2*x - 1)*t**4 + (t0 + x)/x*t**3 - (t0 + 4*x**2)/2*x*t**2 + x*t'), new DifferentialExtension({ D: [P('1', x), P('t0/x**2', t0), KPoly.of(parse('1/x'), t1)] }))).toBe(3);
    expect(() => boundDegree(P('1'), P('1'), P('1'), DE(P('1', x), P('t')), 'unknown')).toThrow(RangeError);
  });
  it('primitive case with db = da and db = da - 1', () => {
    // SymPy 1.14 fails on these (SympifyError, TypeError): it takes the derivative of z = 1/x as a
    // polynomial in x, and compares a Poly with an int. The bounds are those of Bronstein's algorithm.
    const dp = DE(P('1', x), P('1/x'));
    expect(boundDegree(P('x'), P('1'), P('t'), dp)).toBe(2);
    expect(boundDegree(P('1'), P('2/x'), P('t**2'), dp)).toBe(3);
    expect(boundDegree(P('t'), P('x'), P('t**2'), dp)).toBe(2);
    expect(boundDegree(P('t**2'), P('1'), P('t**2'), dp)).toBe(1);
    expect(boundDegree(P('1'), P('t'), P('t**2'), dp)).toBe(1);
  });
  it('exp case with da = db', () => {
    const de = DE(P('1', x), P('t'));
    expect(boundDegree(P('1'), P('1'), P('t**2'), de)).toBe(2);
    expect(boundDegree(P('1'), P('2'), P('t**2'), de)).toBe(2);
    expect(boundDegree(P('1'), P('1'), P('1'), DE(P('1', x), P('t**2 + t')))).toBe(0);
  });
});

describe('spde', () => {
  it('reduces the problem (SymPy test_spde)', () => {
    expect(() => spde(P('t'), P('(t - 1)*(t**2 + 1)'), P('1'), 0, DE(P('1', x), P('t**2 + 1')))).toThrow(NonElementaryIntegralException);
    const r1 = spde(P('t**2 + x*t*2 + x**2'), P('t**2/x**2 + (2/x - 1)*t'), P('t**2/x**2 + (2/x - 1)*t'), 0, DE(P('1', x), P('t')));
    expect([E(r1[0]), E(r1[1]), r1[2], E(r1[3]), E(r1[4])]).toEqual(['0', '0', 0, '0', '1']);
    const de2 = new DifferentialExtension({ D: [P('1', x), P('t0/x**2', t0), P('1/x')] });
    const r2 = spde(P('t**2'), P('-t**2/x**2 - 1/x'), P('(2*x - 1)*t**4 + (t0 + x)/x*t**3 - (t0 + 4*x**2)/(2*x)*t**2 + x*t'), 3, de2);
    expect([E(r2[0]), E(r2[1]), r2[2], E(r2[3])]).toEqual(['0', '0', 0, '0']);
    expect(r2[4].sub(P('t0*t**2/2 + x**2*t**2 - x**2*t')).isZero).toBe(true);
    const de = DE(P('1', x));
    const r3 = spde(P('x**2 + x + 1', x), P('-2*x - 1', x), P('x**5/2 + 3*x**4/4 + x**3 - x**2 + 1', x), 4, de);
    expect([E(r3[0]), E(r3[1]), r3[2], E(r3[3]), E(r3[4])]).toEqual(['0', 'x/2 - 1/4', 2, 'x**2 + x + 1', '5*x/4']);
    expect(() => spde(P('(t - 1)*(t**2 + 1)**2'), P('(t - 1)*(t**2 + 1)'), P('1'), 0, DE(P('1', x), P('1')))).toThrow(NonElementaryIntegralException);
    const r4 = spde(P('x**2 - x', x), P('1', x), P('9*x**4 - 10*x**3 + 2*x**2', x), 4, de);
    expect([E(r4[0]), E(r4[1]), r4[2], E(r4[3]), E(r4[4])]).toEqual(['0', '0', 0, '0', '3*x**3 - 2*x**2']);
    const r5 = spde(P('x**2 - x', x), P('x**2 - 5*x + 3', x), P('x**7 - x**6 - 2*x**4 + 3*x**3 - x**2', x), 5, de);
    expect([E(r5[0]), E(r5[1]), r5[2], E(r5[3]), E(r5[4])]).toEqual(['1', 'x + 1', 1, 'x**4 - x**3', 'x**3 - x**2']);
  });
});

describe('solve_poly_rde', () => {
  it('no cancellation cases (SymPy test_solve_poly_rde_no_cancel)', () => {
    expect(E(solvePolyRde(P('t**2 + 1'), P('t**3 + (x + 1)*t**2 + t + x + 2'), Infinity, DE(P('1', x), P('1 + t**2'))))).toBe('t + x');
    expect(E(solvePolyRde(P('0', x), P('x/2 - 1/4', x), Infinity, DE(P('1', x))))).toBe('x**2/4 - x/4');
    expect(E(solvePolyRde(P('2'), P('t**2 + 2*t + 3'), 1, DE(P('1', x), P('t**2 + 1'))))).toBe('t + 1');
    const r = noCancelEqual(P('1 - t'), P('t**3 + t**2 - 2*x*t - 2*x'), Infinity, DE(P('1', x), P('t**2 + 1')));
    if (r instanceof KPoly) throw new TypeError('a reduced problem expected');
    expect([E(r[0]), r[1], E(r[2])]).toEqual(['t**2', 1, 't*(-2*x - 2) - 2*x']);
  });
  it('the equal-degree case reduces to a cancellation case (not implemented for tan)', () => {
    const de = DE(P('1', x), P('t**2 + 1'));
    expect(() => solvePolyRde(P('1 - t'), P('t**3 + t**2 + 3*t + 1'), 3, de)).toThrow(NotImplementedError);
  });
  it('no_cancel_b_large and no_cancel_b_small raise without a solution', () => {
    const de = DE(P('1', x), P('t'));
    expect(() => noCancelBLarge(P('t**2'), P('t'), 3, de)).toThrow(NonElementaryIntegralException);
    const de2 = DE(P('1', x), P('t**2 + 1'));
    expect(() => noCancelBSmall(P('0'), P('t**5'), 1, de2)).toThrow(NonElementaryIntegralException);
    expect(() => noCancelBSmall(P('0'), P('1'), 0, de2)).toThrow(NonElementaryIntegralException);
    expect(() => noCancelEqual(P('1 - t'), P('t**7'), 1, de2)).toThrow(NonElementaryIntegralException);
    const r = noCancelEqual(P('-t'), P('t'), 3, de2);
    if (r instanceof KPoly) throw new TypeError('a reduced problem expected');
    expect([E(r[0]), r[1], E(r[2])]).toEqual(['0', 1, 't']);
    expect(() => solvePolyRde(P('0'), P('1'), 1, de2)).toThrow(NonElementaryIntegralException);
  });
  it('the remaining cases are not implemented', () => {
    expect(() => solvePolyRde(P('0'), P('t'), 2, DE(P('1', x), P('t')))).toThrow(NotImplementedError);
    expect(() => solvePolyRde(P('1'), P('t'), 2, DE(P('1', x), P('t + 1')))).toThrow(NotImplementedError);
  });
});

describe('cancellation cases', () => {
  it('cancel_exp and cancel_primitive (SymPy test_solve_poly_rde_cancel)', () => {
    const de = DE(P('1', x), P('t'));
    expect(E(cancelExp(P('2*x'), P('2*x'), 0, de))).toBe('1');
    expect(E(cancelExp(P('2*x'), P('(1 + 2*x)*t'), 1, de))).toBe('t');
    expect(E(cancelExp(P('2*x'), P('0'), 1, de))).toBe('0');
    expect(() => cancelExp(P('2*x'), P('t**2'), 1, de)).toThrow(NonElementaryIntegralException);
    expect(() => cancelExp(P('2*x'), P('t**3 + t**2'), 3, de)).toThrow(NonElementaryIntegralException);
    expect(E(cancelExp(P('-1'), P('t'), 1, de))).toBe('t*x');
    const dp = DE(P('1', x), P('1/x'));
    expect(() => cancelPrimitive(P('1'), P('t'), Infinity, dp)).toThrow(NonElementaryIntegralException);
    expect(E(cancelPrimitive(P('1'), P('t + 1/x'), 2, dp))).toBe('t');
    expect(E(cancelPrimitive(P('4*x'), P('4*x*t**2 + 2*t/x'), 3, dp))).toBe('t**2');
    expect(E(cancelPrimitive(P('1'), P('0'), 2, dp))).toBe('0');
    expect(() => cancelPrimitive(P('1'), P('t**3'), 2, dp)).toThrow(NonElementaryIntegralException);
    expect(() => cancelPrimitive(P('1/x'), P('t'), 2, dp)).toThrow(NotImplementedError);
  });
});

describe('rischDE', () => {
  it('solves Dy + f*y = g (SymPy test_rischDE)', () => {
    const de = DE(P('1', x), P('t'));
    de.decrementLevel();
    const [ya, yd] = rischDE(P('-2*x', x), P('1', x), P('1 - 2*x - 2*x**2', x), P('1', x), de);
    expect([E(ya), E(yd)]).toEqual(['x + 1', '1']);
  });
  it('has no solution', () => {
    expect(() => rischDE(P('1'), P('1'), P('t'), P('1'), DE(P('1', x), P('t**2 + t')))).toThrow(NonElementaryIntegralException);
  });
});

describe('num', () => {
  it('reads integer bounds and rejects symbolic ones', () => {
    expect(num(3)).toBe(3);
    expect(num(parse('5/2'))).toBe(2.5);
    expect(() => num(x)).toThrow(NotImplementedError);
  });
});

describe('cases with t = exp(1/x) (Dt = -t/x**2)', () => {
  const ex = DE(P('1', x), P('-t/x**2'));
  it('special_denom with a parametric logarithmic derivative', () => {
    expect(specialDenom(P('1'), P('1 - x + t'), P('x**2'), P('1'), P('t'), ex).map(E)).toEqual(['1', 't/x**2 + (2 - x)/x**2', '1', 't']);
  });
  it('bound_degree, exp case with da = db', () => {
    expect(boundDegree(P('1'), P('(1 - x)/x**2'), P('t'), ex)).toBe(1);
  });
  it('cancel_exp needs is_deriv_in_field', () => {
    expect(() => cancelExp(P('(1 - x)/x**2'), P('t'), 1, ex)).toThrow(NotImplementedError);
  });
});

describe('more polynomial cases (Dt = t**2 + 1)', () => {
  const tan = DE(P('1', x), P('t**2 + 1'));
  it('no_cancel_b_small with deg b = deg c = 0 and with deg b > 0', () => {
    const r = noCancelBSmall(P('2'), P('3'), 0, tan);
    if (r instanceof KPoly) throw new TypeError('a reduced problem expected');
    expect([E(r[0]), str(r[1]), str(r[2])]).toEqual(['0', '2', '3']);
    expect(E(noCancelBSmall(P('t'), P('t'), 0, tan) as KPoly)).toBe('1');
  });
  it('no_cancel_equal with a positive integer M and a complete solution', () => {
    const r = noCancelEqual(P('-2*t'), P('t**3'), 3, tan);
    if (r instanceof KPoly) throw new TypeError('a reduced problem expected');
    expect([E(r[0]), r[1], E(r[2])]).toEqual(['0', 2, 't**3']);
    expect(E(noCancelEqual(P('1 - t'), P('t**3 + t**2 + 2*t'), 3, tan) as KPoly)).toBe('t**2');
    expect(E(solvePolyRde(P('1 - t'), P('t**3 + t**2 + 2*t'), 3, tan))).toBe('t**2');
  });
  it('a symbolic constant of the limited integration does not bound the degree', () => {
    // SymPy 1.14 fails here (it compares a Poly with an int)
    expect(boundDegree(P('t'), P('y/x'), P('t'), DE(P('1', x), P('1/x')))).toBe(1);
    expect(() => rischDE(P('y'), P('x*t'), P('t'), P('1'), DE(P('1', x), P('1/x')))).toThrow(NonElementaryIntegralException);
  });
  it('rischDEOrNone: undefined without a solution, other errors are raised', () => {
    expect(rischDEOrNone(P('1'), P('1'), P('t'), P('1'), DE(P('1', x), P('t**2 + t')))).toBeUndefined();
    expect(E(rischDEOrNone(P('-2*x', x), P('1', x), P('1 - 2*x - 2*x**2', x), P('1', x), DE(P('1', x)))?.[0] ?? P('0'))).toBe('x + 1');
    // the hypertangent special part is not implemented
    expect(() => rischDEOrNone(P('1'), P('t'), P('1'), P('t**2 + 1'), tan)).toThrow(NotImplementedError);
  });
  it('rischDE falls back to an infinite bound when bound_degree is not implemented', () => {
    // bound_degree needs is_log_deriv_k_t_radical_in_field over a hypertangent monomial
    // (and then cancel_primitive needs it again)
    const de = new DifferentialExtension({ D: [P('1', x), KPoly.of(parse('t1**2 + 1'), t1s), P('1/x')] });
    expect(() => rischDE(P('1/x'), P('1'), P('t'), P('1'), de)).toThrow(NotImplementedError);
  });
});

describe('degenerate no-cancellation cases', () => {
  const tan = DE(P('1', x), P('t**2 + 1'));
  it('no_cancel_equal: M for symbolic, fractional and negative leading coefficients', () => {
    expect(E(noCancelEqual(P('x*t'), P('0'), 1, tan) as KPoly)).toBe('0');
    expect(E(noCancelEqual(P('t/2'), P('0'), 1, tan) as KPoly)).toBe('0');
    expect(E(noCancelEqual(P('t'), P('0'), 1, tan) as KPoly)).toBe('0');
  });
  it('no_cancel_equal with m = 0 (SymPy agrees)', () => {
    const r = noCancelEqual(P('1 - t'), P('t + 1'), 3, tan);
    if (r instanceof KPoly) throw new TypeError('a reduced problem expected');
    expect([E(r[0]), r[1], E(r[2])]).toEqual(['0', 1, 't + 1']);
  });
  it('bound_degree, primitive case: limited integration fails (SymPy 1.14 fails: TypeError, SympifyError)', () => {
    const dp = DE(P('1', x), P('1/x'));
    expect(boundDegree(P('t'), P('-1/(x + 1)'), P('t'), dp)).toBe(1);
    expect(boundDegree(P('t'), P('2*t/x + x**2/(x + 1)'), P('t'), dp)).toBe(1);
  });
});

describe('no_cancel_equal with m = 0 and a solution', () => {
  it('Dq + (1 + t)*q = t + 1 (SymPy agrees)', () => {
    expect(E(noCancelEqual(P('1 + t'), P('t + 1'), 3, DE(P('1', x), P('t**2 + 1'))) as KPoly)).toBe('1');
  });
});
