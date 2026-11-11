// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const numeric = (rule: sj.QuadratureRule) => rule.map((row) => row.map((x) => x.toNumber()));

describe('Gaussian quadrature', () => {
  it('matches the reference nodes and weights', () => {
    const cases: [sj.QuadratureRule, number[], number[]][] = [
      [sj.gaussLegendre(3, 5), [-0.77460, 0, 0.77460], [0.55556, 0.88889, 0.55556]],
      [sj.gaussLaguerre(3, 5), [0.41577, 2.2943, 6.2899], [0.71109, 0.27852, 0.010389]],
      [sj.gaussHermite(3, 5), [-1.2247, 0, 1.2247], [0.29541, 1.1816, 0.29541]],
      [sj.gaussGenLaguerre(3, sj.Rational.of(-1, 2), 5), [0.19016, 1.7845, 5.5253], [1.4493, 0.31413, 0.00906]],
      [sj.gaussJacobi(3, sj.S.Half, sj.S.NegHalf, 5), [-0.90097, -0.22252, 0.62349], [1.7063, 1.0973, 0.33795]],
      [sj.gaussChebyshevT(3, 5), [0.86602, 0, -0.86602], [1.0472, 1.0472, 1.0472]],
      [sj.gaussChebyshevU(3, 5), [0.70711, 0, -0.70711], [0.3927, 0.7854, 0.3927]],
      [sj.gaussLobatto(4, 5), [-1, -0.44721, 0.44721, 1], [1/6, 5/6, 5/6, 1/6]],
      [sj.gaussLobatto(2, 5), [-1, 1], [1, 1]],
    ];
    for (const [rule, nodes, weights] of cases) {
      const values = numeric(rule);
      for (const [i, row] of [nodes, weights].entries()) for (const [j, v] of row.entries()) expect(values[i]![j]).toBeCloseTo(v, 4);
    }
  });

  it('integrates all polynomials through the Gaussian exactness degree', () => {
    const rules: [sj.QuadratureRule, number][] = [[sj.gaussLegendre(6, 25), 11], [sj.gaussLobatto(6, 25), 9]];
    for (const [rule, degree] of rules) {
      const [nodes, weights] = numeric(rule);
      for (let k = 0; k <= degree; k++) {
        const sum = nodes!.reduce((s, x, i) => s + weights![i]! * x ** k, 0);
        expect(sum).toBeCloseTo(k % 2 ? 0 : 2 / (k + 1), 13);
      }
    }
    // A 40-digit rule retains precision beyond IEEE doubles.
    expect(String(sj.gaussLegendre(2, 40)[0][1])).toContain('0.5773502691896257645091487805019574556476');
    const laguerre = numeric(sj.gaussGenLaguerre(4, 1.5, 20));
    expect(laguerre[1]!.reduce((a, b) => a+b, 0)).toBeCloseTo(3*Math.sqrt(Math.PI)/4, 13);
    const jacobi = numeric(sj.gaussJacobi(6, 1, 1, 20));
    expect(jacobi[1]!.reduce((a, b) => a+b, 0)).toBeCloseTo(4/3, 13);
  });

  it('validates degree, precision and integrable weight parameters', () => {
    expect(() => sj.gaussLegendre(0, 5)).toThrow(RangeError);
    expect(() => sj.gaussLegendre(2.5, 5)).toThrow(RangeError);
    expect(() => sj.gaussLegendre(2, 0)).toThrow(RangeError);
    expect(() => sj.gaussLegendre(2, 1.5)).toThrow(RangeError);
    expect(() => sj.gaussLobatto(1, 5)).toThrow(RangeError);
    expect(() => sj.gaussGenLaguerre(2, -1, 5)).toThrow(RangeError);
    expect(() => sj.gaussJacobi(2, sj.S.I, 0, 5)).toThrow(RangeError);
    expect(() => sj.gaussJacobi(2, sj.S.Infinity, 0, 5)).toThrow(RangeError);
  });
});
