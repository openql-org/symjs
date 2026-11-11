// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import {
  getResolventByLookup, Poly, Sym, Permutation, Rational, MPContext, xring, parseExpr as p,
  Resolvent, ResolventException, GaloisGroupException, defineResolvents, generateLambdaLookup, sparseSymmetrizeResolventCoeffs, sVars, wrap,
} from '../../../src';
import tables from '../../../src/polys/numberfields/resolventlookupdata';
const x = new Sym('x');
const poly = (s: string): Poly => Poly.from(p(s), [x]);
const X = ['X0', 'X1', 'X2', 'X3'].map((n) => new Sym(n));
const s = [new Permutation([0, 1, 2, 3]), new Permutation([1, 0, 2, 3]), new Permutation([3, 1, 2, 0])];
const R = new Resolvent(p('X0*X2 + X1*X3'), X, s);

it('evaluates lookup-table resolvents and validates monicity', () => {
  expect(getResolventByLookup(poly('x**4+1'), 1).map(String)).toEqual(['1', '0', '-4', '0']);
  expect(() => getResolventByLookup(poly('2*x**4+1'), 0)).toThrow('monic');
});

it('forms the conjugates of a resolvent form (SymPy Resolvent docstring)', () => {
  expect(R.rootLambdas.map((f) => String(f(...X)))).toEqual(['X0*X2 + X1*X3', 'X0*X3 + X1*X2', 'X0*X1 + X2*X3']);
  expect([R.m, R.t, R.r, String(R.coeffPrecFunc), String(R.rootPrecFunc)]).toEqual([3, 2, 2, "Poly(56*M**5, M, domain='ZZ')", "Poly(6*M, M, domain='ZZ')"]);
  const ctx = new MPContext();
  const values = [1, 2, 3, 4].map((v) => ctx.mpc(v));
  expect(String(R.rootLambdas[1]!(...values))).toBe(String(ctx.mpc(10)));
  expect(R.esfLambdas.map((f) => f(ctx.mpc(1), ctx.mpc(2), ctx.mpc(3)).real.toInt())).toEqual([1n, -6n, 11n, -6n]);
  expect(() => R.rootLambdas[0]!(X[0]!)).toThrow(TypeError);
  expect(() => R.rootLambdas[0]!(ctx.mpc(1), X[1]!, X[2]!, X[3]!)).toThrow('unexpected type');
});

it('computes resolvent coefficients and integer roots from approximate roots', () => {
  const cases: [string, bigint[], string, string, string][] = [
    ['x**4+8*x+12', [1n, 0n, -48n, -64n], 'NoMatch', 'NoMatch', '0:-6,1:-1,2:8'],
    ['x**4+1', [1n, 0n, -4n, 0n], '-2', '0', '0:-2,1:0,2:2'],
    ['x**4-2', [1n, 0n, 8n, 0n], '0', '2', '2:0'],
    ['x**4+x+1', [1n, 0n, -4n, -1n], 'NoMatch', 'NoMatch', '0:-2,1:0,2:2'],
  ];
  for (const [T, coeffs, a, i, rounded] of cases) {
    const [Rdup, a0, i0] = R.evalForPoly(poly(T), true);
    expect([Rdup, String(a0), String(i0)]).toEqual([coeffs, a, i]);
    expect([...R.roundRootsToIntegersForPoly(poly(T))].map(([k, v]) => `${k}:${v}`).join(',')).toBe(rounded);
  }
  expect(R.evalForPoly(poly('x**4+1')).slice(1).map(String)).toEqual(['NoMatch', 'NoMatch']);
  expect([R.getPrec(2), R.getPrec(10.5, 'roots'), R.getPrec(1), R.getPrec(Rational.of(7n, 2n))]).toEqual([13, 8, 13, 17]);
  const roots = R.approximateRootsOfPoly(poly('x**4+8*x+12'), 'roots');
  expect(roots.map((r) => r.real.value.toFixed(3))).toEqual(['-1.371', '-1.371', '1.371', '1.371']);
  expect(roots[0]!.context.prec).toBeGreaterThan(8);
});

it('rounds to the nearest integer with ties to even', () => {
  const ctx = new MPContext();
  expect([Resolvent.roundMpf(3n), Resolvent.roundMpf(2.5), Resolvent.roundMpf(3.5), Resolvent.roundMpf(-2.5), Resolvent.roundMpf(-2.6), Resolvent.roundMpf(ctx.mpf(7.25))]).toEqual([3n, 2n, 4n, -2n, -3n, 7n]);
});

it('rejects forms it cannot bound', () => {
  expect(() => new Resolvent(p('2*X0*X2 + X1*X3'), X, s)).toThrow(ResolventException);
  expect(() => new Resolvent(p('X0*X2 + X1'), X, s)).toThrow('homogeneous');
  expect(() => new Resolvent(p('X0'), X, s)).toThrow('m < r*2^t');
  expect(() => new Resolvent(0, X, s)).toThrow(ResolventException);
  expect(new ResolventException('e')).toBeInstanceOf(GaloisGroupException);
  // The coset representatives do not give a symmetric resolvent: its coefficient is a root of T.
  expect(() => new Resolvent(p('X0'), X, [s[0]!]).evalForPoly(poly('x**4+1'))).toThrow('non-integer coeff');
});

it('defines the resolvents of degrees four through six (SymPy define_resolvents)', () => {
  const res = defineResolvents();
  expect([...res].map(([k, [F, Xs, ss]]) => [k, String(F).slice(0, 60), Xs.length, ss.length])).toEqual([
    ['4,0', 'X0**2*X3 + X0*X1**2 + X1*X2**2 + X2*X3**2', 4, 6],
    ['4,1', 'X0*X2 + X1*X3', 4, 3],
    ['5,1', 'X0**2*X1*X4 + X0**2*X2*X3 + X0*X1**2*X2 + X0*X1*X3**2 + X0*X', 5, 6],
    ['6,1', 'X0**2*X1**2*X2*X4 + X0**2*X1**2*X3*X5 + X0**2*X1*X2**2*X5 + ', 6, 6],
    ['6,2', 'X0*X1*X2 + X3*X4*X5', 6, 10],
  ]);
});

it('symmetrizes resolvent coefficients into the lookup tables', () => {
  const res = defineResolvents();
  for (const key of ['4,0', '4,1', '6,2']) {
    const [F, Xs, ss] = res.get(key)!;
    const [symmetrized, times] = sparseSymmetrizeResolventCoeffs(F, Xs, ss);
    expect(times.length).toBe(ss.length);
    const c = Xs.map((_, i) => new Sym(`c${i}`));
    const table = Object.entries(tables).find(([k]) => k === key)![1];
    symmetrized.forEach((text, j) => {
      const e = p(text).subs(Object.fromEntries(sVars(Xs.length).map((v, i) => [v.name, c[i]!])));
      const terms = Poly.from(e, c).terms().map(([m, k]) => `${m.join(' ')}:${k}`).sort();
      expect(terms).toEqual(table[j]!.map((t) => `${t.powers.join(' ')}:${t.coefficient}`).sort());
    });
  }
}, 300_000);

it('reports progress and rejects incomplete coset representatives', () => {
  const [F, Xs, ss] = defineResolvents().get('4,1')!;
  const lines: string[] = [];
  expect(sparseSymmetrizeResolventCoeffs(F, Xs, ss, (t) => lines.push(t))[0]).toEqual(['-s2', 's1*s3 - 4*s4', '-s1**2*s4 + 4*s2*s4 - s3**2']);
  expect(lines.some((l) => l.startsWith('-----\nCoeff 1'))).toBe(true);
  expect(() => sparseSymmetrizeResolventCoeffs(F, Xs, [ss[0]!])).toThrow('nonzero remainder');
});

it('generates the source of the lookup table', () => {
  const table = generateLambdaLookup(undefined, true);
  expect(table).toMatch(/^# This table was generated by a call to\n# `sympy\.polys\.numberfields\.galois_resolvents\.generate_lambda_lookup\(\)`\.\n# The entire job took \d+\.\d\ds\.\n# Of this, Case \(6, 1\) took 0\.00s\.\n/);
  expect(table).toContain('resolvent_coeff_lambdas = {\n    (4, 0): [\n        lambda s1, s2, s3, s4: (-2*s1*s2 + 6*s3),\n        lambda s1, s2, s3, s4: (2*s1**3*s3');
  expect(table.endsWith('64*s3**6 - 320*s3**2*s4**3)\n    ],\n}\n')).toBe(true);
  const [, X2] = xring('X0,X1');
  const small = generateLambdaLookup(undefined, false, new Map([['6,1', [X2[0]!, X2, [new Permutation([0, 1]), new Permutation([1, 0])]]]]));
  expect(small).toContain('    (6, 1): [\n        lambda s1, s2: (-s1),\n        lambda s1, s2: (s2)\n    ],\n}\n');
  expect(wrap('a b c d e f', 2)).toBe('a b\nc d\ne f');
  expect(wrap('x'.repeat(5))).toBe('xxxxx');
});
