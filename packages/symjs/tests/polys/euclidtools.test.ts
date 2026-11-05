// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/euclidtools.ts: the heuristic GCD; expected values from SymPy 1.14
// (test_euclidtools.py test_dup_gcd and test_dmp_gcd, dup_zz_heu_gcd and dmp_zz_heu_gcd).

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src';
import { Poly, Rational, add, mul, parse, pow, symbols } from '../../src';
import { heuGcd, zzExquo } from '../../src/polys/euclidtools';
import type { ZPoly } from '../../src/polys/wang';
import { zpoly } from '../../src/polys/wang';

const toZ = (s: string, vars: readonly Expr[]): ZPoly => {
  const p = Poly.from(parse(s), [...vars]);
  if (p.isZero) return new Map();
  return zpoly(p.terms().map(([m, c]) => [m, (c as Rational).p] as const));
};
const fromZ = (f: ZPoly, vars: readonly Expr[]): string =>
  String(add(...[...f.values()].map((t) => mul(Rational.of(t.c), ...vars.map((v, i) => pow(v, t.e[i] ?? 0))))));

const gcd = (f: string, g: string, vars: readonly Expr[]): string[] | undefined => {
  const r = heuGcd(toZ(f, vars), toZ(g, vars), vars.length);
  return r?.map((p) => fromZ(p, vars));
};

describe('heuGcd (SymPy dup_zz_heu_gcd)', () => {
  const [x] = symbols('x');
  const cases: [string, string, string[]][] = [
    ['0', '0', ['0', '0', '0']],
    ['2', '0', ['2', '1', '0']],
    ['-2', '0', ['2', '-1', '0']],
    ['0', '-2', ['2', '0', '-1']],
    ['0', '2*x + 4', ['2*x + 4', '0', '1']],
    ['2*x + 4', '0', ['2*x + 4', '1', '0']],
    ['2', '2', ['2', '1', '1']],
    ['-2', '2', ['2', '-1', '1']],
    ['2', '-2', ['2', '1', '-1']],
    ['-2', '-2', ['2', '-1', '-1']],
    ['x**2 + 2*x + 1', '1', ['1', 'x**2 + 2*x + 1', '1']],
    ['x**2 + 2*x + 1', '2', ['1', 'x**2 + 2*x + 1', '2']],
    ['2*x**2 + 4*x + 2', '2', ['2', 'x**2 + 2*x + 1', '1']],
    ['2', '2*x**2 + 4*x + 2', ['2', '1', 'x**2 + 2*x + 1']],
    ['2*x**2 + 4*x + 2', 'x + 1', ['x + 1', '2*x + 2', '1']],
    ['x + 1', '2*x**2 + 4*x + 2', ['x + 1', '1', '2*x + 2']],
    ['x - 31', 'x', ['1', 'x - 31', 'x']],
    ['x**4 + 8*x**3 + 21*x**2 + 22*x + 8', 'x**3 + 6*x**2 + 11*x + 6', ['x**2 + 3*x + 2', 'x**2 + 5*x + 4', 'x + 3']],
    ['x**4 - 4', 'x**4 + 4*x**2 + 4', ['x**2 + 2', 'x**2 - 2', 'x**2 + 2']],
    ['x**8 + x**6 - 3*x**4 - 3*x**3 + 8*x**2 + 2*x - 5', '3*x**6 + 5*x**4 - 4*x**2 - 9*x + 21', ['1', 'x**8 + x**6 - 3*x**4 - 3*x**3 + 8*x**2 + 2*x - 5', '3*x**6 + 5*x**4 - 4*x**2 - 9*x + 21']],
    // the candidate from the gcd of the images fails; the one from the cofactor of f works
    ['1317378933230047068160*x + 2945748836994210856960', '120352542776360960*x + 269116466014453760', ['120352542776360960*x + 269116466014453760', '10946', '1']],
  ];
  it.each(cases)('gcd(%s, %s)', (f, g, want) => expect(gcd(f, g, [x])).toEqual(want));

  it('a squarefree part of a large polynomial', () => {
    const f =
      '-352518131239247345597970242177235495263669787845475025293906825864749649589178600387510272*x**49 + 46818041807522713962450042363465092040687472354933295397472942006618953623327997952*x**42 + 378182690892293941192071663536490788434899030680411695933646320291525827756032*x**35 + 112806468807371824947796775491032386836656074179286744191026149539708928*x**28 - 12278371209708240950316872681744825481125965781519138077173235712*x**21 + 289127344604779611146960547954288113529690984687482920704*x**14 + 19007977035740498977629742919480623972236450681*x**7 + 311973482284542371301330321821976049';
    const df = String(parse(f).diff(x));
    expect(gcd(f, df, [x])?.[0]).toBe(
      '365431878023781158602430064717380211405897160759702125019136*x**21 + 197599133478719444145775798221171663643171734081650688*x**14 - 9504116979659010018253915765478924103928886144*x**7 - 311973482284542371301330321821976049',
    );
  });
});

describe('heuGcd (SymPy dmp_zz_heu_gcd)', () => {
  const [x, y, z, u] = symbols('x y z u');
  it('trivial cases in two variables', () => {
    expect(gcd('-2', '0', [x, y])).toEqual(['2', '-1', '0']);
    expect(gcd('2*x**2 + 4*x + 2', 'x + 1', [x, y])).toEqual(['x + 1', '2*x + 2', '1']);
    expect(gcd('x + 1', '2*x**2 + 4*x + 2', [x, y])).toEqual(['x + 1', '1', '2*x + 2']);
  });

  it('polynomials without the main variable', () => {
    const v = [x, y, z, u];
    expect(gcd('u**2 + 2*u + 1', '2*u + 2', v)).toEqual(['u + 1', 'u + 1', '2']);
    expect(gcd('z**2*u**2 + 2*z**2*u + z**2 + z*u + z', 'u**2 + 2*u + 1', v)).toEqual(['u + 1', 'u*z**2 + z**2 + z', 'u + 1']);
    expect(gcd('u**2 + 2*u + 1', 'z**2*u**2 + 2*z**2*u + z**2 + z*u + z', v)).toEqual(['u + 1', 'u + 1', 'u*z**2 + z**2 + z']);
    // the main variable in one of them only: the gcd with its content
    expect(gcd('x*y + y', 'y**2', [x, y])).toEqual(['y', 'x + 1', 'y']);
  });

  it('Fateman polynomials (dmp_fateman_poly_F_1, F_2, F_3 with n = 2)', () => {
    const v = [x, y, z];
    const f1 = 'x**2 + 2*x*y + 2*x*z + 3*x + y**2 + 2*y*z + 3*y + z**2 + 3*z + 2';
    const g1 = '-3*x**4*y - 3*x**2*y**3 + x**2*y**2 - 3*x**2*y*z**2 - 3*x**2*y - x**2 + y**4 + y**2*z**2 - z**2 - 1';
    expect(gcd(f1, g1, v)?.[0]).toBe('1');
    const f2 =
      'x**4 - 2*x**3 - 2*x**2*y**2 - 4*x**2*y*z - 6*x**2*y - 2*x**2*z**2 - 6*x**2*z - 3*x**2 + 2*x*y**2 + 4*x*y*z + 6*x*y + 2*x*z**2 + 6*x*z + 4*x + y**4 + 4*y**3*z + 6*y**3 + 6*y**2*z**2 + 18*y**2*z + 13*y**2 + 4*y*z**3 + 18*y*z**2 + 26*y*z + 12*y + z**4 + 6*z**3 + 13*z**2 + 12*z + 4';
    const g2 =
      'x**4 + 4*x**3*y + 4*x**3*z + 6*x**3 + 6*x**2*y**2 + 12*x**2*y*z + 18*x**2*y + 6*x**2*z**2 + 18*x**2*z + 13*x**2 + 4*x*y**3 + 12*x*y**2*z + 18*x*y**2 + 12*x*y*z**2 + 36*x*y*z + 26*x*y + 4*x*z**3 + 18*x*z**2 + 26*x*z + 12*x + y**4 + 4*y**3*z + 6*y**3 + 6*y**2*z**2 + 18*y**2*z + 13*y**2 + 4*y*z**3 + 18*y*z**2 + 26*y*z + 12*y + z**4 + 6*z**3 + 13*z**2 + 12*z + 4';
    expect(gcd(f2, g2, v)?.[0]).toBe('x**2 + 2*x*y + 2*x*z + 2*x + y**2 + 2*y*z + 2*y + z**2 + 2*z + 1');
    const f3 = String(parse(f2).subs(new Map([[x, pow(x, 3)], [y, pow(y, 3)], [z, pow(z, 3)]])));
    const g3 = String(parse(g2).subs(new Map([[x, pow(x, 3)], [y, pow(y, 3)], [z, pow(z, 3)]])));
    expect(gcd(f3, g3, v)?.[0]).toBe('x**6 + 2*x**3*y**3 + 2*x**3*z**3 + 2*x**3 + y**6 + 2*y**3*z**3 + 2*y**3 + z**6 + 2*z**3 + 1');
  });
});

describe('zzExquo', () => {
  const [x, y] = symbols('x y');
  it('exact quotients over the integers, undefined otherwise', () => {
    const q = (f: string, g: string) => {
      const r = zzExquo(toZ(f, [x, y]), toZ(g, [x, y]));
      return r && fromZ(r, [x, y]);
    };
    expect(q('x**2 - y**2', 'x - y')).toBe('x + y');
    expect(q('x**2 - y**2', 'x - 2*y')).toBeUndefined();
    // the leading coefficient does not divide
    expect(q('x + 1', '2*x + 2')).toBeUndefined();
    // the quotient would need a higher degree in y than f has
    expect(q('x*y + 1', 'x - y')).toBeUndefined();
  });
});

describe('heuGcd retries (small first evaluation points)', () => {
  const [x, y] = symbols('x y');
  const at3 = (f: string, g: string, vars: readonly Expr[] = [x]) => heuGcd(toZ(f, vars), toZ(g, vars), vars.length, 3n)?.map((p) => fromZ(p, vars));
  it('takes the candidate from the gcd of the images, or from one of the cofactors', () => {
    expect(at3('3430*x**3 + 2212*x**2 - 9649*x + 4313', '36260*x**2 - 49521*x + 14755')).toEqual(['245*x - 227', '14*x**2 + 22*x - 19', '148*x - 65']);
    expect(at3('28684*x**3 + 34650*x**2 - 37956*x - 41040', '-10302*x**2 - 10594*x - 1260')).toEqual(['202*x + 180', '142*x**2 + 45*x - 228', '-51*x - 7']);
    // f(3) = 0: the point is skipped
    expect(at3('x**2 - 2*x - 3', 'x**2 - 9')).toEqual(['x - 3', 'x + 1', 'x + 3']);
  });
  it('gives up after six points, also when the images of a recursive step fail', () => {
    const f = '5762*x**3 + 50145*x**2 + 75378*x - 83080';
    const g = '-4386*x**2 - 36108*x - 54672';
    expect(at3(f, g)).toBeUndefined();
    const fy = `${f.replaceAll('x', 'y')} + x*y**4 - 3*y**4`;
    const gy = `${g.replaceAll('x', 'y')} + x*y**3 - 3*y**3`;
    expect(at3(fy, gy, [x, y])).toBeUndefined();
    // the gcd with the content of a polynomial in the main variable fails
    expect(at3(f.replaceAll('x', 'y'), `x*(${g.replaceAll('x', 'y')})`, [x, y])).toBeUndefined();
  });
});
