// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/bessel.ts: evaluation rules, derivatives and the double-precision
// numerics of the Bessel and Airy functions. Expected values are str() results of SymPy 1.14
// (mpmath 1.3 values for the numerics).

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { NotImplementedError, airyaiprime, airybiprime, besselj, diff } from '../src';

// ---- table harness: each case is [kind, SymPy source, str() of the SymPy 1.14 result or [re, im]] ----

type Case = [kind: string, src: string, expected: string | [number, number]];

const x = new sj.Sym('x');
const locals = {
  p: new sj.Sym('p', { positive: true }),
  q: new sj.Sym('q', { positive: true }),
  n: new sj.Sym('n', { integer: true }),
  k: new sj.Sym('k', { integer: true }),
  m: new sj.Sym('m', { integer: true, positive: true }),
  r: new sj.Sym('r', { real: true }),
  ng: new sj.Sym('ng', { negative: true }),
  nn: new sj.Sym('nn', { nonnegative: true }),
  // functions the parser does not know by name
  bernoulli: sj.bernoulli,
  euler: sj.euler,
  genocchi: sj.genocchi,
  bell: (n: sj.Expr, a?: sj.Expr) => sj.bell(n, a),
  fibonacci: sj.fibonacci,
  lucas: sj.lucas,
  tribonacci: sj.tribonacci,
  partition: sj.partition,
  mobius: sj.mobius,
  primenu: sj.primenu,
  primeomega: sj.primeomega,
  multigamma: sj.multigamma,
  frac: sj.frac,
  totient: sj.totient,
  reduced_totient: sj.reducedTotient,
  divisor_sigma: sj.divisorSigma,
  primepi: sj.primepi,
  // bell(n, k, (a, b, ...)) of SymPy
  bellx: (n: sj.Expr, k: sj.Expr, ...xs: sj.Expr[]) => sj.bell(n, k, xs),
};

/** Parse a SymPy expression with the symbols and functions above. */
const P = (src: string): sj.Expr => sj.parse(src, { locals });

/** NV sources are `expr;x=1.5;y=0.5+2i`: the numeric values of the free symbols. */
function numericValues(spec: string[]): Record<string, number | { re: number; im: number }> {
  const vals: Record<string, number | { re: number; im: number }> = {};
  for (const item of spec) {
    const [name = '', v = ''] = item.split('=');
    const c = /^([-+]?[\d.]+)([-+][\d.]+)i$/.exec(v);
    vals[name] = c ? { re: Number(c[1]), im: Number(c[2]) } : Number(v);
  }
  return vals;
}

/** str() of the SymPy operation named by the case kind, or the double-precision value for N / NV. */
function run(kind: string, src: string): string | [number, number] {
  if (kind === 'N' || kind === 'NV') {
    const [e = '', ...vals] = src.split(';');
    const c = sj.toComplex(P(e), numericValues(vals));
    return [c.re, c.im];
  }
  const e = P(src);
  switch (kind) {
    case 'D':
      return String(sj.diff(e, x));
    case 'EF':
      return String(sj.expandFunc(e));
    case 'UP':
      return String(sj.unpolarify(e));
    case 'PL':
      return String(sj.polarify(e, { subs: false }));
    case 'C':
      return String(sj.conjugate(e));
    case 'T':
      return String(sj.transpose(e));
    case 'A':
      return String(sj.adjoint(e));
    case 'E':
      return String(sj.expand(e));
    case 'EFl':
      return String(sj.evalf(e));
    default:
      return String(e);
  }
}

function check(cases: readonly Case[]): void {
  it.each(cases)('%s %s', (kind, src, expected) => {
    const got = run(kind, src);
    if (typeof expected === 'string') {
      expect(got).toBe(expected);
      return;
    }
    if (typeof got === 'string') throw new TypeError(`expected a number, got ${got}`);
    const tol = (v: number) => 1e-9 * Math.max(1, Math.abs(v));
    expect(Math.abs(got[0] - expected[0])).toBeLessThanOrEqual(tol(expected[0]));
    expect(Math.abs(got[1] - expected[1])).toBeLessThanOrEqual(tol(expected[1]));
  });
}

const BESSEL_CASES: Case[] = [
  ["s", "besselj(0, 0)", "1"],
  ["s", "besselj(2, 0)", "0"],
  ["s", "besselj(p, 0)", "0"],
  ["s", "besselj(x, 0)", "besselj(x, 0)"],
  ["s", "besselj(-1/2, 0)", "zoo"],
  ["s", "besseli(0, 0)", "1"],
  ["s", "besseli(1, 0)", "0"],
  ["s", "besseli(x, 0)", "besseli(x, 0)"],
  ["s", "bessely(0, 0)", "-oo"],
  ["s", "bessely(1, 0)", "zoo"],
  ["s", "besselk(0, 0)", "oo"],
  ["s", "besselk(1, 0)", "zoo"],
  ["s", "besselj(2, oo)", "0"],
  ["s", "besselj(2, -oo)", "0"],
  ["s", "bessely(1, oo)", "0"],
  ["s", "besseli(2, oo)", "oo"],
  ["s", "besselj(x, oo)", "0"],
  ["s", "besselj(-2, z)", "besselj(2, z)"],
  ["s", "bessely(-2, z)", "bessely(2, z)"],
  ["s", "bessely(-1, z)", "-bessely(1, z)"],
  ["s", "besseli(-2, z)", "besseli(2, z)"],
  ["s", "besselk(-2, z)", "besselk(2, z)"],
  ["s", "besselj(3, -z)", "-besselj(3, z)"],
  ["s", "besseli(3, -z)", "-besseli(3, z)"],
  ["s", "besseli(2, -z)", "besseli(2, z)"],
  ["s", "bessely(3, -z)", "bessely(3, -z)"],
  ["s", "airyai(oo)", "0"],
  ["s", "airybi(oo)", "oo"],
  ["s", "airyai(-oo)", "0"],
  ["s", "airybi(0)", "3**(5/6)/(3*gamma(2/3))"],
  ["s", "airyaiprime(0)", "-3**(2/3)/(3*gamma(1/3))"],
  ["s", "airybiprime(0)", "3**(1/6)/gamma(1/3)"],
  ["s", "airyaiprime(z)", "airyaiprime(z)"],
  ["D", "besseli(nu, x)", "besseli(nu - 1, x)/2 + besseli(nu + 1, x)/2"],
  ["D", "bessely(nu, x)", "bessely(nu - 1, x)/2 - bessely(nu + 1, x)/2"],
  ["D", "airybi(x)", "airybiprime(x)"],
  ["D", "airyaiprime(x)", "x*airyai(x)"],
  ["D", "airybiprime(x)", "x*airybi(x)"],
  ["N", "besselj(2, 3/2)", [0.23208767214421472, 0.0]],
  ["N", "besselj(1/3, 2 + I)", [0.5464799383244642, -0.5278218598485709]],
  ["N", "besseli(2, 3/2)", [0.33783461833568074, 0.0]],
  ["N", "besseli(1/3, 2 + I)", [1.498668951219072, 1.4107144293258447]],
  ["N", "bessely(0, 3/2)", [0.38244892379775886, 0.0]],
  ["N", "bessely(2, 3/2)", [-0.9321937597629739, 0.0]],
  ["N", "bessely(1/3, 3/2)", [0.0966100877666278, 0.0]],
  ["N", "bessely(2, 1 + I)", [-0.4733680205344934, 0.5773369575804951]],
  ["N", "besselk(0, 3/2)", [0.21380556264752573, 0.0]],
  ["N", "besselk(3, 3/2)", [1.8338037024745792, 0.0]],
  ["N", "besselk(1/3, 3/2)", [0.22015769026776688, 0.0]],
  ["N", "besselk(1, 1 + I)", [0.02456830552374035, -0.4597194738011894]],
  ["NV", "bessely(x, 2);x=-2", [-0.6174081041906827, 0.0]],
  ["N", "airyai(3/2)", [0.07174949700810541, 0.0]],
  ["N", "airybi(3/2)", [1.878941503747895, 0.0]],
  ["N", "airyaiprime(3/2)", [-0.09738201284230132, 0.0]],
  ["N", "airybiprime(3/2)", [1.8862122548481655, 0.0]],
  ["N", "airyai(-2 + I)", [0.5563045393711925, 0.7898014381882759]],
  ["N", "airyaiprime(-2 + I)", [1.1349598127621308, -0.8858793656453342]],
  ["s", "besselj(nu, -z)", "(-z)**nu*besselj(nu, z)/z**nu"],
  ["s", "besseli(nu, -z)", "(-z)**nu*besseli(nu, z)/z**nu"],
  ["s", "besselj(2, I*z)", "-besseli(2, z)"],
  ["s", "besseli(2, I*z)", "-besselj(2, z)"],
  ["s", "besselj(3, 2*I*z)", "-I*besseli(3, 2*z)"],
  ["s", "besselj(I, 0)", "nan"],
  ["s", "besseli(I, 0)", "nan"],
  ["s", "bessely(I, 0)", "nan"],
  ["s", "besselk(I, 0)", "nan"],
  ["s", "bessely(x, 0)", "bessely(x, 0)"],
  ["s", "besselk(x, 0)", "besselk(x, 0)"],
  ["s", "besseli(x, -oo)", "oo*(-1)**x"],
  ["s", "besseli(2, I*oo)", "0"],
  ["s", "besselk(2, oo)", "0"],
  ["s", "besselk(2, I*oo)", "0"],
  ["s", "besselk(2, -I*oo)", "0"],
  ["s", "besselk(2, -oo)", "besselk(2, -oo)"],
  ["s", "bessely(2, I*oo)", "-oo*I"],
  ["s", "bessely(2, -I*oo)", "oo*I"],
  ["s", "bessely(x, I*oo)", "oo*exp(I*pi*(x + 1)/2)"],
  ["s", "airyaiprime(oo)", "0"],
  ["s", "airybiprime(oo)", "oo"],
  ["s", "airybiprime(-oo)", "0"],
  ["s", "airybi(-oo)", "0"],
  ["s", "airyaiprime(-oo)", "airyaiprime(-oo)"],
  ["s", "besselj(-x, 0)", "besselj(-x, 0)"],
  ["s", "besselj(n, 0)", "besselj(n, 0)"],
];

describe('Bessel and Airy functions (SymPy eval, diff and numerics)', () => check(BESSEL_CASES));

describe('Bessel: cases outside the table', () => {
  it('constructors of the Airy derivatives', () => {
    expect(String(airyaiprime(x))).toBe('airyaiprime(x)');
    expect(String(airybiprime(0))).toBe('3**(1/6)/gamma(1/3)');
  });
  it('the derivative with respect to the order is not implemented', () => {
    // SymPy: Derivative(besselj(x, 1), x)
    expect(() => diff(besselj(x, 1), x)).toThrow(NotImplementedError);
  });
});
