// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/exprfacts.ts.
// The facts of numbers, symbols, sums, products, powers and functions. Expected values are
// SymPy 1.14's (expr.is_<fact> for every assumption fact).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { fact, monotonicSign } from '../../src/core/exprfacts';
import { Dummy, Mul, Pow, Rational, S } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';

const camel = (k: string): string => k.replace(/_([a-z])/g, (_m, c: string) => c.toUpperCase());
const SYMBOLS: Readonly<Record<string, Readonly<Record<string, boolean>>>> = {
  x: {}, y: {}, r: { real: true }, p: { positive: true }, q: { positive: true }, n: { negative: true },
  nn: { nonnegative: true }, np: { nonpositive: true }, k: { integer: true }, m: { integer: true, nonzero: true },
  o: { odd: true }, e: { even: true }, pi_: { positive: true, integer: true }, ni: { negative: true, integer: true },
  nni: { nonnegative: true, integer: true }, z: { zero: true }, nz: { nonzero: true }, i: { imaginary: true },
  j: { imaginary: true }, f: { finite: true }, inf: { infinite: true }, c: { complex: true }, h: { hermitian: true },
  ah: { antihermitian: true }, ra: { rational: true }, ir: { irrational: true }, al: { algebraic: true },
  tr: { transcendental: true }, pr: { prime: true }, co: { composite: true }, nr: { real: false },
  er: { extended_real: true }, ep: { extended_positive: true }, en: { extended_negative: true }, pol: { polar: true },
  opr: { prime: true, odd: true }, oco: { composite: true, odd: true }, pe: { positive: true, even: true }, ne: { negative: true, even: true },
  pf: { positive: true, finite: true }, nzr: { real: true, nonzero: true }, inf2: { infinite: true },
  nc: { complex: false, finite: true }, nr2: { real: false }, xh2: { hermitian: true, antihermitian: false, nonzero: true },
  xa2: { hermitian: false, antihermitian: true, zero: false, finite: true }, xz: { zero: true, antihermitian: true },
  z2: { zero: true }, pi2: { positive: true, integer: true }, pinf: { extended_positive: true, infinite: true },
  ninf: { extended_negative: true, infinite: true }, xf: { hermitian: false, antihermitian: false }, nng: { negative: false },
  nng2: { negative: false }, xh4: { hermitian: true, antihermitian: false }, xa4: { hermitian: false, antihermitian: true },
  na: { algebraic: true, nonzero: true }, A: { commutative: false }, B: { commutative: false }, xh: { hermitian: true, commutative: false },
  xa: { antihermitian: true, commutative: false },
};
const symbols: Record<string, Expr> = Object.fromEntries(
  Object.entries(SYMBOLS).map(([name, a]) => [name, new sj.Symbol(name, Object.fromEntries(Object.entries(a).map(([k, v]) => [camel(k), v])))]),
);
const parse = (src: string): Expr => (src.startsWith('raw:') ? sj.parse(src.slice(4), { symbols, evaluate: false }) : sj.parse(src, { symbols }));

const FACTS = [
  'algebraic', 'antihermitian', 'commutative', 'complex', 'composite', 'even',
  'extended_negative', 'extended_nonnegative', 'extended_nonpositive', 'extended_nonzero', 'extended_positive', 'extended_real',
  'finite', 'hermitian', 'imaginary', 'infinite', 'integer', 'irrational',
  'negative', 'noninteger', 'nonnegative', 'nonpositive', 'nonzero', 'odd',
  'polar', 'positive', 'prime', 'rational', 'real', 'transcendental',
  'zero',
] as const;

it.each([
  ['besseli(k, r)', 'extended_real', true], ['bessely(k, p)', 'extended_real', true],
  ['airyai(r)', 'extended_real', true], ['airybiprime(i)', 'extended_real', false],
  ['erf(ep)', 'positive', true], ['erf(en)', 'negative', true], ['erf(c)', 'finite', true],
  ['erfc(I)', 'real', false], ['erf2(I, 0)', 'real', false], ['fresnelc(r)', 'finite', true],
  ['gamma(ne+1/2)', 'positive', true], ['gamma(ne-1/2)', 'positive', false],
  ['loggamma(np)', 'real', false], ['polygamma(2, -2.5)', 'negative', true],
  ['polygamma(-2, -2.5)', 'positive', undefined], ['polygamma(0, I)', 'real', undefined],
  ['zeta(1+p)', 'finite', true], ['zeta(x)', 'finite', undefined],
] as const)('finds the %s %s fact', (source, predicate, expected) => {
  expect(fact(parse(source), predicate)).toBe(expected);
});

it('distinguishes multivariate gamma poles from regular points', () => {
  const expression = (a: sj.ExprLike) => sj.fn('multigamma', [a, 3], { evaluate: false });
  expect(fact(expression(2), 'real')).toBe(true);
  expect(fact(expression(sj.rational(1, 3)), 'real')).toBe(true);
  expect(fact(expression(-1), 'real')).toBe(false);
  expect(fact(expression(new sj.Float(-1)), 'real')).toBe(false);
  expect(fact(expression(sj.symbol('u')), 'real')).toBeUndefined();
});

/**
 * Expressions (raw: unevaluated) and SymPy 1.14's value of each fact of FACTS in order, each
 * asked of a new expression: T True, F False, . None.
 */
const TABLE: readonly (readonly [string, string])[] = [
  ['0', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['1', 'T.TTFFFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['2', 'T.TTFTFTFTTTTTFFTFFFTFTF.TTTTFF'],
  ['3', 'T.TTFFFTFTTTTTFFTFFFTFTT.TTTTFF'],
  ['4', 'T.TTTTFTFTTTTTFFTFFFTFTF.TFTTFF'],
  ['-1', 'T.TTFFTFTTFTTTFFTFTFFTTT.FFTTFF'],
  ['-2', 'T.TTFTTFTTFTTTFFTFTFFTTF.FFTTFF'],
  ['-3', 'T.TTFFTFTTFTTTFFTFTFFTTT.FFTTFF'],
  ['6', 'T.TTTTFTFTTTTTFFTFFFTFTF.TFTTFF'],
  ['7', 'T.TTFFFTFTTTTTFFTFFFTFTT.TTTTFF'],
  ['1/2', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['-3/2', 'T.TTFFTFTTFTTTFFFFTTFTTF.FFTTFF'],
  ['2.5', '..TTFFFTFTTTTTFFF.FTTFTF.TF.T.F'],
  ['0.0', 'T.TTFTFTTFFTTTFFT.FFTTFF.FF.TFT'],
  ['3.0', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['-2.0', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['pi', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['E', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['I', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['EulerGamma', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['Catalan', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['GoldenRatio', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['TribonacciConstant', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['oo', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['-oo', 'F.TFFFTFTTFTF.FTFFFTFFFF.FFFFFF'],
  ['zoo', 'F.TFFFFFFFFFF.FTFFFFFFFF.FFFFFF'],
  ['nan', '..T............................'],
  ['x', '..T............................'],
  ['p', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['o', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['e', 'T.TT.T.....TTTFFTF.F...F...TTF.'],
  ['pr', 'T.TTF.FTFTTTTTFFTFFFTFT..TTTTFF'],
  ['co', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['xh', 'F.FFFFFFFFFF.TF.FFFFFFFF.FFFFFF'],
  ['x + 1', '..T............................'],
  ['p + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p - 1', '..TT.......TTTFF............T..'],
  ['pi_ - 1', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['pi_ - 2', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['nni + 1', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['nni - 1', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['n - 1', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['n + 1', '..TT.......TTTFF............T..'],
  ['np - 3', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['-nn - 1', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['p + q', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p + n', '..TT.......TTTFF............T..'],
  ['nn + np', '..TT.......TTTFF............T..'],
  ['k + 1/2', 'T.TTFF...T.TTTFFFF.T..TF..FTTFF'],
  ['k + m', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['o + 1', 'T.TT.T.....TTTFFTF.F...F...TTF.'],
  ['o + e', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['o + o*e', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['e + 2', 'T.TT.T.....TTTFFTF.F...F...TTF.'],
  ['2*o + 1', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['p + oo', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['p - oo', 'F.TFFFTFTTFTF.FTFFFTFFFF.FFFFFF'],
  ['oo + x', '..T............................'],
  ['oo + inf', '..T..............F.............'],
  ['r + I', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['r + I*p', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['r + i', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['x + i', '..T............................'],
  ['k + i', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['p + I', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['i + j', '.TTT........T..F.F.............'],
  ['1 + I', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['2*I + 3', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['sqrt(2) + 1', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['sqrt(2) + sqrt(3)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['pi + 1', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['ir + 1', '..TTFF...T.TTTFFFT.T..TF..FFT.F'],
  ['ir + ra', '..TTFF...T.TTTFFFT.T..TF..FFT.F'],
  ['ir + x', '..T............................'],
  ['ra + 1', 'T.TT.......TTTFF.F.........TTF.'],
  ['al + 1', 'T.TT........T..F.............F.'],
  ['f + 1', '..T.........T..F...............'],
  ['h + 1', '..T..........T.................'],
  ['ah + I', '.TT............................'],
  ['z + 1', 'T.TT.FFTFTTTTTFFTFFFTFTT.T.TTFF'],
  ['z + I', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['x + z', '..T............................'],
  ['pi_**2 + 1', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['pi_**2 - 1', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['p**2 + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['1/p + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['1/p - 1', '..TT.......TTTFF............T..'],
  ['1/(p + 1) - 1', '..TTFFTFTTFTTTFFF.TTFTTF.FF.T.F'],
  ['p*q + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p*q - 1', '..TT.......TTTFF............T..'],
  ['pi_*nni + 1', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['pi_*nni - 1', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['1 - 1/pi_', 'T.TT.......TTTFF.F.........TTF.'],
  ['-p - 2', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['p + q - 1', '..TT.......TTTFF............T..'],
  ['nni + pi_ - 1', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['x**2 + 1', '..T............................'],
  ['r**2 + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['r**2 - 1', '..TT.......TTTFF............T..'],
  ['k**2 + k', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['nn**3 + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['-nn**3 - 1', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['np**3 - 1', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['2/(p + 1) + 1', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p/(p + 1)', '..TT..FTFTTTTTFF..F.TFT.FT..T.F'],
  ['p/(q + 1) - 1', '..TT.......TTTFF............T..'],
  ['2*x', '..T.....................F......'],
  ['2*k', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['3*k', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['2*o', 'T.TT.T...T.TTTFFTF.F..TFF..TTFF'],
  ['-o', 'T.TT.F...T.TTTFFTF.F..TTF..TTFF'],
  ['o*e', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['o*k', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['k*m', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['o*o', 'T.TT.FFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['k/2', 'T.TT.......TTTFF.F......F..TTF.'],
  ['o/2', 'T.TTFF...T.TTTFFFF.T..TFF.FTTFF'],
  ['e/2', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['3*e/2', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['e**2/2', 'T.TT.TFT...TTTFFTFFFT..FF..TTF.'],
  ['e**2/4', 'T.TT..FT...TTTFFTFFFT...F..TTF.'],
  ['e**2/8', 'T.TT..FT...TTTFF.FF.T...F..TTF.'],
  ['o/e', '..T.FF..........F......FF.F...F'],
  ['k/3', 'T.TT.......TTTFF.F......F..TTF.'],
  ['1/m', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['2/k', '..T.....................F.....F'],
  ['k/m', 'T.TT.......TTTFF.F......F..TTF.'],
  ['4*e/8', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['o*e/2', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['x*y', '..T.....................F......'],
  ['p*q', '..TT..FTFTTTTTFF..F.TFT.FT..T.F'],
  ['p*n', '..TTF.TFTTFTTTFF..T.FTT.FFF.T.F'],
  ['n*n', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p*nn', '..TT..FT...TTTFF..F.T...F...T..'],
  ['p*np', '..TTF...T.FTTTFF.....T..FFF.T..'],
  ['n*np', '..TT..FT...TTTFF..F.T...F...T..'],
  ['r*x', '..T.....................F......'],
  ['r*p', '..TT.......TTTFF........F...T..'],
  ['p*z', 'T.TTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['x*z', '..T.....................F......'],
  ['oo*x', '..T.....................F......'],
  ['oo*p', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['oo*z', '..T.....................F......'],
  ['oo*n', 'F.TFFFTFTTFTF.FTFFFTFFFF.FFFFFF'],
  ['I*p', '.TTTFFFFFFFFT.TFFFFFFFFFFFFFF.F'],
  ['I*r', '..TT........T..F........F......'],
  ['I*x', '..T.....................F......'],
  ['I*i', '..TT.....T.TTTFF......T.F...T.F'],
  ['i*j', '..TT.....T.TTTFF......T.F...T.F'],
  ['i*p', '.TTTFFFFFFFFT.TFFFFFFFFFFFFFF.F'],
  ['i*r', '..TT........T..F........F......'],
  ['i*nz', '.TTTFFFFFFFFT.TFFFFFFFFFFFFFF.F'],
  ['r*i*j', '..TT.......TTTFF........F...T..'],
  ['2*I', 'TTTTFFFFFFFFT.TFFFFFFFFFFFFFFFF'],
  ['I*pi', 'FTTTFFFFFFFFT.TFFFFFFFFFFFFFFTF'],
  ['p*(1 + I)', '..TTFFFFFFFFT.FFFFFFFFFFFFFFF.F'],
  ['r*(2 + I)', '..TT........T..F........F......'],
  ['i*(2 + I)', '..TTFFFFFFFFT.FFFFFFFFFFFFFFF.F'],
  ['x*inf', '..T.....................F......'],
  ['z*inf', '..T.....................F......'],
  ['f*z', 'T.TTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['f*nz', '..T.........T..F........F......'],
  ['h*ah', '..T.....................F......'],
  ['ah*ah', '..T............................'],
  ['xh*xh', 'F.F.FF........F.F......F..FF..F'],
  ['xh*xa', 'F.FFFFFFFFFF..F.FFFFFFFFFFFFFFF'],
  ['xa*xa', 'F.F.FF........F.F......F..FF..F'],
  ['A*B', 'F.FFFFFFFFFF..F.FFFFFFFFFFFFFFF'],
  ['pr*co', 'T.TTT.FTFTTTTTFFTFFFTFT.FTFTTFF'],
  ['pi_*pi_', 'T.TT..FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['(pi_ + 1)*(pi_ + 1)', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['pi_*2', 'T.TT.TFTFTTTTTFFTFFFTFTFFT.TTFF'],
  ['pr*2', 'T.TTTTFTFTTTTTFFTFFFTFTFFTFTTFF'],
  ['ir*2', '..TTFF...T.TTTFFFT.T..TFF.FFT.F'],
  ['ir*ra', '..TT.......TTTFF........F...T..'],
  ['ir*nz', '..TT.....T.TTTFF......T.F...T.F'],
  ['ir*z', 'T.TTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['ir*ir', '..TTFFFTFTTTTTFFFTFTTFTF.TFFT.F'],
  ['sqrt(2)*pi', 'F.TTFFFTFTTTTTFFFTFTTFTFFTFFTTF'],
  ['2*pi', 'F.TTFFFTFTTTTTFFFTFTTFTFFTFFTTF'],
  ['pol*p', '..T.....................T......'],
  ['pol*x', '..T.....................F......'],
  ['pol*pol', '..T.....................T......'],
  ['al*2', 'T.TT........T..F........F....F.'],
  ['al*pi', '..TT........T..F........F......'],
  ['al*tr', '..TT........T..F........F......'],
  ['c*p', '..TT........T..F........F......'],
  ['c*2', '..TT........T..F........F......'],
  ['k*x', '..T.....................F......'],
  ['p*q*n', '..TTF.TFTTFTTTFF..T.FTT.FFF.T.F'],
  ['np*np', '..TT..FT...TTTFF..F.T.......T..'],
  ['nn*np', '..TTF...T.FTTTFF.....T..FFF.T..'],
  ['r*nr', '..T.....................F......'],
  ['nr*nr', '..T..F.................F......F'],
  ['p*nr', '..T.F.....F.............FFF...F'],
  ['x*nr', '..T.....................F......'],
  ['x**2', '..T............................'],
  ['k**2', 'T.TT..FT...TTTFFTFFFT.....FTTF.'],
  ['k**3', 'T.TT.......TTTFFTF.F......FTTF.'],
  ['o**2', 'T.TT.FFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['e**2', 'T.TT.TFT...TTTFFTFFFT..F..FTTF.'],
  ['o**k', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['e**pi_', 'T.TT.T.....TTTFFTF.F...F...TTF.'],
  ['o**pi_', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['(-1)**k', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['(-1)**x', '..T............................'],
  ['2**k', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['2**pi_', 'T.TT.TFTFTTTTTFFTFFFTFTF.T.TTFF'],
  ['2**ni', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['(1/2)**pi_', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['k**(-1)', '..T...........F...............F'],
  ['pi_**(-1)', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['ni**(-1)', 'T.TTF.TFTTFTTTFF.FT.FTT..FFTTFF'],
  ['m**(-1)', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['pi_**(-2)', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['(pi_ + 1)**(-1)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['2**(-pi_)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['sqrt(2)', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['sqrt(3)', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['sqrt(4)', 'T.TTFTFTFTTTTTFFTFFFTFTF.TTTTFF'],
  ['sqrt(p)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['sqrt(n)', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['sqrt(r)', '..TT..F.....T..F..F............'],
  ['sqrt(nn)', '..TT..FT...TTTFF..F.T.......T..'],
  ['sqrt(x)', '..T............................'],
  ['sqrt(-1 + I)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['p**x', '..T............................'],
  ['p**r', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['p**I', '..TT........T.FF..............F'],
  ['n**2', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['n**3', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['n**k', '..TT.....T.TTTFF......T.....T.F'],
  ['n**o', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['n**e', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['n**(1/2)', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['n**(1/3)', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['nn**2', '..TT..FT...TTTFF..F.T.......T..'],
  ['nn**(1/2)', '..TT..FT...TTTFF..F.T.......T..'],
  ['nn**nn', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['np**3', '..TTF...T.FTTTFF.....T...FF.T..'],
  ['np**2', '..TT..FT...TTTFF..F.T.......T..'],
  ['np**o', '..T.F.....F...F..........FF....'],
  ['r**2', '..TT..FT...TTTFF..F.T.......T..'],
  ['r**3', '..TT.......TTTFF............T..'],
  ['r**k', '..T...........F................'],
  ['r**(-1)', '..T...........F...............F'],
  ['r**(-2)', '..T...F.......F...F...........F'],
  ['z**2', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['z**p', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['nz**2', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['nz**(-1)', '..TT.....T.TTTFF......T.....T.F'],
  ['x**(-1)', '..T............................'],
  ['f**2', '..T.........T..F...............'],
  ['f**(-1)', '..T...........................F'],
  ['inf**2', 'F.T.FF..........F......F..FF..F'],
  ['x**x', '..T............................'],
  ['p**p', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['I**2', 'T.TTFFTFTTFTTTFFTFTFFTTT.FFTTFF'],
  ['I**3', 'TTTTFFFFFFFFT.TFFFFFFFFFFFFFFFF'],
  ['I**4', 'T.TTFFFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['I**i', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['I**k', 'T.TT........T..F.............FF'],
  ['I**o', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['I**e', 'T.TT.....T.TTTFF......T.....TFF'],
  ['i**2', '..TTFFTFTTFTTTFF..T.FTTF.FF.T.F'],
  ['i**3', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['i**4', '..TT.FFTFTTTTTFF..F.TFTF.T..T.F'],
  ['i**k', '..TT........T..F..............F'],
  ['i**o', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['i**e', '..TT.....T.TTTFF......T.....T.F'],
  ['i**x', '..T............................'],
  ['i**(1/2)', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['(-I)**i', '..TT..FTFTTTTTFF..F.TFT.FT..T.F'],
  ['(2*I)**i', '..TTF.....F.T.FF........FFF...F'],
  ['(1 + I)**2', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['(1 + I)**3', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(1 + I)**x', '..T............................'],
  ['(1 + I)**(1/2)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['2**I', 'F.TTFFFFFFFFT.FFFFFFFFFF.FFFFTF'],
  ['2**(I*pi)', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['pi**I', '..TT........T.FF..............F'],
  ['(-2)**I', 'F.TTFFFFFFFFT.FFFFFFFFFF.FFFFTF'],
  ['(-1)**I', 'F.TTFF...T.TTTFFFT.T..TF..FFTTF'],
  ['(-1)**(1/2)', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['(-2)**(1/3)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(-2)**(2/3)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(-2)**k', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['(-2)**o', 'T.TTF.TFTTFTTTFF.FT.FTT.FFFTTFF'],
  ['(-2)**e', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['(-2)**x', '..T............................'],
  ['(-2)**r', '..TT........T..F..............F'],
  ['2**r', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['2**x', '..T............................'],
  ['3**(1/2)', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['(1/2)**x', '..T............................'],
  ['(3/2)**ni', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['2**(1/k)', '..T............................'],
  ['ra**k', '..T...........F................'],
  ['ra**m', '..T...........F................'],
  ['ra**2', 'T.TT..FT...TTTFF.FF.T......TTF.'],
  ['ra**(1/2)', 'T.TT..F.....T..F..F..........F.'],
  ['ir**k', '..TT.....T.TTTFF......T.....T.F'],
  ['ir**z', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['ir**2', '..TTFFFTFTTTTTFFFTFTTFTF.TFFT.F'],
  ['ra**ra', '..T............................'],
  ['ra**x', '..T............................'],
  ['al**(1/3)', 'T.TT........T..F.............F.'],
  ['tr**2', 'F.TTFF......T..FF......F..FF.TF'],
  ['tr**(1/2)', 'F.TTFFF.....T..FF.F....F..FF.TF'],
  ['al**al', '..T............................'],
  ['pi**2', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['pi**pi', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['pi**(1/2)', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['E**2', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['pr**2', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['co**2', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['pi_**pi_', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['(pi_ + 1)**2', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['(-pi_ - 1)**2', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['pol**2', '..T.....................T......'],
  ['pol**x', '..T.....................T......'],
  ['A**2', 'F.F.FF........F.F......F..FF..F'],
  ['k**k', 'T.TT.......TTTFF.F.........TTF.'],
  ['nni**nni', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['(1/2)**oo', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['2**oo', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['2**(-oo)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['(1/2)**(-oo)', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['x**oo', '..T............................'],
  ['p**inf', '..T............................'],
  ['r**(1/2)', '..TT..F.....T..F..F............'],
  ['p**(1/2)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['c**2', '..TT........T..F...............'],
  ['c**(-1)', '..T...........................F'],
  ['c**c', '..T............................'],
  ['h**2', '..T............................'],
  ['exp(x)', '..T...........................F'],
  ['exp(r)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(p)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(I)', 'F.TTFFFFFFFFT..FFFFFFFFF.FFFFTF'],
  ['exp(i)', '..TT........T..F..............F'],
  ['exp(I*pi)', 'T.TTFFTFTTFTTTFFTFTFFTTT.FFTTFF'],
  ['exp(I*pi/2)', 'TTTTFFFFFFFFT.TFFFFFFFFF.FFFFFF'],
  ['exp(2*I*pi)', 'T.TTFFFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['exp(I*pi*k)', 'T.TT........T..F.............FF'],
  ['exp(I*pi*k/2)', 'T.TT........T..F.............FF'],
  ['exp(i*pi)', '..TT........T..F..............F'],
  ['exp(2)', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['exp(ra)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(m)', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['exp(al)', '..TT........T..F..............F'],
  ['exp(nz)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(-oo)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['exp(oo)', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['exp(inf)', '..T...........................F'],
  ['exp(f)', '..T.........T..F..............F'],
  ['exp(c)', '..TT........T..F..............F'],
  ['exp(n)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(1 + I)', 'F.TTFF......T..FF......F..FF.TF'],
  ['exp(sqrt(2))', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['exp(pi)', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['exp(I*sqrt(2))', 'F.TTFFFFFFFFT..FFFFFFFFF.FFFFTF'],
  ['exp(x)*2', '..T.....................F.....F'],
  ['exp(i)**I', '..TT.....T.TTTFF......T.....T.F'],
  ['exp(I)**i', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(i)**i', '..TT.....T.TTTFF......T.....T.F'],
  ['exp(x)**2', '..T...........................F'],
  ['exp(I*pi*ra)', 'T.TT........T..F.............FF'],
  ['sin(x)', '..T............................'],
  ['sin(r)', '..TT.......TTTFF............T..'],
  ['sin(p)', '..TT.......TTTFF............T..'],
  ['log(p)', '..TT.......TTTFF............T..'],
  ['log(x)', '..T............................'],
  ['log(1/2)', 'F.TTFFTFTTFTTTFFFTTTFTTFFFFFTTF'],
  ['Abs(x)', '..T...FT...T..F...F............'],
  ['Abs(r)', '..TT..FT...TTTFF..F.T.......T..'],
  ['Abs(p)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['x*atan(x)', '..T.....................F......'],
  ['sin(x)*cos(x)', '..T.....................F......'],
  ['sin(x) - 67', '..T............................'],
  ['1024*sin(x)', '..T.....................F......'],
  ['floor(x)', '..T............................'],
  ['floor(r)', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['re(x)', '..T........T..F................'],
  ['im(x)', '..T........T..F................'],
  ['sign(x)', '..TT........T..F...............'],
  ['x*sin(x)', '..T.....................F......'],
  ['x + sin(x)', '..T............................'],
  ['exp_polar(x)', '..T.....................T.....F'],
  ['polar_lift(x)', '..T.....................T......'],
  ['exp_polar(x)*p', '..T.....................T.....F'],
  ['exp_polar(x)**2', '..T.....................T.....F'],
  ['Abs(x)*p', '..T...FT...T..F...F.....F......'],
  ['log(x)**2', '..T............................'],
  ['tan(r)', '..T........T..F................'],
  ['tan(I*r)', '..TT........T..F........F......'],
  ['tan(x)', '..T............................'],
  ['tan(p)', '..T........T..F................'],
  ['tan(i)', '..T.FFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['tan(pi/2 + x)', '..T.....................F......'],
  ['tan(pi + x)', '..T............................'],
  ['tan(pi/3 + z)', '..T........T..F................'],
  ['tan(pi + z)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['tan(z)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['cot(r)', '..T........T..F................'],
  ['cot(i)', '..T.FFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['cot(x + pi/2)', '..T.....................F......'],
  ['cot(r + pi/4)', '..T........T..F................'],
  ['tan(3*pi/4 + y)', '..T.....................F......'],
  ['tan(-3*pi/4 + z)', '..T........T..F................'],
  ['x + pi*y', '..T............................'],
  ['-4/e', '..T.....................F.....F'],
  ['-2/o', 'T.TT.....T.TTTFF.F....T.F..TTFF'],
  ['o*x**(-2)', '..T.....................F......'],
  ['4/e**2', '..T..FF...........F.....F.....F'],
  ['o*2**(-k)', 'T.TT.....T.TTTFF.F....T.F..TTFF'],
  ['4*2**(-k)', 'T.TT..FTFTTTTTFF.FF.TFT.FT.TTFF'],
  ['1 - p', '..TT.......TTTFF............T..'],
  ['1 - r', '..TT.......TTTFF............T..'],
  ['opr - 3', 'T.TT.TFT...TTTFFTFFFT..F...TTF.'],
  ['oco - 9', 'T.TT.TFT...TTTFFTFFFT..F...TTF.'],
  ['pr - 2', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['co - 4', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['pe - 3', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['ne + 3', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['r + I*x', '..T............................'],
  ['r + 2*I*x', '..T............................'],
  ['r + I*y*x', '..T............................'],
  ['x + I*r', '..T............................'],
  ['z + I*r', '..TT........T..F...............'],
  ['z + i', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['z + 1 + i', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['z + i + j', '..TT........T..F.F.............'],
  ['r + nz', '..TT.......TTTFF............T..'],
  ['p + i', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['2 + i', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['1 + I*r', '..TT........T.FF..............F'],
  ['z + I*z', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['k*I + r', '..TT........T..F...............'],
  ['oo - oo', '..T............................'],
  ['oo + oo', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['oo + 1', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['-oo + p', 'F.TFFFTFTTFTF.FTFFFTFFFF.FFFFFF'],
  ['oo + n', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['inf + 1', 'F.TFFF......F.FTFFF.FFFF.FFFFFF'],
  ['inf + p', 'F.TFFF......F.FTFFF.FFFF.FFFFFF'],
  ['inf + inf', 'F.TFFF....F.F.FTFFF.FFFFFFFFFFF'],
  ['inf + x', '..T............................'],
  ['ep + 1', '..T...FTFTTT..F...F..F........F'],
  ['en - 1', '..T.F.TFTTFT..F.....F....FF...F'],
  ['ep + en', '..T........T..F................'],
  ['er + 1', '..T........T..F................'],
  ['er + p', '..T........T..F................'],
  ['p + er', '..T........T..F................'],
  ['z*x', '..T.....................F......'],
  ['oo*0', '..T............................'],
  ['p*inf', 'F.TFFF....F.F.FTFFF.FFFFFFFFFFF'],
  ['n*inf', 'F.TFFFF.....F.FTFFF.FFFFFFFFFFF'],
  ['nz*inf', 'F.TFFF......F.FTFFF.FFFFFFFFFFF'],
  ['x*nz', '..T.....................F......'],
  ['A*0', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['o/4', 'T.TTFF...T.TTTFFFF.T..TFF.FTTFF'],
  ['e/4', 'T.TT.......TTTFF.F......F..TTF.'],
  ['3*e/4', 'T.TT.......TTTFF.F......F..TTF.'],
  ['o*e/4', 'T.TT.......TTTFF.F......F..TTF.'],
  ['2*o/4', 'T.TTFF...T.TTTFFFF.T..TFF.FTTFF'],
  ['pi_/2', 'T.TT..FTFTTTTTFF.FF.TFT.FT.TTFF'],
  ['e**3/8', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['o/3', 'T.TT.....T.TTTFF.F....T.F..TTFF'],
  ['e/3', 'T.TTFF...T.TTTFFFF.T..TFF.FTTFF'],
  ['pi_/(pi_ + 1)', 'T.TT..FTFTTTTTFF.FF.TFT.FT.TTFF'],
  ['2/(pi_ + 1)', 'T.TT..FTFTTTTTFF.FF.TFT.FT.TTFF'],
  ['k/(m + 1)', '..T.....................F......'],
  ['1/(pi_ + 1)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['i*i', '..TTFFTFTTFTTTFF..T.FTTF.FF.T.F'],
  ['i*h', '..T.....................F......'],
  ['h*h', '..T............................'],
  ['i*ah', '..T.....................F......'],
  ['ah*h', '..T.....................F......'],
  ['x*h', '..T.....................F......'],
  ['z*h', '..T.....................F......'],
  ['z*ah', '..T.....................F......'],
  ['nz*ah', '..T.....................F......'],
  ['ir*x', '..T.....................F......'],
  ['ir*p', '..TT.....T.TTTFF......T.F...T.F'],
  ['ir*nz*ra', '..TT.......TTTFF........F...T..'],
  ['ra*ir', '..TT.......TTTFF........F...T..'],
  ['nr*r', '..T.....................F......'],
  ['nr*p*q', '..T.F.....F.............FFF...F'],
  ['I*nr', '..T.....................F.....F'],
  ['nr*nz', '..T.....................F.....F'],
  ['i*nr', '..T.....................F.....F'],
  ['p*np*n', '..TT..FT...TTTFF..F.T...F...T..'],
  ['p*nn*n', '..TTF...T.FTTTFF.....T..FFF.T..'],
  ['nn*nn', '..TT..FT...TTTFF..F.T.......T..'],
  ['x*np', '..T.....................F......'],
  ['p*nr*r', '..T.....................F......'],
  ['n*np*np', '..TTF...T.FTTTFF.....T..FFF.T..'],
  ['pr*pr', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['pi_*pr', 'T.TT..FTFTTTTTFFTFFFTFT.FT.TTFF'],
  ['pi_*k', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['co*k', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['x**2*o', '..T.....................F......'],
  ['2*o*e', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['3*o*o', 'T.TT.FFTFTTTTTFFTFFFTFTTFT.TTFF'],
  ['o*o*o', 'T.TT.F...T.TTTFFTF.F..TT..FTTFF'],
  ['o*k*k', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['pi_*o*e', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['(o + 1)*o', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['o*(o + 2)', 'T.TT.F...T.TTTFFTF.F..TTF..TTFF'],
  ['o*(e + 1)', 'T.TT.F...T.TTTFFTF.F..TTF..TTFF'],
  ['o*e*x', '..T.....................F......'],
  ['i**(-1)', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['i**(-2)', '..TTF.TFTTFTTTFF..T.FTT..FF.T.F'],
  ['(1/2)**inf', '..T............................'],
  ['2**inf', '..T............................'],
  ['2**(-inf)', '..T............................'],
  ['p**(-inf)', '..T............................'],
  ['(r + 1)**(-1)', '..T...........F...............F'],
  ['2**(I*x)', '..T............................'],
  ['2**(I*r)', '..TT........T..F..............F'],
  ['2**(I*k)', '..TT........T..F..............F'],
  ['(1/2)**(I*r)', '..TT........T..F..............F'],
  ['(2/3)**(I*nz)', '..TT........T.FF..............F'],
  ['r**i', '..T............................'],
  ['p**i', '..TT........T.FF..............F'],
  ['2**i', '..TT........T.FF..............F'],
  ['nn**i', '..T............................'],
  ['n**i', '..TT........T..F..............F'],
  ['(-1)**i', '..TT.....T.TTTFF......T.....T.F'],
  ['x**i', '..T............................'],
  ['i**r', '..TT........T..F..............F'],
  ['i**(r + 2)', '..TT........T..F..............F'],
  ['i**(k + 2)', '..TT........T..F..............F'],
  ['i**(x + 2)', '..T............................'],
  ['I**(r + 1)', '..TT........T..F..............F'],
  ['(-I)**r', '..TT........T..F........F.....F'],
  ['I**r', '..TT........T..F..............F'],
  ['I**(1/2)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['I**(3/2)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(1 + I)**r', '..TT........T..F..............F'],
  ['(1 + I)**(1/3)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(1 + I)**(2/3)', 'T.TTFFFFFFFFT.FFFFFFFFFF.FFFFFF'],
  ['(2 + I)**k', 'T.TT........T..F.............FF'],
  ['k**(-2)', '..T...F.......F...F...........F'],
  ['k**(-k)', '..T...........F................'],
  ['(-2)**(-k)', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['(-3)**(-pi_)', 'T.TTFF...T.TTTFFFF.T..TF..FTTFF'],
  ['(-2)**ni', 'T.TTFF...T.TTTFFFF.T..TF..FTTFF'],
  ['2**(-k)', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['(1/3)**(-pi_)', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['3**(-pi_)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['(-3)**(-ni)', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['(2/3)**pi_', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['(2/3)**k', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['ra**pi_', 'T.TT.......TTTFF.F.........TTF.'],
  ['ra**ni', '..T...........F...............F'],
  ['(ra + 1)**2', 'T.TT..FT...TTTFF.FF.T......TTF.'],
  ['2**(1/2)', 'T.TTFFFTFTTTTTFFFTFTTFTF.TFFTFF'],
  ['(1/2)**(1/2)', 'T.TTFFFTFTTTTTFFFTFTTFTFFTFFTFF'],
  ['4**(1/2)', 'T.TTFTFTFTTTTTFFTFFFTFTF.TTTTFF'],
  ['ra**(1/3)', 'T.TT........T.FF.............F.'],
  ['ir**m', '..TTFF...T.TTTFFFT.T..TF..FFT.F'],
  ['x**k', '..T............................'],
  ['x**m', '..T............................'],
  ['2**ra', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['2**al', '..TT........T..F..............F'],
  ['al**ra', '..T............................'],
  ['al**2', 'T.TT........T..F.............F.'],
  ['tr**ra', '..TT........T..F..............F'],
  ['al**(1/2)', 'T.TT..F.....T..F..F..........F.'],
  ['(al + 1)**(1/2)', 'T.TT..F.....T..F..F..........F.'],
  ['ir**(1/2)', '..TT..F.....T..F..F...........F'],
  ['al**ir', '..T............................'],
  ['2**ir', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['(1/2)**ir', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['pi**ir', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['nz**ra', '..TT........T..F..............F'],
  ['nz**(1/2)', '..TT..F.....T..F..F...........F'],
  ['k**(1/2)', 'T.TT..F.....T..F..F..........F.'],
  ['pi_**(1/2)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['pi_**(3/2)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['pr**k', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['(-2)**pi_', 'T.TT.T...T.TTTFFTF.F..TF...TTFF'],
  ['(-3)**pi_', 'T.TT.F...T.TTTFFTF.F..TT...TTFF'],
  ['(pi_ + 1)**(pi_ + 1)', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['(-pi_ - 2)**e', 'T.TT..FTFTTTTTFF.FF.TFT..T.TTFF'],
  ['(-pi_ - 2)**o', 'T.TTF.TFTTFTTTFF.FT.FTT..FFTTFF'],
  ['(-pi_ - 2)**(2*pi_)', 'T.TTT.FTFTTTTTFFTFFFTFT..TFTTFF'],
  ['(pi_ + 1)**pi_', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['nn**(-1)', '..T...........F...............F'],
  ['nz**(-2)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['f**(-2)', '..T...........................F'],
  ['inf**x', '..T............................'],
  ['inf**p', '..T...........................F'],
  ['f**f', '..T............................'],
  ['f**p', '..T.........T..F...............'],
  ['x**f', '..T............................'],
  ['inf**(1/2)', 'F.T.FF..........F......F..FF..F'],
  ['(x + 1)**2', '..T............................'],
  ['r**o', '..T...........F................'],
  ['r**e', '..T...F.......F...F............'],
  ['np**e', '..T...F.......F...F............'],
  ['np**pi_', '..TT.......TTTFF............T..'],
  ['r**(2/3)', '..TT........T.FF...............'],
  ['n**(2/3)', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['n**(1/4)', '..TTFFFFFFFFT.FFFFFFFFFF.FFFF.F'],
  ['er**2', '..T...FT...T..F...F............'],
  ['er**(1/2)', '..T...F...........F............'],
  ['er**er', '..T............................'],
  ['p**er', '..T...FT...T..F...F............'],
  ['nz**er', '..T............................'],
  ['np**(1/2)', '..TT..F.....T..F..F............'],
  ['c**(1/2)', '..TT..F.....T..F..F............'],
  ['x**(1/2)', '..T............................'],
  ['exp(i)**2', '..TT........T..F..............F'],
  ['exp(I*pi/4)', 'T.TTFFFFFFFFT..FFFFFFFFF.FFFFFF'],
  ['exp(2*I*pi/3)', 'T.TTFFFFFFFFT..FFFFFFFFF.FFFFFF'],
  ['exp(I*x)', '..T...........................F'],
  ['exp(i*2)', '..TT........T..F..............F'],
  ['exp(I*r)', '..TT........T..F..............F'],
  ['exp(-oo*I)', '..T............................'],
  ['exp(nz)*0', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['exp(p - oo)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['exp(ra*pi)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(I*ra*pi)', 'T.TT........T..F.............FF'],
  ['exp(al*I*pi)', '..TT........T..F..............F'],
  ['exp(log(x))', '..T............................'],
  ['exp(1/2)', 'F.TTFFFTFTTTTTFFFTFTTFTF.TFFTTF'],
  ['exp(nz*al)', '..TT........T..F..............F'],
  ['exp(x*pi)', '..T...........................F'],
  ['exp(-inf)', 'F.TFFF........F.FFF.FFFF.FFFFFF'],
  ['exp(en)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['exp(ep)', '..T...FTFTTT..F...F..F........F'],
  ['exp(x + I)', '..T...........................F'],
  ['exp(c*I)', '..TT........T..F..............F'],
  ['Abs(k)', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['Abs(i)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['Abs(z)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['Abs(nz)', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['Abs(f)', '..TT..FT...TTTFF..F.T.......T..'],
  ['Abs(ra)', 'T.TT..FT...TTTFF.FF.T......TTF.'],
  ['Abs(o)', 'T.TT.FFTFTTTTTFFTFFFTFTT.T.TTFF'],
  ['Abs(e)', 'T.TT.TFT...TTTFFTFFFT..F...TTF.'],
  ['Abs(al)', 'T.TT..FT...TTTFF..F.T.......TF.'],
  ['re(i)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['re(f)', '..TT.......TTTFF............T..'],
  ['re(z)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['re(al)', 'T.TT.......TTTFF............TF.'],
  ['im(r)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['im(f)', '..TT.......TTTFF............T..'],
  ['im(i)', '..TT.....T.TTTFF......T.F...T.F'],
  ['sign(p)', 'T.TTFFFTFTTTTTFFTFFFTFTT.TFTTFF'],
  ['sign(n)', 'T.TTFFTFTTFTTTFFTFTFFTTT.FFTTFF'],
  ['sign(z)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['sign(i)', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['sign(r)', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['sign(nn)', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['sign(np)', 'T.TTF...T.FTTTFFTF.F.T...FFTTF.'],
  ['floor(p)', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['floor(n)', 'T.TTF.TFTTFTTTFFTFTFFTT..FFTTFF'],
  ['floor(nn)', 'T.TT..FT...TTTFFTFFFT......TTF.'],
  ['floor(f)', '..T.........T..F...............'],
  ['ceiling(p)', 'T.TT..FTFTTTTTFFTFFFTFT..T.TTFF'],
  ['ceiling(n)', 'T.TTF...T.FTTTFFTF.F.T...FFTTF.'],
  ['ceiling(r)', 'T.TT.......TTTFFTF.F.......TTF.'],
  ['ceiling(np)', 'T.TTF...T.FTTTFFTF.F.T...FFTTF.'],
  ['ceiling(f)', '..T.........T..F...............'],
  ['frac(r)', '..TT..FT...TTTFF..F.T.......T..'],
  ['frac(k)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['frac(x)', '..T.........T..F..F............'],
  ['frac(i)', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['exp_polar(r)', '..TT.....T.TTTFF......T.T...T.F'],
  ['exp_polar(-oo)', 'T.TTFTFTTFFTTTFFTFFFTTFFTFFTTFT'],
  ['exp_polar(inf)', '..T.....................T.....F'],
  ['exp_polar(f)', '..T.........T..F........T.....F'],
  ['exp_polar(ep)', '..T......T.T..F.........T.....F'],
  ['exp_polar(-ep)', '..T......T.T..F.........T.....F'],
  ['tan(x)*0', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['raw:z + z2', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['raw:z + z2 + i', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['raw:z + i', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['raw:z + i + j', '..TT........T..F.F.............'],
  ['raw:nzr - nzr + i', '.TTTFFFFFFFFT.TFFFFFFFFF.FFFF.F'],
  ['raw:nzr - nzr', '..TT.......TTTFF............T..'],
  ['raw:nzr - nzr + I*r', '..TT........T..F...............'],
  ['raw:p + n + i', '..TTFFFFFFFFT..FFFFFFFFF.FFFF.F'],
  ['raw:p + i + I*r', '..TT........T.FF..............F'],
  ['raw:inf + inf2', '..T..............F.............'],
  ['raw:inf + inf2 + 1', '..T..............F.............'],
  ['1/(2*pi_ + 2)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['2/e**2', '..T.FFF.........F.F....FF.F...F'],
  ['nc*p', 'F.TFFFFFFFFFT.FFFFFFFFFFFFFFFFF'],
  ['nr*(1 + I)', '..T.....................F.....F'],
  ['nr*nr2', '..T.....................F.....F'],
  ['xh2*xa2', '.TT.FFFFFFFFTFFFFFFFFFFFFFFFF.F'],
  ['xa2*xa2', '..T..F......T..F.......F......F'],
  ['xh2*xh2', '..TT..FTFTTTTTFF..F.TFT..T..T.F'],
  ['xz*xh2', 'TTTTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['xz*x', '..T.....................F......'],
  ['k*(k + 1)', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['raw:z**p', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['raw:nz**(-1)', '..TT.....T.TTTFF......T.....T.F'],
  ['raw:(1/2)**oo', 'T.TTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['raw:2**oo', '..T.FFFTFTTT..F.F.FT.F.F..FF..F'],
  ['raw:(1/2)**(-oo)', '..T...FTFTTT..F...F..F..F.....F'],
  ['raw:2**(-oo)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['raw:x**oo', '..T............................'],
  ['raw:(-2)**(-3)', 'T.TTFFTFTTFTTTFFFFTTFTTF.FFTTFF'],
  ['raw:(-3)**(-k)', 'T.TT.....T.TTTFF.F....T....TTFF'],
  ['raw:2**(-1)', 'T.TTFFFTFTTTTTFFFFFTTFTF.TFTTFF'],
  ['raw:4**(1/2)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['raw:z*inf', '..T.....................F......'],
  ['raw:0*oo', '..T.....................F......'],
  ['raw:z*p', 'T.TTFTFTTFFTTTFFTFFFTTFFFFFTTFT'],
  ['raw:z*inf*p', '..T.....................F......'],
  ['raw:inf*z', '..T.....................F......'],
  ['raw:p*z*inf', '..T.....................F......'],
  ['raw:2*o*o', 'T.TT.T...T.TTTFFTF.F..TFF..TTFF'],
  ['raw:I*I', 'T.TT.....T.TTTFF......T.F...TFF'],
  ['raw:I*i', '..TT.....T.TTTFF......T.F...T.F'],
  ['raw:I*I*r', '..TT.......TTTFF........F...T..'],
  ['raw:nzr - nzr + z', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['raw:nzr - nzr + i + j', '..TT........T..F...............'],
  ['raw:pinf + ninf', '..T........T..F..F.............'],
  ['raw:pinf + inf', '..T..............F.............'],
  ['xf*xh2', '..T.....................F.....F'],
  ['raw:xh2*xa2', '.TT.FFFFFFFFTFFFFFFFFFFFFFFFF.F'],
  ['raw:xa2*x', '..T.FFFFFFFF....FFFFFFFFFFFFF.F'],
  ['nng*nng2', '..T.....................F......'],
  ['nr*nng', '..T.....................F......'],
  ['raw:nz**oo', '..T...........F................'],
  ['raw:(2/3)**(-1)', 'T.TT..FTFTTTTTFF.FF.TFT.FT.TTFF'],
  ['raw:2.0**(-1)', '..TTFFFTFTTTTTFFF.FTTFTF.TF.T.F'],
  ['i**(x + 1/2)', '..T............................'],
  ['raw:tan(z - pi/3)', '..T........T..F................'],
  ['raw:tan(z - 3*pi/4)', '..T........T..F................'],
  ['raw:cot(z + pi/2)', 'T.TTFTFTTFFTTTFFTFFFTTFF.FFTTFT'],
  ['exp_polar(pinf)', 'F.TFFF...T.TF.FTFFFTFFFFTFFFFFF'],
  ['exp(pinf)', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['raw:exp(oo)', 'F.TFFFFTFTTTF.FTFFFTFFFF.FFFFFF'],
  ['k*(k + 1)*o', 'T.TT.......TTTFFTF.F....F..TTF.'],
  ['sqrt(2)*p + q - 1', '..TT.......TTTFF............T..'],
  ['1/(m*pi_) + 1', 'T.TT.......TTTFF.F.........TTF.'],
  ['raw:r + I*(x + I)', '..T............................'],
  ['xh4*xa4', '.TT.....................F......'],
  ['k*(k + 1)*(k + 3)', 'T.TT.T.....TTTFFTF.F...FF..TTF.'],
  ['raw:p + I*x', '..T............................'],
  ['raw:p + I*(x + I)', '..T............................'],
  ['tan(na)', 'F.TTFF...T.TTTFFFT.T..TF..FFTTF'],
  ['cot(na)', 'F.TTFF...T.TTTFFFT.T..TF..FFTTF'],
  ['tan(pi/7)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['cot(pi/7)', 'T.TT..FTFTTTTTFF..F.TFT..T..TFF'],
  ['tan(ra)', '..T........T..F................'],
  ['tan(2)', 'F.TTFFTFTTFTTTFFFTTTFTTF.FFFTTF'],
  ['cot(nz*ra)', '..T........T..F................'],
  ['raw:0*inf', '..T.....................F......'],
];

describe('the facts of expressions (SymPy expr.is_<fact>)', () => {
  it.each(TABLE)('%s', (src, values) => {
    const got = FACTS.map((k) => {
      const v = fact(parse(src), k);
      return v === undefined ? '.' : v ? 'T' : 'F';
    }).join('');
    expect(got).toBe(values);
  });
});

/** SymPy 1.14's _monotonic_sign (a signed Dummy by its name, the infinitesimal _eps as eps). */
const MONOTONIC_SIGN: readonly (readonly [string, string])[] = [
  ['nni + 1', '1'],
  ['pi_ - 1', 'nneg'],
  ['nni*pi_ + 1', '1'],
  ['pi_*pi2 + 1', '2'],
  ['nni - 1', 'None'],
  ['2*nn + 1', '1'],
  ['2*nn', '0'],
  ['-2*nn - 1', '-1'],
  ['-2*nn', '0'],
  ['2*np - 1', 'neg'],
  ['2*np', '0'],
  ['-2*np + 1', 'pos'],
  ['-2*np', '0'],
  ['nn + 1', '1'],
  ['np - 1', 'neg'],
  ['pi_ + 1', '2'],
  ['-pi_ - 1', '-2'],
  ['nn**2 + 1', 'None'],
  ['1/p + 1', 'pos'],
  ['p/(p + 1)', 'pos'],
  ['1/p', 'pos'],
  ['-1/p', 'neg'],
  ['np/(p + 1)', 'None'],
  ['nn/(p + 1)', 'None'],
  ['r/p', 'None'],
  ['1/(r + 1)', 'None'],
  ['p/q + 1', 'None'],
  ['1/(p*q) + 1', 'None'],
  ['1/(pi_*pi2) + 1', '2'],
  ['2/(pi_*pi2) + 1', '3'],
  ['-1/(pi_*pi2) - 1', '-2'],
  ['1/(m**2*pi_) + 1', 'None'],
  ['p + q - 1', 'None'],
  ['pi_ + pi2 - 1', '1'],
  ['p*q + 1', '1'],
  ['nn + nni + 1', '1'],
  ['x**2*p + 1', 'None'],
  ['r + p + 1', 'None'],
  ['nn*np - 1', '-1'],
  ['-nn - np + 1', 'None'],
  ['x + 1', 'None'],
  ['-p', '-eps'],
  ['-r', 'None'],
  ['opr', '3'],
  ['oco', '9'],
  ['pr', '2'],
  ['co', '4'],
  ['pe', '2'],
  ['ne', '-2'],
  ['ni', '-1'],
  ['n', '-eps'],
  ['pi_', '1'],
  ['p', 'eps'],
  ['nn', '0'],
  ['z', '0'],
  ['r', 'None'],
  ['2*p', 'eps'],
  ['p/q', 'None'],
  ['-pe', '-2'],
  ['sqrt(2)*p + q - 1', 'None'],
  ['1/(m*pi_) + 1', 'None'],
  ['np/(np - 1)', 'nneg'],
  ['np/(1 - np)', 'npos'],
  ['-1/(1 - np)', 'neg'],
  ['nn/(nn + 1)', 'nneg'],
  ['2 - 2*pi_', 'npos'],
  ['2*pi_ - 2', 'nneg'],
  ['sin(p*q) + 1', 'None'],
];

describe('monotonicSign (SymPy _monotonic_sign)', () => {
  it.each(MONOTONIC_SIGN)('%s', (src, want) => {
    const r = monotonicSign(parse(src));
    const got = r === undefined ? 'None' : r instanceof Dummy && r.name !== 'eps' ? r.name : String(r).replace(/_eps/g, 'eps');
    expect(got).toBe(want);
  });
});

describe('facts SymPy decides wrongly or that need unevaluated nodes', () => {
  const [x, z, p, np, k, inf, i, q, pi] = ['x', 'z', 'p', 'np', 'k', 'inf', 'i', 'q', 'pi_'].map((name): Expr => parse(name)) as [Expr, Expr, Expr, Expr, Expr, Expr, Expr, Expr, Expr];
  it('knows that a negative power of 0 is complex infinity', () => {
    // SymPy gives is_infinite False and is_algebraic True for Pow(z, -1) with a zero z
    const e = (): Expr => new Pow(z, Rational.of(-1));
    expect([fact(e(), 'finite'), fact(e(), 'infinite'), fact(e(), 'complex'), fact(e(), 'algebraic')]).toEqual([false, true, false, false]);
    expect(fact(new Pow(z, Rational.of(-2)), 'algebraic')).toBe(false);
  });
  it('does not know whether 0 to a symbolic power is finite', () => {
    // SymPy gives is_finite and is_algebraic True for 0**x (0**x is complex infinity for x < 0)
    expect([fact(new Pow(z, x), 'finite'), fact(new Pow(z, x), 'algebraic'), fact(new Pow(z, x), 'extended_positive')]).toEqual([undefined, undefined, undefined]);
    expect(fact(new Pow(z, np), 'zero')).toBe(false);
    expect(fact(new Pow(z, p), 'algebraic')).toBe(true);
  });
  it('knows that 0 times a finite number is 0, which is even', () => {
    // SymPy gives is_even False for Mul(0, f, evaluate=False) when it asks is_even first
    const f = parse('f');
    expect([fact(new Mul([S.Zero, f]), 'even'), fact(new Mul([S.Zero, f]), 'zero'), fact(new Mul([S.Zero, inf]), 'zero')]).toEqual([true, true, undefined]);
  });
  it('knows that a negative power of an infinite number is 0', () => {
    expect(fact(new Pow(inf, Rational.of(-1)), 'zero')).toBe(true);
  });
  it('decides the powers of numbers by their values', () => {
    expect(fact(new Pow(Rational.of(2, 3), Rational.of(-1)), 'integer')).toBe(false);
    expect(fact(new Pow(Rational.of(-5, 2), sj.mul(-1, pi)), 'integer')).toBe(false);
    expect(fact(new Pow(S.One, x), 'algebraic')).toBe(true);
    expect(fact(new Pow(i, sj.add(p, Rational.of(1, 2))), 'extended_real')).toBe(undefined);
    expect(fact(new Pow(i, sj.add(p, q)), 'extended_real')).toBe(undefined);
    expect(fact(new Pow(i, sj.add(p, 2)), 'extended_real')).toBe(undefined);
    expect(fact(new Pow(S.E, z), 'rational')).toBe(true);
    expect(fact(new Pow(S.E, S.Infinity), 'zero')).toBe(false);
    expect(fact(new Pow(S.E, S.Infinity), 'extended_positive')).toBe(true);
    expect(fact(new Pow(S.E, S.NegativeInfinity), 'extended_positive')).toBe(false);
  });
  it('knows the facts of Mod', () => {
    expect([fact(sj.Mod(k, 3), 'integer'), fact(sj.Mod(k, 3), 'nonnegative'), fact(sj.Mod(x, -3), 'nonpositive')]).toEqual([true, true, true]);
    expect([fact(sj.Mod(x, 3), 'integer'), fact(sj.Mod(x, k), 'nonnegative'), fact(sj.Mod(x, k), 'nonpositive')]).toEqual([undefined, undefined, undefined]);
  });
  it('asks the other functions what they know', () => {
    const g = sj.defineFunction('g');
    expect(fact(g(x), 'commutative')).toBe(true);
    expect(fact(g(x), 'positive')).toBe(undefined);
  });
});


it('uses the nonempty assumptions of indexed bases', () => {
  const base = new sj.IndexedBase('A', { positive: true });
  expect(fact(base, 'positive')).toBe(true);
  expect(fact(base.at(0), 'real')).toBe(true);
});

it('sin and cos of extended real arguments are finite, as are their sums and products', () => {
  const x = new sj.Sym('x', { extendedReal: true });
  const s = sj.sin(x);
  const c = sj.cos(x);
  for (const e of [s, c, sj.mul(1024, s), sj.mul(s, c), sj.add(s, -67), sj.pow(s, 2)]) expect(fact(e, 'finite')).toBe(true);
  expect(fact(sj.sin(new sj.Sym('z')), 'finite')).toBeUndefined();
});

it('reads assumption knowledge bases supplied by extension nodes', () => {
  class Known extends sj.ExtensionExpr {
    readonly assumptions0 = new Map([['finite', true]]);
    constructor() { super('Known', []); }
    withArgs(): sj.Expr { return this; }
  }
  expect(fact(new Known(), 'finite')).toBe(true);
});

it('decides rationality after reducing an unevaluated function', () => {
  const three = Rational.of(3);
  expect(fact(sj.fn('log', [sj.exp(three)], { evaluate: false }), 'rational')).toBe(true);
  expect(fact(sj.fn('sin', [sj.asin(three)], { evaluate: false }), 'rational')).toBe(true);
});

it('classifies integer powers on the complex diagonals', () => {
  const a = sj.symbol('a', { negative: true });
  const b = sj.add(a, sj.mul(-1, sj.I, a));
  for (const n of [-4, -3, -2, 2, 3, 4]) {
    const e = new Pow(b, Rational.of(n));
    expect(fact(e, 'real')).toBe(n % 4 === 0);
    expect(fact(e, 'imaginary')).toBe(Math.abs(n) % 4 === 2);
  }
});

it('reasons about zero integrands, finite logarithms and shifted factorials', () => {
  const x = sj.symbol('x', { complex: true, zero: false });
  const n = sj.symbol('n', { integer: true, nonnegative: true });
  const p = sj.symbol('p', { positive: true });
  expect(fact(new sj.Integral([S.Zero, p, S.Zero, S.One]), 'zero')).toBe(true);
  expect(fact(new sj.Fn('log', [x]), 'complex')).toBe(true);
  expect(fact(new sj.Fn('factorial', [n.add(2)]), 'even')).toBe(true);
  expect(fact(new sj.Fn('factorial', [n]), 'even')).toBeUndefined();
  expect(fact(new sj.Fn('factorial', [n]), 'positive')).toBe(true);
  expect(fact(new sj.Fn('factorial', [n]), 'integer')).toBe(true);
  expect(fact(p.add(2).pow(3).sub(S.Half), 'positive')).toBe(true);
});

it('keeps the dyadic coefficients of imaginary sums exact', () => {
  const e = new sj.Add([sj.mul(new sj.Float(0.866025403784439), S.I), sj.mul(Rational.of(-1, 2), sj.sqrt(3), S.I)]);
  expect(fact(e, 'imaginary')).toBe(true);
  const p = sj.symbol('p', { positive: true });
  expect(fact(p.add(2).pow(3).sub(100), 'positive')).toBeUndefined();
  const y = sj.symbol('y');
  expect(fact(new sj.Fn('factorial', [y]), 'integer')).toBeUndefined();
  expect(fact(new sj.Fn('log', [y]), 'complex')).toBeUndefined();
});

it('detects imaginary sums with both floating and exact parts', () => {
  const e = new sj.Add([new Mul([new sj.Float(1.5), S.I]), new Mul([Rational.of(3, 2), S.I])]);
  expect(fact(e, 'imaginary')).toBe(true);
});

it('classifies an imaginary floating product before the rational conversion hook is loaded', async () => {
  const { impl } = await import('../../src/core/nodes');
  const saved = { ...impl };
  try {
    impl.rationalFromFloat = undefined;
    const e = new sj.Add([sj.mul(new sj.Float(1.5), S.I), S.I]);
    expect(fact(e, 'imaginary')).toBe(true);
  } finally {
    Object.assign(impl, saved);
  }
});

it('infers gamma signs from the floor on negative real intervals', () => {
  const positiveGamma = (z: Expr) => fact(sj.fn('gamma', [z], { evaluate: false }), 'positive');
  expect(positiveGamma(sj.rational(-5, 2))).toBe(false);
  expect(positiveGamma(parse('x + y'))).toBeUndefined();
  expect(positiveGamma(parse('x + 1/2'))).toBeUndefined();
  expect(fact(sj.fn('multigamma', [new sj.Float(0.4), 3], { evaluate: false }), 'real')).toBe(true);
});

it('uses numerical gamma signs when the floor evaluator is unavailable', async () => {
  const { impl } = await import('../../src/core/nodes');
  const evaluator = Object.getOwnPropertyDescriptor(impl, 'fn');
  try {
    delete impl.fn;
    expect(fact(sj.fn('gamma', [sj.rational(-5, 2)], { evaluate: false }), 'positive')).toBe(false);
  } finally {
    if (evaluator) Object.defineProperty(impl, 'fn', evaluator);
  }
});

it('queries special-function assumptions at real and undetermined arguments', () => {
  const p = sj.symbol('p', { positive: true });
  const n = sj.symbol('n', { integer: true });
  const r = sj.symbol('r', { real: true });
  const f = sj.symbol('f', { real: true, integer: false });
  const w = sj.symbol('w');
  const cases: readonly [sj.FnName, string, readonly sj.ExprLike[], boolean | undefined][] = [
    ['erf', 'real', [p], true],
    ['erf', 'real', [w], undefined],
    ['erf', 'imaginary', [w], undefined],
    ['erf', 'finite', [S.Infinity], true],
    ['erfc', 'real', [p], true],
    ['erfc', 'real', [w], undefined],
    ['erf2', 'extended_real', [r, p], true],
    ['erf2', 'extended_real', [w, r], undefined],
    ['beta', 'real', [r, p], true],
    ['beta', 'real', [w, r], undefined],
    ['betainc', 'real', [r, p, 0, 1], true],
    ['betainc', 'real', [w, r, 0, 1], undefined],
    ['besselj', 'extended_real', [n, w], undefined],
    ['gamma', 'real', [-1], false],
    ['gamma', 'real', [new sj.Float(-1)], false],
    ['gamma', 'real', [new sj.Float(2)], true],
    ['gamma', 'real', [new sj.Float(-1.5)], true],
    ['gamma', 'real', [f], true],
    ['gamma', 'positive', [p], true],
    ['loggamma', 'real', [p], true],
    ['loggamma', 'real', [w], undefined],
    ['polygamma', 'real', [p, p], true],
    ['polygamma', 'positive', [1, r], true],
    ['polygamma', 'positive', [2, p], false],
    ['polygamma', 'positive', [1, w], undefined],
    ['polygamma', 'negative', [1, r], false],
    ['polygamma', 'negative', [2, p], true],
    ['polygamma', 'negative', [p, w], undefined],
  ];
  for (const [name, property, args, expected] of cases) {
    expect(fact(sj.fn(name, args, { evaluate: false }), property), `${name}.${property}(${args.join(', ')})`).toBe(expected);
  }
});

it('recognizes factorials and exact values of unevaluated elementary calls', () => {
  const k = sj.symbol('k', { integer: true, nonnegative: true });
  const n = sj.symbol('n', { negative: true, integer: false });
  const w = sj.symbol('w');
  expect(fact(new sj.Fn('factorial', [k.add(3)]), 'composite')).toBe(true);
  expect(fact(new sj.Fn('factorial', [S.Two]), 'composite')).toBe(false);
  expect(fact(new sj.Fn('factorial', [w]), 'composite')).toBeUndefined();
  expect(fact(new sj.Fn('factorial', [k]), 'real')).toBe(true);
  expect(fact(new sj.Fn('factorial', [n]), 'real')).toBe(true);
  expect(fact(new sj.Fn('factorial', [w]), 'real')).toBeUndefined();
  expect(fact(new sj.Fn('sinh', [sj.mul(2, S.I, S.Pi)]), 'zero')).toBe(true);
  expect(fact(new sj.Fn('cosh', [sj.mul(Rational.of(5, 2), S.I, S.Pi)]), 'zero')).toBe(true);
  expect(fact(new sj.Fn('acosh', [S.One]), 'zero')).toBe(true);
  expect(fact(new sj.Fn('sinc', [S.Pi]), 'zero')).toBe(true);
  expect(fact(new sj.Fn('sec', [sj.mul(S.Half, S.Pi)]), 'finite')).toBe(false);
  expect(fact(new sj.Fn('csc', [S.Zero]), 'finite')).toBe(false);
});

it('recognizes exact constants in unevaluated exponentials and trigonometric calls', () => {
  const logThree = new sj.Fn('log', [Rational.of(3)]);
  expect(fact(new Pow(S.E, logThree), 'rational')).toBe(true);
  expect(fact(new Pow(S.E, new sj.Fn('log', [sj.symbol('x')])), 'rational')).toBeUndefined();
  expect(fact(sj.expPolar(0), 'rational')).toBe(true);
  expect(fact(sj.expPolar(sj.symbol('x')), 'rational')).toBeUndefined();
  expect(fact(new sj.Fn('cos', [new sj.Fn('asin', [S.NegOne])]), 'zero')).toBe(true);
});

it('proves zeros of real radicals through exact algebraic identities', () => {
  const radical = sj.sqrt(3);
  const e = sj.add(sj.sqrt(sj.add(1, radical)), sj.sqrt(sj.add(3, sj.mul(3, radical))), sj.neg(sj.sqrt(sj.add(10, sj.mul(6, radical)))));
  expect(fact(e, 'zero')).toBe(true);
  expect(fact(e, 'positive')).toBe(false);
  expect(fact(sj.parse('1 + sqrt(5)'), 'zero')).toBe(false);
  expect(fact(new sj.Add([sj.neg(sj.mul(2, sj.I)), new sj.Pow(sj.add(1, sj.I), sj.S.Two)]), 'zero')).toBeUndefined();
});

it('certifies exact algebraic cancellation before reporting an extended sign', () => {
  const e = sj.parse('-3-sqrt(5)+(-sqrt(10)/2-sqrt(2)/2)**2');
  expect(fact(e, 'extended_positive')).toBe(false);
});
