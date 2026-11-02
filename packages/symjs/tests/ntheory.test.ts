// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * The number theory module (sympy.ntheory): every SymPy doctest example of
 * the ported functions and further cases, with the expected values
 * computed by SymPy 1.14 (printed in Python's form: lists, dicts in
 * insertion order, None for NoMatch/Unsolved).
 */

import { describe, expect, it } from 'vitest';
import { parseExpr } from '../src/index';
import { Expr, Mul, Rational, pi } from '../src/core/nodes';
import { sqrt } from '../src/core/ops';
import { NoMatch, Unsolved } from '../src/core/truth';
import { fn } from '../src/functions/elementary';
import { isprime } from '../src/ntheory/primetest';
import {
  FactorCache,
  MERSENNE_PRIME_EXPONENTS,
  Random,
  Sieve,
  abundance,
  binomialCoefficients,
  binomialCoefficientsList,
  composite,
  compositepi,
  continuedFraction,
  continuedFractionConvergents,
  continuedFractionIterator,
  continuedFractionPeriodic,
  continuedFractionReduce,
  countDigits,
  crt,
  crt1,
  crt2,
  cycleLength,
  digits,
  discreteLog,
  divisorCount,
  divisors,
  dra,
  drm,
  ecm,
  egyptianFraction,
  factorCache,
  factorint,
  factorrat,
  isAbundant,
  isAmicable,
  isDeficient,
  isGaussianPrime,
  isMersennePrime,
  isNthpowResidue,
  isPalindromic,
  isPerfect,
  isPrimitiveRoot,
  isQuadResidue,
  mersennePrimeExponent,
  multinomialCoefficients,
  multinomialCoefficientsIterator,
  multiplicity,
  multiplicityInFactorial,
  nOrder,
  nextprime,
  npartitions,
  nthrootMod,
  perfectPower,
  polynomialCongruence,
  pollardPm1,
  pollardRho,
  prevprime,
  prime,
  primefactors,
  primerange,
  primitiveRoot,
  primorial,
  properDivisorCount,
  properDivisors,
  qs,
  qsFactor,
  quadraticCongruence,
  quadraticResidues,
  randprime,
  seed,
  sieve,
  smoothnessP,
  solveCongruence,
  sqrtMod,
  sqrtModIter,
  symmetricResidue,
} from '../src/ntheory/index';

const P = (s: string): Expr => parseExpr(s);

/** Python's printed form of a result. */
function py(v: unknown): string {
  if (v === NoMatch || v === Unsolved || v === undefined || v === null) return 'None';
  if (v === true) return 'True';
  if (v === false) return 'False';
  if (typeof v === 'bigint' || typeof v === 'number' || typeof v === 'string') return String(v);
  if (v instanceof Expr) return v.toString();
  if (Array.isArray(v)) return `[${v.map(py).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${py(k)}: ${py(w)}`).join(', ')}}`;
  if (v instanceof Set) return `[${[...v].map(py).join(', ')}]`;
  return Object.prototype.toString.call(v);
}

const sortedEntries = (m: Map<bigint, bigint>): [bigint, bigint][] => [...m].sort((a, b) => (a[0] < b[0] ? -1 : 1));
function take<T>(g: Iterator<T>, k: number): T[] {
  const out: T[] = [];
  for (let i = 0; i < k; i++) {
    const r = g.next();
    if (r.done === true) break;
    out.push(r.value);
  }
  return out;
}

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
    ["[10,11,12,13,14].map((i) => [i, nextprime(i)])", () => [10,11,12,13,14].map((i) => [i, nextprime(i)]), "[[10, 11], [11, 13], [12, 13], [13, 17], [14, 17]]"],
    ["nextprime(2, 2)", () => nextprime(2, 2), "5"],
    ["[10,11,12,13,14].map((i) => [i, prevprime(i)])", () => [10,11,12,13,14].map((i) => [i, prevprime(i)]), "[[10, 7], [11, 7], [12, 11], [13, 11], [14, 13]]"],
    ["[prime(10), prime(1), prime(100000), prime(1000), prime(5000), prime(25)]", () => [prime(10), prime(1), prime(100000), prime(1000), prime(5000), prime(25)], "[29, 2, 1299709, 7919, 48611, 97]"],
    ["[...primerange(19)]", () => [...primerange(19)], "[2, 3, 5, 7, 11, 13, 17]"],
    ["[...primerange(7, 19)]", () => [...primerange(7, 19)], "[7, 11, 13, 17]"],
    ["[...primerange(prime(10) + 1n)]", () => [...primerange(prime(10) + 1n)], "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"],
    ["[...primerange(1000000, 1000100)]", () => [...primerange(1000000, 1000100)], "[1000003, 1000033, 1000037, 1000039, 1000081, 1000099]"],
    ["[...sieve.primerange(1, 30)]", () => [...sieve.primerange(1, 30)], "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"],
    ["[...sieve.primerange(19)]", () => [...sieve.primerange(19)], "[2, 3, 5, 7, 11, 13, 17]"],
    ["[...sieve.primerange(7, 19)]", () => [...sieve.primerange(7, 19)], "[7, 11, 13, 17]"],
    ["[...sieve.totientrange(7, 18)]", () => [...sieve.totientrange(7, 18)], "[6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16]"],
    ["[...sieve.mobiusrange(7, 18)]", () => [...sieve.mobiusrange(7, 18)], "[-1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1]"],
    ["sieve.search(25)", () => sieve.search(25), "[9, 10]"],
    ["sieve.search(23)", () => sieve.search(23), "[9, 9]"],
    ["[primorial(4), primorial(4, { nth: false }), primorial(1), primorial(1, { nth: false }), primorial(sqrt(101), { nth: false })]", () => [primorial(4), primorial(4, { nth: false }), primorial(1), primorial(1, { nth: false }), primorial(sqrt(101), { nth: false })], "[210, 6, 2, 1, 210]"],
    ["factorint(primorial(4) + 1n)", () => factorint(primorial(4) + 1n), "{211: 1}"],
    ["factorint(primorial(4) - 1n)", () => factorint(primorial(4) - 1n), "{11: 1, 19: 1}"],
    ["primefactors(11n * 13n * 17n * 19n + 1n).filter((p) => ![11n, 13n, 17n, 19n].includes(p))", () => primefactors(11n * 13n * 17n * 19n + 1n).filter((p) => ![11n, 13n, 17n, 19n].includes(p)), "[2, 5, 31, 149]"],
    ["[composite(36), composite(1), composite(17737), composite(100000)]", () => [composite(36), composite(1), composite(17737), composite(100000)], "[52, 4, 20000, 110487]"],
    ["[compositepi(25), compositepi(1000), compositepi(10**6)]", () => [compositepi(25), compositepi(1000), compositepi(10**6)], "[15, 831, 921501]"],
    ["cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n).next().value", () => cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n).next().value, "[6, 3]"],
    ["[...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { values: true })]", () => [...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { values: true })], "[4, 17, 35, 2, 5, 26, 14, 44, 50, 2, 5, 26, 14]"],
    ["cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4 }).next().value", () => cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4 }).next().value, "[4, None]"],
    ["[...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4, values: true })]", () => [...cycleLength((i: bigint) => (i * i + 1n) % 51n, 4n, { nmax: 4, values: true })], "[4, 17, 35, 2]"],
    ["[0n,1n,2n,3n,4n].map((s) => cycleLength((x: bigint) => (2048n * x * x + 32767n) % 16843009n, s).next().value)", () => [0n,1n,2n,3n,4n].map((s) => cycleLength((x: bigint) => (2048n * x * x + 32767n) % 16843009n, s).next().value), "[[2489, 43], [78, 121], [1482, 100], [1482, 286], [1482, 101]]"],
    ["cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n).next().value", () => cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n).next().value, "[3, 3]"],
    ["[...cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n, { values: true })]", () => [...cycleLength((x: bigint) => (x * x + 12n) % 17n, 2n, { values: true })], "[2, 16, 13, 11, 14, 4]"],
    ["[isMersennePrime(6), isMersennePrime(127), isMersennePrime(2n**61n - 1n), isMersennePrime(2n**67n - 1n)]", () => [isMersennePrime(6), isMersennePrime(127), isMersennePrime(2n**61n - 1n), isMersennePrime(2n**67n - 1n)], "[False, True, True, False]"],
    ["['2+3*I', '3', '7*I', '1+I', '4+I', '-3', '5', '11*I', '2*I'].map((z) => isGaussianPrime(P(z)))", () => ['2+3*I', '3', '7*I', '1+I', '4+I', '-3', '5', '11*I', '2*I'].map((z) => isGaussianPrime(P(z))), "[True, True, True, True, True, True, False, True, False]"],
    ["[divisors(24), divisorCount(24)]", () => [divisors(24), divisorCount(24)], "[[1, 2, 3, 4, 6, 8, 12, 24], 8]"],
    ["[...divisors(120, { generator: true })]", () => [...divisors(120, { generator: true })], "[1, 2, 4, 8, 3, 6, 12, 24, 5, 10, 20, 40, 15, 30, 60, 120]"],
    ["[properDivisors(24), properDivisorCount(24)]", () => [properDivisors(24), properDivisorCount(24)], "[[1, 2, 3, 4, 6, 8, 12], 7]"],
    ["[...properDivisors(120, { generator: true })]", () => [...properDivisors(120, { generator: true })], "[1, 2, 4, 8, 3, 6, 12, 24, 5, 10, 20, 40, 15, 30, 60]"],
    ["[divisorCount(6), divisorCount(6, 2), divisorCount(6, 1, { proper: true }), divisorCount(0), divisorCount(-12), divisorCount(12, 0)]", () => [divisorCount(6), divisorCount(6, 2), divisorCount(6, 1, { proper: true }), divisorCount(0), divisorCount(-12), divisorCount(12, 0)], "[4, 2, 3, 0, 6, 0]"],
    ["[properDivisorCount(6), properDivisorCount(6, 2)]", () => [properDivisorCount(6), properDivisorCount(6, 2)], "[3, 1]"],
    ["[divisors(1), divisors(0), divisors(-12), properDivisors(1)]", () => [divisors(1), divisors(0), divisors(-12), properDivisors(1)], "[[1], [], [1, 2, 3, 4, 6, 12], []]"],
    ["factorint(2000)", () => factorint(2000), "{2: 4, 5: 3}"],
    ["factorint(65537)", () => factorint(65537), "{65537: 1}"],
    ["factorint(1407633717262338957430697921446883n, { limit: 10000 })", () => factorint(1407633717262338957430697921446883n, { limit: 10000 }), "{7: 1, 991: 1, 202916782076162456022877024859: 1}"],
    ["factorint(3n * 101n ** 7n, { limit: 5 })", () => factorint(3n * 101n ** 7n, { limit: 5 }), "{3: 1, 101: 7}"],
    ["factorint(24, { multiple: true })", () => factorint(24, { multiple: true }), "[2, 2, 2, 3]"],
    ["factorint(1764)", () => factorint(1764), "{2: 2, 3: 2, 7: 2}"],
    ["factorint(factorint(1764, { visual: true }))", () => factorint(factorint(1764, { visual: true })), "{2: 2, 3: 2, 7: 2}"],
    ["factorint(factorint(new Map([[4n, 2n], [12n, 3n]])))", () => factorint(factorint(new Map([[4n, 2n], [12n, 3n]]))), "{2: 10, 3: 3}"],
    ["factorint(new Mul([Rational.of(4), Rational.of(12)]))", () => factorint(new Mul([Rational.of(4), Rational.of(12)])), "{2: 4, 3: 1}"],
    ["factorint(12345678910111213141516n)", () => factorint(12345678910111213141516n), "{2: 2, 1231026625769: 1, 2507191691: 1}"],
    ["[factorint(0), factorint(1), factorint(-1), factorint(-12)]", () => [factorint(0), factorint(1), factorint(-1), factorint(-12)], "[{0: 1}, {}, {-1: 1}, {2: 2, 3: 1, -1: 1}]"],
    ["factorint(fn('factorial', [30], { evaluate: false }))", () => factorint(fn('factorial', [30], { evaluate: false })), "{2: 26, 3: 14, 5: 7, 7: 4, 11: 2, 13: 2, 17: 1, 19: 1, 23: 1, 29: 1}"],
    ["factorint(fn('factorial', [12], { evaluate: false }))", () => factorint(fn('factorial', [12], { evaluate: false })), "{2: 10, 3: 5, 5: 2, 7: 1, 11: 1}"],
    ["factorint(25645121643901801n)", () => factorint(25645121643901801n), "{5394769: 1, 4753701529: 1}"],
    ["factorint(9804659461513846513n)", () => factorint(9804659461513846513n), "{4641991: 1, 2112166839943: 1}"],
    ["factorint(2n ** 128n + 1n)", () => factorint(2n ** 128n + 1n), "{59649589127497217: 1, 5704689200685129054721: 1}"],
    ["factorint(10n ** 30n + 57n)", () => factorint(10n ** 30n + 57n), "{1000000000000000000000000000057: 1}"],
    ["factorint(3n ** 40n * 1000003n ** 3n)", () => factorint(3n ** 40n * 1000003n ** 3n), "{3: 40, 1000003: 3}"],
    ["factorint(1000003n ** 2n * 1000033n)", () => factorint(1000003n ** 2n * 1000033n), "{1000033: 1, 1000003: 2}"],
    ["factorint(2n ** 64n - 1n)", () => factorint(2n ** 64n - 1n), "{3: 1, 5: 1, 17: 1, 257: 1, 641: 1, 65537: 1, 6700417: 1}"],
    ["factorint(600851475143n, { useTrial: false })", () => factorint(600851475143n, { useTrial: false }), "{71: 1, 839: 1, 1471: 1, 6857: 1}"],
    ["factorint(4096n * 13n ** 6n, { limit: 3 })", () => factorint(4096n * 13n ** 6n, { limit: 3 }), "{2: 12, 13: 6}"],
    ["sortedEntries(factorint(10000000001n, { limit: 200 }))", () => sortedEntries(factorint(10000000001n, { limit: 200 })), "[[101, 1], [99009901, 1]]"],
    ["[isprime(99009901), primefactors(10000000001n, { limit: 300 })]", () => [isprime(99009901), primefactors(10000000001n, { limit: 300 })], "[False, [101]]"],
    ["[primefactors(6), primefactors(-5), primefactors(123456), primefactors(1), primefactors(0)]", () => [primefactors(6), primefactors(-5), primefactors(123456), primefactors(1), primefactors(0)], "[[2, 3], [5], [2, 3, 643], [], []]"],
    ["sortedEntries(factorint(123456))", () => sortedEntries(factorint(123456)), "[[2, 6], [3, 1], [643, 1]]"],
    ["[factorrat(Rational.of(8, 9)), factorrat(Rational.of(-1, 987))]", () => [factorrat(Rational.of(8, 9)), factorrat(Rational.of(-1, 987))], "[{2: 3, 3: -2}, {-1: 1, 3: -1, 7: -1, 47: -1}]"],
    ["factorrat(Rational.of(25, 12), { multiple: true })", () => factorrat(Rational.of(25, 12), { multiple: true }), "[1/3, 1/2, 1/2, 5, 5]"],
    ["[8, 5, 25, 125, 250].map((n) => multiplicity(5, n))", () => [8, 5, 25, 125, 250].map((n) => multiplicity(5, n)), "[0, 1, 2, 3, 3]"],
    ["[multiplicity(3, Rational.of(1, 9)), multiplicity(Rational.of(2, 3), Rational.of(8, 27)), multiplicity(Rational.of(1, 2), Rational.of(3, 8))]", () => [multiplicity(3, Rational.of(1, 9)), multiplicity(Rational.of(2, 3), Rational.of(8, 27)), multiplicity(Rational.of(1, 2), Rational.of(3, 8))], "[-2, 3, 3]"],
    ["multiplicity(fn('factorial', [25]), fn('factorial', [2n ** 100n], { evaluate: false }))", () => multiplicity(fn('factorial', [25]), fn('factorial', [2n ** 100n], { evaluate: false })), "52818775009509558395695966887"],
    ["[multiplicityInFactorial(2, 3), multiplicityInFactorial(10, 25), multiplicityInFactorial(fn('factorial', [25]), 2n ** 100n)]", () => [multiplicityInFactorial(2, 3), multiplicityInFactorial(10, 25), multiplicityInFactorial(fn('factorial', [25]), 2n ** 100n)], "[1, 6, 52818775009509558395695966887]"],
    ["[perfectPower(16), perfectPower(16, undefined, { big: false }), perfectPower(-4), perfectPower(-8)]", () => [perfectPower(16), perfectPower(16, undefined, { big: false }), perfectPower(-4), perfectPower(-8)], "[[2, 4], [4, 2], False, [-2, 3]]"],
    ["[perfectPower(Rational.of(1, 8)), perfectPower(Rational.of(-27, 8)), perfectPower(Rational.of(4, 9)), perfectPower(Rational.of(4, 27))]", () => [perfectPower(Rational.of(1, 8)), perfectPower(Rational.of(-27, 8)), perfectPower(Rational.of(4, 9)), perfectPower(Rational.of(4, 27))], "[[1/2, 3], [-3/2, 3], [2/3, 2], False]"],
    ["[perfectPower(3 ** 8, [9]), perfectPower(3 ** 8, [2, 4, 8]), perfectPower(3 ** 8, [4, 8], { big: false })]", () => [perfectPower(3 ** 8, [9]), perfectPower(3 ** 8, [2, 4, 8]), perfectPower(3 ** 8, [4, 8], { big: false })], "[False, [3, 8], [9, 4]]"],
    ["[perfectPower(2n ** 120n), perfectPower(3n ** 100n * 5n ** 50n), perfectPower(1000003n ** 7n), perfectPower(2n**64n, undefined, { big: false }), perfectPower(-(7n**15n), undefined, { big: false }), perfectPower(10n**40n + 1n), perfectPower(6n ** 20n, undefined, { factor: false })]", () => [perfectPower(2n ** 120n), perfectPower(3n ** 100n * 5n ** 50n), perfectPower(1000003n ** 7n), perfectPower(2n**64n, undefined, { big: false }), perfectPower(-(7n**15n), undefined, { big: false }), perfectPower(10n**40n + 1n), perfectPower(6n ** 20n, undefined, { factor: false })], "[[2, 120], [45, 50], [1000003, 7], [4294967296, 2], [-16807, 3], False, [6, 20]]"],
    ["pollardRho(16843009n, { F: (x: bigint) => (2048n * x * x + 32767n) % 16843009n })", () => pollardRho(16843009n, { F: (x: bigint) => (2048n * x * x + 32767n) % 16843009n }), "257"],
    ["[pollardRho(16843009n, { a: 16843007n, retries: 0 }), pollardRho(16843009n, { a: 16843007n, retries: 1 })]", () => [pollardRho(16843009n, { a: 16843007n, retries: 0 }), pollardRho(16843009n, { a: 16843007n, retries: 1 })], "[None, 257]"],
    ["[pollardRho(10403n), pollardRho(1000003n * 1000033n), pollardRho(8051n, { s: 3, a: 2 }), pollardRho(455459n, { maxSteps: 3, retries: 3 })]", () => [pollardRho(10403n), pollardRho(1000003n * 1000033n), pollardRho(8051n, { s: 3, a: 2 }), pollardRho(455459n, { maxSteps: 3, retries: 3 })], "[101, 1000033, 83, None]"],
    ["smoothnessP(257n * 1009n)", () => smoothnessP(257n * 1009n), "[-1, [[257, [1, 2, 256]], [1009, [1, 7, 16]]]]"],
    ["[pollardPm1(257n * 1009n, { B: 16, a: 3 }), pollardPm1(257n * 1009n, { B: 256 }), pollardPm1(257n * 1009n, { B: 256, a: 257 })]", () => [pollardPm1(257n * 1009n, { B: 16, a: 3 }), pollardPm1(257n * 1009n, { B: 256 }), pollardPm1(257n * 1009n, { B: 256, a: 257 })], "[1009, None, 1009]"],
    ["[pollardPm1(21477639576571n), pollardPm1(21477639576571n, { B: 2000 }), pollardPm1(21477639576571n, { B: 1786 }), pollardPm1(21477639576571n, { B: 1787 })]", () => [pollardPm1(21477639576571n), pollardPm1(21477639576571n, { B: 2000 }), pollardPm1(21477639576571n, { B: 1786 }), pollardPm1(21477639576571n, { B: 1787 })], "[None, 4410317, None, 4410317]"],
    ["[pollardPm1(1000003n * 1000033n, { retries: 5 }), pollardPm1(21477639576571n, { B: 100, retries: 3, seed: 7 })]", () => [pollardPm1(1000003n * 1000033n, { retries: 5 }), pollardPm1(21477639576571n, { B: 100, retries: 3, seed: 7 })], "[None, None]"],
    ["smoothnessP(21477639576571n, { visual: true })", () => smoothnessP(21477639576571n, { visual: true }), "p**i=4410317**1 has p-1 B=1787, B-pow=1787\np**i=4869863**1 has p-1 B=2434931, B-pow=2434931"],
    ["[factorint(4410317 - 1), factorint(4869863 - 1)]", () => [factorint(4410317 - 1), factorint(4869863 - 1)], "[{2: 2, 617: 1, 1787: 1}, {2: 1, 2434931: 1}]"],
    ["[mersennePrimeExponent(1), mersennePrimeExponent(20)]", () => [mersennePrimeExponent(1), mersennePrimeExponent(20)], "[2, 4423]"],
    ["[isPerfect(20), isPerfect(6), isPerfect(8128), isPerfect(2n**126n * (2n**127n - 1n)), isPerfect(2n**88n*(2n**89n-1n)), isPerfect(28n*3n)]", () => [isPerfect(20), isPerfect(6), isPerfect(8128), isPerfect(2n**126n * (2n**127n - 1n)), isPerfect(2n**88n*(2n**89n-1n)), isPerfect(28n*3n)], "[False, True, True, True, True, False]"],
    ["[isAbundant(20), isAbundant(15), isDeficient(20), isDeficient(15), isAbundant(6), isDeficient(6)]", () => [isAbundant(20), isAbundant(15), isDeficient(20), isDeficient(15), isAbundant(6), isDeficient(6)], "[True, False, False, True, False, False]"],
    ["[isAmicable(220, 284), isAmicable(220, 220), isAmicable(1184, 1210), isAmicable(10, 20)]", () => [isAmicable(220, 284), isAmicable(220, 220), isAmicable(1184, 1210), isAmicable(10, 20)], "[True, False, True, False]"],
    ["[abundance(6), abundance(10), abundance(12)]", () => [abundance(6), abundance(10), abundance(12)], "[0, -2, 4]"],
    ["[dra(3110, 12), drm(9876, 10), drm(49, 10), dra(0, 10), dra(-38, 10), drm(277777788888899n, 10)]", () => [dra(3110, 12), drm(9876, 10), drm(49, 10), dra(0, 10), dra(-38, 10), drm(277777788888899n, 10)], "[8, 0, 8, 0, 2, 0]"],
    ["[isPrimitiveRoot(3, 10), isPrimitiveRoot(9, 10), nOrder(3, 10), nOrder(9, 10), nOrder(3, 7), nOrder(4, 7), nOrder(2, 1000003n * 3n)]", () => [isPrimitiveRoot(3, 10), isPrimitiveRoot(9, 10), nOrder(3, 10), nOrder(9, 10), nOrder(3, 7), nOrder(4, 7), nOrder(2, 1000003n * 3n)], "[True, False, 4, 2, 6, 3, 1000002]"],
    ["[isQuadResidue(21, 100), isQuadResidue(21, 120)]", () => [isQuadResidue(21, 100), isQuadResidue(21, 120)], "[True, False]"],
    ["[0,1,2,3,4,5,6].filter((j) => isQuadResidue(j, 7))", () => [0,1,2,3,4,5,6].filter((j) => isQuadResidue(j, 7)), "[0, 1, 2, 4]"],
    ["[2, 3, 8, 12, 16, 27, 45, 72, 100, 96].flatMap((m) => [0,1,2,3,5,7,9,11,12,16,18,25,27,36].map((a) => isQuadResidue(a, m)))", () => [2, 3, 8, 12, 16, 27, 45, 72, 100, 96].flatMap((m) => [0,1,2,3,5,7,9,11,12,16,18,25,27,36].map((a) => isQuadResidue(a, m))), "[True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, False, True, False, True, True, False, True, True, True, True, True, True, True, True, False, False, False, False, True, False, True, True, False, True, False, True, True, True, False, False, False, False, True, False, True, True, False, True, False, True, True, True, False, False, False, False, True, False, False, True, False, True, False, True, True, True, False, False, False, True, True, False, False, True, False, True, True, True, True, True, False, False, False, False, True, False, False, True, False, True, False, True, True, True, False, False, False, False, True, False, False, True, False, True, False, True, True, True, False, False, False, False, True, False, False, True, False, True, False, True, True, True, False, False, False, False, True, False, False, True, False, True, False, True]"],
    ["[sqrtMod(11, 43), sqrtMod(17, 32, true), sqrtMod(2, 7), sqrtMod(3, 7), sqrtMod(0, 49, true), sqrtMod(9, 27, true), sqrtMod(4, 12, true), sqrtMod(1, 1), sqrtMod(41, 10n**9n + 7n)]", () => [sqrtMod(11, 43), sqrtMod(17, 32, true), sqrtMod(2, 7), sqrtMod(3, 7), sqrtMod(0, 49, true), sqrtMod(9, 27, true), sqrtMod(4, 12, true), sqrtMod(1, 1), sqrtMod(41, 10n**9n + 7n)], "[21, [7, 9, 23, 25], 3, None, [0, 7, 14, 21, 28, 35, 42], [3, 6, 12, 15, 21, 24], [2, 4, 8, 10], 0, None]"],
    ["[[...sqrtModIter(11, 43)], [...sqrtModIter(4, 60)], [...sqrtModIter(9, 3*3*5*5*7)], [...sqrtModIter(0, 36)], [...sqrtModIter(16, 2*9*25)]]", () => [[...sqrtModIter(11, 43)], [...sqrtModIter(4, 60)], [...sqrtModIter(9, 3*3*5*5*7)], [...sqrtModIter(0, 36)], [...sqrtModIter(16, 2*9*25)]], "[[21, 22], [52, 22, 32, 2, 28, 58, 8, 38], [1053, 3, 297, 528, 822, 1278, 1347, 228, 522, 753, 1047, 1572], [0, 18, 12, 30, 24, 6], [4, 104, 346, 446]]"],
    ["[sqrtMod(10, 13n * 10n**9n + 7n, true), sqrtMod(1234, 2n**20n, true).length, sqrtMod(3, 1009 ** 3)]", () => [sqrtMod(10, 13n * 10n**9n + 7n, true), sqrtMod(1234, 2n**20n, true).length, sqrtMod(3, 1009 ** 3)], "[[], 0, 490503301]"],
    ["[quadraticResidues(7), quadraticResidues(12)]", () => [quadraticResidues(7), quadraticResidues(12)], "[[0, 1, 2, 4], [0, 1, 4, 9]]"],
    ["[primitiveRoot(19), primitiveRoot(21), primitiveRoot(50, { smallest: false }), primitiveRoot(50), primitiveRoot(2), primitiveRoot(4), primitiveRoot(8), primitiveRoot(25), primitiveRoot(2 * 3 ** 5), primitiveRoot(2 * 3 ** 5, { smallest: false }), primitiveRoot(1000003), primitiveRoot(41), primitiveRoot(23), primitiveRoot(9, {smallest: false}), primitiveRoot(40487*40487), primitiveRoot(40487*40487, {smallest: false})]", () => [primitiveRoot(19), primitiveRoot(21), primitiveRoot(50, { smallest: false }), primitiveRoot(50), primitiveRoot(2), primitiveRoot(4), primitiveRoot(8), primitiveRoot(25), primitiveRoot(2 * 3 ** 5), primitiveRoot(2 * 3 ** 5, { smallest: false }), primitiveRoot(1000003), primitiveRoot(41), primitiveRoot(23), primitiveRoot(9, {smallest: false}), primitiveRoot(40487*40487), primitiveRoot(40487*40487, {smallest: false})], "[2, None, 27, 3, 1, 3, None, 2, 5, 245, 2, 6, 5, 2, 10, 40492]"],
    ["[nthrootMod(11, 4, 19), nthrootMod(11, 4, 19, true), nthrootMod(68, 3, 109), nthrootMod(3, 2, 7), nthrootMod(16, 4, 64, true), nthrootMod(1, 3, 1000, true), nthrootMod(2, 3, 7, true), nthrootMod(5, 1, 7), nthrootMod(8, 3, 1000003n * 1009n, true), nthrootMod(81, 4, 3 ** 7, true)]", () => [nthrootMod(11, 4, 19), nthrootMod(11, 4, 19, true), nthrootMod(68, 3, 109), nthrootMod(3, 2, 7), nthrootMod(16, 4, 64, true), nthrootMod(1, 3, 1000, true), nthrootMod(2, 3, 7, true), nthrootMod(5, 1, 7), nthrootMod(8, 3, 1000003n * 1009n, true), nthrootMod(81, 4, 3 ** 7, true)], "[8, [8, 11], 23, None, [2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 46, 50, 54, 58, 62], [1], [], 5, [2, 14999044, 71999215, 129000389, 200999602, 808003423, 865003594, 952002858, 994003981], [3, 78, 84, 159, 165, 240, 246, 321, 327, 402, 408, 483, 489, 564, 570, 645, 651, 726, 732, 807, 813, 888, 894, 969, 975, 1050, 1056, 1131, 1137, 1212, 1218, 1293, 1299, 1374, 1380, 1455, 1461, 1536, 1542, 1617, 1623, 1698, 1704, 1779, 1785, 1860, 1866, 1941, 1947, 2022, 2028, 2103, 2109, 2184]]"],
    ["[isNthpowResidue(2, 3, 7), isNthpowResidue(8, 3, 1000), isNthpowResidue(5, 0, 7), isNthpowResidue(1, 0, 7), isNthpowResidue(16, 4, 64), isNthpowResidue(3, 4, 81), isNthpowResidue(32, 10, 1024), isNthpowResidue(10, 2, 13)]", () => [isNthpowResidue(2, 3, 7), isNthpowResidue(8, 3, 1000), isNthpowResidue(5, 0, 7), isNthpowResidue(1, 0, 7), isNthpowResidue(16, 4, 64), isNthpowResidue(3, 4, 81), isNthpowResidue(32, 10, 1024), isNthpowResidue(10, 2, 13)], "[False, True, False, True, True, False, False, True]"],
    ["[discreteLog(41, 15, 7), discreteLog(587, 2n**9n, 2), discreteLog(2456747, 3n**51n, 3), discreteLog(32942478, 11n**127n, 11), discreteLog(5779, 3528, 6215), discreteLog(1000003, 123456, 2), discreteLog(2n**61n - 1n, 10n**12n, 37n)]", () => [discreteLog(41, 15, 7), discreteLog(587, 2n**9n, 2), discreteLog(2456747, 3n**51n, 3), discreteLog(32942478, 11n**127n, 11), discreteLog(5779, 3528, 6215), discreteLog(1000003, 123456, 2), discreteLog(2n**61n - 1n, 10n**12n, 37n)], "[3, 9, 51, 127, 687, 864664, 1351870857717611844]"],
    ["[quadraticCongruence(2, 5, 3, 7), quadraticCongruence(8, 6, 4, 15), quadraticCongruence(1, 0, -1, 8), quadraticCongruence(0, 3, 6, 9), quadraticCongruence(1, 1, 0, 2), quadraticCongruence(6, 4, 2, 12), quadraticCongruence(4, 4, 1, 25)]", () => [quadraticCongruence(2, 5, 3, 7), quadraticCongruence(8, 6, 4, 15), quadraticCongruence(1, 0, -1, 8), quadraticCongruence(0, 3, 6, 9), quadraticCongruence(1, 1, 0, 2), quadraticCongruence(6, 4, 2, 12), quadraticCongruence(4, 4, 1, 25)], "[[2, 6], [], [1, 3, 5, 7], [7, 1, 4], [0, 1], [1, 7], [2, 7, 12, 17, 22]]"],
    ["[polynomialCongruence(P('x**6 - 2*x**5 - 35'), 6125), polynomialCongruence(P('x**3 - 2'), 1000003), polynomialCongruence(P('x**4 + x + 1'), 1323), polynomialCongruence(P('x**2 + 3*x + 2'), 105), polynomialCongruence(P('5*x + 3'), 7), polynomialCongruence(P('x**3 + 3*x**2 + 3*x + 2'), 9), polynomialCongruence(P('x**5 - 1'), 11**2)]", () => [polynomialCongruence(P('x**6 - 2*x**5 - 35'), 6125), polynomialCongruence(P('x**3 - 2'), 1000003), polynomialCongruence(P('x**4 + x + 1'), 1323), polynomialCongruence(P('x**2 + 3*x + 2'), 105), polynomialCongruence(P('5*x + 3'), 7), polynomialCongruence(P('x**3 + 3*x**2 + 3*x + 2'), 9), polynomialCongruence(P('x**5 - 1'), 11**2)], "[[3257], [], [], [13, 19, 34, 68, 83, 89, 103, 104], [5], [1, 4, 7], [1, 3, 9, 27, 81]]"],
    ["[crt([99, 97, 95], [49, 76, 65]), crt([12, 6, 17], [3, 4, 2], { check: false }), crt([12, 6, 17], [3, 4, 2]), crt([3, 6], [2, 5]), crt([5, 7], [3, 4], { symmetric: true })]", () => [crt([99, 97, 95], [49, 76, 65]), crt([12, 6, 17], [3, 4, 2], { check: false }), crt([12, 6, 17], [3, 4, 2]), crt([3, 6], [2, 5]), crt([5, 7], [3, 4], { symmetric: true })], "[[639985, 912285], [954, 1224], None, [5, 6], [-17, 35]]"],
    ["[solveCongruence([[2, 3], [3, 5], [2, 7]]), solveCongruence([[2, 3], [4, 6]]), solveCongruence([[2, 3], [5, 6]]), solveCongruence([[2, 3], [5, 6]], { symmetric: true }), solveCongruence([[1, 4], [3, 6], [5, 10]]), solveCongruence([[3, 9], [3, 9]])]", () => [solveCongruence([[2, 3], [3, 5], [2, 7]]), solveCongruence([[2, 3], [4, 6]]), solveCongruence([[2, 3], [5, 6]]), solveCongruence([[2, 3], [5, 6]], { symmetric: true }), solveCongruence([[1, 4], [3, 6], [5, 10]]), solveCongruence([[3, 9], [3, 9]])], "[[23, 105], None, [5, 6], [-1, 6], [45, 60], [3, 9]]"],
    ["binomialCoefficients(9)", () => binomialCoefficients(9), "{[0, 9]: 1, [9, 0]: 1, [1, 8]: 9, [8, 1]: 9, [2, 7]: 36, [7, 2]: 36, [3, 6]: 84, [6, 3]: 84, [4, 5]: 126, [5, 4]: 126}"],
    ["binomialCoefficientsList(9)", () => binomialCoefficientsList(9), "[1, 9, 36, 84, 126, 126, 84, 36, 9, 1]"],
    ["multinomialCoefficients(2, 5)", () => multinomialCoefficients(2, 5), "{[0, 5]: 1, [5, 0]: 1, [1, 4]: 5, [4, 1]: 5, [2, 3]: 10, [3, 2]: 10}"],
    ["multinomialCoefficients(3, 3)", () => multinomialCoefficients(3, 3), "{[3, 0, 0]: 1, [2, 1, 0]: 3, [1, 2, 0]: 3, [0, 3, 0]: 1, [2, 0, 1]: 3, [1, 1, 1]: 6, [0, 2, 1]: 3, [1, 0, 2]: 3, [0, 1, 2]: 3, [0, 0, 3]: 1}"],
    ["multinomialCoefficients(5, 2)", () => multinomialCoefficients(5, 2), "{[2, 0, 0, 0, 0]: 1, [1, 1, 0, 0, 0]: 2, [0, 2, 0, 0, 0]: 1, [1, 0, 1, 0, 0]: 2, [0, 1, 1, 0, 0]: 2, [0, 0, 2, 0, 0]: 1, [1, 0, 0, 1, 0]: 2, [0, 1, 0, 1, 0]: 2, [0, 0, 1, 1, 0]: 2, [0, 0, 0, 2, 0]: 1, [1, 0, 0, 0, 1]: 2, [0, 1, 0, 0, 1]: 2, [0, 0, 1, 0, 1]: 2, [0, 0, 0, 1, 1]: 2, [0, 0, 0, 0, 2]: 1}"],
    ["[multinomialCoefficients(0, 0), multinomialCoefficients(0, 3), multinomialCoefficients(3, 0), multinomialCoefficients(1, 4)]", () => [multinomialCoefficients(0, 0), multinomialCoefficients(0, 3), multinomialCoefficients(3, 0), multinomialCoefficients(1, 4)], "[{[]: 1}, {}, {[0, 0, 0]: 1}, {[4]: 1}]"],
    ["[...multinomialCoefficientsIterator(6, 2)]", () => [...multinomialCoefficientsIterator(6, 2)], "[[[2, 0, 0, 0, 0, 0], 1], [[1, 1, 0, 0, 0, 0], 2], [[0, 2, 0, 0, 0, 0], 1], [[1, 0, 1, 0, 0, 0], 2], [[0, 1, 1, 0, 0, 0], 2], [[0, 0, 2, 0, 0, 0], 1], [[1, 0, 0, 1, 0, 0], 2], [[0, 1, 0, 1, 0, 0], 2], [[0, 0, 1, 1, 0, 0], 2], [[0, 0, 0, 2, 0, 0], 1], [[1, 0, 0, 0, 1, 0], 2], [[0, 1, 0, 0, 1, 0], 2], [[0, 0, 1, 0, 1, 0], 2], [[0, 0, 0, 1, 1, 0], 2], [[0, 0, 0, 0, 2, 0], 1], [[1, 0, 0, 0, 0, 1], 2], [[0, 1, 0, 0, 0, 1], 2], [[0, 0, 1, 0, 0, 1], 2], [[0, 0, 0, 1, 0, 1], 2], [[0, 0, 0, 0, 1, 1], 2], [[0, 0, 0, 0, 0, 2], 1]]"],
    ["[continuedFractionPeriodic(3, 2, 7), continuedFractionPeriodic(1, 2, 5), continuedFractionPeriodic(4, 3, 0), continuedFractionPeriodic(4, 3, 49), continuedFractionPeriodic(-3, 2, 7), continuedFractionPeriodic(1, -3, 13), continuedFractionPeriodic(2, 3, 5, -1), continuedFractionPeriodic(0, 1, 2), continuedFractionPeriodic(5, 1, 0, 0)]", () => [continuedFractionPeriodic(3, 2, 7), continuedFractionPeriodic(1, 2, 5), continuedFractionPeriodic(4, 3, 0), continuedFractionPeriodic(4, 3, 49), continuedFractionPeriodic(-3, 2, 7), continuedFractionPeriodic(1, -3, 13), continuedFractionPeriodic(2, 3, 5, -1), continuedFractionPeriodic(0, 1, 2), continuedFractionPeriodic(5, 1, 0, 0)], "[[2, [1, 4, 1, 1]], [[1]], [1, 3], [3, 1, 2], [-1, [1, 4, 1, 1]], [-2, 2, [6, 1, 1, 1, 1]], [-1, 1, 11, [1, 2, 2, 2, 1, 12]], [1, [2]], [5]]"],
    ["[[...continuedFractionIterator(Rational.of(3, 8))], [...continuedFractionIterator(Rational.of(-3, 8))], [...continuedFractionIterator(7)]]", () => [[...continuedFractionIterator(Rational.of(3, 8))], [...continuedFractionIterator(Rational.of(-3, 8))], [...continuedFractionIterator(7)]], "[[0, 2, 1, 2], [-1, 1, 1, 1, 2], [7]]"],
    ["take(continuedFractionIterator(pi), 8)", () => take(continuedFractionIterator(pi), 8), "[3, 7, 15, 1, 292, 1, 1, 1]"],
    ["take(continuedFractionIterator(sqrt(2)), 5)", () => take(continuedFractionIterator(sqrt(2)), 5), "[1, 2, 2, 2, 2]"],
    ["[continuedFractionReduce([1, 2, 3, 4, 5]), continuedFractionReduce([-2, 1, 9, 7, 1, 2]), continuedFractionReduce([1, 4, 2, [3, 1]]), continuedFractionReduce([[1]]), continuedFractionReduce(continuedFractionPeriodic(8, 5, 13)), continuedFractionReduce([])]", () => [continuedFractionReduce([1, 2, 3, 4, 5]), continuedFractionReduce([-2, 1, 9, 7, 1, 2]), continuedFractionReduce([1, 4, 2, [3, 1]]), continuedFractionReduce([[1]]), continuedFractionReduce(continuedFractionPeriodic(8, 5, 13)), continuedFractionReduce([])], "[225/157, -256/233, (sqrt(21) + 287)/238, (1 + sqrt(5))/2, (sqrt(13) + 8)/5, 0]"],
    ["[[-3, [1, 2]], [0, [2]], [2, [4]], [0, 1, [2, 3]], [-5, 1, [7, 1, 3]], [1, [1, 2]], [3, [2, 1, 4]], [0, [1]], [-1, [2]], [-2, 5, [1, 1, 1, 4]], [Rational.of(1, 2), [2]]].map((c) => continuedFractionReduce(c))", () => [[-3, [1, 2]], [0, [2]], [2, [4]], [0, 1, [2, 3]], [-5, 1, [7, 1, 3]], [1, [1, 2]], [3, [2, 1, 4]], [0, [1]], [-1, [2]], [-2, 5, [1, 1, 1, 4]], [Rational.of(1, 2), [2]]].map((c) => continuedFractionReduce(c)), "[-4 + sqrt(3), -1 + sqrt(2), sqrt(5), (1 + sqrt(15))/7, (-123 + sqrt(257))/26, sqrt(3), (5 + sqrt(229))/6, (-1 + sqrt(5))/2, -2 + sqrt(2), (-sqrt(7) - 1)/2, (-1 + 2*sqrt(2))/2]"],
    ["continuedFractionReduce([2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8]).evalf(10)", () => continuedFractionReduce([2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8]).evalf(10), "2.718281835"],
    ["[...continuedFractionConvergents([0, 2, 1, 2])]", () => [...continuedFractionConvergents([0, 2, 1, 2])], "[0, 1/2, 1/3, 3/8]"],
    ["[...continuedFractionConvergents([1, Rational.of(1, 2), -7, Rational.of(1, 4)])]", () => [...continuedFractionConvergents([1, Rational.of(1, 2), -7, Rational.of(1, 4)])], "[1, 3, 19/5, 7]"],
    ["take(continuedFractionConvergents(continuedFractionIterator(pi)), 7)", () => take(continuedFractionConvergents(continuedFractionIterator(pi)), 7), "[3, 22/7, 333/106, 355/113, 103993/33102, 104348/33215, 208341/66317]"],
    ["take(continuedFractionConvergents([1, [1, 2]]), 7)", () => take(continuedFractionConvergents([1, [1, 2]]), 7), "[1, 2, 5/3, 7/4, 19/11, 26/15, 71/41]"],
    ["[continuedFraction(P('(1 + 2*sqrt(3))/5')), continuedFraction(Rational.of(415, 93)), continuedFraction(sqrt(7)), continuedFraction(P('3*sqrt(2)/4')), continuedFraction(P('-sqrt(2)')), continuedFraction(P('(3 - sqrt(5))/2')), continuedFraction(5), continuedFraction(P('1 + sqrt(2)'))]", () => [continuedFraction(P('(1 + 2*sqrt(3))/5')), continuedFraction(Rational.of(415, 93)), continuedFraction(sqrt(7)), continuedFraction(P('3*sqrt(2)/4')), continuedFraction(P('-sqrt(2)')), continuedFraction(P('(3 - sqrt(5))/2')), continuedFraction(5), continuedFraction(P('1 + sqrt(2)'))], "[[0, 1, [8, 3, 34, 3]], [4, 2, 6, 7], [2, [1, 1, 1, 4]], [1, [16, 2]], [-2, 1, 1, [2]], [0, 2, [1]], [5], [[2]]]"],
    ["[digits(35), digits(-35), digits(27, 2), digits(35, 10, 4), digits(0), digits(255, 16)]", () => [digits(35), digits(-35), digits(27, 2), digits(35, 10, 4), digits(0), digits(255, 16)], "[[10, 3, 5], [-10, 3, 5], [2, 1, 1, 0, 1, 1], [10, 0, 0, 3, 5], [10, 0], [16, 15, 15]]"],
    ["[countDigits(1111339), countDigits(250), countDigits(250, 16), countDigits(-100)]", () => [countDigits(1111339), countDigits(250), countDigits(250, 16), countDigits(-100)], "[{1: 4, 3: 2, 9: 1}, {2: 1, 5: 1, 0: 1}, {15: 1, 10: 1}, {1: 1, 0: 2}]"],
    ["[0,1,2,3,4,5,6,7,8,9].filter((i) => countDigits(fn('factorial', [77])).get(BigInt(i)) === 7n)", () => [0,1,2,3,4,5,6,7,8,9].filter((i) => countDigits(fn('factorial', [77])).get(BigInt(i)) === 7n), "[1, 3, 7, 9]"],
    ["[[-11, 1, 22, 121].every((i) => isPalindromic(i)), isPalindromic(88, 8), isPalindromic(0o121), isPalindromic(121, 8) && isPalindromic(121)]", () => [[-11, 1, 22, 121].every((i) => isPalindromic(i)), isPalindromic(88, 8), isPalindromic(0o121), isPalindromic(121, 8) && isPalindromic(121)], "[True, False, False, True]"],
    ["[egyptianFraction(Rational.of(3, 7)), egyptianFraction([3, 7], 'Graham Jewett'), egyptianFraction([3, 7], 'Takenouchi'), egyptianFraction([3, 7], 'Golomb'), egyptianFraction([11, 5], 'Golomb')]", () => [egyptianFraction(Rational.of(3, 7)), egyptianFraction([3, 7], 'Graham Jewett'), egyptianFraction([3, 7], 'Takenouchi'), egyptianFraction([3, 7], 'Golomb'), egyptianFraction([11, 5], 'Golomb')], "[[3, 11, 231], [7, 8, 9, 56, 57, 72, 3192], [4, 7, 28], [3, 15, 35], [1, 2, 3, 4, 9, 234, 1118, 2580]]"],
    ["[egyptianFraction(2), egyptianFraction([4, 3]), egyptianFraction([7, 6]), egyptianFraction([5, 121]), egyptianFraction([5, 121], 'Graham Jewett'), egyptianFraction([5, 121], 'Takenouchi'), egyptianFraction([5, 121], 'Golomb'), egyptianFraction([4, 13], 'Takenouchi'), egyptianFraction(3), egyptianFraction([1, 7])]", () => [egyptianFraction(2), egyptianFraction([4, 3]), egyptianFraction([7, 6]), egyptianFraction([5, 121]), egyptianFraction([5, 121], 'Graham Jewett'), egyptianFraction([5, 121], 'Takenouchi'), egyptianFraction([5, 121], 'Golomb'), egyptianFraction([4, 13], 'Takenouchi'), egyptianFraction(3), egyptianFraction([1, 7])], "[[1, 2, 3, 6], [1, 3], [1, 6], [25, 757, 763309, 873960180913, 1527612795642093418846225], [121, 122, 123, 124, 125, 14762, 14763, 14764, 14765, 15006, 15007, 15008, 15252, 15253, 15500, 217931406, 217931407, 217931408, 217960932, 217960933, 217990460, 225195042, 225195043, 225225056, 232638756, 47494097939068242, 47494097939068243, 47494098374931056, 47506968096269556, 50712807166576806, 2255689339045806279678209072038806], [31, 121, 1891, 3691, 27243271], [25, 1225, 3577, 7081, 11737], [4, 28, 46, 4186], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 230, 57960], [7]]"],
    ["ecm(25645121643901801n)", () => ecm(25645121643901801n), "[5394769, 4753701529]"],
    ["ecm(9804659461513846513n)", () => ecm(9804659461513846513n), "[4641991, 2112166839943]"],
    ["ecm(2n ** 64n + 1n)", () => ecm(2n ** 64n + 1n), "[274177, 67280421310721]"],
    ["qs(25645121643901801n, 2000, 10000)", () => qs(25645121643901801n, 2000, 10000), "[5394769, 4753701529]"],
    ["qs(9804659461513846513n, 2000, 10000)", () => qs(9804659461513846513n, 2000, 10000), "[4641991, 2112166839943]"],
    ["qsFactor(1009n * 100003n, 2000, 10000)", () => qsFactor(1009n * 100003n, 2000, 10000), "{1009: 1, 100003: 1}"],
    ["[qsFactor(2n ** 5n * 1000003n * 1000033n, 2000, 10000), qsFactor(1000003n ** 3n, 2000, 10000), qsFactor(7919, 100, 100)]", () => [qsFactor(2n ** 5n * 1000003n * 1000033n, 2000, 10000), qsFactor(1000003n ** 3n, 2000, 10000), qsFactor(7919, 100, 100)], "[{2: 5, 1000003: 1, 1000033: 1}, {1000003: 3}, {7919: 1}]"],
    ["[npartitions(25), npartitions(100)]", () => [npartitions(25), npartitions(100)], "[1958, 190569292]"],
    ["[new Random(1234).getrandbits(32), new Random(1234).getrandbits(100), new Random(2n**70n + 5n).randint(0n, 10n**30n), new Random(0).getrandbits(64), new Random(-5).randint(1n, 6n)]", () => [new Random(1234).getrandbits(32), new Random(1234).getrandbits(100), new Random(2n**70n + 5n).randint(0n, 10n**30n), new Random(0).getrandbits(64), new Random(-5).randint(1n, 6n)], "[4150886329, 114146597024290628900519247801, 829904723954819379215411981483, 7106521602475165645, 5]"],
    ["((r) => [r.randint(1n, 100n), r.randint(1n, 100n), r.randrange(0n, 7n), r.getrandbits(33)])(new Random(42))", () => ((r) => [r.randint(1n, 100n), r.randint(1n, 100n), r.randrange(0n, 7n), r.getrandbits(33)])(new Random(42)), "[82, 15, 0, 3184935163]"],
    ["(seed(3), [randprime(1, 30), randprime(1000, 2000), randprime(10n**20n, 10n**21n), randprime(5, 5)])", () => (seed(3), [randprime(1, 30), randprime(1000, 2000), randprime(10n**20n, 10n**21n), randprime(5, 5)]), "[11, 1607, 526680989626225826647, None]"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/** SymPy srepr of the visual products (Mul, Pow and Integer nodes). */
function srepr(e: Expr): string {
  if (e instanceof Rational) return `Integer(${e.p})`;
  if (e instanceof Mul) return `Mul(${e.args.map(srepr).join(', ')})`;
  return `${e.constructor.name}(${e.args.map(srepr).join(', ')})`;
}

describe('factorint and factorrat: visual forms (unevaluated products)', () => {
  it('has SymPy structure', () => {
    expect(srepr(factorint(4200, { visual: true }))).toBe('Mul(Pow(Integer(2), Integer(3)), Pow(Integer(3), Integer(1)), Pow(Integer(5), Integer(2)), Pow(Integer(7), Integer(1)))');
    expect(srepr(factorint(7, { visual: true }))).toBe('Pow(Integer(7), Integer(1))');
    expect(srepr(factorint(-12, { visual: true }))).toBe('Mul(Integer(-1), Pow(Integer(2), Integer(2)), Pow(Integer(3), Integer(1)))');
    expect(srepr(factorint(1, { visual: true }))).toBe('Integer(1)');
    expect(srepr(factorint(0, { visual: true }))).toBe('Pow(Integer(0), Integer(1))');
    expect(srepr(factorint(1764, { visual: true }))).toBe('Mul(Pow(Integer(2), Integer(2)), Pow(Integer(3), Integer(2)), Pow(Integer(7), Integer(2)))');
    expect(srepr(factorint(new Map([[2n, 2n], [3n, 2n], [7n, 2n]])))).toBe('Mul(Pow(Integer(2), Integer(2)), Pow(Integer(3), Integer(2)), Pow(Integer(7), Integer(2)))');
    expect(srepr(factorint(new Map([[4n, 2n], [12n, 3n]])))).toBe('Mul(Pow(Integer(2), Integer(10)), Pow(Integer(3), Integer(3)))');
    expect(py(factorint(new Map([[4n, 2n], [12n, 3n]]), { visual: false }))).toBe('{2: 10, 3: 3}');
    expect(srepr(factorrat(Rational.of(-8, 9), { visual: true }))).toBe('Mul(Integer(-1), Pow(Integer(2), Integer(3)), Pow(Integer(3), Integer(-2)))');
    expect(factorint(4200, { visual: true }).toString()).toContain('5**2');
  });

  it('pollard_pm1 doctest: a**M is 1 modulo each prime power', () => {
    const n = 257n * 1009n;
    let M = 1n;
    const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
    for (let i = 2n; i < 256n; i++) M = (M / g(M, i)) * i;
    const pm = (b: bigint, e: bigint, m: bigint): bigint => {
      let r = 1n;
      let x = b % m;
      let k = e;
      while (k > 0n) {
        if (k & 1n) r = (r * x) % m;
        x = (x * x) % m;
        k >>= 1n;
      }
      return r;
    };
    const found = new Set<bigint>();
    for (let a = 2n; a < 256n; a++) {
      const d = g(pm(a, M, n) - 1n + n, n);
      if (d !== n) found.add(d);
    }
    expect([...found]).toEqual([1009n]);
    const aM = pm(255n, M, n);
    const v = factorint(n, { visual: true }) as Mul;
    expect(v.args.map((d) => [d.toString(), aM % ((d.args[0] as Rational).p ** (d.args[1] as Rational).p)])).toEqual([
      ['257**1', 1n],
      ['1009**1', 1n],
    ]);
  });
});

describe('Sieve', () => {
  it('doctests of the shared sieve', () => {
    sieve.reset();
    expect(sieve.contains(25)).toBe(false);
    expect(py(sieve.list)).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23]');
    sieve.reset();
    sieve.extend(30);
    expect(sieve.get(10)).toBe(29n);
    sieve.reset();
    sieve.extendToNo(9);
    expect(py(sieve.list)).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23]');
    expect(sieve.search(25)).toEqual([9n, 10n]);
    expect(sieve.search(23)).toEqual([9n, 9n]);
    expect(py([...sieve.primerange(prime(10) + 1n)])).toBe('[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]');
  });

  it('a new sieve, indexing, slicing and iteration', () => {
    const s = new Sieve();
    expect(s.list[s.list.length - 1]).toBe(13n);
    expect([...s.primerangeInternal(18, 31)]).toEqual([19, 23, 29]);
    expect(s.slice(1, 6)).toEqual([2n, 3n, 5n, 7n, 11n]);
    expect(s.slice(2, 12, 3)).toEqual([3n, 11n, 19n, 31n]);
    expect(take(s[Symbol.iterator](), 6)).toEqual([2n, 3n, 5n, 7n, 11n, 13n]);
    expect([s.contains(2), s.contains(4), s.contains(97), s.contains(1), s.contains(Rational.of(1, 2))]).toEqual([true, false, true, false, false]);
    expect(s.toString()).toContain('prime sieve');
    expect(() => s.get(0)).toThrow(RangeError);
    expect(() => s.search(1)).toThrow(RangeError);
    expect(() => new Sieve(0)).toThrow(RangeError);
    expect(py([...s.totientrange(1, 10)])).toBe('[1, 1, 2, 2, 4, 2, 6, 4, 6]');
    expect(py([...s.mobiusrange(1, 10)])).toBe('[1, -1, -1, 0, -1, 1, -1, 0, 0]');
    expect(py([...s.totientrange(3, 5)])).toBe('[2, 2]');
    s.reset({ totient: true });
    expect(py([...s.mobiusrange(2, 5)])).toBe('[-1, -1, 0]');
  });
});

describe('factor cache', () => {
  it('stores the largest prime factor (SymPy factor_cache)', () => {
    factorCache.set(15, 5);
    expect(factorCache.has(15)).toBe(true);
    expect(factorCache.get(15)).toBe(5n);
    expect(factorCache.getItem(15)).toBe(5n);
    factorCache.set(15, 3);
    expect(factorCache.get(15)).toBe(5n);
    expect(() => factorCache.set(15, 4)).toThrow(RangeError);
    expect(factorCache.get(13)).toBe(13n);
    factorCache.delete(15);
    expect(factorCache.get(1000000000000000000n * 3n)).toBe(NoMatch);
    expect(() => factorCache.getItem(4)).toThrow(RangeError);
  });

  it('LRU size limit and external source', () => {
    const c = new FactorCache(2);
    c.set(15, 5);
    c.set(21, 7);
    c.get(15);
    c.set(35, 7);
    expect([...c.keys()]).toEqual([15n, 35n]);
    expect(c.size).toBe(2);
    c.maxsize = 1;
    expect([...c.keys()]).toEqual([35n]);
    expect(() => (c.maxsize = 0)).toThrow(RangeError);
    c.cacheClear();
    expect(c.size).toBe(0);
    class Ext extends FactorCache {
      getExternal(n: bigint): bigint[] {
        return n === 1001n ? [7n, 11n, 13n] : [];
      }
    }
    const e = new Ext();
    expect(e.get(1001)).toBe(13n);
    expect(e.get(77)).toBe(11n);
  });
});

describe('primality', () => {
  it('isprime agrees with SymPy on pseudoprimes and large primes', () => {
    const L = [
      3825123056546413051n, 318665857834031151167461n, 3317044064679887385961981n, 2n ** 89n - 1n, 2n ** 127n - 1n, 561n, 2n ** 127n + 1n, 10n ** 30n + 57n, 341531n,
      4296595241n, 8321n, 1000003n, 2n ** 61n - 1n, 3215031751n, 2152302898747n, 1122004669633n, 3474749660383n, 341550071728321n, 3825123056546413051n * 3n,
      10n ** 100n + 267n, 10n ** 100n + 949n,
    ];
    expect(py(L.map((n) => isprime(n)))).toBe(
      '[False, False, False, True, True, False, False, True, False, False, False, True, True, False, False, False, False, False, False, True, True]',
    );
  });

  it('randprime gives primes in the range', () => {
    for (let i = 0; i < 5; i++) {
      const p = randprime(1, 30);
      expect(typeof p === 'bigint' && isprime(p) && p < 30n).toBe(true);
    }
    expect(randprime(30, 1)).toBe(NoMatch);
    expect(() => randprime(24, 28)).toThrow(RangeError);
    seed(1);
  });

  it('known Mersenne exponents', () => {
    expect(MERSENNE_PRIME_EXPONENTS.length).toBe(52);
    expect(isPerfect(2n ** 12n * (2n ** 13n - 1n))).toBe(true);
  });
});

describe('ntheory: more results', () => {
  it('modular helpers', () => {
    const [mm, e, s] = crt1([3, 5, 7]);
    expect(crt2([3, 5, 7], [2, 3, 2], mm, e, s)).toEqual([23n, 105n]);
    expect(crt2([3, 5, 7], [2, 3, 2], mm, e, s, true)).toEqual([23n, 105n]);
    expect(symmetricResidue(5n, 6n)).toBe(-1n);
    expect(solveCongruence([[2, 3], [3, 5], [2, 7]])).toEqual([23n, 105n]);
    expect([23n % 3n, 23n % 5n, 23n % 7n]).toEqual([2n, 3n, 2n]);
    expect(crt([12, 6, 17], [3, 4, 2])).toBe(NoMatch);
  });

  it('values that SymPy checks with ==', () => {
    expect(prevprime(25)).toBe(prime(9));
    expect(nOrder(3, 10) === 4n && isPrimitiveRoot(3, 10)).toBe(true);
    expect(divisorCount(6, 1, { proper: true })).toBe(3n);
    expect(abundance(6)).toBe(0n);
    expect(isAmicable(220, 284)).toBe(true);
    expect(py(npartitions(25))).toBe('1958');
    expect(multiplicity(fn('factorial', [25]), fn('factorial', [2n ** 100n], { evaluate: false }))).toBe(multiplicityInFactorial(fn('factorial', [25]), 2n ** 100n));
    expect(py(continuedFractionReduce([1, 4, 2, [3, 1]]))).toBe('(sqrt(21) + 287)/238');
    expect(py(continuedFractionReduce([[1]]))).toBe('(1 + sqrt(5))/2');
  });

  it('errors', () => {
    expect(() => prime(0)).toThrow(RangeError);
    expect(() => composite(0)).toThrow(RangeError);
    expect(() => nextprime(5, 0)).toThrow(RangeError);
    expect(() => prevprime(2)).toThrow(RangeError);
    expect(() => primorial(0)).toThrow(RangeError);
    expect(() => pollardRho(4)).toThrow(RangeError);
    expect(() => pollardPm1(3)).toThrow(RangeError);
    expect(() => digits(35, 10, 1)).toThrow(RangeError);
    expect(() => digits(35, 1)).toThrow(RangeError);
    expect(() => egyptianFraction(-1)).toThrow(RangeError);
    expect(() => egyptianFraction(P('x'))).toThrow(TypeError);
    expect(() => multiplicity(1, 5)).toThrow(RangeError);
    expect(() => multiplicity(2, 0)).toThrow(RangeError);
    expect(() => multiplicityInFactorial(0, 5)).toThrow(RangeError);
    expect(() => discreteLog(7, 3, 2)).toThrow(RangeError);
    expect(() => nOrder(2, 4)).toThrow(RangeError);
    expect(() => nOrder(2, 1)).toThrow(RangeError);
    expect(() => isPrimitiveRoot(2, 4)).toThrow(RangeError);
    expect(() => primitiveRoot(1)).toThrow(RangeError);
    expect(() => ecm(15, { B1: 101 })).toThrow(RangeError);
    expect(() => qsFactor(1, 10, 10)).toThrow(RangeError);
    expect(() => mersennePrimeExponent(52)).toThrow(RangeError);
    expect(() => mersennePrimeExponent(0)).toThrow(RangeError);
    expect(() => continuedFractionPeriodic(1, 0)).toThrow(RangeError);
    expect(() => continuedFractionPeriodic(1, 2, -1)).toThrow(RangeError);
    expect(() => continuedFraction(P('x'))).toThrow(RangeError);
    expect(() => continuedFraction(P('sqrt(2) + sqrt(3)'))).toThrow(RangeError);
    expect(() => dra(5, 1)).toThrow(RangeError);
    expect(() => drm(5, 1)).toThrow(RangeError);
    expect(() => quadraticCongruence(1, 1, 1, 1)).toThrow(RangeError);
    expect(() => nthrootMod(1, 0, 7)).toThrow(RangeError);
    expect(() => isNthpowResidue(1, -1, 7)).toThrow(RangeError);
    expect(() => isQuadResidue(1, 0)).toThrow(RangeError);
    expect(() => polynomialCongruence(P('x*y + 1'), 5)).toThrow(RangeError);
    expect(() => polynomialCongruence(P('x/2 + 1'), 5)).toThrow(RangeError);
    expect(() => factorint(Rational.of(1, 2))).toThrow(TypeError);
    expect(() => perfectPower(P('x'))).toThrow(TypeError);
  });

  it('remaining API surface', () => {
    expect(py(sqrtMod(3, 7))).toBe('None');
    expect(py(nthrootMod(3, 3, 7))).toBe('None');
    expect(nthrootMod(3, 3, 7, true)).toEqual([]);
    expect(py(primitiveRoot(12))).toBe('None');
    expect(py(take(sqrtModIter(4, 15), 10))).toBe('[7, 13, 2, 8]');
    expect(py(quadraticResidues(10))).toBe('[0, 1, 4, 5, 6, 9]');
    expect(py(countDigits(0))).toBe('{0: 1}');
    expect(isPalindromic(12321)).toBe(true);
    expect(py(binomialCoefficients(2))).toBe('{[0, 2]: 1, [2, 0]: 1, [1, 1]: 2}');
    expect(py(binomialCoefficientsList(0))).toBe('[1]');
    expect(py([...multinomialCoefficientsIterator(2, 2)])).toBe('[[[0, 2], 1], [[2, 0], 1], [[1, 1], 2]]');
    expect(py(multinomialCoefficients(3, 2))).toBe('{[2, 0, 0]: 1, [1, 1, 0]: 2, [0, 2, 0]: 1, [1, 0, 1]: 2, [0, 1, 1]: 2, [0, 0, 2]: 1}');
    expect(py(take(continuedFractionConvergents(continuedFractionIterator(sqrt(2))), 4))).toBe('[1, 3/2, 7/5, 17/12]');
    expect(py(factorint(Rational.of(12), { multiple: true }))).toBe('[2, 2, 3]');
    expect(py(new Random(5).randbelow(10n))).toBe('9');
    expect(py(pi)).toBe('pi');
  });
});
