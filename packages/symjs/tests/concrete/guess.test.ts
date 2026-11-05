// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/concrete/guess.ts.
// Identification of sequences and numbers. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { findSimpleRecurrence, findSimpleRecurrenceVector, guess, guessGeneratingFunction, guessGeneratingFunctionRational, rationalize } from '../../src/concrete/guess';

const s = (e: sj.Expr | sj.NoMatchResult): string => (sj.isNoMatch(e) ? 'None' : sj.str(e));
const list = (es: readonly sj.Expr[]): string => `[${es.map(sj.str).join(', ')}]`;
const dict = (m: Map<string, sj.Expr>): string => `{${[...m].map(([k, v]) => `'${k}': ${sj.str(v)}`).join(', ')}}`;
const range = (a: number, b: number): number[] => Array.from({ length: b - a }, (_, i) => a + i);
const fib = (a: number, b: number): sj.Expr[] => range(a, b).map((k) => sj.fibonacci(k));
const F = (x: number | string): sj.Expr => sj.float(x);

describe('find_simple_recurrence_vector', () => {
  it('finds the recurrence of a sequence', () => {
    expect(list(findSimpleRecurrenceVector(fib(0, 12)))).toBe('[1, -1, -1]');
    expect(list(findSimpleRecurrenceVector([1, 2, 4, 8, 16, 32]))).toBe('[1, -2]');
    expect(list(findSimpleRecurrenceVector([-1, -2, -4, -8, -16, -32]))).toBe('[1, -2]');
    expect(list(findSimpleRecurrenceVector([0, 0, 1, 1, 2, 3, 5, 8]))).toBe('[1, -1, -1]');
    expect(list(findSimpleRecurrenceVector(['1/2', '1/4', '1/8', '1/16', '1/32', '1/64'].map((x) => sj.parse(x))))).toBe('[2, -1]');
  });
  it('returns [0] when no relation is found', () => {
    expect(list(findSimpleRecurrenceVector([1, 2, 3]))).toBe('[0]');
    expect(list(findSimpleRecurrenceVector([1, 0, 0, 0]))).toBe('[1]');
  });
  it('accepts floating-point terms', () => {
    expect(list(findSimpleRecurrenceVector([1, 2, 4, 8, 16, 32].map(F)))).toBe('[0, -1]');
    expect(list(findSimpleRecurrenceVector([1, 1, 2, 3, 5, 8].map(F)))).toBe('[1, -1, -1]');
  });
});

describe('find_simple_recurrence', () => {
  it('gives the relation as an expression', () => {
    expect(s(findSimpleRecurrence(fib(0, 12)))).toBe('-a(n) - a(n + 1) + a(n + 2)');
    const a = [1, 1, 1];
    for (let k = 0; k < 15; k++) a.push(5 * a.at(-1)! - 3 * a.at(-2)! + 8 * a.at(-3)!);
    expect(s(findSimpleRecurrence(a, sj.SymFunction('f'), new sj.Sym('i')))).toBe('-8*f(i) + 3*f(i + 1) - 5*f(i + 2) + f(i + 3)');
    expect(s(findSimpleRecurrence([1, 2, 4, 7, 11]))).toBe('0');
  });
});

describe('rationalize', () => {
  it('identifies rationals from floating-point values', () => {
    expect(s(rationalize(F(0.5000000000000001)))).toBe('1/2');
    expect(s(rationalize(F('0.333333333333333')))).toBe('1/3');
    expect(s(rationalize(F(-0.75)))).toBe('-3/4');
    expect(s(rationalize(F(1 / 7)))).toBe('1/7');
  });
  it('approximates with a bound on the partial quotients', () => {
    expect(s(rationalize(F(Math.PI), 250))).toBe('355/113');
    expect(s(rationalize(sj.S.Pi, 250))).toBe('355/113');
    expect(s(rationalize(sj.parse('7/3')))).toBe('7/3');
  });
  it('stops on an integral value', () => {
    // SymPy 1.14 raises here (Float(2.0) == 2 is False, so it divides by zero): the value is 2
    expect(s(rationalize(F(2)))).toBe('2');
  });
});

describe('guess_generating_function_rational', () => {
  it('guesses rational generating functions', () => {
    expect(s(guessGeneratingFunctionRational(fib(5, 15)))).toBe('(3*x + 5)/(-x**2 - x + 1)');
    expect(s(guessGeneratingFunctionRational([1, 2, 4, 7, 11, 16], new sj.Sym('t')))).toBe('None');
  });
});

describe('guess_generating_function', () => {
  it('guesses several types', () => {
    const ints = range(1, 13);
    expect(dict(guessGeneratingFunction(ints, undefined, { types: ['ogf', 'lgf', 'hlgf'] }))).toBe("{'ogf': 1/(x**2 - 2*x + 1), 'lgf': 1/(x + 1), 'hlgf': 1/(1 - x)}");
    expect(dict(guessGeneratingFunction(['3/2', '11/2', '0', '-121/2', '-363/2', '121'].map((x) => sj.parse(x))))).toBe("{'ogf': (x + 3/2)/(11*x**2 - 3*x + 1)}");
    expect(dict(guessGeneratingFunction(fib(5, 15), undefined, { types: ['ogf'] }))).toBe("{'ogf': (3*x + 5)/(-x**2 - x + 1)}");
    expect(dict(guessGeneratingFunction(range(0, 12).map((k) => sj.factorial(k)), undefined, { types: ['ogf', 'egf', 'lgf'] }))).toBe("{'egf': 1/(1 - x)}");
    expect(dict(guessGeneratingFunction(ints, undefined, { types: ['egf'] }))).toBe("{'lgdegf': (x + 2)/(x + 1), 'egf': (x + 1)*exp(x)}");
    expect(dict(guessGeneratingFunction(range(1, 9), undefined, { maxsqrtn: 0 }))).toBe(
      "{'ogf': 1/(x**2 - 2*x + 1), 'lgf': 1/(x + 1), 'hlgf': 1/(1 - x), 'lgdogf': 2/(1 - x), 'lgdegf': (x + 2)/(x + 1), 'egf': (x + 1)*exp(x)}",
    );
  });
  it('detects n-th roots of rational functions', () => {
    expect(s(guessGeneratingFunction([1, 2, 5, 14, 41, 124, 383, 1200, 3799, 12122, 38919]).get('ogf')!)).toBe('sqrt(1/(x**4 + 2*x**2 - 4*x + 1))');
  });
  it('integrates logarithmic derivatives', () => {
    expect(dict(guessGeneratingFunction([1, -1, 1, -1, 1, -1, 1, -1], undefined, { types: ['lgdogf'] }))).toBe("{'lgdogf': -1/(x + 1), 'ogf': 1/(x + 1)}");
    expect(dict(guessGeneratingFunction([1, 3, 9, 27, 81, 243], undefined, { types: 'ogf' }))).toBe("{'ogf': 1/(1 - 3*x)}");
    expect(dict(guessGeneratingFunction([1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]))).toBe('{}');
    expect(dict(guessGeneratingFunction([2, 0, 0, 0, 0, 0, 0, 0]))).toBe('{}');
  });
  it('needs a symbol to integrate', () => {
    expect(() => guessGeneratingFunction([1, -1, 1, -1, 1, -1, 1, -1], sj.parse('2*y'), { types: ['lgdogf'] })).toThrow(TypeError);
  });
});

describe('guess', () => {
  it('guesses formulas', () => {
    expect(list(guess([1, 2, 6, 24, 120], { evaluate: false }))).toBe('[Product(i1 + 1, (i1, 1, i0 - 1))]');
    expect(list(guess([1, 2, 6, 24, 120]))).toBe('[RisingFactorial(2, i0 - 1)]');
    expect(list(guess([1, 2, 3, 4, 5]))).toBe('[i0]');
    expect(list(guess([1, 0, 3]))).toBe('[]');
    expect(list(guess([1, 4, 9, 16, 25, 36], { all: true }))).toBe('[i0**2]');
    expect(list(guess([1, 2, 3, 4, 5], { variables: sj.symbols('n m') as sj.Sym[] }))).toBe('[n]');
    expect(list(guess([1, 2, 6, 24, 120, 720], { all: true, niter: 3 }))).toBe('[RisingFactorial(2, i0 - 1), Product(2*RisingFactorial(3, i1 - 1)/RisingFactorial(2, i1 - 1), (i1, 1, i0 - 1))]');
  });
  it('iterates on products of rising factorials', () => {
    const r = guess([1, 2, 7, 42, 429, 7436, 218348, 10850216], { niter: 4 });
    const i0 = new sj.Sym('i0');
    expect(range(1, 10).map((n) => sj.str(sj.doit(sj.subs(r[0]!, [[i0, n]]))))).toEqual(['1', '2', '7', '42', '429', '7436', '218348', '10850216', '911835460']);
  });
});
