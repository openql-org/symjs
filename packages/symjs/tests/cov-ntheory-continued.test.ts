// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of ntheory/continued.ts, with the expected values computed by
 * SymPy 1.14 (Python's printed form).
 */

import { describe, expect, it } from 'vitest';
import { Expr } from '../src/core/nodes';
import { NoMatch, Unsolved } from '../src/core/truth';

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
import { Float, Mul, Pow, Rational, Sym } from '../src/core/nodes';
import { sqrt } from '../src/core/ops';
import { continuedFraction, continuedFractionConvergents, continuedFractionIterator, continuedFractionPeriodic, continuedFractionReduce } from '../src/ntheory/index';

const R = (p: bigint, q: bigint = 1n): Rational => Rational.of(p, q);


describe("ntheory continued fractions: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["continuedFraction(new Mul([sqrt(2).add(1), sqrt(2).sub(1)]))", () => continuedFraction(new Mul([sqrt(2).add(1), sqrt(2).sub(1)])), "[1]"],
    ["continuedFraction(sqrt(2).add(3).div(7))", () => continuedFraction(sqrt(2).add(3).div(7)), "[0, 1, 1, 1, [2]]"],
    ["continuedFraction(sqrt(2).div(3).neg())", () => continuedFraction(sqrt(2).div(3).neg()), "[-1, 1, 1, [8, 4]]"],
    ["continuedFraction(sqrt(5).mul(2).add(3))", () => continuedFraction(sqrt(5).mul(2).add(3)), "[7, [2, 8]]"],
    ["[...continuedFractionIterator(new Float(2.5))]", () => [...continuedFractionIterator(new Float(2.5))], "[2, 2]"],
    ["[...continuedFractionIterator(new Float(-3.75))]", () => [...continuedFractionIterator(new Float(-3.75))], "[-4, 4]"],
    ["continuedFractionReduce([[0n]])", () => continuedFractionReduce([[0n]]), "1"],
    ["continuedFractionReduce([1n, [0n]])", () => continuedFractionReduce([1n, [0n]]), "2"],
    ["continuedFractionReduce([[-1n]])", () => continuedFractionReduce([[-1n]]), "(-1 + sqrt(5))/2"],
    ["continuedFractionReduce([[1n]])", () => continuedFractionReduce([[1n]]), "(1 + sqrt(5))/2"],
    ["continuedFractionReduce([[2n]])", () => continuedFractionReduce([[2n]]), "1 + sqrt(2)"],
    ["continuedFractionReduce([1n, [2n, 2n]])", () => continuedFractionReduce([1n, [2n, 2n]]), "sqrt(2)"],
    ["continuedFractionReduce([[-2n]])", () => continuedFractionReduce([[-2n]]), "-1 + sqrt(2)"],
    ["continuedFractionReduce([[-3n, -1n]])", () => continuedFractionReduce([[-3n, -1n]]), "(-3 + sqrt(21))/2"],
    ["continuedFractionPeriodic(3n, 2n, 4n, 0n)", () => continuedFractionPeriodic(3n, 2n, 4n, 0n), "[1, 2]"],
    ["continuedFractionPeriodic(-3n, 2n, 7n)", () => continuedFractionPeriodic(-3n, 2n, 7n), "[-1, [1, 4, 1, 1]]"],
    ["continuedFractionPeriodic(3n, -2n, 7n, -1n)", () => continuedFractionPeriodic(3n, -2n, 7n, -1n), "[-1, [1, 4, 1, 1]]"],
    ["continuedFractionPeriodic(1n, 2n, 7n, 0n)", () => continuedFractionPeriodic(1n, 2n, 7n, 0n), "[0, 2]"],
    ["continuedFractionPeriodic(0n, 5n, 3n, -2n)", () => continuedFractionPeriodic(0n, 5n, 3n, -2n), "[-1, 3, [3, 1, 10, 1, 3, 2, 2, 2]]"],
    ["continuedFractionPeriodic(-7n, 3n, 2n, 5n)", () => continuedFractionPeriodic(-7n, 3n, 2n, 5n), "[0, [42, 4, 1, 2, 4, 2, 1, 4]]"],
    ["continuedFractionPeriodic(-7n, 3n, 2n, -5n)", () => continuedFractionPeriodic(-7n, 3n, 2n, -5n), "[-5, 3, [4, 2, 1, 4, 42, 4, 1, 2]]"],
    ["continuedFractionPeriodic(7n, 3n, 50n, -1n)", () => continuedFractionPeriodic(7n, 3n, 50n, -1n), "[-1, 1, 41, [4, 1, 2, 4, 2, 1, 4, 42]]"],
    ["continuedFractionPeriodic(-5n, 1n, 2n, 3n)", () => continuedFractionPeriodic(-5n, 1n, 2n, 3n), "[-1, [4, 8]]"],
    ["continuedFractionPeriodic(5n, 1n, 2n, -3n)", () => continuedFractionPeriodic(5n, 1n, 2n, -3n), "[0, 1, 3, [8, 4]]"],
    ["continuedFractionPeriodic(5n, 1n, 50n, -1n)", () => continuedFractionPeriodic(5n, 1n, 50n, -1n), "[-3, 1, 13, [14]]"],
    ["continuedFractionPeriodic(-1n, 1n, 2n, 1n)", () => continuedFractionPeriodic(-1n, 1n, 2n, 1n), "[0, [2]]"],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(py(f())).toBe(want));
  const errors: [string, () => unknown][] = [
    ["continuedFraction(new Pow(R(2n), R(1n, 3n)).mul(3))", () => continuedFraction(new Pow(R(2n), R(1n, 3n)).mul(3))],
    ["continuedFraction(sqrt(2).add(1).pow(-1))", () => continuedFraction(sqrt(2).add(1).pow(-1))],
    ["continuedFraction(sqrt(2).add(sqrt(3)).add(1))", () => continuedFraction(sqrt(2).add(sqrt(3)).add(1))],
    ["continuedFraction(new Pow(R(2n), R(1n, 3n)).mul(2).add(1))", () => continuedFraction(new Pow(R(2n), R(1n, 3n)).mul(2).add(1))],
    ["[...continuedFractionIterator(new Sym(\"x\"))]", () => [...continuedFractionIterator(new Sym("x"))]],
    ["[...continuedFractionConvergents([1n, [2n], 3n])]", () => [...continuedFractionConvergents([1n, [2n], 3n])]],
    ["continuedFractionReduce([[0n, 0n]])", () => continuedFractionReduce([[0n, 0n]])],
    ["continuedFractionReduce([[-1n, 2n]])", () => continuedFractionReduce([[-1n, 2n]])],
    ["continuedFractionReduce([2n, [-3n, 1n]])", () => continuedFractionReduce([2n, [-3n, 1n]])],
    ["continuedFractionReduce([1n, [new Sym(\"x\")]])", () => continuedFractionReduce([1n, [new Sym("x")]])],
    ["continuedFractionPeriodic(1n, 0n)", () => continuedFractionPeriodic(1n, 0n)],
    ["continuedFractionPeriodic(1n, 2n, -3n)", () => continuedFractionPeriodic(1n, 2n, -3n)],
  ];
  for (const [label, f] of errors) it(`${label} throws`, () => expect(f).toThrow());

});
