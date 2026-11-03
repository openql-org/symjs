// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/residue.ts.

import { describe, expect, it } from 'vitest';
import { Expr, Sym } from '../../src/core/nodes';
import { NoMatch, Unsolved } from '../../src/core/truth';
import { parseExpr } from '../../src/index';
import { discreteLog, gfCsolve, isNthpowResidue, isPrimitiveRoot, isQuadResidue, linearCongruence, nOrder, nthrootMod, polynomialCongruence, primitiveRoot, quadraticCongruence, quadraticResidues, sqrtMod, sqrtModIter } from '../../src/ntheory/index';
import { seed } from '../../src/ntheory/random';
import { dlogIndexCalculus, dlogPollardRho, sqrtModPrimePower } from '../../src/ntheory/residue';

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

const x = new Sym('x');
const y = new Sym('y');

describe('ntheory: results equal SymPy 1.14', () => {
  const cases: [string, () => unknown, string][] = [
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
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(py(f())).toBe(expected);
  });
});

/**
 * Coverage of ntheory/residue.ts: orders, primitive roots, square and nth
 * roots, residues, discrete logarithms and congruences, with the expected
 * values computed by SymPy 1.14 (Python's printed form).
 */

describe("ntheory residue: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["nOrder(5n, 27n)", () => nOrder(5n, 27n), "18"],
    ["nOrder(7n, 1000n)", () => nOrder(7n, 1000n), "20"],
    ["nOrder(11n, 5n)", () => nOrder(11n, 5n), "1"],
    ["primitiveRoot(40487n ** 2n, { smallest: false })", () => primitiveRoot(40487n ** 2n, { smallest: false }), "40492"],
    ["primitiveRoot(2n * 40487n ** 2n, { smallest: false })", () => primitiveRoot(2n * 40487n ** 2n, { smallest: false }), "1639237661"],
    ["primitiveRoot(9n, { smallest: false })", () => primitiveRoot(9n, { smallest: false }), "2"],
    ["primitiveRoot(18n, { smallest: false })", () => primitiveRoot(18n, { smallest: false }), "11"],
    ["primitiveRoot(2n * 40487n, { smallest: false })", () => primitiveRoot(2n * 40487n, { smallest: false }), "5"],
    ["primitiveRoot(82n, { smallest: false })", () => primitiveRoot(82n, { smallest: false }), "47"],
    ["primitiveRoot(4n)", () => primitiveRoot(4n), "3"],
    ["primitiveRoot(12n)", () => primitiveRoot(12n), "None"],
    ["primitiveRoot(15n)", () => primitiveRoot(15n), "None"],
    ["primitiveRoot(225n)", () => primitiveRoot(225n), "None"],
    ["primitiveRoot(18n)", () => primitiveRoot(18n), "5"],
    ["primitiveRoot(40487n ** 2n)", () => primitiveRoot(40487n ** 2n), "10"],
    ["primitiveRoot(2n * 40487n ** 2n)", () => primitiveRoot(2n * 40487n ** 2n), "13"],
    ["primitiveRoot(3n ** 5n)", () => primitiveRoot(3n ** 5n), "2"],
    ["primitiveRoot(23n, { smallest: false })", () => primitiveRoot(23n, { smallest: false }), "5"],
    ["primitiveRoot(3n, { smallest: false })", () => primitiveRoot(3n, { smallest: false }), "2"],
    ["primitiveRoot(97n, { smallest: false })", () => primitiveRoot(97n, { smallest: false }), "5"],
    ["primitiveRoot(25n, { smallest: false })", () => primitiveRoot(25n, { smallest: false }), "2"],
    ["primitiveRoot(50n, { smallest: false })", () => primitiveRoot(50n, { smallest: false }), "27"],
    ["primitiveRoot(54n, { smallest: false })", () => primitiveRoot(54n, { smallest: false }), "29"],
    ["primitiveRoot(162n, { smallest: false })", () => primitiveRoot(162n, { smallest: false }), "83"],
    ["primitiveRoot(41n, { smallest: false })", () => primitiveRoot(41n, { smallest: false }), "6"],
    ["primitiveRoot(17n, { smallest: false })", () => primitiveRoot(17n, { smallest: false }), "3"],
    ["primitiveRoot(7n, { smallest: false })", () => primitiveRoot(7n, { smallest: false }), "3"],
    ["primitiveRoot(28n, { smallest: false })", () => primitiveRoot(28n, { smallest: false }), "None"],
    ["primitiveRoot(45n, { smallest: false })", () => primitiveRoot(45n, { smallest: false }), "None"],
    ["isPrimitiveRoot(3n, 4n)", () => isPrimitiveRoot(3n, 4n), "True"],
    ["isPrimitiveRoot(1n, 4n)", () => isPrimitiveRoot(1n, 4n), "False"],
    ["isPrimitiveRoot(3n, 8n)", () => isPrimitiveRoot(3n, 8n), "False"],
    ["isPrimitiveRoot(2n, 15n)", () => isPrimitiveRoot(2n, 15n), "False"],
    ["isPrimitiveRoot(2n, 25n)", () => isPrimitiveRoot(2n, 25n), "True"],
    ["isPrimitiveRoot(7n, 25n)", () => isPrimitiveRoot(7n, 25n), "False"],
    ["isPrimitiveRoot(2n, 225n)", () => isPrimitiveRoot(2n, 225n), "False"],
    ["isPrimitiveRoot(3n, 50n)", () => isPrimitiveRoot(3n, 50n), "True"],
    ["isPrimitiveRoot(2n, 1001n)", () => isPrimitiveRoot(2n, 1001n), "False"],
    ["sqrtMod(1n, 8n, true)", () => sqrtMod(1n, 8n, true), "[1, 3, 5, 7]"],
    ["sqrtMod(1n, 4n, true)", () => sqrtMod(1n, 4n, true), "[1, 3]"],
    ["sqrtMod(1n, 2n, true)", () => sqrtMod(1n, 2n, true), "[1]"],
    ["sqrtMod(17n, 32n, true)", () => sqrtMod(17n, 32n, true), "[7, 9, 23, 25]"],
    ["sqrtMod(3n, 32n, true)", () => sqrtMod(3n, 32n, true), "[]"],
    ["sqrtMod(9n, 64n, true)", () => sqrtMod(9n, 64n, true), "[3, 29, 35, 61]"],
    ["sqrtMod(33n, 2n ** 7n, true)", () => sqrtMod(33n, 2n ** 7n, true), "[17, 47, 81, 111]"],
    ["sqrtMod(3n, 13n, true)", () => sqrtMod(3n, 13n, true), "[4, 9]"],
    ["sqrtMod(2n, 13n, true)", () => sqrtMod(2n, 13n, true), "[]"],
    ["sqrtMod(5n, 29n, true)", () => sqrtMod(5n, 29n, true), "[11, 18]"],
    ["sqrtMod(2n, 41n, true)", () => sqrtMod(2n, 41n, true), "[17, 24]"],
    ["sqrtMod(2n, 73n, true)", () => sqrtMod(2n, 73n, true), "[32, 41]"],
    ["sqrtMod(3n, 241n, true)", () => sqrtMod(3n, 241n, true), "[56, 185]"],
    ["sqrtMod(10n, 241n, true)", () => sqrtMod(10n, 241n, true), "[97, 144]"],
    ["sqrtMod(2n, 7n ** 3n, true)", () => sqrtMod(2n, 7n ** 3n, true), "[108, 235]"],
    ["sqrtMod(2n, 7n ** 4n, true)", () => sqrtMod(2n, 7n ** 4n, true), "[235, 2166]"],
    ["sqrtMod(3n, 13n ** 3n, true)", () => sqrtMod(3n, 13n ** 3n, true), "[1075, 1122]"],
    ["sqrtMod(5n, 13n ** 5n, true)", () => sqrtMod(5n, 13n ** 5n, true), "[]"],
    ["sqrtMod(0n, 27n, true)", () => sqrtMod(0n, 27n, true), "[0, 9, 18]"],
    ["sqrtMod(0n, 81n, true)", () => sqrtMod(0n, 81n, true), "[0, 9, 18, 27, 36, 45, 54, 63, 72]"],
    ["sqrtMod(9n, 27n, true)", () => sqrtMod(9n, 27n, true), "[3, 6, 12, 15, 21, 24]"],
    ["sqrtMod(3n, 27n, true)", () => sqrtMod(3n, 27n, true), "[]"],
    ["sqrtMod(18n, 27n, true)", () => sqrtMod(18n, 27n, true), "[]"],
    ["sqrtMod(45n, 81n, true)", () => sqrtMod(45n, 81n, true), "[]"],
    ["sqrtMod(4n, 2n ** 5n, true)", () => sqrtMod(4n, 2n ** 5n, true), "[2, 6, 10, 14, 18, 22, 26, 30]"],
    ["sqrtMod(8n, 2n ** 5n, true)", () => sqrtMod(8n, 2n ** 5n, true), "[]"],
    ["sqrtMod(0n, 2n ** 5n, true)", () => sqrtMod(0n, 2n ** 5n, true), "[0, 8, 16, 24]"],
    ["sqrtMod(9n, 3n * 5n * 7n, true)", () => sqrtMod(9n, 3n * 5n * 7n, true), "[3, 18, 87, 102]"],
    ["sqrtMod(9n, 27n * 5n, true)", () => sqrtMod(9n, 27n * 5n, true), "[3, 12, 33, 42, 48, 57, 78, 87, 93, 102, 123, 132]"],
    ["sqrtMod(0n, 9n * 25n * 4n, true)", () => sqrtMod(0n, 9n * 25n * 4n, true), "[0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330, 360, 390, 420, 450, 480, 510, 540, 570, 600, 630, 660, 690, 720, 750, 780, 810, 840, 870]"],
    ["sqrtMod(4n, 9n * 5n, true)", () => sqrtMod(4n, 9n * 5n, true), "[2, 7, 38, 43]"],
    ["sqrtMod(3n, 15n, true)", () => sqrtMod(3n, 15n, true), "[]"],
    ["sqrtMod(1n, 2n)", () => sqrtMod(1n, 2n), "1"],
    ["sqrtMod(2n, 3n)", () => sqrtMod(2n, 3n), "None"],
    ["sqrtMod(4n, 8n)", () => sqrtMod(4n, 8n), "2"],
    ["sqrtMod(9n, 18n)", () => sqrtMod(9n, 18n), "3"],
    ["sqrtMod(0n, 1n)", () => sqrtMod(0n, 1n), "0"],
    ["sqrtMod(4n, -7n)", () => sqrtMod(4n, -7n), "2"],
    ["sqrtMod(1n, 1n, true)", () => sqrtMod(1n, 1n, true), "[0]"],
    ["[...sqrtModIter(9n, 27n * 5n)]", () => [...sqrtModIter(9n, 27n * 5n)], "[57, 12, 3, 102, 93, 87, 48, 42, 33, 132, 123, 78]"],
    ["[...sqrtModIter(4n, 5n * 7n)]", () => [...sqrtModIter(4n, 5n * 7n)], "[2, 12, 23, 33]"],
    ["[...sqrtModIter(0n, 9n * 4n * 25n)]", () => [...sqrtModIter(0n, 9n * 4n * 25n)], "[0, 450, 300, 750, 180, 630, 600, 150, 480, 30, 360, 810, 780, 330, 660, 210, 540, 90, 60, 510, 840, 390, 720, 270, 240, 690, 120, 570, 420, 870]"],
    ["[...sqrtModIter(6n, 9n * 5n)]", () => [...sqrtModIter(6n, 9n * 5n)], "[]"],
    ["sqrtModPrimePower(1n, 2n, 1n)", () => sqrtModPrimePower(1n, 2n, 1n), "[1]"],
    ["sqrtModPrimePower(3n, 2n, 4n)", () => sqrtModPrimePower(3n, 2n, 4n), "None"],
    ["sqrtModPrimePower(2n, 3n, 2n)", () => sqrtModPrimePower(2n, 3n, 2n), "None"],
    ["isQuadResidue(1n, 2n)", () => isQuadResidue(1n, 2n), "True"],
    ["isQuadResidue(3n, 8n)", () => isQuadResidue(3n, 8n), "False"],
    ["isQuadResidue(2n, 8n)", () => isQuadResidue(2n, 8n), "False"],
    ["isQuadResidue(5n, 8n)", () => isQuadResidue(5n, 8n), "False"],
    ["isQuadResidue(9n, 16n)", () => isQuadResidue(9n, 16n), "True"],
    ["isQuadResidue(4n, 32n)", () => isQuadResidue(4n, 32n), "True"],
    ["isQuadResidue(8n, 32n)", () => isQuadResidue(8n, 32n), "False"],
    ["isQuadResidue(12n, 32n)", () => isQuadResidue(12n, 32n), "False"],
    ["isQuadResidue(17n, 24n)", () => isQuadResidue(17n, 24n), "False"],
    ["isQuadResidue(5n, 12n)", () => isQuadResidue(5n, 12n), "False"],
    ["isQuadResidue(1n, 6n)", () => isQuadResidue(1n, 6n), "True"],
    ["isQuadResidue(3n, 12n)", () => isQuadResidue(3n, 12n), "False"],
    ["isQuadResidue(2n, 9n)", () => isQuadResidue(2n, 9n), "False"],
    ["isQuadResidue(4n, 9n)", () => isQuadResidue(4n, 9n), "True"],
    ["isQuadResidue(4n, 45n)", () => isQuadResidue(4n, 45n), "True"],
    ["isQuadResidue(9n, 45n)", () => isQuadResidue(9n, 45n), "True"],
    ["isQuadResidue(18n, 45n)", () => isQuadResidue(18n, 45n), "False"],
    ["isQuadResidue(3n, 45n)", () => isQuadResidue(3n, 45n), "False"],
    ["isQuadResidue(27n, 81n)", () => isQuadResidue(27n, 81n), "False"],
    ["isQuadResidue(81n, 81n * 5n)", () => isQuadResidue(81n, 81n * 5n), "True"],
    ["isQuadResidue(6n, 35n)", () => isQuadResidue(6n, 35n), "False"],
    ["isQuadResidue(11n, 35n)", () => isQuadResidue(11n, 35n), "True"],
    ["isQuadResidue(9n, 7n * 7n * 11n)", () => isQuadResidue(9n, 7n * 7n * 11n), "True"],
    ["isQuadResidue(22n, 49n * 11n)", () => isQuadResidue(22n, 49n * 11n), "True"],
    ["isNthpowResidue(1n, 0n, 1n)", () => isNthpowResidue(1n, 0n, 1n), "False"],
    ["isNthpowResidue(1n, 0n, 5n)", () => isNthpowResidue(1n, 0n, 5n), "True"],
    ["isNthpowResidue(2n, 0n, 5n)", () => isNthpowResidue(2n, 0n, 5n), "False"],
    ["isNthpowResidue(0n, 3n, 5n)", () => isNthpowResidue(0n, 3n, 5n), "True"],
    ["isNthpowResidue(3n, 1n, 5n)", () => isNthpowResidue(3n, 1n, 5n), "True"],
    ["isNthpowResidue(3n, 2n, 5n)", () => isNthpowResidue(3n, 2n, 5n), "False"],
    ["isNthpowResidue(8n, 3n, 27n)", () => isNthpowResidue(8n, 3n, 27n), "True"],
    ["isNthpowResidue(9n, 3n, 27n)", () => isNthpowResidue(9n, 3n, 27n), "False"],
    ["isNthpowResidue(27n, 3n, 81n)", () => isNthpowResidue(27n, 3n, 81n), "True"],
    ["isNthpowResidue(9n, 4n, 81n)", () => isNthpowResidue(9n, 4n, 81n), "False"],
    ["isNthpowResidue(3n, 3n, 16n)", () => isNthpowResidue(3n, 3n, 16n), "True"],
    ["isNthpowResidue(5n, 4n, 64n)", () => isNthpowResidue(5n, 4n, 64n), "False"],
    ["isNthpowResidue(17n, 4n, 64n)", () => isNthpowResidue(17n, 4n, 64n), "True"],
    ["isNthpowResidue(17n, 4n, 8n)", () => isNthpowResidue(17n, 4n, 8n), "True"],
    ["isNthpowResidue(81n, 4n, 3n ** 8n)", () => isNthpowResidue(81n, 4n, 3n ** 8n), "True"],
    ["isNthpowResidue(32n, 5n, 3n * 2n ** 10n)", () => isNthpowResidue(32n, 5n, 3n * 2n ** 10n), "True"],
    ["isNthpowResidue(2n, 3n, 7n)", () => isNthpowResidue(2n, 3n, 7n), "False"],
    ["isNthpowResidue(6n, 3n, 7n)", () => isNthpowResidue(6n, 3n, 7n), "True"],
    ["isNthpowResidue(16n, 4n, 2n ** 7n)", () => isNthpowResidue(16n, 4n, 2n ** 7n), "True"],
    ["isNthpowResidue(48n, 4n, 2n ** 7n)", () => isNthpowResidue(48n, 4n, 2n ** 7n), "False"],
    ["nthrootMod(5n, 1n, 7n)", () => nthrootMod(5n, 1n, 7n), "5"],
    ["nthrootMod(5n, 1n, 7n, true)", () => nthrootMod(5n, 1n, 7n, true), "[5]"],
    ["nthrootMod(4n, 2n, 7n)", () => nthrootMod(4n, 2n, 7n), "2"],
    ["nthrootMod(4n, 2n, 7n, true)", () => nthrootMod(4n, 2n, 7n, true), "[2, 5]"],
    ["nthrootMod(3n, 3n, 7n)", () => nthrootMod(3n, 3n, 7n), "None"],
    ["nthrootMod(3n, 3n, 7n, true)", () => nthrootMod(3n, 3n, 7n, true), "[]"],
    ["nthrootMod(6n, 3n, 7n, true)", () => nthrootMod(6n, 3n, 7n, true), "[3, 5, 6]"],
    ["nthrootMod(8n, 3n, 27n, true)", () => nthrootMod(8n, 3n, 27n, true), "[2, 11, 20]"],
    ["nthrootMod(0n, 3n, 27n, true)", () => nthrootMod(0n, 3n, 27n, true), "[0, 3, 6, 9, 12, 15, 18, 21, 24]"],
    ["nthrootMod(9n, 3n, 81n, true)", () => nthrootMod(9n, 3n, 81n, true), "[]"],
    ["nthrootMod(27n, 3n, 81n, true)", () => nthrootMod(27n, 3n, 81n, true), "[3, 12, 21, 30, 39, 48, 57, 66, 75]"],
    ["nthrootMod(2n, 3n, 11n, true)", () => nthrootMod(2n, 3n, 11n, true), "[7]"],
    ["nthrootMod(2n, 5n, 11n, true)", () => nthrootMod(2n, 5n, 11n, true), "[]"],
    ["nthrootMod(3n, 6n, 13n, true)", () => nthrootMod(3n, 6n, 13n, true), "[]"],
    ["nthrootMod(9n, 6n, 13n, true)", () => nthrootMod(9n, 6n, 13n, true), "[]"],
    ["nthrootMod(4n, 4n, 13n, true)", () => nthrootMod(4n, 4n, 13n, true), "[]"],
    ["nthrootMod(7n, 4n, 17n, true)", () => nthrootMod(7n, 4n, 17n, true), "[]"],
    ["nthrootMod(16n, 4n, 17n, true)", () => nthrootMod(16n, 4n, 17n, true), "[2, 8, 9, 15]"],
    ["nthrootMod(1n, 8n, 17n, true)", () => nthrootMod(1n, 8n, 17n, true), "[1, 2, 4, 8, 9, 13, 15, 16]"],
    ["nthrootMod(1n, 4n, 64n, true)", () => nthrootMod(1n, 4n, 64n, true), "[1, 15, 17, 31, 33, 47, 49, 63]"],
    ["nthrootMod(17n, 4n, 64n, true)", () => nthrootMod(17n, 4n, 64n, true), "[3, 13, 19, 29, 35, 45, 51, 61]"],
    ["nthrootMod(3n, 3n, 16n, true)", () => nthrootMod(3n, 3n, 16n, true), "[11]"],
    ["nthrootMod(1n, 3n, 4n * 7n * 9n, true)", () => nthrootMod(1n, 3n, 4n * 7n * 9n, true), "[1, 25, 37, 85, 109, 121, 169, 193, 205]"],
    ["nthrootMod(8n, 3n, 5n * 7n, true)", () => nthrootMod(8n, 3n, 5n * 7n, true), "[2, 22, 32]"],
    ["nthrootMod(2n, 3n, 7n * 13n)", () => nthrootMod(2n, 3n, 7n * 13n), "None"],
    ["nthrootMod(5n, 6n, 7n ** 3n, true)", () => nthrootMod(5n, 6n, 7n ** 3n, true), "[]"],
    ["nthrootMod(1n, 6n, 7n ** 2n, true)", () => nthrootMod(1n, 6n, 7n ** 2n, true), "[1, 18, 19, 30, 31, 48]"],
    ["nthrootMod(68n, 3n, 109n, true)", () => nthrootMod(68n, 3n, 109n, true), "[23, 32, 54]"],
    ["nthrootMod(11n, 4n, 19n, true)", () => nthrootMod(11n, 4n, 19n, true), "[8, 11]"],
    ["nthrootMod(64n, 6n, 3n ** 5n, true)", () => nthrootMod(64n, 6n, 3n ** 5n, true), "[2, 79, 83, 160, 164, 241]"],
    ["nthrootMod(2n, 12n, 37n * 5n, true)", () => nthrootMod(2n, 12n, 37n * 5n, true), "[]"],
    ["nthrootMod(10n, 15n, 31n, true)", () => nthrootMod(10n, 15n, 31n, true), "[]"],
    ["nthrootMod(18n, 12n, 19n, true)", () => nthrootMod(18n, 12n, 19n, true), "[]"],
    ["nthrootMod(5n, 9n, 13n, true)", () => nthrootMod(5n, 9n, 13n, true), "[2, 5, 6]"],
    ["nthrootMod(3n ** 12n % 19n ** 2n, 12n, 19n ** 2n, true)", () => nthrootMod(3n ** 12n % 19n ** 2n, 12n, 19n ** 2n, true), "[3, 154, 157, 204, 207, 358]"],
    ["discreteLog(1n, 7n, 3n)", () => discreteLog(1n, 7n, 3n), "0"],
    ["discreteLog(41n, 15n, 7n)", () => discreteLog(41n, 15n, 7n), "3"],
    ["discreteLog(587n, 2n ** 9n, 2n)", () => discreteLog(587n, 2n ** 9n, 2n), "9"],
    ["discreteLog(2456747n, 3n ** 51n, 3n)", () => discreteLog(2456747n, 3n ** 51n, 3n), "51"],
    ["discreteLog(1000000007n, 123456789n, 5n)", () => discreteLog(1000000007n, 123456789n, 5n), "981640996"],
    ["discreteLog(5779n, 3528n, 6215n)", () => discreteLog(5779n, 3528n, 6215n), "687"],
    ["discreteLog(587n, 2n ** 9n, 2n, 293n, true)", () => discreteLog(587n, 2n ** 9n, 2n, 293n, true), "9"],
    ["discreteLog(587n, 2n ** 9n, 2n, 586n)", () => discreteLog(587n, 2n ** 9n, 2n, 586n), "9"],
    ["discreteLog(13n ** 10n, 2n ** 20n, 2n)", () => discreteLog(13n ** 10n, 2n ** 20n, 2n), "20"],
    ["discreteLog(2000000000123n, 349287970764n, 4n, 1000000000061n, true)", () => discreteLog(2000000000123n, 349287970764n, 4n, 1000000000061n, true), "123456789"],
    ["discreteLog(983n, 1n, 2n, 2n ** 61n - 1n, true)", () => discreteLog(983n, 1n, 2n, 2n ** 61n - 1n, true), "0"],
    ["linearCongruence(3n, 2n, 5n)", () => linearCongruence(3n, 2n, 5n), "[4]"],
    ["linearCongruence(0n, 0n, 4n)", () => linearCongruence(0n, 0n, 4n), "[0, 1, 2, 3]"],
    ["linearCongruence(5n, 3n, 5n)", () => linearCongruence(5n, 3n, 5n), "[]"],
    ["linearCongruence(6n, 4n, 10n)", () => linearCongruence(6n, 4n, 10n), "[4, 9]"],
    ["linearCongruence(6n, 3n, 10n)", () => linearCongruence(6n, 3n, 10n), "[]"],
    ["linearCongruence(-4n, 6n, 10n)", () => linearCongruence(-4n, 6n, 10n), "[6, 1]"],
    ["quadraticCongruence(0n, 3n, 2n, 5n)", () => quadraticCongruence(0n, 3n, 2n, 5n), "[1]"],
    ["quadraticCongruence(1n, 1n, 0n, 2n)", () => quadraticCongruence(1n, 1n, 0n, 2n), "[0, 1]"],
    ["quadraticCongruence(1n, 0n, 1n, 2n)", () => quadraticCongruence(1n, 0n, 1n, 2n), "[1]"],
    ["quadraticCongruence(1n, 1n, 1n, 2n)", () => quadraticCongruence(1n, 1n, 1n, 2n), "[]"],
    ["quadraticCongruence(1n, 0n, 0n, 2n)", () => quadraticCongruence(1n, 0n, 0n, 2n), "[0]"],
    ["quadraticCongruence(2n, 3n, 1n, 7n)", () => quadraticCongruence(2n, 3n, 1n, 7n), "[3, 6]"],
    ["quadraticCongruence(1n, 3n, -4n, 9n)", () => quadraticCongruence(1n, 3n, -4n, 9n), "[1, 5]"],
    ["quadraticCongruence(2n, 1n, -1n, 8n)", () => quadraticCongruence(2n, 1n, -1n, 8n), "[7]"],
    ["quadraticCongruence(4n, 2n, -2n, 12n)", () => quadraticCongruence(4n, 2n, -2n, 12n), "[5, 11]"],
    ["quadraticCongruence(3n, 3n, 6n, 9n)", () => quadraticCongruence(3n, 3n, 6n, 9n), "[]"],
    ["quadraticCongruence(2n, 2n, 0n, 6n)", () => quadraticCongruence(2n, 2n, 0n, 6n), "[0, 2, 3, 5]"],
    ["gfCsolve([1n, 1n, 7n], 189n)", () => gfCsolve([1n, 1n, 7n], 189n), "[13, 49, 76, 112, 139, 175]"],
    ["gfCsolve([1n, 0n, 0n, -8n], 27n)", () => gfCsolve([1n, 0n, 0n, -8n], 27n), "[2, 11, 20]"],
    ["gfCsolve([1n, 2n, 3n, 4n, 5n], 7n)", () => gfCsolve([1n, 2n, 3n, 4n, 5n], 7n), "[]"],
    ["gfCsolve([1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, -1n], 3n)", () => gfCsolve([1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, -1n], 3n), "[1, 2]"],
    ["gfCsolve([0n], 6n)", () => gfCsolve([0n], 6n), "[0, 1, 2, 3, 4, 5]"],
    ["gfCsolve([3n], 9n)", () => gfCsolve([3n], 9n), "[]"],
    ["gfCsolve([5n], 9n)", () => gfCsolve([5n], 9n), "[]"],
    ["gfCsolve([1n, 0n, 0n, 0n], 101n)", () => gfCsolve([1n, 0n, 0n, 0n], 101n), "[0]"],
    ["gfCsolve([1n, -3n, 2n], 101n)", () => gfCsolve([1n, -3n, 2n], 101n), "[1, 2]"],
    ["gfCsolve([1n, -6n, 11n, -6n], 1009n)", () => gfCsolve([1n, -6n, 11n, -6n], 1009n), "[1, 2, 3]"],
    ["gfCsolve([1n, -10n, 35n, -50n, 24n], 1009n)", () => gfCsolve([1n, -10n, 35n, -50n, 24n], 1009n), "[1, 2, 3, 4]"],
    ["gfCsolve([1n, -21n, 175n, -735n, 1624n, -1764n, 720n], 10007n)", () => gfCsolve([1n, -21n, 175n, -735n, 1624n, -1764n, 720n], 10007n), "[1, 2, 3, 4, 5, 6]"],
    ["gfCsolve([1n, 0n, 0n, -2n], 10007n)", () => gfCsolve([1n, 0n, 0n, -2n], 10007n), "[2486]"],
    ["gfCsolve([1n, 0n, 0n, 0n, -1n], 10009n)", () => gfCsolve([1n, 0n, 0n, 0n, -1n], 10009n), "[1, 3303, 6706, 10008]"],
    ["gfCsolve([1n, 0n, -3n, 2n], 101n)", () => gfCsolve([1n, 0n, -3n, 2n], 101n), "[1, 99]"],
    ["gfCsolve([1n, -6n, 11n, -6n, 0n], 1009n)", () => gfCsolve([1n, -6n, 11n, -6n, 0n], 1009n), "[0, 1, 2, 3]"],
    ["gfCsolve([2n, 3n, 5n, 7n, 11n], 1009n)", () => gfCsolve([2n, 3n, 5n, 7n, 11n], 1009n), "[344]"],
    ["gfCsolve([1n, 0n, 0n, 0n, -1n], 5n ** 3n)", () => gfCsolve([1n, 0n, 0n, 0n, -1n], 5n ** 3n), "[1, 57, 68, 124]"],
    ["gfCsolve([1n, 1n, 1n, 1n, 1n, 1n], 31n * 4n)", () => gfCsolve([1n, 1n, 1n, 1n, 1n, 1n], 31n * 4n), "[67, 87, 99, 119, 123]"],
    ["gfCsolve([1n, 0n, 0n, 0n, 0n, 0n, 0n, -2n], 13n)", () => gfCsolve([1n, 0n, 0n, 0n, 0n, 0n, 0n, -2n], 13n), "[11]"],
    ["gfCsolve([3n, 0n, 5n, 0n, 1n], 9n * 49n)", () => gfCsolve([3n, 0n, 5n, 0n, 1n], 9n * 49n), "[]"],
    ["polynomialCongruence(x.pow(6).sub(x.pow(2).mul(2)).add(5), 7n)", () => polynomialCongruence(x.pow(6).sub(x.pow(2).mul(2)).add(5), 7n), "[]"],
    ["polynomialCongruence(x.pow(2).add(x).add(1), 7n)", () => polynomialCongruence(x.pow(2).add(x).add(1), 7n), "[2, 4]"],
    ["polynomialCongruence(x.mul(3).add(1), 7n)", () => polynomialCongruence(x.mul(3).add(1), 7n), "[2]"],
    ["polynomialCongruence(x.pow(5).sub(3), 11n)", () => polynomialCongruence(x.pow(5).sub(3), 11n), "[]"],
    ["polynomialCongruence(x.pow(3).add(x.mul(2)).add(1), 125n)", () => polynomialCongruence(x.pow(3).add(x.mul(2)).add(1), 125n), "[]"],
    ["polynomialCongruence(x.pow(4).mul(2).add(x).sub(3), 1000n)", () => polynomialCongruence(x.pow(4).mul(2).add(x).sub(3), 1000n), "[1]"],
    ["polynomialCongruence(x.pow(2).mul(x.add(1)).sub(x.pow(3)), 5n)", () => polynomialCongruence(x.pow(2).mul(x.add(1)).sub(x.pow(3)), 5n), "[0]"],
    ["polynomialCongruence(x.pow(3).add(1), 9n)", () => polynomialCongruence(x.pow(3).add(1), 9n), "[2, 5, 8]"],
    ["polynomialCongruence(x.pow(3).mul(4).add(1), 9n)", () => polynomialCongruence(x.pow(3).mul(4).add(1), 9n), "[]"],
  ];
  for (const [label, f, want] of cases) it(label, () => expect(py(f())).toBe(want));
  const errors: [string, () => unknown][] = [
    ["nOrder(1n, 1n)", () => nOrder(1n, 1n)],
    ["nOrder(6n, 9n)", () => nOrder(6n, 9n)],
    ["nOrder(10n, 1n)", () => nOrder(10n, 1n)],
    ["primitiveRoot(1n)", () => primitiveRoot(1n)],
    ["isPrimitiveRoot(2n, 1n)", () => isPrimitiveRoot(2n, 1n)],
    ["isPrimitiveRoot(3n, 6n)", () => isPrimitiveRoot(3n, 6n)],
    ["isPrimitiveRoot(2n, 2n * 7n ** 3n)", () => isPrimitiveRoot(2n, 2n * 7n ** 3n)],
    ["isQuadResidue(3n, 0n)", () => isQuadResidue(3n, 0n)],
    ["isNthpowResidue(2n, 3n, 0n)", () => isNthpowResidue(2n, 3n, 0n)],
    ["isNthpowResidue(2n, -1n, 5n)", () => isNthpowResidue(2n, -1n, 5n)],
    ["nthrootMod(3n, 0n, 7n)", () => nthrootMod(3n, 0n, 7n)],
    ["nthrootMod(3n, 3n, 0n)", () => nthrootMod(3n, 3n, 0n)],
    ["discreteLog(2n ** 5n * 3n ** 3n, 17n, 5n)", () => discreteLog(2n ** 5n * 3n ** 3n, 17n, 5n)],
    ["discreteLog(32942478n, 1122334455n, 3n)", () => discreteLog(32942478n, 1122334455n, 3n)],
    ["discreteLog(7n, 3n, 2n)", () => discreteLog(7n, 3n, 2n)],
    ["discreteLog(0n, 3n, 2n)", () => discreteLog(0n, 3n, 2n)],
    ["discreteLog(10n, 3n, 9n)", () => discreteLog(10n, 3n, 9n)],
    ["discreteLog(2027n, -1n, 4n, 1013n, true)", () => discreteLog(2027n, -1n, 4n, 1013n, true)],
    ["discreteLog(1000003n, 5n, 1000002n)", () => discreteLog(1000003n, 5n, 1000002n)],
    ["quadraticCongruence(1n, 1n, 1n, 1n)", () => quadraticCongruence(1n, 1n, 1n, 1n)],
    ["polynomialCongruence(x.mul(y), 9n)", () => polynomialCongruence(x.mul(y), 9n)],
    ["polynomialCongruence(x.div(2).add(1), 9n)", () => polynomialCongruence(x.div(2).add(1), 9n)],
    ["polynomialCongruence(x.pow(-1).add(1), 9n)", () => polynomialCongruence(x.pow(-1).add(1), 9n)],
    ["polynomialCongruence(x.add(y), 9n)", () => polynomialCongruence(x.add(y), 9n)],
    ["polynomialCongruence(5, 7n)", () => polynomialCongruence(5, 7n)],
  ];
  for (const [label, f] of errors) it(`${label} throws`, () => expect(f).toThrow());
  // SymPy's test_residue vectors for the internal algorithms, with the order n_order(b, n) and rseed as there
  it('dlogPollardRho', () => {
    expect(dlogPollardRho(6013199n, 2n ** 6n, 2n, 3006599n, 10, 0n)).toBe(6n);
    expect(dlogPollardRho(6138719n, 2n ** 19n, 2n, 3069359n, 10, 0n)).toBe(19n);
    expect(dlogPollardRho(36721943n, 2n ** 40n, 2n, 18360971n, 10, 0n)).toBe(40n);
    expect(dlogPollardRho(24567899n, 3n ** 333n, 3n, 12283949n, 10, 0n)).toBe(333n);
    expect(() => dlogPollardRho(11n, 7n, 31n, 5n, 10, 0n)).toThrow(RangeError);
    expect(() => dlogPollardRho(227n, 3n ** 7n, 5n, 226n, 10, 0n)).toThrow(RangeError);
  });
  it('dlogIndexCalculus', () => {
    expect(dlogIndexCalculus(983n, 948n, 2n, 491n)).toBe(183n);
    expect(dlogIndexCalculus(633383n, 21794n, 2n, 316691n)).toBe(68048n);
    expect(dlogIndexCalculus(47747730623n, 19410045286n, 43425105668n, 645239603n)).toBe(590504662n);
    expect(dlogIndexCalculus(983n, 948n, 2n, 491n, 0n)).toBe(183n);
    expect(dlogIndexCalculus(633383n, 21794n, 2n, 316691n, 1n)).toBe(68048n);
    // SymPy raises ValueError: a is never smooth, and b = 1 gives no relations
    expect(() => dlogIndexCalculus(983n, 947n, 2n, 1n)).toThrow(RangeError);
    expect(() => dlogIndexCalculus(983n, 2n, 1n, 10n)).toThrow(RangeError);
  });
  // a prime order much larger than the true one sends discrete_log to the index calculus, whose outcome depends on the shared generator
  it('discreteLog through the index calculus (SymPy with seed(0) and seed(11))', () => {
    seed(0);
    expect(() => discreteLog(983n, 948n, 2n, 2n ** 61n - 1n, true)).toThrow(RangeError);
    seed(11);
    expect(discreteLog(983n, 948n, 2n, 2n ** 61n - 1n, true)).toBe(472802671616939134n);
  });
  // SymPy 1.14 raises UnboundLocalError for an order that is given and not prime (order_factors is unset);
  // the logarithm is the one found without the order: 2**864664 = 123456 (mod 1000003)
  it('discreteLog with a composite order', () => expect(discreteLog(1000003n, 123456n, 2n, 1000002n)).toBe(864664n));
  it('gfCsolve: the random splitting with a fixed seed', () => {
    for (let s = 0; s < 8; s++) {
      seed(s);
      expect(py(gfCsolve([1n, -6n, 11n, -6n], 1009n))).toBe('[1, 2, 3]');
      expect(py(gfCsolve([1n, -10n, 35n, -50n, 24n], 1009n))).toBe('[1, 2, 3, 4]');
    }
  });
});
