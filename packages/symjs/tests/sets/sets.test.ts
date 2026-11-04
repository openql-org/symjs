// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/sets/sets.ts.

// Coverage of sets/sets.ts. Each case gives the SymPy 1.14 expression and its str(); where symjs
// differs, the comment gives SymPy's answer and the reason.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import * as Sets from '../../src/sets/sets';

const x = sj.symbol('x');
const y = sj.symbol('y');
const r = sj.symbol('r', { real: true });
const f = sj.SymFunction('f');
const I = (a: sj.ExprLike, b: sj.ExprLike, l = false, ro = false): Sets.SetExpr => Sets.interval(a, b, l, ro);
const F = (...a: sj.ExprLike[]): Sets.SetExpr => Sets.finiteSet(...a);
const U = (...a: Sets.SetExpr[]): Sets.SetExpr => Sets.union(...a);
const C = (s: Sets.SetExpr, v: sj.ExprLike): sj.Expr => Sets.contains(s, sj.sympify(v));
const show = (v: unknown): string => (v === undefined ? 'None' : typeof v === 'boolean' ? (v ? 'True' : 'False') : v instanceof sj.Expr ? v.toString() : typeof v === 'string' ? v : JSON.stringify(v));
const attempt = (run: () => unknown): string => {
  try {
    return show(run());
  } catch (err) {
    return `ERR ${err instanceof Error ? err.name : String(err)}`;
  }
};
const CASES: readonly (readonly [sympy: string, run: () => unknown, expected: string])[] = [
  ["Interval(0,1).is_empty", () => I(0, 1).isEmpty, "False"],
  ["S.EmptySet.is_empty", () => Sets.EmptySet.isEmpty, "True"],
  ["S.Reals.is_empty", () => Sets.Reals.isEmpty, "False"],
  ["Interval(2,1)", () => I(2, 1), "EmptySet"],
  ["Interval(pi + Rational(1,10**20), pi)", () => I(sj.add(sj.pi, sj.Rational.of(1n, 10n ** 20n)), sj.pi), "EmptySet"],
  ["Interval(pi, pi + Rational(1,10**20))", () => I(sj.pi, sj.add(sj.pi, sj.Rational.of(1n, 10n ** 20n))), "Interval(pi, 1/100000000000000000000 + pi)"],
  ["Interval(Float(0.5), Rational(1,2))", () => I(sj.sympify(0.5), sj.Rational.of(1n, 2n)), "{0.5}"],  // SymPy 1.14: Interval(0.500000000000000, 1/2); 0.5 = 1/2, so the interval is the single point
  ["Interval(oo, oo)", () => I(sj.oo, sj.oo), "EmptySet"],
  ["Interval(1, 1)", () => I(1, 1), "{1}"],
  ["Interval.open(1, 1)", () => Sets.openInterval(1, 1), "EmptySet"],
  ["Interval.open(0, 1)", () => Sets.openInterval(0, 1), "Interval.open(0, 1)"],
  ["Interval.Lopen(0, 1)", () => Sets.Lopen(0, 1), "Interval.Lopen(0, 1)"],
  ["Interval.Ropen(0, 1)", () => Sets.Ropen(0, 1), "Interval.Ropen(0, 1)"],
  ["Interval(-oo, 1)", () => I(sj.S.NegativeInfinity, 1), "Interval(-oo, 1)"],
  ["Interval(0, oo)", () => I(0, sj.oo), "Interval(0, oo)"],
  ["Interval(-oo, 1, True, True)", () => I(sj.S.NegativeInfinity, 1, true, true), "Interval.open(-oo, 1)"],
  ["S.Reals.contains(x)", () => C(Sets.Reals, x), "(-oo < x) & (x < oo)"],
  ["S.Reals.contains(oo)", () => C(Sets.Reals, sj.oo), "False"],
  ["S.Reals.contains(sqrt(2))", () => C(Sets.Reals, sj.sqrt(2)), "True"],
  ["S.Reals.contains(I)", () => C(Sets.Reals, sj.I), "False"],
  ["S.Reals.contains(r)", () => C(Sets.Reals, r), "True"],
  ["S.EmptySet.contains(x)", () => C(Sets.EmptySet, x), "False"],
  ["S.Complexes.contains(oo)", () => C(Sets.Complexes, sj.oo), "False"],
  ["S.Complexes.contains(I)", () => C(Sets.Complexes, sj.I), "True"],
  ["S.Integers.contains(2)", () => C(Sets.Integers, 2), "True"],
  ["S.Integers.contains(Rational(1,2))", () => C(Sets.Integers, sj.Rational.of(1n, 2n)), "False"],
  ["S.Naturals.contains(0)", () => C(Sets.Naturals, 0), "False"],
  ["S.Naturals.contains(3)", () => C(Sets.Naturals, 3), "True"],
  ["S.Naturals0.contains(0)", () => C(Sets.Naturals0, 0), "True"],
  ["S.Naturals0.contains(-1)", () => C(Sets.Naturals0, -1), "False"],
  ["S.Integers.contains(x)", () => C(Sets.Integers, x), "Contains(x, Integers)"],
  ["FiniteSet(1, 2).contains(2)", () => C(F(1, 2), 2), "True"],
  ["FiniteSet(1, 2).contains(3)", () => C(F(1, 2), 3), "False"],
  ["FiniteSet(1, 2).contains(x)", () => C(F(1, 2), x), "Eq(1, x) | Eq(2, x)"],
  ["Interval(0, 1).contains(oo)", () => C(I(0, 1), sj.oo), "False"],
  ["Interval(0, 1).contains(Rational(1,2))", () => C(I(0, 1), sj.Rational.of(1n, 2n)), "True"],
  ["Interval.open(0, 1).contains(0)", () => C(Sets.openInterval(0, 1), 0), "False"],
  ["Interval.open(0, 1).contains(1)", () => C(Sets.openInterval(0, 1), 1), "False"],
  ["Interval(0, 1).contains(x)", () => C(I(0, 1), x), "(0 <= x) & (x <= 1)"],
  ["Interval.open(0, 1).contains(x)", () => C(Sets.openInterval(0, 1), x), "(0 < x) & (x < 1)"],
  ["Union(Interval(0, 1), FiniteSet(x)).contains(Rational(1,2))", () => C(U(I(0, 1), F(x)), sj.Rational.of(1n, 2n)), "True"],
  ["Union(Interval(0, 1), Interval(2, 3)).contains(5)", () => C(U(I(0, 1), I(2, 3)), 5), "False"],
  ["Union(Interval(0, 1), FiniteSet(x)).contains(5)", () => C(U(I(0, 1), F(x)), 5), "Eq(x, 5)"],
  ["Intersection(FiniteSet(x), Interval(0, 1)).contains(5)", () => C(Sets.intersection(F(x), I(0, 1)), 5), "False"],
  ["Intersection(FiniteSet(x, 1), Interval(0, 2)).contains(1)", () => C(Sets.intersection(F(x, 1), I(0, 2)), 1), "True"],
  ["Complement(FiniteSet(x), Interval(0, 1))", () => Sets.complement(F(x), I(0, 1)), "Complement({x}, Interval(0, 1))"],
  ["Complement(FiniteSet(x, 2), Interval(0, 1)).contains(2)", () => C(Sets.complement(F(x, 2), I(0, 1)), 2), "True"],
  ["Complement(FiniteSet(x, 2), Interval(0, 1)).contains(Rational(1,2))", () => C(Sets.complement(F(x, 2), I(0, 1)), sj.Rational.of(1n, 2n)), "False"],
  ["Complement(FiniteSet(x, 2), Interval(0, 1)).contains(5)", () => C(Sets.complement(F(x, 2), I(0, 1)), 5), "Eq(x, 5)"],
  ["Complement(FiniteSet(x, 2), Interval(0, 1)).contains(y)", () => C(Sets.complement(F(x, 2), I(0, 1)), y), "Eq(2, y) | (Eq(x, y) & ~((0 <= y) & (y <= 1)))"],
  ["Complement(Interval(0, 2), FiniteSet(x)).contains(1)", () => C(Sets.complement(I(0, 2), F(x)), 1), "Ne(x, 1)"],
  ["Union(Interval(0, 1), S.Reals)", () => U(I(0, 1), Sets.Reals), "Reals"],  // SymPy 1.14: Interval(-oo, oo), the same set; symjs writes the whole line as Reals
  ["Union(S.Reals, FiniteSet(1, 2))", () => U(Sets.Reals, F(1, 2)), "Reals"],
  ["Union(S.Reals, FiniteSet(I))", () => U(Sets.Reals, F(sj.I)), "Union({I}, Reals)"],
  ["Union(Interval.open(0, 1), FiniteSet(0, 1))", () => U(Sets.openInterval(0, 1), F(0, 1)), "Interval(0, 1)"],
  ["Union(Interval.open(0, 1), FiniteSet(Rational(1,2), 5))", () => U(Sets.openInterval(0, 1), F(sj.Rational.of(1n, 2n), 5)), "Union({5}, Interval.open(0, 1))"],
  ["Union(Interval(0, 1), Interval(x, 2))", () => U(I(0, 1), I(x, 2)), "Union(Interval(0, 1), Interval(x, 2))"],
  ["Union(Interval(0, 1), Interval(Rational(1,2), x))", () => U(I(0, 1), I(sj.Rational.of(1n, 2n), x)), "Union(Interval(0, 1), Interval(1/2, x))"],
  ["Union(Interval(0, x), Interval(-1, 2))", () => U(I(0, x), I(-1, 2)), "Union(Interval(-1, 2), Interval(0, x))"],
  ["Union(Interval(0, 2), Interval(1, 3))", () => U(I(0, 2), I(1, 3)), "Interval(0, 3)"],
  ["Union(Interval(0, 2, True), Interval(0, 1))", () => U(I(0, 2, true), I(0, 1)), "Interval(0, 2)"],
  ["Union(Interval(0, 1, False, True), Interval(0, 1))", () => U(I(0, 1, false, true), I(0, 1)), "Interval(0, 1)"],
  ["Union(Interval(0, 1, False, True), Interval(1, 2, True))", () => U(I(0, 1, false, true), I(1, 2, true)), "Union(Interval.Ropen(0, 1), Interval.Lopen(1, 2))"],
  ["Union(Interval(-oo, 0), Interval(0, oo))", () => U(I(sj.S.NegativeInfinity, 0), I(0, sj.oo)), "Reals"],  // SymPy 1.14: Interval(-oo, oo), the same set; symjs writes the whole line as Reals
  ["Union(S.Integers, Interval(0, 1))", () => U(Sets.Integers, I(0, 1)), "Union(Integers, Interval(0, 1))"],
  ["Intersection(S.Reals, Interval(0, 1))", () => Sets.intersection(Sets.Reals, I(0, 1)), "Interval(0, 1)"],
  ["Intersection(S.Reals, S.Reals)", () => Sets.intersection(Sets.Reals, Sets.Reals), "Reals"],
  ["Intersection(Interval(0, 1), S.Reals)", () => Sets.intersection(I(0, 1), Sets.Reals), "Interval(0, 1)"],
  ["Intersection(Interval(0, 1), S.EmptySet)", () => Sets.intersection(I(0, 1), Sets.EmptySet), "EmptySet"],
  ["Intersection(FiniteSet(1, x), Interval(0, 2))", () => Sets.intersection(F(1, x), I(0, 2)), "Intersection({1, x}, Interval(0, 2))"],
  ["Intersection(FiniteSet(5, x), Interval(0, 2))", () => Sets.intersection(F(5, x), I(0, 2)), "Intersection({x}, Interval(0, 2))"],
  ["Intersection(Interval(0, x), Interval(1, 2))", () => Sets.intersection(I(0, x), I(1, 2)), "Intersection(Interval(0, x), Interval(1, 2))"],
  ["Intersection(Interval(0, 2), Interval(1, 3))", () => Sets.intersection(I(0, 2), I(1, 3)), "Interval(1, 2)"],
  ["Intersection(Interval(1, 3), Interval(0, 2))", () => Sets.intersection(I(1, 3), I(0, 2)), "Interval(1, 2)"],
  ["Intersection(Interval(0, 2, True), Interval(0, 2, False, True))", () => Sets.intersection(I(0, 2, true), I(0, 2, false, true)), "Interval.open(0, 2)"],
  ["Complement(Interval(0, 1), S.EmptySet)", () => Sets.complement(I(0, 1), Sets.EmptySet), "Interval(0, 1)"],
  ["Complement(S.EmptySet, Interval(0, 1))", () => Sets.complement(Sets.EmptySet, I(0, 1)), "EmptySet"],
  ["Complement(FiniteSet(1, 5), Interval(0, 2))", () => Sets.complement(F(1, 5), I(0, 2)), "{5}"],
  ["Complement(FiniteSet(1, x), Interval(0, 2))", () => Sets.complement(F(1, x), I(0, 2)), "Complement({x}, Interval(0, 2))"],
  ["Complement(Interval(0, 3), FiniteSet(1, 2))", () => Sets.complement(I(0, 3), F(1, 2)), "Union(Interval.Ropen(0, 1), Interval.open(1, 2), Interval.Lopen(2, 3))"],
  ["Complement(Interval(0, 3), FiniteSet(5))", () => Sets.complement(I(0, 3), F(5)), "Interval(0, 3)"],
  ["Complement(S.Reals, FiniteSet(0))", () => Sets.complement(Sets.Reals, F(0)), "Union(Interval.open(-oo, 0), Interval.open(0, oo))"],
  ["Complement(Interval(0, 3), Interval(1, 2))", () => Sets.complement(I(0, 3), I(1, 2)), "Union(Interval.Ropen(0, 1), Interval.Lopen(2, 3))"],
  ["Complement(Interval(0, 3), Interval(5, 6))", () => Sets.complement(I(0, 3), I(5, 6)), "Interval(0, 3)"],
  ["Complement(Interval(0, 3), S.Integers)", () => Sets.complement(I(0, 3), Sets.Integers), "Complement(Interval(0, 3), Integers)"],
  ["Complement(S.Reals, Interval(0, 1))", () => Sets.complement(Sets.Reals, I(0, 1)), "Union(Interval.open(-oo, 0), Interval.open(1, oo))"],
  ["Complement(Union(Interval(0, 1), Interval(2, 3)), Interval(Rational(1,2), Rational(5,2)))", () => Sets.complement(U(I(0, 1), I(2, 3)), I(sj.Rational.of(1n, 2n), sj.Rational.of(5n, 2n))), "Union(Interval.Ropen(0, 1/2), Interval.Lopen(5/2, 3))"],
  ["Interval(0, 1).is_subset(S.Reals)", () => Sets.isSubset(I(0, 1), Sets.Reals), "True"],
  ["FiniteSet(1, 2).is_subset(S.Reals)", () => Sets.isSubset(F(1, 2), Sets.Reals), "True"],
  ["S.EmptySet.is_subset(Interval(0, 1))", () => Sets.isSubset(Sets.EmptySet, I(0, 1)), "True"],
  ["FiniteSet(1, 2).is_subset(Interval(0, 1))", () => Sets.isSubset(F(1, 2), I(0, 1)), "False"],
  ["FiniteSet(1, x).is_subset(Interval(0, 1))", () => Sets.isSubset(F(1, x), I(0, 1)), "None"],
  ["FiniteSet(1, I).is_subset(S.Reals)", () => Sets.isSubset(F(1, sj.I), Sets.Reals), "False"],
  ["Interval(0, 1).is_subset(Interval(0, 2))", () => Sets.isSubset(I(0, 1), I(0, 2)), "True"],
  ["Interval(0, 3).is_subset(Interval(0, 2))", () => Sets.isSubset(I(0, 3), I(0, 2)), "False"],
  ["Interval(0, 3).is_subset(S.Integers)", () => Sets.isSubset(I(0, 3), Sets.Integers), "False"],
  ["S.EmptySet.as_relational(x)", () => Sets.asRelational(Sets.EmptySet, x), "False"],
  ["S.Reals.as_relational(x)", () => Sets.asRelational(Sets.Reals, x), "(-oo < x) & (x < oo)"],
  ["Interval.open(0, 1).as_relational(x)", () => Sets.asRelational(Sets.openInterval(0, 1), x), "(0 < x) & (x < 1)"],
  ["Interval(0, 1).as_relational(x)", () => Sets.asRelational(I(0, 1), x), "(0 <= x) & (x <= 1)"],
  ["FiniteSet(1, 2).as_relational(x)", () => Sets.asRelational(F(1, 2), x), "Eq(x, 1) | Eq(x, 2)"],
  ["Union(Interval(0, 1), Interval(2, 3)).as_relational(x)", () => Sets.asRelational(U(I(0, 1), I(2, 3)), x), "((0 <= x) & (x <= 1)) | ((2 <= x) & (x <= 3))"],
  ["Intersection(FiniteSet(y), Interval(0, 1)).as_relational(x)", () => Sets.asRelational(Sets.intersection(F(y), I(0, 1)), x), "Eq(x, y) & (0 <= x) & (x <= 1)"],
  ["Interval(0, 1).inf", () => Sets.inf(I(0, 1)), "0"],
  ["S.Reals.inf", () => Sets.inf(Sets.Reals), "-oo"],
  ["FiniteSet(3, 1, 2).inf", () => Sets.inf(F(3, 1, 2)), "1"],
  ["Union(Interval(2, 3), Interval(0, 1)).inf", () => Sets.inf(U(I(2, 3), I(0, 1))), "0"],
  ["Interval(0, 1).sup", () => Sets.sup(I(0, 1)), "1"],
  ["S.Reals.sup", () => Sets.sup(Sets.Reals), "oo"],
  ["FiniteSet(3, 1, 2).sup", () => Sets.sup(F(3, 1, 2)), "3"],
  ["Union(Interval(2, 3), Interval(0, 1)).sup", () => Sets.sup(U(I(2, 3), I(0, 1))), "3"],
  ["Interval(-oo, oo) (the class constructor)", () => new Sets.Interval(sj.S.NegativeInfinity, sj.oo, true, true), "Interval(-oo, oo)"],
  ["Intersection(Interval(0,1), Union(Interval(2,3), FiniteSet(Rational(1,2), 7)))", () => Sets.intersection(I(0, 1), U(I(2, 3), F(sj.Rational.of(1n, 2n), 7))), "{1/2}"],
  ["Intersection(Union(Interval(2,3), FiniteSet(Rational(1,2), 7)), Interval(0,1))", () => Sets.intersection(U(I(2, 3), F(sj.Rational.of(1n, 2n), 7)), I(0, 1)), "{1/2}"],
  ["Union(Interval(0, 1), FiniteSet(x)).contains(y)", () => C(U(I(0, 1), F(x)), y), "Eq(x, y) | ((0 <= y) & (y <= 1))"],
  ["Intersection(FiniteSet(x), Interval(0, 1)).contains(y)", () => C(Sets.intersection(F(x), I(0, 1)), y), "Eq(x, y) & (0 <= y) & (y <= 1)"],
  ["Complement(Interval(0,2), FiniteSet(x)).contains(y)", () => C(Sets.complement(I(0, 2), F(x)), y), "(0 <= y) & (y <= 2) & Ne(x, y)"],
  ["S.Integers.contains(x)", () => C(Sets.Integers, x), "Contains(x, Integers)"],
  ["S.Naturals.contains(x)", () => C(Sets.Naturals, x), "Contains(x, Naturals)"],
  ["S.Complexes.contains(x)", () => C(Sets.Complexes, x), "Contains(x, Complexes)"],
  ["ImageSet(Lambda(x, x**2), S.Integers).contains(y)", () => C(Sets.imageSet(x, sj.pow(x, 2), Sets.Integers), y), "Contains(y, ImageSet(Lambda(x, x**2), Integers))"],
  ["Contains(x, S.Integers).subs(x, 2)", () => C(Sets.Integers, x).subs(x, 2), "True"],
  ["latex(Contains(x, S.Integers))", () => sj.latex(C(Sets.Integers, x)), "x \\in \\mathbb{Z}"],
  ["Complement(FiniteSet(x, 2, Rational(1,2)), Interval(0, 1))", () => Sets.complement(F(x, 2, sj.Rational.of(1n, 2n)), I(0, 1)), "Union(Complement({x}, Interval(0, 1)), {2})"],
  ["Interval(x, y).is_subset(S.Integers)", () => Sets.isSubset(I(x, y), Sets.Integers), "None"],  // SymPy 1.14 raises TypeError; the interval may be empty
  ["Interval(0, 3).is_subset(S.Naturals0)", () => Sets.isSubset(I(0, 3), Sets.Naturals0), "False"],
  ["Interval(0, 1) == Interval(0, 1)", () => I(0, 1).equals(I(0, 1)), "True"],
  ["FiniteSet(1, 2) == FiniteSet(2, 1)", () => F(1, 2).equals(F(2, 1)), "True"],
  ["Union(Interval(0, 1), S.Integers) == Union(S.Integers, Interval(0, 1))", () => U(I(0, 1), Sets.Integers).equals(U(Sets.Integers, I(0, 1))), "True"],
  ["ImageSet(Lambda(x, x**2), S.Integers) == ImageSet(Lambda(x, x**2), S.Integers)", () => Sets.imageSet(x, sj.pow(x, 2), Sets.Integers).equals(Sets.imageSet(x, sj.pow(x, 2), Sets.Integers)), "True"],
  ["ConditionSet(x, x > 0, S.Reals) == ConditionSet(x, x > 0, S.Reals)", () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals).equals(new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals)), "True"],
  ["Intersection(ImageSet(Lambda(x, x**2), S.Integers), ImageSet(Lambda(x, x**3+x), S.Integers))", () => Sets.intersection(Sets.imageSet(x, sj.pow(x, 2), Sets.Integers), Sets.imageSet(x, sj.add(sj.pow(x, 3), x), Sets.Integers)), "Intersection(ImageSet(Lambda(x, x**2), Integers), ImageSet(Lambda(x, x**3 + x), Integers))"],
  ["S.Complexes.contains(r)", () => C(Sets.Complexes, r), "True"],
  ["S.Complexes.contains(zoo)", () => C(Sets.Complexes, sj.zoo), "False"],
  ["Interval(0, 1).contains(f(1))", () => C(I(0, 1), f(1)), "(0 <= f(1)) & (f(1) <= 1)"],
  ["Complement(Interval(0, 2), S.Integers).contains(Rational(1,2))", () => C(Sets.complement(I(0, 2), Sets.Integers), sj.Rational.of(1n, 2n)), "True"],
  ["Complement(Interval(0, 2), S.Integers).contains(1)", () => C(Sets.complement(I(0, 2), Sets.Integers), 1), "False"],
  ["Union(Union(Interval(0, 1), FiniteSet(x)), Interval(2, 3))", () => U(U(I(0, 1), F(x)), I(2, 3)), "Union({x}, Interval(0, 1), Interval(2, 3))"],
  ["Union(Interval(0, 1), Interval(2, 3), FiniteSet(Rational(1,2)))", () => U(I(0, 1), I(2, 3), F(sj.Rational.of(1n, 2n))), "Union(Interval(0, 1), Interval(2, 3))"],
  ["Union(Interval(0, x), Interval(1, 2))", () => U(I(0, x), I(1, 2)), "Union(Interval(0, x), Interval(1, 2))"],
  ["Union(Interval(0, 2, False, True), Interval(1, 2))", () => U(I(0, 2, false, true), I(1, 2)), "Interval(0, 2)"],
  ["Union(Interval(0, 1, True), Interval(0, 2, True))", () => U(I(0, 1, true), I(0, 2, true)), "Interval.Lopen(0, 2)"],
  ["Intersection(Interval(0, 1), Interval(2, 3), Interval(0, 5))", () => Sets.intersection(I(0, 1), I(2, 3), I(0, 5)), "EmptySet"],
  ["Complement(Interval(0, 3), Union(Interval.open(0, 1), Interval(2, 3)))", () => Sets.complement(I(0, 3), U(Sets.openInterval(0, 1), I(2, 3))), "Union({0}, Interval.Ropen(1, 2))"],
  ["Complement(Interval(0, 3), FiniteSet(2, 1))", () => Sets.complement(I(0, 3), F(2, 1)), "Union(Interval.Ropen(0, 1), Interval.open(1, 2), Interval.Lopen(2, 3))"],
  ["FiniteSet(1, 2).is_subset(Interval(0, 3))", () => Sets.isSubset(F(1, 2), I(0, 3)), "True"],
  ["S.Integers.as_relational(x)", () => Sets.asRelational(Sets.Integers, x), "(-oo < x) & (x < oo) & Eq(floor(x), x)"],
  ["S.Naturals.as_relational(x)", () => Sets.asRelational(Sets.Naturals, x), "(x >= 1) & (x < oo) & Eq(floor(x), x)"],
  ["S.Naturals0.as_relational(x)", () => Sets.asRelational(Sets.Naturals0, x), "(x >= 0) & (x < oo) & Eq(floor(x), x)"],
  ["S.Complexes.as_relational(x)", () => Sets.asRelational(Sets.Complexes, x), "ERR NotImplementedError"],  // SymPy 1.14 raises AttributeError
  ["S.Integers.inf", () => Sets.inf(Sets.Integers), "-oo"],
  ["S.Integers.sup", () => Sets.sup(Sets.Integers), "oo"],
  ["S.Naturals.inf", () => Sets.inf(Sets.Naturals), "1"],
  ["S.Naturals.sup", () => Sets.sup(Sets.Naturals), "oo"],
  ["S.Naturals0.inf", () => Sets.inf(Sets.Naturals0), "0"],
  ["S.Naturals0.sup", () => Sets.sup(Sets.Naturals0), "oo"],
  ["S.Complexes.inf", () => Sets.inf(Sets.Complexes), "ERR NotImplementedError"],
  ["S.Complexes.sup", () => Sets.sup(Sets.Complexes), "ERR NotImplementedError"],
  ["FiniteSet(x, 1, 2).inf", () => Sets.inf(F(x, 1, 2)), "Min(1, x)"],
  ["FiniteSet(x, 1).sup", () => Sets.sup(F(x, 1)), "Max(1, x)"],
  ["Union(Interval(x, 2), Interval(3, 4)).inf", () => Sets.inf(U(I(x, 2), I(3, 4))), "Min(3, x)"],
  ["Union(Interval(0, 2), Interval(3, x)).sup", () => Sets.sup(U(I(0, 2), I(3, x))), "Max(2, x)"],
  ["Interval(-oo, oo)", () => I(sj.S.NegativeInfinity, sj.oo), "Reals"],  // SymPy 1.14: Interval(-oo, oo), the same set; symjs writes the whole line as Reals
  ["Interval(0, 1)", () => Sets.Interval.of(0, 1), "Interval(0, 1)"],
  ["Interval.open(0, 1)", () => Sets.Interval.open(0, 1), "Interval.open(0, 1)"],
  ["Interval.Lopen(0, 1)", () => Sets.Interval.Lopen(0, 1), "Interval.Lopen(0, 1)"],
  ["Interval.Ropen(0, 1)", () => Sets.Interval.Ropen(0, 1), "Interval.Ropen(0, 1)"],
  ["FiniteSet(2, 1, 2)", () => Sets.FiniteSet.of(2, 1, 2), "{1, 2}"],
  ["ConditionSet(x, x > 0, S.Reals)", () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), "ConditionSet(x, x > 0, Reals)"],
  ["Union(Interval(0, 1), FiniteSet(1, 2))", () => U(I(0, 1), F(1, 2)), "Union({2}, Interval(0, 1))"],
  ["Union(Interval(0, 3), Interval(1, 2))", () => U(I(0, 3), I(1, 2)), "Interval(0, 3)"],
  ["type(ConditionSet(x, x > 0, S.Reals)).__name__", () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals).className, "ConditionSet"],
];

describe('sets (SymPy sympy.sets)', () => {
  it.each(CASES)('%s', (_sympy, run, expected) => {
    expect(attempt(run)).toBe(expected);
  });
});

describe('Range, Integers in an interval and ImageSet membership', () => {
  const n = (e: string) => sj.parse(e);
  it('Intersection(Integers, Interval) is a Range (SymPy)', () => {
    expect(String(Sets.intersection(Sets.Integers, I(0, 1)))).toBe('Range(0, 2, 1)');
    expect(String(Sets.intersection(I(-2.5, 3), Sets.Integers))).toBe('Range(-2, 4, 1)');
    expect(String(Sets.intersection(Sets.Naturals, I(0, 3)))).toBe('Range(1, 4, 1)');
    expect(String(Sets.intersection(Sets.Naturals0, I(-5, 2)))).toBe('Range(0, 3, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(0, 3, true, true)))).toBe('Range(1, 3, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(n('-7/2'), n('-1/2'), true, true)))).toBe('Range(-3, 0, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(0, n('oo'))))).toBe('Range(0, oo, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(n('-oo'), n('sqrt(2)'))))).toBe('Range(-oo, 2, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(n('1/2'), n('2/3'))))).toBe('EmptySet');
    expect(String(Sets.intersection(Sets.Integers, I(0, n('2.0'))))).toBe('Range(0, 3, 1)');
    expect(String(Sets.intersection(Sets.Integers, I(0, n('2.5'))))).toBe('Range(0, 3, 1)');
    // an end that is not a known real number, or a number too close to an integer to place, is left unevaluated
    expect(String(Sets.intersection(Sets.Integers, I(0, y)))).toBe('Intersection(Integers, Interval(0, y))');
    expect(String(Sets.intersection(Sets.Integers, I(0, n('2.0000000000001'))))).toBe('Intersection(Integers, Interval(0, 2.0000000000001))');
    expect(Sets.intersection(Sets.Reals, Sets.Integers)).toBe(Sets.Integers);
    expect(Sets.intersection(Sets.Naturals, Sets.Reals)).toBe(Sets.Naturals);
  });
  it('Range', () => {
    expect(String(Sets.Range.of(0, 3))).toBe('Range(0, 3, 1)');
    expect(String(Sets.range(0, 4, 2))).toBe('Range(0, 4, 2)');
    expect(String(Sets.range(0, 5, 2))).toBe('Range(0, 6, 2)');
    expect(String(Sets.range(5, 0, -2))).toBe('Range(5, -1, -2)');
    // SymPy's empty Range
    expect(String(Sets.range(1, 1))).toBe('Range(0, 0, 1)');
    expect(String(Sets.range(3, 1))).toBe('Range(0, 0, 1)');
    expect(() => Sets.range(0, n('1/2'))).toThrow(TypeError);
    expect(() => Sets.range(0, 2, 0)).toThrow(TypeError);
    const r3 = Sets.range(0, 6, 2);
    expect([C(r3, 2), C(r3, 3), C(r3, 6), C(r3, -2), C(r3, n('1/2')), C(r3, n('sqrt(2)')), C(r3, x)].map(String)).toEqual(['True', 'False', 'False', 'False', 'False', 'False', 'Contains(x, Range(0, 6, 2))']);
    expect(String(C(Sets.range(5, -1, -2), 1))).toBe('True');
    expect(String(C(Sets.range(n('-oo'), 4), -10))).toBe('True');
    expect(String(C(Sets.range(1, 1), 0))).toBe('False');
    expect(Sets.range(0, 3).equals(Sets.Range.of(0, 3, 1))).toBe(true);
    // a set without a membership test here (SymPy: True)
    expect(String(C(new Sets.ConditionSet(x, sj.parse('x > 1'), Sets.Reals), 2))).toBe('Contains(2, ConditionSet(x, x > 1, Reals))');
    expect([Sets.inf(r3), Sets.sup(r3), Sets.inf(Sets.range(5, -1, -2)), Sets.sup(Sets.range(5, -1, -2))].map(String)).toEqual(['0', '4', '1', '5']);
  });
  it('Integers contains', () => {
    // SymPy: False for an irrational number
    expect(String(C(Sets.Integers, n('sqrt(3)')))).toBe('False');
    expect(String(C(Sets.Integers, n('pi')))).toBe('False');
  });
  it('ImageSet contains (SymPy ImageSet._contains)', () => {
    const sq = Sets.imageSet(x, n('x**2'), Sets.Integers);
    expect([C(sq, 4), C(sq, 3), C(sq, y)].map(String)).toEqual(['True', 'False', 'Contains(y, ImageSet(Lambda(x, x**2), Integers))']);
    const odd = Sets.imageSet(x, n('2*x + 1'), Sets.Integers);
    expect([C(odd, 3), C(odd, n('1/2'))].map(String)).toEqual(['True', 'False']);
    // roots whose membership is not decided
    expect(String(C(Sets.imageSet(x, n('x**2'), I(0, y)), 4))).toBe('Contains(4, ImageSet(Lambda(x, x**2), Interval(0, y)))');
    // the roots of a quintic are not all known; a non-polynomial expression is not solved
    expect(String(C(Sets.imageSet(x, n('x**5 + x'), Sets.Integers), 3))).toBe('Contains(3, ImageSet(Lambda(x, x**5 + x), Integers))');
    expect(String(C(Sets.imageSet(x, n('sin(x)'), Sets.Integers), 0))).toBe('Contains(0, ImageSet(Lambda(x, sin(x)), Integers))');
    expect(String(C(Sets.imageSet(n('2*x'), n('x'), Sets.Integers), 0))).toBe('Contains(0, ImageSet(Lambda(2*x, x), Integers))');
  });
  it('isSubset of an interval with a finite end', () => {
    // SymPy: Reals.is_subset(Interval(0, 1)) is False
    expect(Sets.isSubset(Sets.Reals, I(0, 1))).toBe(false);
    expect(Sets.isSubset(Sets.Integers, I(n('-oo'), 1))).toBe(false);
  });
});

// SymPy 1.14 str() of each expression; where symjs differs, the comment gives SymPy's answer and why.
describe('Rationals, UniversalSet, ProductSet, PowerSet, DisjointUnion and SymmetricDifference', () => {
  const p = (e: string) => sj.parse(e);
  const A = F(1, 2, 3);
  const B = I(0, 5);
  const Cs = F(x, sj.symbol('y'), sj.symbol('z'));
  const T = (...a: sj.ExprLike[]) => sj.Tuple(...a);
  const k = sj.symbol('k', { integer: true });
  it('Rationals and UniversalSet', () => {
    expect([C(Sets.Rationals, p('1/2')), C(Sets.Rationals, sj.pi), C(Sets.Rationals, sj.I), C(Sets.Rationals, sj.oo), C(Sets.Rationals, x), C(Sets.Rationals, k), C(Sets.Rationals, sj.S.Catalan)].map(String)).toEqual([
      'True',
      'False',
      'False',
      'False',
      'Contains(x, Rationals)',
      'True',
      'Contains(Catalan, Rationals)',
    ]);
    expect(String(C(Sets.UniversalSet, x))).toBe('True');
    expect(String(U(I(0, 1), Sets.UniversalSet))).toBe('UniversalSet');
    expect(String(U(Sets.Rationals, Sets.Integers))).toBe('Rationals');
    expect(String(Sets.intersection(Sets.Rationals, Sets.Integers))).toBe('Integers');
    expect(String(Sets.intersection(Sets.Rationals, Sets.Reals))).toBe('Rationals');
    expect(String(Sets.intersection(Sets.Rationals, I(0, 1)))).toBe('Intersection(Interval(0, 1), Rationals)');
    expect(String(Sets.intersection(Sets.UniversalSet, I(0, 1)))).toBe('Interval(0, 1)');
    expect(String(Sets.complement(I(0, 1), Sets.UniversalSet))).toBe('EmptySet');
    // SymPy: None for UniversalSet.is_subset(Interval(0, 1)); the universal set has elements outside [0, 1]
    expect([Sets.isSubset(I(0, 1), Sets.UniversalSet), Sets.isSubset(Sets.UniversalSet, I(0, 1)), Sets.isSubset(Sets.Integers, Sets.Rationals), Sets.isSubset(Sets.Rationals, Sets.Reals)]).toEqual([true, false, true, true]);
  });
  it('ProductSet', () => {
    expect([sj.ProductSet(), sj.ProductSet(A, Sets.EmptySet), sj.ProductSet(B, A)].map(String)).toEqual(['{()}', 'EmptySet', 'ProductSet(Interval(0, 5), {1, 2, 3})']);
    const ps = sj.ProductSet(A, B) as sj.ProductSetNode;
    expect(String((sj.ProductSet(ps, Cs) as sj.ProductSetNode).flatten())).toBe('ProductSet({1, 2, 3}, Interval(0, 5), {x, y, z})');
    expect(ps.sets.map(String)).toEqual(['{1, 2, 3}', 'Interval(0, 5)']);
    expect([C(ps, T(1, 2)), C(ps, T(4, 2)), C(ps, T(1, 2, 3)), C(ps, T(x, 2)), C(ps, x), C(ps, 1)].map(String)).toEqual([
      'True',
      'False',
      'False',
      'Contains((x, 2), ProductSet({1, 2, 3}, Interval(0, 5)))',
      'Contains(x, ProductSet({1, 2, 3}, Interval(0, 5)))',
      'False',
    ]);
    expect(String(Sets.intersection(sj.ProductSet(B, B), sj.ProductSet(I(1, 7), I(2, 3))))).toBe('ProductSet(Interval(1, 5), Interval(2, 3))');
    expect(String(Sets.intersection(sj.ProductSet(B, B), sj.ProductSet(B, B, B)))).toBe('EmptySet');
    // SymPy: None for the last two; [1, 7] is not in [0, 5], and pairs are not triples
    expect([
      Sets.isSubset(sj.ProductSet(I(1, 2), I(1, 2)), sj.ProductSet(B, B)),
      Sets.isSubset(sj.ProductSet(I(1, 7), I(1, 2)), sj.ProductSet(B, B)),
      Sets.isSubset(sj.ProductSet(B, B), sj.ProductSet(B, B, B)),
      Sets.isSubset(sj.ProductSet(B, I(0, x)), sj.ProductSet(B, B)),
    ]).toEqual([true, false, false, undefined]);
    expect(Sets.isSubset(I(0, x), B)).toBe(undefined);
    expect(String(U(sj.ProductSet(B, B), sj.ProductSet(I(1, 2), I(1, 2))))).toBe('ProductSet(Interval(0, 5), Interval(0, 5))');
    expect(String(U(sj.ProductSet(A, B), sj.ProductSet(Cs, B)))).toBe('ProductSet({1, 2, 3, x, y, z}, Interval(0, 5))');
    expect(String(U(sj.ProductSet(A, B), sj.ProductSet(Cs, A)))).toBe('Union(ProductSet({1, 2, 3}, Interval(0, 5)), ProductSet({x, y, z}, {1, 2, 3}))');
    expect(String(U(sj.ProductSet(A, B, B), sj.ProductSet(Cs, A, A)))).toBe('Union(ProductSet({1, 2, 3}, Interval(0, 5), Interval(0, 5)), ProductSet({x, y, z}, {1, 2, 3}, {1, 2, 3}))');
    expect(sj.latex(ps)).toBe('\\left\\{1, 2, 3\\right\\} \\times \\left[0, 5\\right]');
    expect(sj.latex(sj.ProductSet(B, B))).toBe('\\left[0, 5\\right]^{2}');
    expect(sj.latex(sj.ProductSet(U(I(0, 1), I(2, 3)), A))).toBe('\\left(\\left[0, 1\\right] \\cup \\left[2, 3\\right]\\right) \\times \\left\\{1, 2, 3\\right\\}');
  });
  it('PowerSet and powerset', () => {
    expect([Sets.powerset(Sets.EmptySet), Sets.powerset(B), Sets.powerset(A)].map(String)).toEqual(['{EmptySet}', 'PowerSet(Interval(0, 5))', 'FiniteSet(EmptySet, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3})']);
    const pw = sj.PowerSet(B);
    expect([C(pw, I(1, 2)), C(pw, x)].map(String)).toEqual(['True', 'Contains(x, PowerSet(Interval(0, 5)))']);
    expect([sj.PowerSet(F(1, 2)).rewriteAsFiniteSet(), sj.PowerSet(Sets.EmptySet).rewriteAsFiniteSet(), pw.rewriteAsFiniteSet()].map(String)).toEqual(['FiniteSet(EmptySet, {1}, {2}, {1, 2})', '{EmptySet}', 'PowerSet(Interval(0, 5))']);
    expect(sj.latex(pw)).toBe('\\mathcal{P}\\left(\\left[0, 5\\right]\\right)');
    expect(String(F(T(F(1), 2)))).toBe('FiniteSet(({1}, 2))');
  });
  it('DisjointUnion', () => {
    const du = sj.DisjointUnion(A, B);
    expect(String(du)).toBe('DisjointUnion({1, 2, 3}, Interval(0, 5))');
    expect(du.sets.map(String)).toEqual(['{1, 2, 3}', 'Interval(0, 5)']);
    expect([du.isEmpty, sj.DisjointUnion(Sets.EmptySet, Sets.EmptySet).isEmpty]).toEqual([false, true]);
    expect([C(du, T(2, 0)), C(du, T(2, 5)), C(du, T(2, p('1/2'))), C(du, 2), C(du, T(7, 1)), C(du, T(7, -1)), C(du, T(x, 1))].map(String)).toEqual([
      'True',
      'False',
      'False',
      'False',
      'False',
      'False',
      'Contains((x, 1), DisjointUnion({1, 2, 3}, Interval(0, 5)))',
    ]);
    expect(String(du.rewriteAsUnion())).toBe('Union(ProductSet({1, 2, 3}, {0}), ProductSet(Interval(0, 5), {1}))');
    expect(sj.latex(du)).toBe('\\operatorname{DisjointUnion}\\left(\\left\\{1, 2, 3\\right\\}, \\left[0, 5\\right]\\right)');
  });
  it('SymmetricDifference', () => {
    expect([sj.SymmetricDifference(A, F(3, 4, 5)), sj.SymmetricDifference(Sets.EmptySet, A), sj.SymmetricDifference(Sets.Reals, Sets.EmptySet), Sets.symmetricDifference(I(1, 3), Sets.Reals)].map(String)).toEqual([
      '{1, 2, 4, 5}',
      '{1, 2, 3}',
      'Reals',
      'Union(Interval.open(-oo, 1), Interval.open(3, oo))',
    ]);
    // SymPy: UniversalSet.symmetric_difference(B) is B; U ^ B is the complement of B
    expect(String(Sets.symmetricDifference(Sets.UniversalSet, B))).toBe('Complement(UniversalSet, Interval(0, 5))');
    const sd = Sets.symmetricDifference(A, B, { evaluate: false });
    expect(String(sd)).toBe('SymmetricDifference({1, 2, 3}, Interval(0, 5))');
    // SymPy: NotImplementedError (SymmetricDifference._contains)
    expect([C(sd, p('1/2')), C(sd, 2), C(sd, 7), C(sd, x)].map(String)).toEqual(['True', 'False', 'False', 'Contains(x, SymmetricDifference({1, 2, 3}, Interval(0, 5)))']);
    expect(sj.latex(sd)).toBe('\\left\\{1, 2, 3\\right\\} \\triangle \\left[0, 5\\right]');
    expect(sj.latex(Sets.Rationals)).toBe('\\mathbb{Q}');
  });
  it('substitution in sets (SymPy _eval_subs)', () => {
    const [yy, z] = [sj.symbol('y'), sj.symbol('z')];
    const cs = (v: sj.Expr, c: string, b: Sets.SetExpr) => sj.ConditionSet.of(v, p(c), b);
    expect([
      sj.subs(cs(x, 'x < y', Sets.Integers), [[x, z]]),
      sj.subs(cs(x, 'x < y', Sets.Integers), [[yy, z]]),
      // SymPy keeps x < y for a number: _diff_wrt is False
      sj.subs(cs(x, 'x < y', Sets.Integers), [[yy, 2]]),
      sj.subs(cs(x, 'x < y', I(0, yy)), [[yy, 3]]),
      sj.subs(cs(x, 'x < y', F(x, z)), [[z, 1]]),
      sj.subs(cs(x, 'x < 1', F(x, z)), [[x, yy]]),
      sj.subs(Sets.imageSet(x, p('x**2 + y'), I(0, yy)), [[yy, 2]]),
      sj.subs(Sets.imageSet(x, p('x**2'), I(0, yy)), [[x, 2]]),
      // SymPy: BadSignatureError; the x of the base set is free and is replaced
      sj.subs(Sets.imageSet(x, p('x**2'), I(0, x)), [[x, 2]]),
      sj.subs(I(0, yy), [[yy, 2]]),
      sj.subs(U(I(0, yy), F(z)), new Map<sj.Expr, sj.ExprLike>([[yy, 2], [z, 3]])),
      sj.subs(sj.ProductSet(I(0, yy), A), [[yy, 1]]),
      sj.subs(sj.PowerSet(I(0, yy)), [[yy, 1]]),
      sj.subs(sj.DisjointUnion(I(0, yy)), [[yy, 1]]),
      sj.subs(Sets.symmetricDifference(I(0, yy), A, { evaluate: false }), [[yy, 1]]),
      sj.subs(Sets.intersection(I(0, yy), I(z, 1)), [[yy, 2]]),
      sj.subs(Sets.complement(I(0, yy), F(z)), [[z, 1]]),
      sj.subs(Sets.range(0, sj.oo, 2), [[yy, 1]]),
    ].map(String)).toEqual([
      'ConditionSet(x, x < y, Integers)',
      'ConditionSet(x, x < z, Integers)',
      'ConditionSet(x, x < y, Integers)',
      'ConditionSet(x, x < 3, Interval(0, 3))',
      'ConditionSet(x, x < y, {1, x})',
      'ConditionSet(x, x < 1, {y, z})',
      'ImageSet(Lambda(x, x**2 + 2), Interval(0, 2))',
      'ImageSet(Lambda(x, x**2), Interval(0, y))',
      'ImageSet(Lambda(x, x**2), Interval(0, 2))',
      'Interval(0, 2)',
      'Union({3}, Interval(0, 2))',
      'ProductSet(Interval(0, 1), {1, 2, 3})',
      'PowerSet(Interval(0, 1))',
      'DisjointUnion(Interval(0, 1))',
      'SymmetricDifference(Interval(0, 1), {1, 2, 3})',
      'Intersection(Interval(0, 2), Interval(z, 1))',
      // SymPy: Union(Intersection(Interval.open(-oo, 1), Interval(0, y)), Intersection(Interval(0, y), Interval.open(1, oo)))
      'Complement(Interval(0, y), {1})',
      'Range(0, oo, 2)',
    ]);
    // a set of another class rebuilds itself through withArgs
    expect(Sets.EmptySet.withArgs([])).toBe(Sets.EmptySet);
  });
});

describe('ConditionSet and imageset evaluation', () => {
  const p = (e: string) => sj.parse(e);
  const [yy, z, nn] = [sj.symbol('y'), sj.symbol('z'), sj.symbol('n')];
  const cs = (v: sj.Expr, c: string | boolean, b?: Sets.SetExpr) => sj.ConditionSet.of(v, typeof c === 'string' ? p(c) : c, b);
  const img = (e: string, b: Sets.SetExpr, v: sj.Expr = x) => sj.imageset(v, p(e), b);
  it('ConditionSet (SymPy ConditionSet.__new__)', () => {
    expect([
      cs(x, true, B()),
      cs(nn, false, Sets.Integers),
      cs(x, 'x > 1', Sets.EmptySet),
      cs(x, 'x > 1', F(0, 1, 2, 3)),
      cs(x, 'x > y', F(0, 3, z)),
      cs(x, 'x > 1', F(2, z)),
      cs(x, 'x < 1', cs(x, 'x > y', Sets.Integers)),
      cs(x, 'x < y', cs(z, 'z + y < 2', Sets.Integers)),
      cs(x, 'x < z', cs(z, 'z + x < 2', Sets.Integers)),
      cs(x, 'x < y + z', cs(z, 'z + x < 2', Sets.Integers)),
      sj.ConditionSet.of(x, new sj.Contains(x, I(0, 2)), I(1, 3)),
      sj.ConditionSet.of(x, p('x > 1')),
    ].map(String)).toEqual([
      'Interval(0, 5)',
      'EmptySet',
      'EmptySet',
      '{2, 3}',
      'ConditionSet(x, x > y, {0, 3, z})',
      'Union(ConditionSet(x, x > 1, {z}), {2})',
      'ConditionSet(x, (x > y) & (x < 1), Integers)',
      'ConditionSet(x, (x < y) & (x + y < 2), Integers)',
      'ConditionSet(x, x < z, ConditionSet(z, x + z < 2, Integers))',
      'ConditionSet(x, x < y + z, ConditionSet(z, x + z < 2, Integers))',
      'Interval(1, 2)',
      'ConditionSet(x, x > 1)',
    ]);
    // the merged inner variable is renamed when the outer condition is free of it
    expect(String(sj.ConditionSet.of(x, p('y < 1'), cs(z, 'z + x < 2', Sets.Integers)))).toBe('ConditionSet(z, (y < 1) & (x + z < 2), Integers)');
    const c = new sj.ConditionSet(x, p('x < 1'), Sets.Reals);
    expect([c.sym, c.baseSet].map(String)).toEqual(['x', 'Reals']);
  });
  it('imageset of finite sets, unions, intervals and compositions', () => {
    expect([
      img('x**2', F(-1, 1, 2)),
      img('x**2', Sets.EmptySet),
      img('2*x', U(I(0, 1), I(2, 3))),
      img('x', I(0, 1)),
      sj.imageset(yy, p('y + 1'), img('x**2', Sets.Naturals)),
      img('-3*x + 1', Sets.openInterval(0, 2)),
      img('x**2', I(1, sj.oo)),
      img('-x**3', I(sj.S.NegativeInfinity, 1)),
      img('x**2 - 2*x', Sets.Reals),
      img('x**2', Sets.openInterval(-1, 1)),
      img('x**3 - 3*x', I(-2, 3)),
      img('x**3 - 2*x', I(-1, 2)),
      img('x*y', I(0, 1)),
      img('3', I(0, 1)),
      img('sin(x)', I(0, 1)),
      img('x**2 + y', I(0, 1)),
      img('x**2', I(0, yy)),
      img('x**3 + x', I(0, 1)),
      img('x**6 + x**2 + x', I(0, 1)),
      img('y', I(0, yy)),
      img('3', Sets.Integers),
      img('x**2', Sets.Naturals),
      sj.imageset(p('2*x'), p('x'), I(0, 1)),
    ].map(String)).toEqual([
      '{1, 4}',
      'EmptySet',
      'Union(Interval(0, 2), Interval(4, 6))',
      'Interval(0, 1)',
      'ImageSet(Lambda(x, x**2 + 1), Naturals)',
      'Interval.open(-5, 1)',
      'Interval(1, oo)',
      'Interval(-1, oo)',
      'Interval(-1, oo)',
      'Interval.Ropen(0, 1)',
      'Interval(-2, 18)',
      'Interval(-4*sqrt(6)/9, 4)',
      'ImageSet(Lambda(x, x*y), Interval(0, 1))',
      '{3}',
      'ImageSet(Lambda(x, sin(x)), Interval(0, 1))',
      'ImageSet(Lambda(x, x**2 + y), Interval(0, 1))',
      'ImageSet(Lambda(x, x**2), Interval(0, y))',
      'Interval(0, 2)',
      // SymPy: Interval(0, 3); the critical points (roots of a quintic) are not known here
      'ImageSet(Lambda(x, x**6 + x**2 + x), Interval(0, 1))',
      'ImageSet(Lambda(x, y), Interval(0, y))',
      '{3}',
      'ImageSet(Lambda(x, x**2), Naturals)',
      'ImageSet(Lambda(2*x, x), Interval(0, 1))',
    ]);
  });
  it('imageset of the integers in canonical form (SymPy _set_function(Lambda, Integers))', () => {
    const z2 = (e: string) => img(e, Sets.Integers, nn);
    expect(['Abs(n)', 'n + 3', '-n + 1/2 + 2', '3*n + 7 + y', '2*n + 3*I', '2*I*n + 3 + 5*I', 'n**2', '2.0*n + 1', 'pi*n - pi/3', '-2*n + 5', 'n*y + 2', '2*n + I*y'].map((e) => String(z2(e)))).toEqual([
      'Naturals0',
      'Integers',
      'ImageSet(Lambda(n, n + 1/2), Integers)',
      'ImageSet(Lambda(n, 3*n + y + 7), Integers)',
      'ImageSet(Lambda(n, 2*n + 3*I), Integers)',
      'ImageSet(Lambda(n, 2*I*n + 3 + I), Integers)',
      'ImageSet(Lambda(n, n**2), Integers)',
      'ImageSet(Lambda(n, 2.0*n + 1), Integers)',
      'ImageSet(Lambda(n, pi*n + 2*pi/3), Integers)',
      'ImageSet(Lambda(n, 2*n + 1), Integers)',
      'ImageSet(Lambda(n, n*y + 2), Integers)',
      'ImageSet(Lambda(n, 2*n + I*y), Integers)',
    ]);
    expect(String((img('x**2', Sets.Naturals) as sj.ImageSet).lamda.call(2))).toBe('4');
    expect((img('x**2', Sets.Naturals) as sj.ImageSet).baseSets.map(String)).toEqual(['Naturals']);
  });
  it('intersections of ranges, image sets and intervals (SymPy intersection_sets)', () => {
    const R = (a: sj.ExprLike, b: sj.ExprLike, s: sj.ExprLike = 1) => Sets.range(a, b, s);
    const ninf = sj.S.NegativeInfinity;
    const X = Sets.intersection;
    expect([
      X(R(0, 10), Sets.Integers),
      X(R(-5, 5), Sets.Naturals),
      X(R(-5, 5), Sets.Naturals0),
      X(R(0, 20, 3), Sets.openInterval(3, 12)),
      X(R(0, 20), I(sj.pi, sj.mul(2, sj.pi))),
      X(R(0, sj.oo, 2), I(3, sj.oo)),
      X(R(ninf, 0), I(ninf, -3)),
      X(R(0, 3), I(4, sj.oo)),
      X(R(0, 10, 2), I(3, 7)),
      X(R(0, 30, 4), R(1, 40, 3)),
      X(R(0, sj.oo, 4), R(1, sj.oo, 3)),
      X(R(ninf, 0), R(ninf, 10, 3)),
      X(R(10, ninf, -2), R(0, sj.oo, 3)),
      X(R(0, 10, 2), R(1, 10, 2)),
      X(R(ninf, sj.oo), R(0, 10, 3)),
      X(R(0, 10, 3), R(ninf, sj.oo)),
      X(R(0, 10, 3), R(0, 0)),
      X(R(0, 30, 6), R(29, 0, -4)),
      X(R(0, 30, 6), R(25, 100, 10)),
      X(R(0, 3), R(4, sj.oo)),
      X(R(0, 5), Sets.Rationals),
      X(R(0, 5), I(0, x)),
      X(R(0, 5), I(0, sj.sqrt(2))),
      X(R(0, 5), F(x).isEmpty ? Sets.EmptySet : Sets.imageSet(x, p('x**2'), Sets.Integers)),
    ].map(String)).toEqual([
      'Range(0, 10, 1)',
      'Range(1, 5, 1)',
      'Range(0, 5, 1)',
      'Range(6, 12, 3)',
      'Range(4, 7, 1)',
      'Range(4, oo, 2)',
      'Range(-oo, -2, 1)',
      'EmptySet',
      'Range(4, 8, 2)',
      'Range(4, 40, 12)',
      'Range(4, oo, 12)',
      'Range(-oo, 1, 3)',
      'Range(0, 12, 6)',
      'EmptySet',
      'Range(0, 12, 3)',
      'Range(0, 12, 3)',
      'EmptySet',
      'EmptySet',
      'EmptySet',
      'EmptySet',
      'Range(0, 5, 1)',
      'Intersection(Interval(0, x), Range(0, 5, 1))',
      'Range(0, 2, 1)',
      'Intersection(ImageSet(Lambda(x, x**2), Integers), Range(0, 5, 1))',
    ]);
    const im = (e: string, b: Sets.SetExpr = Sets.Integers, v: sj.Expr = nn) => Sets.imageSet(v, p(e), b);
    const m = sj.symbol('m');
    expect([
      X(im('2*n'), im('3*m + 1', Sets.Integers, m)),
      X(im('n/2'), im('m/3', Sets.Integers, m)),
      X(im('2*n'), im('pi*m', Sets.Integers, m)),
      X(im('4*n + 2'), Sets.Integers),
      X(im('n/2 + 1/4'), Sets.Integers),
      X(im('-2*n + 1'), I(0, 10)),
      X(im('2*n'), Sets.Lopen(0, 3)),
      X(im('2*n', Sets.Naturals), I(0, 20)),
      X(im('2*n'), I(p('1/3'), p('1/2'))),
      X(im('n**2'), I(0, 10)),
      X(im('n*y'), I(0, 10)),
      X(im('2*n'), I(0, sj.oo)),
      X(im('2*n', I(0, 10)), I(0, 1)),
      X(im('n*y'), im('2*m', Sets.Integers, m)),
      X(im('2*n', Sets.Naturals), im('2*m', Sets.Integers, m)),
    ].map(String)).toEqual([
      'ImageSet(Lambda(n, 6*n + 4), Integers)',
      'Integers',
      'Intersection(ImageSet(Lambda(m, pi*m), Integers), ImageSet(Lambda(n, 2*n), Integers))',
      'ImageSet(Lambda(n, 4*n + 2), Integers)',
      'EmptySet',
      '{1, 3, 5, 7, 9}',
      '{2}',
      '{2, 4, 6, 8, 10, 12, 14, 16, 18, 20}',
      'EmptySet',
      'Intersection(ImageSet(Lambda(n, n**2), Integers), Interval(0, 10))',
      // SymPy: {0}, which holds only for y = 0 or |y| > 10
      'Intersection(ImageSet(Lambda(n, n*y), Integers), Interval(0, 10))',
      // SymPy: {0}; the even numbers 0, 2, 4, ... are all in [0, oo)
      'ImageSet(Lambda(n, 2*n), Range(0, oo, 1))',
      'Interval(0, 1)',
      'Intersection(ImageSet(Lambda(m, 2*m), Integers), ImageSet(Lambda(n, n*y), Integers))',
      'Intersection(ImageSet(Lambda(m, 2*m), Integers), ImageSet(Lambda(n, 2*n), Naturals))',
    ]);
    expect(String(X(I(-1, 1), im('pi*n')))).toBe('{0}');
  });
  function B(): Sets.SetExpr {
    return I(0, 5);
  }
  it('more branches of the handlers', () => {
    const z2 = (e: string) => String(img(e, Sets.Integers, nn));
    expect([z2('2*n + sqrt(1 + I)'), z2('n + y + 3'), z2('2*I*n + 3')]).toEqual(['ImageSet(Lambda(n, 2*n + sqrt(1 + I)), Integers)', 'ImageSet(Lambda(n, n + y), Integers)', 'ImageSet(Lambda(n, 2*I*n + 3), Integers)']);
    expect([img('3', I(0, yy)), img('x**3', Sets.Reals)].map(String)).toEqual(['ImageSet(Lambda(x, 3), Interval(0, y))', 'Reals']);
    expect(String(U(Sets.Rationals, I(0, 1)))).toBe('Union(Interval(0, 1), Rationals)');
    expect(String(U(sj.ProductSet(F(1, 2, 3), I(0, 5)), sj.ProductSet(F(1, 2, 3), I(7, 8))))).toBe('ProductSet({1, 2, 3}, Union(Interval(0, 5), Interval(7, 8)))');
    expect(String(Sets.intersection(I(0, 1), Sets.UniversalSet))).toBe('Interval(0, 1)');
    const R = (a: sj.ExprLike, b: sj.ExprLike, st: sj.ExprLike = 1) => Sets.range(a, b, st);
    const X = Sets.intersection;
    expect([X(R(1, 1), I(0, 1)), X(R(5, 20), R(0, 30, 3)), X(R(0, 10, 4), R(5, 7))].map(String)).toEqual(['EmptySet', 'Range(6, 21, 3)', 'EmptySet']);
    // SymPy: Range(0, 4, 1); the floor of a number equal to 0 that symjs does not evaluate
    expect(String(X(R(-5, 5), I(p('sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))'), 3)))).toBe('Intersection(Interval(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3), 3), Range(-5, 5, 1))');
    const im = (e: string, v: sj.Expr = nn) => Sets.imageSet(v, p(e), Sets.Integers);
    // SymPy: {0} for both, which leaves out 2, 4, ... and -2, -4, ... (the image of -2*n is that of 2*n)
    expect([X(im('-2*n'), I(0, sj.oo)), X(im('2*n'), I(sj.S.NegativeInfinity, 0))].map(String)).toEqual(['ImageSet(Lambda(n, 2*n), Range(0, oo, 1))', 'ImageSet(Lambda(n, 2*n), Range(-oo, 1, 1))']);
    expect(String(X(new Sets.ImageSet(nn, p('-2*n'), Sets.Integers), I(0, sj.oo)))).toBe('ImageSet(Lambda(n, -2*n), Range(-oo, 1, 1))');
    expect(String(X(Sets.imageSet(p('2*x'), x, Sets.Integers), I(0, 1)))).toBe('Intersection(ImageSet(Lambda(2*x, x), Integers), Interval(0, 1))');
    expect([Sets.isSubset(Sets.Rationals, Sets.Complexes), Sets.isSubset(Sets.Rationals, Sets.Integers)]).toEqual([true, undefined]);
    expect([sj.xreplace(R(0, 5), [[sj.S.Zero, sj.S.One]]), sj.xreplace(sj.ConditionSet.of(x, p('x < y'), Sets.Integers), [[yy, 2]])].map(String)).toEqual(['Range(1, 5, 1)', 'ConditionSet(x, x < 2, Integers)']);
  });
});
describe('Range with symbolic bounds (SymPy 1.14 Range)', () => {
  const nn = new sj.Sym('n');
  const [a, b, c] = [new sj.Sym('a'), new sj.Sym('b'), new sj.Sym('c')];
  const i = new sj.Sym('i', { integer: true });
  const k = new sj.Sym('k', { integer: true, positive: true });
  const x = new sj.Sym('x');
  const R = (start: sj.ExprLike, stop?: sj.ExprLike, step?: sj.ExprLike): Sets.Range => {
    const r = Sets.Range.of(start, stop, step);
    if (!(r instanceof Sets.Range)) throw new TypeError('not a Range');
    return r;
  };
  const S = (f: () => unknown): string => {
    try {
      return String(f());
    } catch (e) {
      return `${(e as Error).constructor.name}: ${(e as Error).message}`;
    }
  };
  const L = (s: Sets.SetExpr): string => sj.latex(s);

  it('construction', () => {
    // SymPy Range(n), Range(0, n), Range(a, b, 2), Range(a, b, c)
    expect([R(nn), R(0, nn), R(a, b, 2), R(a, b, c)].map(String)).toEqual(['Range(0, n, 1)', 'Range(0, n, 1)', 'Range(a, b, 2)', 'Range(a, b, c)']);
    // a rational count: the stop is canonical (SymPy Range(i, i + 5, 2), Range(i, i + 5, -2), Range(i, i - 5, -2))
    expect(String(R(i, sj.add(i, 5), 2))).toBe('Range(i, i + 6, 2)');
    expect(String(R(i, sj.add(i, 5), -2))).toBe('Range(i, i + 6, -2)');
    expect(String(R(i, sj.add(i, -5), -2))).toBe('Range(i, i - 4, -2)');
    expect(String(R(i, sj.add(i, -3)))).toBe('Range(i, i - 3, 1)');
    // a symbolic rational count: SymPy Range(i, 3*i, i), Range(k, 3*k, k), Range(2*k, k, -k)
    expect(String(R(i, sj.mul(3, i), i))).toBe('Range(i, 3*i, i)');
    expect(String(R(k, sj.mul(3, k), k))).toBe('Range(k, 3*k, k)');
    expect(String(R(sj.mul(2, k), k, sj.neg(k)))).toBe('Range(2*k, k, -k)');
    // empty: SymPy Range(i, i), Range(k, 0)
    expect(String(R(i, i))).toBe('Range(0, 0, 1)');
    expect(String(R(k, 0))).toBe('Range(0, 0, 1)');
    // SymPy Range(k, 4*k, 2*k) = Range(k, 5*k, 2*k); Range(i, -oo) and Range(-oo, i, -1) are empty
    expect(String(R(k, sj.mul(4, k), sj.mul(2, k)))).toBe('Range(k, 5*k, 2*k)');
    expect([R(i, sj.neg(sj.oo)), R(sj.neg(sj.oo), i, -1)].map(String)).toEqual(['Range(0, 0, 1)', 'Range(0, 0, 1)']);
    expect(String(R(i, sj.neg(sj.oo), -1).size)).toBe('oo');
    // a symbol that is not an integer (SymPy ValueError)
    expect(() => R(new sj.Sym('y', { integer: false }))).toThrow(TypeError);
  });

  it('construction with infinite ends and steps (SymPy)', () => {
    // SymPy Range(-oo, 5, -1), Range(oo, 1): empty; Range(-oo, oo, 2): ValueError
    expect(String(R(sj.neg(sj.oo), 5, -1))).toBe('Range(0, 0, 1)');
    expect(String(R(sj.oo, 1))).toBe('Range(0, 0, 1)');
    expect(() => R(sj.neg(sj.oo), sj.oo, 2)).toThrow('step size must be 1 in this case');
    expect(() => R(sj.oo, sj.neg(sj.oo), -2)).toThrow('step size must be -1 in this case');
    // an infinite step: SymPy Range(0, 10, oo) = Range(0, -10, -oo) = Range(0, 1, 1); Range(10, 0, oo) is empty
    expect([R(0, 10, sj.oo), R(0, -10, sj.neg(sj.oo)), R(10, 0, sj.oo)].map(String)).toEqual(['Range(0, 1, 1)', 'Range(0, 1, 1)', 'Range(0, 0, 1)']);
  });

  it('size, inf, sup, is_empty and is_finite_set', () => {
    // SymPy Range(k): size k, inf 0, sup k - 1, is_empty False
    const rk = R(k);
    expect([rk.size, Sets.inf(rk), Sets.sup(rk)].map(String)).toEqual(['k', '0', 'k - 1']);
    expect([rk.isEmptyQ, rk.isFiniteSet]).toEqual([false, true]);
    // SymPy Range(1, k): size k - 1, inf raises (it may be empty)
    expect(String(R(1, k).size)).toBe('k - 1');
    expect(S(() => Sets.inf(R(1, k)))).toBe('RangeError: cannot tell if Range is null or not');
    expect(R(1, k).isEmptyQ).toBe('unknown');
    // SymPy Range(n): size, inf and sup raise, is_empty None
    expect(S(() => R(nn).size)).toBe('RangeError: Invalid method for symbolic Range');
    expect(S(() => Sets.sup(R(nn)))).toBe('RangeError: cannot tell if Range is null or not');
    expect(R(nn).isEmptyQ).toBe('unknown');
    expect(S(() => R(nn).isFiniteSet)).toBe('RangeError: Invalid method for symbolic Range');
    expect(R(i).isFiniteSet).toBe(true);
    // SymPy Range(i, i + 6, 2): size 3, inf i, sup i + 4; Range(i, 3*i, i): size 2, inf raises
    const r6 = R(i, sj.add(i, 5), 2);
    expect([r6.size, Sets.inf(r6), Sets.sup(r6)].map(String)).toEqual(['3', 'i', 'i + 4']);
    expect(String(R(i, sj.mul(3, i), i).size)).toBe('2');
    expect(S(() => Sets.inf(R(i, sj.mul(3, i), i)))).toBe('RangeError: cannot tell if Range is null or not');
    // a negative step: SymPy Range(i + 4, i - 2, -2) has inf i - 2 + 2 = i... (sup i + 4, inf i)
    const neg = R(sj.add(i, 4), sj.add(i, -2), -2);
    expect([Sets.inf(neg), Sets.sup(neg)].map(String)).toEqual(['i', 'i + 4']);
    // SymPy Range(n, n + 3).inf: invalid method (n may not be an integer)
    expect(S(() => Sets.inf(R(nn, sj.add(nn, 3))))).toBe('RangeError: invalid method for symbolic range');
    // SymPy Range(i, i - 3): inf raises (invalid method)
    expect(S(() => Sets.inf(R(i, sj.add(i, -3))))).toBe('RangeError: invalid method for symbolic range');
    // infinite: SymPy Range(i, oo).size = Range(-oo, i).size = oo, is_finite_set False
    expect([R(i, sj.oo).size, R(sj.neg(sj.oo), i).size].map(String)).toEqual(['oo', 'oo']);
    expect([R(i, sj.oo).isFiniteSet, R(i, sj.oo).isEmptyQ]).toEqual([false, false]);
    // SymPy Range(0).inf: NotImplementedError
    expect(S(() => Sets.inf(R(0)))).toBe('NotImplementedError: (EmptySet)._inf');
    expect(S(() => Sets.sup(R(0)))).toBe('NotImplementedError: (EmptySet)._sup');
    expect(String(R(0).size)).toBe('0');
    expect(R(0).isEmptyQ).toBe(true);
    // a numeric Range with a negative step
    expect([Sets.inf(R(5, 0, -2)), Sets.sup(R(5, 0, -2))].map(String)).toEqual(['1', '5']);
  });

  it('elements and reversed', () => {
    const r6 = R(i, sj.add(i, 5), 2);
    // SymPy r[1], r[2], r[-2], r[-4] (IndexError); SymPy gives i + 6 for r[3], which is not an
    // element (the size is 3), so here it is an IndexError too
    expect([r6.at(0), r6.at(1), r6.at(2), r6.at(-1), r6.at(-2)].map(String)).toEqual(['i', 'i + 2', 'i + 4', 'i + 4', 'i + 2']);
    expect(S(() => r6.at(3))).toBe('RangeError: Range index out of range');
    expect(S(() => r6.at(-4))).toBe('RangeError: Range index out of range');
    expect(S(() => R(nn).at(0))).toBe('RangeError: Invalid method for symbolic Range');
    expect(S(() => R(0).at(0))).toBe('RangeError: Range index out of range');
    expect(S(() => R(sj.neg(sj.oo), i).at(0))).toBe('RangeError: cannot slice from the end with an infinite value');
    expect(S(() => R(i, sj.oo).at(-1))).toBe('RangeError: cannot slice from the end with an infinite value');
    // SymPy Range(-oo, i)[-3] = i - 3
    expect(String(R(sj.neg(sj.oo), i).at(-3))).toBe('i - 3');
    expect(S(() => R(0, sj.oo).at(-2))).toBe('RangeError: cannot slice from the end with an infinite value');
    // SymPy raises an IndexError for Range(i, oo)[2], although i + 2 is the element of index 2
    expect(String(R(i, sj.oo).at(2))).toBe('i + 2');
    // an index that depends on the unknown size: SymPy Range(k)[1] = 1 (k > 1 is not known: it raises)
    expect(S(() => R(k).at(1))).toBe('RangeError: Invalid method for symbolic Range');
    // SymPy Range(i, i + 6, 2).reversed, Range(k).reversed, Range(-oo, i).reversed, Range(n).reversed (raises)
    expect([r6.reversed, R(k).reversed, R(sj.neg(sj.oo), i).reversed].map(String)).toEqual(['Range(i + 4, i - 2, -2)', 'Range(k - 1, -1, -1)', 'Range(i - 1, -oo, -1)']);
    expect(S(() => R(nn).reversed)).toBe('RangeError: invalid method for symbolic range');
    expect(R(0).reversed.isEmpty).toBe(true);
    expect(String(R(3).reversed)).toBe('Range(2, -1, -1)');
  });

  it('contains (SymPy Range._contains)', () => {
    const vals = [i, sj.Rational.of(1n, 2n), 3, x, -1];
    const row = (r: Sets.SetExpr): string[] => vals.map((v) => String(C(r, v)));
    expect(row(R(nn))).toEqual(['Contains(i, Range(0, n, 1))', 'False', 'Contains(3, Range(0, n, 1))', 'Contains(x, Range(0, n, 1))', 'Contains(-1, Range(0, n, 1))']);
    expect(row(R(k))).toEqual(['(i >= 0) & (i <= k - 1)', 'False', '3 <= k - 1', 'Contains(x, Range(0, k, 1))', 'False']);
    expect(row(R(i, sj.add(i, 5), 2))).toEqual(['True', 'False', 'Contains(3, Range(i, i + 6, 2))', 'Contains(x, Range(i, i + 6, 2))', 'Contains(-1, Range(i, i + 6, 2))']);
    expect(String(C(R(i, sj.mul(3, i), i), i))).toBe('((i >= 1) & (i <= 2*i)) | ((i <= -1) & (i >= 2*i))');
    expect(row(R(i, sj.oo))).toEqual(['True', 'False', '3 >= i', 'Contains(x, Range(i, oo, 1))', '-1 >= i']);
    expect(row(R(sj.neg(sj.oo), i))).toEqual(['False', 'False', '3 <= i - 1', 'Contains(x, Range(-oo, i, 1))', '-1 <= i - 1']);
    // SymPy Range(i, i + 2, 2).contains(3) = Eq(3, i); Range(i, i + 6, 2).contains(i + 1) = False; oo is not an element
    expect(String(C(R(i, sj.add(i, 2), 2), 3))).toBe('Eq(3, i)');
    expect(String(C(R(i, sj.add(i, 6), 2), sj.add(i, 1)))).toBe('False');
    expect(String(C(R(i, sj.add(i, 6), 2), sj.oo))).toBe('False');
    // SymPy Range(-oo, oo).contains(i) = True, Range(0, 10, 3).contains(4) = False
    expect(String(C(R(sj.neg(sj.oo), sj.oo), i))).toBe('True');
    expect(String(C(R(0, 10, 3), 4))).toBe('False');
    expect(Sets.containsQ(R(k), sj.sympify(-1))).toBe(false);
  });

  it('as_relational (SymPy)', () => {
    expect(String(Sets.asRelational(R(k), x))).toBe('(x >= 0) & Eq(Mod(x, 1), 0) & (x <= k - 1)');
    expect(String(Sets.asRelational(R(i, sj.add(i, 6), 2), x))).toBe('(x >= i) & (x <= i + 4) & Eq(Mod(-i + x, 2), 0)');
    // SymPy (x > -oo) & Eq(Mod(x, 1), 0) & (x <= i - 1): Mod(x - i + 1, 1) is not reduced to Mod(x, 1) here
    expect(String(Sets.asRelational(R(sj.neg(sj.oo), i), x))).toBe('(x > -oo) & (x <= i - 1) & Eq(Mod(-i + x + 1, 1), 0)');
    // SymPy Eq(Mod(x, i), 0) & ...: Mod(x - i, i) is not reduced here
    expect(String(Sets.asRelational(R(i, sj.mul(3, i), i), x))).toBe('Eq(Mod(-i + x, i), 0) & (((i >= 1) & (x >= i) & (x <= 2*i)) | ((i <= -1) & (x <= i) & (x >= 2*i)))');
    expect(String(Sets.asRelational(R(i, sj.add(i, 2), 2), x))).toBe('Eq(x, i)');
    expect(String(Sets.asRelational(R(0), x))).toBe('False');
    // SymPy Range(0, oo).as_relational(x) = (x >= 0) & (x < oo) & Eq(Mod(x, 1), 0)
    expect(String(Sets.asRelational(R(0, sj.oo), x))).toBe('(x >= 0) & (x < oo) & Eq(Mod(x, 1), 0)');
  });

  it('intersections stay unevaluated (SymPy)', () => {
    expect(String(Sets.intersection(R(nn), I(0, 5)))).toBe('Intersection(Interval(0, 5), Range(0, n, 1))');
    expect(String(Sets.intersection(R(nn), R(3)))).toBe('Intersection(Range(0, 3, 1), Range(0, n, 1))');
    expect(String(Sets.intersection(R(3), R(nn)))).toBe('Intersection(Range(0, 3, 1), Range(0, n, 1))');
    expect(String(Sets.intersection(R(nn), Sets.Integers))).toBe('Range(0, n, 1)');
  });

  it('printing (SymPy str, latex and pretty)', () => {
    expect(L(R(nn))).toBe('\\text{Range}\\left(n\\right)');
    expect(L(R(a, b, 2))).toBe('\\text{Range}\\left(a, b, 2\\right)');
    expect(L(R(1, nn, 2))).toBe('\\text{Range}\\left(1, n, 2\\right)');
    expect(L(R(0, nn, 2))).toBe('\\text{Range}\\left(0, n, 2\\right)');
    expect(L(R(1, k))).toBe('\\text{Range}\\left(1, k\\right)');
    expect(L(R(k))).toBe('\\text{Range}\\left(k\\right)');
    expect(L(R(i, sj.add(i, -3)))).toBe('\\text{Range}\\left(i, i - 3\\right)');
    expect(L(R(i, sj.add(i, 5), 2))).toBe('\\left\\{i, i + 2, i + 4\\right\\}');
    expect(L(R(i, sj.mul(3, i), i))).toBe('\\left\\{i, 2 i\\right\\}');
    expect(L(R(i, sj.add(i, 8), 2))).toBe('\\left\\{i, i + 2, \\ldots, i + 6\\right\\}');
    expect(L(R(i, sj.oo))).toBe('\\left\\{i, i + 1, \\ldots\\right\\}');
    expect(L(R(sj.neg(sj.oo), i))).toBe('\\left\\{\\ldots, i - 2, i - 1\\right\\}');
    expect(sj.pretty(R(i, sj.add(i, 8), 2))).toBe('{i, i + 2, i + 4, i + 6}');
    expect(sj.pretty(R(i, sj.add(i, 10), 2))).toBe('{i, i + 2, …, i + 8}');
    expect(sj.pretty(R(i, sj.mul(3, i), i), { useUnicode: false })).toBe('{i, 2*i}');
    expect(sj.pretty(R(sj.neg(sj.oo), i), { useUnicode: false })).toBe('{..., i - 2, i - 1}');
    // SymPy's pretty printer and its LaTeX printer for Range(-oo, n) and Range(n, oo) raise; the
    // function form of the LaTeX printer is shown
    expect(sj.pretty(R(nn))).toBe('Range(n)');
    expect(sj.pretty(R(a, b, 2))).toBe('Range(a, b, 2)');
    expect(L(R(sj.neg(sj.oo), nn))).toBe('\\text{Range}\\left(-\\infty, n\\right)');
    expect(L(R(nn, sj.oo))).toBe('\\text{Range}\\left(n, \\infty\\right)');
    expect(String(R(nn))).toBe('Range(0, n, 1)');
  });
});
