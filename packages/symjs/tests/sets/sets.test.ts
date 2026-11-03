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
