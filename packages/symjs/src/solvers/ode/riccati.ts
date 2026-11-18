// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Rational Riccati coefficient construction, ported from SymPy's ode/riccati.py. */
import { Add, Derivative, type Expr, Float, Rel, S, type Sym, type UndefFn } from '../../core/nodes';
import { at } from '../../core/guard';
import { add, mul, neg, pow, sqrt, sub } from '../../core/ops';
import { coeff, isRationalFunction } from '../../core/methods';
import { freeSymbols, subs } from '../../core/traverse';
import { expand } from '../../simplify/expand';
import { cancel } from '../../simplify/rational';
import { Poly } from '../../polys/sympoly';
import { sign } from '../../functions/special/special';

/** Match w' = b0 + b1*w + b2*w² with rational coefficients. */
export function matchRiccati(eq: Expr, f: UndefFn, x: Sym): [boolean, Expr[]] {
  let e = expand(eq instanceof Rel ? sub(eq.lhs, eq.rhs) : eq);
  const derivative = new Derivative([f, x, S.One]);
  const cf = coeff(e, derivative);
  if (cf.equals(S.Zero) || !(e instanceof Add)) return [false, []];
  e = expand(add(...e.args.map((term) => cancel(mul(term, pow(cf, -1))))));
  const b1 = neg(coeff(e, f));
  const b2 = neg(coeff(e, pow(f, 2)));
  const b0 = expand(sub(sub(sub(derivative, mul(b1, f)), mul(b2, pow(f, 2))), e));
  const values = [b0, b1, b2];
  const hasFloat = (v: Expr): boolean => v instanceof Float || v.args.some(hasFloat);
  if (values.some((v) => freeSymbols(v).size > 1 || hasFloat(v)) || b2.equals(S.Zero)
      || values.some((v) => v.has(f) || !isRationalFunction(v, [x]))) return [false, []];
  return [true, values];
}

/** Valuation of num/den at infinity. */
export function valAtInf(num: Poly, den: Poly, x: Sym): number {
  return den.degree(x) - num.degree(x);
}

/** Necessary pole multiplicities for a rational Riccati solution. */
export function checkNecessaryConds(valInf: number, muls: readonly number[]): boolean {
  return (valInf >= 2 || (valInf <= 0 && valInf % 2 === 0))
    && muls.every((m) => m === 1 || (m >= 2 && m % 2 === 0));
}

/** Limit of a rational function at positive infinity. */
export function limitAtInf(num: Poly, den: Poly, x: Sym): Expr {
  const valuation = valAtInf(num, den, x);
  const ratio = mul(num.LC(), pow(den.LC(), -1));
  if (valuation < 0) return mul(S.Infinity, sign(ratio));
  return valuation === 0 ? ratio : S.Zero;
}

/** Coefficients after the substitution x -> 1/x. */
export function inverseTransformPoly(num: Poly, den: Poly, x: Sym): [Poly, Poly] {
  const degree = Math.max(num.degree(x), den.degree(x));
  const transform = (p: Poly): Poly => Poly.from(expand(mul(pow(x, degree), subs(p.asExpr(), [[x, pow(x, -1)]]))), [x]);
  const n = transform(num), d = transform(den);
  const gcd = n.gcd(d);
  return [n.exquo(gcd), d.exquo(gcd)];
}

/** Laurent coefficients indexed by descending powers of the local reciprocal variable. */
export function rationalLaurentSeries(numIn: Poly, denIn: Poly, x: Sym, rIn: Expr, m: number, n: number): Map<number, Expr> {
  let num = numIn, den = denIn, r = rIn;
  if (r.equals(S.Infinity)) {
    [num, den] = inverseTransformPoly(num, den, x);
    r = S.Zero;
  }
  const shift = (p: Poly): Poly => Poly.from(expand(subs(p.asExpr(), [[x, add(x, r)]])), [x]);
  num = shift(num); den = shift(den);
  const numerator = Poly.from(mul(num.asExpr(), pow(x, m)), [x]);
  const gcd = numerator.gcd(den);
  num = numerator.exquo(gcd); den = den.exquo(gcd);
  const count = Math.max(n, 1 + num.degree(), 1 + den.degree());
  const series: Expr[] = [];
  for (let i = 0; i < count; i++) {
    const convolution = add(...Array.from({ length: Math.min(i, den.degree()) }, (_, j) => mul(den.nth(j + 1), at(series, i - j - 1))));
    series.push(cancel(mul(sub(num.nth(i), convolution), pow(den.nth(0), -1))));
  }
  return new Map(series.map((value, i) => [m - i, value]));
}

const coefficient = (series: ReadonlyMap<number, Expr>, i: number): Expr => series.get(i) ?? S.Zero;
const divideTwice = (a: Expr, b: Expr): Expr => mul(a, pow(mul(2, b), -1));
const quadraticChoices = (r: Expr): Expr[][] => {
  const root = sqrt(add(1, mul(4, r)));
  const plus = mul(add(1, root), S.Half);
  return root.equals(S.Zero) ? [[plus]] : [[plus], [mul(sub(1, root), S.Half)]];
};

/** Residues at a double pole. */
export function constructCCase1(num: Poly, den: Poly, x: Sym, pole: Expr): Expr[][] {
  return quadraticChoices(coefficient(rationalLaurentSeries(num, den, x, pole, 2, 1), 2));
}

/** Principal parts at a pole of even multiplicity greater than two. */
export function constructCCase2(num: Poly, den: Poly, x: Sym, pole: Expr, multiplicity: number): Expr[][] {
  const ri = Math.floor(multiplicity / 2);
  const series = rationalLaurentSeries(num, den, x, pole, multiplicity, 6);
  const plus: Expr[] = Array.from({ length: ri }, () => S.Zero);
  const root = sqrt(coefficient(series, 2 * ri));
  plus[ri - 1] = root;
  let sum: Expr = S.Zero;
  for (let s = ri - 1; s > 0; s--) {
    sum = add(...Array.from({ length: ri - s - 1 }, (_, k) => {
      const j = s + k + 1;
      return mul(at(plus, j - 1), at(plus, ri + s - j - 1));
    }));
    if (s !== 1) plus[s - 1] = divideTwice(sub(coefficient(series, ri + s), sum), root);
  }
  const minus = plus.map(neg);
  plus[0] = divideTwice(sub(sub(coefficient(series, ri + Math.min(1, ri - 1)), sum), mul(ri, root)), root);
  minus[0] = divideTwice(sub(sub(coefficient(series, ri + Math.min(1, ri - 1)), sum), mul(-ri, root)), neg(root));
  return [plus, minus];
}

/** A simple pole has residue one. */
export function constructCCase3(): Expr[][] { return [[S.One]]; }

/** All principal-part choices, one entry per finite pole. */
export function constructC(num: Poly, den: Poly, x: Sym, poles: readonly Expr[], muls: readonly number[]): Expr[][][] {
  return poles.map((pole, i) => {
    const m = at(muls, i);
    return m === 1 ? constructCCase3() : m === 2 ? constructCCase1(num, den, x, pole) : constructCCase2(num, den, x, pole, m);
  });
}

/** Polynomial parts for a pole at infinity of order 2*N. */
export function constructDCase4(series: ReadonlyMap<number, Expr>, N: number): Expr[][] {
  const plus: Expr[] = Array.from({ length: N + 2 }, () => S.Zero);
  const root = sqrt(coefficient(series, 2 * N));
  plus[N] = root;
  let sum: Expr = S.Zero;
  for (let s = N - 1; s >= -1; s--) {
    sum = add(...Array.from({ length: N - s - 1 }, (_, k) => {
      const j = s + k + 1;
      return mul(at(plus, j), at(plus, N + s - j));
    }));
    if (s !== -1) plus[s] = divideTwice(sub(coefficient(series, N + s), sum), root);
  }
  const minus = plus.map(neg);
  plus[N + 1] = divideTwice(sub(sub(coefficient(series, N - 1), mul(N, root)), sum), root);
  minus[N + 1] = divideTwice(sub(sub(coefficient(series, N - 1), mul(-N, root)), sum), neg(root));
  return [plus, minus];
}

/** Constant polynomial parts and their residues at infinity. */
export function constructDCase5(series: ReadonlyMap<number, Expr>): Expr[][] {
  const root = sqrt(coefficient(series, 0));
  const plus = [root, divideTwice(coefficient(series, -1), root)];
  return [plus, plus.map(neg)];
}

/** Residues when the rational function vanishes at infinity. */
export function constructDCase6(num: Poly, den: Poly, x: Sym): Expr[][] {
  return quadraticChoices(limitAtInf(Poly.from(mul(pow(x, 2), num.asExpr()), [x]), den, x));
}

/** Polynomial-part choices at infinity. */
export function constructD(num: Poly, den: Poly, x: Sym, valInf: number): Expr[][] {
  if (valInf > 0) return constructDCase6(num, den, x);
  const series = rationalLaurentSeries(num, den, x, S.Infinity, Math.max(0, -valInf), 1);
  return valInf < 0 ? constructDCase4(series, -valInf / 2) : constructDCase5(series);
}
