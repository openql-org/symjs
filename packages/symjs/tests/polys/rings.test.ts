// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/rings.ts: sparse polynomial rings; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { EX, QQ, RR, ZZ } from '../../src/polys/domains';
import { grlex, lex } from '../../src/polys/orderings';
import { PolyElement, PolyRing, ring, sring, vring, xring } from '../../src/polys/rings';

/** Python's str of a value (lists for tuples, -oo for the degree of zero). */
function show(v: unknown): string {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v === -Infinity) return '-oo';
  if (v instanceof sj.Expr) return sj.str(v);
  return String(v);
}

const [R, x, y] = ring('x,y', ZZ) as [PolyRing, PolyElement, PolyElement];
const [Q, a, b] = ring('a,b', QQ) as [PolyRing, PolyElement, PolyElement];
const [U, t] = ring('t', ZZ) as [PolyRing, PolyElement];
const [, s] = ring('s', QQ) as [PolyRing, PolyElement];
const [G, gx, gy] = ring('x,y', ZZ, grlex) as [PolyRing, PolyElement, PolyElement];
const [, e] = ring('e', EX) as [PolyRing, PolyElement];
const [, fz] = ring('z', RR) as [PolyRing, PolyElement];
const [P, px, py] = ring('x,y', 'ZZ[w]') as [PolyRing, PolyElement, PolyElement];
const w = sj.symbols('w')[0];
void [Q, U, G, P, py, xring, sring, vring, lex];

describe('SymPy doctest and suite values', () => {
  it("R", () => {
    expect(show(R)).toBe("Polynomial ring in x, y over ZZ with lex order");
  });
  it("G", () => {
    expect(show(G)).toBe("Polynomial ring in x, y over ZZ with grlex order");
  });
  it("x.pow(2).mul(y).sub(x.mul(y.pow(2)).mulGround(3)).add(5)", () => {
    expect(show(x.pow(2).mul(y).sub(x.mul(y.pow(2)).mulGround(3)).add(5))).toBe("x**2*y - 3*x*y**2 + 5");
  });
  it("x.neg().sub(1)", () => {
    expect(show(x.neg().sub(1))).toBe("-x - 1");
  });
  it("R.zero", () => {
    expect(show(R.zero)).toBe("0");
  });
  it("R.groundNew(-3)", () => {
    expect(show(R.groundNew(-3))).toBe("-3");
  });
  it("a.pow(2).mulGround(sj.Rational.of(-1, 2)).sub(sj.Rational.of", () => {
    expect(show(a.pow(2).mulGround(sj.Rational.of(-1, 2)).sub(sj.Rational.of(3, 2)))).toBe("-1/2*a**2 - 3/2");
  });
  it("x.add(y).pow(5)", () => {
    expect(show(x.add(y).pow(5))).toBe("x**5 + 5*x**4*y + 10*x**3*y**2 + 10*x**2*y**3 + 5*x*y**4 + y**5");
  });
  it("x.add(y).add(1).pow(4)", () => {
    expect(show(x.add(y).add(1).pow(4))).toBe("x**4 + 4*x**3*y + 4*x**3 + 6*x**2*y**2 + 12*x**2*y + 6*x**2 + 4*x*y**3 + 12*x*y**2 + 12*x*y + 4*x + y**4 + 4*y**3 + 6*y**2 + 4*y + 1");
  });
  it("x.add(y).add(1).add(x.mul(y)).add(x.pow(2)).add(y.pow(2)).po", () => {
    expect(show(x.add(y).add(1).add(x.mul(y)).add(x.pow(2)).add(y.pow(2)).pow(6))).toBe("x**12 + 6*x**11*y + 6*x**11 + 21*x**10*y**2 + 36*x**10*y + 21*x**10 + 50*x**9*y**3 + 120*x**9*y**2 + 120*x**9*y + 50*x**9 + 90*x**8*y**4 + 270*x**8*y**3 + 375*x**8*y**2 + 270*x**8*y + 90*x**8 + 126*x**7*y**5 + 450*x**7*y**4 + 780*x**7*y**3 + 780*x**7*y**2 + 450*x**7*y + 126*x**7 + 141*x**6*y**6 + 576*x**6*y**5 + 1185*x**6*y**4 + 1480*x**6*y**3 + 1185*x**6*y**2 + 576*x**6*y + 141*x**6 + 126*x**5*y**7 + 576*x**5*y**6 + 1356*x**5*y**5 + 2010*x**5*y**4 + 2010*x**5*y**3 + 1356*x**5*y**2 + 576*x**5*y + 126*x**5 + 90*x**4*y**8 + 450*x**4*y**7 + 1185*x**4*y**6 + 2010*x**4*y**5 + 2385*x**4*y**4 + 2010*x**4*y**3 + 1185*x**4*y**2 + 450*x**4*y + 90*x**4 + 50*x**3*y**9 + 270*x**3*y**8 + 780*x**3*y**7 + 1480*x**3*y**6 + 2010*x**3*y**5 + 2010*x**3*y**4 + 1480*x**3*y**3 + 780*x**3*y**2 + 270*x**3*y + 50*x**3 + 21*x**2*y**10 + 120*x**2*y**9 + 375*x**2*y**8 + 780*x**2*y**7 + 1185*x**2*y**6 + 1356*x**2*y**5 + 1185*x**2*y**4 + 780*x**2*y**3 + 375*x**2*y**2 + 120*x**2*y + 21*x**2 + 6*x*y**11 + 36*x*y**10 + 120*x*y**9 + 270*x*y**8 + 450*x*y**7 + 576*x*y**6 + 576*x*y**5 + 450*x*y**4 + 270*x*y**3 + 120*x*y**2 + 36*x*y + 6*x + y**12 + 6*y**11 + 21*y**10 + 50*y**9 + 90*y**8 + 126*y**7 + 141*y**6 + 126*y**5 + 90*y**4 + 50*y**3 + 21*y**2 + 6*y + 1");
  });
  it("x.mulGround(2).pow(3)", () => {
    expect(show(x.mulGround(2).pow(3))).toBe("8*x**3");
  });
  it("x.add(y).pow(0)", () => {
    expect(show(x.add(y).pow(0))).toBe("1");
  });
  it("x.add(y).pow(1)", () => {
    expect(show(x.add(y).pow(1))).toBe("x + y");
  });
  it("e.mulGround(sj.sqrt(2)).sub(sj.sqrt(3))", () => {
    expect(show(e.mulGround(sj.sqrt(2)).sub(sj.sqrt(3)))).toBe("EX(sqrt(2))*e - EX(-sqrt(3))");
  });
  it("fz.mulGround(1.5).sub(2.25)", () => {
    expect(show(fz.mulGround(1.5).sub(2.25))).toBe("1.5*z - 2.25");
  });
  it("px.mulGround(sj.neg(w))", () => {
    expect(show(px.mulGround(sj.neg(w)))).toBe("-w*x");
  });
  it("x.pow(2).add(x.mul(y)).div(x.mulGround(2).add(2))", () => {
    expect(show(x.pow(2).add(x.mul(y)).div(x.mulGround(2).add(2)))).toBe("[0, x**2 + x*y]");
  });
  it("a.pow(2).add(a.mul(b)).div(a.mulGround(2).add(2))", () => {
    expect(show(a.pow(2).add(a.mul(b)).div(a.mulGround(2).add(2)))).toBe("[1/2*a + 1/2*b - 1/2, -b + 1]");
  });
  it("x.pow(2).mul(y).add(x.mul(y.pow(2))).add(y.pow(2)).div([x.mu", () => {
    expect(show(x.pow(2).mul(y).add(x.mul(y.pow(2))).add(y.pow(2)).div([x.mul(y).sub(1), y.pow(2).sub(1)]))).toBe("[[x + y, 1], x + y + 1]");
  });
  it("x.pow(2).mul(y).add(x.mul(y.pow(2))).add(y.pow(2)).rem([x.mu", () => {
    expect(show(x.pow(2).mul(y).add(x.mul(y.pow(2))).add(y.pow(2)).rem([x.mul(y).sub(1), y.pow(2).sub(1)]))).toBe("x + y + 1");
  });
  it("x.pow(2).sub(1).quo(x.sub(1))", () => {
    expect(show(x.pow(2).sub(1).quo(x.sub(1)))).toBe("x + 1");
  });
  it("x.pow(2).sub(1).quo([x.sub(1)])", () => {
    expect(show(x.pow(2).sub(1).quo([x.sub(1)]))).toBe("[x + 1]");
  });
  it("x.pow(2).sub(1).exquo(x.sub(1))", () => {
    expect(show(x.pow(2).sub(1).exquo(x.sub(1)))).toBe("x + 1");
  });
  it("x.pow(2).add(3).divmod(x)", () => {
    expect(show(x.pow(2).add(3).divmod(x))).toBe("[x, 3]");
  });
  it("x.pow(2).mulGround(3).add(4).divmod(2)", () => {
    expect(show(x.pow(2).mulGround(3).add(4).divmod(2))).toBe("[2, x**2]");
  });
  it("x.pow(2).mulGround(3).add(4).floordiv(2)", () => {
    expect(show(x.pow(2).mulGround(3).add(4).floordiv(2))).toBe("2");
  });
  it("x.pow(2).mulGround(3).add(4).mod(2)", () => {
    expect(show(x.pow(2).mulGround(3).add(4).mod(2))).toBe("x**2");
  });
  it("x.pow(2).mulGround(2).add(4).truediv(2)", () => {
    expect(show(x.pow(2).mulGround(2).add(4).truediv(2))).toBe("x**2 + 2");
  });
  it("x.pow(2).sub(1).truediv(x.add(1))", () => {
    expect(show(x.pow(2).sub(1).truediv(x.add(1)))).toBe("x - 1");
  });
  it("a.pow(2).truediv(Q.groundNew(2))", () => {
    expect(show(a.pow(2).truediv(Q.groundNew(2)))).toBe("1/2*a**2");
  });
  it("x.pow(2).mul(y).add(y.mulGround(3)).degree()", () => {
    expect(show(x.pow(2).mul(y).add(y.mulGround(3)).degree())).toBe("2");
  });
  it("x.pow(2).mul(y).add(y.mulGround(3)).degree(y)", () => {
    expect(show(x.pow(2).mul(y).add(y.mulGround(3)).degree(y))).toBe("1");
  });
  it("x.pow(2).mul(y).add(y.mulGround(3)).degrees()", () => {
    expect(show(x.pow(2).mul(y).add(y.mulGround(3)).degrees())).toBe("[2, 1]");
  });
  it("x.pow(2).mul(y).add(y.mulGround(3)).tailDegree()", () => {
    expect(show(x.pow(2).mul(y).add(y.mulGround(3)).tailDegree())).toBe("0");
  });
  it("x.pow(2).mul(y).add(y.mulGround(3)).tailDegrees()", () => {
    expect(show(x.pow(2).mul(y).add(y.mulGround(3)).tailDegrees())).toBe("[0, 1]");
  });
  it("gx.mul(gy.pow(2)).add(gx.pow(2)).leadingExpv()", () => {
    expect(show(gx.mul(gy.pow(2)).add(gx.pow(2)).leadingExpv())).toBe("[1, 2]");
  });
  it("gx.mul(gy.pow(2)).add(gx.pow(2)).terms('lex')", () => {
    expect(show(gx.mul(gy.pow(2)).add(gx.pow(2)).terms('lex'))).toBe("[[[2, 0], 1], [[1, 2], 1]]");
  });
  it("x.mul(y).mulGround(3).add(y.pow(2)).LC", () => {
    expect(show(x.mul(y).mulGround(3).add(y.pow(2)).LC)).toBe("3");
  });
  it("x.mul(y).mulGround(3).add(y.pow(2)).LM", () => {
    expect(show(x.mul(y).mulGround(3).add(y.pow(2)).LM)).toBe("[1, 1]");
  });
  it("x.mul(y).mulGround(3).add(y.pow(2)).LT", () => {
    expect(show(x.mul(y).mulGround(3).add(y.pow(2)).LT)).toBe("[[1, 1], 3]");
  });
  it("R.groundNew(5).leadingMonom()", () => {
    expect(show(R.groundNew(5).leadingMonom())).toBe("1");
  });
  it("R.zero.leadingTerm()", () => {
    expect(show(R.zero.leadingTerm())).toBe("0");
  });
  it("x.mulGround(6).add(y.mulGround(4)).content()", () => {
    expect(show(x.mulGround(6).add(y.mulGround(4)).content())).toBe("2");
  });
  it("x.mulGround(6).add(y.mulGround(4)).primitive()", () => {
    expect(show(x.mulGround(6).add(y.mulGround(4)).primitive())).toBe("[2, 3*x + 2*y]");
  });
  it("R.zero.primitive()", () => {
    expect(show(R.zero.primitive())).toBe("[0, 0]");
  });
  it("a.mulGround(2).add(b.mulGround(4)).monic()", () => {
    expect(show(a.mulGround(2).add(b.mulGround(4)).monic())).toBe("a + 2*b");
  });
  it("x.mulGround(2).add(y.mulGround(3)).quoGround(2)", () => {
    expect(show(x.mulGround(2).add(y.mulGround(3)).quoGround(2))).toBe("x");
  });
  it("x.pow(2).mul(y).mulGround(2).add(x.mulGround(3)).quoTerm([[1", () => {
    expect(show(x.pow(2).mul(y).mulGround(2).add(x.mulGround(3)).quoTerm([[1, 0], 2]))).toBe("x*y");
  });
  it("x.pow(2).mul(y).mulGround(2).add(x.mulGround(3)).quoTerm([[0", () => {
    expect(show(x.pow(2).mul(y).mulGround(2).add(x.mulGround(3)).quoTerm([[0, 0], 2]))).toBe("x**2*y");
  });
  it("R.zero.quoTerm([[1, 0], 2])", () => {
    expect(show(R.zero.quoTerm([[1, 0], 2]))).toBe("0");
  });
  it("x.add(y).mulMonom([1, 2])", () => {
    expect(show(x.add(y).mulMonom([1, 2]))).toBe("x**2*y**2 + x*y**3");
  });
  it("x.add(y).mulTerm([[1, 2], 3])", () => {
    expect(show(x.add(y).mulTerm([[1, 2], 3]))).toBe("3*x**2*y**2 + 3*x*y**3");
  });
  it("x.add(y).mulTerm([[1, 2], 0])", () => {
    expect(show(x.add(y).mulTerm([[1, 2], 0]))).toBe("0");
  });
  it("x.mulGround(7).add(y.mulGround(5)).sub(4).truncGround(3)", () => {
    expect(show(x.mulGround(7).add(y.mulGround(5)).sub(4).truncGround(3))).toBe("x - y - 1");
  });
  it("x.mulGround(7).add(y.mulGround(5)).sub(4).remGround(3)", () => {
    expect(show(x.mulGround(7).add(y.mulGround(5)).sub(4).remGround(3))).toBe("x - y - 1");
  });
  it("x.mulGround(6).add(4).extractGround(x.mulGround(4).add(8))", () => {
    expect(show(x.mulGround(6).add(4).extractGround(x.mulGround(4).add(8)))).toBe("[2, 3*x + 2, 2*x + 4]");
  });
  it("x.mulGround(-7).add(y.mulGround(5)).sub(4).maxNorm()", () => {
    expect(show(x.mulGround(-7).add(y.mulGround(5)).sub(4).maxNorm())).toBe("7");
  });
  it("x.mulGround(-7).add(y.mulGround(5)).sub(4).l1Norm()", () => {
    expect(show(x.mulGround(-7).add(y.mulGround(5)).sub(4).l1Norm())).toBe("16");
  });
  it("x.pow(2).mul(y.pow(4)).add(x.pow(4)).deflate(x.pow(2))", () => {
    expect(show(x.pow(2).mul(y.pow(4)).add(x.pow(4)).deflate(x.pow(2)))).toBe("[[2, 4], [x**2 + x*y, x]]");
  });
  it("x.add(y).deflate()", () => {
    expect(show(x.add(y).deflate())).toBe("[[1, 1], [x + y]]");
  });
  it("x.add(y).inflate([2, 3])", () => {
    expect(show(x.add(y).inflate([2, 3]))).toBe("x**2 + y**3");
  });
  it("x.pow(2).sub(1).gcd(x.pow(2).sub(x.mulGround(2)).add(1))", () => {
    expect(show(x.pow(2).sub(1).gcd(x.pow(2).sub(x.mulGround(2)).add(1)))).toBe("x - 1");
  });
  it("x.pow(2).sub(1).cofactors(x.pow(2).sub(x.mulGround(2)).add(1", () => {
    expect(show(x.pow(2).sub(1).cofactors(x.pow(2).sub(x.mulGround(2)).add(1)))).toBe("[x - 1, x + 1, x - 1]");
  });
  it("a.pow(2).sub(1).cofactors(a.pow(2).mulGround(2).sub(a.mulGro", () => {
    expect(show(a.pow(2).sub(1).cofactors(a.pow(2).mulGround(2).sub(a.mulGround(4)).add(2)))).toBe("[a - 1, a + 1, 2*a - 2]");
  });
  it("R.zero.cofactors(R.zero)", () => {
    expect(show(R.zero.cofactors(R.zero))).toBe("[0, 0, 0]");
  });
  it("R.zero.cofactors(x.neg())", () => {
    expect(show(R.zero.cofactors(x.neg()))).toBe("[x, 0, -1]");
  });
  it("R.zero.cofactors(x)", () => {
    expect(show(R.zero.cofactors(x))).toBe("[x, 0, 1]");
  });
  it("x.neg().cofactors(R.zero)", () => {
    expect(show(x.neg().cofactors(R.zero))).toBe("[x, -1, 0]");
  });
  it("x.cofactors(R.zero)", () => {
    expect(show(x.cofactors(R.zero))).toBe("[x, 1, 0]");
  });
  it("x.pow(2).mul(y).mulGround(2).cofactors(x.mul(y).mulGround(4)", () => {
    expect(show(x.pow(2).mul(y).mulGround(2).cofactors(x.mul(y).mulGround(4).add(x.pow(3).mulGround(6))))).toBe("[2*x, x*y, 3*x**2 + 2*y]");
  });
  it("x.mul(y).mulGround(4).add(x.pow(3).mulGround(6)).cofactors(x", () => {
    expect(show(x.mul(y).mulGround(4).add(x.pow(3).mulGround(6)).cofactors(x.pow(2).mul(y).mulGround(2)))).toBe("[2*x, 3*x**2 + 2*y, x*y]");
  });
  it("x.pow(4).sub(1).cofactors(x.pow(2).sub(1))", () => {
    expect(show(x.pow(4).sub(1).cofactors(x.pow(2).sub(1)))).toBe("[x**2 - 1, x**2 + 1, 1]");
  });
  it("x.pow(2).sub(1).lcm(x.pow(2).sub(x.mulGround(2)).add(1))", () => {
    expect(show(x.pow(2).sub(1).lcm(x.pow(2).sub(x.mulGround(2)).add(1)))).toBe("x**3 - x**2 - x + 1");
  });
  it("a.pow(2).sub(1).lcm(a.pow(2).mulGround(2).sub(a.mulGround(4)", () => {
    expect(show(a.pow(2).sub(1).lcm(a.pow(2).mulGround(2).sub(a.mulGround(4)).add(2)))).toBe("a**3 - a**2 - a + 1");
  });
  it("x.pow(2).mulGround(2).sub(2).cancel(x.pow(2).sub(x.mulGround", () => {
    expect(show(x.pow(2).mulGround(2).sub(2).cancel(x.pow(2).sub(x.mulGround(2)).add(1)))).toBe("[2*x + 2, x - 1]");
  });
  it("a.pow(2).mulGround(sj.Rational.of(1, 2)).sub(1).cancel(a.mul", () => {
    expect(show(a.pow(2).mulGround(sj.Rational.of(1, 2)).sub(1).cancel(a.mulGround(sj.Rational.of(-1, 3)).sub(1)))).toBe("[-3*a**2 + 6, 2*a + 6]");
  });
  it("R.zero.cancel(x)", () => {
    expect(show(R.zero.cancel(x))).toBe("[0, 1]");
  });
  it("x.add(1).cancel(x.neg().sub(1))", () => {
    expect(show(x.add(1).cancel(x.neg().sub(1)))).toBe("[-1, 1]");
  });
  it("x.neg().canonicalUnit()", () => {
    expect(show(x.neg().canonicalUnit())).toBe("-1");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).diff(x)", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).diff(x))).toBe("3*x**2*y + 2");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).evaluate(x, 2)", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).evaluate(x, 2))).toBe("8*y + 4");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[x, 2], [y, 3]", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[x, 2], [y, 3]]))).toBe("28");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[y, 3], [x, 2]", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[y, 3], [x, 2]]))).toBe("28");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[y, 3]])", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).evaluate([[y, 3]]))).toBe("3*x**3 + 2*x");
  });
  it("t.pow(2).add(1).evaluate(t, 3)", () => {
    expect(show(t.pow(2).add(1).evaluate(t, 3))).toBe("10");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).call(2)", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).call(2))).toBe("8*y + 4");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).call(2, 3)", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).call(2, 3))).toBe("28");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).subs(x, 2)", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).subs(x, 2))).toBe("8*y + 4");
  });
  it("x.pow(3).mul(y).add(x.mulGround(2)).subs([[x, 2], [y, 3]])", () => {
    expect(show(x.pow(3).mul(y).add(x.mulGround(2)).subs([[x, 2], [y, 3]]))).toBe("28");
  });
  it("x.pow(2).add(y).compose(x, y.add(1))", () => {
    expect(show(x.pow(2).add(y).compose(x, y.add(1)))).toBe("y**2 + 3*y + 1");
  });
  it("x.pow(2).add(y).compose([[x, y.add(1)], [y, x]])", () => {
    expect(show(x.pow(2).add(y).compose([[x, y.add(1)], [y, x]]))).toBe("x + y**2 + 2*y + 1");
  });
  it("x.pow(2).add(y).compose(new Map([[y, x], [x, y.add(1)]]))", () => {
    expect(show(x.pow(2).add(y).compose(new Map([[y, x], [x, y.add(1)]])))).toBe("x + y**2 + 2*y + 1");
  });
  it("x.pow(2).mul(y).add(3).coeffWrt(x, 2)", () => {
    expect(show(x.pow(2).mul(y).add(3).coeffWrt(x, 2))).toBe("y");
  });
  it("x.pow(2).mul(y).add(3).coeffWrt(x, 5)", () => {
    expect(show(x.pow(2).mul(y).add(3).coeffWrt(x, 5))).toBe("0");
  });
  it("x.pow(2).add(x.mul(y)).prem(x.mulGround(2).add(2))", () => {
    expect(show(x.pow(2).add(x.mul(y)).prem(x.mulGround(2).add(2)))).toBe("-4*y + 4");
  });
  it("x.prem(x.pow(2))", () => {
    expect(show(x.prem(x.pow(2)))).toBe("x");
  });
  it("x.pdiv(x.pow(2))", () => {
    expect(show(x.pdiv(x.pow(2)))).toBe("[0, x]");
  });
  it("x.pow(2).add(x.mul(y)).pexquo(x.add(y))", () => {
    expect(show(x.pow(2).add(x.mul(y)).pexquo(x.add(y)))).toBe("x");
  });
  it("x.pow(2).add(y).subresultants(x.add(1))", () => {
    expect(show(x.pow(2).add(y).subresultants(x.add(1)))).toBe("[x**2 + y, x + 1, y + 1]");
  });
  it("x.add(1).subresultants(x.pow(2).add(y))", () => {
    expect(show(x.add(1).subresultants(x.pow(2).add(y)))).toBe("[x**2 + y, x + 1, y + 1]");
  });
  it("x.pow(3).add(y).subresultants(x.pow(2).add(x.mul(y)).add(1))", () => {
    expect(show(x.pow(3).add(y).subresultants(x.pow(2).add(x.mul(y)).add(1)))).toBe("[x**3 + y, x**2 + x*y + 1, x*y**2 - x + 2*y, -y**4 + 4*y**2 + 1]");
  });
  it("x.pow(2).add(y).subresultants(R.zero)", () => {
    expect(show(x.pow(2).add(y).subresultants(R.zero))).toBe("[x**2 + y, 1]");
  });
  it("R.zero.subresultants(R.zero)", () => {
    expect(show(R.zero.subresultants(R.zero))).toBe("[0, 0]");
  });
  it("x.pow(2).mul(y).add(x.mul(y.pow(2))).symmetrize()", () => {
    expect(show(x.pow(2).mul(y).add(x.mul(y.pow(2))).symmetrize())).toBe("[x*y, 0, [[x, x + y], [y, x*y]]]");
  });
  it("R.symmetricPoly(0)", () => {
    expect(show(R.symmetricPoly(0))).toBe("1");
  });
  it("R.symmetricPoly(2)", () => {
    expect(show(R.symmetricPoly(2))).toBe("x*y");
  });
  it("t.pow(2).add(t).decompose()", () => {
    expect(show(t.pow(2).add(t).decompose())).toBe("[t**2 + t]");
  });
  it("t.pow(2).add(t).shift(1)", () => {
    expect(show(t.pow(2).add(t).shift(1))).toBe("t**2 + 3*t + 2");
  });
  it("x.mul(y).add(x).shiftList([1, 2])", () => {
    expect(show(x.mul(y).add(x).shiftList([1, 2]))).toBe("x*y + 3*x + y + 3");
  });
  it("s.pow(3).sub(s).sturm()", () => {
    expect(show(s.pow(3).sub(s).sturm())).toBe("[s**3 - s, 3*s**2 - 1, 2/3*s, 1]");
  });
  it("t.pow(5).add(t.pow(4).mulGround(2)).sub(t.pow(3)).sub(t.pow(", () => {
    expect(show(t.pow(5).add(t.pow(4).mulGround(2)).sub(t.pow(3)).sub(t.pow(2).mulGround(2)).gffList())).toBe("[[t, 1], [t + 2, 4]]");
  });
  it("x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)).sqfPart()", () => {
    expect(show(x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)).sqfPart())).toBe("x + y");
  });
  it("x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)).sqfList()", () => {
    expect(show(x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)).sqfList())).toBe("[1, [[x + y, 2]]]");
  });
  it("x.pow(2).mulGround(2).sub(y.pow(2).mulGround(2)).factorList(", () => {
    expect(show(x.pow(2).mulGround(2).sub(y.pow(2).mulGround(2)).factorList())).toBe("[2, [[x - y, 1], [x + y, 1]]]");
  });
  it("s.pow(2).sub(1).gcdex(s.pow(2).add(s))", () => {
    expect(show(s.pow(2).sub(1).gcdex(s.pow(2).add(s)))).toBe("[-1, 1, s + 1]");
  });
  it("s.pow(2).sub(1).halfGcdex(s.pow(2).add(s))", () => {
    expect(show(s.pow(2).sub(1).halfGcdex(s.pow(2).add(s)))).toBe("[-1, s + 1]");
  });
  it("x.pow(2).add(y).resultant(x.add(y))", () => {
    expect(show(x.pow(2).add(y).resultant(x.add(y)))).toBe("y**2 + y");
  });
  it("x.pow(2).add(y).discriminant()", () => {
    expect(show(x.pow(2).add(y).discriminant())).toBe("-4*y");
  });
  it("x.pow(2).mul(y).dropToGround(y)", () => {
    expect(show(x.pow(2).mul(y).dropToGround(y))).toBe("y*x**2");
  });
  it("x.pow(2).drop(y)", () => {
    expect(show(x.pow(2).drop(y))).toBe("x**2");
  });
  it("U.groundNew(3).drop(t)", () => {
    expect(show(U.groundNew(3).drop(t))).toBe("3");
  });
  it("x.add(y).clearDenoms()", () => {
    expect(show(x.add(y).clearDenoms())).toBe("[1, x + y]");
  });
  it("a.mulGround(sj.Rational.of(1, 2)).add(b.mulGround(sj.Rationa", () => {
    expect(show(a.mulGround(sj.Rational.of(1, 2)).add(b.mulGround(sj.Rational.of(1, 3))).clearDenoms())).toBe("[6, 3*a + 2*b]");
  });
  it("x.pow(2).add(1).setRing(new PolyRing('y,x', 'ZZ'))", () => {
    expect(show(x.pow(2).add(1).setRing(new PolyRing('y,x', 'ZZ')))).toBe("x**2 + 1");
  });
  it("x.pow(2).add(1).setRing(new PolyRing('x,y', 'QQ'))", () => {
    expect(show(x.pow(2).add(1).setRing(new PolyRing('x,y', 'QQ')))).toBe("x**2 + 1");
  });
  it("R.add([0, 1, 2, 3].map((i) => x.pow(2).add(2 * i + 3)))", () => {
    expect(show(R.add([0, 1, 2, 3].map((i) => x.pow(2).add(2 * i + 3))))).toBe("4*x**2 + 24");
  });
  it("R.mul(x.add(1), [x, x])", () => {
    expect(show(R.mul(x.add(1), [x, x]))).toBe("x**3 + x**2");
  });
  it("R.drop(x)", () => {
    expect(show(R.drop(x))).toBe("Polynomial ring in y over ZZ with lex order");
  });
  it("R.drop(x, y)", () => {
    expect(show(R.drop(x, y))).toBe("ZZ");
  });
  it("R.dropToGround(x)", () => {
    expect(show(R.dropToGround(x))).toBe("Polynomial ring in y over ZZ[x] with lex order");
  });
  it("R.dropToGround(x, y)", () => {
    expect(show(R.dropToGround(x, y))).toBe("Polynomial ring in x, y over ZZ with lex order");
  });
  it("P.toGround()", () => {
    expect(show(P.toGround())).toBe("Polynomial ring in x, y over ZZ with lex order");
  });
  it("R.index(-1)", () => {
    expect(show(R.index(-1))).toBe("0");
  });
  it("R.index(y)", () => {
    expect(show(R.index(y))).toBe("1");
  });
  it("R.index()", () => {
    expect(show(R.index())).toBe("0");
  });
  it("R.compose(R)", () => {
    expect(show(R.compose(R))).toBe("Polynomial ring in x, y over ZZ with lex order");
  });
  it("R.fromList([[1, 2], [3]])", () => {
    expect(show(R.fromList([[1, 2], [3]]))).toBe("x*y + 2*x + 3");
  });
  it("R.fromDict(new Map([[[1, 0], 3], [[0, 0], 0]]))", () => {
    expect(show(R.fromDict(new Map([[[1, 0], 3], [[0, 0], 0]])))).toBe("3*x");
  });
  it("R.ringNew([[[1, 0], 3], [[0, 1], 2]])", () => {
    expect(show(R.ringNew([[[1, 0], 3], [[0, 1], 2]]))).toBe("3*x + 2*y");
  });
  it("R.ringNew(new Map([[[1, 1], 2]]))", () => {
    expect(show(R.ringNew(new Map([[[1, 1], 2]])))).toBe("2*x*y");
  });
  it("R.ringNew(x)", () => {
    expect(show(R.ringNew(x))).toBe("x");
  });
  it("R.ringNew(5)", () => {
    expect(show(R.ringNew(5))).toBe("5");
  });
  it("R.ringNew(sj.parseExpr('x**2*y + 3'))", () => {
    expect(show(R.ringNew(sj.parseExpr('x**2*y + 3')))).toBe("x**2*y + 3");
  });
  it("R.fromExpr(sj.parseExpr('(x + y)**2'))", () => {
    expect(show(R.fromExpr(sj.parseExpr('(x + y)**2')))).toBe("x**2 + 2*x*y + y**2");
  });
  it("x.asExpr(...sj.symbols('u v'))", () => {
    expect(show(x.asExpr(...sj.symbols('u v')))).toBe("u");
  });
  it("x.mul(y).add(1).toDense()", () => {
    expect(show(x.mul(y).add(1).toDense())).toBe("[[1, 0], [1]]");
  });
  it("vring('x,y,z', ZZ, lex)", () => {
    expect(show(vring('x,y,z', ZZ, lex))).toBe("Polynomial ring in x, y, z over ZZ with lex order");
  });
  it("sring(sj.parseExpr('x**2 + 2*y'))[1]", () => {
    expect(show(sring(sj.parseExpr('x**2 + 2*y'))[1])).toBe("x**2 + 2*y");
  });
  it("sring([sj.parseExpr('x/2 + y'), sj.parseExpr('x')])[1]", () => {
    expect(show(sring([sj.parseExpr('x/2 + y'), sj.parseExpr('x')])[1])).toBe("[1/2*x + y, x]");
  });
  it("sring(sj.parseExpr('x + y'), { domain: 'QQ' })[0]", () => {
    expect(show(sring(sj.parseExpr('x + y'), { domain: 'QQ' })[0])).toBe("Polynomial ring in x, y over QQ with lex order");
  });
});

describe('ring construction and conversions', () => {
  const X = sj.symbols('x')[0];
  it('parses generators, domains and orders', () => {
    expect(new PolyRing(X).toString()).toBe('Polynomial ring in x over ZZ with lex order');
    expect(new PolyRing(['u', 'v w']).ngens).toBe(3);
    expect(new PolyRing([X, w]).ngens).toBe(2);
    expect(() => new PolyRing(['u', X])).toThrow('expected a string');
    expect(new PolyRing('u', 'QQ(v)').domain.toString()).toBe('QQ(v)');
    expect(() => new PolyRing('u', 'GF(7)')).toThrow('valid domain');
    expect(() => new PolyRing('u', ZZ, 'foo')).toThrow('orderings');
    // SymPy: polynomial ring and it's ground domain share generators
    expect(() => new PolyRing('w', 'ZZ[w]')).toThrow(sj.GeneratorsError);
    expect(R.equals(new PolyRing('x,y', ZZ))).toBe(true);
    expect(R.isMultivariate).toBe(true);
    expect(xring('x', ZZ)[1].map(String)).toEqual(['x']);
  });
  it('converts values into the ring', () => {
    expect(String(R.domainNew(R.groundNew(4)))).toBe('4');
    expect(() => R.domainNew(x)).toThrow('cannot convert');
    expect(R.termNew([1, 0], 0).isZero).toBe(true);
    const [, qx, qy] = ring('x,y', QQ) as [PolyRing, PolyElement, PolyElement];
    expect(R.ringNew(qx.add(qy)).toString()).toBe('x + y');
    expect(() => R.ringNew(a)).toThrow(sj.NotImplementedError);
    expect(() => R.ringNew('x' as never)).toThrow(sj.NotImplementedError);
    expect(() => R.ringNew(true as unknown as number)).toThrow(TypeError);
    expect(R.fromDict([[[0, 1], 2]]).toString()).toBe('2*y');
    expect(R.ringNew([[1, 2], [3]]).toString()).toBe('x*y + 2*x + 3');
    expect(() => R.fromTerms([[[1], 1]])).toThrow('length 2');
    expect(R.fromList([[0, 2], [0]]).toString()).toBe('2*x');
    expect(() => R.fromList([[[1]], [1]])).toThrow('more deeply');
    expect(() => R.fromList([1, 2])).toThrow('less deeply');
    expect(() => R.fromExpr(sj.sin(X))).toThrow('convertible');
    // SymPy compares a string with the symbols and does not find it; symjs looks the name up
    expect(R.index('y')).toBe(1);
    expect(() => R.index('z')).toThrow('invalid generator');
    expect(() => R.index(a)).toThrow('invalid generator');
    expect(() => R.index(5)).toThrow('invalid generator index');
    expect(new PolyRing([]).index()).toBe(-1);
    expect(() => R.toGround()).toThrow('not a composite domain');
    expect(new PolyRing('a,b', 'QQ[w]').toGround().toString()).toBe('Polynomial ring in a, b over QQ with lex order');
    expect(new PolyRing('a', 'QQ(w)').toGround().toString()).toBe('Polynomial ring in a over QQ with lex order');
    expect(new PolyRing('a', RR.polyRing(w)).toGround().domain).toBe(RR);
    expect(new PolyRing('a', EX.polyRing(w)).toGround().domain).toBe(EX);
    expect(R.compose(new PolyRing('z', ZZ)).ngens).toBe(3);
    expect(() => R.symmetricPoly(3)).toThrow('Cannot generate');
    const [, sx] = ring([sj.sin(X)], ZZ) as [PolyRing, PolyElement];
    expect(sx.pow(2).add(sx.mulGround(3)).toString()).toBe('(sin(x))**2 + 3*(sin(x))');
    expect(() => new PolyRing([sj.sin(X), X]).dropToGround(0)).toThrow('not a symbol');
  });
});

describe('ring elements', () => {
  it('print coefficients and exponents as SymPy', () => {
    expect(px.pow(2).mulGround(sj.add(w, 1)).sub(py).toString()).toBe('(w + 1)*x**2 - y');
    expect(R.fromTerms([[[-1, 0], 1], [[0, 2], 3]]).toString()).toBe('3*y**2 + x**(-1)');
    expect(show(x.add(1).toDict())).toBe('[object Map]');
    expect([...x.add(1).toDict().keys()].map(show)).toEqual(['[1, 0]', '[0, 0]']);
    expect(new PolyRing([]).groundNew(3).toDense()).toEqual([sj.Rational.of(3)]);
  });
  it('move between rings', () => {
    expect(x.setRing(R)).toBe(x);
    expect(() => x.add(y).setRing(new PolyRing('x', ZZ))).toThrow('unable to drop');
    expect(x.setRing(new PolyRing('x', ZZ)).toString()).toBe('x');
    expect(() => x.asExpr(w)).toThrow('Wrong number of symbols');
    expect(() => t.drop(t)).toThrow('Cannot drop');
    expect(() => x.drop(x)).toThrow('Cannot drop');
    expect(() => t.dropToGround(t)).toThrow('only generator');
  });
  it('compare', () => {
    expect(x.equals(a)).toBe(false);
    expect(R.zero.equals(Q.zero)).toBe(true);
    expect(x.equals(x.add(y))).toBe(false);
    expect(x.equals(x.mulGround(2))).toBe(false);
    expect(R.groundNew(3).equals(3)).toBe(true);
    expect(R.zero.equals(0)).toBe(true);
    expect(x.add(1).equals(1)).toBe(false);
    expect(x.equals(1)).toBe(false);
    expect(x.equals('x')).toBe(false);
  });
  it('have SymPy predicates', () => {
    const [u, v] = [x, y];
    expect(t.isGenerator).toBe(true);
    expect(u.mulGround(2).isMonomial).toBe(false);
    expect(u.isTerm).toBe(true);
    expect(u.add(1).isLinear).toBe(true);
    expect(u.mul(v).isQuadratic).toBe(true);
    expect(u.pow(2).sub(1).isSquarefree).toBe(true);
    expect(u.pow(2).add(1).isIrreducible).toBe(true);
    expect(t.pow(2).add(t).add(1).isCyclotomic).toBe(true);
    expect(() => u.isCyclotomic).toThrow(sj.MultivariatePolynomialError);
    expect(t.pow(2).add(1).isPrimitive).toBe(true);
    expect(t.neg().isNonpositive).toBe(true);
    expect(t.isPositive).toBe(true);
    expect(U.one.isOne).toBe(true);
    expect(t.add(1).isMonic).toBe(true);
    expect(new PolyRing([]).one.isSquarefree).toBe(true);
    expect(new PolyRing([]).one.isIrreducible).toBe(true);
  });
  it('reject invalid arithmetic', () => {
    expect(x.add(new PolyRing([]).groundNew(2)).toString()).toBe('x + 2');
    expect(() => x.add(a)).toThrow('cannot combine');
    expect(() => x.pow(-1)).toThrow('non-negative');
    expect(() => R.zero.pow(0)).toThrow('0**0');
    expect(() => x.div(R.zero)).toThrow('polynomial division');
    expect(() => x.div(a)).toThrow('same ring');
    expect(x.add(1).rem(x).toString()).toBe('1');
    expect(() => x.exquo(y)).toThrow(sj.ExactQuotientFailed);
    expect(() => x.truediv(0)).toThrow('polynomial division');
    expect(x.mulGround(2).truediv(R.groundNew(2)).toString()).toBe('x');
    expect(() => x.quoGround(0)).toThrow('polynomial division');
    expect(() => x.quoTerm([[0, 0], 0])).toThrow('polynomial division');
    expect(x.mulGround(0).isZero).toBe(true);
    expect(R.zero.monic().isZero).toBe(true);
    expect(() => x.pdiv(R.zero)).toThrow('polynomial division');
    expect(() => x.pexquo(y.add(x))).toThrow(sj.ExactQuotientFailed);
    expect(x.pow(2).pquo(x).toString()).toBe('x');
  });
  it('give degrees, coefficients and terms', () => {
    const Z = new PolyRing([]);
    expect(Z.groundNew(2).degree()).toBe(0);
    expect(Z.groundNew(2).tailDegree()).toBe(0);
    expect(R.zero.tailDegree()).toBe(-Infinity);
    expect(R.zero.degree()).toBe(-Infinity);
    expect(R.zero.leadingExpv()).toEqual([0, 0]);
    expect(String(x.add(3).coeff(1))).toBe('3');
    expect(() => x.coeff(2)).toThrow('expected a monomial');
    expect(String(x.mul(y).mulGround(5).coeff(x.mul(y)))).toBe('5');
    expect(() => x.coeff(x.mulGround(2))).toThrow('expected a monomial');
    expect(() => x.coeff(a)).toThrow('expected a monomial');
    expect(R.zero.leadingMonom().isZero).toBe(true);
    expect(x.add(y.mulGround(2)).coeffs().map(String)).toEqual(['1', '2']);
    expect(show(x.add(y).monoms('grlex'))).toBe('[[1, 0], [0, 1]]');
  });
  it('evaluate and substitute', () => {
    expect(() => x.call()).toThrow('expected at least 1');
    expect(x.evaluate([])).toBe(x);
    expect(x.add(y).subs(x).toString()).toBe('y');
    expect(x.add(y).evaluate(x).toString()).toBe('y');
    expect(() => x.compose(x)).toThrow('expected a generator');
  });
  it('symmetrize and build subresultants', () => {
    // SymPy: (u**2, -v, [(u, u + v), (v, u*v)])
    expect(show(x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)).sub(y).symmetrize())).toBe('[x**2, -y, [[x, x + y], [y, x*y]]]');
    expect(show(y.symmetrize())).toBe('[0, y, [[x, x + y], [y, x*y]]]');
    expect(show(new PolyRing([]).one.symmetrize())).toBe('[1, 0, []]');
    expect(show(x.pow(4).add(y).subresultants(x, 0))).toBe('[x**4 + y, x, y]');
    expect(show(x.pow(3).add(y).subresultants(x.add(1)))).toBe('[x**3 + y, x + 1, -y + 1]');
    expect(show(x.pow(6).add(x.mul(y)).add(1).subresultants(x.pow(3).add(y)))).toBe('[x**6 + x*y + 1, x**3 + y, x*y + y**2 + 1, y**6 + 2*y**4 + 3*y**2 + 1]');
  });
  it('need univariate rings for univariate operations', () => {
    expect(() => x.decompose()).toThrow(sj.MultivariatePolynomialError);
    expect(() => x.shift(1)).toThrow(sj.MultivariatePolynomialError);
    expect(() => x.sturm()).toThrow(sj.MultivariatePolynomialError);
  });
  it('builds rings from expressions', () => {
    const X = sj.symbols('x')[0];
    expect(show(sring(sj.Rational.of(0), X))).toBe('[Polynomial ring in x over ZZ with lex order, 0]');
    expect(show(sring([X], { domain: 'QQ' }))).toBe('[Polynomial ring in x over QQ with lex order, [x]]');
  });
});
