// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/compatibility.ts: the R.dup_*/R.dmp_* methods of polynomial
// rings and the ground domain helpers; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { EX, QQ, RR, ZZ } from '../../src/polys/domains';
import * as C from '../../src/polys/compatibility';
import { PolyElement, PolyRing, ring } from '../../src/polys/rings';

/** Python's str of a value (lists for tuples). */
function show(v: unknown): string {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof sj.Expr) return sj.str(v);
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  return String(v);
}

const [R, x, y] = ring('x,y', ZZ) as [PolyRing, PolyElement, PolyElement];
const [Q, a, b] = ring('a,b', QQ) as [PolyRing, PolyElement, PolyElement];
const [U, t] = ring('t', ZZ) as [PolyRing, PolyElement];
const [V, s] = ring('s', QQ) as [PolyRing, PolyElement];
const [T, p, q, r] = ring('p,q,r', ZZ) as [PolyRing, PolyElement, PolyElement, PolyElement];
const Y = sj.symbols('y')[0];
void [EX, RR, C, T, p, q, r, Y];

describe('SymPy doctest and suite values', () => {
  it("U.dupAddTerm(t.pow(2).sub(1), 2, 4)", () => {
    expect(show(U.dupAddTerm(t.pow(2).sub(1), 2, 4))).toBe("2*t**4 + t**2 - 1");
  });
  it("R.dmpAddTerm(x.mul(y).add(1), 2, 2)", () => {
    expect(show(R.dmpAddTerm(x.mul(y).add(1), 2, 2))).toBe("2*x**2 + x*y + 1");
  });
  it("U.dupSubTerm(t.pow(4).mulGround(2).add(t.pow(2)).sub(1), 2, ", () => {
    expect(show(U.dupSubTerm(t.pow(4).mulGround(2).add(t.pow(2)).sub(1), 2, 4))).toBe("t**2 - 1");
  });
  it("R.dmpSubTerm(x.pow(2).mulGround(2).add(x.mul(y)).add(1), 2, ", () => {
    expect(show(R.dmpSubTerm(x.pow(2).mulGround(2).add(x.mul(y)).add(1), 2, 2))).toBe("x*y + 1");
  });
  it("U.dupMulTerm(t.pow(2).sub(1), 3, 2)", () => {
    expect(show(U.dupMulTerm(t.pow(2).sub(1), 3, 2))).toBe("3*t**4 - 3*t**2");
  });
  it("R.dmpMulTerm(x.pow(2).mul(y).add(x), y.mulGround(3), 2)", () => {
    expect(show(R.dmpMulTerm(x.pow(2).mul(y).add(x), y.mulGround(3), 2))).toBe("3*x**4*y**2 + 3*x**3*y");
  });
  it("U.dupAddGround(t.pow(3).add(4), 4)", () => {
    expect(show(U.dupAddGround(t.pow(3).add(4), 4))).toBe("t**3 + 8");
  });
  it("R.dmpAddGround(x.pow(3).add(4), 4)", () => {
    expect(show(R.dmpAddGround(x.pow(3).add(4), 4))).toBe("x**3 + 8");
  });
  it("U.dupSubGround(t.pow(3).add(4), 4)", () => {
    expect(show(U.dupSubGround(t.pow(3).add(4), 4))).toBe("t**3");
  });
  it("R.dmpSubGround(x.pow(3).add(4), 4)", () => {
    expect(show(R.dmpSubGround(x.pow(3).add(4), 4))).toBe("x**3");
  });
  it("U.dupMulGround(t.pow(2).add(t.mulGround(2)).sub(1), 3)", () => {
    expect(show(U.dupMulGround(t.pow(2).add(t.mulGround(2)).sub(1), 3))).toBe("3*t**2 + 6*t - 3");
  });
  it("R.dmpMulGround(x.mulGround(2).add(y.mulGround(2)), 3)", () => {
    expect(show(R.dmpMulGround(x.mulGround(2).add(y.mulGround(2)), 3))).toBe("6*x + 6*y");
  });
  it("U.dupQuoGround(t.pow(2).mulGround(3).add(2), 2)", () => {
    expect(show(U.dupQuoGround(t.pow(2).mulGround(3).add(2), 2))).toBe("t**2 + 1");
  });
  it("Q.dmpQuoGround(a.pow(2).mul(b).mulGround(2).add(a.mulGround(", () => {
    expect(show(Q.dmpQuoGround(a.pow(2).mul(b).mulGround(2).add(a.mulGround(3)), 2))).toBe("a**2*b + 3/2*a");
  });
  it("V.dupExquoGround(s.pow(2).add(2), 2)", () => {
    expect(show(V.dupExquoGround(s.pow(2).add(2), 2))).toBe("1/2*s**2 + 1");
  });
  it("Q.dmpExquoGround(a.pow(2).mul(b).add(a.mulGround(2)), 2)", () => {
    expect(show(Q.dmpExquoGround(a.pow(2).mul(b).add(a.mulGround(2)), 2))).toBe("1/2*a**2*b + a");
  });
  it("U.dupLshift(t.pow(2).add(1), 2)", () => {
    expect(show(U.dupLshift(t.pow(2).add(1), 2))).toBe("t**4 + t**2");
  });
  it("U.dupRshift(t.pow(4).add(t.pow(2)).add(2), 2)", () => {
    expect(show(U.dupRshift(t.pow(4).add(t.pow(2)).add(2), 2))).toBe("t**2 + 1");
  });
  it("U.dupAbs(t.pow(2).sub(1))", () => {
    expect(show(U.dupAbs(t.pow(2).sub(1)))).toBe("t**2 + 1");
  });
  it("R.dmpAbs(x.pow(2).mul(y).sub(x))", () => {
    expect(show(R.dmpAbs(x.pow(2).mul(y).sub(x)))).toBe("x**2*y + x");
  });
  it("U.dupNeg(t.pow(2).sub(1))", () => {
    expect(show(U.dupNeg(t.pow(2).sub(1)))).toBe("-t**2 + 1");
  });
  it("R.dmpNeg(x.pow(2).mul(y).sub(x))", () => {
    expect(show(R.dmpNeg(x.pow(2).mul(y).sub(x)))).toBe("-x**2*y + x");
  });
  it("U.dupAdd(t.pow(2).sub(1), t.sub(2))", () => {
    expect(show(U.dupAdd(t.pow(2).sub(1), t.sub(2)))).toBe("t**2 + t - 3");
  });
  it("R.dmpAdd(x.pow(2).add(y), x.pow(2).mul(y).add(x))", () => {
    expect(show(R.dmpAdd(x.pow(2).add(y), x.pow(2).mul(y).add(x)))).toBe("x**2*y + x**2 + x + y");
  });
  it("U.dupSub(t.pow(2).sub(1), t.sub(2))", () => {
    expect(show(U.dupSub(t.pow(2).sub(1), t.sub(2)))).toBe("t**2 - t + 1");
  });
  it("R.dmpSub(x.pow(2).add(y), x.pow(2).mul(y).add(x))", () => {
    expect(show(R.dmpSub(x.pow(2).add(y), x.pow(2).mul(y).add(x)))).toBe("-x**2*y + x**2 - x + y");
  });
  it("U.dupAddMul(t.pow(2).sub(1), t.sub(2), t.add(2))", () => {
    expect(show(U.dupAddMul(t.pow(2).sub(1), t.sub(2), t.add(2)))).toBe("2*t**2 - 5");
  });
  it("R.dmpAddMul(x.pow(2).add(y), x, x.add(2))", () => {
    expect(show(R.dmpAddMul(x.pow(2).add(y), x, x.add(2)))).toBe("2*x**2 + 2*x + y");
  });
  it("U.dupSubMul(t.pow(2).sub(1), t.sub(2), t.add(2))", () => {
    expect(show(U.dupSubMul(t.pow(2).sub(1), t.sub(2), t.add(2)))).toBe("3");
  });
  it("R.dmpSubMul(x.pow(2).add(y), x, x.add(2))", () => {
    expect(show(R.dmpSubMul(x.pow(2).add(y), x, x.add(2)))).toBe("-2*x + y");
  });
  it("U.dupMul(t.sub(2), t.add(2))", () => {
    expect(show(U.dupMul(t.sub(2), t.add(2)))).toBe("t**2 - 4");
  });
  it("R.dmpMul(x.mul(y).add(1), x)", () => {
    expect(show(R.dmpMul(x.mul(y).add(1), x))).toBe("x**2*y + x");
  });
  it("U.dupSqr(t.pow(2).add(1))", () => {
    expect(show(U.dupSqr(t.pow(2).add(1)))).toBe("t**4 + 2*t**2 + 1");
  });
  it("R.dmpSqr(x.pow(2).add(x.mul(y)).add(y.pow(2)))", () => {
    expect(show(R.dmpSqr(x.pow(2).add(x.mul(y)).add(y.pow(2))))).toBe("x**4 + 2*x**3*y + 3*x**2*y**2 + 2*x*y**3 + y**4");
  });
  it("U.dupPow(t.sub(2), 3)", () => {
    expect(show(U.dupPow(t.sub(2), 3))).toBe("t**3 - 6*t**2 + 12*t - 8");
  });
  it("R.dmpPow(x.mul(y).add(1), 3)", () => {
    expect(show(R.dmpPow(x.mul(y).add(1), 3))).toBe("x**3*y**3 + 3*x**2*y**2 + 3*x*y + 1");
  });
  it("R.dmpPow(x.mul(y).add(1), 0)", () => {
    expect(show(R.dmpPow(x.mul(y).add(1), 0))).toBe("1");
  });
  it("R.dmpPow(R.zero, 2)", () => {
    expect(show(R.dmpPow(R.zero, 2))).toBe("0");
  });
  it("U.dupPdiv(t.pow(2).add(1), t.mulGround(2).sub(4))", () => {
    expect(show(U.dupPdiv(t.pow(2).add(1), t.mulGround(2).sub(4)))).toBe("[2*t + 4, 20]");
  });
  it("U.dupPdiv(t, t.pow(2).mulGround(2).sub(4))", () => {
    expect(show(U.dupPdiv(t, t.pow(2).mulGround(2).sub(4)))).toBe("[0, t]");
  });
  it("U.dupPrem(t.pow(2).add(1), t.mulGround(2).sub(4))", () => {
    expect(show(U.dupPrem(t.pow(2).add(1), t.mulGround(2).sub(4)))).toBe("20");
  });
  it("U.dupPquo(t.pow(2).sub(1), t.mulGround(2).sub(2))", () => {
    expect(show(U.dupPquo(t.pow(2).sub(1), t.mulGround(2).sub(2)))).toBe("2*t + 2");
  });
  it("U.dupPexquo(t.pow(2).sub(1), t.mulGround(2).sub(2))", () => {
    expect(show(U.dupPexquo(t.pow(2).sub(1), t.mulGround(2).sub(2)))).toBe("2*t + 2");
  });
  it("R.dmpPdiv(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2))", () => {
    expect(show(R.dmpPdiv(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2)))).toBe("[2*x + 2*y - 2, -4*y + 4]");
  });
  it("R.dmpPrem(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2))", () => {
    expect(show(R.dmpPrem(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2)))).toBe("-4*y + 4");
  });
  it("R.dmpPquo(x.pow(2).add(x.mul(y)), x.mulGround(2).add(y.mulGr", () => {
    expect(show(R.dmpPquo(x.pow(2).add(x.mul(y)), x.mulGround(2).add(y.mulGround(2))))).toBe("2*x");
  });
  it("R.dmpPexquo(x.pow(2).add(x.mul(y)), x.mulGround(2).add(y.mul", () => {
    expect(show(R.dmpPexquo(x.pow(2).add(x.mul(y)), x.mulGround(2).add(y.mulGround(2))))).toBe("2*x");
  });
  it("U.dupRrDiv(t.pow(2).add(1), t.mulGround(2).sub(4))", () => {
    expect(show(U.dupRrDiv(t.pow(2).add(1), t.mulGround(2).sub(4)))).toBe("[0, t**2 + 1]");
  });
  it("U.dupRrDiv(t.pow(2).mulGround(2).add(t.mulGround(4)), t.mulG", () => {
    expect(show(U.dupRrDiv(t.pow(2).mulGround(2).add(t.mulGround(4)), t.mulGround(2)))).toBe("[t + 2, 0]");
  });
  it("R.dmpRrDiv(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2))", () => {
    expect(show(R.dmpRrDiv(x.pow(2).add(x.mul(y)), x.mulGround(2).add(2)))).toBe("[0, x**2 + x*y]");
  });
  it("R.dmpRrDiv(x.pow(2).mul(y).add(x.mul(y.pow(2))), x.mul(y).ad", () => {
    expect(show(R.dmpRrDiv(x.pow(2).mul(y).add(x.mul(y.pow(2))), x.mul(y).add(y)))).toBe("[x + y - 1, -y**2 + y]");
  });
  it("V.dupFfDiv(s.pow(2).add(1), s.mulGround(2).sub(4))", () => {
    expect(show(V.dupFfDiv(s.pow(2).add(1), s.mulGround(2).sub(4)))).toBe("[1/2*s + 1, 5]");
  });
  it("Q.dmpFfDiv(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2))", () => {
    expect(show(Q.dmpFfDiv(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2)))).toBe("[1/2*a + 1/2*b - 1/2, -b + 1]");
  });
  it("V.dupDiv(s.pow(2).add(1), s.mulGround(2).sub(4))", () => {
    expect(show(V.dupDiv(s.pow(2).add(1), s.mulGround(2).sub(4)))).toBe("[1/2*s + 1, 5]");
  });
  it("V.dupRem(s.pow(2).add(1), s.mulGround(2).sub(4))", () => {
    expect(show(V.dupRem(s.pow(2).add(1), s.mulGround(2).sub(4)))).toBe("5");
  });
  it("V.dupQuo(s.pow(2).add(1), s.mulGround(2).sub(4))", () => {
    expect(show(V.dupQuo(s.pow(2).add(1), s.mulGround(2).sub(4)))).toBe("1/2*s + 1");
  });
  it("U.dupExquo(t.pow(2).sub(1), t.sub(1))", () => {
    expect(show(U.dupExquo(t.pow(2).sub(1), t.sub(1)))).toBe("t + 1");
  });
  it("Q.dmpDiv(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2))", () => {
    expect(show(Q.dmpDiv(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2)))).toBe("[1/2*a + 1/2*b - 1/2, -b + 1]");
  });
  it("Q.dmpRem(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2))", () => {
    expect(show(Q.dmpRem(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2)))).toBe("-b + 1");
  });
  it("Q.dmpQuo(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2))", () => {
    expect(show(Q.dmpQuo(a.pow(2).add(a.mul(b)), a.mulGround(2).add(2)))).toBe("1/2*a + 1/2*b - 1/2");
  });
  it("R.dmpExquo(x.pow(2).add(x.mul(y)), x)", () => {
    expect(show(R.dmpExquo(x.pow(2).add(x.mul(y)), x))).toBe("x + y");
  });
  it("U.dupMaxNorm(t.pow(2).neg().add(t.mulGround(2)).sub(3))", () => {
    expect(show(U.dupMaxNorm(t.pow(2).neg().add(t.mulGround(2)).sub(3)))).toBe("3");
  });
  it("R.dmpMaxNorm(x.mul(y).mulGround(2).sub(x).sub(3))", () => {
    expect(show(R.dmpMaxNorm(x.mul(y).mulGround(2).sub(x).sub(3)))).toBe("3");
  });
  it("U.dupL1Norm(t.pow(3).mulGround(2).sub(t.pow(2).mulGround(3))", () => {
    expect(show(U.dupL1Norm(t.pow(3).mulGround(2).sub(t.pow(2).mulGround(3)).add(1)))).toBe("6");
  });
  it("R.dmpL1Norm(x.mul(y).mulGround(2).sub(x).sub(3))", () => {
    expect(show(R.dmpL1Norm(x.mul(y).mulGround(2).sub(x).sub(3)))).toBe("6");
  });
  it("U.dupL2NormSquared(t.pow(3).mulGround(2).sub(t.pow(2).mulGro", () => {
    expect(show(U.dupL2NormSquared(t.pow(3).mulGround(2).sub(t.pow(2).mulGround(3)).add(1)))).toBe("14");
  });
  it("R.dmpL2NormSquared(x.mul(y).mulGround(2).sub(x).sub(3))", () => {
    expect(show(R.dmpL2NormSquared(x.mul(y).mulGround(2).sub(x).sub(3)))).toBe("14");
  });
  it("U.dupExpand([t.pow(2).sub(1), t, U.groundNew(2)])", () => {
    expect(show(U.dupExpand([t.pow(2).sub(1), t, U.groundNew(2)]))).toBe("2*t**3 - 2*t");
  });
  it("R.dmpExpand([x.pow(2).add(y.pow(2)), x.add(1)])", () => {
    expect(show(R.dmpExpand([x.pow(2).add(y.pow(2)), x.add(1)]))).toBe("x**3 + x**2 + x*y**2 + y**2");
  });
  it("V.dupIntegrate(s.pow(2).add(s.mulGround(2)), 2)", () => {
    expect(show(V.dupIntegrate(s.pow(2).add(s.mulGround(2)), 2))).toBe("1/12*s**4 + 1/3*s**3");
  });
  it("V.dupIntegrate(s.pow(2).add(s.mulGround(2)), 0)", () => {
    expect(show(V.dupIntegrate(s.pow(2).add(s.mulGround(2)), 0))).toBe("s**2 + 2*s");
  });
  it("Q.dmpIntegrate(a.add(b.mulGround(2)), 2)", () => {
    expect(show(Q.dmpIntegrate(a.add(b.mulGround(2)), 2))).toBe("1/6*a**3 + a**2*b");
  });
  it("Q.dmpIntegrateIn(a.add(b.mulGround(2)), 1, 1)", () => {
    expect(show(Q.dmpIntegrateIn(a.add(b.mulGround(2)), 1, 1))).toBe("a*b + b**2");
  });
  it("U.dupDiff(t.pow(3).add(t.pow(2).mulGround(2)).add(t.mulGroun", () => {
    expect(show(U.dupDiff(t.pow(3).add(t.pow(2).mulGround(2)).add(t.mulGround(3)).add(4), 2))).toBe("6*t + 4");
  });
  it("U.dupDiff(t.pow(3), 0)", () => {
    expect(show(U.dupDiff(t.pow(3), 0))).toBe("t**3");
  });
  it("R.dmpDiff(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x.m", () => {
    expect(show(R.dmpDiff(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x.mulGround(3)).add(y.pow(2).mulGround(2)).add(y.mulGround(3)).add(1), 1))).toBe("y**2 + 2*y + 3");
  });
  it("R.dmpDiffIn(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x", () => {
    expect(show(R.dmpDiffIn(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x.mulGround(3)).add(y.pow(2).mulGround(2)).add(y.mulGround(3)).add(1), 1, 1))).toBe("2*x*y + 2*x + 4*y + 3");
  });
  it("U.dupEval(t.pow(2).add(t.mulGround(2)).add(3), 2)", () => {
    expect(show(U.dupEval(t.pow(2).add(t.mulGround(2)).add(3), 2))).toBe("11");
  });
  it("R.dmpEval(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y).a", () => {
    expect(show(R.dmpEval(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y).add(2), 2))).toBe("5*y + 8");
  });
  it("R.dmpEvalIn(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y)", () => {
    expect(show(R.dmpEvalIn(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y).add(2), 2, 1))).toBe("7*x + 4");
  });
  it("T.dmpEvalIn(p.mul(q).mul(r).add(1), 2, 1)", () => {
    expect(show(T.dmpEvalIn(p.mul(q).mul(r).add(1), 2, 1))).toBe("2*p*r + 1");
  });
  it("R.dmpDiffEvalIn(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).a", () => {
    expect(show(R.dmpDiffEvalIn(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x.mulGround(3)).add(y.pow(2).mulGround(2)).add(y.mulGround(3)).add(1), 1, 2, 1))).toBe("6*x + 11");
  });
  it("R.dmpEvalTail(x.mul(y).mulGround(2).add(x.mulGround(3)).add(", () => {
    expect(show(R.dmpEvalTail(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y).add(2), [2]))).toBe("7*x + 4");
  });
  it("R.dmpEvalTail(x.mul(y).mulGround(2).add(x.mulGround(3)).add(", () => {
    expect(show(R.dmpEvalTail(x.mul(y).mulGround(2).add(x.mulGround(3)).add(y).add(2), [2, 2]))).toBe("18");
  });
  it("U.dupTrunc(t.pow(3).mulGround(2).add(t.pow(2).mulGround(3)).", () => {
    expect(show(U.dupTrunc(t.pow(3).mulGround(2).add(t.pow(2).mulGround(3)).add(t.mulGround(5)).add(7), 3))).toBe("-t**3 - t + 1");
  });
  it("R.dmpGroundTrunc(x.pow(2).mul(y).mulGround(3).add(x.pow(2).m", () => {
    expect(show(R.dmpGroundTrunc(x.pow(2).mul(y).mulGround(3).add(x.pow(2).mulGround(8)).add(x.mul(y).mulGround(5)), 3))).toBe("-x**2 - x*y");
  });
  it("U.dupMonic(t.pow(2).mulGround(3).add(t.mulGround(6)).add(9))", () => {
    expect(show(U.dupMonic(t.pow(2).mulGround(3).add(t.mulGround(6)).add(9)))).toBe("t**2 + 2*t + 3");
  });
  it("U.dupMonic(U.zero)", () => {
    expect(show(U.dupMonic(U.zero))).toBe("0");
  });
  it("U.dupMonic(t.add(1))", () => {
    expect(show(U.dupMonic(t.add(1)))).toBe("t + 1");
  });
  it("V.dupMonic(s.pow(2).mulGround(3).add(s.mulGround(4)).add(2))", () => {
    expect(show(V.dupMonic(s.pow(2).mulGround(3).add(s.mulGround(4)).add(2)))).toBe("s**2 + 4/3*s + 2/3");
  });
  it("Q.dmpGroundMonic(a.pow(2).mul(b).mulGround(3).add(a.pow(2).m", () => {
    expect(show(Q.dmpGroundMonic(a.pow(2).mul(b).mulGround(3).add(a.pow(2).mulGround(8)).add(a.mul(b).mulGround(5)).add(a.mulGround(6)).add(b.mulGround(2)).add(3)))).toBe("a**2*b + 8/3*a**2 + 5/3*a*b + 2*a + 2/3*b + 1");
  });
  it("U.dupContent(t.pow(2).mulGround(6).add(t.mulGround(8)).add(1", () => {
    expect(show(U.dupContent(t.pow(2).mulGround(6).add(t.mulGround(8)).add(12)))).toBe("2");
  });
  it("R.dmpGroundContent(x.mul(y).mulGround(2).add(x.mulGround(6))", () => {
    expect(show(R.dmpGroundContent(x.mul(y).mulGround(2).add(x.mulGround(6)).add(y.mulGround(4)).add(12)))).toBe("2");
  });
  it("U.dupPrimitive(t.pow(2).mulGround(6).add(t.mulGround(8)).add", () => {
    expect(show(U.dupPrimitive(t.pow(2).mulGround(6).add(t.mulGround(8)).add(12)))).toBe("[2, 3*t**2 + 4*t + 6]");
  });
  it("U.dupPrimitive(t.add(1))", () => {
    expect(show(U.dupPrimitive(t.add(1)))).toBe("[1, t + 1]");
  });
  it("R.dmpGroundPrimitive(x.mul(y).mulGround(2).add(x.mulGround(6", () => {
    expect(show(R.dmpGroundPrimitive(x.mul(y).mulGround(2).add(x.mulGround(6)).add(y.mulGround(4)).add(12)))).toBe("[2, x*y + 3*x + 2*y + 6]");
  });
  it("U.dupExtract(t.pow(2).mulGround(6).add(t.mulGround(12)).add(", () => {
    expect(show(U.dupExtract(t.pow(2).mulGround(6).add(t.mulGround(12)).add(18), t.pow(2).mulGround(4).add(t.mulGround(8)).add(12)))).toBe("[2, 3*t**2 + 6*t + 9, 2*t**2 + 4*t + 6]");
  });
  it("U.dupExtract(t.add(1), t)", () => {
    expect(show(U.dupExtract(t.add(1), t))).toBe("[1, t + 1, t]");
  });
  it("R.dmpGroundExtract(x.mul(y).mulGround(6).add(x.mulGround(12)", () => {
    expect(show(R.dmpGroundExtract(x.mul(y).mulGround(6).add(x.mulGround(12)).add(18), x.mul(y).mulGround(4).add(x.mulGround(8)).add(12)))).toBe("[2, 3*x*y + 6*x + 9, 2*x*y + 4*x + 6]");
  });
  it("R.dupRealImag(x.pow(3).add(x.pow(2)).add(x).add(1))", () => {
    expect(show(R.dupRealImag(x.pow(3).add(x.pow(2)).add(x).add(1)))).toBe("[x**3 + x**2 - 3*x*y**2 + x - y**2 + 1, 3*x**2*y + 2*x*y - y**3 + y]");
  });
  it("U.dupMirror(t.pow(3).add(t.pow(2).mulGround(2)).sub(t.mulGro", () => {
    expect(show(U.dupMirror(t.pow(3).add(t.pow(2).mulGround(2)).sub(t.mulGround(4)).add(2)))).toBe("-t**3 + 2*t**2 + 4*t + 2");
  });
  it("U.dupScale(t.pow(2).sub(t.mulGround(2)).add(1), 2)", () => {
    expect(show(U.dupScale(t.pow(2).sub(t.mulGround(2)).add(1), 2))).toBe("4*t**2 - 4*t + 1");
  });
  it("U.dupShift(t.pow(2).sub(t.mulGround(2)).add(1), 2)", () => {
    expect(show(U.dupShift(t.pow(2).sub(t.mulGround(2)).add(1), 2))).toBe("t**2 + 2*t + 1");
  });
  it("R.dmpShift(x.pow(2).mul(y).add(x.pow(2).mulGround(2)).add(x)", () => {
    expect(show(R.dmpShift(x.pow(2).mul(y).add(x.pow(2).mulGround(2)).add(x).add(1), [1, 2]))).toBe("x**2*y + 4*x**2 + 2*x*y + 9*x + y + 6");
  });
  it("U.dupTransform(t.pow(2).sub(t.mulGround(2)).add(1), t.pow(2)", () => {
    expect(show(U.dupTransform(t.pow(2).sub(t.mulGround(2)).add(1), t.pow(2).add(1), t.sub(1)))).toBe("t**4 - 2*t**3 + 5*t**2 - 4*t + 4");
  });
  it("U.dupTransform(U.zero, t.pow(2).add(1), t.sub(1))", () => {
    expect(show(U.dupTransform(U.zero, t.pow(2).add(1), t.sub(1)))).toBe("0");
  });
  it("U.dupCompose(t.pow(2).add(t), t.sub(1))", () => {
    expect(show(U.dupCompose(t.pow(2).add(t), t.sub(1)))).toBe("t**2 - t");
  });
  it("R.dmpCompose(x.mul(y).add(x.mulGround(2)).add(y), y)", () => {
    expect(show(R.dmpCompose(x.mul(y).add(x.mulGround(2)).add(y), y))).toBe("y**2 + 3*y");
  });
  it("U.dupDecompose(t.pow(4).sub(t.pow(3).mulGround(2)).add(t.pow", () => {
    expect(show(U.dupDecompose(t.pow(4).sub(t.pow(3).mulGround(2)).add(t.pow(2))))).toBe("[t**2, t**2 - t]");
  });
  it("U.dupSignVariations(t.pow(4).sub(t.pow(2)).sub(t).add(1))", () => {
    expect(show(U.dupSignVariations(t.pow(4).sub(t.pow(2)).sub(t).add(1)))).toBe("2");
  });
  it("V.dupClearDenoms(s.mulGround(sj.Rational.of(1, 2)).add(sj.Ra", () => {
    expect(show(V.dupClearDenoms(s.mulGround(sj.Rational.of(1, 2)).add(sj.Rational.of(1, 3))))).toBe("[6, 3*s + 2]");
  });
  it("V.dupClearDenoms(s.mulGround(sj.Rational.of(1, 2)).add(sj.Ra", () => {
    expect(show(V.dupClearDenoms(s.mulGround(sj.Rational.of(1, 2)).add(sj.Rational.of(1, 3)), true))).toBe("[6, 3*s + 2]");
  });
  it("V.dupClearDenoms(s.add(1))", () => {
    expect(show(V.dupClearDenoms(s.add(1)))).toBe("[1, s + 1]");
  });
  it("U.dupClearDenoms(t.add(1))", () => {
    expect(show(U.dupClearDenoms(t.add(1)))).toBe("[1, t + 1]");
  });
  it("Q.dmpClearDenoms(a.mulGround(sj.Rational.of(1, 2)).add(b.mul", () => {
    expect(show(Q.dmpClearDenoms(a.mulGround(sj.Rational.of(1, 2)).add(b.mulGround(sj.Rational.of(1, 3))).add(1)))).toBe("[6, 3*a + 2*b + 6]");
  });
  it("V.dupRevert(V.one.sub(s.pow(2).mulGround(sj.Rational.of(1, 2", () => {
    expect(show(V.dupRevert(V.one.sub(s.pow(2).mulGround(sj.Rational.of(1, 2))).add(s.pow(4).mulGround(sj.Rational.of(1, 24))).sub(s.pow(6).mulGround(sj.Rational.of(1, 720))), 8))).toBe("61/720*s**6 + 5/24*s**4 + 1/2*s**2 + 1");
  });
  it("U.dupRevert(U.one.add(t), 4)", () => {
    expect(show(U.dupRevert(U.one.add(t), 4))).toBe("-t**3 + t**2 - t + 1");
  });
  it("U.dupSqfP(t.pow(2).sub(t.mulGround(2)).add(1))", () => {
    expect(show(U.dupSqfP(t.pow(2).sub(t.mulGround(2)).add(1)))).toBe("False");
  });
  it("U.dupSqfP(U.zero)", () => {
    expect(show(U.dupSqfP(U.zero))).toBe("True");
  });
  it("R.dmpSqfP(x.pow(2).add(y.pow(2)))", () => {
    expect(show(R.dmpSqfP(x.pow(2).add(y.pow(2))))).toBe("True");
  });
  it("R.dmpSqfP(x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2)))", () => {
    expect(show(R.dmpSqfP(x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2))))).toBe("False");
  });
  it("R.dmpSqfP(y.pow(2).add(1))", () => {
    expect(show(R.dmpSqfP(y.pow(2).add(1)))).toBe("True");
  });
  it("U.dupSqfPart(t.pow(3).sub(t.mulGround(3)).sub(2))", () => {
    expect(show(U.dupSqfPart(t.pow(3).sub(t.mulGround(3)).sub(2)))).toBe("t**2 - t - 2");
  });
  it("U.dupSqfPart(t.pow(2).neg().add(t.mulGround(2)).sub(1))", () => {
    expect(show(U.dupSqfPart(t.pow(2).neg().add(t.mulGround(2)).sub(1)))).toBe("t - 1");
  });
  it("V.dupSqfPart(s.pow(2).mulGround(2).add(s.mulGround(4)).add(2", () => {
    expect(show(V.dupSqfPart(s.pow(2).mulGround(2).add(s.mulGround(4)).add(2)))).toBe("s + 1");
  });
  it("U.dupSqfPart(U.zero)", () => {
    expect(show(U.dupSqfPart(U.zero))).toBe("0");
  });
  it("R.dmpSqfPart(x.pow(3).add(x.pow(2).mul(y).mulGround(2)).add(", () => {
    expect(show(R.dmpSqfPart(x.pow(3).add(x.pow(2).mul(y).mulGround(2)).add(x.mul(y.pow(2)))))).toBe("x**2 + x*y");
  });
  it("U.dupSqfList(t.pow(5).mulGround(2).add(t.pow(4).mulGround(16", () => {
    expect(show(U.dupSqfList(t.pow(5).mulGround(2).add(t.pow(4).mulGround(16)).add(t.pow(3).mulGround(50)).add(t.pow(2).mulGround(76)).add(t.mulGround(56)).add(16)))).toBe("[2, [[t + 1, 2], [t + 2, 3]]]");
  });
  it("U.dupSqfList(t.pow(5).mulGround(2).add(t.pow(4).mulGround(16", () => {
    expect(show(U.dupSqfList(t.pow(5).mulGround(2).add(t.pow(4).mulGround(16)).add(t.pow(3).mulGround(50)).add(t.pow(2).mulGround(76)).add(t.mulGround(56)).add(16), true))).toBe("[2, [[1, 1], [t + 1, 2], [t + 2, 3]]]");
  });
  it("U.dupSqfList(t.pow(2).neg().add(t.mulGround(2)).sub(1))", () => {
    expect(show(U.dupSqfList(t.pow(2).neg().add(t.mulGround(2)).sub(1)))).toBe("[-1, [[t - 1, 2]]]");
  });
  it("U.dupSqfList(U.groundNew(3))", () => {
    expect(show(U.dupSqfList(U.groundNew(3)))).toBe("[3, []]");
  });
  it("V.dupSqfList(s.pow(2).mulGround(2).add(s.mulGround(4)).add(2", () => {
    expect(show(V.dupSqfList(s.pow(2).mulGround(2).add(s.mulGround(4)).add(2)))).toBe("[2, [[s + 1, 2]]]");
  });
  it("R.dmpSqfList(x.pow(5).add(x.pow(4).mul(y).mulGround(2)).add(", () => {
    expect(show(R.dmpSqfList(x.pow(5).add(x.pow(4).mul(y).mulGround(2)).add(x.pow(3).mul(y.pow(2)))))).toBe("[1, [[x + y, 2], [x, 3]]]");
  });
  it("R.dmpSqfList(x.pow(5).add(x.pow(4).mul(y).mulGround(2)).add(", () => {
    expect(show(R.dmpSqfList(x.pow(5).add(x.pow(4).mul(y).mulGround(2)).add(x.pow(3).mul(y.pow(2))), true))).toBe("[1, [[1, 1], [x + y, 2], [x, 3]]]");
  });
  it("R.dmpSqfList(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(", () => {
    expect(show(R.dmpSqfList(x.mul(y.pow(2)).add(x.mul(y).mulGround(2)).add(x)))).toBe("[1, [[x, 1], [y + 1, 2]]]");
  });
  it("R.dmpSqfList(y.pow(2).add(y.mulGround(2)).add(1))", () => {
    expect(show(R.dmpSqfList(y.pow(2).add(y.mulGround(2)).add(1)))).toBe("[1, [[y + 1, 2]]]");
  });
  it("R.dmpSqfList(R.zero)", () => {
    expect(show(R.dmpSqfList(R.zero))).toBe("[0, []]");
  });
  it("U.dupSqfListInclude(t.pow(5).mulGround(2).add(t.pow(4).mulGr", () => {
    expect(show(U.dupSqfListInclude(t.pow(5).mulGround(2).add(t.pow(4).mulGround(16)).add(t.pow(3).mulGround(50)).add(t.pow(2).mulGround(76)).add(t.mulGround(56)).add(16)))).toBe("[[2, 1], [t + 1, 2], [t + 2, 3]]");
  });
  it("U.dupSqfListInclude(t.mulGround(2).add(2))", () => {
    expect(show(U.dupSqfListInclude(t.mulGround(2).add(2)))).toBe("[[2*t + 2, 1]]");
  });
  it("R.dmpSqfListInclude(x.pow(5).add(x.pow(4).mul(y).mulGround(2", () => {
    expect(show(R.dmpSqfListInclude(x.pow(5).add(x.pow(4).mul(y).mulGround(2)).add(x.pow(3).mul(y.pow(2)))))).toBe("[[1, 1], [x + y, 2], [x, 3]]");
  });
  it("U.dupGffList(t.pow(5).add(t.pow(4).mulGround(2)).sub(t.pow(3", () => {
    expect(show(U.dupGffList(t.pow(5).add(t.pow(4).mulGround(2)).sub(t.pow(3)).sub(t.pow(2).mulGround(2))))).toBe("[[t, 1], [t + 2, 4]]");
  });
  it("U.dupGffList(t.mul(t.add(1)))", () => {
    expect(show(U.dupGffList(t.mul(t.add(1))))).toBe("[[t + 1, 2]]");
  });
  it("U.dmpGffList(t.pow(2).add(t))", () => {
    expect(show(U.dmpGffList(t.pow(2).add(t)))).toBe("[[t + 1, 2]]");
  });
  it("R.dmpFactorList(x.pow(2).mulGround(2).sub(y.pow(2).mulGround", () => {
    expect(show(R.dmpFactorList(x.pow(2).mulGround(2).sub(y.pow(2).mulGround(2))))).toBe("[2, [[x - y, 1], [x + y, 1]]]");
  });
  it("U.dupFactorList(t.pow(4).mulGround(2).sub(2))", () => {
    expect(show(U.dupFactorList(t.pow(4).mulGround(2).sub(2)))).toBe("[2, [[t - 1, 1], [t + 1, 1], [t**2 + 1, 1]]]");
  });
  it("U.dupZzFactor(t.pow(4).mulGround(2).sub(2))", () => {
    expect(show(U.dupZzFactor(t.pow(4).mulGround(2).sub(2)))).toBe("[2, [[t - 1, 1], [t + 1, 1], [t**2 + 1, 1]]]");
  });
  it("R.dmpZzFactor(x.pow(2).mulGround(2).sub(y.pow(2).mulGround(2", () => {
    expect(show(R.dmpZzFactor(x.pow(2).mulGround(2).sub(y.pow(2).mulGround(2))))).toBe("[2, [[x - y, 1], [x + y, 1]]]");
  });
  it("R.dmpIrreducibleP(x.pow(2).add(y.pow(2)))", () => {
    expect(show(R.dmpIrreducibleP(x.pow(2).add(y.pow(2))))).toBe("True");
  });
  it("R.dmpIrreducibleP(x.pow(2).sub(y.pow(2)))", () => {
    expect(show(R.dmpIrreducibleP(x.pow(2).sub(y.pow(2))))).toBe("False");
  });
  it("U.dupZzMignotteBound(t.pow(2).mulGround(2).add(t.mulGround(3", () => {
    expect(show(U.dupZzMignotteBound(t.pow(2).mulGround(2).add(t.mulGround(3)).add(4)))).toBe("6");
  });
  it("U.dupZzMignotteBound(t.pow(3).neg().add(t.pow(2).mulGround(1", () => {
    expect(show(U.dupZzMignotteBound(t.pow(3).neg().add(t.pow(2).mulGround(14)).add(t.mulGround(56)).add(64)))).toBe("152");
  });
  it("U.dupCyclotomicP(t.pow(4).add(t.pow(3)).add(t.pow(2)).add(t)", () => {
    expect(show(U.dupCyclotomicP(t.pow(4).add(t.pow(3)).add(t.pow(2)).add(t).add(1)))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(2).sub(t).add(1))", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).sub(t).add(1)))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(2).add(t).add(1), true)", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).add(t).add(1), true))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(2).add(1))", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).add(1)))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(4).add(1))", () => {
    expect(show(U.dupCyclotomicP(t.pow(4).add(1)))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(4).add(t.pow(2)).add(1))", () => {
    expect(show(U.dupCyclotomicP(t.pow(4).add(t.pow(2)).add(1)))).toBe("False");
  });
  it("U.dupCyclotomicP(t.pow(4).add(t.pow(2)).add(1), true)", () => {
    expect(show(U.dupCyclotomicP(t.pow(4).add(t.pow(2)).add(1), true))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(2).add(t.mulGround(2)).add(1), true)", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).add(t.mulGround(2)).add(1), true))).toBe("True");
  });
  it("U.dupCyclotomicP(t.pow(2).add(t.mulGround(3)).add(1), true)", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).add(t.mulGround(3)).add(1), true))).toBe("False");
  });
  it("U.dupCyclotomicP(t.mulGround(2).add(1))", () => {
    expect(show(U.dupCyclotomicP(t.mulGround(2).add(1)))).toBe("False");
  });
  it("U.dupCyclotomicP(t.pow(2).add(2))", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).add(2)))).toBe("False");
  });
  it("U.dupCyclotomicP(t.pow(2).sub(1))", () => {
    expect(show(U.dupCyclotomicP(t.pow(2).sub(1)))).toBe("False");
  });
  it("V.dupCyclotomicP(s.pow(2).add(s).add(1))", () => {
    expect(show(V.dupCyclotomicP(s.pow(2).add(s).add(1)))).toBe("True");
  });
  it("V.dupCyclotomicP(s.pow(2).add(s.mulGround(sj.Rational.of(1, ", () => {
    expect(show(V.dupCyclotomicP(s.pow(2).add(s.mulGround(sj.Rational.of(1, 2))).add(1)))).toBe("False");
  });
  it("R.dmpInnerGcd(x.pow(2).sub(y.pow(2)), x.pow(2).add(x.mul(y).", () => {
    expect(show(R.dmpInnerGcd(x.pow(2).sub(y.pow(2)), x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2))))).toBe("[x + y, x - y, x + y]");
  });
  it("R.dmpInnerGcd(R.zero, R.zero)", () => {
    expect(show(R.dmpInnerGcd(R.zero, R.zero))).toBe("[0, 0, 0]");
  });
  it("U.dupInnerGcd(t.pow(2).sub(1), t.neg().add(1))", () => {
    expect(show(U.dupInnerGcd(t.pow(2).sub(1), t.neg().add(1)))).toBe("[t - 1, t + 1, -1]");
  });
  it("V.dupGcd(s.pow(2).mulGround(2).sub(2), s.mulGround(4).add(4)", () => {
    expect(show(V.dupGcd(s.pow(2).mulGround(2).sub(2), s.mulGround(4).add(4)))).toBe("s + 1");
  });
  it("R.dmpGcd(x.pow(2).sub(y.pow(2)), x.sub(y))", () => {
    expect(show(R.dmpGcd(x.pow(2).sub(y.pow(2)), x.sub(y)))).toBe("x - y");
  });
  it("R.dmpLcm(x.pow(2).sub(y.pow(2)), x.pow(2).add(x.mul(y).mulGr", () => {
    expect(show(R.dmpLcm(x.pow(2).sub(y.pow(2)), x.pow(2).add(x.mul(y).mulGround(2)).add(y.pow(2))))).toBe("x**3 + x**2*y - x*y**2 - y**3");
  });
  it("R.dmpLcm(x.neg(), y)", () => {
    expect(show(R.dmpLcm(x.neg(), y))).toBe("-x*y");
  });
  it("R.dmpLcm(R.zero, y)", () => {
    expect(show(R.dmpLcm(R.zero, y))).toBe("0");
  });
  it("V.dupLcm(s.pow(2).mulGround(2).sub(2), s.mulGround(4).add(4)", () => {
    expect(show(V.dupLcm(s.pow(2).mulGround(2).sub(2), s.mulGround(4).add(4)))).toBe("s**2 - 1");
  });
  it("R.dmpResultant(x.pow(2).add(y), x.sub(y))", () => {
    expect(show(R.dmpResultant(x.pow(2).add(y), x.sub(y)))).toBe("y**2 + y");
  });
  it("U.dupResultant(t.pow(2).add(1), t.sub(2))", () => {
    expect(show(U.dupResultant(t.pow(2).add(1), t.sub(2)))).toBe("5");
  });
  it("R.dmpDiscriminant(x.pow(2).add(y))", () => {
    expect(show(R.dmpDiscriminant(x.pow(2).add(y)))).toBe("-4*y");
  });
  it("U.dupDiscriminant(t.pow(2).add(1))", () => {
    expect(show(U.dupDiscriminant(t.pow(2).add(1)))).toBe("-4");
  });
  it("V.dupGcdex(s.pow(2).sub(1), s.pow(2).add(s))", () => {
    expect(show(V.dupGcdex(s.pow(2).sub(1), s.pow(2).add(s)))).toBe("[-1, 1, s + 1]");
  });
  it("V.dupHalfGcdex(s.pow(2).sub(1), s.pow(2).add(s))", () => {
    expect(show(V.dupHalfGcdex(s.pow(2).sub(1), s.pow(2).add(s)))).toBe("[-1, s + 1]");
  });
  it("V.dupInvert(s.add(1), s.pow(2).add(1))", () => {
    expect(show(V.dupInvert(s.add(1), s.pow(2).add(1)))).toBe("-1/2*s + 1/2");
  });
  it("V.dupSturm(s.pow(3).sub(s))", () => {
    expect(show(V.dupSturm(s.pow(3).sub(s)))).toBe("[s**3 - s, 3*s**2 - 1, 2/3*s, 1]");
  });
});

describe('ground domain operations', () => {
  const W = sj.symbols('w')[0];
  const ZW = ZZ.polyRing(W);
  const QW = QQ.fracField(W);
  const n = (k: number, d = 1): sj.Expr => sj.Rational.of(k, d);
  it('divide in ZZ, QQ and polynomial rings', () => {
    expect(show(C.groundQuo(ZZ, n(-7), n(2)))).toBe('-4');
    expect(show(C.groundRem(ZZ, n(-7), n(2)))).toBe('1');
    expect(show(C.groundQuo(QQ, n(1), n(2)))).toBe('1/2');
    expect(show(C.groundRem(QQ, n(1), n(2)))).toBe('0');
    expect(show(C.groundQuo(ZW, sj.mul(2, W), W))).toBe('2');
    expect(show(C.groundRem(ZW, sj.mul(2, W), W))).toBe('0');
    expect(() => C.groundExquo(ZW, W, sj.add(W, 1))).toThrow(sj.ExactQuotientFailed);
    expect(() => C.groundExquo(ZZ, n(3), n(2))).toThrow(sj.ExactQuotientFailed);
    expect(() => C.groundQuo(ZZ, n(3), n(0))).toThrow('division by zero');
    expect(() => C.groundRem(ZZ, n(3), n(0))).toThrow('division by zero');
    expect(() => C.groundExquo(ZZ, n(3), n(0))).toThrow('division by zero');
  });
  it('take gcds and lcms', () => {
    expect(show(C.groundGcd(QQ, n(2, 3), n(4, 5)))).toBe('2/15');
    expect(show(C.groundLcm(QQ, n(2, 3), n(4, 5)))).toBe('4');
    expect(show(C.groundGcd(ZW, sj.sub(sj.pow(W, 2), 1), sj.add(W, 1)))).toBe('w + 1');
    expect(show(C.groundLcm(ZW, sj.sub(W, 1), sj.add(W, 1)))).toBe('w**2 - 1');
    expect(show(C.groundLcm(ZW, n(0), W))).toBe('0');
    expect(show(C.groundGcd(EX, sj.sqrt(2), n(2)))).toBe('1');
    expect(show(C.groundLcm(EX, sj.sqrt(2), n(2)))).toBe('2*sqrt(2)');
  });
  it('know signs, units and rings', () => {
    expect(C.groundIsNegative(QW, sj.mul(sj.neg(W), sj.pow(sj.add(W, 1), -1)))).toBe(true);
    expect(C.groundIsNegative(EX, sj.neg(sj.sqrt(2)))).toBe(true);
    expect(C.groundRing(QQ)).toBe(ZZ);
    expect(C.groundRing(RR)).toBe(RR);
    expect(C.hasAssocRing(ZZ)).toBe(true);
    expect(C.groundIsUnit(ZZ, n(-1))).toBe(true);
    expect(C.groundIsUnit(ZZ, n(2))).toBe(false);
    expect(() => C.groundDenom(sj.sqrt(2))).toThrow('expected a rational number');
  });
});

describe('compatibility methods', () => {
  it('follow the SymPy doctests', () => {
    // SymPy: R.dmp_trunc(3*x**2*y + 8*x**2 + 5*x*y + 6*x + 2*y + 3, y - 1) == 11*x**2 + 11*x + 5
    const [Ry, yy] = ring('y', ZZ) as [PolyRing, PolyElement];
    const f = x.pow(2).mul(y).mulGround(3).add(x.pow(2).mulGround(8)).add(x.mul(y).mulGround(5)).add(x.mulGround(6)).add(y.mulGround(2)).add(3);
    expect(R.dmpTrunc(f, yy.sub(1)).toString()).toBe('11*x**2 + 11*x + 5');
    expect(() => R.dmpTrunc(f, a)).toThrow('not generators of the ring');
    void Ry;
    // SymPy: (2, [(x, 1), (x*y + y, 2)]) over QQ, printed MPQ(2,1)
    expect(show(Q.dmpSqfList(a.pow(3).mul(b.pow(2)).mulGround(2).add(a.pow(2).mul(b.pow(2)).mulGround(4)).add(a.mul(b.pow(2)).mulGround(2))))).toBe('[2, [[a, 1], [a*b + b, 2]]]');
    expect(show(U.dupZzMignotteBound(t.add(1)))).toBe('2');
    expect(show(U.dupEval(U.zero, 3))).toBe('0');
    // SymPy fails with AttributeError (the ring R[1:] of a univariate ring is the domain); the value is the ground element
    expect(show(U.dmpEval(t.pow(2).add(1), 2))).toBe('5');
    // SymPy fails on R[:-0]; no value is replaced
    expect(show(R.dmpEvalTail(x.add(y), []))).toBe('x + y');
    const [E, u] = ring('u', EX) as [PolyRing, PolyElement];
    expect(E.dupCyclotomicP(u.pow(2).add(u).add(1))).toBe(false);
  });
  it('reject invalid input', () => {
    expect(() => R.dmpPow(x, -1)).toThrow('negative power');
    expect(() => U.dupPdiv(t, U.zero)).toThrow('polynomial division');
    expect(() => U.dupRrDiv(t, U.zero)).toThrow('polynomial division');
    expect(() => U.dupPexquo(t, t.add(1))).toThrow(sj.ExactQuotientFailed);
    expect(() => U.dupExquo(t, t.add(1))).toThrow(sj.ExactQuotientFailed);
    expect(() => R.dmpDiffIn(x, 1, 2)).toThrow('0 <= j <= 1');
    expect(() => U.dupRealImag(t)).toThrow('two generators');
    expect(() => ring('x,y', RR)[0].dupRealImag(ring('x,y', RR)[1] as PolyElement)).toThrow('not supported');
    expect(() => R.dupRealImag(x.mul(y))).toThrow('univariate');
    expect(() => U.dupRevert(t.add(2), 4)).toThrow('not a unit');
    expect(() => U.dupGffList(U.zero)).toThrow("doesn't exist");
    expect(() => R.dmpGffList(x)).toThrow(sj.MultivariatePolynomialError);
    expect(() => new PolyRing([sj.sin(Y)]).dmpResultant(new PolyRing([sj.sin(Y)]).gens[0] as PolyElement, new PolyRing([sj.sin(Y)]).one)).toThrow('must be a symbol');
  });
});
