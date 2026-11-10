// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References from SymPy 1.14.0 (scripts/gen_numberfields.py): power bases, submodules and their
// elements (arithmetic, representation, reduction), module homomorphisms and find_min_poly.
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Dummy, PythonMPQ, Rational, Sym, parseExpr as P, sqrt } from '../../../src';
import { AlgebraicField } from '../../../src/polys/domains/algebraicfield';
import { GF } from '../../../src/polys/domains/finitefield';
import { QQ, ZZ } from '../../../src/polys/domains';
import { DM, DomainMatrix } from '../../../src/polys/matrices/domainmatrix';
import { AlgebraicNumber } from '../../../src/polys/numberfields';
import '../../../src/polys/numberfields/basis';
import { ClosureFailure, MissingUnityError, StructureError } from '../../../src/polys/numberfields/exceptions';
import {
  EndomorphismRing,
  InnerEndomorphism,
  ModuleElement,
  ModuleEndomorphism,
  ModuleHomomorphism,
  PowerBasis,
  PowerBasisElement,
  Submodule,
  findMinPoly,
  isSqMaxrankHNF,
  makeModElt,
  toCol,
} from '../../../src/polys/numberfields/modules';
import { UnificationFailed } from '../../../src/polys/polyerrors';
import { NotImplementedError } from '../../../src/core/errors';
import { Poly } from '../../../src/polys/sympoly';

const ref = JSON.parse(readFileSync(new URL('./numberfields.references.json', import.meta.url), 'utf8'));
const m = ref.modules;
const x = new Sym('x');
const poly = (s: string): Poly => Poly.from(P(s), [x]);
const s = (v: unknown): string => String(v);
const eye = (n: number, k: number): DomainMatrix => DomainMatrix.eye(n, ZZ).rscalarmul(Rational.of(k));
const tab = (M: Map<number, Map<number, bigint[]>>, n: number): number[][][] =>
  Array.from({ length: n }, (_, u) => Array.from({ length: n - u }, (_, v) => (M.get(u)?.get(u + v) ?? []).map(Number)));

const T5 = poly('x**4 + x**3 + x**2 + x + 1');
const A = new PowerBasis(T5);
const B = A.submoduleFromMatrix(eye(4, 2), 3);
const C = A.submoduleFromMatrix(eye(4, 3));
const e = A.call(toCol([0, 2, 0, 0]), 3);
const f = A.call(toCol([0, 0, 0, 7]), 5);
const g = C.call(toCol([1, 1, 1, 1]));
const h = A.call(toCol([1, 2, 3, 4]), 6);
const D = B.submoduleFromMatrix(DM([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 1, 1]], ZZ).transpose());
const d = D.call(toCol([1, 2, 3, 4]));

describe('PowerBasis and Submodule', () => {
  it('prints and multiplies basis elements', () => {
    expect([s(A), s(B), A.n, B.n]).toEqual([m.A, m.B, 4, 4]);
    expect(tab(A.multTab(), 4)).toEqual(m.multab);
    expect(A.parent).toBeUndefined();
    expect(A.numberField).toBeUndefined();
    expect(B.numberField).toBeUndefined();
    expect([A.startsWithUnity(), B.startsWithUnity(), C.startsWithUnity()]).toEqual([true, false, false]);
    expect(A.equals(new PowerBasis(poly('x**4 + x**3 + x**2 + x + 1')))).toBe(true);
    expect(A.equals(B)).toBe(false);
    expect(B.parent).toBe(A);
    expect(B.isPowerBasisSubmodule()).toBe(true);
    expect(D.isPowerBasisSubmodule()).toBe(false);
    expect([D.ancestors(true), D.ancestors()]).toEqual([[A, B, D], [A, B]]);
    expect(D.powerBasisAncestor()).toBe(A);
    expect(s(A.one())).toBe('[1, 0, 0, 0]');
    expect(s(B.coeffs)).toBe('2,0,0,0,0,2,0,0,0,0,2,0,0,0,0,2');
    expect(B.denom).toBe(3n);
    expect(A.wholeSubmodule().matrix.equals(DomainMatrix.eye(4, ZZ))).toBe(true);
    expect(A.endomorphismRing()).toBeInstanceOf(EndomorphismRing);
  });
  it('computes element arithmetic like SymPy', () => {
    const got: Record<string, unknown> = {
      'e+f': e.add(f), 'e-f': e.sub(f), 'e-g': e.sub(g), 'e+7/10': e.add(new PythonMPQ(7, 10)), 'e*f': e.mul(f),
      'e**2': e.pow(2), 'e**0': e.pow(0), 'e**5': e.pow(5), 'e**-2': e.pow(-2), 'f//g': f.floordiv(g), 'f*2/3': f.mul(new PythonMPQ(2, 3)),
      'f//3': f.floordiv(3), 'h.reduced': h.reduced(), 'h%2': h.mod(2), 'g*g': g.mul(g), 'g+1': g.add(1),
      'd+h': d.add(h), 'd*e': d.mul(e), 'd.to_parent': d.toParent(), 'd.over': d.overPowerBasis(),
      'h.mod3': h.reducedModP(3), 'B(1)': B.call(1), 'B(1)+B(2)': B.call(1).add(B.call(2)),
    };
    expect(Object.fromEntries(Object.entries(got).map(([k, v]) => [k, s(v)]))).toEqual(m.ops);
  });
  it('converts power basis elements', () => {
    expect([s(h.poly().asExpr()), s(h.numerator().asExpr()), s(h.norm()), s(h.inverse()), s(h.toANP()), h.isRational]).toEqual([m.h_poly, m.h_numerator, m.h_norm, m.h_inverse, m.h_anp, m.h_rational]);
    expect(A.call(0).mul(5).floordiv(2).overPowerBasis().isRational).toBe(true);
    expect([s(e.unify(f)), s(e.sub(1)), e.pow(1)]).toEqual(['[0, 2, 0, 0]/3,[0, 0, 0, 7]/5', '[-3, 2, 0, 0]/3', e]);
    const plain = new ModuleElement(A, toCol([1, 2, 3, 4]));
    expect(plain.overPowerBasis()).toBeInstanceOf(PowerBasisElement);
    expect(s(h.asExpr())).toBe(s(h.poly().asExpr()));
    expect(s(h.generator)).toBe('x');
    expect(h.T).toBe(A.T);
    expect([g.equiv(A.call(toCol([3, 3, 3, 3]))), g.equiv(e), A.call(0).mul(3).equiv(3), C.call(0).mul(1).equiv(3)]).toEqual(m.g_equiv);
    expect(A.call(0).equiv(A.call(0))).toBe(true);
    expect(s(h.column())).toBe('DomainMatrix([[1], [2], [3], [4]], (4, 1), ZZ)');
    expect(s(h.column(QQ))).toBe('DomainMatrix([[1], [2], [3], [4]], (4, 1), QQ)');
    expect(s(A.elementFromPoly(poly('x**6 + 1/2')))).toBe('[1, 2, 0, 0]/2');
    expect(s(A.elementFromPoly(poly('x**5 - 1')))).toBe('[0, 0, 0, 0]');
    expect(s(ModuleElement.fromIntList(A, [1, 2, 3, 4], 2))).toBe('[1, 2, 3, 4]/2');
    expect(makeModElt(B, toCol([1, 0, 0, 0]))).not.toBeInstanceOf(PowerBasisElement);
    expect(() => h.toAlgNum()).toThrow(StructureError);
    expect(() => B.call(0).pow(-1)).toThrow(TypeError);
    expect(() => e.pow(0.5)).toThrow(TypeError);
    expect(() => e.floordiv(0)).toThrow(RangeError);
    expect(() => A.call(0).toParent()).toThrow(RangeError);
  });
  it('represents and reduces elements', () => {
    expect(s(B.represent(A.call(toCol([2, 4, 6, 8]), 3)))).toBe(m.B_represent);
    expect(s(D.represent(A.call(toCol([2, 4, 6, 8]), 3)))).toBe(m.D_represent);
    expect(s(B.represent(B.call(2)))).toBe('DomainMatrix([[0], [0], [1], [0]], (4, 1), ZZ)');
    expect(s(A.represent(A.call(1)))).toBe('DomainMatrix([[0], [1], [0], [0]], (4, 1), ZZ)');
    expect(() => B.represent(A.call(toCol([1, 2, 2, 2])))).toThrow(new ClosureFailure('Element in QQ-span but not ZZ-span of this basis.'));
    const E2 = A.submoduleFromMatrix(DM([[1, 0, 0, 0]], ZZ).transpose());
    expect(() => E2.represent(A.call(1))).toThrow(new ClosureFailure('Element outside QQ-span of this basis.'));
    expect(() => A.represent(h)).toThrow(ClosureFailure);
    expect(() => B.represent(new PowerBasis(poly('x**2 + 1')).call(0))).toThrow(new ClosureFailure('Element outside ancestor chain of this module.'));
  });
  it('makes submodules', () => {
    const gens = [A.call(0), A.call(1).mul(2), A.call(2).mul(3), A.call(3).mul(4).floordiv(5)];
    expect(s(A.submoduleFromGens(gens))).toBe(m.gens);
    expect(s(A.submoduleFromGens(gens, { hnf: false }))).toBe(m.gens_nohnf);
    expect(s(A.submoduleFromGens([0, 1, 2, 3].map((i) => A.call(i).mul(2)), { hnfModulus: 16 }))).toBe(m.gens_mod);
    expect(s(A.submoduleFromGens([A.call(1)]))).toBe('Submodule[[0, 1, 0, 0]]');
    const got: Record<string, unknown> = {
      'B+C': B.add(C), 'B*C': B.mul(C), 'B*e': B.mul(e), 'B*2/3': B.mul(new PythonMPQ(2, 3)), 'B**2': B.pow(2), 'B**3': B.pow(3),
    };
    for (const [k, v] of Object.entries(got)) expect(s(v), k).toBe(m[k]);
    expect(B.mul(1)).toBe(B);
    expect(B.pow(1)).toBe(B);
    expect(s(B.add(C, { hnf: false }))).toBe('Submodule[[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2], [9, 0, 0, 0], [0, 9, 0, 0], [0, 0, 9, 0], [0, 0, 0, 9]]/3');
    expect(s(A.submoduleFromMatrix(eye(4, 6), 4).reduced())).toBe(m.B_reduced);
    expect(C.reduced()).toBe(C);
    expect(A.submoduleFromMatrix(eye(4, 2), 3).reduced().denom).toBe(3n);
    expect(s(B.QQMatrix)).toBe('DomainMatrix([[2/3, 0, 0, 0], [0, 2/3, 0, 0], [0, 0, 2/3, 0], [0, 0, 0, 2/3]], (4, 4), QQ)');
    expect([B.equals(C), B.equals(A.submoduleFromMatrix(eye(4, 2), 3)), B.equals(D)]).toEqual([m.B_eq_C, m.B_eq_B, false]);
    // the discarded submodule keeps the slices of C's multiplication table, computed for g*g
    expect([s(C.discardBefore(2)), tab(C.discardBefore(2).multTab(), 2), tab(C.multTab(), 4)]).toEqual([m.C_discard, m.C_discard_multab, m.C_multab]);
    expect(s(A.submoduleFromMatrix(eye(4, 3)).discardBefore(3))).toBe('Submodule[[0, 0, 0, 3]]');
    const C2 = A.submoduleFromMatrix(eye(4, 3));
    C2.computeMultTab();
    expect(tab(C2.multTab(), 4)).toEqual(m.C_multab);
    A.computeMultTab();
    expect(tab(A.multTab(), 4)).toEqual(m.multab);
    expect(new Submodule(A, eye(4, 1)).isSqMaxrankHNF()).toBe(true);
  });
  it('reduces modulo a submodule in Hermite normal form', () => {
    const k = new AlgebraicField(QQ, new AlgebraicNumber(new Sym('r'), [1, 0], { minpoly: Poly.from(P('t**3 + t**2 - 2*t + 8'), [new Sym('t')]) }));
    const Zk = k.maximalOrder();
    const Ak = Zk.powerBasisAncestor();
    const Bk = Zk.mul(Ak.call(2).sub(Ak.call(0).mul(3)));
    expect([s(Bk), s(Bk.reduceElement(Ak.call(2)))]).toEqual([m.Bk, m.Bk_reduce]);
    expect(Ak.numberField).toBe(k);
    expect(Zk.numberField).toBe(k);
    expect(() => Bk.reduceElement(Zk.call(0))).toThrow(NotImplementedError);
    expect(() => B.reduceElement(A.call(0))).not.toThrow();
    expect(() => B.mul(B.call(0))).toThrow(TypeError);
    expect(() => A.submoduleFromMatrix(DM([[1, 0], [0, 1]], ZZ), 1).reduceElement(A.call(0))).toThrow(RangeError);
    expect(() => D.reduceElement(B.call(0))).toThrow(StructureError);
    expect(() => h.mod(D)).toThrow(TypeError);
  });
  it('checks Hermite normal forms', () => {
    expect([DM([[2, 1], [0, 3]], ZZ), DM([[2, 3], [0, 3]], ZZ), DM([[0, 0], [0, 1]], ZZ), DM([[2, -1], [0, 3]], ZZ), DM([[1, 0]], ZZ), DM([[1, 0], [1, 1]], ZZ), DM([[1, 0], [0, 1]], QQ)].map(isSqMaxrankHNF)).toEqual([true, false, false, false, false, false, false]);
  });
  it('rejects invalid inputs', () => {
    expect(() => A.call(4)).toThrow(RangeError);
    expect(() => A.call(DM([[1], [2]], ZZ))).toThrow(RangeError);
    expect(() => A.submoduleFromGens([])).toThrow(RangeError);
    expect(() => A.submoduleFromGens([B.call(0)])).toThrow(RangeError);
    expect(() => A.submoduleFromMatrix(DM([[1]], QQ))).toThrow(RangeError);
    expect(() => A.submoduleFromMatrix(DM([[1]], ZZ))).toThrow(RangeError);
    expect(() => new PowerBasis(poly('2*x**2 + 1'))).toThrow(RangeError);
    expect(() => B.add(new PowerBasis(poly('x**2 + 1')).wholeSubmodule())).toThrow(TypeError);
    expect(() => B.mul(new PowerBasis(poly('x**2 + 1')).wholeSubmodule())).toThrow(TypeError);
    expect(() => B.pow(0)).toThrow(TypeError);
    expect(() => e.add(new PowerBasis(poly('x**2 + 1')).call(0))).toThrow(TypeError);
    expect(() => e.mul(new PowerBasis(poly('x**2 + 1')).call(0))).toThrow(TypeError);
    expect(() => e.unify(new PowerBasis(poly('x**2 + 1')).call(0))).toThrow(UnificationFailed);
    expect(() => B.call(0).overPowerBasis().toAlgNum()).toThrow(StructureError);
  });
});

describe('number fields', () => {
  it('converts between the field and its power basis', () => {
    const K = new AlgebraicField(QQ, sqrt(5));
    const pb = new PowerBasis(K);
    const a = K.new([1, 2]);
    const elt = pb.elementFromANP(a);
    expect([s(elt), s(elt.toANP()), s(elt.toAlgNum().asExpr())]).toEqual(['[2, 1]', s(a), '2 + sqrt(5)']);
    expect(s(pb.elementFromAlgNum(K.toAlgNum(a)))).toBe('[2, 1]');
    expect(() => pb.elementFromANP(new AlgebraicField(QQ, sqrt(3)).new([1, 2]))).toThrow(UnificationFailed);
    // an alias names the generator
    const Ka = new AlgebraicField(QQ, new AlgebraicNumber(sqrt(5), [1, 0], { alias: 'alpha' }));
    const pa = new PowerBasis(Ka);
    expect([s(pa.call(1).generator), s(pa.call(1).mul(3).floordiv(2).overPowerBasis().asExpr()), s(pa.call(1).asExpr(x))]).toEqual(['alpha', '3*alpha/2', 'x']);
  });
  it('scales a primitive element that is not an algebraic integer', () => {
    // QQ<sqrt(2)/3>: theta' = 9*theta = 3*sqrt(2) has the minimal polynomial x**2 - 18
    const K = new AlgebraicField(QQ, P('sqrt(2)/3'));
    const pb = new PowerBasis(K);
    expect([s(pb.T.asExpr().subs(pb.T.gens[0]!, x)), pb.scale]).toEqual(['x**2 - 18', 9n]);
    const a = K.new([1, 0]);
    expect([s(pb.elementFromANP(a)), s(pb.elementFromANP(a).toANP()), s(K.toSympy(pb.call(1).toANP()))]).toEqual(['[0, 1]/9', s(a), '3*sqrt(2)']);
    const Ka = new AlgebraicField(QQ, new AlgebraicNumber(P('sqrt(2)/3'), [1, 0], { alias: 'alpha' }));
    expect(s(new PowerBasis(Ka).call(1).asExpr())).toBe('9*alpha');
  });
});

describe('homomorphisms', () => {
  it('computes matrices and kernels', () => {
    const phi = new ModuleEndomorphism(A, (y) => y.mul(A.call(1)));
    expect(s(phi.matrix())).toBe(m.endo);
    expect(phi.matrix(3).toList().map((r) => r.map((c) => Number(((BigInt(String(c)) % 3n) + 3n) % 3n)))).toEqual(m.endo_mod);
    expect(s(new ModuleEndomorphism(A, (y) => y.pow(5)).kernel(5))).toBe(m.kernel);
    expect(s(new ModuleHomomorphism(A, A, (y) => y.mul(A.call(0).sub(A.call(1)))).kernel())).toBe(m.kernel_qq);
    const E = A.endomorphismRing();
    const tau = E.innerEndomorphism(A.call(1));
    expect(tau).toBeInstanceOf(InnerEndomorphism);
    expect(tau.multiplier).toEqual(A.call(1));
    expect(s(E.represent(tau).transpose())).toBe(m.endring);
    expect(E.n).toBe(16);
    expect(() => E.represent(new ModuleEndomorphism(B, (y) => y))).toThrow(NotImplementedError);
    const Z0 = A.submoduleFromMatrix(DomainMatrix.zeros([4, 0], ZZ));
    expect(s(new ModuleHomomorphism(Z0, A, (y) => y).matrix())).toBe('DomainMatrix([[], [], [], []], (4, 0), ZZ)');
    expect(s(Z0.endomorphismRing().represent(new ModuleEndomorphism(Z0, (y) => y)))).toBe('DomainMatrix([], (0, 0), ZZ)');
    expect(s(Z0)).toBe('Submodule[]');
  });
  it('finds minimal polynomials', () => {
    const C13 = new PowerBasis(poly('x**12 + x**11 + x**10 + x**9 + x**8 + x**7 + x**6 + x**5 + x**4 + x**3 + x**2 + x + 1'));
    let eta: ModuleElement = C13.zero();
    for (let k = 0; k < 6; k++) eta = eta.add(C13.call(2 ** (2 * k + 1) % 13));
    const pw: ModuleElement[] = [];
    expect(s(findMinPoly(eta, QQ, x, pw).asExpr())).toBe(ref.minpolys.eta);
    expect(pw.map(s)).toEqual(ref.minpolys.eta_powers);
    expect(s(findMinPoly(A.call(2), QQ, x).asExpr())).toBe(ref.minpolys.zeta2);
    expect(s(findMinPoly(A.call(0), QQ, x).asExpr())).toBe(ref.minpolys.one);
    expect(s(findMinPoly(A.call(1).add(A.call(2)), GF(7), x).asExpr())).toBe(ref.minpolys.ff);
    expect(findMinPoly(A.call(1), QQ).gens[0]).toBeInstanceOf(Dummy);
    // SymPy drops the denominator of the powers; zeta/2 is a root of 16*x**4 + 8*x**3 + 4*x**2 + 2*x + 1
    expect(s(findMinPoly(A.call(1).floordiv(2), QQ, x).asExpr())).toBe('x**4 + x**3/2 + x**2/4 + x/8 + 1/16');
    expect(s(findMinPoly(A.call(1).floordiv(2), GF(7), x).asExpr())).toBe(s(Poly.from(P('x**4 + 4*x**3 + 2*x**2 + x + 4'), [x], { modulus: 7 }).asExpr()));
    expect(() => findMinPoly(B.call(0), QQ)).toThrow(MissingUnityError);
  });
});
