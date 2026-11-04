// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference: SymPy 1.14 tensor.tensor. Limitations are tested explicitly.
import { expect, it } from 'vitest';
import { TensorIndexType, TensorIndex, TensorSymmetry, TensorHead, tensorIndices, tensorHeads, Tensor, TensMul, canonBp, contractMetric, mul, add, pow, S, symbols } from '../../src';
const L = TensorIndexType('L', { dim: 4 }), i = TensorIndex('i', L), j = TensorIndex('j', L), k = TensorIndex('k', L);
const A = TensorHead('A', [L]), T = TensorHead('T', [L, L], TensorSymmetry.fullySymmetric(2));
it('represents index types, variance and tensor slots structurally', () => {
  expect(String(L)).toBe('L'); expect(String(i.neg())).toBe('-i'); expect(i.neg().neg().equals(i)).toBe(true);
  expect(String(A)).toBe('A(L)'); expect(A.rank).toBe(1); expect(String(A.at(i))).toBe('A(i)');
  expect(tensorHeads('A, B', [L]).map(String)).toEqual(['A(L)', 'B(L)']);
  expect(tensorIndices('', L)).toEqual([]);
  const K = new TensorIndexType('K'); expect(String(K.dim)).toBe('dim_K');
  expect(new TensorIndex('i', L).equals(i)).toBe(true);
  for (const e of [L, i, i.neg(), A, T.symmetry, TensorSymmetry.noSymmetry(1), TensorSymmetry.fullySymmetric(-2), A.at(i)]) expect(e.withArgs(e.args).equals(e)).toBe(true);
  expect(() => TensorHead('bad', [L], T.symmetry)).toThrow('rank');
  expect(() => TensorHead('bad', [L, K], T.symmetry)).toThrow('same index type');
  expect(() => new TensorSymmetry(-1)).toThrow('rank');
  expect(() => A.at(i, j)).toThrow('number');
  expect(() => A.at(TensorIndex('k', K))).toThrow('type mismatch');
});
it('validates Einstein contractions and preserves free indices', () => {
  const contraction = mul(A.at(i), A.at(i.neg()));
  expect(contraction).toBeInstanceOf(TensMul);
  expect((contraction as TensMul).getFreeIndices()).toEqual([]);
  expect((contraction as TensMul).isScalar).toBe(true); expect(A.at(i).isScalar).toBe(false); expect(A.at(i).isCommutative).toBe(false);
  expect((mul(T.at(i, j), A.at(j.neg())) as TensMul).getFreeIndices().map(String)).toEqual(['i']);
  expect(() => mul(A.at(i), A.at(i))).toThrow('once up');
  expect(() => mul(A.at(i), A.at(i.neg()), A.at(i))).toThrow('once up');
  const square = mul(contraction, contraction) as TensMul;
  expect(square.getIndices().map((v) => v.indexName)).toEqual(['L_0', 'L_0', 'L_1', 'L_1']);
  expect(square.withArgs(square.args).equals(square)).toBe(true);
  expect(String(mul(2, A.at(i)))).toBe('(2)*A(i)'); expect(mul(0, A.at(i)).equals(0)).toBe(true);
  expect(mul(1, A.at(i)).equals(A.at(i))).toBe(true);
});
it('canonicalizes free symmetric and antisymmetric slots', () => {
  const B = TensorHead('B', [L, L], TensorSymmetry.fullySymmetric(-2));
  expect(String(T.at(j, i).canonBp())).toBe('T(i, j)');
  expect(String(canonBp(B.at(j, i)))).toBe('-B(i, j)');
  expect(canonBp(B.at(i, i.neg())).equals(0)).toBe(true);
  expect(String(canonBp(mul(2, T.at(j, i), A.at(k))))).toBe('(2)*A(k)*T(i, j)');
  expect(canonBp(S.One)).toBe(S.One);
  expect(() => canonBp(mul(A.at(i), A.at(i.neg())))).toThrow('dummy-index');
  expect(() => add(A.at(i), A.at(j))).toThrow('multiplication');
  expect(() => pow(A.at(i), 2)).toThrow('multiplication');
  const [q] = symbols('q', { commutative: false });
  expect(() => mul(q, A.at(i))).toThrow('commute');
});
it('contracts symmetric metrics and traces', () => {
  const g = L.metric;
  expect(String((mul(g.at(i, j), A.at(j.neg())) as TensMul).contractMetric(g))).toBe('A(i)');
  expect(String(contractMetric(mul(g.at(i, j), A.at(i.neg())), g))).toBe('A(j)');
  expect(g.at(i, i.neg()).contractMetric(g).equals(4)).toBe(true);
  expect(String(contractMetric(mul(g.at(i, j), T.at(i.neg(), j.neg())), g))).toBe('T(j, -j)');
  expect(String(contractMetric(mul(2, g.at(i, i.neg()), A.at(k)), g))).toBe('(8)*A(k)');
  expect(contractMetric(A.at(i), g).equals(A.at(i))).toBe(true);
  expect(contractMetric(S.One, g)).toBe(S.One);
  expect(contractMetric(g.at(i, j), g).equals(g.at(i, j))).toBe(true);
  expect(() => contractMetric(A.at(i), A)).toThrow('symmetric');
  expect(new Tensor(A, [i]).equals(A.at(i))).toBe(true);
});

it('retains uncontracted metric factors and already ordered slots', () => {
  expect(TensorIndexType('M').dim.toString()).toBe('dim_M');
  expect(tensorIndices('i,j', L).map(String)).toEqual(['i', 'j']);
  expect(String(mul(A.at(i), A.at(i.neg())))).toBe('A(i)*A(-i)');
  expect(canonBp(T.at(i, j)).equals(T.at(i, j))).toBe(true);
  const expr = mul(A.at(k), L.metric.at(i, j));
  expect(contractMetric(expr, L.metric).equals(expr)).toBe(true);
});
