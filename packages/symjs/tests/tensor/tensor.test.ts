// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 sympy.tensor.tensor (printed with str()).
import { describe, expect, it } from 'vitest';
import type { Expr, TensExpr } from '../../src';
import {
  ExprMap,
  Matrix,
  Permutation,
  Rational,
  S,
  Sym,
  TensAdd,
  TensMul,
  Tensor,
  TensorElement,
  TensorHead,
  TensorIndex,
  TensorIndexType,
  TensorManager,
  TensorSymmetry,
  Wild,
  WildTensExpr,
  WildTensorHead,
  WildTensorIndex,
  add,
  canonBp,
  contractMetric,
  doit,
  mul,
  perm2tensor,
  pow,
  riemannCyclic,
  riemannCyclicReplace,
  sub,
  substituteIndices,
  symbols,
  tensorHeads,
  tensorIndices,
  tensorMul,
} from '../../src';

const str = (e: unknown): string => (Array.isArray(e) ? `[${e.map(str).join(', ')}]` : e instanceof Map ? `{${[...e].map(([k, v]) => `${str(k)}: ${str(v)}`).join(', ')}}` : String(e));
const tens = (e: Expr): TensExpr => e as TensExpr;

const Lo = TensorIndexType('Lorentz', { dummyName: 'L' });
const [i, j, k, l, m] = tensorIndices('i j k l m', Lo) as [TensorIndex, TensorIndex, TensorIndex, TensorIndex, TensorIndex];
const [A, B, C] = tensorHeads('A B C', [Lo]) as [TensorHead, TensorHead, TensorHead];
const T = TensorHead('T', [Lo, Lo], TensorSymmetry.fullySymmetric(2));
const F = TensorHead('F', [Lo, Lo], TensorSymmetry.fullySymmetric(-2));
const g = Lo.metric;
const [x] = symbols('x') as [Sym];
const L0 = TensorIndex('L_0', Lo);

describe('index types, indices, symmetries and heads', () => {
  it('builds index types with their metric, delta and epsilon', () => {
    const L = TensorIndexType('L', { dim: 4 });
    expect([String(L), String(L.metric), String(L.delta), String(L.epsilon), L.dummyName, String(L.dim)]).toEqual(['L', 'metric(L,L)', 'KD(L,L)', 'Eps(L,L,L,L)', 'L', '4']);
    expect(L.metric).toBe(L.metric);
    expect(String(L.epsilon.at(i.withName('a').withName('a'), 'b', 'c', 'd'))).toBe('Eps(a, b, c, d)');
    expect(String(TensorIndexType('Q').dim)).toBe('dim_Q');
    // SymPy returns None for these
    expect(() => TensorIndexType('Q').epsilon).toThrow('no epsilon');
    expect(() => TensorIndexType('Q', { metricSymmetry: null }).metric).toThrow('no metric');
    const N = TensorIndexType('Ns', { metricSymmetry: 0, epsDim: 3, metricName: 'h' });
    expect(String(N.metric.symmetry)).toBe(String(TensorSymmetry.noSymmetry(2)));
    expect([String(N.metric), String(N.epsilon), N.metricName, N.metricSymmetry]).toEqual(['h(Ns,Ns)', 'Eps(Ns,Ns,Ns)', 'h', 0]);
    expect(String(TensorIndexType('Sp', { metricSymmetry: -1 }).metric.symmetry)).toBe('TensorSymmetry((0,), ((0 1)(2 3),))');
    for (const t of [L, N, TensorIndexType('Sp', { metricSymmetry: -1 }), TensorIndexType('Q', { metricSymmetry: null })]) expect(t.withArgs(t.args).equals(t)).toBe(true);
  });
  it('builds indices', () => {
    expect([String(i), String(i.neg()), i.neg().neg().equals(i), i.isUp, i.indexName, i.tensorIndexType.equals(Lo)]).toEqual(['i', '-i', true, true, 'i', true]);
    const R = TensorIndexType('Rauto');
    expect([String(TensorIndex(true, R)), String(TensorIndex(true, R)), String(WildTensorIndex(true, R))]).toEqual(['_i0', '_i1', '_i2']);
    expect(i.withArgs(i.args).equals(i)).toBe(true);
    expect(i.neg().withArgs(i.neg().args).equals(i.neg())).toBe(true);
    expect(str(i.matches(i))).toBe('{}');
    expect(str(i.matches(j))).toBe('NoMatch');
    // tensor_indices('i0:3', Lorentz) -> [i0, i1, i2] (names parsed like symbols())
    expect(tensorIndices('i0:3', Lo).map(String)).toEqual(['i0', 'i1', 'i2']);
  });
  it('builds slot symmetries', () => {
    expect(String(TensorSymmetry.fullySymmetric(2))).toBe('TensorSymmetry((0,), ((3)(0 1),))');
    expect(String(TensorSymmetry.riemann())).toBe('TensorSymmetry((0, 2), ((0 1)(4 5), (2 3)(4 5), (5)(0 2)(1 3)))');
    expect(String(TensorSymmetry.noSymmetry(2))).toBe('TensorSymmetry((), ((3),))');
    expect(String(TensorSymmetry.directProduct(1, -2))).toBe('TensorSymmetry((1,), ((1 2)(3 4),))');
    expect(String(TensorSymmetry.directProduct(2, 0, 1))).toBe('TensorSymmetry((0,), ((4)(0 1),))');
    expect(TensorSymmetry.fullySymmetric(0).rank).toBe(0);
    expect(TensorSymmetry.fullySymmetric(1).equals(TensorSymmetry.noSymmetry(1))).toBe(true);
    expect(new TensorSymmetry(2, 1).equals(TensorSymmetry.fullySymmetric(2))).toBe(true);
    expect(new TensorSymmetry(2, -1).equals(TensorSymmetry.fullySymmetric(-2))).toBe(true);
    expect(new TensorSymmetry(2, 0).equals(TensorSymmetry.noSymmetry(2))).toBe(true);
    expect(new TensorSymmetry(2).equals(TensorSymmetry.noSymmetry(2))).toBe(true);
    const s = TensorSymmetry.riemann();
    expect(new TensorSymmetry([s.base, s.generators]).equals(s)).toBe(true);
    expect(s.withArgs(s.args).equals(s)).toBe(true);
    expect([s.base, s.rank]).toEqual([[0, 2], 4]);
    expect(() => new TensorSymmetry(-1)).toThrow('rank');
  });
  it('builds heads and tensors', () => {
    expect([String(A), A.rank, String(T), String(T.at(j, i)), String(T.at('i', '-j'))]).toEqual(['A(Lorentz)', 1, 'T(Lorentz,Lorentz)', 'T(j, i)', 'T(i, -j)']);
    expect(T.withArgs(T.args).equals(T)).toBe(true);
    expect(() => TensorHead('bad', [Lo], T.symmetry)).toThrow('rank');
    const [si, sj] = symbols('i j') as [Sym, Sym];
    expect(String(T.at(si, mul(-1, sj)))).toBe('T(i, -j)');
    expect(() => T.at(si, x.add(1))).toThrow('index not understood');
    expect(() => A.at(i, j)).toThrow('number');
    expect(String(TensorHead('S', []).at())).toBe('S');
    const t = T.at(i, i.neg());
    expect([String(t), str(t.free), str(t.dum), t.extRank, t.rank, String(t.coeff), t.nocoeff === t]).toEqual(['T(L_0, -L_0)', '[]', '[[0, 1]]', 2, 0, '1', true]);
    expect([str(T.at(j, i).freeArgs), str(T.at(j, i).getFreeIndices()), str(t.split()), t.sortedComponents() === t]).toEqual(['[i, j]', '[j, i]', '[T(L_0, -L_0)]', true]);
    expect(t.withArgs(t.args).equals(t)).toBe(true);
    expect(() => T.at(i, i)).toThrow('two equal contravariant indices in slots 0 and 1');
    expect(() => T.at(i.neg(), i.neg())).toThrow('two equal covariant indices');
    expect(T.at(i.neg(), i).dum).toEqual([[1, 0]]);
    expect(A.at(i).isCommutative).toBe(false);
    expect(A.at(i).commutesWith(x)).toBe(0);
  });
});

describe('commutation groups', () => {
  it('canonicalizes (anti)commuting and noncommuting heads', () => {
    const G = TensorHead('G', [Lo], TensorSymmetry.noSymmetry(1), 'Gcomm');
    const GH = TensorHead('GH', [Lo], TensorSymmetry.noSymmetry(1), 'GHcomm');
    TensorManager.setComm('Gcomm', 'GHcomm', 0);
    expect(String(canonBp(mul(GH.at(j), G.at(i))))).toBe('G(i)*GH(j)');
    expect(String(canonBp(mul(G.at(j), G.at(i))))).toBe('G(j)*G(i)');
    expect(String(canonBp(mul(G.at(j), A.at(i))))).toBe('A(i)*G(j)');
    expect(G.commutesWith(G)).toBe('none');
    TensorManager.setComms(['Gcomm', 'GHcomm', null]);
    expect(G.commutesWith(GH)).toBe('none');
    expect(TensorManager.getComm(99, 98)).toBe('none');
    expect(TensorManager.getComm(0, 98)).toBe(0);
    expect(TensorManager.getComm(1, 98)).toBe('none');
    TensorManager.clear();
    const [G1, G2] = tensorHeads('G1 G2', [Lo], undefined, 1) as [TensorHead, TensorHead];
    expect(String(canonBp(mul(G2.at(i), G1.at(j))))).toBe('-G1(j)*G2(i)');
    expect(canonBp(mul(G1.at(i), G1.at(i.neg())))).toBe(S.Zero);
    expect(String(canonBp(mul(G2.at(i.neg()), G1.at(i))))).toBe('-G1(L_0)*G2(-L_0)');
    expect(String(canonBp(mul(G1.at(j), G1.at(i))))).toBe('-G1(i)*G1(j)');
  });
});

describe('products and sums', () => {
  it('contracts and renames dummy indices', () => {
    const c = mul(A.at(i), A.at(i.neg())) as TensMul;
    expect([String(c), str(c.getFreeIndices()), c.rank, str(c.getIndices())]).toEqual(['A(L_0)*A(-L_0)', '[]', 0, '[L_0, -L_0]']);
    expect(String(mul(c, c))).toBe('A(L_0)*A(-L_0)*A(L_1)*A(-L_1)');
    expect(String(mul(A.at(L0), T.at(i, i.neg())))).toBe('A(L_0)*T(L_1, -L_1)');
    expect(String(mul(A.at(L0), A.at(i), A.at(i.neg())))).toBe('A(L_0)*A(L_1)*A(-L_1)');
    expect(() => mul(A.at(i), A.at(i))).toThrow('Repeated index: i');
    const t = mul(T.at(i, j), A.at(j.neg())) as TensMul;
    expect([str(t.getIndices()), str(t.getFreeIndices()), str(t.free), str(t.dum), t.extRank, str(t.components), str(t.freeArgs)]).toEqual(['[i, L_0, -L_0]', '[i]', '[[i, 0]]', '[[1, 2]]', 3, '[T(Lorentz,Lorentz), A(Lorentz)]', '[i]']);
    expect(t.withArgs(t.args).equals(t)).toBe(true);
    expect(str((mul(T.at(j, i), A.at(k)) as TensMul).freeArgs)).toBe('[i, j, k]');
  });
  it('prints coefficients like SymPy', () => {
    const half = Rational.of(1, 2);
    const got = [mul(-1, A.at(i)), mul(-2, A.at(i)), mul(-1, x, A.at(i)), mul(add(x, 1), A.at(i)), mul(-1, add(x, 1), A.at(i)), mul(half, A.at(i)), mul(pow(x, 2), A.at(i)), mul(2, x, A.at(i)), mul(-1, half, A.at(i))].map(String);
    expect(got).toEqual(['-A(i)', '-2*A(i)', '-x*A(i)', '(x + 1)*A(i)', '-(x + 1)*A(i)', '(1/2)*A(i)', 'x**2*A(i)', '2*x*A(i)', '-(1/2)*A(i)']);
    expect(String(A.at(i).neg())).toBe('-A(i)');
    expect(String(A.at(i).div(2))).toBe('(1/2)*A(i)');
    expect(String(new TensMul([2, x]).doitShallow())).toBe('2*x');
    expect(new TensMul([0, A.at(i)]).doitShallow()).toBe(S.Zero);
    expect(String(new TensMul([1, A.at(i)]).doitShallow())).toBe('A(i)');
    expect(String(tensorMul(A.at(i), 2))).toBe('2*A(i)');
    expect(String(tensorMul())).toBe('1');
  });
  it('splits products and gives the coefficient', () => {
    const t = mul(2, A.at(i), B.at(j), x) as TensMul;
    expect(str(t.split())).toBe('[2*x*A(i), B(j)]');
    expect([String(t.coeff), String(t.nocoeff)]).toEqual(['2*x', 'A(i)*B(j)']);
  });
  it('collects and orders terms like SymPy', () => {
    const got = [
      add(B.at(i), A.at(i)),
      add(mul(2, B.at(i)), A.at(i)),
      add(mul(x, A.at(i)), B.at(i)),
      add(T.at(j, i), T.at(i, j)),
      add(mul(A.at(i), B.at(j)), mul(B.at(i), A.at(j))),
      sub(mul(A.at(i), B.at(j)), mul(2, A.at(j), B.at(i))),
      add(mul(T.at(i, j), A.at(j.neg())), B.at(i)),
      add(mul(x, A.at(i)), mul(2, A.at(i))),
      add(mul(x, A.at(i)), mul(-1, x, A.at(i)), B.at(i)),
      add(T.at(i.neg(), i), x),
      add(TensorHead('A', [Lo], TensorSymmetry.fullySymmetric(1)).at(i), A.at(i)),
      sub(A.at(i), mul(2, B.at(i))),
      add(A.at(i), A.at(i)),
      sub(A.at(i), A.at(i)),
      add(mul(A.at(j), A.at(j.neg())), x),
      add(mul(A.at(j), A.at(j.neg())), x, 1),
      sub(add(mul(A.at(j), A.at(j.neg())), 1), 1),
    ].map(String);
    expect(got).toEqual([
      'A(i) + B(i)',
      '2*B(i) + A(i)',
      'x*A(i) + B(i)',
      'T(i, j) + T(j, i)',
      'A(i)*B(j) + B(i)*A(j)',
      'A(i)*B(j) - 2*A(j)*B(i)',
      'T(i, L_0)*A(-L_0) + B(i)',
      '(x + 2)*A(i)',
      'B(i)',
      'x + T(-L_0, L_0)',
      '2*A(i)',
      '-2*B(i) + A(i)',
      '2*A(i)',
      '0',
      'x + A(L_0)*A(-L_0)',
      '1 + x + A(L_0)*A(-L_0)',
      'A(L_0)*A(-L_0)',
    ]);
    expect(() => add(A.at(i), A.at(j))).toThrow('same indices');
    expect(String(add(new TensMul([0, A.at(i)]), B.at(i)))).toBe('B(i)');
    expect(add(new TensMul([0, A.at(i)]), new TensMul([0, B.at(i)]))).toBe(S.Zero);
    const s = add(A.at(i), B.at(i)) as TensAdd;
    expect([String(s.coeff), s.nocoeff === s, s.rank, str(s.getFreeIndices()), str(s.getIndices())]).toEqual(['1', true, 1, '[i]', '[i]']);
    expect(str((add(mul(A.at(j), A.at(j.neg())), mul(B.at(i), B.at(i.neg()))) as TensAdd).getIndices())).toBe('[L_0, -L_0]');
    expect((add(mul(A.at(j), A.at(j.neg())), x) as TensAdd).rank).toBe(0);
    expect(s.withArgs(s.args).equals(s)).toBe(true);
    expect(String(doit(s))).toBe('A(i) + B(i)');
    expect(String(doit(mul(A.at(i), A.at(i.neg()))))).toBe('A(L_0)*A(-L_0)');
    expect(() => pow(A.at(i), 2)).toThrow('No power');
    expect(() => mul(x, pow(A.at(i), -1))).toThrow('No power');
    expect(() => pow(2, A.at(i))).toThrow('exponent');
  });
  it('expands products over sums', () => {
    const e = mul(A.at(i), add(B.at(i.neg()), C.at(i.neg())));
    expect(String(e)).toBe('A(L_0)*(B(-L_0) + C(-L_0))');
    expect(String(e.expand())).toBe('A(L_0)*B(-L_0) + A(L_0)*C(-L_0)');
    expect(String(canonBp(e))).toBe('A(L_0)*B(-L_0) + A(L_0)*C(-L_0)');
    expect(String(mul(add(x, 1), A.at(i)).expand())).toBe('x*A(i) + A(i)');
    expect(String(add(mul(add(x, 1), A.at(i)), B.at(i)).expand())).toBe('x*A(i) + A(i) + B(i)');
    expect(A.at(i).expand()).toEqual(A.at(i));
  });
});

describe('canonicalization', () => {
  it('canonicalizes slot symmetries and dummies', () => {
    const got = [
      T.at(j, i).canonBp(),
      F.at(j, i).canonBp(),
      F.at(i, i.neg()).canonBp(),
      canonBp(mul(2, T.at(j, i), A.at(k))),
      canonBp(mul(B.at(i.neg()), A.at(i))),
      canonBp(mul(B.at(j), T.at(i.neg(), j.neg()), A.at(i))),
      sub(T.at(i, j), T.at(j, i)),
      canonBp(add(T.at(i, j), T.at(j, i))),
      canonBp(mul(T.at(i, l), T.at(l.neg(), j), A.at(k))),
      canonBp(mul(T.at(j, l), T.at(i, l.neg()))),
      canonBp(mul(T.at(l.neg(), m.neg()), T.at(l, k), T.at(m, j))),
      canonBp(mul(A.at(L0, ...[]), A.at(L0.neg()))),
    ].map(String);
    expect(got).toEqual([
      'T(i, j)',
      '-F(i, j)',
      '0',
      '2*A(k)*T(i, j)',
      'A(L_0)*B(-L_0)',
      'A(L_0)*B(L_1)*T(-L_0, -L_1)',
      '-T(j, i) + T(i, j)',
      '2*T(i, j)',
      'A(k)*T(i, L_0)*T(j, -L_0)',
      'T(i, L_0)*T(j, -L_0)',
      'T(j, L_0)*T(k, L_1)*T(-L_0, -L_1)',
      'A(L_0)*A(-L_0)',
    ]);
    expect(String(canonBp(sub(T.at(i, j), T.at(j, i))))).toBe('0');
    // the doctests of TensMul.canon_bp and contract_metric
    const A2 = TensorHead('A', [Lo, Lo], TensorSymmetry.fullySymmetric(-2));
    const [L1, L2] = [TensorIndex('L_1', Lo), TensorIndex('L_2', Lo)];
    expect(String(canonBp(mul(A2.at(L0, L1.neg()), A2.at(L1, L0.neg()))))).toBe('-A(L_0, L_1)*A(-L_0, -L_1)');
    expect(canonBp(mul(A2.at(L0, L1.neg()), A2.at(L1, L2.neg()), A2.at(L2, L0.neg())))).toBe(S.Zero);
    const [p, q] = tensorHeads('p q', [Lo]) as [TensorHead, TensorHead];
    expect(String(canonBp(mul(p.at(L0), q.at(L1), g.at(L0.neg(), L1.neg()))))).toBe('metric(L_0, L_1)*p(-L_0)*q(-L_1)');
    expect(String(canonBp(contractMetric(mul(p.at(i), q.at(j), g.at(i.neg(), j.neg())), g)))).toBe('p(L_0)*q(-L_0)');
    const c = canonBp(mul(B.at(i.neg()), A.at(i))) as TensMul;
    expect(c.canonBp()).toBe(c);
    const t = T.at(j, i).canonBp() as Tensor;
    expect(t.canonBp()).toBe(t);
    expect(canonBp(x)).toBe(x);
    expect(String(canonBp(new TensMul([2, x])))).toBe('2*x');
  });
  it('canonicalizes the Riemann tensor, direct products and given base and strong generating sets', () => {
    const R = TensorHead('R', [Lo, Lo, Lo, Lo], TensorSymmetry.riemann());
    expect([R.at(j, i, l, k), R.at(k, l, i, j), R.at(i, i.neg(), k, l), R.at(i, j, i.neg(), j.neg())].map((t) => String(canonBp(t)))).toEqual(['R(i, j, k, l)', 'R(i, j, k, l)', '0', 'R(L_0, L_1, -L_0, -L_1)']);
    expect(String(canonBp(TensorHead('D', [Lo, Lo, Lo], TensorSymmetry.directProduct(1, -2)).at(i, k, j)))).toBe('-D(i, j, k)');
    // a base that is not minimal is replaced by a minimal one
    expect(String(canonBp(TensorHead('Z', [Lo, Lo], new TensorSymmetry([1], [new Permutation([1, 0, 2, 3])])).at(j, i)))).toBe('Z(i, j)');
    // Schreier-Sims gives no minimal base here: the naive algorithm (SymPy 1.14 raises IndexError and TypeError)
    const Z = TensorHead('Z', [Lo, Lo, Lo], new TensorSymmetry([], [new Permutation([0, 2, 1, 3, 4]), new Permutation([1, 0, 2, 3, 4])]));
    expect(String(canonBp(Z.at(k, j, i)))).toBe('Z(i, j, k)');
    expect(String(canonBp(Z.at(k, j, k.neg())))).toBe('Z(j, L_0, -L_0)');
    const Y = TensorHead('Y', [Lo, Lo], new TensorSymmetry([], [new Permutation([1, 0, 3, 2])]));
    expect(canonBp(Y.at(i, i.neg()))).toBe(S.Zero);
  });
  it('canonicalizes with antisymmetric and symmetry-free metrics and several index types', () => {
    const Sp = TensorIndexType('Sp', { dummyName: 'S', metricSymmetry: -1, dim: 2 });
    const [a, b] = tensorIndices('a b', Sp) as [TensorIndex, TensorIndex];
    const [P, Q] = tensorHeads('P Q', [Sp]) as [TensorHead, TensorHead];
    const e = Sp.metric;
    expect([mul(P.at(a), e.at(a.neg(), b.neg()), Q.at(b)), mul(P.at(a), P.at(a.neg())), mul(P.at(a.neg()), P.at(a)), mul(P.at(a), Q.at(a.neg())), mul(Q.at(a.neg()), P.at(a))].map((t) => String(canonBp(t)))).toEqual(['P(S_0)*Q(S_1)*metric(-S_0, -S_1)', '0', '0', 'P(S_0)*Q(-S_0)', 'P(S_0)*Q(-S_0)']);
    expect(String(canonBp(mul(P.at(a), A.at(i), Q.at(a.neg()), B.at(i.neg()))))).toBe('A(L_0)*B(-L_0)*P(S_0)*Q(-S_0)');
    const Ns = TensorIndexType('Ns', { metricSymmetry: 0 });
    const [n1] = tensorIndices('n1', Ns) as [TensorIndex];
    const X = TensorHead('X', [Ns]);
    expect([mul(X.at(n1), X.at(n1.neg())), mul(X.at(n1.neg()), X.at(n1))].map((t) => String(canonBp(t)))).toEqual(['X(N_0)*X(-N_0)', 'X(N_0)*X(-N_0)']);
    const H2 = TensorHead('H2', [Sp, Lo]);
    expect(String(canonBp(mul(A.at(i), H2.at(a, j), P.at(a.neg()))))).toBe('A(i)*H2(S_0, j)*P(-S_0)');
    expect([mul(H2.at(a, j), A.at(i)), mul(A.at(i), P.at(a)), mul(P.at(a), A.at(i))].map((t) => String((t as TensMul).sortedComponents()))).toEqual(['A(i)*H2(a, j)', 'A(i)*P(a)', 'A(i)*P(a)']);
  });
  it('applies a permutation of the ordered indices', () => {
    expect(String(perm2tensor(T.at(i, j), [1, 0, 2, 3]))).toBe('T(j, i)');
    expect(String(perm2tensor(T.at(i, j), [0, 1, 3, 2]))).toBe('-T(i, j)');
  });
});

describe('metric contraction and index substitution', () => {
  it('contracts a symmetric metric', () => {
    const got = [
      (mul(g.at(i, j), A.at(j.neg())) as TensMul).contractMetric(g),
      contractMetric(mul(g.at(i, j), A.at(i.neg())), g),
      g.at(i, i.neg()).contractMetric(g),
      contractMetric(mul(g.at(i, j), T.at(i.neg(), j.neg())), g),
      contractMetric(mul(2, g.at(i, i.neg()), A.at(k)), g),
      contractMetric(mul(g.at(i, j), A.at(k)), g),
      contractMetric(mul(A.at(i), add(mul(g.at(i.neg(), j), B.at(j.neg())), C.at(i.neg()))), g),
      contractMetric(mul(g.at(i, j), g.at(j.neg(), k)), g),
      (add(mul(g.at(i, j), A.at(j.neg())), B.at(i)) as TensAdd).contractMetric(g),
      contractMetric(mul(2, g.at(i, i.neg())), g),
      tens(mul(g.at(i, j), A.at(j.neg()))).contractDelta(g),
    ].map(String);
    expect(got).toEqual(['A(i)', 'A(j)', 'dim_L', 'T(L_0, -L_0)', '2*dim_L*A(k)', 'metric(i, j)*A(k)', 'A(L_0)*B(-L_0) + A(L_0)*C(-L_0)', 'metric(i, k)', 'A(i) + B(i)', '2*dim_L', 'A(i)']);
    expect(contractMetric(A.at(i), g)).toEqual(A.at(i));
    expect(contractMetric(g.at(i, j), g)).toEqual(g.at(i, j));
    expect(contractMetric(mul(A.at(i), B.at(j)), g)).toEqual(mul(A.at(i), B.at(j)));
    expect(contractMetric(x, g)).toBe(x);
    expect(String(Lo.delta.at(i, i.neg()).contractDelta(Lo.delta))).toBe('dim_L');
  });
  it('contracts an antisymmetric metric with the signs of SymPy', () => {
    const Sp = TensorIndexType('Sp', { dummyName: 'S', metricSymmetry: -1, dim: 2 });
    const [a, b] = tensorIndices('a b', Sp) as [TensorIndex, TensorIndex];
    const [P, Q] = tensorHeads('P Q', [Sp]) as [TensorHead, TensorHead];
    const e = Sp.metric;
    const cases: [Expr, string][] = [
      [e.at(a, a.neg()), '-2'],
      [e.at(a.neg(), a), '2'],
      [mul(e.at(a, b), P.at(b.neg())), 'P(a)'],
      [mul(e.at(a, b), P.at(a.neg())), '-P(b)'],
      [mul(P.at(b.neg()), e.at(a, b)), 'P(a)'],
      [mul(P.at(a.neg()), e.at(a, b)), 'P(b)'],
      [mul(e.at(a, b), P.at(a.neg()), Q.at(b.neg())), '-P(S_0)*Q(-S_0)'],
      [mul(P.at(a.neg()), Q.at(b.neg()), e.at(a, b)), 'P(S_0)*Q(-S_0)'],
      [mul(P.at(a), Q.at(b), e.at(a.neg(), b.neg())), '-P(S_0)*Q(-S_0)'],
      [mul(e.at(a.neg(), b.neg()), P.at(a), Q.at(b)), '-P(S_0)*Q(-S_0)'],
      [mul(e.at(b.neg(), a.neg()), P.at(a), Q.at(b)), 'P(S_0)*Q(-S_0)'],
      [mul(P.at(a), e.at(a.neg(), b.neg()), Q.at(b)), 'P(S_0)*Q(-S_0)'],
      [mul(e.at(a, a.neg()), Q.at(b)), '-2*Q(b)'],
      [mul(e.at(a.neg(), a), Q.at(b)), '2*Q(b)'],
      [mul(e.at(a, b), e.at(a.neg(), b.neg())), '2'],
    ];
    expect(cases.map(([t]) => String(contractMetric(t, e)))).toEqual(cases.map(([, s]) => s));
    const Ns = TensorIndexType('Ns', { metricSymmetry: 0 });
    const [n1, n2] = tensorIndices('n1 n2', Ns) as [TensorIndex, TensorIndex];
    const X = TensorHead('X', [Ns]);
    expect(String(contractMetric(mul(Ns.metric.at(n1, n2), X.at(n2.neg())), Ns.metric))).toBe('X(n1)');
    expect(String(contractMetric(Ns.metric.at(n1, n1.neg()), Ns.metric))).toBe('dim_N');
    const Odd = TensorHead('odd', [Lo, Lo], new TensorSymmetry([1], [new Permutation([1, 0, 2, 3])]));
    expect(() => contractMetric(mul(Odd.at(i, j), A.at(j.neg())), Odd)).toThrow('general symmetry');
  });
  it('substitutes indices', () => {
    expect(String((mul(T.at(i, j), A.at(j.neg())) as TensMul).substituteIndices([i, k], [j, l]))).toBe('T(k, L_0)*A(-L_0)');
    expect(String(substituteIndices(add(A.at(i), B.at(i)), [i, k.neg()]))).toBe('A(-k) + B(-k)');
    expect(String(substituteIndices(A.at(i.neg()), [i, k]))).toBe('A(-k)');
    expect(String(A.at(j).substituteIndices([i, k]))).toBe('A(j)');
    expect(String(substituteIndices(add(mul(A.at(j), A.at(j.neg())), x), [i, k]))).toBe('x + A(L_0)*A(-L_0)');
    expect(substituteIndices(x, [i, k])).toBe(x);
  });
});

describe('component arrays', () => {
  const L = TensorIndexType('L', { dim: 2 });
  const [a, b, c, d] = symbols('a b c d') as [Sym, Sym, Sym, Sym];
  const [li, lj, lk] = tensorIndices('i j k', L) as [TensorIndex, TensorIndex, TensorIndex];
  const LA = TensorHead('A', [L]);
  const LT = TensorHead('T', [L, L]);
  const abcd = [
    [a, b],
    [c, d],
  ];
  const gm = Matrix.diag(1, -1);
  const rwa = (e: Expr, repl: [Expr, unknown][], idx?: (TensorIndex | Expr)[]): string => String(tens(e).replaceWithArrays(new Map(repl) as never, idx));
  it('reads the components with raised, lowered and permuted indices', () => {
    const got = [
      rwa(LT.at(li, li.neg()), [[LT.at(li, lj), abcd], [L, gm]]),
      rwa(LT.at(li.neg(), li), [[LT.at(li, lj), abcd], [L, gm]]),
      rwa(LT.at(li, li.neg()), [[LT.at(li.neg(), lj.neg()), abcd], [L, gm]]),
      rwa(LT.at(li, lj), [[LT.at(li.neg(), lj), abcd], [L, gm]]),
      rwa(LT.at(li, lj), [[LT.at(lj, li), abcd]]),
      rwa(LT.at(li, lj), [[LT.at(lj, lk), abcd]]),
      rwa(LT.at(li, lj), [[LT.at(lj.neg(), lk), abcd], [L, gm]]),
      rwa(LT.at(li, lj), [[LT.at(li, lj), abcd]], [lj, li]),
      rwa(LT.at(li, lj), [[LT.at(li, lj), abcd], [L, gm]], [li.neg(), lj]),
      rwa(LT.at(li, lj.neg()), [[LT.at(li, lj), abcd], [L, gm]], [(li.args[0] as Expr), (lj.args[0] as Expr)]),
      rwa(LT.at(li, lj.neg()), [[LT.at(li, lj), abcd], [L, gm]], [mul(-1, (li.args[0] as Expr)), mul(-1, (lj.args[0] as Expr))]),
      rwa(LT.at(li, li.neg()), [[LT.at(lj, lj.neg()), abcd]]),
      rwa(LA.at(li), [[LA.at(li), [a, b]]], [lj]),
      rwa(add(mul(LA.at(li), LA.at(li.neg())), x), [[LA.at(li), [a, b]], [L, gm]]),
      rwa(mul(3, LA.at(li), LA.at(lj)), [[LA.at(li), [a, b]]]),
      rwa(mul(3, LA.at(li), LA.at(li.neg())), [[LA.at(li), [a, b]], [L, gm]]),
      rwa(TensorElement(LT.at(li, lj), new Map([[li, 1]])), [[LT.at(li, lj), abcd]]),
      rwa(TensorElement(LT.at(li, lj), new Map([[li, 1], [lj, 0]])), [[LT.at(li, lj), abcd]]),
      rwa(add(LT.at(li, lj), LT.at(lj, li)), [[LT.at(li, lj), abcd]]),
    ];
    expect(got).toEqual([
      'a - d',
      'a - d',
      'a - d',
      '[[a, b], [-c, -d]]',
      '[[a, c], [b, d]]',
      '[[a, b], [c, d]]',
      '[[a, b], [-c, -d]]',
      '[[a, c], [b, d]]',
      '[[a, b], [-c, -d]]',
      '[[a, b], [c, d]]',
      '[[a, -b], [-c, d]]',
      '[[a, b], [c, d]]',
      '[a, b]',
      'a**2 - b**2 + x',
      '[[3*a**2, 3*a*b], [3*a*b, 3*b**2]]',
      '3*a**2 - 3*b**2',
      '[c, d]',
      'c',
      '[[2*a, b + c], [b + c, 2*d]]',
    ]);
  });
  it('rejects missing tensors, metrics and incompatible shapes', () => {
    expect(() => rwa(LT.at(li, lj), [[LT.at(lk, lk.neg()), abcd]])).toThrow('T(L_0, -L_0) with contractions is not implemented');
    expect(() => rwa(LT.at(li, lj), [[LA.at(li), [a, b]]])).toThrow('not found');
    expect(() => rwa(LT.at(li, lj), [[LT.at(li, lj), [a, b]]])).toThrow('shapes for tensor T(i, j)');
    expect(() => rwa(LT.at(li, lj), [[LT.at(li, lj), abcd], [L, [1, 2]]])).toThrow('shapes for tensor L');
    expect(() => rwa(LA.at(li.neg()), [[LA.at(li), [a, b]]])).toThrow('No metric provided');
    expect(() => rwa(LT.at(li, lj), [[LT.at(li, lj), abcd]], [li, li])).toThrow('incompatible indices');
    expect(() => rwa(LT.at(li, lj), [[LT.at(li, lj), abcd]], [li, lk, lj])).toThrow('incompatible indices');
    // symbolic dimensions are not checked
    expect(rwa(A.at(i), [[A.at(i), [1, 2, 3]]])).toBe('[1, 2, 3]');
  });
  it('builds tensor elements', () => {
    const [si, sj] = symbols('i j') as [Sym, Sym];
    const S2 = TensorHead('A', [L, L], TensorSymmetry.fullySymmetric(2));
    expect(str(S2.at(si, sj).getFreeIndices())).toBe('[i, j]');
    const te = TensorElement(S2.at(si, sj), new Map([[si, 2]])) as TensorElement;
    expect([String(te), str(te.getFreeIndices()), str(te.getIndices()), String(te.coeff), te.nocoeff === te, String(te.expr), String(te.indexMap)]).toEqual(['TensorElement(A(i, j), {i: 2})', '[j]', '[j]', '1', true, 'A(i, j)', '{i: 2}']);
    expect(te.withArgs(te.args).equals(te)).toBe(true);
    expect([te.doitShallow(), te.canonBp(), te.contractMetric(), te.substituteIndices()].every((v) => v === te)).toBe(true);
    expect(String(te.replaceIndices(new Map([[li.key, lk]])))).toBe('TensorElement(A(k, j), {k: 2})');
    expect(String(TensorElement(mul(LA.at(li), LA.at(lj)), new Map([[li, 1]])))).toBe('TensorElement(A(i), {i: 1})*A(j)');
    expect(TensorElement(LT.at(li, lj), new Map([[lk, 1]]))).toEqual(LT.at(li, lj));
    expect(() => TensorElement(x, new Map([[lk, 1]]))).toThrow('not a tensor expression');
    expect(() => TensorElement(mul(2, LA.at(li)), new Map([[li, 1]]))).toThrow('not a tensor expression');
  });
});

describe('matching', () => {
  const R3 = TensorIndexType('R3', { dim: 3 });
  const [p, q, s] = tensorIndices('p q s', R3) as [TensorIndex, TensorIndex, TensorIndex];
  const K = TensorHead('K', [R3]);
  const Q = TensorHead('Q', [R3, R3]);
  const FA = TensorHead('F', [R3, R3], TensorSymmetry.fullySymmetric(-2));
  const w = WildTensorIndex('w', R3);
  const v = WildTensorIndex('v', R3);
  const u = WildTensorIndex('u', R3, true, true);
  const W = WildTensorHead('W');
  const U = WildTensorHead('U', { unorderedIndices: true });
  it('matches tensors, wild indices and wild tensors (the doctests)', () => {
    const got = [
      W.at(p).matches(K.at(p)),
      W.at(p).matches(K.at(q)),
      W.at(p).matches(K.at(p.neg())),
      W.at().matches(K.at(p)),
      W.at().matches(Q.at(p, q)),
      W.at(p, q).matches(Q.at(q, p)),
      U.at(p, q).matches(Q.at(q, p)),
      WildTensorIndex('q', R3).matches(p),
      WildTensorIndex('q', R3).matches(p.neg()),
      u.matches(p.neg()),
      u.matches(p),
    ].map(str);
    expect(got).toEqual(['{W(R3): _WildTensExpr(K(p))}', 'NoMatch', 'NoMatch', '{W: K(p)}', '{W: Q(p, q)}', 'NoMatch', '{U(R3,R3): _WildTensExpr(Q(q, p))}', '{q: p}', 'NoMatch', '{u: -p}', '{u: p}']);
  });
  it('matches with symmetries, repeated wild indices and unordered indices', () => {
    const got = [
      K.at(p).matches(K.at(p)),
      K.at(p).matches(Q.at(p, q)),
      K.at(p).matches(x),
      Q.at(w, v).matches(Q.at(p, q)),
      Q.at(w, w.neg()).matches(Q.at(p, p.neg())),
      Q.at(w, w.neg()).matches(Q.at(p, q.neg())),
      FA.at(w, v).matches(FA.at(q, p)),
      FA.at(p, q).matches(FA.at(q, p)),
      FA.at(q, p).matches(FA.at(q, p)),
      Q.at(w, p).matches(Q.at(q, s)),
      W.at().matches(1),
      W.at(p).matches(1),
      W.at().matches(x),
      W.at(p).matches(Q.at(p, q)),
      W.at(w).matches(K.at(q)),
      U.at(p, q).matches(Q.at(p, s)),
      U.at(w, u).matches(Q.at(q.neg(), p)),
      U.at(w, w.neg()).matches(Q.at(q, q.neg())),
      U.at(w, w.neg()).matches(Q.at(q, s.neg())),
      U.at(u, u.neg()).matches(Q.at(q, s)),
      U.at(p, w).matches(Q.at(q, p)),
      w.matches(K.at(p)),
      w.matches(TensorIndex('z', TensorIndexType('Z'))),
    ].map(str);
    expect(got).toEqual([
      '{}',
      'NoMatch',
      'NoMatch',
      '{w: p, v: q}',
      '{R_0: R_0, -R_0: -R_0}',
      'NoMatch',
      '{w: q, v: p}',
      'NoMatch',
      '{}',
      'NoMatch',
      '{W: 1}',
      'NoMatch',
      'NoMatch',
      'NoMatch',
      '{w: q, W(R3): _WildTensExpr(K(q))}',
      'NoMatch',
      '{w: p, u: -q, U(R3,R3): _WildTensExpr(Q(-q, p))}',
      'NoMatch',
      'NoMatch',
      'NoMatch',
      '{w: q, U(R3,R3): _WildTensExpr(Q(q, p))}',
      'NoMatch',
      'NoMatch',
    ]);
    expect(str(Q.at(w, v).matches(Q.at(p, q), new Map([[x, x]])))).toBe('{x: x, w: p, v: q}');
    expect(str(Q.at(w, w.neg()).matchesForm(mul(-1, Q.at(p, q)), new ExprMap()))).toBe('NoMatch');
  });
  it('matches products and sums without wild tensors', () => {
    const got = [
      tens(mul(K.at(p), K.at(q))).matches(mul(K.at(q), K.at(p))),
      tens(mul(K.at(p), K.at(q))).matches(mul(K.at(p), K.at(s))),
      tens(mul(K.at(p), K.at(p.neg()))).matches(x),
      tens(mul(K.at(p), K.at(q))).matches(x),
      tens(mul(K.at(p), K.at(p.neg()))).matches(mul(K.at(q), K.at(q.neg()))),
      tens(mul(2, K.at(p), K.at(p.neg()))).matches(mul(K.at(q), K.at(q.neg()))),
      tens(add(K.at(p), mul(Q.at(p, q), K.at(q.neg())))).matches(add(mul(Q.at(p, s), K.at(s.neg())), K.at(p))),
      tens(add(K.at(p), mul(Q.at(p, q), K.at(q.neg())))).matches(K.at(p)),
    ].map(str);
    expect(got).toEqual(['{}', 'NoMatch', 'NoMatch', 'NoMatch', '{}', 'NoMatch', '{}', 'NoMatch']);
    expect(() => tens(mul(W.at(p), K.at(q))).matches(mul(K.at(p), K.at(q)))).toThrow('wild tensors');
    expect(() => tens(mul(new Wild('X'), K.at(q))).matches(mul(K.at(q), 2))).toThrow('wild tensors');
    expect(() => tens(add(K.at(w), mul(Q.at(w, p), K.at(p.neg())))).matches(add(K.at(q), mul(Q.at(q, p), K.at(p.neg()))))).toThrow('wild tensors');
  });
  it('builds wild heads, tensors and indices', () => {
    expect([String(W), String(W.at(p)), String(W.at(p).component), String(U.at(p, q).component), String(W.at(p, q).head), String(WildTensorHead('V', { indexTypes: [R3] }))]).toEqual(['W()', 'W(p)', 'W(R3)', 'U(R3,R3)', 'W(R3,R3)', 'V(R3)']);
    expect(() => WildTensorHead('V', { indexTypes: [R3, R3], symmetry: TensorSymmetry.fullySymmetric(2) })).toThrow('Wild matching based on symmetry is not implemented.');
    expect([String(w.neg()), String(u.neg()), u.neg().ignoreUpdown, u.neg().isUp, w.ignoreUpdown]).toEqual(['-w', '-u', true, false, false]);
    expect(String(W.at(w, w.neg()))).toBe('W(R_0, -R_0)');
    for (const e of [W, U, w, u, W.at(p), U.at(p, q)]) expect(e.withArgs(e.args).equals(e)).toBe(true);
    const m = W.at(p).matches(K.at(p)) as Map<Expr, Expr>;
    const we = [...m.values()][0] as WildTensExpr;
    expect([String(we.call(q)), String(we.withArgs(we.args))]).toEqual(['K(q)', '_WildTensExpr(K(p))']);
    expect(String(W.at(p).replaceIndices(new Map([[p.key, q]])))).toBe('W(q)');
  });
});

describe('Riemann cyclic identity', () => {
  const R = TensorHead('R', [Lo, Lo, Lo, Lo], TensorSymmetry.riemann());
  it('replaces Riemann tensors by their cyclic form', () => {
    const t = mul(R.at(i, j, k, l), sub(R.at(i.neg(), j.neg(), k.neg(), l.neg()), mul(2, R.at(i.neg(), k.neg(), j.neg(), l.neg()))));
    // SymPy prints the inner coefficient as (-2), from a TensMul left unevaluated by index renaming
    expect(String(t)).toBe('R(L_0, L_1, L_2, L_3)*(-2*R(-L_0, -L_2, -L_1, -L_3) + R(-L_0, -L_1, -L_2, -L_3))');
    expect(riemannCyclic(t)).toBe(S.Zero);
    expect(String(riemannCyclic(R.at(i, j, k, l)))).toBe('-(1/3)*R(i, l, j, k) + (1/3)*R(i, k, j, l) + (2/3)*R(i, j, k, l)');
    expect(String(riemannCyclic(mul(R.at(i, j, k, l), R.at(i.neg(), j.neg(), k.neg(), l.neg()))))).toBe('(2/3)*R(L_0, L_1, L_2, L_3)*R(-L_0, -L_1, -L_2, -L_3) + (2/3)*R(L_0, L_1, L_2, L_3)*R(-L_0, -L_2, -L_1, -L_3)');
    expect(String(riemannCyclicReplace(R.at(i, j, k, l)))).toBe('-(1/3)*R(i, l, j, k) + (1/3)*R(i, k, j, l) + (2/3)*R(i, j, k, l)');
    expect(() => riemannCyclic(add(mul(R.at(i, j, k, l), R.at(i.neg(), j.neg(), k.neg(), l.neg())), x))).toThrow('a product of tensors');
  });
});

describe('edge cases', () => {
  it('orders indices of different types with the same name by position', () => {
    const La = TensorIndexType('L', { dim: 2 });
    const Lb = TensorIndexType('L', { dim: 3 });
    const M = TensorHead('M', [La, Lb]);
    expect(String(canonBp(M.at(TensorIndex('i', La), TensorIndex('i', Lb))))).toBe('M(i, i)');
    expect(str(M.at(TensorIndex('j', La), TensorIndex('i', Lb)).getFreeIndices())).toBe('[j, i]');
    expect(() => new Tensor(A, [i, j])).toThrow('wrong number of indices');
  });
  it('renames dummies clashing with free indices of other factors', () => {
    expect(String(mul(A.at(L0), B.at(L0.neg()), T.at(i, i.neg())))).toBe('A(L_0)*B(-L_0)*T(L_1, -L_1)');
    expect(String(mul(add(mul(A.at(j), A.at(j.neg())), x), B.at(L0)))).toBe('(x + A(L_1)*A(-L_1))*B(L_0)');
  });
  it('sorts components with several index types', () => {
    const Sp = TensorIndexType('Sp', { dummyName: 'S', metricSymmetry: -1, dim: 2 });
    const [a, b] = tensorIndices('a b', Sp) as [TensorIndex, TensorIndex];
    const H2 = TensorHead('H2', [Sp, Lo]);
    const H3 = TensorHead('H3', [Lo, Sp]);
    expect(String((mul(H3.at(j, b), H2.at(a, i)) as TensMul).sortedComponents())).toBe('H2(a, i)*H3(j, b)');
    expect(String((mul(H2.at(a, i), H3.at(j, b)) as TensMul).sortedComponents())).toBe('H2(a, i)*H3(j, b)');
    expect(String(contractMetric(mul(TensorHead('P', [Sp]).at(a), Sp.metric.at(a.neg(), b)), Sp.metric))).toBe('P(b)');
  });
  it('orders sums with tensor elements and reads rank-zero tensors', () => {
    const L = TensorIndexType('L', { dim: 2 });
    const [li, lj] = tensorIndices('i j', L) as [TensorIndex, TensorIndex];
    const LT = TensorHead('T', [L, L]);
    const LB = TensorHead('B', [L]);
    const te = TensorElement(LT.at(li, lj), new Map([[li, 1]]));
    expect([String(add(te, LB.at(lj))), String(add(LB.at(lj), te))]).toEqual(['B(j) + TensorElement(T(i, j), {i: 1})', 'B(j) + TensorElement(T(i, j), {i: 1})']);
    expect(String(tens(te).replaceIndices(new Map()))).toBe('TensorElement(T(i, j), {i: 1})');
    const Sx = TensorHead('S', []);
    expect(String(Sx.at())).toBe('S');
    expect(String(tens(mul(Sx.at(), LB.at(li))).replaceWithArrays(new Map<Expr, never>([[Sx.at(), 5 as never], [LB.at(li), [1, 2] as never]])))).toBe('[5, 10]');
    expect(String(Sx.at().replaceWithArrays(new Map<Expr, never>([[Sx.at(), 5 as never]])))).toBe('5');
  });
  it('rebuilds wild heads with index types and keeps unreplaced indices', () => {
    const R3 = TensorIndexType('R3', { dim: 3 });
    const [p, q, s] = tensorIndices('p q s', R3) as [TensorIndex, TensorIndex, TensorIndex];
    const V = WildTensorHead('V', { indexTypes: [R3] });
    expect(V.withArgs(V.args).equals(V)).toBe(true);
    expect(String(WildTensorHead('W').at(p, q).replaceIndices(new Map([[p.key, s]])))).toBe('W(s, q)');
  });
});
