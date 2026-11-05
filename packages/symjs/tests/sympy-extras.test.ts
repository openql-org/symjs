// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * More of SymPy's API: matrix methods, assumptions (Q, ask, refine),
 * series helpers, base classes and small number-theory and polys helpers.
 * Expected values are SymPy 1.14 output.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Expr } from '../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const s = (e: unknown) => (e instanceof Expr ? sj.str(e) : String(e));
const M = (rows: readonly (readonly sj.ExprLike[])[]): sj.Matrix => sj.Matrix.of(rows);
const A = M([[1, 2], [3, 4]]);

describe('matrix methods', () => {
  it('Berkowitz', () => {
    expect(sj.berkowitz(A).map((r) => r.map(s))).toEqual([['1'], ['1', '-1'], ['1', '-5', '-2']]);
    expect(sj.berkowitzMinors(A).map(s)).toEqual(['1', '1', '-2']);
    expect(sj.berkowitz(sj.Matrix.zeros(0, 0)).map((r) => r.map(s))).toEqual([['1']]);
  });

  it('dual and elementary operations', () => {
    expect(s(sj.dual(M([[0, 1, 2, 3], [-1, 0, 4, 5], [-2, -4, 0, 6], [-3, -5, -6, 0]])))).toBe('Matrix([[0, -6, 5, -4], [6, 0, 3, -2], [-5, -3, 0, 1], [4, 2, -1, 0]])');
    expect(s(sj.dual(sj.Matrix.eye(3)))).toBe('Matrix([[0, 0, 0], [0, 0, 0], [0, 0, 0]])');
    expect(s(sj.elementaryRowOp(A, { op: 'n->kn', index: 1, k: 5 }))).toBe('Matrix([[1, 2], [15, 20]])');
    expect(s(sj.elementaryRowOp(A, { op: 'n<->m', index1: 0, index2: 1 }))).toBe('Matrix([[3, 4], [1, 2]])');
    expect(s(sj.elementaryRowOp(A, { op: 'n->n+km', index: 1, k: 2, index2: 0 }))).toBe('Matrix([[1, 2], [5, 8]])');
    expect(s(sj.elementaryColOp(A, { op: 'n->n+km', index: 1, k: 2, index2: 0 }))).toBe('Matrix([[1, 4], [3, 10]])');
    expect(() => sj.elementaryRowOp(A, { op: 'n<->m', index1: 0 })).toThrow(TypeError);
    expect(() => sj.elementaryRowOp(A, { index: 5 })).toThrow(RangeError);
  });

  it('permutations by swaps and deletion', () => {
    const B = M([[0, 1, 2], [3, 4, 5], [6, 7, 8]]);
    expect(s(sj.permuteFwd(B, [[0, 1], [0, 2]]))).toBe('Matrix([[6, 7, 8], [0, 1, 2], [3, 4, 5]])');
    expect(s(sj.permuteBkwd(B, [[0, 1], [0, 2]]))).toBe('Matrix([[3, 4, 5], [6, 7, 8], [0, 1, 2]])');
    expect(s(sj.permuteFwd(B, [2, 0, 1]))).toBe('Matrix([[6, 7, 8], [0, 1, 2], [3, 4, 5]])');
    expect(s(sj.rowDel(B, -1))).toBe('Matrix([[0, 1, 2], [3, 4, 5]])');
    expect(s(sj.colDel(B, 0))).toBe('Matrix([[1, 2], [4, 5], [7, 8]])');
    expect(() => sj.colDel(B, 3)).toThrow(RangeError);
  });

  it('LU variants', () => {
    expect(sj.LUdecompositionSimple(A).map((v) => (Array.isArray(v) ? JSON.stringify(v) : s(v)))).toEqual(['Matrix([[1, 2], [3, -2]])', '[]']);
    expect(sj.LUdecompositionSimple(M([[0, 2], [3, 4]])).map((v) => (Array.isArray(v) ? JSON.stringify(v) : s(v)))).toEqual(['Matrix([[3, 4], [0, 2]])', '[[0,1]]']);
    expect(sj.LUdecompositionFF(A).map(s)).toEqual(['Matrix([[1, 0], [0, 1]])', 'Matrix([[1, 0], [3, 1]])', 'Matrix([[1, 0], [0, 1]])', 'Matrix([[1, 2], [0, -2]])']);
    expect(sj.LUdecompositionFF(M([[0, 1], [1, 0]])).map(s)[0]).toBe('Matrix([[0, 1], [1, 0]])');
  });

  it('LLL', () => {
    const L = M([[1, 0, 0, 0, -20160], [0, 1, 0, 0, 33768], [0, 0, 1, 0, 39578], [0, 0, 0, 1, 47757]]);
    expect(s(sj.lll(L))).toBe('Matrix([[10, -3, -2, 8, -4], [3, -9, 8, 1, -11], [-3, 13, -9, -3, -9], [-12, -7, -11, 9, -1]])');
    const [B, T] = sj.lllTransform(L);
    expect(T.mul(L).equals(B)).toBe(true);
    expect(() => sj.lll(L, sj.Rational.of(1n, 5n))).toThrow(RangeError);
    expect(() => sj.lll(M([[1], [2]]))).toThrow(RangeError);
  });

  it('Householder forms and SVD', () => {
    expect(sj.upperHessenbergDecomposition(M([[1, 2, 3], [-3, 5, 6], [4, -8, 9]])).map(s)).toEqual([
      'Matrix([[1, 6/5, 17/5], [5, 213/25, -134/25], [0, 216/25, 137/25]])',
      'Matrix([[1, 0, 0], [0, -3/5, 4/5], [0, 4/5, 3/5]])',
    ]);
    expect(sj.singularValueDecomposition(M([[1, 2], [2, 1]])).map(s)).toEqual([
      'Matrix([[sqrt(2)/2, sqrt(2)/2], [-sqrt(2)/2, sqrt(2)/2]])',
      'Matrix([[1, 0], [0, 3]])',
      'Matrix([[-sqrt(2)/2, sqrt(2)/2], [sqrt(2)/2, sqrt(2)/2]])',
    ]);
    expect(sj.singularValueDecomposition(M([[1, 0, 2]])).map((m) => m.shape.join('x'))).toEqual(['1x1', '1x1', '3x1']);
    const [U, Bd, V] = sj.bidiagonalDecomposition(A);
    expect(U.mul(Bd).mul(V).sub(A).map((e) => sj.simplify(e)).isZero).toBe(true);
    expect(sj.simplify(sj.bidiagonalize(A).get(1, 0))).toEqual(sj.S.Zero);
    const [Ul, Bl, Vl] = sj.bidiagonalDecomposition(A, false);
    expect(Ul.mul(Bl).mul(Vl).sub(A).map((e) => sj.simplify(e)).isZero).toBe(true);
    expect(sj.simplify(sj.bidiagonalize(A, false).get(0, 1))).toEqual(sj.S.Zero);
  });

  it('blocks and graph decompositions', () => {
    expect(sj.getDiagBlocks(M([[1, 3, 0, 0], [y, 9, 0, 0], [0, 0, x, 0], [0, 0, 0, 0]])).map(s)).toEqual(['Matrix([[1, 3], [y, 9]])', 'Matrix([[x]])', 'Matrix([[0]])']);
    const G = M([[1, 0, 2], [0, 3, 0], [4, 0, 5]]);
    const [P, B] = sj.connectedComponentsDecomposition(G);
    expect(P.T.mul(B).mul(P).equals(G)).toBe(true);
    const H = M([[1, 2, 0], [0, 3, 0], [4, 5, 6]]);
    for (const lower of [true, false]) {
      const [P2, B2] = sj.stronglyConnectedComponentsDecomposition(H, lower);
      expect(P2.T.mul(B2).mul(P2).equals(H)).toBe(true);
    }
    expect(s(sj.jordanCell(sj.Sym ? new sj.Sym('a') : 0, 2))).toBe('Matrix([[a, 1], [0, a]])');
    const [Pj, cells] = sj.jordanCells(M([[1, 1], [0, 1]]));
    expect([s(Pj), ...cells.map(s)]).toEqual(['Matrix([[1, 0], [0, 1]])', 'Matrix([[1, 1], [0, 1]])']);
  });

  it('iteration, indexing, printing and constructors', () => {
    const m = M([[0, 1], [2, 3]]);
    expect(JSON.stringify(sj.iterItems(m).map(([ij, v]) => [ij, s(v)]))).toBe('[[[0,1],"1"],[[1,0],"2"],[[1,1],"3"]]');
    expect(sj.iterValues(m).map(s)).toEqual(['1', '2', '3']);
    expect(sj.key2ij(A, [-1, 0])).toEqual([1, 0]);
    expect(sj.key2ij(A, 3)).toEqual([1, 1]);
    expect(sj.key2ij(A, { start: 1 })).toEqual([1, 4]);
    expect(sj.key2ij(A, [{ start: 0, stop: 1 }, 1])).toEqual([{ start: 0, stop: 1 }, 1]);
    expect(sj.key2bounds(A, [{}, 1])).toEqual([0, 2, 1, 2]);
    expect(() => sj.key2ij(A, 9)).toThrow(RangeError);
    expect(sj.printNonzero(M([[0, 1, 2], [3, 4, 5]]))).toBe('[ XX]\n[XXX]');
    expect(sj.printNonzero(sj.Matrix.eye(2), 'x')).toBe('[x ]\n[ x]');
    const T = M([[1, 2], [-33, 4]]);
    expect(sj.table(T)).toBe('[  1, 2]\n[-33, 4]');
    expect(sj.table(T, { rowsep: ',\n' })).toBe('[  1, 2],\n[-33, 4]');
    expect(sj.table(T, { colsep: ' ' })).toBe('[  1 2]\n[-33 4]');
    expect(sj.table(T, { align: 'center' })).toBe('[ 1 , 2]\n[-33, 4]');
    expect(sj.table(T, { align: 'left', rowstart: '{', rowend: '}' })).toBe('{1  , 2}\n{-33, 4}');
    expect(sj.table(sj.Matrix.zeros(0, 0))).toBe('[]');
    const [wm, wp] = sj.wilkinson(1);
    expect([s(wm), s(wp)]).toEqual(['Matrix([[-1, 1, 0], [1, 0, 1], [0, 1, 1]])', 'Matrix([[1, 1, 0], [1, 0, 1], [0, 1, 1]])']);
    const r1 = sj.randMatrix(3, 3, { seed: 1 });
    expect(r1.equals(sj.randMatrix(3, 3, { seed: 1 }))).toBe(true);
    expect(r1.equals(sj.randMatrix(3, 3, { seed: 2 }))).toBe(false);
    const sym = sj.randMatrix(4, 4, { seed: 3, symmetric: true, percent: 50, min: 1, max: 9 });
    expect(sym.equals(sym.T)).toBe(true);
    expect(sym.data.every((e) => e.toNumber() >= 0 && e.toNumber() <= 9)).toBe(true);
    expect(() => sj.randMatrix(2, 3, { symmetric: true })).toThrow(RangeError);
    expect((sj.symarray('a', 3) as Expr[]).map(s)).toEqual(['a_0', 'a_1', 'a_2']);
    expect(((sj.symarray('a', [2, 2]) as Expr[][])[1]!).map(s)).toEqual(['a_1_0', 'a_1_1']);
    expect((sj.symarray('a', 1, { real: true })[0] as sj.Sym).assumptions.real).toBe(true);
    expect(sj.matrix2numpy(A, 'float')).toEqual([[1, 2], [3, 4]]);
    expect((sj.list2numpy([1, [2, 3]]) as unknown[]).length).toBe(2);
    expect(sj.list2numpy([1.5], 'float')).toEqual([1.5]);
  });

  it('DomainMatrix', () => {
    expect(String(sj.toDM(A))).toBe('DomainMatrix({0: {0: 1, 1: 2}, 1: {0: 3, 1: 4}}, (2, 2), ZZ)');
    expect(sj.toDM(A).toMatrix().equals(A)).toBe(true);
    expect(sj.toDM(A).shape).toEqual([2, 2]);
    const P = M([[x, 1], [1, x]]);
    expect(sj.toDM(P).domain).toBe('ZZ[x]');
    expect(sj.toDM(P, { field: true }).domain).toBe('ZZ(x)');
    expect(sj.toDM(A, { field: true }).domain).toBe('QQ');
    expect(sj.toDM(M([[sj.sqrt(2)]])).domain).toBe('EXRAW');
    expect(sj.toDM(M([[new sj.Float(1.5), x]])).domain).toBe('RR[x]');
    expect(String(sj.toDM(M([[0, sj.Rational.of(1n, 2n)]])))).toBe('DomainMatrix({0: {1: 1/2}}, (1, 2), QQ)');
  });

  it('mutable row operations', () => {
    const m = sj.MutableDenseMatrix.eye(3);
    m.rowAdd(0, 2, 3);
    m.rowMult(1, 7);
    expect(String(m)).toBe('Matrix([[1, 0, 0], [0, 7, 0], [3, 0, 1]])');
    m.copyinList(0, 1, [8, 9]);
    m.copyinList(2, 0, [[4, 5]]);
    expect(String(m)).toBe('Matrix([[1, 8, 0], [0, 9, 0], [4, 5, 1]])');
  });
});

describe('assumptions: Q, ask, refine', () => {
  it('refines with predicates', () => {
    expect(s(sj.refine(sj.pow(sj.abs(x), 2), sj.Q.real(x)))).toBe('x**2');
    expect(s(sj.refine(sj.sqrt(sj.pow(x, 2)), sj.Q.real(x)))).toBe('Abs(x)');
    expect(s(sj.refine(sj.abs(x), sj.Q.positive(x)))).toBe('x');
    expect(s(sj.refine(sj.sqrt(sj.pow(x, 2)), sj.Q.negative(x)))).toBe('-x');
    expect(s(sj.refine(sj.abs(sj.mul(x, y)), sj.Q.positive(x).and(sj.Q.positive(y))))).toBe('x*y');
    expect(s(sj.refine(sj.abs(x)))).toBe('Abs(x)');
    expect(s(sj.refine(sj.abs(sj.add(x, 1)), sj.Q.positive(sj.add(x, 1))))).toBe('Abs(x + 1)');
    const R = sj.refine(M([[sj.pow(sj.abs(x), 2), sj.sqrt(sj.pow(x, 2))]]), sj.Q.real(x));
    expect(s(R)).toBe('Matrix([[x**2, Abs(x)]])');
    expect(String(sj.Q.even(x))).toBe('Q.even(x)');
  });
  it('asks', () => {
    expect(sj.ask(sj.Q.positive(sj.add(x, 1)), sj.Q.positive(x))).toBe(true);
    expect(sj.ask(sj.Q.real(x))).toBe('unknown');
    expect(sj.ask(sj.Q.integer(sj.mul(2, x)), sj.Q.even(x))).toBe(true);
    expect(sj.ask(sj.Q.negative(x), sj.Q.positive(x))).toBe(false);
    expect(sj.ask(sj.Q.nonnegative(x), sj.Q.zero(x))).toBe(true);
    expect(sj.ask(sj.Q.nonzero(x), sj.Q.prime(x))).toBe(true);
    expect(sj.ask(sj.Q.nonpositive(x), sj.Q.negative(x))).toBe(true);
    expect(sj.ask(sj.Q.commutative(x))).toBe(true);
    expect(sj.ask(sj.Q.odd(x), sj.Q.odd(x))).toBe(true);
  });
});

describe('series helpers', () => {
  it('fourier series', () => {
    expect(s(sj.fourierSeries(x, x).truncate(3))).toBe('2*sin(x) - sin(2*x) + 2*sin(3*x)/3');
    expect(s(sj.fourierSeries(sj.pow(x, 2), x).truncate(3))).toBe('-4*cos(x) + cos(2*x) + pi**2/3');
    expect(s(sj.fourierSeries(x, x, [0, 1]).truncate(3))).toBe('-sin(2*pi*x)/pi - sin(4*pi*x)/(2*pi) + 1/2');
  });
  it('formal power series and lseries', () => {
    expect(s(sj.fps(sj.exp(x), x).truncate(4))).toBe('1 + x + x**2/2 + x**3/6 + O(x**4)');
    expect(s(sj.fps(sj.sin(x), x).truncate())).toBe('x - x**3/6 + x**5/120 + O(x**6)');
    expect(s(sj.fps(sj.exp(x), x).polynomial(3))).toBe('x**2/2 + x + 1');
    expect(s(sj.fps(sj.exp(x), x).coeff(3))).toBe('1/6');
    expect(sj.fps(sj.cos(x), x).terms(3).map(s)).toEqual(['1', '-x**2/2', 'x**4/24']);
    expect(String(sj.fps(sj.exp(x), x))).toBe('FormalPowerSeries(exp(x), x, 0, 1, (SeqFormula(Piecewise((1/factorial(_k), Eq(Mod(_k, 1), 0)), (0, True)), (_k, 1, oo)), SeqFormula(x**_k, (_k, 0, oo)), 1))');
    const it1 = sj.lseries(sj.exp(x), x);
    expect([0, 1, 2, 3].map(() => s(it1.next().value))).toEqual(['1', 'x', 'x**2/2', 'x**3/6']);
    const it2 = sj.lseries(sj.sin(x), x, sj.pi);
    expect([0, 1, 2].map(() => s(it2.next().value))).toEqual(['pi - x', '(x - pi)**3/6', '-(x - pi)**5/120']);
    expect([...sj.lseries(sj.add(x, 1), x)].map(s)).toEqual(['1', 'x']);
  });
  it('dir', () => {
    expect(s(sj.dir(sj.sin(x), x, 1))).toBe('1');
    expect(s(sj.dir(sj.add(sj.pow(x, 3), sj.pow(x, 2)), x, -1))).toBe('2');
    expect(s(sj.dir(sj.sub(sj.cos(x), 1), x, 1))).toBe('-1');
    expect(s(sj.dir(0, x, 1))).toBe('0');
  });
});

describe('Expr helpers and base classes', () => {
  it('asTerms, classKey, separate', () => {
    const [terms, gens] = sj.asTerms(sj.add(sj.mul(x, y), sj.mul(2, x), sj.cos(x)));
    expect(terms.map(([t, [c, m, nc]]) => [s(t), c, m, nc.length])).toEqual([
      ['x*y', [1, 0], [1, 1, 0], 0],
      ['2*x', [2, 0], [1, 0, 0], 0],
      ['cos(x)', [1, 0], [0, 0, 1], 0],
    ]);
    expect(gens.map(s)).toEqual(['x', 'y', 'cos(x)']);
    const [t2] = sj.asTerms(sj.add(sj.mul(sj.I, sj.pow(x, sj.Rational.of(3n, 2n))), sj.pow(y, sj.mul(2, x))));
    expect(t2.map(([, [c, m]]) => [c, m])).toEqual([[[0, 1], [3, 0]], [[1, 0], [0, 2]]]);
    expect(sj.classKey(sj.mul(x, y))).toEqual([3, 0, 'Mul']);
    expect(sj.classKey(sj.cos(x))).toEqual([4, 21, 'cos']);
    expect(sj.classKey(sj.pi)).toEqual([2, 0, 'Pi']);
    expect(sj.classKey(sj.Basic(x))).toEqual([5, 0, 'Basic']);
    expect(s(sj.separate(sj.pow(sj.mul(2, y), x)))).toBe('2**x*y**x');
  });

  it('Number, RealNumber, Atom, FunctionClass', () => {
    expect(s(sj.SymNumber(3))).toBe('3');
    expect(s(sj.SymNumber(1.5))).toBe('1.50000000000000');
    expect(s(sj.SymNumber('2/3'))).toBe('2/3');
    expect(s(sj.SymNumber('-7'))).toBe('-7');
    expect(s(sj.SymNumber('0.25'))).toBe('0.250000000000000');
    expect(() => sj.SymNumber('abc')).toThrow(TypeError);
    expect(() => sj.SymNumber(x)).toThrow(TypeError);
    expect(sj.Rational.of(1n) instanceof (sj.SymNumber as never)).toBe(true);
    expect(x instanceof (sj.SymNumber as never)).toBe(false);
    expect(new sj.RealNumber(2)).toBeInstanceOf(sj.Float);
    expect(s(sj.Atom())).toBe('Atom()');
    expect(s(sj.AtomicExpr())).toBe('AtomicExpr()');
    expect(s(sj.genericExpr(x, 1))).toBe('Expr(x, 1)');
    expect(x instanceof (sj.Atom as never)).toBe(true);
    expect(sj.sin(x) instanceof (sj.AtomicExpr as never)).toBe(false);
    const f = sj.FunctionClass('f');
    expect(s(f(x))).toBe('f(x)');
    expect(f instanceof (sj.FunctionClass as never)).toBe(true);
    expect(s(sj.MatrixBase.of([[1]]))).toBe('Matrix([[1]])');
  });

  it('UnevaluatedExpr and DeferredVector', () => {
    const u = sj.mul(x, new sj.UnevaluatedExpr(sj.pow(x, -1)));
    expect(s(u)).toBe('x*1/x');
    expect(sj.latex(u)).toBe('x \\frac{1}{x}');
    expect(s(sj.doit(u))).toBe('1');
    expect(s(sj.diff(new sj.UnevaluatedExpr(sj.pow(x, 2)), x))).toBe('2*x');
    const X = new sj.DeferredVector('X');
    expect(s(X)).toBe('X');
    expect(s(X.at(2))).toBe('X[2]');
    const f = sj.lambdify(sj.add(X.at(0), 2, sj.mul(y, X.at(2))), [X, y]);
    expect(f([1, 2, 3], 10).re).toBe(33);
    expect(() => f([1], 1)).toThrow(RangeError);
    expect(() => X.at(-1)).toThrow(RangeError);
  });

  it('errors and seterr', () => {
    expect(() => sj.sympify({} as never)).toThrow(sj.SympifyError);
    expect(new sj.PoleError('pole').name).toBe('PoleError');
    expect(new sj.PrecisionExhausted().message).toBe('precision exhausted');
    sj.seterr({ divide: true });
    try {
      expect(() => sj.mul(0, sj.pow(0, -1))).toThrow('Indeterminate 0/0');
    } finally {
      sj.seterr();
    }
    expect(s(sj.mul(0, sj.pow(0, -1)))).toBe('nan');
  });
});

describe('number theory and polys helpers', () => {
  it('Carmichael numbers', () => {
    expect(sj.findFirstNCarmichaels(5)).toEqual([561n, 1105n, 1729n, 2465n, 2821n]);
    expect(sj.findCarmichaelNumbersInRange(0, 562)).toEqual([561n]);
    expect(sj.findCarmichaelNumbersInRange(0, 2000)).toEqual([561n, 1105n, 1729n]);
    expect(sj.isCarmichael(561)).toBe(true);
    expect(sj.carmichael.isCarmichael(563)).toBe(false);
    expect(sj.isCarmichael(sj.Rational.of(1105n))).toBe(true);
    expect(() => sj.findCarmichaelNumbersInRange(5, 1)).toThrow(RangeError);
  });

  it('poly_from_expr, parallel_poly_from_expr, gff', () => {
    const [p, o] = sj.polyFromExpr(sj.add(sj.pow(x, 2), y), [x]);
    expect([String(p), o.gens.map(s), o.domain]).toEqual(["Poly(x**2 + y, x, domain='ZZ[y]')", ['x'], 'ZZ[y]']);
    const [ps, o2] = sj.parallelPolyFromExpr([sj.add(sj.pow(x, 2), 1), sj.mul(x, y)]);
    expect([ps.map(String), o2.gens.map(s), o2.domain]).toEqual([["Poly(x**2 + 1, x, y, domain='ZZ')", "Poly(x*y, x, y, domain='ZZ')"], ['x', 'y'], 'ZZ']);
    const [ps2] = sj.parallelPolyFromExpr([x, sj.mul(sj.Rational.of(1n, 2n), x)], [x]);
    expect(ps2.map((q) => q.domain)).toEqual(['QQ', 'QQ']);
    expect(() => sj.gff(sj.sub(sj.pow(x, 3), x))).toThrow('symbolic falling factorial');
  });
});
