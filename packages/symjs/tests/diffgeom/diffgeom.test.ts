// SPDX-License-Identifier: MIT
import { describe, expect, it } from 'vitest';
import {
  Expr,
  ExtensionExpr,
  Sym,
  Matrix,
  S,
  add,
  mul,
  sub,
  sin,
  exp,
  sqrt,
  rcall,
  simplify,
  expand,
  latex,
  diff,
  Lambda,
  Tuple,
  ImmutableDenseNDimArray,
} from '@symjs/symjs';
import {
  Manifold,
  Patch,
  CoordSystem,
  CoordinateSymbol,
  Point,
  Differential,
  TensorProduct as TP,
  WedgeProduct as WP,
  Commutator,
  LieDerivative,
  BaseCovarDerivativeOp,
  CovarDerivativeOp,
  covariantOrder,
  contravariantOrder,
  vectorsInBasis,
  intcurveSeries,
  intcurveDiffequ,
  twoformToMatrix,
  metricToChristoffel1st,
  metricToChristoffel2nd,
  metricToRiemannComponents,
  metricToRicciComponents,
} from '../../src/diffgeom/diffgeom';
import { R2, R2R, R2P, R2Origin } from '../../src/diffgeom/rn';

const { x, y, eX, eY, dx, dy } = R2;
const t = new Sym('t');
const flat = add(TP(dx, dx), TP(dy, dy));
const eq = (a: Expr, b: Expr | number) => expect(simplify(sub(a, b)).equals(0), `${a} != ${b}`).toBe(true);

describe('charts and points', () => {
  it('represents manifolds, patches and coordinate identities', () => {
    const m = new Manifold('M', 2),
      p = new Patch('P', m),
      c = new CoordSystem('C', p);
    expect(String(m)).toBe('M');
    expect(String(p)).toBe('P');
    expect(String(c)).toBe('C');
    expect(latex(new Manifold('M^a_b', 2))).toBe('\\text{M}^{a}_{b}');
    expect(latex(m)).toBe('\\text{M}');
    expect(latex(p)).toBe('\\text{P}_{\\text{M}}');
    expect(latex(c)).toBe('\\text{C}^{\\text{P}}_{\\text{M}}');
    expect(c.dim).toBe(2);
    expect(c.manifold).toBe(m);
    expect(p.dim).toBe(2);
    expect(c.symbols.map(String)).toEqual(['C_0', 'C_1']);
    expect(c.withArgs(c.args).equals(c)).toBe(true);
    expect(p.withArgs(p.args).equals(p)).toBe(true);
    expect(m.withArgs(m.args).equals(m)).toBe(true);
    expect(new CoordSystem('D', p, ['u', 'v']).symbols.map(String)).toEqual(['u', 'v']);
    expect(() => new Manifold('bad', -1)).toThrow(RangeError);
    expect(() => p.withArgs([t])).toThrow(TypeError);
    expect(() => m.withArgs([t])).toThrow(RangeError);
    expect(() => c.baseScalar(4)).toThrow(RangeError);
    expect(() => c.baseVector(-1)).toThrow(RangeError);
  });
  it('distinguishes coordinate symbols from ordinary symbols and fields', () => {
    const cs = R2R.symbols[0]!;
    expect(cs).toBeInstanceOf(CoordinateSymbol);
    expect(cs.equals(new Sym('x', { real: true }))).toBe(false);
    expect(cs.equals(x)).toBe(false);
    expect(cs.sortClass).toBe('CoordinateSymbol');
    expect(String(R2R.symbols[1]!.rewrite(R2P))).toBe('rho*sin(theta)');
    expect(cs.rewrite('exp')).toBe(cs);
    expect(diff(cs, cs).equals(1)).toBe(true);
    expect(diff(x, t).equals(0)).toBe(true);
    expect(x.freeSymbols().size).toBe(0);
    expect(x.diffSelf().equals(0)).toBe(true);
  });
  it('transforms points and prints scalar/vector fields', () => {
    const point = new Point(R2R, [3, 4]);
    expect(point.patch).toBe(R2Origin);
    expect(point.manifold).toBe(R2);
    expect(point.dim).toBe(2);
    expect(point.coords().data.map(String)).toEqual(['3', '4']);
    expect(R2R.pointToCoords(point).equals(point.coords())).toBe(true);
    eq(R2P.baseScalar(0).call(point), 5);
    expect(point.withArgs(point.args).equals(point)).toBe(true);
    expect(String(point)).toContain('Point(rectangular, Matrix');
    expect(new Point(R2R, [t, 2]).freeSymbols().has(t)).toBe(true);
    expect(() => R2R.point([1])).toThrow(RangeError);
    expect(x.call(1)).toBe(x);
    expect(x.call()).toBe(x);
    expect(x.withArgs(x.args).equals(x)).toBe(true);
    expect(eX.withArgs(eX.args).equals(eX)).toBe(true);
    expect(x.patch).toBe(R2Origin);
    expect(eX.patch).toBe(R2Origin);
    expect(x.manifold).toBe(R2);
    expect(eX.manifold).toBe(R2);
    expect(x.dim).toBe(2);
    expect(eX.dim).toBe(2);
    expect(String(eX)).toBe('e_x');
    expect(latex(eX)).toBe('\\partial_{x}');
    expect(latex(x)).toBe('\\mathbf{x}');
    expect(R2R.coordFunction(0).equals(x)).toBe(true);
    expect(R2R.coordFunctions().map(String)).toEqual(['x', 'y']);
  });
  it('computes transformations, Jacobians and determinants', () => {
    expect(R2P.transform(R2R, [2, 0]).data.map(String)).toEqual(['2', '0']);
    expect(R2P.transformation(R2R).call(2, 0).data.map(String)).toEqual(['2', '0']);
    expect(String(R2P.transformation(R2R))).toContain('Lambda((rho, theta), Matrix');
    expect(R2R.transform(R2R).data.every((v, i) => v.equals(R2R.symbols[i]!))).toBe(true);
    expect(R2P.jacobianMatrix(R2R, [2, 0]).data.map(String)).toEqual(['1', '0', '0', '2']);
    eq(R2P.jacobianDeterminant(R2R, [2, 0]), 2);
    expect(
      R2R.coordTupleTransformTo(R2P, Matrix.of([[3], [4]]))
        .get(0, 0)
        .equals(5),
    ).toBe(true);
    expect(() => R2P.transform(R2R, [1])).toThrow(RangeError);
    expect(() => R2P.transformation(R2R).call(1)).toThrow(RangeError);
    expect(() => R2R.jacobian(R2P, [1])).toThrow(RangeError);
  });
  it('inverts and composes coordinate relations, including Lambda signatures', () => {
    const a = new Sym('a'),
      b = new Sym('b'),
      c = new Sym('c'),
      d = new Sym('d');
    const relations = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>([
      [
        ['A', 'B'],
        [
          [a, b],
          [mul(2, a), add(mul(3, b), 1)],
        ],
      ],
      [
        ['C', 'B'],
        [
          [c, d],
          [sub(-2, c), mul(2, d)],
        ],
      ],
    ]);
    const A = new CoordSystem('A', R2Origin, [a, b], relations),
      B = new CoordSystem('B', R2Origin, [c, d], relations),
      C = new CoordSystem('C', R2Origin, [c, d], relations);
    expect(A.transform(C, [2, 3]).data.map(String)).toEqual(['-6', '5']);
    expect(C.transform(A, [-6, 5]).data.map(String)).toEqual(['2', '3']);
    expect(B.transform(A, [4, 10]).data.map(String)).toEqual(['2', '3']);
    const rel = new Map<readonly [string, string], Lambda>([[['D', 'E'], Lambda([a, b], new Tuple([mul(2, a), b]))]]);
    const D = new CoordSystem('D', R2Origin, [a, b], rel),
      E = new CoordSystem('E', R2Origin, [c, d], rel);
    expect(D.transform(E, [2, 3]).data.map(String)).toEqual(['4', '3']);
    const F = new CoordSystem('F', R2Origin, [a, b]);
    expect(() => F.transform(A)).toThrow(/not connected/);
    F.connectTo(A, [a, b], [b, a], { fillInGaps: true });
    expect(F.transform(A, [1, 2]).data.map(String)).toEqual(['2', '1']);
    expect(A.transform(F, [1, 2]).data.map(String)).toEqual(['2', '1']);
    F.connectTo(B, [a, b], [a, b], { inverse: false });
    expect(F.transforms.size).toBe(2);
    const one = new CoordSystem('one', new Patch('P1', new Manifold('M1', 1)), [a]);
    expect(String(one.transformation(one))).toContain('Lambda(a,');
  });
  it('rejects ambiguous and impossible inverse transformations', () => {
    const a = new Sym('a'),
      b = new Sym('b');
    const rel = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>([
      [
        ['A1', 'B1'],
        [[a], [a.pow(2)]],
      ],
    ]);
    const A = new CoordSystem('A1', R2Origin, [a], rel),
      B = new CoordSystem('B1', R2Origin, [b], rel);
    expect(() => B.transform(A)).toThrow(/multiple inverse/);
    const p = new Sym('p', { positive: true }),
      q = new Sym('q', { positive: true });
    const impossible = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>([
      [
        ['PA', 'PB'],
        [[p], [p.neg()]],
      ],
    ]);
    const PA = new CoordSystem('PA', R2Origin, [p], impossible),
      PB = new CoordSystem('PB', R2Origin, [q], impossible);
    expect(() => PB.transform(PA)).toThrow(/Cannot solve/);
    expect(() => A.connectTo(B, [a], [S.Zero])).toThrow(/underdetermined/);
    const over = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>([
      [
        ['OA', 'OB'],
        [[a], [a, a]],
      ],
    ]);
    const OA = new CoordSystem('OA', R2Origin, [a], over),
      OB = new CoordSystem('OB', R2Origin, [a, b], over);
    expect(OB.transform(OA, [3, 3]).data.map(String)).toEqual(['3']);
    expect(() => OB.transform(OA, [2, 3])).toThrow(/Cannot solve/);
  });
});

describe('fields and tensors', () => {
  it('takes directional derivatives and commutators', () => {
    eq(eX.call(x.pow(2)), mul(2, x));
    eq(eX.call(3), 0);
    expect(eX.call()).toBe(eX);
    eq(Commutator(eX, eY), 0);
    eq(Commutator(eX, eX), 0);
    eq(Commutator(mul(x, eX), mul(x, eY)), mul(x, eY));
    const bracket = Commutator(eX, R2.eR);
    expect(String(bracket)).toBe('Commutator(e_x, e_rho)');
    expect(bracket.isCommutative).toBe(false);
    // A commutator remains a vector field even when its charts differ.
    expect(contravariantOrder(bracket)).toBe(1);
    eq(rcall(bracket, x), mul(y, sin(R2.theta)).div(add(x.pow(2), y.pow(2))));
    expect((bracket as ExtensionExpr).withArgs(bracket.args).equals(bracket)).toBe(true);
    expect(() => Commutator(eX, x)).toThrow(RangeError);
    expect(() => eX.call(dx)).toThrow(RangeError);
    expect(() => eX.call(eY)).toThrow(RangeError);
  });
  it('evaluates exterior derivatives, including the commutator term', () => {
    const f = mul(x, dy),
      df = Differential(f);
    eq(rcall(df, eX, eY), 1);
    eq(rcall(df, eX, mul(x, eY)), x);
    eq(rcall(df, mul(y, eX), mul(x, eY)), mul(x, y));
    eq(Differential(df), 0);
    expect(rcall(dx, null).equals(dx)).toBe(true);
    expect(rcall(df).equals(df)).toBe(true);
    expect(rcall(df, null).equals(df)).toBe(true);
    expect(() => rcall(dx, x)).toThrow(RangeError);
    expect(() => Differential(eX)).toThrow(RangeError);
    expect(() => rcall(dx, eX, eY)).toThrow(RangeError);
    expect(() => rcall(df, eX)).toThrow(/Partial contraction/);
    expect(String(Differential(mul(x, y)))).toBe('d(x*y)');
    expect(latex(dx)).toBe('\\operatorname{d}x');
    expect(String(dx)).toBe('dx');
    expect(latex(Differential(mul(x, y)))).toContain('\\left(');
    expect((dx as ExtensionExpr).withArgs(dx.args).equals(dx)).toBe(true);
  });
  it('contracts ordinary and alternating tensor products', () => {
    eq(rcall(TP(dx, dy), eX, eY), 1);
    eq(rcall(TP(dx, dy), eY, eX), 0);
    eq(rcall(TP(dx, mul(x, dy)), mul(x, eX), eY), x.pow(2));
    eq(rcall(TP(eX, eY), x.pow(2), y.pow(2)), mul(4, x, y));
    expect(rcall(TP(dx, dy), eX).equals(dy)).toBe(true);
    expect(rcall(TP(dx, dy), null, eY).equals(dx)).toBe(true);
    expect(rcall(TP(eX, eY), null, y).equals(eX)).toBe(true);
    expect(TP(x, dx).equals(mul(x, dx))).toBe(true);
    eq(TP(2, 3), 6);
    eq(TP(), 1);
    eq(rcall(TP(TP(dx, dy), dx), eX, eY, eX), 1);
    eq(rcall(WP(dx, dy), eX, eY), 1);
    eq(rcall(WP(dx, dy), eY, eX), -1);
    eq(rcall(WP(WP(dx, dy), dx), eX, eY, eX), 0);
    eq(rcall(WP(eX, eY), y, null), eX.neg());
    // Omitting the second slot must agree with an explicit partial contraction.
    eq(rcall(WP(eX, eY), y), eX.neg());
    expect(() => rcall(TP(dx, dy), eX, eX, eX)).toThrow(RangeError);
    const tp = TP(dx, dy) as ExtensionExpr;
    expect(tp.withArgs(tp.args).equals(tp)).toBe(true);
  });
  it('computes Lie derivatives with the tensor contraction correction', () => {
    eq(LieDerivative(eX, y), 0);
    eq(LieDerivative(add(eX, eY), x), 1);
    eq(LieDerivative(eX, eX), 0);
    expect(String(LieDerivative(eX, R2.eR))).toBe('Commutator(e_x, e_rho)');
    const ld = LieDerivative(eX, TP(dx, dy));
    expect(ld.isCommutative).toBe(false);
    eq(rcall(ld, eX, eY), 0);
    expect((ld as ExtensionExpr).withArgs(ld.args).equals(ld)).toBe(true);
    // L_(x e_x) dx = dx; SymPy 1.14 omits evaluating dx on the commutator.
    eq(rcall(LieDerivative(mul(x, eX), dx), eX), 1);
    eq(rcall(LieDerivative(mul(x, eX), TP(dx, dy)), eX, eY), 1);
    expect(covariantOrder(ld)).toBe(2);
    expect(contravariantOrder(ld)).toBe(0);
    expect(() => LieDerivative(dx, dx)).toThrow(RangeError);
    const X = sub(mul(x, eX), mul(y, eY)),
      Y = sub(mul(add(x.pow(2), y.pow(2)), eX), mul(x, y, eY));
    eq(expand(LieDerivative(X, Y)), sub(sub(mul(x.pow(2), eX), mul(3, y.pow(2), eX)), mul(x, y, eY)));
  });
  it('validates covariant and contravariant orders', () => {
    expect(covariantOrder(add(dx, dy))).toBe(1);
    expect(contravariantOrder(add(eX, eY))).toBe(1);
    expect(covariantOrder(TP(dx, dy))).toBe(2);
    expect(contravariantOrder(TP(eX, eY))).toBe(2);
    expect(covariantOrder(x.pow(3))).toBe(0);
    expect(contravariantOrder(x.pow(3))).toBe(0);
    expect(covariantOrder(2, true)).toBe(-1);
    expect(contravariantOrder(2, true)).toBe(-1);
    expect(covariantOrder(x, true)).toBe(0);
    expect(covariantOrder(mul(2, dx))).toBe(1);
    for (const order of [covariantOrder, contravariantOrder]) {
      expect(() => order(add(dx, eX))).toThrow(RangeError);
      expect(() => order(dx.pow(2))).toThrow(RangeError);
      // Powers of vectors have no tensor meaning; SymPy checks the wrong variance.
      expect(() => order(eX.pow(2))).toThrow(RangeError);
    }
    expect(() => covariantOrder(mul(dx, dy))).toThrow(RangeError);
    expect(() => contravariantOrder(mul(eX, eY))).toThrow(RangeError);
  });
  it('changes vector bases without changing scalar coefficients', () => {
    const converted = vectorsInBasis(eX, R2P);
    eq(rcall(converted, R2.r), x.div(sqrt(add(x.pow(2), y.pow(2)))));
    expect(vectorsInBasis(x, R2P).equals(x)).toBe(true);
    expect(vectorsInBasis(mul(x, eX), R2R).equals(mul(x, eX))).toBe(true);
  });
});

describe('connections, curvature and integral curves', () => {
  it('computes a metric matrix and rejects ambiguous/non-symmetric metrics', () => {
    expect(twoformToMatrix(flat).data.map(String)).toEqual(['1', '0', '0', '1']);
    expect(twoformToMatrix(TP(dx, dy)).data.map(String)).toEqual(['0', '0', '1', '0']);
    expect(twoformToMatrix(WP(dx, dy)).data.map(String)).toEqual(['0', '-1', '1', '0']);
    expect(() => twoformToMatrix(dx)).toThrow(RangeError);
    expect(() => twoformToMatrix(add(TP(dx, dx), TP(R2.dr, R2.dr)))).toThrow(RangeError);
    for (const fn of [
      metricToChristoffel1st,
      metricToChristoffel2nd,
      metricToRiemannComponents,
      metricToRicciComponents,
    ])
      expect(() => fn(TP(dx, dy))).toThrow(/not symmetric/);
  });
  it('computes flat and curved Christoffel, Riemann and Ricci components', () => {
    expect(
      metricToChristoffel1st(flat)
        .flatElements()
        .every((e) => e.equals(0)),
    ).toBe(true);
    expect(
      metricToChristoffel2nd(flat)
        .flatElements()
        .every((e) => e.equals(0)),
    ).toBe(true);
    expect(
      metricToRiemannComponents(flat)
        .flatElements()
        .every((e) => e.equals(0)),
    ).toBe(true);
    expect(
      metricToRicciComponents(flat)
        .flatElements()
        .every((e) => e.equals(0)),
    ).toBe(true);
    const polarMetric = add(TP(R2.dr, R2.dr), mul(R2.r.pow(2), TP(R2.dtheta, R2.dtheta)));
    const ch = metricToChristoffel2nd(polarMetric);
    eq(ch.get(0, 1, 1), R2.r.neg());
    eq(ch.get(1, 0, 1), R2.r.pow(-1));
    expect(
      metricToRiemannComponents(polarMetric)
        .flatElements()
        .every((e) => e.equals(0)),
    ).toBe(true);
    const curved = add(mul(exp(mul(2, R2.r)), TP(R2.dr, R2.dr)), mul(R2.r.pow(2), TP(R2.dtheta, R2.dtheta)));
    eq(metricToRiemannComponents(curved).get(0, 1, 0, 1), mul(exp(mul(-2, R2.r)), R2.r));
    eq(metricToRicciComponents(curved).get(0, 0), R2.r.pow(-1));
    // SymPy's hyperbolic half-plane test: ds² = (dx² + dy²)/y².
    const hyperbolic = metricToRicciComponents(flat.div(y.pow(2)));
    eq(hyperbolic.get(0, 0), y.pow(-2).neg());
    eq(mul(add(hyperbolic.get(0, 0), hyperbolic.get(1, 1)), y.pow(2)), -2);
  });
  it('differentiates scalar, vector and tensor fields covariantly', () => {
    const ch = metricToChristoffel2nd(flat),
      cv = new BaseCovarDerivativeOp(R2R, 0, ch);
    eq(cv.call(x), 1);
    eq(cv.call(mul(x, eX)), eX);
    eq(cv.call(add(mul(x, eX), mul(y, eY))), eX);
    eq(cv.call(TP(mul(x, eX), eY)), TP(eX, eY));
    expect(cv.withArgs(cv.args).equals(cv)).toBe(true);
    const cv2 = new CovarDerivativeOp(mul(x, eX), ch);
    eq(cv2.call(x), x);
    eq(cv2.call(mul(x, eX)), mul(x, eX));
    expect(cv2.withArgs(cv2.args).equals(cv2)).toBe(true);
    expect(
      new BaseCovarDerivativeOp(R2R, 0, [
        [
          [0, 0],
          [0, 0],
        ],
        [
          [0, 0],
          [0, 0],
        ],
      ]).christoffel,
    ).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(
      new CovarDerivativeOp(eX, [
        [
          [0, 0],
          [0, 0],
        ],
        [
          [0, 0],
          [0, 0],
        ],
      ]).christoffel,
    ).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(() => cv.call(dx)).toThrow(/forms/);
    expect(() => new CovarDerivativeOp(dx, [])).toThrow(RangeError);
    expect(() => new CovarDerivativeOp(add(eX, R2.eR), ch)).toThrow(/mixed/);
  });
  it('computes Taylor coefficients and integral-curve equations', () => {
    const v = sub(mul(x, eY), mul(y, eX)),
      start = R2R.point([1, 0]);
    const series = intcurveSeries(v, t, start, 4);
    eq(series.get(0, 0), sub(1, t.pow(2).div(2)));
    eq(series.get(1, 0), sub(t, t.pow(3).div(6)));
    expect(intcurveSeries(eX, t, start, 3, { coeffs: true }).map((m) => m.data.map(String))).toEqual([
      ['1', '0'],
      ['t', '0'],
      ['0', '0'],
    ]);
    expect(intcurveSeries(eX, t, start).rows).toBe(2);
    expect(intcurveSeries(eX, t, start, 0).data.every((e) => e.equals(0))).toBe(true);
    expect(intcurveSeries(v, t, start, 2, { coordSys: R2P }).rows).toBe(2);
    const [equations, initial] = intcurveDiffequ(v, t, start);
    expect(equations.map(String)).toEqual(['f_1(t) + Derivative(f_0(t), t)', '-f_0(t) + Derivative(f_1(t), t)']);
    expect(initial.map(String)).toEqual(['f_0(0) - 1', 'f_1(0)']);
    expect(intcurveDiffequ(v, t, start, R2P)[0].map(String)).toEqual([
      'Derivative(f_0(t), t)',
      'Derivative(f_1(t), t) - 1',
    ]);
    expect(() => intcurveSeries(dx, t, start)).toThrow(RangeError);
    expect(() => intcurveSeries(eX, t, start, -1)).toThrow(RangeError);
    expect(() => intcurveDiffequ(dx, t, start)).toThrow(RangeError);
  });
});
