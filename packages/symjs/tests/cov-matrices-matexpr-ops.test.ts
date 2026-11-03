// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of the operations of sympy.matrices.expressions (MatAdd, MatMul,
 * MatPow, Inverse, Transpose, Adjoint, MatrixSlice, Trace, Determinant,
 * Permanent, ElementwiseApplyFunction, ImmutableMatrix) with the expected
 * values of SymPy 1.14 (str form).
 */

import { describe, expect, it } from 'vitest';
import { I as ImagUnit, Lambda, S, Matrix, SymFunction as UFunction, conjugate, cos, diff, latex, sin, sstr, symbol, symbols, transpose } from '../src';
import type { Expr } from '../src';
import {
  Adjoint,
  Determinant,
  ElementwiseApplyFunction,
  GenericIdentity,
  GenericZeroMatrix,
  Identity,
  ImmutableMatrix,
  Inverse,
  MatAdd,
  MatMul,
  MatPow,
  MatScalar,
  MatrixElement,
  MatrixExpr,
  MatrixSymbol,
  OneMatrix,
  Permanent,
  PermutationMatrix,
  Str,
  Trace,
  Transpose,
  ZeroMatrix,
  mergeExplicitMatAdd,
  mergeExplicitMatMul,
} from '../src/matrices/expressions';
import { doit } from '../src/calculus/doit';
import { MatMulNode, MatrixElementNode, MatrixSliceNode, TraceNode, negate, transposeOf } from '../src/matrices/expressions/matexpr';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [x, y, n, m, k, i] = symbols('x y n m k i');
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);
const Z = MatrixSymbol('Z', 2, 2);
const A = MatrixSymbol('A', 2, 3);
const B = MatrixSymbol('B', 3, 2);
const W = MatrixSymbol('W', n, n);
const X3 = MatrixSymbol('X', 3, 3);
const Mi = ImmutableMatrix([
  [1, 2],
  [3, 4],
]);

describe('construction', () => {
  it('validates dimensions and arguments', () => {
    expect(() => MatrixSymbol('A', symbol('q', { negative: true }), 2)).toThrow('The dimension specification q should be a nonnegative integer.');
    expect(() => MatrixSymbol('A', 1.5, 2)).toThrow('should be a nonnegative integer');
    expect(() => Transpose(2)).toThrow('2 is not a matrix');
    expect(() => MatAdd(A, MatrixSymbol('C', 2, 4))).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => MatPow(2, 2)).toThrow('MatPow base should be a matrix');
    expect(() => Inverse(2)).toThrow('mat should be a matrix');
    expect(() => Inverse(A)).toThrow('Inverse of non-square matrix A');
    expect(() => Trace(2)).toThrow('input to Trace, 2, is not a matrix');
    expect(() => Determinant(2)).toThrow('Input to Determinant, 2, not a matrix');
    expect(() => Determinant(A)).toThrow('Det of a non-square matrix');
    expect(() => Permanent(2)).toThrow('Input to Permanent, 2, not a matrix');
    expect(() => ElementwiseApplyFunction(sin, 2)).toThrow('2 must be a matrix instance.');
    expect(() => ElementwiseApplyFunction(Lambda([x, y], x.add(y)), X)).toThrow('should be able to accept 1 arguments.');
    // SymPy only raises in as_coeff_matrices
    expect(() => MatMul(symbol('a', { commutative: false }), X)).toThrow('noncommutative scalars in MatMul are not supported.');
  });
  it('ImmutableMatrix from entries, a function or a matrix expression', () => {
    expect(s(ImmutableMatrix(2, 2, [1, 2, 3, 4]))).toBe('Matrix([[1, 2], [3, 4]])');
    expect(s(ImmutableMatrix(2, 2, (a, b) => a + b))).toBe('Matrix([[0, 1], [1, 2]])');
    expect(s(ImmutableMatrix(OneMatrix(2, 2)))).toBe('Matrix([[1, 1], [1, 1]])');
    expect(s(ImmutableMatrix(Matrix.zeros(0, 2)))).toBe('Matrix(0, 2, [])');
    expect(s(ImmutableMatrix(0))).toBe('Matrix(0, 0, [])');
    expect(latex(ImmutableMatrix(1, 11, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))).toBe('\\left[\\begin{array}{ccccccccccc}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10\\end{array}\\right]');
    expect(s(ImmutableMatrix([[x]]).subs(x, 2))).toBe('Matrix([[2]])');
    expect(s(Mi.at(-1, -1))).toBe('4');
    expect(Mi.isMatrixExpr).toBe(false);
    expect(X.isMatrixExpr).toBe(true);
    expect(X.isScalar).toBe(false);
    expect(s(Mi.doit({ deep: false }))).toBe('Matrix([[1, 2], [3, 4]])');
  });
  it('Str', () => {
    const a = new Str('a');
    expect(latex(a)).toBe('a');
    expect(a.withArgs()).toBe(a);
  });
});

describe('MatAdd', () => {
  it('special sums, adjoint and printing', () => {
    expect(s(MatAdd())).toBe('0');
    expect(s(M(Adjoint(MatAdd(X, Y))).doit())).toBe('Adjoint(X) + Adjoint(Y)');
    // SymPy MatrixExpr.canonicalize returns the expression itself
    expect(s(M(MatAdd(X, X, Y)).canonicalize())).toBe('X + X + Y');
    const nested = MatAdd(X, MatAdd(Y, Z));
    expect(s(nested)).toBe('(Y + Z) + X');
    expect(latex(nested)).toBe('\\left(Y + Z\\right) + X');
    expect(s(mergeExplicitMatAdd(X))).toBe('X');
    expect(s(mergeExplicitMatMul(X))).toBe('X');
    expect(s(transposeOf(x))).toBe('x');
    expect(s(negate(x))).toBe('-x');
  });
  it('orders the terms like SymPy', () => {
    expect(s(M(MatAdd(MatMul(x, X, Y), Z)).doit())).toBe('x*X*Y + Z');
    expect(s(MatAdd(MatMul(x.pow(2), X), Y))).toBe('x**2*X + Y');
    expect(s(MatAdd(MatMul(x, X), MatMul(y, Y)))).toBe('x*X + y*Y');
    expect(s(MatAdd(MatMul(ImagUnit, X), Y))).toBe('I*X + Y');
    expect(s(MatAdd(MatMul(y, X), MatMul(x, Y), MatMul(x.mul(y), Z)))).toBe('x*Y + y*X + (x*y)*Z');
    expect(s(MatAdd(X3.slice([null, 1]), MatrixSymbol('Y', 3, 3).slice([null, 1])))).toBe('X[:1, :] + Y[:1, :]');
  });
});

describe('MatMul', () => {
  it('special products', () => {
    expect(s(MatMul())).toBe('I');
    expect(s(MatMul(2, 3))).toBe('6');
    // SymPy MatrixExpr.canonicalize returns the expression itself
    expect(s(M(MatMul(X, Identity(2), X)).canonicalize())).toBe('X*I*X');
    expect(s(MatMul(UFunction('f')(), X))).toBe('f()*X');
    expect(s(M(MatMul(x, X)).subs(x, y))).toBe('y*X');
    expect(s(M(MatMul(X, MatAdd(Y, Y))).doit({ deep: false }))).toBe('X*(Y + Y)');
    expect(s(X.div(Y))).toBe('X*Y**(-1)');
    // the product rule of an expression free of x
    expect(s(M(MatMul(2, X)).diffSelf(x, diff))).toBe('0');
  });
  it('determinants of products', () => {
    const P = MatrixSymbol('P', n, m);
    const Q = MatrixSymbol('Q', m, k);
    expect(() => Determinant(P.mul(Q)).doit()).toThrow('Invalid matrices being multiplied');
    expect(s(Determinant(A.mul(B)).doit())).toBe('Determinant(A*B)');
    expect(s(Determinant(MatMul(X, Y)).doit({ deep: false }))).toBe('Determinant(X)*Determinant(Y)');
  });
  it('canonicalization rules', () => {
    expect(s(M(MatMul(MatAdd(X, Y), 2)).doit())).toBe('2*X + 2*Y');
    expect(s(M(MatMul(X, Y, Inverse(MatMul(X, Y)))).doit())).toBe('I');
    expect(s(M(MatMul(Inverse(MatMul(X, Y)), X, Y)).doit())).toBe('I');
    expect(s(M(MatMul(X, OneMatrix(2, 2))).doit())).toBe('X*1');
    expect(s(M(MatMul(Mi, 2)).doit())).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(M(MatMul(2, 3, Mi)).doit())).toBe('Matrix([[6, 12], [18, 24]])');
    expect(s(M(MatMul(2, Mi)).doit())).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(M(MatMul(PermutationMatrix([1, 0, 2]), PermutationMatrix([0, 2, 1]))).doit())).toBe('PermutationMatrix((0 2 1))');
  });
});

describe('MatPow and Inverse', () => {
  it('entries', () => {
    expect(s(Inverse(X).at(0, 0))).toBe('X[1, 1]/(X[0, 0]*X[1, 1] - X[0, 1]*X[1, 0])');
    expect(s(MatPow(W, k).at(0, 0))).toBe('(W**k)[0, 0]');
    expect(s(MatPow(X, 2).at(0, 1))).toBe('X[0, 0]*X[0, 1] + X[0, 1]*X[1, 1]');
    // SymPy writes the entry of X**k out with the eigenvalues of X; it is left unevaluated here
    expect(s(MatPow(X, k).at(0, 0))).toBe('(X**k)[0, 0]');
    const e = MatPow(X, -2).at(0, 1);
    const ref = X.at(0, 0).mul(X.at(0, 1)).add(X.at(0, 1).mul(X.at(1, 1))).neg().div(X.at(0, 0).mul(X.at(1, 1)).sub(X.at(0, 1).mul(X.at(1, 0))).pow(2));
    expect(s(e.sub(ref).simplify())).toBe('0');
  });
  it('doit, subs and printing', () => {
    expect(s(M(MatPow(X, n)).subs(n, 2))).toBe('X**2');
    expect(s(M(MatPow(MatPow(Mi, 2), 3)).doit({ deep: false }))).toBe('Matrix([[5743, 8370], [12555, 18298]])');
    expect(latex(MatPow(ImmutableMatrix([[x.pow(2)]]), 2))).toBe('\\left(\\left[\\begin{matrix}x^{2}\\end{matrix}\\right]\\right)^{2}');
  });
  it('derivatives', () => {
    // SymPy 1.14 raises TypeError (Mix of Matrix and Scalar symbols) for these derivatives
    expect(s(diff(MatPow(MatMul(x, X), 2), x))).toBe('(2*x)*X**2');
    expect(s(diff(MatPow(MatMul(x, X), -2), x))).toBe('(-2/x**3)*X**(-2)');
    expect(s(M(MatPow(MatAdd(MatMul(x, X), Y), -2)).diffSelf(x, diff))).toBe('-(x*X + Y)**(-1)*X*(x*X + Y)**(-2) - (x*X + Y)**(-2)*X*(x*X + Y)**(-1)');
    expect(s(diff(Inverse(MatMul(x, X)), x))).toBe('(-1/x**2)*X**(-1)');
    expect(s((Inverse(MatAdd(MatMul(x, X), Y)) as MatrixExpr).diffSelf(x, diff))).toBe('-(x*X + Y)**(-1)*X*(x*X + Y)**(-1)');
    // SymPy raises as well
    expect(() => diff(MatPow(MatMul(x, X), k), x)).toThrow('diff: MatPow does not define a derivative');
    expect(() => diff(MatPow(X, x), x)).toThrow('diff: MatPow does not define a derivative');
  });
});

describe('Transpose and Adjoint', () => {
  it('Transpose', () => {
    expect(s(M(Transpose(W)).subs(n, 2))).toBe('W.T');
    expect(s(M(Transpose(MatMul(X, Y))).doit({ deep: false }))).toBe('Y.T*X.T');
    expect(s(M(Transpose(X)).doit({ deep: false }))).toBe('X.T');
    // SymPy 1.14 gives X; the derivative of (x*X).T is X.T
    expect(s(diff(Transpose(MatMul(x, X)), x))).toBe('X.T');
    expect(latex(Transpose(ImmutableMatrix([[x.pow(2), 1]])))).toBe('\\left(\\left[\\begin{matrix}x^{2} & 1\\end{matrix}\\right]\\right)^{T}');
  });
  it('Adjoint', () => {
    expect(s(M(Adjoint(W)).subs(n, 2))).toBe('Adjoint(W)');
    expect(s(M(Adjoint(MatMul(X, Y))).doit({ deep: false }))).toBe('Adjoint(Y)*Adjoint(X)');
    expect(s(M(Adjoint(Adjoint(X))).doit())).toBe('X');
    expect(s(M(Transpose(Adjoint(X))).doit())).toBe('Adjoint(X.T)');
    expect(s(M(Adjoint(X)).conjugate())).toBe('X.T');
    expect(s(conjugate(Adjoint(X)))).toBe('X.T');
    expect(latex(Adjoint(MatMul(X, Y)))).toBe('\\left(X Y\\right)^{\\dagger}');
    expect(latex(MatMul(X, Adjoint(Y)))).toBe('X Y^{\\dagger}');
    // SymPy 1.14 raises AttributeError; for a real x the derivative of Adjoint(x*X) is Adjoint(X)
    const xr = symbol('xr', { real: true });
    expect(s(diff(Adjoint(MatMul(xr, X)), xr))).toBe('Adjoint(X)');
  });
});

describe('MatrixSlice', () => {
  it('normalizes and validates slices', () => {
    expect(s(X3.slice(-1))).toBe('X[2:, :]');
    expect(s(X3.slice([-2, -1]))).toBe('X[1:2, :]');
    expect(() => X3.slice([1, 1])).toThrow('Invalid slice');
    expect(() => X3.slice([0, 5])).toThrow('Invalid slice');
    const V = MatrixSymbol('V', symbol('p', { positive: true, integer: true }), symbol('p', { positive: true, integer: true }));
    const p = symbol('p', { positive: true, integer: true });
    expect(() => M(V.slice([0, p, 2])).slice([0, p])).toThrow('Invalid slice');
    expect(latex(X3.slice([0, 2, 2], [1, null]))).toBe('X\\left[:2:2, 1:\\right]');
    expect(s(X3.slice([1, 3, 2], [null, 2]))).toBe('X[1::2, :2]');
    expect(s(M(W.slice([0, k])).subs(k, 1))).toBe('W[:1, :]');
    expect(M(X3.slice([0, 2], [0, 2])) instanceof MatrixSliceNode).toBe(true);
  });
});

describe('Trace, Determinant and Permanent', () => {
  it('Trace', () => {
    const t = Trace(W).subs(n, 2) as TraceNode;
    expect(s(t)).toBe('Trace(W)');
    expect(t.arg.shape.map(s)).toEqual(['2', '2']);
    expect(s(Trace(Mi).doit({ deep: false }))).toBe('5');
    expect(s(Trace(X).doit({ deep: false }))).toBe('Trace(X)');
    expect(s(Trace(X).asExplicit())).toBe('X[0, 0] + X[1, 1]');
    expect(s(Trace(X).rewrite('Sum'))).toBe('X[0, 0] + X[1, 1]');
    expect(s(Trace(X).rewrite('sin'))).toBe('Trace(X)');
    expect(s(transpose(Trace(X)))).toBe('Trace(X)');
    // SymPy: Trace(X).diff(X[0, 0]) = 1. diff() replaces the element by a dummy
    // before differentiating, which misses it inside Trace(X); the handler is right
    expect(s((Trace(X) as TraceNode).diffSelf(X.at(0, 0), diff))).toBe('1');
    expect(s(Trace(MatrixSymbol('V', i, i)).rewrite('Sum'))).toBe('Sum(V[i0, i0], (i0, 0, i - 1))');
    expect(s(Trace(X).simplify())).toBe('Trace(X)');
    expect(s(Trace(X.mul(MatAdd(Y, Z))).expand())).toBe('Trace(X*Y + X*Z)');
    expect(s(M(MatMul(Trace(X).add(1), Y)).simplify())).toBe('(Trace(X) + 1)*Y');
    expect(s(diff(Trace(W), n))).toBe('0');
  });
  it('Determinant and Permanent', () => {
    expect(s(Determinant(W).subs(n, 2))).toBe('Determinant(W)');
    expect(s(Permanent(W).subs(n, 2))).toBe('Permanent(W)');
  });
});

describe('MatrixElement and derivatives of special matrices', () => {
  it('derivatives with respect to a dimension', () => {
    expect(s(diff(W, n))).toBe('0');
    // SymPy 1.14 raises AttributeError for these
    expect(s(diff(Identity(n), n))).toBe('0');
    expect(s(diff(ZeroMatrix(n, n), n))).toBe('0');
    expect(s(diff(W.at(0, 0), n))).toBe('0');
  });
  it('subs of the special matrices', () => {
    expect(s(ZeroMatrix(n, 2).subs(n, 3))).toBe('0');
    expect(M(ZeroMatrix(n, 2).subs(n, 3)).shape.map(s)).toEqual(['3', '2']);
    expect(M(OneMatrix(n, 2).subs(n, 3)).shape.map(s)).toEqual(['3', '2']);
  });
  it('MatrixElement doit', () => {
    expect(s((MatrixElement(X, 0, 1) as MatrixElementNode).doit({ deep: false }))).toBe('X[0, 1]');
    const e = X.at(0, 1) as MatrixElementNode;
    expect(s(e.diffSelf(X.at(0, 1), diff))).toBe('1');
    expect(s(e.diffSelf(X.at(1, 1), diff))).toBe('0');
    expect(s(e.diffSelf(MatrixSymbol('B', 2, 2).at(0, 0), diff))).toBe('0');
    expect(new MatrixElementNode(MatMul(X, A), S.Zero, S.Zero).diffSelf(X.at(0, 0), diff)).toBe(undefined);
    expect(s(new MatrixElementNode(MatMul(x, W), S.Zero, S.Zero).diffSelf(x, diff))).toBe('W[0, 0]');
    expect(new MatrixElementNode(MatPow(X, x), S.Zero, S.Zero).diffSelf(x, () => x)).toBe(undefined);
    const bad = new MatrixElementNode(x, S.Zero, S.Zero);
    expect(bad.doit()).toBe(bad);
    expect(bad.diffSelf(x, diff)).toBe(undefined);
  });
});

describe('ElementwiseApplyFunction', () => {
  it('construction and doit', () => {
    expect(s(X.applyfunc(Lambda(x, x.pow(2))))).toBe('Lambda(x, x**2).(X)');
    expect(s(MatrixSymbol('V', 1, 1).applyfunc(Lambda(x, x)))).toBe('V');
    // SymPy prints Lambda(_x, _x).(X): its IdentityFunction reports is_identity False
    expect(s(M(ElementwiseApplyFunction(Lambda(x, x), X)).doit())).toBe('X');
    expect(M(ElementwiseApplyFunction(sin, W).subs(n, 2)).shape.map(s)).toEqual(['2', '2']);
    expect(s(M(ElementwiseApplyFunction(sin, MatMul(X, Y))).doit({ deep: false }))).toBe('Lambda(_d, sin(_d)).(X*Y)');
    expect(s(M(ElementwiseApplyFunction(sin, X)).doit())).toBe('Lambda(_d, sin(_d)).(X)');
    expect(s(M(ElementwiseApplyFunction(sin, ElementwiseApplyFunction(cos, X))).doit())).toBe('Lambda(_d, sin(cos(_d))).(X)');
  });
});

describe('defaults and remaining paths', () => {
  /** A matrix expression with only the required members (the defaults of MatrixExpr). */
  class Bare extends MatrixExpr {
    constructor(args: readonly Expr[] = []) {
      super('Bare', args);
    }
    get shape(): [Expr, Expr] {
      return [S.One, S.One];
    }
    withArgs(args: readonly Expr[]): Expr {
      return new Bare(args);
    }
  }
  /** A matrix scalar with only the required members (the defaults of MatScalar). */
  class BareScalar extends MatScalar {
    constructor(a: Expr) {
      super('BareScalar', [a]);
    }
    withArgs(args: readonly Expr[]): Expr {
      return new BareScalar(args[0] ?? S.Zero);
    }
  }
  it('the base class defaults', () => {
    const b = new Bare();
    expect(() => b.at(0, 0)).toThrow('Indexing not implemented for Bare');
    expect(b.diffSelf(x, diff)).toBe(undefined);
    expect(b.doit({ deep: false })).toBe(b);
    expect(doit(b)).toBe(b);
    expect(s(new Bare([MatAdd(X, X)]).doit())).toBe('Bare(2*X)');
    const bs = new BareScalar(Trace(MatAdd(X, X)));
    expect(bs.doit({ deep: false })).toBe(bs);
    expect(s(bs.doit())).toBe('BareScalar(2*Trace(X))');
    expect(s(doit(bs))).toBe('BareScalar(Trace(2*X))');
    const bx = new BareScalar(x);
    expect(bx.doit()).toBe(bx);
    expect(M(X.applyfunc(sin)).diffSelf(x, diff)).toBe(undefined);
  });
  it('doit of MatrixSymbol and equalsExplicit with a symbolic shape', () => {
    expect(X.doit({ deep: false })).toBe(X);
    expect(s(doit(X))).toBe('X');
    expect(X.equalsExplicit(W)).toBe(false);
  });
  it('sort keys of products with several scalar factors', () => {
    expect(s(M(MatAdd(MatMul(x, y, X), Z)).doit({ deep: false }))).toBe('(x*y)*X + Z');
    expect(s(MatAdd(new MatMulNode([X, new MatMulNode([x, y, Y])]), Z))).toBe('X*(x*y*Y) + Z');
    expect(s(M(MatMul(Trace(X).add(1), Y)).expand())).toBe('(Trace(X) + 1)*Y');
  });
  it('MatPow with explicit and special bases', () => {
    expect(s(MatPow(X, 1).at(0, 0))).toBe('X[0, 0]');
    // SymPy diagonalizes the matrix; the power with a symbolic exponent is kept unevaluated
    expect(s(M(MatPow(Mi, x)).doit())).toBe('Matrix([[1, 2], [3, 4]])**x');
    expect(() => M(MatPow(OneMatrix(2, 2), -2)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(() => M(MatPow(ZeroMatrix(2, 2), -2)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(s(Determinant(OneMatrix(1, 1)).doit({ deep: false }))).toBe('1');
    expect(s(Inverse(OneMatrix(1, 1)).doit({ deep: false }))).toBe('I');
    expect(s(M(MatPow(OneMatrix(1, 1), 5)).doit({ deep: false }))).toBe('I');
    expect(s(OneMatrix(2, 2).doit({ deep: false }))).toBe('1');
    expect(s(diff(OneMatrix(n, n), n))).toBe('0');
  });
  it('products with inverses of products', () => {
    expect(s(M(MatMul(X, Y, Inverse(MatMul(X, Y)))).doit({ deep: false }))).toBe('I');
    expect(s(M(MatMul(Inverse(MatMul(X, Y)), X, Y)).doit({ deep: false }))).toBe('I');
  });
  it('merge_explicit of a product', () => {
    expect(s(mergeExplicitMatMul(MatMul(Mi, 2)))).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(mergeExplicitMatMul(MatMul(2, 3, Mi)))).toBe('Matrix([[6, 12], [18, 24]])');
  });
  it('generic identity and zero', () => {
    expect(GenericIdentity().key).toBe('GenericIdentity()');
    expect(GenericZeroMatrix().key).toBe('GenericZeroMatrix()');
    expect(GenericIdentity().withArgs()).toEqual(GenericIdentity());
    expect(GenericZeroMatrix().withArgs()).toEqual(GenericZeroMatrix());
  });
  it('substituting a scalar for the matrix', () => {
    expect(s(M(Transpose(X).subs(X, x)).doit())).toBe('x');
  });
  it('Trace.rewrite with a used name and ElementwiseApplyFunction.doit', () => {
    const [i0] = symbols('i0');
    expect(s(Trace(MatrixSymbol('V', i.add(i0), i.add(i0))).rewrite('Sum'))).toBe('Sum(V[i1, i1], (i1, 0, i + i0 - 1))');
    expect(s(M(ElementwiseApplyFunction(sin, MatAdd(X, X))).doit())).toBe('Lambda(_d, sin(_d)).(2*X)');
  });
  it('ImmutableMatrix with missing entries', () => {
    expect(s(ImmutableMatrix(2, 2))).toBe('Matrix([[0, 0], [0, 0]])');
    expect(s(ImmutableMatrix(2, 2, [1]))).toBe('Matrix([[1, 0], [0, 0]])');
    expect(s(ImmutableMatrix(2))).toBe('Matrix(2, 0, [])');
  });
});
