// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/algebras/quaternion.ts (SymPy sympy/algebras/quaternion.py and
// sympy/algebras/tests/test_quaternion.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  Abs,
  Derivative,
  E,
  Expr,
  type ExprLike,
  I,
  Integral,
  Matrix,
  Rational,
  S,
  Sym,
  AppliedUndef,
  acos,
  add,
  asin,
  atan,
  atan2,
  conjugate,
  cos,
  diff,
  doit,
  evalf,
  expand,
  factor,
  im,
  integrate,
  latex,
  log,
  mul,
  parse,
  pi,
  pow,
  pretty,
  re,
  sign,
  simplify,
  sin,
  sqrt,
  sstr,
  sub,
  subs,
  symbols,
  trigsimp,
} from '../../src';
import { Quaternion } from '../../src/algebras';
import type { QuaternionNode } from '../../src/algebras';

const [w, x, y, z] = symbols('w x y z');
const [a, b, c, d] = symbols('a b c d');
const phi = new Sym('phi');
const half = Rational.of(1n, 2n);
const r = (p: number, q: number): Rational => Rational.of(BigInt(p), BigInt(q));

/** Structural equality, like SymPy ==. */
const same = (u: Expr, v: Expr): boolean => u.key === v.key;
const strs = (xs: readonly Expr[]): string[] => xs.map(sstr);
const mat = (m: Matrix): string => m.toString();
const qmul = (...xs: ExprLike[]): QuaternionNode => mul(...xs) as QuaternionNode;

describe('Quaternion construction and printing', () => {
  it('prints like SymPy (str, LaTeX and pretty)', () => {
    expect(sstr(Quaternion(1, 2, 3, 4))).toBe('1 + 2*i + 3*j + 4*k');
    const q = Quaternion(1, pow(x, 2), half, -3);
    expect(sstr(q)).toBe('1 + x**2*i + 1/2*j + (-3)*k');
    expect(latex(q)).toBe('1 + x^{2} i + \\frac{1}{2} j + \\left(-3\\right) k');
    expect(pretty(q)).toBe('1 + x**2*i + 1/2*j + (-3)*k');
    expect(pretty(Quaternion(add(mul(x, half), 1), mul(-1, x), mul(3, I), pow(x, 3)))).toBe('(x/2 + 1) + (-x)*i + 3*I*j + x**3*k');
    expect(latex(Quaternion(mul(-1, x), add(x, 1), mul(x, y), r(-1, 2)))).toBe(
      '- x + \\left(x + 1\\right) i + x y j + \\left(- \\frac{1}{2}\\right) k',
    );
    expect(latex(Quaternion(new Integral([x, x]), 0, 0, 0))).toBe('\\int x\\, dx + 0 i + 0 j + 0 k');
    expect(sstr(Quaternion())).toBe('0 + 0*i + 0*j + 0*k');
  });

  it('constructs over the complex field and with a norm', () => {
    expect(sstr(Quaternion(x, pow(x, 3), x, pow(x, 2), { realField: false }))).toBe('x + x**3*i + x*j + x**2*k');
    const q2 = Quaternion(add(3, mul(4, I)), add(2, mul(5, I)), 0, add(7, mul(8, I)), { realField: false });
    expect(sstr(q2)).toBe('(3 + 4*I) + (2 + 5*I)*i + 0*j + (7 + 8*I)*k');
    expect(q2.realField).toBe(false);
    const q = Quaternion(w, x, y, z, { norm: 1 });
    expect(sstr(q)).toBe('w + x*i + y*j + z*k');
    expect(sstr(q.norm())).toBe('1');
    expect(q.isCommutative).toBe(false);
    expect([...q.freeSymbols()].map(String).sort()).toEqual(['w', 'x', 'y', 'z']);
    // the norm is an attribute: equality ignores it, as in SymPy
    expect(q.equals(Quaternion(w, x, y, z))).toBe(true);
    const nc = new Sym('nc', { commutative: false });
    expect(() => Quaternion(w, x, nc, z)).toThrow('arguments have to be commutative');
  });

  it('sets and checks the norm (SymPy set_norm, _check_norm)', () => {
    const q = Quaternion(a, b, c, d);
    expect(sstr(q.norm())).toBe('sqrt(a**2 + b**2 + c**2 + d**2)');
    q.setNorm(1);
    expect(sstr(q.norm())).toBe('1');
    q.setNorm(undefined);
    expect(sstr(q.norm())).toBe('sqrt(a**2 + b**2 + c**2 + d**2)');
    expect(() => Quaternion(1, 2, 3, 4, { norm: -1 })).toThrow('Input norm must be positive.');
    expect(() => Quaternion(1, 2, 3, 4, { norm: 0 })).toThrow('Input norm must be positive.');
    expect(() => Quaternion(1, 2, 3, 4, { norm: 2 })).toThrow('Incompatible value for norm.');
    expect(sstr(Quaternion(1, 2, 3, 4, { norm: sqrt(30) }).norm())).toBe('sqrt(30)');
    // a symbolic norm and symbolic elements are not checked
    expect(sstr(Quaternion(1, 2, 3, 4, { norm: x }).norm())).toBe('x');
    expect(sstr(Quaternion(x, 2, 3, 4, { norm: 2 }).norm())).toBe('2');
    expect(() => Quaternion(1, 0, 0, 0, { norm: I })).toThrow('Input norm must be positive.');
  });

  it('keeps real_field only on the same object, like SymPy (every new quaternion is over the real field)', () => {
    const qc = Quaternion(x, 2, 3, 4, { realField: false });
    expect(qc.realField).toBe(false);
    // SymPy _eval_subs builds a new quaternion even when nothing is substituted
    const fresh: Expr[] = [qc.subs(y, 1), qc.subs(x, 1), conjugate(qc), simplify(qc), qc.withArgs(qc.args), qc.diff(x), evalf(qc), qc.integrate(x), qc.neg(), mul(qc, qc), add(qc, qc), qc.normalize(), factor(qc)];
    for (const e of fresh) expect((e as QuaternionNode).realField).toBe(true);
    // expand and trigsimp of an unchanged quaternion return it (SymPy keeps real_field=False)
    expect((expand(qc) as QuaternionNode).realField).toBe(false);
    expect((trigsimp(qc) as QuaternionNode).realField).toBe(false);
  });

  it('parses like SymPy sympify', () => {
    expect(sstr(parse('Quaternion(1, 2, 3, 4)'))).toBe('1 + 2*i + 3*j + 4*k');
    expect(parse('Quaternion(1, 2, 3, 4)')).toBeInstanceOf(Quaternion);
    expect(sstr(parse('Quaternion(1, x)'))).toBe('1 + x*i + 0*j + 0*k');
    expect((parse('Quaternion(1, 2, 3, 4, 0)') as QuaternionNode).realField).toBe(false);
    expect((parse('Quaternion(1, 2, 3, 4, 1, sqrt(30))') as QuaternionNode).norm().toString()).toBe('sqrt(30)');
    expect(sstr(parse('2*Quaternion(1, 2, 3, 4) + 1'))).toBe('3 + 4*i + 6*j + 8*k');
    expect(() => parse('Quaternion(1, 2, 3, 4, 1, 2, 3)')).toThrow('Quaternion.__new__() takes from 1 to 7 positional arguments but 8 were given');
  });

  it('converts to and from matrices', () => {
    const q = Quaternion(a, b, c, d);
    expect(mat(q.toMatrix())).toBe('Matrix([[a], [b], [c], [d]])');
    expect(mat(q.toMatrix(true))).toBe('Matrix([[b], [c], [d]])');
    expect(sstr(Quaternion.fromMatrix([a, b, c, d]))).toBe('a + b*i + c*j + d*k');
    expect(sstr(Quaternion.fromMatrix([b, c, d]))).toBe('0 + b*i + c*j + d*k');
    expect(() => Quaternion.fromMatrix([a, b])).toThrow('Input elements must have length 3 or 4, got 2 elements');
    // test_to_and_from_Matrix
    const p = Quaternion(w, x, y, z);
    expect(p.addQuaternion(Quaternion.fromMatrix(p.toMatrix()).neg()).isZeroQuaternion()).toBe(true);
    expect(p.vectorPart().addQuaternion(Quaternion.fromMatrix(p.toMatrix(true)).neg()).isZeroQuaternion()).toBe(true);
  });

  it('gives the product matrices (SymPy product_matrix_left/right)', () => {
    const q1 = Quaternion(1, 0, 0, 1);
    const q2 = Quaternion(a, b, c, d);
    expect(mat(q1.productMatrixLeft)).toBe('Matrix([[1, 0, 0, -1], [0, 1, -1, 0], [0, 1, 1, 0], [1, 0, 0, 1]])');
    expect(mat(q1.productMatrixLeft.mul(q2.toMatrix()))).toBe('Matrix([[a - d], [b - c], [b + c], [a + d]])');
    expect(mat(qmul(q1, q2).toMatrix())).toBe('Matrix([[a - d], [b - c], [b + c], [a + d]])');
    expect(mat(q1.productMatrixRight)).toBe('Matrix([[1, 0, 0, -1], [0, 1, 1, 0], [0, -1, 1, 0], [1, 0, 0, 1]])');
    expect(mat(q1.productMatrixRight.mul(q2.toMatrix()))).toBe('Matrix([[a - d], [b + c], [-b + c], [a + d]])');
    expect(mat(qmul(q2, q1).toMatrix())).toBe('Matrix([[a - d], [b + c], [-b + c], [a + d]])');
    // test_product_matrices
    const p1 = Quaternion(w, x, y, z);
    expect(qmul(p1, q2).toMatrix().equals(p1.productMatrixLeft.mul(q2.toMatrix()).expand())).toBe(true);
    expect(qmul(p1, q2).toMatrix().equals(q2.productMatrixRight.mul(p1.toMatrix()).expand())).toBe(true);
    const R1 = p1.productMatrixLeft.mul(p1.productMatrixRight.T).slice([1, 2, 3], [1, 2, 3]);
    const R2 = p1.toRotationMatrix().mul(pow(p1.norm(), 2)).map((e) => simplify(e));
    expect(R1.expand().equals(R2.expand())).toBe(true);
  });
});

describe('Quaternion arithmetic', () => {
  it('adds (SymPy add)', () => {
    const q1 = Quaternion(1, 2, 3, 4);
    const q2 = Quaternion(5, 6, 7, 8);
    expect(sstr(q1.addQuaternion(q2))).toBe('6 + 8*i + 10*j + 12*k');
    expect(sstr(add(q1, 5))).toBe('6 + 2*i + 3*j + 4*k');
    const xr = new Sym('x', { real: true });
    expect(sstr(q1.addQuaternion(xr))).toBe('(x + 1) + 2*i + 3*j + 4*k');
    const q3 = Quaternion(add(3, mul(4, I)), add(2, mul(5, I)), 0, add(7, mul(8, I)), { realField: false });
    expect(sstr(q3.addQuaternion(add(2, mul(3, I))))).toBe('(5 + 7*I) + (2 + 5*I)*i + 0*j + (7 + 8*I)*k');
    const q = Quaternion(w, x, y, z);
    expect(same(add(q, q), Quaternion(mul(2, w), mul(2, x), mul(2, y), mul(2, z)))).toBe(true);
    expect(sstr(q.add(x))).toBe('(w + x) + x*i + y*j + z*k');
    expect(sstr(add(x, y, q))).toBe('(w + x + y) + x*i + y*j + z*k');
  });

  it('adds complex and real scalars (test_quaternion_complex_real_addition)', () => {
    const br = new Sym('b', { real: true });
    const nc = new Sym('c', { commutative: false });
    const q = Quaternion(w, x, y, z);
    expect(same(add(1, q), Quaternion(add(1, w), x, y, z))).toBe(true);
    expect(same(add(I, q), Quaternion(w, add(1, x), y, z))).toBe(true);
    expect(same(add(br, q), Quaternion(add(w, br), x, y, z))).toBe(true);
    // a complex symbol (SymPy complex=True) splits into re and im; symjs has no complex assumption, so I*b with b real stands in
    expect(same(add(mul(I, br), q), Quaternion(w, add(x, br), y, z))).toBe(true);
    expect(sstr(re(mul(I, br)))).toBe('0');
    expect(sstr(im(mul(I, br)))).toBe('b');
    expect(() => add(nc, q)).toThrow('Only commutative expressions can be added with a Quaternion.');
    expect(() => mul(q, nc)).toThrow('Only commutative expressions can be multiplied with a Quaternion.');
    expect(() => mul(nc, q)).toThrow('Only commutative expressions can be multiplied with a Quaternion.');
    expect(same(q.neg(), Quaternion(mul(-1, w), mul(-1, x), mul(-1, y), mul(-1, z)))).toBe(true);
    expect(same(mul(-1, q), q.neg())).toBe(true);

    const q1 = Quaternion(add(3, mul(4, I)), add(2, mul(5, I)), 0, add(7, mul(8, I)), { realField: false });
    const q2 = Quaternion(1, 4, 7, 8);
    const z23 = add(2, mul(3, I));
    expect(same(add(q1, z23), Quaternion(add(5, mul(7, I)), add(2, mul(5, I)), 0, add(7, mul(8, I))))).toBe(true);
    expect(same(add(q2, z23), Quaternion(3, 7, 7, 8))).toBe(true);
    expect(same(mul(q1, z23), Quaternion(mul(z23, add(3, mul(4, I))), mul(z23, add(2, mul(5, I))), 0, mul(z23, add(7, mul(8, I)))))).toBe(true);
    expect(same(mul(q2, z23), Quaternion(-10, 11, 38, -5))).toBe(true);

    const p1 = Quaternion(1, 2, 3, 4);
    const p0 = Quaternion(0, 0, 0, 0);
    expect(same(add(p1, p0), p1)).toBe(true);
    expect(same(sub(p1, p0), p1)).toBe(true);
    expect(same(sub(p1, p1), p0)).toBe(true);
  });

  it('subtracts like SymPy: a - q for a scalar a is the unevaluated Add(a, -q) (Expr.__rsub__)', () => {
    const q = Quaternion(1, 2, 3, 4);
    const cases: [Expr, string, string][] = [
      [sub(1, q), '1 + (-1) + (-2)*i + (-3)*j + (-4)*k', '1 + \\left(-1\\right) + \\left(-2\\right) i + \\left(-3\\right) j + \\left(-4\\right) k'],
      [x.sub(q), 'x + (-1) + (-2)*i + (-3)*j + (-4)*k', 'x + \\left(-1\\right) + \\left(-2\\right) i + \\left(-3\\right) j + \\left(-4\\right) k'],
      [sub(0, q), '(-1) + (-2)*i + (-3)*j + (-4)*k', '\\left(-1\\right) + \\left(-2\\right) i + \\left(-3\\right) j + \\left(-4\\right) k'],
      [sub(add(x, y), q), 'x + y + (-1) + (-2)*i + (-3)*j + (-4)*k', 'x + y + \\left(-1\\right) + \\left(-2\\right) i + \\left(-3\\right) j + \\left(-4\\right) k'],
      [sub(add(x, 1), q), 'x + 1 + (-1) + (-2)*i + (-3)*j + (-4)*k', 'x + 1 + \\left(-1\\right) + \\left(-2\\right) i + \\left(-3\\right) j + \\left(-4\\right) k'],
      [sub(2, Quaternion(x, 0, 0, 0)), '2 + (-x) + 0*i + 0*j + 0*k', '2 + - x + 0 i + 0 j + 0 k'],
      [sub(q, 1), '0 + 2*i + 3*j + 4*k', '0 + 2 i + 3 j + 4 k'],
      [q.sub(x), '(1 - x) + 2*i + 3*j + 4*k', '\\left(1 - x\\right) + 2 i + 3 j + 4 k'],
      [sub(q, Quaternion(1, 1, 1, 1)), '0 + 1*i + 2*j + 3*k', '0 + 1 i + 2 j + 3 k'],
      [sub(Quaternion(1, 1, 1, 1), q), '0 + (-1)*i + (-2)*j + (-3)*k', '0 + \\left(-1\\right) i + \\left(-2\\right) j + \\left(-3\\right) k'],
    ];
    for (const [e, s1, l] of cases) {
      expect(sstr(e)).toBe(s1);
      expect(latex(e)).toBe(l);
    }
    expect(sub(1, q).kind).toBe('Add');
    // without a quaternion, subtraction is unchanged
    expect(sstr(x.sub(y))).toBe('x - y');
    expect(sstr(sub(x, y))).toBe('x - y');
    // SymPy: (1 - q) + 2 is 3 + (-1) + ...; (1 - q) + q raises ValueError (the Add is not commutative)
    expect(sstr(add(sub(1, q), 2))).toBe('3 + (-1) + (-2)*i + (-3)*j + (-4)*k');
    expect(() => add(sub(1, q), q)).toThrow('Only commutative expressions can be added with a Quaternion.');
  });

  it('multiplies (SymPy mul and _generic_mul)', () => {
    const q1 = Quaternion(1, 2, 3, 4);
    const q2 = Quaternion(5, 6, 7, 8);
    expect(sstr(q1.mul(q2))).toBe('(-60) + 12*i + 30*j + 24*k');
    expect(sstr(q1.mul(2))).toBe('2 + 4*i + 6*j + 8*k');
    const xr = new Sym('x', { real: true });
    expect(sstr(q1.mul(xr))).toBe('x + 2*x*i + 3*x*j + 4*x*k');
    const q3 = Quaternion(add(3, mul(4, I)), add(2, mul(5, I)), 0, add(7, mul(8, I)), { realField: false });
    expect(sstr(q3.mul(add(2, mul(3, I))))).toBe('(2 + 3*I)*(3 + 4*I) + (2 + 3*I)*(2 + 5*I)*i + 0*j + (2 + 3*I)*(7 + 8*I)*k');
    expect(sstr(Quaternion.genericMul(q1, q2))).toBe('(-60) + 12*i + 30*j + 24*k');
    expect(sstr(Quaternion.genericMul(q1, 2))).toBe('2 + 4*i + 6*j + 8*k');
    expect(sstr(Quaternion.genericMul(q1, xr))).toBe('x + 2*x*i + 3*x*j + 4*x*k');
    expect(sstr(Quaternion.genericMul(q3, add(2, mul(3, I))))).toBe('(2 + 3*I)*(3 + 4*I) + (2 + 3*I)*(2 + 5*I)*i + 0*j + (2 + 3*I)*(7 + 8*I)*k');
    // test_quaternion_multiplication
    const p1 = Quaternion(add(3, mul(4, I)), add(2, mul(5, I)), 0, add(7, mul(8, I)), { realField: false });
    const p2 = Quaternion(1, 2, 3, 5);
    const p3 = Quaternion(1, 1, 1, y);
    expect(sstr(Quaternion.genericMul(4, 1))).toBe('4');
    expect(same(Quaternion.genericMul(4, p1), Quaternion(add(12, mul(16, I)), add(8, mul(20, I)), 0, add(28, mul(32, I))))).toBe(true);
    expect(same(p2.mul(2), Quaternion(2, 4, 6, 10))).toBe(true);
    expect(same(p2.mul(p3), Quaternion(add(mul(-5, y), -4), add(mul(3, y), -2), add(9, mul(-2, y)), add(y, 4)))).toBe(true);
    const qr = Quaternion(...symbols('q0 q1 q2 q3', { real: true }));
    const br = new Sym('b', { real: true });
    // z = I*b stands in for a complex symbol (symjs has no complex assumption)
    const zc = mul(I, br);
    const zq = Quaternion(re(zc), im(zc), 0, 0);
    expect(same(mul(zc, qr), mul(zq, qr))).toBe(true);
    expect(same(mul(qr, zc), mul(qr, zq))).toBe(true);
    // several factors are multiplied from the left
    expect(sstr(mul(2, x, Quaternion(1, 0, 0, 1), Quaternion(0, 1, 0, 0)))).toBe('0 + 2*x*i + 2*x*j + 0*k');
  });

  it('keeps a pre-defined norm through products (test_quaternion_construction_norm)', () => {
    const q1 = Quaternion(a, b, c, d);
    const q2 = Quaternion(w, x, y, z);
    expect(sstr(expand(sub(pow(qmul(q1, q2).norm(), 2), mul(pow(q1.norm(), 2), pow(q2.norm(), 2)))))).toBe('0');
    const q3 = Quaternion(w, x, y, z, { norm: 1 });
    expect(same(qmul(q1, q3).norm(), q1.norm())).toBe(true);
  });

  it('takes powers, inverses and divides (SymPy pow, inverse, __truediv__)', () => {
    const q = Quaternion(w, x, y, z);
    const q1 = Quaternion(1, 2, 3, 4);
    const q0 = Quaternion(0, 0, 0, 0);
    const n2 = add(pow(w, 2), pow(x, 2), pow(y, 2), pow(z, 2));
    expect(sstr(q1.pow(4))).toBe('668 + (-224)*i + (-336)*j + (-448)*k');
    expect(same(q.inverse(), Quaternion(w, mul(-1, x), mul(-1, y), mul(-1, z)).div(n2))).toBe(true);
    expect(same(q.inverse(), q.pow(-1))).toBe(true);
    expect(() => q0.inverse()).toThrow('Cannot compute inverse for a quaternion with zero norm');
    expect(() => mul(1, pow(q0, -1))).toThrow('Cannot compute inverse for a quaternion with zero norm');
    expect(same(q.pow(2), Quaternion(add(pow(w, 2), mul(-1, pow(x, 2)), mul(-1, pow(y, 2)), mul(-1, pow(z, 2))), mul(2, w, x), mul(2, w, y), mul(2, w, z)))).toBe(true);
    expect(same(pow(q, 2), q.pow(2))).toBe(true);
    expect(same(q1.pow(-2), Quaternion(r(-7, 225), r(-1, 225), r(-1, 150), r(-2, 225)))).toBe(true);
    expect(same(pow(q1, -2), q1.pow(-2))).toBe(true);
    expect(same(q1.pow(1), q1)).toBe(true);
    expect(sstr(q1.pow(0))).toBe('1 + 0*i + 0*j + 0*k');
    expect(sstr(q1.div(2))).toBe('1/2 + 1*i + 3/2*j + 2*k');
    // SymPy: q1**(-0.5) and q1**n raise TypeError; the method q1.pow(-0.5) returns NotImplemented,
    // which JavaScript cannot return (a public result is never undefined), so it throws the same TypeError
    expect(() => q1.pow(-0.5)).toThrow(TypeError);
    expect(() => pow(q1, -0.5)).toThrow(TypeError);
    expect(() => pow(q1, new Sym('n'))).toThrow(TypeError);
    // SymPy q1**q2 raises TypeError as well (both __pow__ and __rpow__ give NotImplemented)
    expect(() => pow(q1, Quaternion(5, 6, 7, 8))).toThrow(TypeError);
    expect(() => pow(q1, new Sym('n', { integer: true }))).toThrow(TypeError);
    // b**q for a scalar b stays unevaluated (SymPy Pow(2, q))
    expect(pow(2, q1).kind).toBe('Pow');
  });

  it('conjugates', () => {
    const q = Quaternion(w, x, y, z);
    expect(same(conjugate(q), Quaternion(w, mul(-1, x), mul(-1, y), mul(-1, z)))).toBe(true);
    expect(same(q.conjugate(), conjugate(q))).toBe(true);
    expect(sstr((conjugate(Quaternion(1, 2, 3, 4, { norm: sqrt(30) })) as QuaternionNode).norm())).toBe('sqrt(30)');
  });

  it('works with floating-point rotations (test_issue_25254)', () => {
    const p = Quaternion(1, 0, 0, 0);
    const q = Quaternion.fromAxisAngle([1, 1, 1], (3 * Math.PI) / 4);
    const qi = q.inverse();
    const test = mul(q, p, qi) as QuaternionNode;
    expect(test.addQuaternion(p.neg()).norm().toNumber()).toBeLessThan(1e-10);
  });
});

describe('Quaternion functions', () => {
  it('exp, log and pow_cos_sin', () => {
    const q1 = Quaternion(1, 2, 3, 4);
    const s29 = sqrt(29);
    expect(same(q1.exp(), Quaternion(mul(E, cos(s29)), mul(2, s29, E, sin(s29), r(1, 29)), mul(3, s29, E, sin(s29), r(1, 29)), mul(4, s29, E, sin(s29), r(1, 29))))).toBe(true);
    expect(sstr(q1.exp())).toBe('E*cos(sqrt(29)) + 2*sqrt(29)*E*sin(sqrt(29))/29*i + 3*sqrt(29)*E*sin(sqrt(29))/29*j + 4*sqrt(29)*E*sin(sqrt(29))/29*k');
    expect(sstr(q1.log())).toBe('log(sqrt(30)) + 2*sqrt(29)*acos(sqrt(30)/30)/29*i + 3*sqrt(29)*acos(sqrt(30)/30)/29*j + 4*sqrt(29)*acos(sqrt(30)/30)/29*k');
    const t = acos(mul(sqrt(30), r(1, 30)));
    expect(same(q1.log(), Quaternion(log(sqrt(30)), mul(2, s29, t, r(1, 29)), mul(3, s29, t, r(1, 29)), mul(4, s29, t, r(1, 29))))).toBe(true);
    const t2 = mul(2, t);
    expect(same(q1.powCosSin(2), Quaternion(mul(30, cos(t2)), mul(60, s29, sin(t2), r(1, 29)), mul(90, s29, sin(t2), r(1, 29)), mul(120, s29, sin(t2), r(1, 29))))).toBe(true);
    expect(sstr(q1.powCosSin(4))).toBe(
      '900*cos(4*acos(sqrt(30)/30)) + 1800*sqrt(29)*sin(4*acos(sqrt(30)/30))/29*i + 2700*sqrt(29)*sin(4*acos(sqrt(30)/30))/29*j + 3600*sqrt(29)*sin(4*acos(sqrt(30)/30))/29*k',
    );
  });

  it('differentiates and integrates', () => {
    expect(same(diff(Quaternion(x, x, x, x), x), Quaternion(1, 1, 1, 1))).toBe(true);
    expect(sstr(Quaternion(x, pow(x, 2), 1, 2).diff(x))).toBe('1 + 2*x*i + 0*j + 0*k');
    // SymPy Quaternion.diff gives the zero quaternion for a constant one
    expect(sstr(Quaternion(1, 2, 3, 4).diff(x))).toBe('0 + 0*i + 0*j + 0*k');
    expect(sstr(doit(Derivative(Quaternion(x, pow(x, 2), 1, 2), x)))).toBe('1 + 2*x*i + 0*j + 0*k');
    expect(same(integrate(Quaternion(x, x, x, x), x), Quaternion(mul(pow(x, 2), half), mul(pow(x, 2), half), mul(pow(x, 2), half), mul(pow(x, 2), half)))).toBe(true);
    expect(same(Quaternion(1, x, pow(x, 2), pow(x, 3)).integrate(x), Quaternion(x, mul(pow(x, 2), half), mul(pow(x, 3), r(1, 3)), mul(pow(x, 4), r(1, 4))))).toBe(true);
    expect(same(Quaternion(sin(x), cos(x), sin(mul(2, x)), cos(mul(2, x))).integrate(x), Quaternion(mul(-1, cos(x)), sin(x), mul(-1, cos(mul(2, x)), half), mul(sin(mul(2, x)), half)))).toBe(true);
    // SymPy integrate(x, y): one variable after the other
    expect(same(Quaternion(pow(x, 2), pow(y, 2), pow(z, 2), mul(x, y, z)).integrate(x).integrate(y), Quaternion(mul(pow(x, 3), y, r(1, 3)), mul(x, pow(y, 3), r(1, 3)), mul(x, y, pow(z, 2)), mul(pow(x, 2), pow(y, 2), z, r(1, 4))))).toBe(true);
    expect(sstr(Quaternion(1, 2, 3, 4).integrate(x))).toBe('x + 2*x*i + 3*x*j + 4*x*k');
    expect(sstr(Quaternion(1, 2, 3, 4).integrate(x, [1, 5]))).toBe('4 + 8*i + 12*j + 16*k');
    expect(sstr(integrate(Quaternion(1, 2, 3, 4), x, [1, 5]))).toBe('4 + 8*i + 12*j + 16*k');
    expect(sstr(doit(new Integral([Quaternion(x, 1, 0, 0), x])))).toBe('x**2/2 + x*i + 0*j + 0*k');
  });

  it('substitutes, evaluates and simplifies', () => {
    const q = Quaternion.fromAxisAngle([0, 0, 1], phi);
    expect(same(q.subs(phi, 0), Quaternion(1, 0, 0, 0))).toBe(true);
    expect(sstr(subs(Quaternion(1, pow(x, 2), half, -3), [[x, 2]]))).toBe('1 + 4*i + 1/2*j + (-3)*k');
    // the pre-defined norm is substituted too, and checked
    const qn = Quaternion(x, 0, 0, 0, { norm: x });
    expect(sstr((qn.subs(x, 2) as QuaternionNode).norm())).toBe('2');
    expect(() => qn.subs(x, -2)).toThrow('Input norm must be positive.');
    // test_quaternion_evalf
    expect(same(evalf(Quaternion(sqrt(2), 0, 0, sqrt(3))), Quaternion(evalf(sqrt(2)), 0, 0, evalf(sqrt(3))))).toBe(true);
    expect(same(Quaternion(pow(sqrt(2), -1), 0, 0, pow(sqrt(2), -1)).evalf(), Quaternion(evalf(pow(sqrt(2), -1)), 0, 0, evalf(pow(sqrt(2), -1))))).toBe(true);
    expect(sstr(Quaternion(1, pow(sqrt(2), -1), pow(sqrt(3), -1), half).evalf())).toBe('1.0 + 0.707106781186548*i + 0.577350269189626*j + 0.5*k');
    expect(sstr(evalf(Quaternion(x, sqrt(2), 1, 2), 5))).toBe('x + 1.4142*i + 1.0*j + 2.0*k');
    expect(sstr(simplify(Quaternion(add(pow(sin(x), 2), pow(cos(x), 2)), mul(add(pow(x, 2), -1), pow(add(x, -1), -1)), 0, 0)))).toBe('1 + (x + 1)*i + 0*j + 0*k');
    expect(sstr(trigsimp(Quaternion(add(pow(sin(x), 2), pow(cos(x), 2)), mul(2, sin(x), cos(x)), 0, 0)))).toBe('1 + sin(2*x)*i + 0*j + 0*k');
    expect(sstr(expand(Quaternion(pow(add(x, 1), 2), 0, 0, 0)))).toBe('(x**2 + 2*x + 1) + 0*i + 0*j + 0*k');
    expect(sstr(factor(Quaternion(add(pow(x, 2), -1), 0, 0, 0)))).toBe('(x - 1)*(x + 1) + 0*i + 0*j + 0*k');
  });

  it('gives the parts, axis, angle, index vector and mensor', () => {
    const q = Quaternion(w, x, y, z);
    const q1 = Quaternion(1, 2, 3, 4);
    const q0 = Quaternion(0, 0, 0, 0);
    expect(same(q.norm(), sqrt(add(pow(w, 2), pow(x, 2), pow(y, 2), pow(z, 2))))).toBe(true);
    expect(same(q.normalize(), Quaternion(w, x, y, z).div(sqrt(add(pow(w, 2), pow(x, 2), pow(y, 2), pow(z, 2)))))).toBe(true);
    expect(sstr(Quaternion(4, 8, 13, 12).scalarPart())).toBe('4');
    expect(sstr(Quaternion(22, 23, 55, 8).scalarPart())).toBe('22');
    expect(same(q.scalarPart(), w)).toBe(true);
    expect(sstr(Quaternion(1, 1, 1, 1).vectorPart())).toBe('0 + 1*i + 1*j + 1*k');
    expect(sstr(Quaternion(4, 8, 13, 12).vectorPart())).toBe('0 + 8*i + 13*j + 12*k');
    expect(same(q.vectorPart(), Quaternion(0, x, y, z))).toBe(true);
    expect(sstr(Quaternion(1, 1, 1, 1).axis())).toBe('0 + sqrt(3)/3*i + sqrt(3)/3*j + sqrt(3)/3*k');
    expect(same(q1.axis(), Quaternion(0, mul(2, sqrt(29), r(1, 29)), mul(3, sqrt(29), r(1, 29)), mul(4, sqrt(29), r(1, 29))))).toBe(true);
    expect(same(q1.axis().pow(2), Quaternion(-1, 0, 0, 0))).toBe(true);
    expect(sstr(q0.axis().scalarPart())).toBe('0');
    const n = sqrt(add(pow(x, 2), pow(y, 2), pow(z, 2)));
    expect(same(q.axis(), Quaternion(0, mul(x, pow(n, -1)), mul(y, pow(n, -1)), mul(z, pow(n, -1))))).toBe(true);
    expect(sstr(Quaternion(1, 4, 4, 4).angle())).toBe('2*atan(4*sqrt(3))');
    expect(same(q1.angle(), mul(2, atan(sqrt(29))))).toBe(true);
    expect(same(q.angle(), mul(2, atan2(n, w)))).toBe(true);
    expect(sstr(Quaternion(2, 4, 2, 4).indexVector())).toBe('0 + 4*sqrt(10)/3*i + 2*sqrt(10)/3*j + 4*sqrt(10)/3*k');
    expect(same(q1.indexVector(), Quaternion(0, mul(2, sqrt(870), r(1, 29)), mul(3, sqrt(870), r(1, 29)), mul(4, sqrt(870), r(1, 29))))).toBe(true);
    expect(same(Quaternion(0, 3, 9, 4).indexVector(), Quaternion(0, 3, 9, 4))).toBe(true);
    expect(sstr(Quaternion(2, 4, 2, 4).mensor())).toBe('log(2*sqrt(10))');
    expect(sstr(Quaternion(2, 4, 2, 4).norm())).toBe('2*sqrt(10)');
    expect(same(Quaternion(4, 3, 9, 4).mensor(), log(sqrt(122)))).toBe(true);
    expect(same(Quaternion(3, 3, 0, 2).mensor(), log(sqrt(22)))).toBe(true);
  });

  it('decides the predicates', () => {
    const q1 = Quaternion(1, 2, 3, 4);
    const q0 = Quaternion(0, 0, 0, 0);
    expect(q0.isPure()).toBe(true);
    expect(q1.isPure()).toBe(false);
    expect(Quaternion(0, 0, 0, 3).isPure()).toBe(true);
    expect(Quaternion(0, 8, 13, 12).isPure()).toBe(true);
    expect(Quaternion(w, 2, 10, 3).isPure()).toBe('unknown');
    expect(q0.isZeroQuaternion()).toBe(true);
    expect(q1.isZeroQuaternion()).toBe(false);
    expect(Quaternion(1, 0, 0, 0).isZeroQuaternion()).toBe(false);
    expect(Quaternion(w, 0, 0, 0).isZeroQuaternion()).toBe('unknown');
    // a complex norm sqrt(-7 + 24*I) is decided numerically; f(1) cannot be evaluated (SymPy is_zero None)
    expect(Quaternion(add(3, mul(4, I)), 0, 0, 0, { realField: false }).isZeroQuaternion()).toBe(false);
    expect(Quaternion(new AppliedUndef('f', [S.One]), 1, 0, 0).isPure()).toBe('unknown');

    expect(Quaternion(1, 4, 4, 4).arcCoplanar(Quaternion(3, 8, 8, 8))).toBe(true);
    expect(Quaternion(2, 8, 13, 12).arcCoplanar(Quaternion(3, 8, 8, 8))).toBe(false);
    expect(q1.arcCoplanar(Quaternion(2, 4, 6, 8))).toBe(true);
    expect(q1.arcCoplanar(Quaternion(1, -2, -3, -4))).toBe(true);
    expect(q1.arcCoplanar(Quaternion(1, 8, 12, 16))).toBe(true);
    expect(q1.arcCoplanar(Quaternion(1, 2, 3, 4))).toBe(true);
    expect(q1.arcCoplanar(Quaternion(w, 4, 6, 8))).toBe(true);
    expect(q1.arcCoplanar(Quaternion(2, 7, 4, 1))).toBe(false);
    expect(q1.arcCoplanar(Quaternion(w, x, y, z))).toBe('unknown');
    expect(() => q1.arcCoplanar(q0)).toThrow('Neither of the given quaternions can be 0');
    expect(() => q0.arcCoplanar(q1)).toThrow('Neither of the given quaternions can be 0');

    expect(Quaternion.vectorCoplanar(Quaternion(0, 4, 4, 4), Quaternion(0, 8, 8, 8), Quaternion(0, 24, 24, 24))).toBe(true);
    expect(Quaternion.vectorCoplanar(Quaternion(0, 8, 16, 8), Quaternion(0, 8, 3, 12), Quaternion(0, 24, 24, 24))).toBe(false);
    expect(Quaternion.vectorCoplanar(Quaternion(0, 8, 12, 16), Quaternion(0, 4, 6, 8), Quaternion(0, 2, 3, 4))).toBe(true);
    expect(Quaternion.vectorCoplanar(q0, Quaternion(0, 4, 6, 8), Quaternion(0, 2, 3, 4))).toBe(true);
    expect(Quaternion.vectorCoplanar(Quaternion(0, 8, 2, 6), Quaternion(0, 1, 6, 6), Quaternion(0, 0, 3, 4))).toBe(false);
    expect(Quaternion.vectorCoplanar(Quaternion(0, 1, 3, 4), Quaternion(0, 4, w, 6), Quaternion(0, 6, 8, 1))).toBe('unknown');
    expect(() => Quaternion.vectorCoplanar(q0, Quaternion(0, 4, 6, 8), q1)).toThrow('The given quaternions must be pure');

    expect(Quaternion(0, 4, 4, 4).parallel(Quaternion(0, 8, 8, 8))).toBe(true);
    expect(Quaternion(0, 4, 4, 4).parallel(Quaternion(0, 8, 13, 12))).toBe(false);
    expect(Quaternion(0, 1, 2, 3).parallel(Quaternion(0, 2, 4, 6))).toBe(true);
    expect(Quaternion(0, 1, 2, 3).parallel(Quaternion(0, 2, 2, 6))).toBe(false);
    expect(Quaternion(0, 1, 2, 3).parallel(Quaternion(w, x, y, 6))).toBe('unknown');
    expect(() => q0.parallel(q1)).toThrow('The provided quaternions must be pure');
    expect(() => q1.parallel(q0)).toThrow('The provided quaternions must be pure');

    expect(Quaternion(0, 4, 4, 4).orthogonal(Quaternion(0, 8, 8, 8))).toBe(false);
    expect(Quaternion(0, 2, -2, 0).orthogonal(Quaternion(0, 2, 2, 0))).toBe(true);
    expect(Quaternion(0, 1, 2, 3).orthogonal(Quaternion(0, -2, 1, 0))).toBe(true);
    expect(Quaternion(0, 2, 4, 7).orthogonal(Quaternion(0, 2, 2, 6))).toBe(false);
    expect(Quaternion(0, 2, 4, 7).orthogonal(Quaternion(w, x, y, 6))).toBe('unknown');
    expect(() => q0.orthogonal(q1)).toThrow('The given quaternions must be pure');
    expect(() => q1.orthogonal(q0)).toThrow('The given quaternions must be pure');
  });
});

describe('Quaternion rotations', () => {
  it('converts from an axis and an angle (test_quaternion_axis_angle)', () => {
    expect(sstr(Quaternion.fromAxisAngle([div3(sqrt(3)), div3(sqrt(3)), div3(sqrt(3))], mul(2, pi, r(1, 3))))).toBe('1/2 + 1/2*i + 1/2*j + 1/2*k');
    const s2 = mul(sqrt(2), half);
    const is3 = pow(sqrt(3), -1);
    const data: [[number, number, number], Expr, Expr[]][] = [
      [[1, 0, 0], S.Zero, [S.One, S.Zero, S.Zero, S.Zero]],
      [[1, 0, 0], mul(pi, half), [s2, s2, S.Zero, S.Zero]],
      [[0, 1, 0], mul(pi, half), [s2, S.Zero, s2, S.Zero]],
      [[0, 0, 1], mul(pi, half), [s2, S.Zero, S.Zero, s2]],
      [[1, 0, 0], pi, [S.Zero, S.One, S.Zero, S.Zero]],
      [[0, 1, 0], pi, [S.Zero, S.Zero, S.One, S.Zero]],
      [[0, 0, 1], pi, [S.Zero, S.Zero, S.Zero, S.One]],
      [[1, 1, 1], pi, [S.Zero, is3, is3, is3]],
    ];
    for (const [axis, angle, e] of data) expect(same(Quaternion.fromAxisAngle(axis, angle), Quaternion(...e))).toBe(true);
    // test_quaternion_axis_angle_simplification
    const result = Quaternion.fromAxisAngle([1, 2, 3], asin(4));
    const h = sin(mul(asin(4), half));
    expect(same(result.a, cos(mul(asin(4), half)))).toBe(true);
    expect(same(result.b, mul(sqrt(14), h, r(1, 14)))).toBe(true);
    expect(same(result.c, mul(sqrt(14), h, r(1, 7)))).toBe(true);
    expect(same(result.d, mul(3, sqrt(14), h, r(1, 14)))).toBe(true);
  });

  it('converts from a rotation matrix', () => {
    const M = Matrix.of([[cos(phi), mul(-1, sin(phi)), 0], [sin(phi), cos(phi), 0], [0, 0, 1]]);
    const q3 = trigsimp(Quaternion.fromRotationMatrix(M));
    expect(same(q3, Quaternion(mul(sqrt(2), sqrt(add(cos(phi), 1)), half), 0, 0, mul(sqrt(add(2, mul(-2, cos(phi)))), sign(sin(phi)), half)))).toBe(true);
    expect(sstr(q3)).toBe('sqrt(2)*sqrt(cos(phi) + 1)/2 + 0*i + 0*j + sqrt(2 - 2*cos(phi))*sign(sin(phi))/2*k');
  });

  it('converts to an axis and an angle', () => {
    const [axis, angle] = Quaternion(1, 1, 1, 1).toAxisAngle();
    expect(strs(axis)).toEqual(['sqrt(3)/3', 'sqrt(3)/3', 'sqrt(3)/3']);
    expect(sstr(angle)).toBe('2*pi/3');
    const [ax1, an1] = Quaternion(1, 2, 3, 4).toAxisAngle();
    expect(strs(ax1)).toEqual(strs([mul(2, sqrt(29), r(1, 29)), mul(3, sqrt(29), r(1, 29)), mul(4, sqrt(29), r(1, 29))]));
    expect(same(an1, mul(2, acos(mul(sqrt(30), r(1, 30)))))).toBe(true);
    const theta = new Sym('theta', { real: true });
    const q2 = Quaternion(cos(mul(theta, half)), 0, 0, sin(mul(theta, half)));
    const [ax2, an2] = q2.toAxisAngle();
    expect(strs(ax2)).toEqual(strs([S.Zero, S.Zero, mul(sin(mul(theta, half)), pow(Abs(sin(mul(theta, half))), -1))]));
    expect(same(an2, mul(2, acos(cos(mul(theta, half)))))).toBe(true);
    // test_issue_16318: a negative scalar part is negated first
    const [ax3, an3] = Quaternion(-1, 1, 1, 1).toAxisAngle();
    expect(strs(ax3)).toEqual(['-sqrt(3)/3', '-sqrt(3)/3', '-sqrt(3)/3']);
    expect(sstr(an3)).toBe('2*pi/3');
  });

  it('rotates points', () => {
    const q = Quaternion(cos(mul(x, half)), 0, 0, sin(mul(x, half)));
    expect(strs(Quaternion.rotatePoint([1, 1, 1], q).map((e) => trigsimp(e)))).toEqual(['sqrt(2)*cos(x + pi/4)', 'sqrt(2)*sin(x + pi/4)', '1']);
    const [axis, angle] = q.toAxisAngle();
    // SymPy's trigsimp of the whole tuple gives (sqrt(2)*cos(x + pi/4), sqrt(2)*sin(x + pi/4), 1); trigsimp of
    // each coordinate, in SymPy as here, leaves the third one as below (it equals 1)
    expect(strs(Quaternion.rotatePoint([1, 1, 1], [axis, angle]).map((e) => trigsimp(e)))).toEqual([
      'sqrt(2)*cos(x + pi/4)',
      'sqrt(2)*sin(x + pi/4)',
      'cos(x/2)**2 + 2*sin(x/2)**4/(1 - cos(x))',
    ]);
    const q1 = Quaternion(1, 2, 3, 4);
    expect(strs(Quaternion.rotatePoint([1, 1, 1], q1))).toEqual(['1/5', '1', '7/5']);
    const [ax1, an1] = q1.toAxisAngle();
    expect(strs(Quaternion.rotatePoint([1, 1, 1], [ax1, an1]))).toEqual(['1/5', '1', '7/5']);
  });

  it('converts to rotation matrices (test_quaternion_conversions)', () => {
    const q1 = Quaternion(1, 2, 3, 4);
    expect(mat(q1.toRotationMatrix())).toBe('Matrix([[-2/3, 2/15, 11/15], [2/3, -1/3, 2/3], [1/3, 14/15, 2/15]])');
    expect(mat(q1.toRotationMatrix([1, 1, 1]))).toBe('Matrix([[-2/3, 2/15, 11/15, 4/5], [2/3, -1/3, 2/3, 0], [1/3, 14/15, 2/15, -2/5], [0, 0, 0, 1]])');
    expect(mat(q1.toRotationMatrix(undefined, { homogeneous: false }))).toBe('Matrix([[-2/3, 2/15, 11/15], [2/3, -1/3, 2/3], [1/3, 14/15, 2/15]])');
    const theta = new Sym('theta', { real: true });
    const q2 = Quaternion(cos(mul(theta, half)), 0, 0, sin(mul(theta, half)));
    const ts = (m: Matrix): string => mat(m.map((e) => trigsimp(e)));
    expect(ts(q2.toRotationMatrix())).toBe('Matrix([[cos(theta), -sin(theta), 0], [sin(theta), cos(theta), 0], [0, 0, 1]])');
    expect(ts(q2.toRotationMatrix([1, 1, 1]))).toBe(
      'Matrix([[cos(theta), -sin(theta), 0, sin(theta) - cos(theta) + 1], [sin(theta), cos(theta), 0, -sin(theta) - cos(theta) + 1], [0, 0, 1, 0], [0, 0, 0, 1]])',
    );
    // test_quaternion_rotation_iss1593
    const q3 = Quaternion(cos(mul(phi, half)), sin(mul(phi, half)), 0, 0);
    expect(ts(q3.toRotationMatrix())).toBe('Matrix([[1, 0, 0], [0, cos(phi), -sin(phi)], [0, sin(phi), cos(phi)]])');
    // test_rotation_matrix_homogeneous
    const q = Quaternion(w, x, y, z);
    const R1 = q.toRotationMatrix(undefined, { homogeneous: true }).mul(pow(q.norm(), 2));
    const R2 = q.toRotationMatrix(undefined, { homogeneous: false }).mul(pow(q.norm(), 2)).map((e) => simplify(e));
    expect(R1.map((e) => expand(e)).equals(R2.map((e) => expand(e)))).toBe(true);
    expect(mat(q.toRotationMatrix(undefined, { homogeneous: false }))).toBe(
      'Matrix([[-2*(y**2 + z**2)/(w**2 + x**2 + y**2 + z**2) + 1, 2*(-w*z + x*y)/(w**2 + x**2 + y**2 + z**2), 2*(w*y + x*z)/(w**2 + x**2 + y**2 + z**2)], [2*(w*z + x*y)/(w**2 + x**2 + y**2 + z**2), -2*(x**2 + z**2)/(w**2 + x**2 + y**2 + z**2) + 1, 2*(-w*x + y*z)/(w**2 + x**2 + y**2 + z**2)], [2*(-w*y + x*z)/(w**2 + x**2 + y**2 + z**2), 2*(w*x + y*z)/(w**2 + x**2 + y**2 + z**2), -2*(x**2 + y**2)/(w**2 + x**2 + y**2 + z**2) + 1]])',
    );
  });

  it('converts from Euler angles', () => {
    expect(sstr(Quaternion.fromEuler([mul(pi, half), 0, 0], 'xyz'))).toBe('sqrt(2)/2 + sqrt(2)/2*i + 0*j + 0*k');
    expect(sstr(Quaternion.fromEuler([0, mul(pi, half), pi], 'zyz'))).toBe('0 + (-sqrt(2)/2)*i + 0*j + sqrt(2)/2*k');
    expect(sstr(Quaternion.fromEuler([0, mul(pi, half), pi], 'ZYZ'))).toBe('0 + sqrt(2)/2*i + 0*j + sqrt(2)/2*k');
    expect(sstr(Quaternion.fromEuler(Matrix.col(0, mul(pi, half), pi), 'ZYZ'))).toBe('0 + sqrt(2)/2*i + 0*j + sqrt(2)/2*k');
    expect(() => Quaternion.fromEuler([0, 0], 'xyz')).toThrow('3 angles must be given.');
    expect(() => Quaternion.fromEuler([0, 0, 0], 'xy')).toThrow('Expected 3 axes, got `xy`.');
    expect(() => Quaternion.fromEuler([0, 0, 0], 'xYz')).toThrow('seq must either be fully uppercase');
    expect(() => Quaternion.fromEuler([0, 0, 0], '123')).toThrow('seq must either be fully uppercase');
    expect(() => Quaternion.fromEuler([0, 0, 0], 'xxz')).toThrow('Consecutive axes must be different');
    expect(() => Quaternion.fromEuler([0, 0, 0], 'xzz')).toThrow('Consecutive axes must be different');
    expect(() => Quaternion.fromEuler([0, 0, 0], 'xaz')).toThrow("Expected axes from `seq` to be from ['x', 'y', 'z'] or ['X', 'Y', 'Z'], got a");
  });

  it('converts to Euler angles', () => {
    expect(strs(Quaternion(a, b, c, d).toEuler('zyz'))).toEqual(['-atan2(-b, c) + atan2(d, a)', '2*atan2(sqrt(b**2 + c**2), sqrt(a**2 + d**2))', 'atan2(-b, c) + atan2(d, a)']);
    const q = Quaternion(w, x, y, z);
    expect(strs(q.toEuler('zxy'))).toEqual([
      '-atan2(y - z, w + x) + atan2(y + z, w - x)',
      '2*atan2(sqrt((w + x)**2 + (y - z)**2), sqrt((w - x)**2 + (y + z)**2)) - pi/2',
      'atan2(y - z, w + x) + atan2(y + z, w - x)',
    ]);
    expect(strs(q.toEuler('XYZ'))).toEqual([
      '-atan2(-x - z, w + y) - atan2(-x + z, w - y)',
      '2*atan2(sqrt((w + y)**2 + (-x - z)**2), sqrt((w - y)**2 + (-x + z)**2)) - pi/2',
      '-atan2(-x - z, w + y) + atan2(-x + z, w - y)',
    ]);
    expect(strs(q.toEuler('ZXZ'))).toEqual(['atan2(y, x) + atan2(z, w)', '2*atan2(sqrt(x**2 + y**2), sqrt(w**2 + z**2))', '-atan2(y, x) + atan2(z, w)']);
    expect(strs(q.toEuler('zyz', { angleAddition: false, avoidSquareRoot: true }))).toEqual([
      'atan2(w*x + y*z, w*y - x*z)',
      'acos((w**2 - x**2 - y**2 + z**2)/(w**2 + x**2 + y**2 + z**2))',
      'atan2(-w*x + y*z, w*y + x*z)',
    ]);
    expect(strs(q.toEuler('zyx', { angleAddition: false, avoidSquareRoot: true }))).toEqual([
      'atan2(-(w - y)*(-x - z) + (w + y)*(-x + z), (w - y)*(w + y) + (-x - z)*(-x + z))',
      'asin((-(w - y)**2 + (w + y)**2 + (-x - z)**2 - (-x + z)**2)/(2*w**2 + 2*x**2 + 2*y**2 + 2*z**2))',
      '-atan2((w - y)*(-x - z) + (w + y)*(-x + z), (w - y)*(w + y) - (-x - z)*(-x + z))',
    ]);
    expect(() => Quaternion(0, 0, 0, 0).toEuler('zyz')).toThrow('Cannot convert a quaternion with norm 0.');
  });

  it('handles the numerical singularities of to_euler', () => {
    const cases: [[Expr, Expr, Expr], string][] = [
      [[mul(pi, half), S.Zero, S.Zero], 'zyz'],
      [[mul(pi, half), S.Zero, S.Zero], 'ZYZ'],
      [[mul(pi, half), pi, S.Zero], 'zyz'],
      [[mul(pi, half), pi, S.Zero], 'ZYZ'],
      [[mul(pi, half), mul(pi, half), S.Zero], 'zyx'],
      [[mul(pi, half), mul(pi, r(-1, 2)), S.Zero], 'zyx'],
      [[mul(pi, half), mul(pi, half), S.Zero], 'ZYX'],
      [[mul(pi, half), mul(pi, r(-1, 2)), S.Zero], 'ZYX'],
    ];
    for (const [angles, seq] of cases) {
      const q = Quaternion.fromEuler(angles, seq) as QuaternionNode;
      expect(strs(q.toEuler(seq))).toEqual(strs(angles));
    }
    // test_to_euler_iss24504
    const q = Quaternion.fromEuler([phi, 0, 0], 'zyz') as QuaternionNode;
    expect(strs(q.toEuler('zyz').map((e) => trigsimp(e, { inverse: true })))).toEqual(['phi', '0', '0']);
  });

  it('round-trips through Euler angles (test_to_euler)', () => {
    const q = Quaternion(w, x, y, z);
    const qn = q.normalize();
    // SymPy checks simplify(from_euler(to_euler(q))) == q.normalize() symbolically; here the
    // symbolic angles are evaluated at a point first, which keeps the test fast
    const at = { w: 0.3, x: -0.7, y: 1.1, z: 0.4 };
    for (const seq of ['zxy', 'zyx', 'zyz', 'zxz', 'ZXY', 'ZYX', 'ZYZ', 'ZXZ']) {
      const angles = q.toEuler(seq).map((e) => evalfNum(e, at));
      const back = Quaternion.fromEuler(angles, seq) as QuaternionNode;
      back.args.forEach((e, i) => expect(Math.abs(e.toNumber() - evalfNum(at3(qn.args, i), at))).toBeLessThan(1e-12));
    }
  });

  it('agrees between the to_euler options (test_to_euler_options)', () => {
    for (const seq of ['xyz', 'zxz', 'YZX', 'XYX']) {
      for (const el of [[1, 0, 0, 0], [0, 1, -1, 1], [1, -1, 0, 1], [-1, 1, 1, 1], [0, 0, 0, 1]] as const) {
        const q = Quaternion(...el);
        const a1 = q.toEuler(seq, { angleAddition: true, avoidSquareRoot: true });
        const a2 = q.toEuler(seq, { angleAddition: false, avoidSquareRoot: false });
        for (let i = 0; i < 3; i++) {
          const e = sub(at3(a1, i), at3(a2, i)).toNumber();
          const wrapped = ((((e + Math.PI) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)) - Math.PI;
          expect(Math.abs(wrapped)).toBeLessThan(1e-7);
        }
      }
    }
  });
});

function div3(e: Expr): Expr {
  return mul(e, r(1, 3));
}

function at3(xs: readonly Expr[], i: number): Expr {
  const v = xs[i];
  if (v === undefined) throw new RangeError('index');
  return v;
}

function evalfNum(e: Expr, values: Record<string, number>): number {
  return e.toNumber(values);
}
