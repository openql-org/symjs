// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/algebras/quaternion.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.algebras.quaternion: the Quaternion expression node
 * a + b*i + c*j + d*k with the Hamilton product, rotations (axis-angle,
 * rotation matrices, Euler angles), exp/log/pow and the geometric
 * predicates.
 *
 * Arithmetic follows SymPy's operators (Quaternion has a higher
 * _op_priority than other expressions): add, mul and pow with a quaternion
 * among the operands give a quaternion. The module registers this with
 * the core when it is loaded.
 */

import { isNegative, isNonZero, isPositive, isReal, isZero as isZeroQ } from '../core/assumptions';
import { callableClass } from '../core/callable';
import { at, cast } from '../core/guard';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Derivative, ExtensionExpr, Integral, Limit, Mul, Pow, Rational, S, Special, UndefFn, impl } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import type { Truth } from '../core/truth';
import { toTruth, truthOr } from '../core/truth';
import { Concrete } from '../core/concrete';
import { acos, asin, cos, im, log, re, sin } from '../functions/elementary/elementary';
import { atan2, sign } from '../functions/special/special';
import { Matrix } from '../matrices/matrix';
import { PREC, precedence } from '../printing/str';
import { trigsimp } from '../simplify/trigsimp';
import { parserHooks } from '../parsing/parser';

/** Options of the Quaternion constructor (SymPy real_field and norm). */
export interface QuaternionOptions {
  /** The coefficients are real (default true): a complex scalar added or multiplied is split into a + b*i. */
  realField?: boolean;
  /** A pre-defined norm, returned by norm() instead of computing it. */
  norm?: ExprLike;
}

/** Options of Quaternion.toEuler (SymPy angle_addition and avoid_square_root). */
export interface ToEulerOptions {
  /** First and third angles as a sum and difference of two atan2 (default true). */
  angleAddition?: boolean;
  /** The second angle from acos/asin instead of atan2 of square roots (default false). */
  avoidSquareRoot?: boolean;
}

/** Options of Quaternion.toRotationMatrix (SymPy homogeneous). */
export interface ToRotationMatrixOptions {
  /** The homogeneous form of the diagonal (default true). */
  homogeneous?: boolean;
}

type Vector3 = readonly [ExprLike, ExprLike, ExprLike];

/** SymPy is_zero as far as the assumptions decide it, and numerically for a nonzero constant (sqrt(-7 + 24*I)). */
function zeroTruth(e: Expr): boolean | undefined {
  const z = isZeroQ(e);
  if (z !== undefined) return z;
  if (isNonZero(e) === true) return false;
  if (freeSymbols(e).size === 0 && !hasSpecial(e)) {
    try {
      const v = e.toComplex();
      if (Math.hypot(v.re, v.im) > 1e-12) return false;
    } catch {
      // not numerically evaluable
    }
  }
  return undefined;
}

const hasSpecial = (e: Expr): boolean => e instanceof Special || e.args.some(hasSpecial);

/** SymPy is_number: no free symbols and no undefined functions. */
const isNumberExpr = (e: Expr): boolean => freeSymbols(e).size === 0 && !hasUndef(e);
const hasUndef = (e: Expr): boolean => e instanceof UndefFn || e.args.some(hasUndef);

/**
 * SymPy is_complex as far as it decides the arithmetic: a finite value
 * whose symbols are real. A value that may be non-complex (an unknown
 * symbol) is added or multiplied as a whole.
 */
function isComplexValue(e: Expr): boolean {
  if (!e.isCommutative || hasSpecial(e) || hasUndef(e)) return false;
  for (const s of freeSymbols(e)) if (isReal(s) !== true) return false;
  return true;
}

/** SymPy _check_norm: a given numeric norm must be positive and agree with numeric elements. */
function checkNorm(elements: readonly Expr[], norm: Expr | undefined): void {
  if (norm === undefined || !isNumberExpr(norm)) return;
  if (isPositive(norm) === false || zeroTruth(norm) === true) throw new RangeError('Input norm must be positive.');
  const numerical = elements.every((i) => isNumberExpr(i) && isReal(i) === true);
  if (numerical && zeroTruth(add(pow(norm, 2), mul(-1, add(...elements.map((i) => pow(i, 2)))))) === false) {
    throw new RangeError('Incompatible value for norm.');
  }
}

/** SymPy _is_extrinsic: validates seq, true for lowercase (extrinsic) and false for uppercase (intrinsic). */
function isExtrinsic(seq: string): boolean {
  if (seq.length !== 3) throw new RangeError(`Expected 3 axes, got \`${seq}\`.`);
  const cased = seq.toUpperCase() !== seq.toLowerCase();
  const intrinsic = cased && seq === seq.toUpperCase();
  const extrinsic = cased && seq === seq.toLowerCase();
  if (!(intrinsic || extrinsic)) {
    throw new RangeError('seq must either be fully uppercase (for extrinsic rotations), or fully lowercase, for intrinsic rotations).');
  }
  const [i, j, k] = seq.toLowerCase();
  if (i === j || j === k) throw new RangeError('Consecutive axes must be different');
  const bad = [...new Set(seq.split(''))].filter((ch) => !'xyzXYZ'.includes(ch));
  if (bad.length) throw new RangeError(`Expected axes from \`seq\` to be from ['x', 'y', 'z'] or ['X', 'Y', 'Z'], got ${bad.join('')}`);
  return extrinsic;
}

/** SymPy LaTeX precedence_traditional of a coefficient: products bind like Mul whatever their sign. */
function latexPrecedence(e: Expr): number {
  if (e instanceof Mul || e instanceof Integral || e instanceof Derivative || e instanceof Limit || e instanceof Concrete) return PREC.MUL;
  return precedence(e);
}

/**
 * SymPy Quaternion: a + b*i + c*j + d*k as an expression node with the four
 * coefficients as arguments. The pre-defined norm and the real_field flag
 * are attributes, not arguments (as in SymPy, equality ignores them).
 */
export class QuaternionNode extends ExtensionExpr {
  #realField: boolean;
  #norm: Expr | undefined;

  constructor(a: ExprLike = 0, b: ExprLike = 0, c: ExprLike = 0, d: ExprLike = 0, opts: QuaternionOptions = {}) {
    const args = [a, b, c, d].map(sympify);
    if (args.some((i) => !i.isCommutative)) throw new RangeError('arguments have to be commutative');
    super('Quaternion', args);
    this.#realField = opts.realField ?? true;
    this.#norm = undefined;
    this.setNorm(opts.norm);
  }

  /**
   * Set the pre-defined norm (SymPy set_norm); undefined removes it. Like
   * SymPy, this changes the quaternion in place.
   */
  setNorm(norm: ExprLike | undefined): void {
    const n = norm === undefined ? undefined : sympify(norm);
    checkNorm(this.args, n);
    this.#norm = n;
  }

  get a(): Expr {
    return at(this.args, 0);
  }
  get b(): Expr {
    return at(this.args, 1);
  }
  get c(): Expr {
    return at(this.args, 2);
  }
  get d(): Expr {
    return at(this.args, 3);
  }
  /** The coefficients are real (SymPy real_field). */
  get realField(): boolean {
    return this.#realField;
  }

  override withArgs(args: readonly Expr[]): Expr {
    // SymPy func(*args): a new quaternion over the real field, without the pre-defined norm
    return fromArgs(args);
  }
  protected override computeCommutative(): boolean {
    return false;
  }

  /** SymPy product_matrix_left: the 4x4 matrix of q*p acting on the column of p. */
  get productMatrixLeft(): Matrix {
    const { a, b, c, d } = this;
    const n = (x: Expr): Expr => mul(-1, x);
    return Matrix.of([
      [a, n(b), n(c), n(d)],
      [b, a, n(d), c],
      [c, d, a, n(b)],
      [d, n(c), b, a],
    ]);
  }
  /** SymPy product_matrix_right: the 4x4 matrix of p*q acting on the column of p. */
  get productMatrixRight(): Matrix {
    const { a, b, c, d } = this;
    const n = (x: Expr): Expr => mul(-1, x);
    return Matrix.of([
      [a, n(b), n(c), n(d)],
      [b, a, d, n(c)],
      [c, n(d), a, b],
      [d, c, n(b), a],
    ]);
  }
  /** The coefficients as a column (SymPy to_Matrix); only b, c, d with vectorOnly. */
  toMatrix(vectorOnly = false): Matrix {
    return Matrix.col(...(vectorOnly ? this.args.slice(1) : this.args));
  }
  /** A quaternion from 4 elements, or 3 with a zero real part (SymPy from_Matrix). */
  static fromMatrix(elements: Matrix | readonly ExprLike[]): QuaternionNode {
    const es: readonly ExprLike[] = elements instanceof Matrix ? elements.data : elements;
    if (es.length !== 3 && es.length !== 4) throw new RangeError(`Input elements must have length 3 or 4, got ${es.length} elements`);
    return fromArgs((es.length === 3 ? [0, ...es] : es).map(sympify));
  }

  /** The rotation quaternion of the Euler angles in the sequence seq (SymPy from_euler). */
  static fromEuler(angles: Matrix | readonly ExprLike[], seq: string): Expr {
    const as: readonly ExprLike[] = angles instanceof Matrix ? angles.data : angles;
    if (as.length !== 3) throw new RangeError('3 angles must be given.');
    const extrinsic = isExtrinsic(seq);
    const axes = seq.toLowerCase().split('');
    const basis = (n: number): Vector3 => {
      const ax = at(axes, n);
      return [ax === 'x' ? 1 : 0, ax === 'y' ? 1 : 0, ax === 'z' ? 1 : 0];
    };
    const qi = QuaternionNode.fromAxisAngle(basis(0), at(as, 0));
    const qj = QuaternionNode.fromAxisAngle(basis(1), at(as, 1));
    const qk = QuaternionNode.fromAxisAngle(basis(2), at(as, 2));
    return trigsimp(extrinsic ? mul(qk, qj, qi) : mul(qi, qj, qk));
  }

  /**
   * The Euler angles of the same rotation in the sequence seq (SymPy
   * to_euler, after doi:10.1371/journal.pone.0276302). In gimbal lock the
   * third angle is zero.
   */
  toEuler(seq: string, opts: ToEulerOptions = {}): [Expr, Expr, Expr] {
    const angleAddition = opts.angleAddition ?? true;
    const avoidSquareRoot = opts.avoidSquareRoot ?? false;
    if (this.isZeroQuaternion() === true) throw new RangeError('Cannot convert a quaternion with norm 0.');
    const angles: Expr[] = [S.Zero, S.Zero, S.Zero];
    const extrinsic = isExtrinsic(seq);
    const lower = seq.toLowerCase();
    let i = 'xyz'.indexOf(lower.charAt(0)) + 1;
    const j = 'xyz'.indexOf(lower.charAt(1)) + 1;
    let k = 'xyz'.indexOf(lower.charAt(2)) + 1;
    if (!extrinsic) [i, k] = [k, i];
    const symmetric = i === k;
    if (symmetric) k = 6 - i - j;
    // parity of the permutation
    const sgn = ((i - j) * (j - k) * (k - i)) / 2;
    const elements = this.args;
    let a = this.a;
    let b = at(elements, i);
    let c = at(elements, j);
    let d = mul(at(elements, k), sgn);
    if (!symmetric) [a, b, c, d] = [add(a, mul(-1, c)), add(b, d), add(c, a), add(d, mul(-1, b))];
    const sq = (x: Expr): Expr => mul(x, x);
    if (avoidSquareRoot) {
      if (symmetric) {
        const n2 = pow(this.norm(), 2);
        angles[1] = acos(mul(add(sq(a), sq(b), mul(-1, sq(c)), mul(-1, sq(d))), pow(n2, -1)));
      } else {
        const n2 = mul(2, pow(this.norm(), 2));
        angles[1] = asin(mul(add(sq(c), sq(d), mul(-1, sq(a)), mul(-1, sq(b))), pow(n2, -1)));
      }
    } else {
      angles[1] = mul(2, atan2(sqrt(add(sq(c), sq(d))), sqrt(add(sq(a), sq(b)))));
      if (!symmetric) angles[1] = add(at(angles, 1), mul(-1, S.Pi, S.Half));
    }
    // singularities in numerical cases
    let kase = 0;
    if (zeroTruth(c) === true && zeroTruth(d) === true) kase = 1;
    if (zeroTruth(a) === true && zeroTruth(b) === true) kase = 2;
    if (kase === 0) {
      if (angleAddition) {
        angles[0] = add(atan2(b, a), atan2(d, c));
        angles[2] = add(atan2(b, a), mul(-1, atan2(d, c)));
      } else {
        angles[0] = atan2(add(mul(b, c), mul(a, d)), add(mul(a, c), mul(-1, b, d)));
        angles[2] = atan2(add(mul(b, c), mul(-1, a, d)), add(mul(a, c), mul(b, d)));
      }
    } else {
      // a degenerate case
      angles[extrinsic ? 0 : 2] = S.Zero;
      const idx = extrinsic ? 2 : 0;
      angles[idx] = kase === 1 ? mul(2, atan2(b, a)) : mul(2, atan2(d, c), extrinsic ? -1 : 1);
    }
    // Tait-Bryan angles
    if (!symmetric) angles[0] = mul(at(angles, 0), sgn);
    const [x, y, z] = [at(angles, 0), at(angles, 1), at(angles, 2)];
    return extrinsic ? [z, y, x] : [x, y, z];
  }

  /** The rotation quaternion of an axis and an angle (SymPy from_axis_angle); normalized by construction. */
  static fromAxisAngle(vector: Vector3, angle: ExprLike): QuaternionNode {
    const v = [sympify(vector[0]), sympify(vector[1]), sympify(vector[2])];
    const norm = sqrt(add(...v.map((t) => pow(t, 2))));
    const half = mul(sympify(angle), S.Half);
    const s = sin(half);
    return fromArgs([cos(half), ...v.map((t) => mul(t, pow(norm, -1), s))]);
  }

  /**
   * The quaternion of a rotation matrix (SymPy from_rotation_matrix); it is
   * normalized when the matrix is special orthogonal.
   */
  static fromRotationMatrix(M: Matrix): QuaternionNode {
    const absQ = pow(M.det(), Rational.of(1n, 3n));
    const m = (r: number, c: number): Expr => M.get(r, c);
    const part = (s1: number, s2: number, s3: number): Expr =>
      mul(sqrt(add(absQ, mul(s1, m(0, 0)), mul(s2, m(1, 1)), mul(s3, m(2, 2)))), S.Half);
    const a = part(1, 1, 1);
    const b = mul(part(1, -1, -1), sign(add(m(2, 1), mul(-1, m(1, 2)))));
    const c = mul(part(-1, 1, -1), sign(add(m(0, 2), mul(-1, m(2, 0)))));
    const d = mul(part(-1, -1, 1), sign(add(m(1, 0), mul(-1, m(0, 1)))));
    return new QuaternionNode(a, b, c, d);
  }

  // ---- arithmetic (SymPy __add__, __mul__, __pow__, ...) --------------------

  /** Negation (SymPy __neg__). */
  override neg(): QuaternionNode {
    return new QuaternionNode(mul(-1, this.a), mul(-1, this.b), mul(-1, this.c), mul(-1, this.d));
  }

  /**
   * The Hamilton product of q1 and q2 when either is a quaternion, else
   * q1*q2 (SymPy Quaternion._generic_mul).
   *
   * @internal
   */
  static genericMul(q1In: ExprLike, q2In: ExprLike): Expr {
    const q1 = sympify(q1In);
    const q2 = sympify(q2In);
    if (q1 instanceof QuaternionNode) return qmul(q1, q2);
    if (q2 instanceof QuaternionNode) return scalarTimes(q2, q1, true);
    return mul(q1, q2);
  }

  /** The Hamilton product (the norm is pre-defined when either factor has one). */
  static hamilton(q1: QuaternionNode, q2: QuaternionNode): QuaternionNode {
    const norm = q1.#norm === undefined && q2.#norm === undefined ? undefined : mul(q1.norm(), q2.norm());
    const [a1, b1, c1, d1] = [q1.a, q1.b, q1.c, q1.d];
    const [a2, b2, c2, d2] = [q2.a, q2.b, q2.c, q2.d];
    return new QuaternionNode(
      add(mul(-1, b1, b2), mul(-1, c1, c2), mul(-1, d1, d2), mul(a1, a2)),
      add(mul(b1, a2), mul(c1, d2), mul(-1, d1, c2), mul(a1, b2)),
      add(mul(-1, b1, d2), mul(c1, a2), mul(d1, b2), mul(a1, c2)),
      add(mul(b1, c2), mul(-1, c1, b2), mul(d1, a2), mul(a1, d2)),
      { norm },
    );
  }

  /** The sum with a quaternion or a scalar (SymPy add); a complex scalar adds to a and b when realField. */
  addQuaternion(other: ExprLike): QuaternionNode {
    const q2 = sympify(other);
    if (!(q2 instanceof QuaternionNode)) {
      if (this.realField && isComplexValue(q2)) return new QuaternionNode(add(re(q2), this.a), add(im(q2), this.b), this.c, this.d);
      if (q2.isCommutative) return new QuaternionNode(add(this.a, q2), this.b, this.c, this.d);
      throw new RangeError('Only commutative expressions can be added with a Quaternion.');
    }
    return new QuaternionNode(add(this.a, q2.a), add(this.b, q2.b), add(this.c, q2.c), add(this.d, q2.d));
  }

  /** The p-th power for an integer p, the inverse power for p < 0 (SymPy pow). */
  override pow(pIn: ExprLike): QuaternionNode {
    const p0 = sympify(pIn);
    if (!(p0 instanceof Rational && p0.isInteger)) throw new TypeError(`unsupported operand type for Quaternion power: ${p0.toString()}`);
    let q: QuaternionNode = this;
    let p = p0.p;
    if (p < 0n) {
      q = q.inverse();
      p = -p;
    }
    if (p === 1n) return q;
    let res = new QuaternionNode(1, 0, 0, 0);
    while (p > 0n) {
      if (p & 1n) res = qmul(res, q);
      q = qmul(q, q);
      p >>= 1n;
    }
    return res;
  }

  /** The conjugate a - b*i - c*j - d*k, keeping a pre-defined norm (SymPy _eval_conjugate; real_field is not kept). */
  override conjugateSelf(): QuaternionNode {
    return new QuaternionNode(this.a, mul(-1, this.b), mul(-1, this.c), mul(-1, this.d), { norm: this.#norm });
  }

  /** The norm sqrt(a**2 + b**2 + c**2 + d**2), or the pre-defined one (SymPy norm). */
  norm(): Expr {
    if (this.#norm !== undefined) return this.#norm;
    // trigsimp simplifies the sin(x)**2 + cos(x)**2 that from_axis_angle gives
    return sqrt(trigsimp(add(...this.args.map((x) => pow(x, 2)))));
  }
  /** q / |q| (SymPy normalize). */
  normalize(): QuaternionNode {
    return qmul(this, pow(this.norm(), -1));
  }
  /** conjugate(q) / |q|**2 (SymPy inverse). */
  inverse(): QuaternionNode {
    const n = this.norm();
    if (zeroTruth(n) === true) throw new RangeError('Cannot compute inverse for a quaternion with zero norm');
    return qmul(this.conjugateSelf(), pow(n, -2));
  }

  /** e**q = e**a*(cos|v| + v/|v|*sin|v|) (SymPy exp). */
  exp(): QuaternionNode {
    const { a, b, c, d } = this;
    const vn = sqrt(add(pow(b, 2), pow(c, 2), pow(d, 2)));
    const ea = exp(a);
    const f = (x: Expr): Expr => mul(ea, sin(vn), x, pow(vn, -1));
    return new QuaternionNode(mul(ea, cos(vn)), f(b), f(c), f(d));
  }
  /** log q = log|q| + v/|v|*acos(a/|q|) (SymPy log). */
  log(): QuaternionNode {
    const { a, b, c, d } = this;
    const vn = sqrt(add(pow(b, 2), pow(c, 2), pow(d, 2)));
    const qn = this.norm();
    const t = acos(mul(a, pow(qn, -1)));
    const f = (x: Expr): Expr => mul(x, t, pow(vn, -1));
    return new QuaternionNode(log(qn), f(b), f(c), f(d));
  }
  /** The p-th power in the cos-sin form |q|**p*(cos(p*t) + u*sin(p*t)) (SymPy pow_cos_sin). */
  powCosSin(p: ExprLike): QuaternionNode {
    const [v, angle] = this.toAxisAngle();
    const q2 = QuaternionNode.fromAxisAngle(v, mul(p, angle));
    return qmul(q2, pow(this.norm(), p));
  }

  /** SymPy _eval_subs: the coefficients and the pre-defined norm substituted (real_field is not kept). */
  override subsSelf(_old: Expr, _nw: Expr, subs: (e: Expr) => Expr): QuaternionNode {
    const norm = this.#norm === undefined ? undefined : subs(this.#norm);
    return fromArgs(this.args.map(subs), { norm });
  }
  /** SymPy simplify: each coefficient simplified (simplify maps over the arguments of the node). */
  override simplifySelf(simplify: (e: Expr) => Expr): QuaternionNode {
    return fromArgs(this.args.map(simplify));
  }
  /** The derivative of each coefficient (SymPy Quaternion.diff). */
  override diff(x: Expr, n = 1): QuaternionNode {
    return fromArgs(this.args.map((e) => impl.diff(e, x, n)));
  }
  override diffSelf(x: Expr, dd: (e: Expr, x: Expr) => Expr): Expr {
    return fromArgs(this.args.map((e) => dd(e, x)));
  }
  /** The integral of each coefficient, between the limits when given (SymPy Quaternion.integrate). */
  override integrate(x: Sym, limits?: [ExprLike, ExprLike]): QuaternionNode {
    return fromArgs(this.args.map((e) => impl.integrate(e, x, limits)));
  }
  override integrateSelf(_x: Sym, _limits: readonly [Expr, Expr] | undefined, integrate: (e: Expr) => Expr): Expr {
    return fromArgs(this.args.map(integrate));
  }

  /**
   * The point pin rotated by r, a quaternion (normalized first) or an
   * [axis, angle] pair (SymPy rotate_point).
   */
  static rotatePoint(pin: Vector3, r: QuaternionNode | readonly [Vector3, ExprLike]): [Expr, Expr, Expr] {
    const q = r instanceof QuaternionNode ? r.normalize() : QuaternionNode.fromAxisAngle(r[0], r[1]);
    const pout = qmul(qmul(q, new QuaternionNode(0, pin[0], pin[1], pin[2])), q.conjugateSelf());
    return [pout.b, pout.c, pout.d];
  }

  /** The axis and angle of the rotation (SymPy to_axis_angle). */
  toAxisAngle(): [[Expr, Expr, Expr], Expr] {
    let q: QuaternionNode = this;
    if (isNegative(q.a) === true) q = qmul(q, -1);
    q = q.normalize();
    const angle = trigsimp(mul(2, acos(q.a)));
    // the quaternion is normalized, so q.a is at most 1
    const s = sqrt(add(1, mul(-1, q.a, q.a)));
    const f = (x: Expr): Expr => trigsimp(mul(x, pow(s, -1)));
    return [[f(q.b), f(q.c), f(q.d)], angle];
  }

  /**
   * The rotation matrix of the quaternion about the origin, or the 4x4
   * transformation about the point v (SymPy to_rotation_matrix).
   */
  toRotationMatrix(v?: Vector3, opts: ToRotationMatrixOptions = {}): Matrix {
    const homogeneous = opts.homogeneous ?? true;
    const { a, b, c, d } = this;
    const s = pow(this.norm(), -2);
    const sq = (x: Expr): Expr => pow(x, 2);
    const neg = (x: Expr): Expr => mul(-1, x);
    let m00: Expr;
    let m11: Expr;
    let m22: Expr;
    if (homogeneous) {
      m00 = mul(s, add(sq(a), sq(b), neg(sq(c)), neg(sq(d))));
      m11 = mul(s, add(sq(a), neg(sq(b)), sq(c), neg(sq(d))));
      m22 = mul(s, add(sq(a), neg(sq(b)), neg(sq(c)), sq(d)));
    } else {
      m00 = add(1, mul(-2, s, add(sq(c), sq(d))));
      m11 = add(1, mul(-2, s, add(sq(b), sq(d))));
      m22 = add(1, mul(-2, s, add(sq(b), sq(c))));
    }
    const m01 = mul(2, s, add(mul(b, c), neg(mul(d, a))));
    const m02 = mul(2, s, add(mul(b, d), mul(c, a)));
    const m10 = mul(2, s, add(mul(b, c), mul(d, a)));
    const m12 = mul(2, s, add(mul(c, d), neg(mul(b, a))));
    const m20 = mul(2, s, add(mul(b, d), neg(mul(c, a))));
    const m21 = mul(2, s, add(mul(c, d), mul(b, a)));
    if (v === undefined) return Matrix.of([[m00, m01, m02], [m10, m11, m12], [m20, m21, m22]]);
    const [x, y, z] = [sympify(v[0]), sympify(v[1]), sympify(v[2])];
    const m03 = add(x, neg(mul(x, m00)), neg(mul(y, m01)), neg(mul(z, m02)));
    const m13 = add(y, neg(mul(x, m10)), neg(mul(y, m11)), neg(mul(z, m12)));
    const m23 = add(z, neg(mul(x, m20)), neg(mul(y, m21)), neg(mul(z, m22)));
    return Matrix.of([[m00, m01, m02, m03], [m10, m11, m12, m13], [m20, m21, m22, m23], [0, 0, 0, 1]]);
  }

  /** The scalar part a (SymPy scalar_part). */
  scalarPart(): Expr {
    return this.a;
  }
  /** The vector part 0 + b*i + c*j + d*k (SymPy vector_part). */
  vectorPart(): QuaternionNode {
    return new QuaternionNode(0, this.b, this.c, this.d);
  }
  /** The versor of the vector part, an imaginary unit (SymPy axis). */
  axis(): QuaternionNode {
    const ax = this.vectorPart().normalize();
    return new QuaternionNode(0, ax.b, ax.c, ax.d);
  }
  /** The scalar part is zero (SymPy is_pure). */
  isPure(): Truth {
    return toTruth(zeroTruth(this.a));
  }
  /** The norm is zero (SymPy is_zero_quaternion). */
  isZeroQuaternion(): Truth {
    return toTruth(zeroTruth(this.norm()));
  }
  /** The angle 2*atan2(|v|, a) measured in the real-axis plane (SymPy angle). */
  angle(): Expr {
    return mul(2, atan2(this.vectorPart().norm(), this.scalarPart()));
  }
  /** The rotation arcs of the two quaternions lie in the same plane: their axes are parallel (SymPy arc_coplanar). */
  arcCoplanar(other: QuaternionNode): Truth {
    if (this.isZeroQuaternion() === true || other.isZeroQuaternion() === true) throw new RangeError('Neither of the given quaternions can be 0');
    const a1 = this.axis();
    const a2 = other.axis();
    return truthOr(a1.addQuaternion(a2.neg()).isZeroQuaternion(), a1.addQuaternion(a2).isZeroQuaternion());
  }
  /** The three pure quaternions, seen as 3D vectors, are coplanar (SymPy vector_coplanar). */
  static vectorCoplanar(q1: QuaternionNode, q2: QuaternionNode, q3: QuaternionNode): Truth {
    if ([q1, q2, q3].some((q) => q.isPure() === false)) throw new RangeError('The given quaternions must be pure');
    const M = Matrix.of([q1, q2, q3].map((q) => [q.b, q.c, q.d]));
    return toTruth(zeroTruth(M.det()));
  }
  /** The two pure quaternions, seen as 3D vectors, are parallel: their product commutes (SymPy parallel). */
  parallel(other: QuaternionNode): Truth {
    if (this.isPure() === false || other.isPure() === false) throw new RangeError('The provided quaternions must be pure');
    return qmul(this, other).addQuaternion(qmul(other, this).neg()).isZeroQuaternion();
  }
  /** The two pure quaternions, seen as 3D vectors, are orthogonal: their product anticommutes (SymPy orthogonal). */
  orthogonal(other: QuaternionNode): Truth {
    if (this.isPure() === false || other.isPure() === false) throw new RangeError('The given quaternions must be pure');
    return qmul(this, other).addQuaternion(qmul(other, this)).isZeroQuaternion();
  }
  /** The norm times the axis (SymPy index_vector). */
  indexVector(): QuaternionNode {
    return qmul(this.axis(), this.norm());
  }
  /** The natural logarithm of the norm (SymPy mensor). */
  mensor(): Expr {
    return log(this.norm());
  }

  // ---- printing ------------------------------------------------------------

  /** SymPy StrPrinter._print_Quaternion: a + b*i + c*j + d*k, a coefficient binding weaker than Mul parenthesized. */
  override printStr(print: (e: Expr) => string): string {
    const s = this.args.map((e) => (precedence(e) < PREC.MUL ? `(${print(e)})` : print(e)));
    return [at(s, 0), ...s.slice(1).map((x, i) => `${x}*${at('ijk', i)}`)].join(' + ');
  }
  /** SymPy LatexPrinter._print_Quaternion. */
  override printLatex(print: (e: Expr) => string): string {
    const s = this.args.map((e) => (latexPrecedence(e) < PREC.MUL ? `\\left(${print(e)}\\right)` : print(e)));
    return [at(s, 0), ...s.slice(1).map((x, i) => `${x} ${at('ijk', i)}`)].join(' + ');
  }
}

/** A quaternion from its four coefficients. */
function fromArgs(args: readonly Expr[], opts: QuaternionOptions = {}): QuaternionNode {
  return new QuaternionNode(at(args, 0), at(args, 1), at(args, 2), at(args, 3), opts);
}

/** q*o for a quaternion or a scalar o. */
function qmul(q: QuaternionNode, o: ExprLike): QuaternionNode {
  const s = sympify(o);
  return s instanceof QuaternionNode ? QuaternionNode.hamilton(q, s) : scalarTimes(q, s, false);
}

/** s*q (left) or q*s for a scalar s (the scalar branches of SymPy _generic_mul). */
function scalarTimes(q: QuaternionNode, s: Expr, left: boolean): QuaternionNode {
  if (q.realField && isComplexValue(s)) {
    const sq = new QuaternionNode(re(s), im(s), 0, 0);
    return left ? QuaternionNode.hamilton(sq, q) : QuaternionNode.hamilton(q, sq);
  }
  if (s.isCommutative) return fromArgs(q.args.map((x) => mul(s, x)));
  throw new RangeError('Only commutative expressions can be multiplied with a Quaternion.');
}

/**
 * SymPy Expr.__rsub__ for a - q with a scalar a: the unevaluated sum Add(a, -q)
 * (the terms of a, without a zero; just -q when a is 0).
 */
function rsub(a: Expr, q: QuaternionNode): Expr {
  const terms = [...(a instanceof Add ? a.args : isZeroQ(a) === true ? [] : [a]), q.neg()];
  return terms.length === 1 ? at(terms, 0) : new Add(terms);
}

// SymPy _op_priority: add, sub, mul and pow with a quaternion operand use the quaternion's operators
impl.arithmetic = (op, args) => {
  if (!args.some((x) => x instanceof QuaternionNode)) return undefined;
  switch (op) {
    case 'add':
      return args.reduce((acc, x) => (acc instanceof QuaternionNode ? acc.addQuaternion(x) : x instanceof QuaternionNode ? x.addQuaternion(acc) : add(acc, x)));
    case 'sub': {
      // SymPy q - b is q.add(b*-1); a - q for a scalar a is Expr.__rsub__
      const [a, b] = [at(args, 0), at(args, 1)];
      return a instanceof QuaternionNode ? a.addQuaternion(mul(b, -1)) : rsub(a, cast(b, QuaternionNode));
    }
    case 'mul':
      return args.reduce((acc, x) => QuaternionNode.genericMul(acc, x));
    case 'pow': {
      const [b, e] = [at(args, 0), at(args, 1)];
      // SymPy b**q for a scalar b: Expr.__rpow__ leaves Pow(b, q) unevaluated
      return b instanceof QuaternionNode ? b.pow(e) : new Pow(b, e);
    }
  }
};

/**
 * SymPy Quaternion(a, b, c, d, real_field=True, norm=None), callable and
 * usable with instanceof.
 */
export const Quaternion = /* @__PURE__ */ callableClass(
  QuaternionNode,
  (a: ExprLike = 0, b: ExprLike = 0, c: ExprLike = 0, d: ExprLike = 0, opts: QuaternionOptions = {}): QuaternionNode => new QuaternionNode(a, b, c, d, opts),
);
export type Quaternion = QuaternionNode;

/** SymPy sympify('Quaternion(a, b, c, d, real_field, norm)'): positional arguments, real_field by truth value. */
function parseQuaternion(args: readonly Expr[]): QuaternionNode {
  if (args.length > 6) throw new TypeError(`Quaternion.__new__() takes from 1 to 7 positional arguments but ${args.length + 1} were given`);
  const [a, b, c, d] = [0, 1, 2, 3].map((i) => args[i] ?? S.Zero);
  const rf = args[4];
  return new QuaternionNode(a, b, c, d, { realField: rf === undefined || isZeroQ(rf) !== true, norm: args[5] });
}
parserHooks.constructors.set('Quaternion', parseQuaternion);
