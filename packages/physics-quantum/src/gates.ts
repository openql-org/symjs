// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Symbolic quantum gates and states.
 *
 * Basis ordering follows q5m.js: for n qubits the basis state is
 * |q_{n-1} ... q_1 q_0⟩, i.e. qubit 0 is the least significant bit and the
 * rightmost factor of a Kronecker product.
 */

// extend modules depend on the public API of the base module only
import type { Expr, ExprLike } from '@symjs/symjs';
import { Matrix, Rational, S, add, cos, exp, expandMul as expand, mul, neg, sin, sqrt } from '@symjs/symjs';

const half = (t: ExprLike) => mul(S.Half, t);
const iExp = (t: ExprLike) => exp(mul(S.I, t));
const ISQ2 = () => mul(S.Half, sqrt(2)); // 1/sqrt(2)

// ---- single-qubit gates ------------------------------------------------------

export const I2 = (): Matrix => Matrix.eye(2);
export const X = (): Matrix => Matrix.of([[0, 1], [1, 0]]);
export const Y = (): Matrix => Matrix.of([[0, neg(S.I)], [S.I, 0]]);
export const Z = (): Matrix => Matrix.of([[1, 0], [0, -1]]);
export const H = (): Matrix => Matrix.of([[1, 1], [1, -1]]).scale(ISQ2());
export const S_ = (): Matrix => Matrix.diag(1, S.I);
export const Sdg = (): Matrix => Matrix.diag(1, neg(S.I));
export const T = (): Matrix => Matrix.diag(1, iExp(mul(Rational.of(1, 4), S.Pi)));
export const Tdg = (): Matrix => Matrix.diag(1, iExp(mul(Rational.of(-1, 4), S.Pi)));
/** sqrt(X) */
export const SX = (): Matrix =>
  Matrix.of([
    [add(1, S.I), add(1, neg(S.I))],
    [add(1, neg(S.I)), add(1, S.I)],
  ]).scale(S.Half);

/** Rx(θ) = exp(-iθX/2) */
export const Rx = (theta: ExprLike): Matrix => {
  const c = cos(half(theta));
  const s = mul(neg(S.I), sin(half(theta)));
  return Matrix.of([[c, s], [s, c]]);
};
/** Ry(θ) = exp(-iθY/2) */
export const Ry = (theta: ExprLike): Matrix => {
  const c = cos(half(theta));
  const s = sin(half(theta));
  return Matrix.of([[c, neg(s)], [s, c]]);
};
/** Rz(θ) = exp(-iθZ/2) */
export const Rz = (theta: ExprLike): Matrix => Matrix.diag(iExp(neg(half(theta))), iExp(half(theta)));
/** Phase gate P(λ) = diag(1, e^{iλ}) */
export const P = (lambda: ExprLike): Matrix => Matrix.diag(1, iExp(lambda));
/** General single-qubit gate U(θ, φ, λ) (OpenQASM 3 convention). */
export const U = (theta: ExprLike, phi: ExprLike, lambda: ExprLike): Matrix => {
  const c = cos(half(theta));
  const s = sin(half(theta));
  return Matrix.of([
    [c, mul(-1, iExp(lambda), s)],
    [mul(iExp(phi), s), mul(iExp(add(phi, lambda)), c)],
  ]);
};

// ---- multi-qubit gates ---------------------------------------------------------

/**
 * Controlled-U on n = 1 + log2(dim U) qubits where the control is the most
 * significant qubit (block-diagonal form diag(I, U)).
 */
export function controlled(u: Matrix, numControls = 1): Matrix {
  let m = u;
  for (let k = 0; k < numControls; k++) {
    const d = m.rows;
    m = Matrix.fromFunction(2 * d, 2 * d, (i, j) => {
      if (i < d && j < d) return i === j ? 1 : 0;
      if (i >= d && j >= d) return m.get(i - d, j - d);
      return 0;
    });
  }
  return m;
}

/** CNOT with control = qubit 1 (MSB), target = qubit 0. */
export const CX = (): Matrix => controlled(X());
export const CNOT = CX;
export const CZ = (): Matrix => controlled(Z());
export const SWAP = (): Matrix =>
  Matrix.of([
    [1, 0, 0, 0],
    [0, 0, 1, 0],
    [0, 1, 0, 0],
    [0, 0, 0, 1],
  ]);
export const CCX = (): Matrix => controlled(X(), 2);

/**
 * Embed a single-qubit gate acting on `target` into an n-qubit operator.
 * Uses the |q_{n-1} ... q_0⟩ ordering (qubit 0 = rightmost Kronecker factor).
 */
export function onQubit(gate: Matrix, target: number, n: number): Matrix {
  if (gate.rows !== 2 || gate.cols !== 2) throw new RangeError('onQubit: gate must be 2x2');
  if (target < 0 || target >= n) throw new RangeError('onQubit: target out of range');
  const factors: Matrix[] = [];
  for (let q = n - 1; q >= 0; q--) factors.push(q === target ? gate : Matrix.eye(2));
  return Matrix.kron(...factors);
}

/**
 * Build the n-qubit operator of a gate acting on arbitrary qubits by permuting
 * basis states. `qubits[k]` is the qubit acted on by the k-th (from LSB) qubit
 * of `gate`'s own basis. E.g. onQubits(CX(), [target, control], n).
 */
export function onQubits(gate: Matrix, qubits: readonly number[], n: number): Matrix {
  const k = qubits.length;
  if (gate.rows !== 1 << k || gate.cols !== 1 << k) throw new RangeError('onQubits: gate dimension mismatch');
  if (new Set(qubits).size !== k || qubits.some((q) => q < 0 || q >= n)) throw new RangeError('onQubits: invalid qubits');
  const dim = 1 << n;
  const mask = qubits.reduce((m, q) => m | (1 << q), 0);
  const local = (idx: number) => qubits.reduce((acc, q, b) => acc | (((idx >> q) & 1) << b), 0);
  return Matrix.fromFunction(dim, dim, (i, j) => {
    if ((i & ~mask) !== (j & ~mask)) return 0;
    return gate.get(local(i), local(j));
  });
}

// ---- states ------------------------------------------------------------------

/** Computational-basis ket from a bit string, e.g. ket('01') = |q1=0, q0=1⟩. */
export function ket(bits: string): Matrix {
  if (!/^[01]+$/.test(bits)) throw new SyntaxError('ket: expected a string of 0/1');
  const idx = parseInt(bits, 2);
  return Matrix.fromFunction(1 << bits.length, 1, (i) => (i === idx ? 1 : 0));
}

/** Bra ⟨bits|. */
export function bra(bits: string): Matrix {
  return ket(bits).adjoint();
}

/** Column state vector from amplitudes. */
export function state(...amplitudes: ExprLike[]): Matrix {
  return Matrix.col(...amplitudes);
}

/** Inner product ⟨a|b⟩ of two column vectors. */
export function inner(a: Matrix, b: Matrix): Expr {
  return expand(a.adjoint().mul(b).get(0, 0));
}

/** Outer product |a⟩⟨b|. */
export function outer(a: Matrix, b: Matrix): Matrix {
  return a.mul(b.adjoint());
}

/** Expectation value ⟨ψ|O|ψ⟩. */
export function expectation(op: Matrix, psi: Matrix): Expr {
  return inner(psi, op.mul(psi));
}

/** Density matrix |ψ⟩⟨ψ|. */
export function densityMatrix(psi: Matrix): Matrix {
  return outer(psi, psi);
}
