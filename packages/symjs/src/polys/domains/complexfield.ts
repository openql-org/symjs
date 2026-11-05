// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/complexfield.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The complex floating-point field CC (SymPy ComplexField). Elements
 * are expressions a + b*I with floats a and b at the field's precision.
 */

import { DomainError } from '../../core/errors';
import type { ExprLike } from '../../core/nodes';
import { type Expr, Float, S } from '../../core/nodes';
import { add, mul, sympify } from '../../core/ops';
import { asRealImag } from '../../core/methods';
import { evalf } from '../../numeric/evalf';
import { str } from '../../printing/str';
import { CoercionFailed, Domain } from '../domains';
import { QQ_I } from './gaussiandomains';

/** The field of complex floats (SymPy ComplexField); CC has 53 bits. */
export class ComplexField extends Domain {
  readonly ground = 'RR' as const;
  readonly isField = true;
  /** The precision in bits (SymPy precision). */
  readonly precision: number;
  constructor(prec = 53) {
    super();
    this.precision = prec;
  }
  /** The precision in decimal digits (SymPy dps). */
  get dps(): number {
    return Math.max(1, Math.round(this.precision / 3.3219280948873626) - 1);
  }
  toString(): string {
    return this.precision === 53 ? 'CC' : `CC_${this.precision}`;
  }
  override equals(o: Domain): boolean {
    return o instanceof ComplexField && o.precision === this.precision;
  }
  /** a + b*I with float parts (SymPy from_sympy); throws CoercionFailed for a non-number. */
  canon(e: Expr): Expr {
    const [re, im] = asRealImag(evalf(e, this.dps));
    if (!(re instanceof Float || re === S.Zero) || !(im instanceof Float || im === S.Zero)) throw new CoercionFailed(`expected complex number, got ${str(e)}`);
    const f = (x: Expr): Expr => (x instanceof Float ? new Float(x.mpf, this.precision) : new Float(0, this.precision));
    return add(f(re), mul(S.I, f(im)));
  }
  fromSympy(e: ExprLike): Expr {
    return this.canon(sympify(e));
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    throw new DomainError(`there is no ring associated with ${this.toString()}`);
  }
  /** The exact counterpart QQ_I (SymPy get_exact). */
  getExact(): Domain {
    return QQ_I;
  }
  /** SymPy: complex floats are neither positive nor negative. */
  override isNegative(_a: unknown): boolean {
    return false;
  }
  override isPositive(_a: unknown): boolean {
    return false;
  }
  override isNonnegative(_a: unknown): boolean {
    return false;
  }
  override isNonpositive(_a: unknown): boolean {
    return false;
  }
  override gcd(_a: unknown, _b: unknown): Expr {
    return this.canon(S.One);
  }
  override lcm(a: unknown, b: unknown): Expr {
    return this.canon(mul(this.toSympy(a), this.toSympy(b)));
  }
}

/** SymPy CC (53 bits). */
export const CC: ComplexField = new ComplexField();
