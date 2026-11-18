// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumption queries that use the new assumptions when they are given
 * (SymPy sympy.assumptions.wrapper): is_infinite, is_extended_real and
 * is_extended_nonnegative. Without assumptions they are the facts of the
 * expression itself (SymPy `obj.is_infinite`, ...).
 */

import type { ExprLike } from '../core/nodes';
import type { Assumption, PredicateName } from '../core/refine';
import { Q, ask } from '../core/refine';
import { sympify } from '../core/ops';
import { fact } from '../core/exprfacts';
import type { Truth } from '../core/truth';
import { toTruth } from '../core/truth';

/** The fact of obj (without assumptions) or what ask decides under them. */
function query(obj: ExprLike, name: PredicateName, assumptions: Assumption | undefined): Truth {
  if (assumptions === undefined) return toTruth(fact(sympify(obj), name));
  return ask(Q[name](obj), assumptions);
}

/** SymPy is_infinite: Q.infinite of obj under the assumptions ('unknown' when undecided). */
export function isInfinite(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'infinite', assumptions);
}

/** SymPy is_extended_real: Q.extended_real of obj under the assumptions. */
export function isExtendedReal(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_real', assumptions);
}

/** SymPy is_extended_nonnegative: Q.extended_nonnegative of obj under the assumptions. */
export function isExtendedNonnegative(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_nonnegative', assumptions);
}

/** An expression whose assumption properties are evaluated under local facts. */
export class AssumptionsWrapper {
  constructor(readonly expr: ExprLike, readonly assumptions?: Assumption) {}

  get isAlgebraic(): Truth {
    return query(this.expr, 'algebraic', this.assumptions);
  }

  get isAntihermitian(): Truth {
    return query(this.expr, 'antihermitian', this.assumptions);
  }

  get isCommutative(): Truth {
    return query(this.expr, 'commutative', this.assumptions);
  }

  get isComplex(): Truth {
    return query(this.expr, 'complex', this.assumptions);
  }

  get isComposite(): Truth {
    return query(this.expr, 'composite', this.assumptions);
  }

  get isEven(): Truth {
    return query(this.expr, 'even', this.assumptions);
  }

  get isExtendedNegative(): Truth {
    return query(this.expr, 'extended_negative', this.assumptions);
  }

  get isExtendedNonnegative(): Truth {
    return query(this.expr, 'extended_nonnegative', this.assumptions);
  }

  get isExtendedNonpositive(): Truth {
    return query(this.expr, 'extended_nonpositive', this.assumptions);
  }

  get isExtendedNonzero(): Truth {
    return query(this.expr, 'extended_nonzero', this.assumptions);
  }

  get isExtendedPositive(): Truth {
    return query(this.expr, 'extended_positive', this.assumptions);
  }

  get isExtendedReal(): Truth {
    return query(this.expr, 'extended_real', this.assumptions);
  }

  get isFinite(): Truth {
    return query(this.expr, 'finite', this.assumptions);
  }

  get isHermitian(): Truth {
    return query(this.expr, 'hermitian', this.assumptions);
  }

  get isImaginary(): Truth {
    return query(this.expr, 'imaginary', this.assumptions);
  }

  get isInfinite(): Truth {
    return query(this.expr, 'infinite', this.assumptions);
  }

  get isInteger(): Truth {
    return query(this.expr, 'integer', this.assumptions);
  }

  get isIrrational(): Truth {
    return query(this.expr, 'irrational', this.assumptions);
  }

  get isNegative(): Truth {
    return query(this.expr, 'negative', this.assumptions);
  }

  get isNoninteger(): Truth {
    return query(this.expr, 'noninteger', this.assumptions);
  }

  get isNonnegative(): Truth {
    return query(this.expr, 'nonnegative', this.assumptions);
  }

  get isNonpositive(): Truth {
    return query(this.expr, 'nonpositive', this.assumptions);
  }

  get isNonzero(): Truth {
    return query(this.expr, 'nonzero', this.assumptions);
  }

  get isOdd(): Truth {
    return query(this.expr, 'odd', this.assumptions);
  }

  get isPositive(): Truth {
    return query(this.expr, 'positive', this.assumptions);
  }

  get isPrime(): Truth {
    return query(this.expr, 'prime', this.assumptions);
  }

  get isRational(): Truth {
    return query(this.expr, 'rational', this.assumptions);
  }

  get isReal(): Truth {
    return query(this.expr, 'real', this.assumptions);
  }

  get isTranscendental(): Truth {
    return query(this.expr, 'transcendental', this.assumptions);
  }

  get isZero(): Truth {
    return query(this.expr, 'zero', this.assumptions);
  }
}
