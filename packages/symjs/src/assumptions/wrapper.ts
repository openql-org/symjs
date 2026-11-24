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

/**
 * Tests whether the expression is infinite under the given assumptions.
 *
 * @param obj - Expression whose assumptions are queried.
 * @param assumptions - Facts assumed to hold.
 * @returns Whether the predicate holds, or `'unknown'` when undecided.
 * @see SymPy `sympy.assumptions.wrapper.is_infinite`
 */
export function isInfinite(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'infinite', assumptions);
}

/**
 * Tests whether the expression is real or one of the two real infinities.
 *
 * @param obj - Expression whose assumptions are queried.
 * @param assumptions - Facts assumed to hold.
 * @returns Whether the predicate holds, or `'unknown'` when undecided.
 * @see SymPy `sympy.assumptions.wrapper.is_extended_real`
 */
export function isExtendedReal(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_real', assumptions);
}

/**
 * Tests whether the expression is nonnegative on the extended real line.
 *
 * @param obj - Expression whose assumptions are queried.
 * @param assumptions - Facts assumed to hold.
 * @returns Whether the predicate holds, or `'unknown'` when undecided.
 * @see SymPy `sympy.assumptions.wrapper.is_extended_nonnegative`
 */
export function isExtendedNonnegative(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_nonnegative', assumptions);
}

/**
 * An expression whose assumption properties are evaluated under local facts.
 *
 * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper`
 * @example
 * ```ts
 * import { AssumptionsWrapper, Q, symbols } from '@symjs/symjs';
 *
 * const [y] = symbols('y');
 * new AssumptionsWrapper(y, Q.even(y)).isInteger; // => True
 * ```
 */
export class AssumptionsWrapper {
  /**
   * Constructs a new `AssumptionsWrapper`.
   *
   * @param expr - Expression to evaluate.
   * @param assumptions - Facts assumed to hold.
   */
  constructor(
    /** The expression to which the operation applies. */
    readonly expr: ExprLike,
    /** Local facts used to query the expression. */
    readonly assumptions?: Assumption
  ) {}

  /**
   * Whether the expression is algebraic under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_algebraic`
   */
  get isAlgebraic(): Truth {
    return query(this.expr, 'algebraic', this.assumptions);
  }

  /**
   * Whether the expression is antihermitian under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_antihermitian`
   */
  get isAntihermitian(): Truth {
    return query(this.expr, 'antihermitian', this.assumptions);
  }

  /**
   * Whether the expression is commutative under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_commutative`
   */
  get isCommutative(): Truth {
    return query(this.expr, 'commutative', this.assumptions);
  }

  /**
   * Whether the expression is complex under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_complex`
   */
  get isComplex(): Truth {
    return query(this.expr, 'complex', this.assumptions);
  }

  /**
   * Whether the expression is composite under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_composite`
   */
  get isComposite(): Truth {
    return query(this.expr, 'composite', this.assumptions);
  }

  /**
   * Whether the expression is even under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_even`
   */
  get isEven(): Truth {
    return query(this.expr, 'even', this.assumptions);
  }

  /**
   * Whether the expression is extended negative under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_negative`
   */
  get isExtendedNegative(): Truth {
    return query(this.expr, 'extended_negative', this.assumptions);
  }

  /**
   * Whether the expression is extended nonnegative under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_nonnegative`
   */
  get isExtendedNonnegative(): Truth {
    return query(this.expr, 'extended_nonnegative', this.assumptions);
  }

  /**
   * Whether the expression is extended nonpositive under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_nonpositive`
   */
  get isExtendedNonpositive(): Truth {
    return query(this.expr, 'extended_nonpositive', this.assumptions);
  }

  /**
   * Whether the expression is extended nonzero under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_nonzero`
   */
  get isExtendedNonzero(): Truth {
    return query(this.expr, 'extended_nonzero', this.assumptions);
  }

  /**
   * Whether the expression is extended positive under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_positive`
   */
  get isExtendedPositive(): Truth {
    return query(this.expr, 'extended_positive', this.assumptions);
  }

  /**
   * Whether the expression is extended real under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_extended_real`
   */
  get isExtendedReal(): Truth {
    return query(this.expr, 'extended_real', this.assumptions);
  }

  /**
   * Whether the expression is finite under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_finite`
   */
  get isFinite(): Truth {
    return query(this.expr, 'finite', this.assumptions);
  }

  /**
   * Whether the expression is hermitian under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_hermitian`
   */
  get isHermitian(): Truth {
    return query(this.expr, 'hermitian', this.assumptions);
  }

  /**
   * Whether the expression is imaginary under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_imaginary`
   */
  get isImaginary(): Truth {
    return query(this.expr, 'imaginary', this.assumptions);
  }

  /**
   * Whether the expression is infinite under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_infinite`
   */
  get isInfinite(): Truth {
    return query(this.expr, 'infinite', this.assumptions);
  }

  /**
   * Whether the expression is integer under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_integer`
   */
  get isInteger(): Truth {
    return query(this.expr, 'integer', this.assumptions);
  }

  /**
   * Whether the expression is irrational under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_irrational`
   */
  get isIrrational(): Truth {
    return query(this.expr, 'irrational', this.assumptions);
  }

  /**
   * Whether the expression is negative under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_negative`
   */
  get isNegative(): Truth {
    return query(this.expr, 'negative', this.assumptions);
  }

  /**
   * Whether the expression is noninteger under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_noninteger`
   */
  get isNoninteger(): Truth {
    return query(this.expr, 'noninteger', this.assumptions);
  }

  /**
   * Whether the expression is nonnegative under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_nonnegative`
   */
  get isNonnegative(): Truth {
    return query(this.expr, 'nonnegative', this.assumptions);
  }

  /**
   * Whether the expression is nonpositive under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_nonpositive`
   */
  get isNonpositive(): Truth {
    return query(this.expr, 'nonpositive', this.assumptions);
  }

  /**
   * Whether the expression is nonzero under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_nonzero`
   */
  get isNonzero(): Truth {
    return query(this.expr, 'nonzero', this.assumptions);
  }

  /**
   * Whether the expression is odd under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_odd`
   */
  get isOdd(): Truth {
    return query(this.expr, 'odd', this.assumptions);
  }

  /**
   * Whether the expression is positive under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_positive`
   */
  get isPositive(): Truth {
    return query(this.expr, 'positive', this.assumptions);
  }

  /**
   * Whether the expression is prime under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_prime`
   */
  get isPrime(): Truth {
    return query(this.expr, 'prime', this.assumptions);
  }

  /**
   * Whether the expression is rational under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_rational`
   */
  get isRational(): Truth {
    return query(this.expr, 'rational', this.assumptions);
  }

  /**
   * Whether the expression is real under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_real`
   */
  get isReal(): Truth {
    return query(this.expr, 'real', this.assumptions);
  }

  /**
   * Whether the expression is transcendental under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_transcendental`
   */
  get isTranscendental(): Truth {
    return query(this.expr, 'transcendental', this.assumptions);
  }

  /**
   * Whether the expression is zero under the local assumptions, or `'unknown'` if undecided.
   *
   * @returns Whether the predicate holds, or `'unknown'` when undecided.
   * @see SymPy `sympy.assumptions.wrapper.AssumptionsWrapper.is_zero`
   */
  get isZero(): Truth {
    return query(this.expr, 'zero', this.assumptions);
  }
}
