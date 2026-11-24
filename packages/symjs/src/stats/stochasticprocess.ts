// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/stochastic_process.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.stochastic_process: the probability space of the
 * random indexed symbols of a stochastic process. Probabilities and
 * expectations of the random indexed symbols are computed by the process
 * (sympy.stats.stochastic_process_types).
 */

import type { Expr } from '../core/nodes';
import { at, cast, expectType } from '../core/guard';
import type { SetExpr } from '../sets/sets';
import { Distribution, ProductDomain, ProductPSpace, symbolConverter } from './rv';
import type { ComputeOptions, RandomDomain } from './rv';

/** The members of a stochastic process that its probability space uses. */
export interface ProcessLike extends Expr {
  /** The set of time indices of the process. */
  readonly indexSet: SetExpr;
  /** The set of possible process values. */
  readonly stateSpace: SetExpr;
  /**
   * The probability that the event holds.
   *
   * @param condition - Condition on the random variables.
   * @param givenCondition - Additional event assumed to hold.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability of the event.
   */
  probability(condition: Expr, givenCondition?: Expr, opts?: ComputeOptions): Expr;
  /**
   * The expected value of the expression in this process.
   *
   * @param expr - Expression to evaluate.
   * @param condition - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value of the expression in this process.
   */
  expectation(expr: Expr, condition?: Expr, opts?: ComputeOptions): Expr;
}

/** The value is a stochastic process (SymPy isinstance(process, StochasticProcess)). */
const isProcess = (x: unknown): x is ProcessLike => typeof x === 'object' && x !== null && 'indexSet' in x && 'stateSpace' in x && 'expectation' in x;

/**
 * An unspecified probability law for the value of a stochastic process.
 *
 * @see SymPy `sympy.stats.rv.Distribution`
 */
export class UnspecifiedDistribution extends Distribution {
  /**
   * Constructs a new `UnspecifiedDistribution`.
   *
   * @param args - The defining expressions in structural order.
   */
  constructor(args: readonly Expr[] = []) {
    super('Distribution', args);
  }
  /**
   * The probability density at the supplied value.
   *
   * @returns The density evaluated at the supplied outcome.
   * @throws TypeError when the probability law is unspecified.
   */
  pdf(): Expr {
    throw new TypeError('the distribution is not specified');
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @throws TypeError when the probability law is unspecified.
   */
  get set(): SetExpr {
    throw new TypeError('the distribution is not specified');
  }
}

/**
 * The probability space
 * of the random indexed symbols of a stochastic process.
 *
 * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace`
 */
export class StochasticPSpace extends ProductPSpace {
  /**
   * Constructs a new `StochasticPSpace`.
   *
   * @param args - Operands in the order `sym`, `process`, `distribution`.
   * @throws TypeError when the process argument does not represent a stochastic process.
   */
  constructor(args: readonly Expr[]) {
    const process = at(args, 1);
    if (!isProcess(process)) throw new TypeError('`process` must be an instance of StochasticProcess.');
    super([symbolConverter(at(args, 0)), process, args[2] ?? new UnspecifiedDistribution()], 'StochasticPSpace');
  }
  /**
   * Whether the probability space is stochastic.
   *
   * @returns `true` for this space.
   */
  override get isStochastic(): boolean {
    return true;
  }
  /**
   * The stochastic process.
   *
   * @returns The stochastic process.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.process`
   */
  get process(): ProcessLike {
    return expectType(at(this.args, 1), isProcess, 'process');
  }
  /**
   * The product of the index set and the state space.
   *
   * @returns The product of the index set and the state space.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.domain`
   */
  override get domain(): RandomDomain {
    return new ProductDomain([this.process.indexSet, this.process.stateSpace]);
  }
  /**
   * The underlying symbol naming the random variable.
   *
   * @returns The underlying symbol naming the random variable.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.symbol`
   */
  get symbol(): Expr {
    return at(this.args, 0);
  }
  /**
   * The probability law governing the random variable.
   *
   * @returns The probability law governing the random variable.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.distribution`
   */
  get distribution(): Distribution {
    return cast(at(this.args, 2), Distribution, 'distribution');
  }
  /**
   * The probability of the event under the additional condition.
   *
   * @param condition - Condition on the random variables.
   * @param givenCondition - Additional event assumed to hold.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability of the event under the additional condition.
   */
  override probabilityGiven(condition: Expr, givenCondition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.probability(condition, givenCondition, opts);
  }
  /**
   * The expected value under the conditioning event.
   *
   * @param expr - Expression to evaluate.
   * @param condition - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value under the conditioning event.
   */
  override expectationGiven(expr: Expr, condition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.expectation(expr, condition, opts);
  }
}
