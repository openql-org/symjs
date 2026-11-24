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
   * Computes the probability assigned to the event.
   *
   * @param condition - Condition on the random variables.
   * @param givenCondition - Additional event assumed to hold.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability of the event.
   */
  probability(condition: Expr, givenCondition?: Expr, opts?: ComputeOptions): Expr;
  /**
   * Computes the mean of the expression under the process law.
   *
   * @param expr - Expression to evaluate.
   * @param condition - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expectation.
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
   * Evaluates the probability density at the supplied outcome.
   *
   * @returns The density evaluated at the supplied outcome.
   * @throws TypeError when the probability law is unspecified.
   */
  pdf(): Expr {
    throw new TypeError('the distribution is not specified');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
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
   * Tests whether this is a stochastic process probability space.
   *
   * @returns `true` for this space.
   */
  override get isStochastic(): boolean {
    return true;
  }
  /**
   * Identifies the stochastic process governing this space.
   *
   * @returns The process object.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.process`
   */
  get process(): ProcessLike {
    return expectType(at(this.args, 1), isProcess, 'process');
  }
  /**
   * Combines the process time indices with the possible states.
   *
   * @returns The product domain.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.domain`
   */
  override get domain(): RandomDomain {
    return new ProductDomain([this.process.indexSet, this.process.stateSpace]);
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.symbol`
   */
  get symbol(): Expr {
    return at(this.args, 0);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.stochastic_process.StochasticPSpace.distribution`
   */
  get distribution(): Distribution {
    return cast(at(this.args, 2), Distribution, 'distribution');
  }
  /**
   * Computes the chance of the event subject to the given condition.
   *
   * @param condition - Condition on the random variables.
   * @param givenCondition - Additional event assumed to hold.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The conditional probability.
   */
  override probabilityGiven(condition: Expr, givenCondition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.probability(condition, givenCondition, opts);
  }
  /**
   * Computes the mean of the expression under the supplied condition.
   *
   * @param expr - Expression to evaluate.
   * @param condition - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The conditional expectation.
   */
  override expectationGiven(expr: Expr, condition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.expectation(expr, condition, opts);
  }
}
