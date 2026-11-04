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

/** The members of a stochastic process that its probability space uses (SymPy StochasticProcess). */
export interface ProcessLike extends Expr {
  /** SymPy index_set. */
  readonly indexSet: SetExpr;
  /** SymPy state_space. */
  readonly stateSpace: SetExpr;
  /** SymPy probability(condition, given_condition, evaluate). */
  probability(condition: Expr, givenCondition?: Expr, opts?: ComputeOptions): Expr;
  /** SymPy expectation(expr, condition, evaluate). */
  expectation(expr: Expr, condition?: Expr, opts?: ComputeOptions): Expr;
}

/** The value is a stochastic process (SymPy isinstance(process, StochasticProcess)). */
const isProcess = (x: unknown): x is ProcessLike => typeof x === 'object' && x !== null && 'indexSet' in x && 'stateSpace' in x && 'expectation' in x;

/**
 * SymPy Distribution(): the distribution of a random indexed symbol of a
 * process that has no distribution at a given time (a Markov chain).
 */
export class UnspecifiedDistribution extends Distribution {
  constructor(args: readonly Expr[] = []) {
    super('Distribution', args);
  }
  pdf(): Expr {
    throw new TypeError('the distribution is not specified');
  }
  get set(): SetExpr {
    throw new TypeError('the distribution is not specified');
  }
}

/**
 * SymPy StochasticPSpace(sym, process, distribution): the probability space
 * of the random indexed symbols of a stochastic process.
 */
export class StochasticPSpace extends ProductPSpace {
  constructor(args: readonly Expr[]) {
    const process = at(args, 1);
    if (!isProcess(process)) throw new TypeError('`process` must be an instance of StochasticProcess.');
    super([symbolConverter(at(args, 0)), process, args[2] ?? new UnspecifiedDistribution()], 'StochasticPSpace');
  }
  override get isStochastic(): boolean {
    return true;
  }
  /** The stochastic process (SymPy process). */
  get process(): ProcessLike {
    return expectType(at(this.args, 1), isProcess, 'process');
  }
  /** SymPy domain: the product of the index set and the state space. */
  override get domain(): RandomDomain {
    return new ProductDomain([this.process.indexSet, this.process.stateSpace]);
  }
  get symbol(): Expr {
    return at(this.args, 0);
  }
  get distribution(): Distribution {
    return cast(at(this.args, 2), Distribution, 'distribution');
  }
  override probabilityGiven(condition: Expr, givenCondition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.probability(condition, givenCondition, opts);
  }
  override expectationGiven(expr: Expr, condition: Expr | undefined, opts: ComputeOptions = {}): Expr {
    return this.process.expectation(expr, condition, opts);
  }
}
