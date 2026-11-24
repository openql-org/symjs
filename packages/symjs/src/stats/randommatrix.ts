// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/random_matrix.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.random_matrix: the probability space of the
 * random matrices of a random matrix ensemble (its model).
 */

import type { Expr, Sym } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { at } from '../core/guard';
import { PSpace, RandomMatrixSymbol, randomMatrixSymbols, symbolConverter } from './rv';
import type { DensityResult } from './rv';

/** An expression representing a random matrix model with a density evaluator. */
export interface RandomMatrixModel extends Expr {
  /**
   * The density of a random matrix of the model.
   *
   * @param expr - Expression to evaluate.
   * @returns The density of a random matrix of the model.
   */
  density(expr: Expr): Expr;
}

/** The value is a model of random matrices. */
const isModel = (e: Expr): e is RandomMatrixModel => 'density' in e && typeof e.density === 'function';

/**
 * The probability space of a random matrix of an ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix.RandomMatrixPSpace`
 */
export class RandomMatrixPSpace extends PSpace {
  /**
   * Constructs a new `RandomMatrixPSpace`.
   *
   * @param args - Operands in the order `sym`, `model`.
   */
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), ...args.slice(1)], 'RandomMatrixPSpace');
  }
  /**
   * The underlying symbol naming the random variable.
   *
   * @returns The underlying symbol naming the random variable.
   */
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  /**
   * The space has a model (SymPy model is not None).
   *
   * @returns Whether the space specifies an ensemble model.
   */
  get hasModel(): boolean {
    return this.args.length > 1;
  }
  /**
   * The ensemble model of the random matrices.
   *
   * @returns The ensemble model of the random matrices.
   * @throws TypeError when the stored model is not a random matrix ensemble.
   * @see SymPy `sympy.stats.random_matrix.RandomMatrixPSpace.model`
   */
  get model(): RandomMatrixModel {
    const m = at(this.args, 1);
    if (!isModel(m)) throw new TypeError(`${m.toString()} is not a random matrix ensemble model`);
    return m;
  }
  /**
   * Whether this space supplies a density for its random symbol.
   *
   * @returns Whether this space supplies a density for its random symbol.
   */
  override get hasValueDensity(): boolean {
    return this.hasModel;
  }
  /**
   * The density associated with the random symbol of the space.
   *
   * @returns The density associated with the random symbol of the space.
   */
  override get valueDensity(): Expr {
    return this.model;
  }
  /**
   * The distribution of the expression on this probability space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @throws NotImplementedError when the expression involves unsupported combinations of random matrices.
   * @see SymPy `sympy.stats.random_matrix.RandomMatrixPSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    if (randomMatrixSymbols(expr).length > 2 || !(expr instanceof RandomMatrixSymbol)) {
      throw new NotImplementedError('Currently, no algorithm has been implemented to handle general expressions containing multiple random matrices.');
    }
    return this.model.density(expr);
  }
}
