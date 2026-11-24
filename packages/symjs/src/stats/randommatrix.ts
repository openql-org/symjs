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
   * Computes the probability density of a matrix drawn from the model.
   *
   * @param expr - Expression to evaluate.
   * @returns The matrix density.
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
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   */
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  /**
   * Indicates whether the probability space has an ensemble model.
   *
   * @returns Whether the space specifies an ensemble model.
   */
  get hasModel(): boolean {
    return this.args.length > 1;
  }
  /**
   * Identifies the ensemble governing the random matrices.
   *
   * @returns The ensemble model.
   * @throws TypeError when the stored model is not a random matrix ensemble.
   * @see SymPy `sympy.stats.random_matrix.RandomMatrixPSpace.model`
   */
  get model(): RandomMatrixModel {
    const m = at(this.args, 1);
    if (!isModel(m)) throw new TypeError(`${m.toString()} is not a random matrix ensemble model`);
    return m;
  }
  /**
   * Indicates whether the space defines a density for its random symbol.
   *
   * @returns The density-availability flag.
   */
  override get hasValueDensity(): boolean {
    return this.hasModel;
  }
  /**
   * Identifies the probability density of the space's random symbol.
   *
   * @returns The value density.
   */
  override get valueDensity(): Expr {
    return this.model;
  }
  /**
   * Computes the distribution induced by the expression on this space.
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
