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

/** The model of a random matrix space: an expression node with a density (SymPy RandomMatrixEnsembleModel). */
export interface RandomMatrixModel extends Expr {
  /** The density of a random matrix of the model (SymPy density). */
  density(expr: Expr): Expr;
}

/** The value is a model of random matrices. */
const isModel = (e: Expr): e is RandomMatrixModel => 'density' in e && typeof e.density === 'function';

/** SymPy RandomMatrixPSpace(sym, model=None): the probability space of a random matrix of an ensemble. */
export class RandomMatrixPSpace extends PSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), ...args.slice(1)], 'RandomMatrixPSpace');
  }
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  /** The space has a model (SymPy model is not None). */
  get hasModel(): boolean {
    return this.args.length > 1;
  }
  /** The ensemble model of the random matrices (SymPy model). */
  get model(): RandomMatrixModel {
    const m = at(this.args, 1);
    if (!isModel(m)) throw new TypeError(`${m.toString()} is not a random matrix ensemble model`);
    return m;
  }
  override get hasValueDensity(): boolean {
    return this.hasModel;
  }
  override get valueDensity(): Expr {
    return this.model;
  }
  override computeDensity(expr: Expr): DensityResult {
    if (randomMatrixSymbols(expr).length > 2 || !(expr instanceof RandomMatrixSymbol)) {
      throw new NotImplementedError('Currently, no algorithm has been implemented to handle general expressions containing multiple random matrices.');
    }
    return this.model.density(expr);
  }
}
