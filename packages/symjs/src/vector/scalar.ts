// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/scalar.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.scalar: BaseScalar, a coordinate variable of a
 * coordinate system (C.x, C.y, C.z).
 *
 * A base scalar is a symbol named after its system (`C.x`), so it can be
 * differentiated, integrated and solved for like any symbol; it equals
 * only the base scalar of the same index of the same system.
 */

import { Sym } from '../core/nodes';
import { callableClass } from '../core/callable';
import { at } from '../core/guard';
import { CoordSysBase } from './basisdependent';

/**
 * A coordinate symbol.
 *
 * @see SymPy `sympy.vector.scalar.BaseScalar`
 */
export class BaseScalarNode extends Sym {
  /** Zero-based index or indices selecting the desired component. */
  readonly index: number;
  /**
   * The coordinate system that supplies the basis.
   *
   * @see SymPy `sympy.vector.scalar.BaseScalar.system`
   */
  readonly system: CoordSysBase;
  readonly #pretty: string;
  readonly #latex: string;

  /**
   * Constructs an instance of `BaseScalarNode`.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @param system - Coordinate system in which to express components.
   * @param prettyStr - Label for the pretty printer.
   * @param latexStr - Label for the LaTeX printer.
   * @throws RangeError when the basis index is outside 0 through 2.
   * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
   */
  constructor(index: number, system: CoordSysBase, prettyStr?: string | Sym, latexStr?: string | Sym) {
    if (!(system instanceof CoordSysBase)) throw new TypeError('system should be a CoordSys3D');
    if (!Number.isInteger(index) || index < 0 || index > 2) throw new RangeError('Invalid index specified.');
    super(`${system.sysName}.${at(system.variableNames, index)}`);
    this.index = index;
    this.system = system;
    this.#pretty = prettyStr === undefined ? `x${index}` : prettyStr instanceof Sym ? prettyStr.name : prettyStr;
    this.#latex = latexStr === undefined ? `x_${index}` : latexStr instanceof Sym ? latexStr.name : latexStr;
  }

  /**
   * The label used by the pretty printer.
   *
   * @returns The label used by the pretty printer.
   */
  override get prettyForm(): string {
    return this.#pretty;
  }

  /**
   * LaTeX representation of this basis element.
   *
   * @returns The formatted text.
   */
  override get latexForm(): string {
    return this.#latex;
  }

  /**
   * The printed name (R.x), as SymPy's BaseScalar repr is its str.
   *
   * @returns The constructor representation.
   */
  printRepr(): string {
    return this.name;
  }

  /**
   * Sorted as SymPy's class BaseScalar (before the symbols).
   *
   * @returns The formatted text.
   */
  override get sortClass(): string {
    return 'BaseScalar';
  }

  /** Equal to the base scalar of the same index and system (SymPy _id). */
  protected override computeKey(): string {
    return `BaseScalar(${this.index};${this.system.key})`;
  }
}

/**
 * A coordinate scalar of a three-dimensional coordinate system.
 *
 * @param index - Zero-based index or indices selecting the desired component.
 * @param system - Coordinate system in which to express components.
 * @param prettyStr - Label for the pretty printer.
 * @param latexStr - Label for the LaTeX printer.
 * @returns The resulting `BaseScalar` expression.
 * @throws RangeError when the basis index is outside 0 through 2.
 * @throws TypeError when a supplied coordinate system is not a `CoordSys3D`.
 * @see SymPy `sympy.vector.scalar.BaseScalar`
 */
export const BaseScalar = /* @__PURE__ */ callableClass(
  BaseScalarNode,
  (index: number, system: CoordSysBase, prettyStr?: string | Sym, latexStr?: string | Sym): BaseScalarNode => new BaseScalarNode(index, system, prettyStr, latexStr),
);
export type BaseScalar = BaseScalarNode;
