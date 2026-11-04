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

/** SymPy BaseScalar(index, system, pretty_str, latex_str): a coordinate symbol. */
export class BaseScalarNode extends Sym {
  readonly index: number;
  readonly system: CoordSysBase;
  readonly #pretty: string;
  readonly #latex: string;

  constructor(index: number, system: CoordSysBase, prettyStr?: string | Sym, latexStr?: string | Sym) {
    if (!(system instanceof CoordSysBase)) throw new TypeError('system should be a CoordSys3D');
    if (!Number.isInteger(index) || index < 0 || index > 2) throw new RangeError('Invalid index specified.');
    super(`${system.sysName}.${at(system.variableNames, index)}`);
    this.index = index;
    this.system = system;
    this.#pretty = prettyStr === undefined ? `x${index}` : prettyStr instanceof Sym ? prettyStr.name : prettyStr;
    this.#latex = latexStr === undefined ? `x_${index}` : latexStr instanceof Sym ? latexStr.name : latexStr;
  }

  /** SymPy _pretty_form. */
  override get prettyForm(): string {
    return this.#pretty;
  }

  /** SymPy _latex_form. */
  override get latexForm(): string {
    return this.#latex;
  }

  /** Sorted as SymPy's class BaseScalar (before the symbols). */
  override get sortClass(): string {
    return 'BaseScalar';
  }

  /** Equal to the base scalar of the same index and system (SymPy _id). */
  protected override computeKey(): string {
    return `BaseScalar(${this.index};${this.system.key})`;
  }
}

/** SymPy BaseScalar(index, system, pretty_str=None, latex_str=None). */
export const BaseScalar = /* @__PURE__ */ callableClass(
  BaseScalarNode,
  (index: number, system: CoordSysBase, prettyStr?: string | Sym, latexStr?: string | Sym): BaseScalarNode => new BaseScalarNode(index, system, prettyStr, latexStr),
);
export type BaseScalar = BaseScalarNode;
