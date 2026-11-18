// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/tensor_functions.py),
// BSD 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The Levi-Civita symbol (SymPy LeviCivita and Eijk). KroneckerDelta is
 * in functions/special/hyper.ts.
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Fn, Rational, S, Sym, registerHeadResolver } from '../../core/nodes';
import type { FunctionDefinition } from '../../core/defun';
import { DefinedFunctionCall, defineFunction } from '../../core/defun';
import { add, mul, neg } from '../../core/ops';
import { at, pair } from '../../core/guard';

function deltaIndices(e: Expr): readonly [Expr, Expr] {
  if (!(e instanceof Fn) || e.name !== 'KroneckerDelta') throw new TypeError('expected KroneckerDelta');
  return pair(e.args);
}
const above = (i: Expr): boolean => i instanceof Sym && i.assumptions.aboveFermi === true;
const below = (i: Expr): boolean => i instanceof Sym && i.assumptions.belowFermi === true;

/** The delta can be nonzero above / below the Fermi level. */
export function isAboveFermi(e: Expr): boolean { return !deltaIndices(e).some(below); }
export function isBelowFermi(e: Expr): boolean { return !deltaIndices(e).some(above); }
/** At least one index is restricted to the indicated Fermi sector. */
export function isOnlyAboveFermi(e: Expr): boolean { return deltaIndices(e).some(above); }
export function isOnlyBelowFermi(e: Expr): boolean { return deltaIndices(e).some(below); }
/** Whether either index can be eliminated without losing a Fermi restriction. */
export function indicesContainEqualInformation(e: Expr): boolean {
  const indices = deltaIndices(e);
  return indices.every(below) || indices.every(above) || (isAboveFermi(e) && isBelowFermi(e));
}
function preferredPosition(e: Expr): number {
  const [i] = deltaIndices(e);
  if (!isAboveFermi(e)) return below(i) ? 0 : 1;
  if (!isBelowFermi(e)) return above(i) ? 0 : 1;
  return 0;
}
/** The index carrying the most information, with ties resolved by argument order. */
export function preferredIndex(e: Expr): Expr { return at(deltaIndices(e), preferredPosition(e)); }
/** The index eliminated when the delta is applied. */
export function killableIndex(e: Expr): Expr { return at(deltaIndices(e), 1 - preferredPosition(e)); }

/** SymPy eval_levicivita: prod_{i<j} (a_j - a_i) / prod_i i!, for integer arguments. */
function evalLeviCivita(args: readonly bigint[]): Expr {
  let num = 1n;
  let den = 1n;
  let fact = 1n;
  for (let i = 0; i < args.length; i++) {
    if (i > 0) fact *= BigInt(i);
    den *= fact;
    for (let j = i + 1; j < args.length; j++) num *= at(args, j) - at(args, i);
  }
  return Rational.of(num, den);
}

class LeviCivitaCall extends DefinedFunctionCall {
  constructor(args: readonly Expr[]) { super('LeviCivita', args, leviCivitaDefinition); }
  override printLatex(print: (e: Expr) => string): string {
    return `\\varepsilon_{${this.args.map(print).join(' ')}}`;
  }
  override conjugateSelf(): Expr { return this; }
  override adjointSelf(): Expr { return this; }
  override isRealSelf(): boolean { return true; }
  override doitSelf(): Expr {
    const factors: Expr[] = [];
    let denominator = 1n;
    let factorial = 1n;
    for (const [i, a] of this.args.entries()) {
      factorial *= BigInt(Math.max(1, i));
      denominator *= factorial;
      for (const b of this.args.slice(i + 1)) factors.push(add(b, neg(a)));
    }
    return mul(Rational.of(1n, denominator), ...factors);
  }
}

const leviCivitaDefinition: FunctionDefinition = {
  eval: (...indices) => {
    const ints = indices.flatMap((a) => (a instanceof Rational && a.isInteger ? [a.p] : []));
    if (ints.length === indices.length) return evalLeviCivita(ints);
    if (new Set(indices.map((a) => a.key)).size < indices.length) return S.Zero;
    return new LeviCivitaCall(indices);
  },
};
const leviCivita = defineFunction('LeviCivita', leviCivitaDefinition);

/**
 * The Levi-Civita symbol (SymPy LeviCivita): the sign of the permutation of
 * integer arguments, 0 for a repeated index, unevaluated otherwise.
 */
export function LeviCivita(...args: ExprLike[]): Expr {
  return leviCivita(...args);
}
registerHeadResolver(LeviCivitaCall, () => leviCivita);

/** SymPy Eijk: the Levi-Civita symbol, LeviCivita(*args). */
export function Eijk(...args: ExprLike[]): Expr {
  return LeviCivita(...args);
}
