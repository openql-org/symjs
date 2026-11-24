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

/**
 * Tests whether the delta can be nonzero in the specified Fermi sector.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns Whether the delta can be nonzero in the selected sector.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.is_above_fermi`
 * @example
 * ```ts
 * import { ex, isAboveFermi } from '@symjs/symjs';
 *
 * isAboveFermi(ex`KroneckerDelta(p, q)`); // => True
 * ```
 */
export function isAboveFermi(e: Expr): boolean { return !deltaIndices(e).some(below); }
/**
 * Tests whether the Kronecker delta can be nonzero below the Fermi level.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns Whether the delta can be nonzero in the selected sector.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.is_below_fermi`
 * @example
 * ```ts
 * import { ex, isBelowFermi } from '@symjs/symjs';
 *
 * isBelowFermi(ex`KroneckerDelta(p, q)`); // => True
 * ```
 */
export function isBelowFermi(e: Expr): boolean { return !deltaIndices(e).some(above); }
/**
 * Tests whether at least one index is confined to the specified Fermi sector.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns Whether the delta is confined to the selected sector.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.is_only_above_fermi`
 * @example
 * ```ts
 * import { ex, isOnlyAboveFermi } from '@symjs/symjs';
 *
 * isOnlyAboveFermi(ex`KroneckerDelta(p, q)`); // => False
 * ```
 */
export function isOnlyAboveFermi(e: Expr): boolean { return deltaIndices(e).some(above); }
/**
 * Tests whether a delta index restricts the delta to states below the Fermi level.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns Whether the delta is confined to the selected sector.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.is_only_below_fermi`
 * @example
 * ```ts
 * import { ex, isOnlyBelowFermi } from '@symjs/symjs';
 *
 * isOnlyBelowFermi(ex`KroneckerDelta(p, q)`); // => False
 * ```
 */
export function isOnlyBelowFermi(e: Expr): boolean { return deltaIndices(e).some(below); }
/**
 * Checks whether eliminating either index preserves the Fermi restriction.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns Whether both indices impose the same Fermi restrictions.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.indices_contain_equal_information`
 * @example
 * ```ts
 * import { ex, indicesContainEqualInformation } from '@symjs/symjs';
 *
 * indicesContainEqualInformation(ex`KroneckerDelta(p, q)`); // => True
 * indicesContainEqualInformation(ex`KroneckerDelta(p, q + 1)`); // => True
 * ```
 */
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
/**
 * Selects the more informative index, breaking ties by argument order.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns The index to retain in a substitution.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.preferred_index`
 * @example
 * ```ts
 * import { KroneckerDelta, ex, preferredIndex } from '@symjs/symjs';
 *
 * preferredIndex(KroneckerDelta(ex`i`, ex`j`)); // => i
 * ```
 */
export function preferredIndex(e: Expr): Expr { return at(deltaIndices(e), preferredPosition(e)); }
/**
 * Selects the index to eliminate when the delta is applied.
 *
 * @param e - The Kronecker delta to inspect.
 * @returns The index to eliminate in a substitution.
 * @see SymPy `sympy.functions.special.tensor_functions.KroneckerDelta.killable_index`
 * @example
 * ```ts
 * import { KroneckerDelta, ex, killableIndex } from '@symjs/symjs';
 *
 * killableIndex(KroneckerDelta(ex`i`, ex`j`)); // => j
 * ```
 */
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
 * Computes the permutation sign for integer indices, giving zero for repetitions and retaining symbolic
 * indices when needed.
 *
 * @param args - The arguments in positional order.
 * @returns The Levi-Civita symbol.
 * @see SymPy `sympy.functions.special.tensor_functions.LeviCivita`
 * @example
 * ```ts
 * import { LeviCivita } from '@symjs/symjs';
 *
 * LeviCivita(1, 2, 3); // => 1
 * LeviCivita(1, 2, 2); // => 0
 * ```
 */
export function LeviCivita(...args: ExprLike[]): Expr {
  return leviCivita(...args);
}
registerHeadResolver(LeviCivitaCall, () => leviCivita);

/**
 * Evaluates the alternating Levi-Civita symbol on the supplied indices.
 *
 * @param args - The arguments in positional order.
 * @returns The permutation-sign expression.
 * @see SymPy `sympy.functions.special.tensor_functions.Eijk`
 */
export function Eijk(...args: ExprLike[]): Expr {
  return LeviCivita(...args);
}
