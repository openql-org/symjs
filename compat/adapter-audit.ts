// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { ADAPTERS, type Case } from './harness';
import { PORTS } from './ports';

/** A passing adapter is not automatically evidence of a public implementation. */
export const REVIEWED_ADAPTERS: Readonly<Record<string, string>> = {
  TableForm: 'TableForm; convert nested collection cells to their Python text representation',
  nonlinsolve: 'nonlinsolve',
  substitution: 'substitution',
  checksol: 'checksol',
  linsolve: 'linsolve / linsolveAugmented / gaussJordanSolve',
  _linsolve: '_linsolve; map EmptySet to the internal Python None result',
  _linear_eq_to_dict: '_linearEqToDict; preserve the result tuple and coefficient maps',
  _lin_eq2dict: '_linEq2dict; convert the symbol set and preserve the result tuple',
  dom_eigenvects: 'domEigenvects; preserve nested tuples and lists',
  dom_eigenvects_to_sympy: 'domEigenvectsToSympy; convert domain tuples and the column-matrix factory',
  solve_lin_sys: 'solveLinSys; reconstruct PolyRing inputs and convert expression coefficients to the Python domain representation',
  solve_linear_system: 'linsolveAugmented',
  solve_linear_system_LU: 'linsolveAugmented',
  solve_poly_system: 'solvePolySystem',
  solve_undetermined_coeffs: 'solveUndeterminedCoeffs',
  trigsimp_groebner: 'trigsimpGroebner; convert Python function hints and containers to public options',
  nsolve: 'nsolve; scalar and system arguments only',
  finite_diff_weights: 'finiteDiffWeights; convert the derivative order to a JavaScript number',
  constantsimp: 'constantsimp; convert the set of constants to an array',
  integer_powers: 'integerPowers; preserve Python tuple/list nesting',
  cornacchia: 'cornacchia; format the solution set as tuples',
  diop_univariate: 'diopUnivariate; format the solution set as tuples',
  diop_quadratic: 'diopQuadratic; format the solution set as tuples',
  diop_solve: 'diopSolve; preserve the tuple versus set result',
  diop_general_sum_of_squares: 'diopGeneralSumOfSquares; format the solution set as tuples',
  diop_general_sum_of_even_powers: 'diopGeneralSumOfEvenPowers; format the solution set as tuples',
  prime_as_sum_of_two_squares: 'primeAsSumOfTwoSquares; represent EmptySet as the Python None result',
  invert_complex: 'invertComplex; preserve the result tuple',
  invert_real: 'invertReal; preserve the result tuple',
  solve_generic: 'solveGeneric; extract the generator order from polynomial Options',
  solve_biquadratic: 'solveBiquadratic; extract the generator order from polynomial Options',
};
/** Known mathematical implementations still in the harness, pending migration. */
export const COMPUTATIONAL_ADAPTERS: Readonly<Record<string, string>> = {
  solve: 'Implicit and special-form solving branches are implemented in the adapter.',
  solve_triangulated: 'The adapter selects algebraic roots using numerical matching.',
  div: 'Integer-domain division is computed in divOverZZ.',
  rem: 'Integer-domain remainders are computed in divOverZZ.',
  ff: 'Polynomial falling factorials are computed in polyFactorial.',
  rf: 'Polynomial rising factorials are computed in polyFactorial.',
};
export type Evidence = 'public-call' | 'reviewed-conversion' | 'harness-computation' | 'unreviewed-adapter' | 'unreviewed-translation';
export function evidenceFor(c: Case): Evidence {
  if (PORTS[`${c.module}:${c.src}`]) return 'unreviewed-translation';
  if (COMPUTATIONAL_ADAPTERS[c.fn]) return 'harness-computation';
  if (REVIEWED_ADAPTERS[c.fn]) return 'reviewed-conversion';
  return ADAPTERS[c.fn] ? 'unreviewed-adapter' : 'public-call';
}
export function adapterInventory(): { name: string; status: Evidence; note: string }[] {
  return Object.keys(ADAPTERS).sort().map((name) => ({
    name,
    status: COMPUTATIONAL_ADAPTERS[name] ? 'harness-computation' : REVIEWED_ADAPTERS[name] ? 'reviewed-conversion' : 'unreviewed-adapter',
    note: COMPUTATIONAL_ADAPTERS[name] ?? REVIEWED_ADAPTERS[name] ?? 'Review required; a passing result is not counted as verified public-API behavior.',
  }));
}
