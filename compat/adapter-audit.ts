// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { ADAPTERS, type Case } from './harness';
import { PORTS } from './ports';

/** A passing adapter is not automatically evidence of a public implementation. */
export const REVIEWED_ADAPTERS: Readonly<Record<string, string>> = {
  nonlinsolve: 'nonlinsolve',
  substitution: 'substitution',
  checksol: 'checksol',
  linsolve: 'linsolve / linsolveAugmented / gaussJordanSolve',
  solve_linear_system: 'linsolveAugmented',
  solve_linear_system_LU: 'linsolveAugmented',
  solve_poly_system: 'solvePolySystem',
  solve_undetermined_coeffs: 'solveUndeterminedCoeffs',
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
