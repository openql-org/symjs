// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, core/parameters.py, BSD-3-Clause; see LICENSE.

/**
 * @file The global parameters of automatic evaluation (SymPy `global_parameters`) and the scoped
 * switch `evaluate`. SymPy's context manager (`with evaluate(False): ...`) is a
 * function that runs a callback with the parameter set and restores it afterwards, also when the
 * callback throws: `evaluate(false, () => add(x, x))` is `x + x`. JavaScript runs one thread per
 * realm, so the parameters are module state (SymPy's are thread-local).
 */

interface Parameters {
  evaluate: boolean;
}

const state: Parameters = { evaluate: true };

/**
 * The current global parameters (SymPy `global_parameters`): `evaluate`, the automatic evaluation of
 * `Add`, `Mul` and `Pow`.
 */
export const globalParameters: Readonly<Parameters> = {
  get evaluate(): boolean {
    return state.evaluate;
  },
};

/**
 * Runs `fn` with automatic evaluation switched on or off (SymPy's context manager
 * `with evaluate(flag): ...`): with `false`, `add`, `mul` and `pow` build their arguments as given
 * (`x + x` stays `x + x`). The previous setting is restored when `fn` returns or throws.
 */
export function evaluate<T>(flag: boolean, fn: () => T): T {
  const old = state.evaluate;
  state.evaluate = flag;
  try {
    return fn();
  } finally {
    state.evaluate = old;
  }
}
