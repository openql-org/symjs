// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file A node class that can also be called like SymPy's class constructors
 * (`Derivative(f, x)`, `Piecewise([e, c], ...)`) while `instanceof` and the
 * static members keep working.
 */

/* eslint-disable @typescript-eslint/no-explicit-any */
export function callableClass<C extends abstract new (...args: any[]) => any, F extends (...args: any[]) => any>(cls: C, call: F): C & F {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the Proxy's apply trap makes the class callable as F; the type system cannot express a Proxy that adds a call signature
  return new Proxy(cls, { apply: (_target, _self, args) => call(...args) }) as C & F;
}
