// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file A node class that can also be called like SymPy's class constructors
 * (`Derivative(f, x)`, `Piecewise([e, c], ...)`) while `instanceof` and the
 * static members keep working.
 */

/** The class behind each callable class, so that static members called through it find their class. */
const classes = new WeakMap<object, object>();

/** The class itself for a callable class made by callableClass, otherwise the value as it is. */
export function classOf<T extends object>(c: T): T {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the map only holds the class a callable class wraps, which has the callable class's type
  return (classes.get(c) as T | undefined) ?? c;
}

/* eslint-disable @typescript-eslint/no-explicit-any */
export function callableClass<C extends abstract new (...args: any[]) => any, F extends (...args: any[]) => any>(cls: C, call: F): C & F {
  const callable = new Proxy(cls, { apply: (_target, _self, args) => call(...args) });
  classes.set(callable, cls);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the Proxy's apply trap makes the class callable as F; the type system cannot express a Proxy that adds a call signature
  return callable as C & F;
}
