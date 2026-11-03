// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Set nodes as the printers see them: sets/ is a higher layer, so the
 * printers recognize a set by its class name and order the arguments of a
 * Union or Intersection the way SymPy stores them.
 */

import type { Expr } from '../core/nodes';
import { Special, impl, isNum } from '../core/nodes';
import { at } from '../core/guard';
import { ordered } from '../core/match';

/** Shape of SymPy sets (sets/ is a higher layer): the class name and the arguments. */
interface SetLike {
  readonly kind: 'Set';
  readonly className: string;
  readonly args: readonly Expr[];
}
const isSetLike = (e: Expr): e is Expr & SetLike => e.kind === 'Set' && 'className' in e && typeof e.className === 'string';
export const setClass = (e: Expr): string | undefined => (isSetLike(e) ? e.className : undefined);

/** A real number as a JS number, or undefined when it is not a comparable number. */
function realNumber(e: Expr): number | undefined {
  if (e instanceof Special) return e.name === 'oo' ? Infinity : e.name === '-oo' ? -Infinity : undefined;
  if (isNum(e)) return e.value;
  if (impl.freeSymbols(e).size > 0) return undefined;
  try {
    const v = impl.toComplex(e);
    return v.im === 0 ? v.re : undefined;
  } catch {
    return undefined;
  }
}

const allDefined = <T>(xs: readonly (T | undefined)[]): xs is T[] => xs.every((v) => v !== undefined);

/** SymPy `Set.inf` of the sets the printer knows, or undefined when unknown. */
function setInfimum(e: Expr): number | undefined {
  switch (setClass(e)) {
    case 'Interval':
      return realNumber(at(e.args, 0));
    case 'FiniteSet': {
      const vs = e.args.map(realNumber);
      return allDefined(vs) ? Math.min(...vs) : undefined;
    }
    case 'Union': {
      const vs = e.args.map(setInfimum);
      return allDefined(vs) ? Math.min(...vs) : undefined;
    }
    case 'Reals':
    case 'Integers':
      return -Infinity;
    case 'Naturals':
      return 1;
    case 'Naturals0':
      return 0;
    default:
      return undefined;
  }
}

/**
 * The arguments of a Union or Intersection in SymPy's order: SymPy sorts
 * them by infimum (`ordered(args, Set._infimum_key)`; an unknown infimum
 * counts as oo), then like `ordered` by the node count and the default sort
 * key.
 */
export function setArgsOrdered(args: readonly Expr[]): Expr[] {
  // a stable sort by infimum of the ordered arguments
  const keyed = ordered(args).map((a) => [setInfimum(a) ?? Infinity, a] as const);
  return keyed.sort((p, q) => (p[0] < q[0] ? -1 : p[0] > q[0] ? 1 : 0)).map(([, a]) => a);
}
