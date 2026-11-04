// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Set nodes as the printers see them: sets/ is a higher layer, so the
 * printers recognize a set by its class name and order the arguments of a
 * Union or Intersection the way SymPy stores them.
 */

import type { Expr } from '../core/nodes';
import { Rational, Special, impl, isNum } from '../core/nodes';
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

/** The ellipsis in the elements a printer shows for a set or a sequence. */
export const DOTS = 'dots';

/**
 * The elements SymPy's printers show for a Range (`_print_Range` of the
 * LaTeX and pretty printers): all of them up to `most` elements (3 in
 * LaTeX, 4 in the pretty form), else the first two, an ellipsis and the
 * last one; an infinite end becomes an ellipsis. (A Range here has integer
 * or infinite start and stop and a stop that is the first value not taken.)
 */
export function rangePrintset(e: Expr, most: number): (Expr | typeof DOTS)[] {
  const [start, stop, step] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
  const int = (x: Expr): bigint => (x instanceof Rational ? x.p : 0n);
  const [a, b, d] = [int(start), int(stop), int(step)];
  const num = (v: bigint) => Rational.of(v);
  if (start instanceof Special && stop instanceof Special) return d > 0n ? [DOTS, num(-1n), num(0n), num(1n), DOTS] : [DOTS, num(1n), num(0n), num(-1n), DOTS];
  if (start instanceof Special) return [DOTS, num(b - 2n * d), num(b - d)];
  if (stop instanceof Special) return [start, num(a + d), DOTS];
  const size = (b - a) / d;
  if (size <= BigInt(most)) return Array.from({ length: Number(size) }, (_, k) => num(a + BigInt(k) * d));
  return [start, num(a + d), DOTS, num(b - d)];
}
