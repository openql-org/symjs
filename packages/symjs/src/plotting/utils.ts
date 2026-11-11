// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/utils.py (BSD-3-Clause).
import { Expr, Sym, Dummy } from '../core/nodes';
import { freeSymbols, subs } from '../core/traverse';
import { cast } from '../core/guard';
import { sympify } from '../core/ops';
import { ImageSet, SetExpr, finiteSet, Integers, Naturals, Naturals0 } from '../sets/sets';
import type { PlotExpression, PlotParameters, PlotRange } from './series';
/** Free symbols in deterministic name order, excluding numeric callbacks. */
export function getFreeSymbols(expressions: readonly PlotExpression[]): Sym[] {
  const symbols = new Map<string, Sym>();
  for (const e of expressions) if (typeof e !== 'function') for (const s of freeSymbols(sympify(e))) symbols.set(s.key, cast(s, Sym));
  return [...symbols.values()].sort((a, b) => a.name.localeCompare(b.name));
}
/** Complete omitted ranges with [-10, 10], validating variables and parameters. */
export function createRanges(expressions: readonly PlotExpression[], ranges: readonly PlotRange[], npar: number, params: PlotParameters = new Map()): PlotRange[] {
  const free = getFreeSymbols(expressions).filter((s) => ![...params.keys()].some((p) => p.equals(s)));
  if (free.length > npar || ranges.length > npar) throw new RangeError('Too many free symbols or plotting ranges.');
  const result = [...ranges], names = new Set(ranges.map((r) => r[0].key));
  if (names.size !== ranges.length) throw new RangeError('Multiple ranges with the same symbol.');
  for (const s of free) if (!names.has(s.key)) { if (result.length === npar) throw new RangeError('Expression symbols do not match plotting ranges.'); result.push([s, -10, 10]); names.add(s.key); }
  while (result.length < npar) result.push([new Dummy('x'), -10, 10]);
  return result;
}
/** Replace integer ImageSets by finite prefixes for exclusion-point sampling. */
export function extractSolution(solution: SetExpr, n = 10): SetExpr {
  if (!Number.isInteger(n) || n < 0) throw new RangeError('Sample count must be a nonnegative integer.');
  const images: ImageSet[] = [];
  const visit = (e: Expr): void => { if (e instanceof ImageSet) images.push(e); else e.args.forEach(visit); };
  visit(solution);
  let result: Expr = solution;
  for (const image of images) {
    if (![Integers, Naturals, Naturals0].some((s) => s.equals(image.base))) throw new TypeError('Only integer ImageSet domains can be enumerated.');
    const values = Array.from({ length: n }, (_, i) => image.base.equals(Integers) ? (i % 2 ? (i + 1) / 2 : -i / 2) : i + (image.base.equals(Naturals) ? 1 : 0));
    result = subs(result, new Map([[image, finiteSet(...values.map((v) => subs(image.expr, new Map([[image.variable, sympify(v)]]))))]]));
  }
  return cast(result, SetExpr);
}
/** Range guard for the plot factories. */
export function isPlotRange(value: unknown): value is PlotRange {
  return Array.isArray(value) && value.length === 3 && value[0] instanceof Sym && value.slice(1).every((v) => v instanceof Expr ? !v.has(value[0]) : typeof v === 'number' || typeof v === 'bigint' || typeof v === 'object' && v !== null && 're' in v && 'im' in v);
}
