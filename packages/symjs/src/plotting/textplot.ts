// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/textplot.py (BSD-3-Clause).
import type { ExprLike } from '../core/nodes';
import { sympify } from '../core/ops';
import { Dummy, S } from '../core/nodes';
import { at, first, last } from '../core/guard';
import { getFreeSymbols } from './utils';
import { LineOver1DRangeSeries, discretize } from './series';
function rounded(v: number): number { const f = Math.floor(v), remainder = v - f; return remainder === 0.5 ? f % 2 === 0 ? f : f + 1 : Math.round(v); }
function general(v: number): string { if (v === 0) return '0'; return Number(v.toPrecision(6)).toString(); }
/** Lines of SymPy's plain-text plot; consumes no display or terminal backend. */
export function* textplotStr(expr: ExprLike, a: number, b: number, W = 55, H = 21): IterableIterator<string> {
  if (!Number.isInteger(W) || !Number.isInteger(H) || W < 2 || H < 2) throw new RangeError('Text plot dimensions must be integers of at least two.');
  const free = getFreeSymbols([expr]); if (free.length > 1) throw new RangeError('Text plots require at most one variable.');
  const series = new LineOver1DRangeSeries(expr, [free[0] ?? new Dummy('x'), a, b], '', { n: W });
  const data = series.getData(), xs = at(data, 0), values = at(data, 1);
  // The textplot reference rejects complex-typed results even when their imaginary component vanishes.
  const x = xs, y = sympify(expr).has(S.I) ? values.map(() => NaN) : values, finite = y.filter(Number.isFinite);
  let mi = finite.length ? Math.min(...finite) : -1, ma = finite.length ? Math.max(...finite) : 1;
  if (ma === mi) { if (ma) { mi = Math.min(0, 2 * ma); ma = Math.max(0, 2 * ma); } else { mi = -1; ma = 1; } }
  const factor = 10 ** (1 - Math.floor(Math.log10(ma - mi))); mi = rounded(mi * factor) / factor; ma = rounded(ma * factor) / factor;
  const bins = discretize(mi, ma, H), samples = y.map((v) => Number.isFinite(v) ? rounded((v - mi) / (ma - mi) * (H - 1)) : NaN);
  for (let h = H - 1; h >= 0; h--) {
    const line = Array<string>(W).fill(' ');
    for (let i = 0; i < W; i++) if (at(samples, i) === h) line[i] = (i === 0 || at(samples, i - 1) === h - 1) && (i === W - 1 || at(samples, i + 1) === h + 1) ? '/' : (i === 0 || at(samples, i - 1) === h + 1) && (i === W - 1 || at(samples, i + 1) === h - 1) ? '\\' : '.';
    if (h === 0) line.fill('_');
    const prefix = h === 0 || h === Math.floor(H / 2) || h === H - 1 ? general(at(bins, h)).padStart(7).slice(0, 7) : ' '.repeat(7);
    yield prefix + ' |' + (h === Math.floor(H / 2) ? line.join('').replaceAll(' ', '-') : line.join(''));
  }
  yield ' '.repeat(9) + general(first(x)).padEnd(Math.floor(W / 2)) + general(at(x, Math.floor(W / 2))).padEnd(Math.floor(W / 2) - (W % 2 ? 0 : 1)) + general(last(x));
}
/** Return the text that SymPy prints, including its final newline. */
export function textplot(expr: ExprLike, a: number, b: number, W = 55, H = 21): string { return [...textplotStr(expr, a, b, W, H)].join('\n') + '\n'; }
