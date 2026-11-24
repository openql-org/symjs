// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/intervalmath (BSD-3-Clause).
import type { IntervalLike } from './interval_arithmetic';
import { interval, asInterval, whole } from './interval_arithmetic';
import { intervalMembership } from './interval_membership';
import type { Truth } from '../../core/truth';
import { truthOr } from '../../core/truth';
const monotone = (x: IntervalLike, f: (x: number) => number): interval => { const i = asInterval(x); return new interval(f(i.start), f(i.end), { isValid: i.isValid }); };
const domain = (x: IntervalLike, f: (x: number) => number, lo: number, hi: number, open = false): interval => {
  const i = asInterval(x);
  if (i.isValid === false || (open ? i.end <= lo || i.start >= hi : i.end < lo || i.start > hi)) return whole(false);
  if (open ? i.start <= lo || i.end >= hi : i.start < lo || i.end > hi) return whole('unknown');
  return monotone(i, f);
};
export const Abs = (x: IntervalLike): interval => { const i = asInterval(x); return new interval(i.contains(0) ? 0 : Math.min(Math.abs(i.start), Math.abs(i.end)), Math.max(Math.abs(i.start), Math.abs(i.end)), { isValid: i.isValid }); };
export const exp = (x: IntervalLike): interval => monotone(x, Math.exp);
export const log = (x: IntervalLike): interval => domain(x, Math.log, 0, Infinity, true);
export const log10 = (x: IntervalLike): interval => domain(x, Math.log10, 0, Infinity, true);
export const atan = (x: IntervalLike): interval => monotone(x, Math.atan);
function periodic(x: IntervalLike, cosine: boolean): interval {
  const i = asInterval(x), f = cosine ? Math.cos : Math.sin;
  if (!Number.isFinite(i.width) || i.width >= 2 * Math.PI) return new interval(-1, 1, { isValid: i.isValid });
  let low = Math.min(f(i.start), f(i.end)), high = Math.max(f(i.start), f(i.end));
  const offset = cosine ? 0 : Math.PI / 2;
  if (Math.ceil((i.start - offset) / (2 * Math.PI)) <= Math.floor((i.end - offset) / (2 * Math.PI))) high = 1;
  if (Math.ceil((i.start - offset - Math.PI) / (2 * Math.PI)) <= Math.floor((i.end - offset - Math.PI) / (2 * Math.PI))) low = -1;
  return new interval(low, high, { isValid: i.isValid });
}
export const sin = (x: IntervalLike): interval => periodic(x, false);
/** Scalar cos computes cosine; SymPy 1.14 incorrectly calls sine for scalar inputs. */
export const cos = (x: IntervalLike): interval => periodic(x, true);
export const tan = (x: IntervalLike): interval => sin(x).div(cos(x));
/**
 * Computes the interval square root on the nonnegative real axis, including zero.
 *
 * @see SymPy `sympy.plotting.intervalmath.lib_interval.sqrt`
 */
export const sqrt = (x: IntervalLike): interval => domain(x, Math.sqrt, 0, Infinity);
export const sinh = (x: IntervalLike): interval => monotone(x, Math.sinh);
export const cosh = (x: IntervalLike): interval => { const i = asInterval(x); return new interval(i.contains(0) ? 1 : Math.min(Math.cosh(i.start), Math.cosh(i.end)), Math.max(Math.cosh(i.start), Math.cosh(i.end)), { isValid: i.isValid }); };
export const tanh = (x: IntervalLike): interval => monotone(x, Math.tanh);
export const asin = (x: IntervalLike): interval => domain(x, Math.asin, -1, 1);
export const acos = (x: IntervalLike): interval => domain(x, Math.acos, -1, 1);
export const asinh = (x: IntervalLike): interval => monotone(x, Math.asinh);
export const acosh = (x: IntervalLike): interval => domain(x, Math.acosh, 1, Infinity);
export const atanh = (x: IntervalLike): interval => domain(x, Math.atanh, -1, 1, true);
function discrete(x: IntervalLike, f: (x: number) => number): interval { const i = asInterval(x); if (i.isValid === false) return whole(false); const a = f(i.start), b = f(i.end); return new interval(a, b, { isValid: a === b ? i.isValid : 'unknown' }); }
export const ceil = (x: IntervalLike): interval => discrete(x, Math.ceil);
export const floor = (x: IntervalLike): interval => discrete(x, Math.floor);
function extremum(args: readonly IntervalLike[], f: (...xs: number[]) => number): interval {
  if (!args.length) throw new RangeError('At least one interval is required.');
  const all = args.map(asInterval), valid = all.filter((i) => i.isValid === true);
  if (!valid.length) return whole(all.every((i) => i.isValid === false) ? false : 'unknown');
  return new interval(f(...valid.map((i) => i.start)), f(...valid.map((i) => i.end)));
}
export const imin = (...args: IntervalLike[]): interval => extremum(args, Math.min);
export const imax = (...args: IntervalLike[]): interval => extremum(args, Math.max);
type Predicate = intervalMembership | readonly [Truth, Truth];
const predicate = (v: Predicate): intervalMembership => v instanceof intervalMembership ? v : new intervalMembership(v[0], v[1]);
export const And = (...args: Predicate[]): intervalMembership => args.map(predicate).reduce((a, b) => a.and(b), new intervalMembership(true, true));
export const Or = (...args: Predicate[]): intervalMembership => args.map(predicate).reduce((a, b) => new intervalMembership(truthOr(a.value, b.value), truthOr(a.isValid, b.isValid)), new intervalMembership(false, false));
