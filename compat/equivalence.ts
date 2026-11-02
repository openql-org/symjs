// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Mathematical equivalence of a symjs result and SymPy's printed result.
 *
 * Both strings are read back as values (expressions, lists, tuples, sets,
 * dicts, matrices). Expressions are equivalent when they agree at random
 * points (or simplify(a - b) == 0); collections are compared element-wise
 * (lists and sets without regard to order). A result that is still
 * unevaluated (Integral, Limit, Sum, ...) where SymPy computed a value is
 * never equivalent: "cannot compute" is not the same capability.
 */

import * as sj from '../packages/symjs/src';
import { Expr } from '../packages/symjs/src';

type V =
  | { t: 'expr'; e: Expr }
  | { t: 'list' | 'tuple' | 'set'; items: V[] }
  | { t: 'dict'; entries: [V, V][] }
  | { t: 'matrix'; rows: V[][] }
  | { t: 'raw'; s: string };

/** Split at top-level commas (outside brackets and quotes). */
function splitTop(s: string, sep = ','): string[] {
  const out: string[] = [];
  let depth = 0;
  let cur = '';
  let quote = '';
  for (const ch of s) {
    if (quote) {
      cur += ch;
      if (ch === quote) quote = '';
      continue;
    }
    if (ch === "'" || ch === '"') quote = ch;
    if ('([{'.includes(ch)) depth++;
    if (')]}'.includes(ch)) depth--;
    if (ch === sep && depth === 0) {
      out.push(cur);
      cur = '';
    } else cur += ch;
  }
  if (cur.trim()) out.push(cur);
  return out.map((x) => x.trim());
}

const enclosed = (s: string, open: string, close: string) => {
  if (!s.startsWith(open) || !s.endsWith(close)) return false;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if ('([{'.includes(s[i]!)) depth++;
    if (')]}'.includes(s[i]!)) depth--;
    if (depth === 0 && i < s.length - 1) return false;
  }
  return true;
};

/** Symbols of the case (with their assumptions), used when reading the printed values. */
let symbolTable: Record<string, Expr> = {};

function parseValue(s0: string): V {
  const s = s0.trim();
  if (s === 'True' || s === 'False' || s === 'None' || s === 'set()' || s === 'EmptySet') return { t: 'raw', s };
  if (enclosed(s, '[', ']')) return { t: 'list', items: splitTop(s.slice(1, -1)).map(parseValue) };
  if (enclosed(s, '{', '}')) {
    const parts = splitTop(s.slice(1, -1));
    if (parts.length && parts.every((p) => splitTop(p, ':').length === 2)) {
      return { t: 'dict', entries: parts.map((p) => splitTop(p, ':').map(parseValue) as [V, V]) };
    }
    return { t: 'set', items: parts.map(parseValue) };
  }
  if (enclosed(s, '(', ')')) {
    const parts = splitTop(s.slice(1, -1));
    if (parts.length > 1 || s.slice(1, -1).trim().endsWith(',')) return { t: 'tuple', items: parts.map(parseValue) };
  }
  if (s.startsWith('Matrix(') && enclosed(s.slice(6), '(', ')')) {
    const inner = parseValue(s.slice(7, -1));
    if (inner.t === 'list' && inner.items.every((r) => r.t === 'list')) {
      return { t: 'matrix', rows: inner.items.map((r) => (r as { items: V[] }).items) };
    }
  }
  try {
    return { t: 'expr', e: sj.parse(s, { symbols: symbolTable }) };
  } catch {
    return { t: 'raw', s };
  }
}

const UNEVALUATED = ['Integral', 'Limit', 'Sum', 'Product', 'Derivative', 'Subs', 'RootSum'];

function hasUnevaluated(s: string): Set<string> {
  return new Set(UNEVALUATED.filter((n) => s.includes(`${n}(`)));
}

/**
 * Test values respecting the assumptions: integers for integer symbols,
 * positive/negative/real numbers for such symbols and complex numbers
 * otherwise (so that e.g. Abs(x) and x are told apart).
 */
function trialValue(s: sj.Sym, k: number): Expr {
  const a = s.assumptions;
  const pick = <T>(xs: T[]) => xs[(k + s.name.length) % xs.length]!;
  if (a.integer) {
    if (a.positive) return sj.Rational.of(pick([2, 3, 5, 7]));
    if (a.negative) return sj.Rational.of(pick([-2, -3, -5, -7]));
    if (a.nonnegative) return sj.Rational.of(pick([0, 2, 3, 5]));
    return sj.Rational.of(pick([2, -3, 5, -1]));
  }
  if (a.positive || a.nonnegative) return sj.float(pick([0.71, 1.93, 0.37, 2.41]));
  if (a.negative || a.nonpositive) return sj.float(pick([-0.71, -1.93, -0.37, -2.41]));
  if (a.real) return sj.float(pick([0.71, -1.29, 2.17, -0.43]));
  const [re, im] = pick([[0.71, 0.33], [-1.29, 0.47], [0.53, -0.81], [-0.37, -0.29]]);
  return sj.add(sj.float(re), sj.mul(sj.float(im), sj.I));
}

function numericValue(e: Expr, k: number): sj.ComplexValue | undefined {
  try {
    const rep = [...sj.freeSymbols(e)].map((s) => [s, trialValue(s, k)] as [Expr, Expr]);
    const v = sj.evalf(sj.xreplace(e, rep), 20);
    const c = v.toComplex();
    if (!Number.isFinite(c.re) || !Number.isFinite(c.im)) return undefined;
    return c;
  } catch {
    return undefined;
  }
}

function exprEquivalent(a: Expr, b: Expr): boolean {
  if (a.key === b.key) return true;
  let agree = 0;
  for (let k = 0; k < 4; k++) {
    const x = numericValue(a, k);
    const y = numericValue(b, k);
    if (!x || !y) continue;
    const scale = Math.max(1, Math.hypot(x.re, x.im), Math.hypot(y.re, y.im));
    if (Math.hypot(x.re - y.re, x.im - y.im) > 1e-9 * scale) return false;
    agree++;
  }
  if (agree >= 2) return true;
  try {
    const d = sj.simplify(sj.add(a, sj.mul(-1, b)));
    return d instanceof sj.Rational && d.isZero;
  } catch {
    return false;
  }
}

function valueEquivalent(a: V, b: V): boolean {
  if (a.t === 'raw' || b.t === 'raw') return a.t === 'raw' && b.t === 'raw' && a.s === b.s;
  if (a.t === 'expr' && b.t === 'expr') {
    if (a.e instanceof sj.Rel && b.e instanceof sj.Rel) {
      if (a.e.op !== b.e.op) return false;
      return (
        (exprEquivalent(a.e.lhs, b.e.lhs) && exprEquivalent(a.e.rhs, b.e.rhs)) ||
        exprEquivalent(sj.add(a.e.lhs, sj.mul(-1, a.e.rhs)), sj.add(b.e.lhs, sj.mul(-1, b.e.rhs)))
      );
    }
    return exprEquivalent(a.e, b.e);
  }
  if (a.t === 'matrix' && b.t === 'matrix') {
    return a.rows.length === b.rows.length && a.rows.every((r, i) => r.length === b.rows[i]!.length && r.every((v, j) => valueEquivalent(v, b.rows[i]![j]!)));
  }
  if (a.t === 'tuple' && b.t === 'tuple') return a.items.length === b.items.length && a.items.every((v, i) => valueEquivalent(v, b.items[i]!));
  if ((a.t === 'list' || a.t === 'set') && a.t === b.t) return unorderedEquivalent(a.items, b.items);
  if (a.t === 'dict' && b.t === 'dict') {
    if (a.entries.length !== b.entries.length) return false;
    return a.entries.every(([k, v]) => b.entries.some(([k2, v2]) => valueEquivalent(k, k2) && valueEquivalent(v, v2)));
  }
  return false;
}

function unorderedEquivalent(xs: V[], ys: V[]): boolean {
  if (xs.length !== ys.length) return false;
  const used = new Set<number>();
  for (const x of xs) {
    const j = ys.findIndex((y, i) => !used.has(i) && valueEquivalent(x, y));
    if (j < 0) return false;
    used.add(j);
  }
  return true;
}

/** Is the symjs result (printed) mathematically the same as SymPy's printed result? */
/**
 * Functions whose capability is the form of the result (simplification and
 * rewriting): an equal value is not enough, the result must have been
 * transformed (not the input returned unchanged) and be no more complex
 * than SymPy's.
 */
const FORM_FUNCTIONS = new Set([
  'simplify', 'trigsimp', 'nsimplify', 'sqrtdenest', 'radsimp', 'ratsimp', 'factor', 'cancel', 'collect', 'rcollect',
  'together', 'apart', 'expand', 'expand_mul', 'expand_log', 'expand_power_exp', 'expand_power_base', 'expand_trig',
  'expand_complex', 'expand_multinomial', 'expand_func', 'powsimp', 'powdenest', 'logcombine', 'factor_terms', 'gcd_terms',
  'besselsimp', 'exptrigsimp', 'combsimp', 'gammasimp', 'hyperexpand', 'horner', 'signsimp', 'separatevars',
  '.simplify', '.expand', '.factor', '.cancel', '.together', '.apart', '.trigsimp', '.rewrite', '.powsimp', '.radsimp', '.nsimplify',
]);

export type EquivalenceOptions = { fn?: string; input?: string };

export function equivalent(got: string, expected: string, symbols: readonly sj.Sym[] = [], opts: EquivalenceOptions = {}): boolean {
  if (got === expected) return true;
  if (opts.fn && FORM_FUNCTIONS.has(opts.fn)) {
    if (opts.input !== undefined && got === opts.input) return false;
    try {
      symbolTable = Object.fromEntries(symbols.filter((s) => !(s instanceof sj.Dummy)).map((s) => [s.name, s]));
      const g = parseValue(got);
      const e = parseValue(expected);
      if (g.t === 'expr' && e.t === 'expr' && sj.countOps(g.e) > sj.countOps(e.e)) return false;
    } catch {
      return false;
    }
  }
  symbolTable = Object.fromEntries(symbols.filter((s) => !(s instanceof sj.Dummy)).map((s) => [s.name, s]));
  // an unevaluated object where SymPy has a value (or the other way round) is a different capability
  const ug = hasUnevaluated(got);
  const ue = hasUnevaluated(expected);
  if ([...ug].some((n) => !ue.has(n))) return false;
  // printed object addresses and other non-values cannot be compared
  if (expected.includes(' object at 0x')) return false;
  try {
    return valueEquivalent(parseValue(got), parseValue(expected));
  } catch {
    return false;
  }
}
