// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sets of numbers (SymPy sets): Interval, FiniteSet, Union,
 * Intersection, Complement, EmptySet and the standard sets Reals,
 * Integers, Naturals, Naturals0 and Complexes. Set operations simplify
 * for real intervals and finite sets with comparable elements.
 */

import { NotImplementedError } from '../core/errors';
import { Expr, ExprLike, Float, Rational, S, Special, impl } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { Eq, Le, Lt } from '../core/logic';
import { and, or } from '../core/boolalg';
import { compareKeys, sortKey } from '../printing/sortkey';

/** Base class of all sets. */
export abstract class SetExpr extends Expr {
  readonly kind = 'Set' as const;
  abstract get className(): string;
  get isEmpty(): boolean {
    return false;
  }
}

const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
const isInf = (e: Expr) => isOo(e) || isNegOo(e);

/** Real value for ordering, or undefined when it cannot be decided. */
export function realValue(e: Expr): number | undefined {
  if (isOo(e)) return Infinity;
  if (isNegOo(e)) return -Infinity;
  if (e instanceof Rational || e instanceof Float) return e.value;
  if (e.freeSymbols().size) return undefined;
  try {
    const v = impl.toComplex(e);
    return Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re)) ? undefined : v.re;
  } catch {
    return undefined;
  }
}

/** Compare two real numbers: -1, 0, 1, or undefined when unknown. */
export function cmpReal(a: Expr, b: Expr): number | undefined {
  if (a.key === b.key) return 0;
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    return d < 0n ? -1 : d > 0n ? 1 : 0;
  }
  const x = realValue(a);
  const y = realValue(b);
  if (x === undefined || y === undefined) return undefined;
  if (x === y) {
    const d = add(a, mul(-1, b));
    if (d instanceof Rational) return d.isZero ? 0 : d.isNegative ? -1 : 1;
    return Math.abs(x) === Infinity ? 0 : 0;
  }
  return x < y ? -1 : 1;
}

// ---------------------------------------------------------------------------
// Standard sets
// ---------------------------------------------------------------------------

class NamedSet extends SetExpr {
  readonly args: readonly Expr[] = [];
  constructor(readonly name: 'Reals' | 'Integers' | 'Naturals' | 'Naturals0' | 'Complexes' | 'EmptySet' | 'UniversalSet') {
    super();
  }
  get className(): string {
    return this.name;
  }
  get isEmpty(): boolean {
    return this.name === 'EmptySet';
  }
  protected computeKey(): string {
    return `%${this.name}`;
  }
  printStr(): string {
    return this.name;
  }
}

export const EmptySet = new NamedSet('EmptySet');
export const Reals = new NamedSet('Reals');
export const Integers = new NamedSet('Integers');
export const Naturals = new NamedSet('Naturals');
export const Naturals0 = new NamedSet('Naturals0');
export const Complexes = new NamedSet('Complexes');
export const UniversalSet = new NamedSet('UniversalSet');

// ---------------------------------------------------------------------------
// Interval
// ---------------------------------------------------------------------------

export class Interval extends SetExpr {
  readonly args: readonly Expr[];
  /** SymPy `Interval(a, b, left_open, right_open)` (EmptySet or a point when degenerate). */
  static of(a: ExprLike, b: ExprLike, leftOpen = false, rightOpen = false): SetExpr {
    return interval(a, b, leftOpen, rightOpen);
  }
  /** SymPy `Interval.open(a, b)`. */
  static open(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, true, true);
  }
  /** SymPy `Interval.Lopen(a, b)`: open on the left. */
  static Lopen(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, true, false);
  }
  /** SymPy `Interval.Ropen(a, b)`: open on the right. */
  static Ropen(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, false, true);
  }
  /** @internal use Interval.of() */
  constructor(
    readonly start: Expr,
    readonly end: Expr,
    readonly leftOpen: boolean,
    readonly rightOpen: boolean,
  ) {
    super();
    this.args = [start, end, leftOpen ? S.true : S.false, rightOpen ? S.true : S.false];
  }
  get className(): string {
    return 'Interval';
  }
  protected computeKey(): string {
    return `Interval(${this.start.key},${this.end.key},${this.leftOpen},${this.rightOpen})`;
  }
  printStr(p: (e: Expr) => string): string {
    const a = this.start;
    const b = this.end;
    const l = this.leftOpen;
    const r = this.rightOpen;
    let m: string;
    if (isInf(a) && isInf(b)) m = '';
    else if (isInf(a) && !r) m = '';
    else if (isInf(b) && !l) m = '';
    else if (!l && !r) m = '';
    else if (l && r) m = '.open';
    else if (l) m = '.Lopen';
    else m = '.Ropen';
    return `Interval${m}(${p(a)}, ${p(b)})`;
  }
}

/** Interval(a, b) with open ends; empty or degenerate intervals simplify. */
export function interval(aIn: ExprLike, bIn: ExprLike, leftOpen = false, rightOpen = false): SetExpr {
  const a = sympify(aIn);
  const b = sympify(bIn);
  const c = cmpReal(a, b);
  if (c === 1) return EmptySet;
  if (c === 0) {
    if (leftOpen || rightOpen) return EmptySet;
    if (isInf(a)) return EmptySet;
    return finiteSet(a);
  }
  if (isNegOo(a)) leftOpen = true;
  if (isOo(b)) rightOpen = true;
  if (isNegOo(a) && isOo(b)) return Reals;
  return new Interval(a, b, leftOpen, rightOpen);
}

export const openInterval = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, true, true);
export const Lopen = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, true, false);
export const Ropen = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, false, true);

// ---------------------------------------------------------------------------
// FiniteSet
// ---------------------------------------------------------------------------

export class FiniteSet extends SetExpr {
  readonly args: readonly Expr[];
  /** SymPy `FiniteSet(*elements)` (EmptySet when empty, duplicates removed). */
  static of(...xs: ExprLike[]): SetExpr {
    return finiteSet(...xs);
  }
  /** @internal use FiniteSet.of() */
  constructor(elems: readonly Expr[]) {
    super();
    this.args = [...elems].sort((x, y) => compareKeys(sortKey(x), sortKey(y)));
  }
  get className(): string {
    return 'FiniteSet';
  }
  protected computeKey(): string {
    return `{${this.args.map((a) => a.key).join(',')}}`;
  }
  printStr(p: (e: Expr) => string): string {
    return `{${this.args.map(p).join(', ')}}`;
  }
}

export function finiteSet(...xs: ExprLike[]): SetExpr {
  const m = new Map<string, Expr>();
  for (const x of xs.map(sympify)) m.set(x.key, x);
  return m.size ? new FiniteSet([...m.values()]) : EmptySet;
}

// ---------------------------------------------------------------------------
// ImageSet / ConditionSet
// ---------------------------------------------------------------------------

/** { expr(v) : v in base } (SymPy ImageSet(Lambda(v, expr), base)). */
export class ImageSet extends SetExpr {
  readonly args: readonly Expr[];
  constructor(
    readonly variable: Expr,
    readonly expr: Expr,
    readonly base: SetExpr,
  ) {
    super();
    this.args = [variable, expr, base];
  }
  get className(): string {
    return 'ImageSet';
  }
  protected computeKey(): string {
    return `ImageSet(${this.variable.key},${this.expr.key},${this.base.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ImageSet(Lambda(${p(this.variable)}, ${p(this.expr)}), ${p(this.base)})`;
  }
}

/** { v in base : condition } (SymPy ConditionSet). */
export class ConditionSet extends SetExpr {
  readonly args: readonly Expr[];
  constructor(
    readonly variable: Expr,
    readonly condition: Expr,
    readonly base: SetExpr,
  ) {
    super();
    this.args = [variable, condition, base];
  }
  get className(): string {
    return 'ConditionSet';
  }
  protected computeKey(): string {
    return `ConditionSet(${this.variable.key},${this.condition.key},${this.base.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ConditionSet(${p(this.variable)}, ${p(this.condition)}, ${p(this.base)})`;
  }
}

/** ImageSet(Lambda(v, expr), base). */
export function imageSet(v: Expr, expr: ExprLike, base: SetExpr): SetExpr {
  return new ImageSet(v, sympify(expr), base);
}

// ---------------------------------------------------------------------------
// Union / Intersection / Complement
// ---------------------------------------------------------------------------

class SetOp extends SetExpr {
  constructor(
    readonly op: 'Union' | 'Intersection' | 'Complement',
    readonly args: readonly Expr[],
  ) {
    super();
  }
  get className(): string {
    return this.op;
  }
  protected computeKey(): string {
    return `${this.op}(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `${this.op}(${this.args.map(p).join(', ')})`;
  }
}
export { SetOp };

const sortSets = (xs: SetExpr[]): SetExpr[] => [...xs].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

/** Does the set contain x? true/false, or undefined when undecidable. */
export function containsQ(s: SetExpr, x: Expr): boolean | undefined {
  if (s === EmptySet) return false;
  if (s === Reals) {
    if (isInf(x)) return false;
    const v = realValue(x);
    return v === undefined ? (impl.isReal?.(x) ?? undefined) : true;
  }
  if (s === Complexes) return !isInf(x);
  if (s === Integers || s === Naturals || s === Naturals0) {
    if (x instanceof Rational) return x.isInteger && (s === Integers || (s === Naturals ? x.p > 0n : x.p >= 0n));
    return undefined;
  }
  if (s instanceof FiniteSet) {
    if (s.args.some((a) => a.key === x.key)) return true;
    const unknown = s.args.some((a) => cmpReal(a, x) === undefined);
    return unknown ? undefined : false;
  }
  if (s instanceof Interval) {
    if (isInf(x)) return false;
    const lo = cmpReal(s.start, x);
    const hi = cmpReal(x, s.end);
    if (lo === undefined || hi === undefined) return undefined;
    const okLo = s.leftOpen ? lo < 0 : lo <= 0;
    const okHi = s.rightOpen ? hi < 0 : hi <= 0;
    return okLo && okHi;
  }
  if (s instanceof SetOp) {
    const parts = s.args.map((a) => containsQ(a as SetExpr, x));
    if (s.op === 'Union') return parts.some((v) => v === true) ? true : parts.every((v) => v === false) ? false : undefined;
    if (s.op === 'Intersection') return parts.every((v) => v === true) ? true : parts.some((v) => v === false) ? false : undefined;
    const [a, b] = parts;
    if (a === false || b === true) return false;
    if (a === true && b === false) return true;
    return undefined;
  }
  return undefined;
}

/** SymPy Set.contains: True/False or an unevaluated condition. */
export function contains(s: SetExpr, x: Expr): Expr {
  const v = containsQ(s, x);
  if (v !== undefined) return v ? S.true : S.false;
  if (s instanceof Interval) {
    return and(s.leftOpen ? Lt(s.start, x) : Le(s.start, x), s.rightOpen ? Lt(x, s.end) : Le(x, s.end));
  }
  return S.false;
}

function intervalParts(s: SetExpr): Interval[] | undefined {
  if (s instanceof Interval) return [s];
  if (s === Reals) return [new Interval(S.NegativeInfinity, S.Infinity, true, true)];
  if (s === EmptySet) return [];
  if (s instanceof SetOp && s.op === 'Union' && s.args.every((a) => a instanceof Interval)) return s.args as Interval[];
  return undefined;
}

/** Union of sets, merging overlapping intervals and absorbing points. */
export function union(...sets0: SetExpr[]): SetExpr {
  const sets = sets0.flatMap((s) => (s instanceof SetOp && s.op === 'Union' ? (s.args as SetExpr[]) : [s])).filter((s) => s !== EmptySet);
  if (!sets.length) return EmptySet;
  if (sets.some((s) => s === Reals) && sets.every((s) => s === Reals || s instanceof Interval || (s instanceof FiniteSet && s.args.every((a) => containsQ(Reals, a) === true)))) return Reals;
  let ivs: Interval[] = [];
  const points: Expr[] = [];
  const others: SetExpr[] = [];
  for (const s of sets) {
    if (s instanceof Interval) ivs.push(s);
    else if (s === Reals) ivs.push(new Interval(S.NegativeInfinity, S.Infinity, true, true));
    else if (s instanceof FiniteSet) points.push(...s.args);
    else others.push(s);
  }
  // merge intervals
  ivs = mergeIntervals(ivs);
  // absorb points
  const rest: Expr[] = [];
  for (const pt of points) {
    let absorbed = false;
    ivs = ivs.map((iv) => {
      if (absorbed) return iv;
      if (containsQ(iv, pt) === true) {
        absorbed = true;
        return iv;
      }
      if (iv.leftOpen && cmpReal(iv.start, pt) === 0) {
        absorbed = true;
        return new Interval(iv.start, iv.end, false, iv.rightOpen);
      }
      if (iv.rightOpen && cmpReal(iv.end, pt) === 0) {
        absorbed = true;
        return new Interval(iv.start, iv.end, iv.leftOpen, false);
      }
      return iv;
    });
    if (!absorbed) rest.push(pt);
  }
  ivs = mergeIntervals(ivs);
  const out: SetExpr[] = ivs.map((iv) => (isNegOo(iv.start) && isOo(iv.end) ? Reals : iv));
  if (rest.length) out.push(finiteSet(...rest));
  out.push(...others);
  if (out.length === 1) return out[0]!;
  return new SetOp('Union', sortSets(out));
}

function mergeIntervals(ivs0: Interval[]): Interval[] {
  const ivs = [...ivs0];
  let changed = true;
  while (changed) {
    changed = false;
    outer: for (let i = 0; i < ivs.length; i++) {
      for (let j = i + 1; j < ivs.length; j++) {
        const m = mergeTwo(ivs[i]!, ivs[j]!);
        if (m) {
          ivs.splice(j, 1);
          ivs[i] = m;
          changed = true;
          break outer;
        }
      }
    }
  }
  return ivs;
}

function mergeTwo(a: Interval, b: Interval): Interval | undefined {
  // order so that a starts first
  const c = cmpReal(a.start, b.start);
  if (c === undefined) return undefined;
  if (c > 0 || (c === 0 && a.leftOpen && !b.leftOpen)) [a, b] = [b, a];
  // overlap or touch: b.start <= a.end
  const t = cmpReal(b.start, a.end);
  if (t === undefined) return undefined;
  if (t > 0) return undefined;
  if (t === 0 && a.rightOpen && b.leftOpen) return undefined;
  const e = cmpReal(a.end, b.end);
  if (e === undefined) return undefined;
  let end = a.end;
  let rightOpen = a.rightOpen;
  if (e < 0 || (e === 0 && a.rightOpen && !b.rightOpen)) {
    end = b.end;
    rightOpen = b.rightOpen;
  }
  const leftOpen = cmpReal(a.start, b.start) === 0 ? a.leftOpen && b.leftOpen : a.leftOpen;
  return new Interval(a.start, end, leftOpen, rightOpen);
}

/** Intersection of sets. */
export function intersection(...sets: SetExpr[]): SetExpr {
  if (sets.some((s) => s === EmptySet)) return EmptySet;
  let acc: SetExpr = sets[0]!;
  for (const s of sets.slice(1)) acc = intersectTwo(acc, s);
  return acc;
}

function intersectTwo(a: SetExpr, b: SetExpr): SetExpr {
  if (a === EmptySet || b === EmptySet) return EmptySet;
  if (a instanceof FiniteSet || b instanceof FiniteSet) {
    const [f, o] = a instanceof FiniteSet ? [a, b] : [b as FiniteSet, a];
    const keep: Expr[] = [];
    const unknown: Expr[] = [];
    for (const x of f.args) {
      const c = containsQ(o, x);
      if (c === true) keep.push(x);
      else if (c === undefined) unknown.push(x);
    }
    if (unknown.length) {
      const known = keep.length ? [finiteSet(...keep)] : [];
      return union(...known, new SetOp('Intersection', sortSets([finiteSet(...unknown), o])));
    }
    return finiteSet(...keep);
  }
  if (a === Reals && (b instanceof Interval || b === Reals)) return b;
  if (b === Reals && a instanceof Interval) return a;
  const pa = intervalParts(a);
  const pb = intervalParts(b);
  if (pa && pb) {
    const out: SetExpr[] = [];
    for (const x of pa) for (const y of pb) out.push(intersectIntervals(x, y));
    return union(...out);
  }
  if (a instanceof SetOp && a.op === 'Union') return union(...(a.args as SetExpr[]).map((s) => intersectTwo(s, b)));
  if (b instanceof SetOp && b.op === 'Union') return union(...(b.args as SetExpr[]).map((s) => intersectTwo(a, s)));
  return new SetOp('Intersection', sortSets([a, b]));
}

function intersectIntervals(a: Interval, b: Interval): SetExpr {
  const cs = cmpReal(a.start, b.start);
  const ce = cmpReal(a.end, b.end);
  if (cs === undefined || ce === undefined) return new SetOp('Intersection', sortSets([a, b]));
  const [start, lo] = cs > 0 ? [a.start, a.leftOpen] : cs < 0 ? [b.start, b.leftOpen] : [a.start, a.leftOpen || b.leftOpen];
  const [end, ro] = ce < 0 ? [a.end, a.rightOpen] : ce > 0 ? [b.end, b.rightOpen] : [a.end, a.rightOpen || b.rightOpen];
  return interval(start, end, lo, ro);
}

/** a \ b. */
export function complement(a: SetExpr, b: SetExpr): SetExpr {
  if (b === EmptySet) return a;
  if (a === EmptySet) return EmptySet;
  if (a instanceof FiniteSet) {
    const keep: Expr[] = [];
    const unknown: Expr[] = [];
    for (const x of a.args) {
      const c = containsQ(b, x);
      if (c === false) keep.push(x);
      else if (c === undefined) unknown.push(x);
    }
    if (unknown.length) return new SetOp('Complement', [finiteSet(...keep, ...unknown), b]);
    return finiteSet(...keep);
  }
  const pa = intervalParts(a);
  if (pa && b instanceof FiniteSet && b.args.every((x) => realValue(x) !== undefined)) {
    const pts = [...b.args].sort((x, y) => cmpReal(x, y)!);
    let parts: SetExpr[] = pa;
    for (const pt of pts) {
      parts = parts.flatMap((iv) => {
        if (!(iv instanceof Interval) || containsQ(iv, pt) !== true) return [iv];
        return [interval(iv.start, pt, iv.leftOpen, true), interval(pt, iv.end, true, iv.rightOpen)];
      });
    }
    return union(...parts);
  }
  const pb = intervalParts(b);
  if (pa && pb) {
    let parts: SetExpr[] = pa;
    for (const y of pb) {
      parts = parts.flatMap((x) => {
        if (!(x instanceof Interval)) return [x];
        const left = interval(x.start, y.start, x.leftOpen, !y.leftOpen);
        const right = interval(y.end, x.end, !y.rightOpen, x.rightOpen);
        const inter = intersectIntervals(x, y);
        if (inter === EmptySet) return [x];
        return [left, right];
      });
    }
    return union(...parts);
  }
  return new SetOp('Complement', [a, b]);
}

/** Is a a subset of b (true/false/undefined)? */
export function isSubset(a: SetExpr, b: SetExpr): boolean | undefined {
  if (a === EmptySet) return true;
  if (b === Reals && (a instanceof Interval || (a instanceof FiniteSet && a.args.every((x) => containsQ(Reals, x) === true)))) return true;
  if (a instanceof FiniteSet) {
    const cs = a.args.map((x) => containsQ(b, x));
    return cs.every((c) => c === true) ? true : cs.some((c) => c === false) ? false : undefined;
  }
  const c = complement(a, b);
  if (c === EmptySet) return true;
  if (c instanceof SetOp) return undefined;
  return false;
}

/** The set as a condition on x (SymPy as_relational). */
export function asRelational(s: SetExpr, x: Expr): Expr {
  if (s === EmptySet) return S.false;
  if (s === Reals) return and(Lt(S.NegativeInfinity, x), Lt(x, S.Infinity));
  if (s instanceof Interval) {
    const left = s.leftOpen ? Lt(s.start, x) : Le(s.start, x);
    const right = s.rightOpen ? Lt(x, s.end) : Le(x, s.end);
    return and(left, right);
  }
  if (s instanceof FiniteSet) return or(...s.args.map((a) => Eq(x, a)));
  if (s instanceof SetOp && s.op === 'Union') return or(...s.args.map((a) => asRelational(a as SetExpr, x)));
  if (s instanceof SetOp && s.op === 'Intersection') return and(...s.args.map((a) => asRelational(a as SetExpr, x)));
  throw new NotImplementedError('as_relational: unsupported set');
}

/** Infimum / supremum of a real set. */
export function inf(s: SetExpr): Expr {
  if (s instanceof Interval) return s.start;
  if (s === Reals) return S.NegativeInfinity;
  if (s instanceof FiniteSet) return [...s.args].sort((a, b) => cmpReal(a, b) ?? 0)[0]!;
  if (s instanceof SetOp && s.op === 'Union') return (s.args as SetExpr[]).map(inf).sort((a, b) => cmpReal(a, b) ?? 0)[0]!;
  throw new NotImplementedError('inf: unsupported set');
}
export function sup(s: SetExpr): Expr {
  if (s instanceof Interval) return s.end;
  if (s === Reals) return S.Infinity;
  if (s instanceof FiniteSet) return [...s.args].sort((a, b) => cmpReal(b, a) ?? 0)[0]!;
  if (s instanceof SetOp && s.op === 'Union') return (s.args as SetExpr[]).map(sup).sort((a, b) => cmpReal(b, a) ?? 0)[0]!;
  throw new NotImplementedError('sup: unsupported set');
}


