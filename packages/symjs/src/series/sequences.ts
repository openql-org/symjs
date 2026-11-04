// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/series/sequences.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Sequences (SymPy sympy.series.sequences): formula sequences
 * (SeqFormula), periodic sequences (SeqPer), recursive sequences
 * (RecursiveSeq), their term-wise sums and products (SeqAdd, SeqMul), the
 * empty sequence, and find_linear_recurrence.
 */

import type { ExprLike } from '../core/nodes';
import { Dummy, type Expr, ExtensionExpr, Rational, S, Special, Sym, UndefFn } from '../core/nodes';
import { at, cast } from '../core/guard';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { type NoMatchResult, NoMatch } from '../core/truth';
import { Matrix } from '../matrices/matrix';
import { matrixSolve } from '../matrices/linalg';
import { factor } from '../polys/sympoly';
import { EmptySet, type SetExpr, inf, intersection, interval, sup } from '../sets/sets';
import { expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';

const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isInf = (e: Expr, name: 'oo' | '-oo'): boolean => e instanceof Special && e.name === name;

/** a < b for numbers (false when the order is unknown). */
function less(a: Expr, b: Expr): boolean {
  if (isInf(a, '-oo') || isInf(b, 'oo')) return !(a.key === b.key);
  if (isInf(a, 'oo') || isInf(b, '-oo')) return false;
  if (a instanceof Rational && b instanceof Rational) return a.p * b.q < b.p * a.q;
  return false;
}

/** An integer point of a sequence as a JavaScript number. */
function asIndex(pt: Expr): number {
  const r = pt;
  if (!(r instanceof Rational) || !r.isInteger) throw new TypeError(`sequence index must be an integer: ${r.toString()}`);
  return Number(r.p);
}

/** SymPy SeqBase: the base class of sequences. */
export abstract class SeqBase extends ExtensionExpr {
  /** The interval on which the sequence is defined. */
  abstract get interval(): SetExpr;
  /** The first point (SymPy start). */
  get start(): Expr {
    return inf(this.interval);
  }
  /** The last point (SymPy stop). */
  get stop(): Expr {
    return sup(this.interval);
  }
  /** The number of terms (stop - start + 1, oo for an infinite sequence). */
  get length(): Expr {
    return add(sub(this.stop, this.start), 1);
  }
  /** The bound variables. */
  get variables(): Sym[] {
    return [];
  }
  /** The term at the point pt (SymPy coeff). */
  abstract coeff(pt: ExprLike): Expr;
  /** The point pt, checked to lie within the interval of the sequence. */
  protected point(pt: ExprLike): Expr {
    const p = sympify(pt);
    if (less(p, this.start) || less(this.stop, p)) throw new RangeError(`Index ${p.toString()} out of bounds ${this.interval.toString()}`);
    return p;
  }
  /** The i-th point (counted from the start, or backwards from the stop of a sequence unbounded below). */
  protected ithPoint(i: number): Expr {
    return isInf(this.start, '-oo') ? add(this.stop, -i) : add(this.start, i);
  }
  /**
   * Every term multiplied by coeff (SymPy coeff_mul). The operation is not
   * defined for sequences in general: only SeqFormula, SeqPer and
   * EmptySequence have it, and SymPy raises for the others (SeqAdd, SeqMul,
   * RecursiveSeq), as for their negation.
   */
  coeffMul(coeff: ExprLike): SeqBase {
    throw new TypeError(`cannot multiply ${this.name} and ${String(coeff)}`);
  }
  /** The term-wise sum (SymPy +). */
  override add(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot add sequence and ${String(other)}`);
    return SeqAdd(this, other);
  }
  /** The term-wise difference (SymPy -). */
  override sub(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot subtract sequence and ${String(other)}`);
    return SeqAdd(this, other.neg());
  }
  /** The sequence with every term negated. */
  override neg(): SeqBase {
    return this.coeffMul(-1);
  }
  /** The term-wise product (SymPy *). */
  override mul(other: ExprLike): SeqBase {
    if (!(other instanceof SeqBase)) throw new TypeError(`cannot multiply sequence and ${String(other)}`);
    return SeqMul(this, other);
  }
  /** The i-th term (SymPy seq[i]). */
  getItem(i: number): Expr {
    return this.coeff(this.ithPoint(i));
  }
  /** The terms i = start, start + step, ... before stop (SymPy seq[start:stop:step]). */
  slice(start = 0, stop?: number, step = 1): Expr[] {
    const end = stop ?? asIndex(this.length);
    const out: Expr[] = [];
    for (let i = start; step > 0 ? i < end : i > end; i += step) out.push(this.getItem(i));
    return out;
  }
  /** The terms in order (an infinite sequence never ends). */
  *[Symbol.iterator](): Generator<Expr, void, undefined> {
    const len = this.length;
    for (let i = 0; isInf(len, 'oo') || i < asIndex(len); i++) yield this.getItem(i);
  }

  /**
   * SymPy find_linear_recurrence(n, d, gfvar): the coefficients [c1, ..., ck]
   * of the shortest linear recurrence a(m) = c1*a(m-1) + ... + ck*a(m-k) of
   * order at most d satisfied by the first n terms ([] when there is none);
   * with gfvar also the generating function in gfvar (NoMatch when there is
   * no recurrence).
   */
  findLinearRecurrence(n: number, d?: number): Expr[];
  findLinearRecurrence(n: number, d: number | undefined, gfvar: Sym): [Expr[], Expr | NoMatchResult];
  findLinearRecurrence(n: number, d?: number, gfvar?: Sym): Expr[] | [Expr[], Expr | NoMatchResult] {
    const x = this.slice(0, n).map((t) => simplify(expand(t)));
    const lx = x.length;
    const r = d === undefined ? Math.floor(lx / 2) : Math.min(d, Math.floor(lx / 2));
    let coeffs: Expr[] = [];
    for (let l = 1; l <= r; l++) {
      const l2 = 2 * l;
      const m = Matrix.of(Array.from({ length: l }, (_, k) => x.slice(k, k + l)));
      if (isZero(simplify(m.det()))) continue;
      const y = matrixSolve(m, Matrix.of(x.slice(l, l2).map((t) => [t]))).map((t) => simplify(t));
      if (lx === l2) {
        coeffs = [...y.data].reverse();
        break;
      }
      const rest = Matrix.of(Array.from({ length: lx - 2 * l }, (_, k) => x.slice(l + k, l + k + l)));
      const prod = rest.mul(y);
      if (x.slice(l2).every((t, i) => isZero(simplify(sub(at(prod.data, i), t))))) {
        coeffs = [...y.data].reverse();
        break;
      }
    }
    if (gfvar === undefined) return coeffs;
    const l = coeffs.length;
    if (l === 0) return [[], NoMatch];
    let num: Expr = mul(at(x, l - 1), pow(gfvar, l - 1));
    let den: Expr = sub(1, mul(at(coeffs, l - 1), pow(gfvar, l)));
    for (let i = 0; i < l - 1; i++) {
      num = add(num, mul(at(x, i), pow(gfvar, i)));
      for (let j = 0; j < l - i - 1; j++) num = sub(num, mul(at(coeffs, i), at(x, j), pow(gfvar, i + j + 1)));
      den = sub(den, mul(at(coeffs, i), pow(gfvar, i + 1)));
    }
    return [coeffs, simplify(mul(factor(num), pow(factor(den), -1)))];
  }
}

/** SymPy EmptySequence: the sequence with no terms. */
export class EmptySequenceNode extends SeqBase {
  constructor() {
    super('EmptySequence', []);
  }
  withArgs(): Expr {
    return EmptySequence;
  }
  get interval(): SetExpr {
    return EmptySet;
  }
  override get length(): Expr {
    return S.Zero;
  }
  override get start(): Expr {
    return S.Infinity;
  }
  override get stop(): Expr {
    return S.NegativeInfinity;
  }
  /** EmptySequence has no terms: every index is out of bounds. */
  coeff(pt: ExprLike): Expr {
    return this.point(pt);
  }
  override coeffMul(): SeqBase {
    return this;
  }
  override printStr(): string {
    return 'EmptySequence';
  }
}

/** SymPy S.EmptySequence. */
export const EmptySequence: SeqBase = new EmptySequenceNode();

/** A sequence given by an expression of its variable on an interval (SymPy SeqExpr). */
abstract class SeqExpr extends SeqBase {
  /** The bound variable. */
  get variable(): Sym {
    return cast(at(this.args, 0), Sym, 'sequence variable');
  }
  get interval(): SetExpr {
    return interval(at(this.args, 1), at(this.args, 2));
  }
  override get start(): Expr {
    return at(this.args, 1);
  }
  override get stop(): Expr {
    return at(this.args, 2);
  }
  override get variables(): Sym[] {
    return [this.variable];
  }
  protected limitsStr(print: (e: Expr) => string): string {
    return `(${print(this.variable)}, ${print(this.start)}, ${print(this.stop)})`;
  }
}

/** Limits (x, start, stop) or (start, stop) of a sequence. */
export type SeqLimits = readonly [Sym, ExprLike, ExprLike] | readonly [ExprLike, ExprLike];

/** The variable, start and stop of a sequence (the variable found from the expression when omitted). */
function parseLimits(limits: SeqLimits | undefined, find: () => Sym): [Sym, Expr, Expr] {
  let x: Sym;
  let start: Expr;
  let stop: Expr;
  if (limits === undefined) [x, start, stop] = [find(), S.Zero, S.Infinity];
  else if (limits.length === 3) {
    const v = limits[0];
    if (!(v instanceof Sym)) throw new RangeError(`Invalid limits given: ${String(limits)}`);
    [x, start, stop] = [v, sympify(limits[1]), sympify(limits[2])];
  } else [x, start, stop] = [find(), sympify(limits[0]), sympify(limits[1])];
  if (isInf(start, '-oo') && isInf(stop, 'oo')) throw new RangeError('Both the start and end value cannot be unbounded');
  return [x, start, stop];
}

/** SymPy SeqFormula: the sequence of the values of a formula. */
export class SeqFormulaNode extends SeqExpr {
  constructor(formula: Expr, x: Sym, start: Expr, stop: Expr) {
    super('SeqFormula', [x, start, stop, formula]);
  }
  /** The formula of the terms. */
  get formula(): Expr {
    return at(this.args, 3);
  }
  withArgs(args: readonly Expr[]): Expr {
    return SeqFormula(at(args, 3), [cast(at(args, 0), Sym, 'sequence variable'), at(args, 1), at(args, 2)]);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [0], scope: [3] };
  }
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return subs(this.formula, [[this.variable, pt]]);
  }
  override coeffMul(coeff: ExprLike): SeqBase {
    return SeqFormula(mul(this.formula, sympify(coeff)), [this.variable, this.start, this.stop]);
  }
  /** The sequence of the expanded formula (SymPy SeqFormula.expand). */
  expand(): SeqBase {
    return SeqFormula(expand(this.formula), [this.variable, this.start, this.stop]);
  }
  override printStr(print: (e: Expr) => string): string {
    return `SeqFormula(${print(this.formula)}, ${this.limitsStr(print)})`;
  }
}

/**
 * SymPy SeqFormula(formula, limits): the sequence formula(x) for x from
 * start to stop ((x, 0, oo) with the free symbol of the formula by
 * default); EmptySequence on an empty interval.
 */
export function SeqFormula(formulaIn: ExprLike, limits?: SeqLimits): SeqBase {
  const formula = sympify(formulaIn);
  const [x, start, stop] = parseLimits(limits, () => {
    const free = [...freeSymbols(formula)];
    if (free.length === 1) return at(free, 0);
    if (free.length === 0) return new Dummy('k');
    throw new RangeError(
      ` specify dummy variables for ${formula.toString()}. If the formula contains more than one free symbol, a dummy variable should be supplied explicitly e.g., SeqFormula(m*n**2, (n, 0, 5))`,
    );
  });
  if (interval(start, stop) === EmptySet) return EmptySequence;
  return new SeqFormulaNode(formula, x, start, stop);
}

/** SymPy SeqPer: a periodic sequence. */
export class SeqPerNode extends SeqExpr {
  constructor(periodical: readonly Expr[], x: Sym, start: Expr, stop: Expr) {
    super('SeqPer', [x, start, stop, ...periodical]);
  }
  /** The terms of one period. */
  get periodical(): Expr[] {
    return this.args.slice(3);
  }
  /** The length of the period. */
  get period(): number {
    return this.args.length - 3;
  }
  withArgs(args: readonly Expr[]): Expr {
    return SeqPer(args.slice(3), [cast(at(args, 0), Sym, 'sequence variable'), at(args, 1), at(args, 2)]);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    return { variables: [0], scope: this.periodical.map((_, i) => 3 + i) };
  }
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    const k = isInf(this.start, '-oo') ? asIndex(sub(this.stop, pt)) : asIndex(sub(pt, this.start));
    const idx = ((k % this.period) + this.period) % this.period;
    return subs(at(this.periodical, idx), [[this.variable, pt]]);
  }
  override coeffMul(coeff: ExprLike): SeqBase {
    const c = sympify(coeff);
    return SeqPer(this.periodical.map((t) => mul(t, c)), [this.variable, this.start, this.stop]);
  }
  override printStr(print: (e: Expr) => string): string {
    const per = this.periodical;
    const tuple = per.length === 1 ? `(${print(at(per, 0))},)` : `(${per.map(print).join(', ')})`;
    return `SeqPer(${tuple}, ${this.limitsStr(print)})`;
  }
}

/**
 * SymPy SeqPer(periodical, limits): the sequence repeating the terms of
 * periodical from start to stop ((x, 0, oo) by default); EmptySequence on
 * an empty interval.
 */
export function SeqPer(periodical: readonly ExprLike[], limits?: SeqLimits): SeqBase {
  const per = periodical.map(sympify);
  const [x, start, stop] = parseLimits(limits, () => {
    const free = new Map<string, Sym>();
    for (const t of per) for (const s of freeSymbols(t)) free.set(s.key, s);
    return free.size === 1 ? at([...free.values()], 0) : new Dummy('k');
  });
  if (interval(start, stop) === EmptySet) return EmptySequence;
  return new SeqPerNode(per, x, start, stop);
}

/**
 * SymPy sequence(seq, limits): a periodic sequence for an array of terms, a
 * formula sequence otherwise.
 */
export function sequence(seq: ExprLike | readonly ExprLike[], limits?: SeqLimits): SeqBase {
  const isList = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
  return isList(seq) ? SeqPer(seq, limits) : SeqFormula(seq, limits);
}

/** The applications y(...) of the undefined function y in e. */
function applications(e: Expr, y: string, out: Expr[] = []): Expr[] {
  if (e instanceof UndefFn && e.name === y) out.push(e);
  for (const a of e.args) applications(a, y, out);
  return out;
}

/** SymPy RecursiveSeq: a sequence defined by a recurrence relation and initial terms. */
export class RecursiveSeqNode extends SeqBase {
  /** The terms computed so far, from the start on. */
  private readonly terms: Expr[];
  /** The order of the recurrence. */
  readonly degree: number;
  constructor(recurrence: Expr, yn: UndefFn, n: Sym, initial: readonly Expr[], start: Expr, degree: number) {
    super('RecursiveSeq', [recurrence, yn, n, start, ...initial]);
    this.degree = degree;
    this.terms = [...initial];
  }
  /** The right-hand side of the recurrence y(n) = recurrence. */
  get recurrence(): Expr {
    return at(this.args, 0);
  }
  /** The term y(n). */
  get yn(): UndefFn {
    return cast(at(this.args, 1), UndefFn, 'recurrence function');
  }
  /** The recurrence variable (SymPy n). */
  get variable(): Sym {
    return cast(at(this.args, 2), Sym, 'recurrence variable');
  }
  /** The initial terms. */
  get initial(): Expr[] {
    return this.args.slice(4);
  }
  override get start(): Expr {
    return at(this.args, 3);
  }
  override get stop(): Expr {
    return S.Infinity;
  }
  get interval(): SetExpr {
    return interval(this.start, S.Infinity);
  }
  withArgs(args: readonly Expr[]): Expr {
    return RecursiveSeq(at(args, 0), at(args, 1), at(args, 2), args.slice(4), at(args, 3));
  }
  coeff(pt: ExprLike): Expr {
    const index = this.point(pt);
    const i = asIndex(sub(index, this.start));
    for (let current = this.terms.length; current <= i; current++) {
      const rec = xreplace(this.recurrence, [[this.variable, add(this.start, current)]]);
      // the earlier terms y(start + k) by their values
      const known = this.terms.map((t, k): [Expr, Expr] => [new UndefFn(this.yn.name, [add(this.start, k)]), t]);
      this.terms.push(xreplace(rec, known));
    }
    return at(this.terms, i);
  }
  override printStr(print: (e: Expr) => string): string {
    const init = this.initial;
    return `RecursiveSeq(${print(this.recurrence)}, ${print(this.yn)}, ${print(this.variable)}, (${init.map(print).join(', ')}${init.length === 1 ? ',' : ''}), ${print(this.start)})`;
  }
}

/**
 * SymPy RecursiveSeq(recurrence, yn, n, initial, start): the sequence y(n)
 * with y(n) = recurrence for n >= start + degree and the initial terms
 * (Dummy symbols c_k when omitted) before.
 */
export function RecursiveSeq(recurrenceIn: ExprLike, yn: Expr, n: Expr, initial: readonly ExprLike[] = [], startIn: ExprLike = 0): SeqBase {
  if (!(yn instanceof UndefFn)) throw new TypeError(`recurrence sequence must be an applied undefined function, found \`${yn.toString()}\``);
  if (!(n instanceof Sym)) throw new TypeError(`recurrence variable must be a symbol, found \`${n.toString()}\``);
  if (yn.args.length !== 1 || at(yn.args, 0).key !== n.key) throw new TypeError('recurrence sequence does not match symbol');
  const recurrence = sympify(recurrenceIn);
  let degree = 0;
  for (const prev of applications(recurrence, yn.name)) {
    if (prev.args.length !== 1) throw new TypeError('Recurrence should be in a single variable');
    const shift = sub(at(prev.args, 0), n);
    if (!(shift instanceof Rational && shift.isInteger && shift.isNegative)) throw new TypeError(`Recurrence should have constant, negative, integer shifts (found ${prev.toString()})`);
    degree = Math.max(degree, -Number(shift.p));
  }
  const init = initial.length ? initial.map(sympify) : Array.from({ length: degree }, (_, k) => new Dummy(`c_${k}`));
  if (init.length !== degree) throw new RangeError('Number of initial terms must equal degree');
  return new RecursiveSeqNode(recurrence, yn, n, init, sympify(startIn), degree);
}

/** The bounds of the interval common to two sequences. */
function commonBounds(a: SeqBase, b: SeqBase): [Expr, Expr] {
  const iv = intersection(a.interval, b.interval);
  return [inf(iv), sup(iv)];
}

/** Two periodic sequences combined term-wise over the least common period. */
function combinePeriodic(a: SeqPerNode, b: SeqPerNode, op: (u: Expr, v: Expr) => Expr): SeqBase {
  const [p1, p2] = [a.periodical, b.periodical];
  const g = (u: number, v: number): number => (v === 0 ? u : g(v, u % v));
  const len = (p1.length / g(p1.length, p2.length)) * p2.length;
  const per = Array.from({ length: len }, (_, i) => op(at(p1, i % p1.length), at(p2, i % p2.length)));
  const [start, stop] = commonBounds(a, b);
  return SeqPer(per, [a.variable, start, stop]);
}

/**
 * The term-wise sum or product of two sequences when a rule applies (SymPy
 * SeqFormula._add and _mul, SeqPer._add and _mul), else undefined.
 */
function combineRule(s: SeqBase, t: SeqBase, op: (u: Expr, v: Expr) => Expr): SeqBase | undefined {
  if (s instanceof SeqFormulaNode && t instanceof SeqFormulaNode) {
    const [start, stop] = commonBounds(s, t);
    return SeqFormula(op(s.formula, subs(t.formula, [[t.variable, s.variable]])), [s.variable, start, stop]);
  }
  if (s instanceof SeqPerNode && t instanceof SeqPerNode) return combinePeriodic(s, t, op);
  return undefined;
}

/** The number of nodes of an expression tree (SymPy _nodes). */
const nodeCount = (e: Expr): number => 1 + e.args.reduce((t, a) => t + nodeCount(a), 0);

/** The number of nodes of a sequence as SymPy counts them (the limits are a Tuple, the period of SeqPer too). */
function seqNodes(s: SeqBase): number {
  if (s instanceof SeqFormulaNode) return 5 + nodeCount(s.formula);
  if (s instanceof SeqPerNode) return 6 + s.periodical.reduce((t, a) => t + nodeCount(a), 0);
  return 1 + s.args.reduce((t, a) => t + (a instanceof SeqBase ? seqNodes(a) : nodeCount(a)), 0);
}

/**
 * The arguments of SeqAdd and SeqMul in SymPy's order (ordered with the key
 * _start_key): by start, then by the number of nodes, then by class name and
 * printed form.
 */
function ordered(args: readonly SeqBase[]): SeqBase[] {
  return [...args].sort((a, b) => {
    const [sa, sb] = [a.start, b.start];
    if (less(sa, sb)) return -1;
    if (less(sb, sa)) return 1;
    const d = seqNodes(a) - seqNodes(b);
    if (d !== 0) return d;
    if (a.name !== b.name) return a.name < b.name ? -1 : 1;
    return a.key < b.key ? -1 : a.key > b.key ? 1 : 0;
  });
}

/** The sequences of nested arguments, with nested operations of the same class flattened. */
function flattenSeqs(args: readonly (SeqBase | readonly SeqBase[])[], cls: typeof SeqAddNode | typeof SeqMulNode): SeqBase[] {
  const out: SeqBase[] = [];
  const go = (a: SeqBase | readonly SeqBase[]): void => {
    if (a instanceof cls) a.seqs.forEach(go);
    else if (a instanceof SeqBase) out.push(a);
    else a.forEach(go);
  };
  args.forEach(go);
  return out;
}

/** The interval common to the sequences. */
const commonInterval = (args: readonly SeqBase[]): SetExpr => intersection(...args.map((a) => a.interval));

/** Combine pairs of the sequences by the rule until none applies (SymPy SeqAdd.reduce and SeqMul.reduce). */
function reduce(args0: readonly SeqBase[], rule: (s: SeqBase, t: SeqBase) => SeqBase | undefined): SeqBase[] {
  let args = [...args0];
  for (let changed = true; changed; ) {
    changed = false;
    outer: for (let i = 0; i < args.length; i++) {
      for (let j = 0; j < args.length; j++) {
        if (i === j) continue;
        const s = at(args, i);
        const t = at(args, j);
        const r = rule(s, t);
        if (r !== undefined) {
          args = [...args.filter((a) => a !== s && a !== t), r];
          changed = true;
          break outer;
        }
      }
    }
  }
  return args;
}

/** Term-wise operation of sequences (SymPy SeqExprOp). */
abstract class SeqExprOp extends SeqBase {
  /** The operand sequences. */
  get seqs(): SeqBase[] {
    return this.args.map((a) => cast(a, SeqBase, 'sequence'));
  }
  get interval(): SetExpr {
    return commonInterval(this.seqs);
  }
  override get variables(): Sym[] {
    return this.seqs.flatMap((s) => s.variables);
  }
}

/** SymPy SeqAdd: the term-wise sum of sequences (unevaluated). */
export class SeqAddNode extends SeqExprOp {
  constructor(args: readonly SeqBase[]) {
    super('SeqAdd', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return SeqAdd(...args.map((a) => cast(a, SeqBase, 'sequence')));
  }
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return add(...this.seqs.map((a) => a.coeff(pt)));
  }
}

/** SymPy SeqMul: the term-wise product of sequences (unevaluated). */
export class SeqMulNode extends SeqExprOp {
  constructor(args: readonly SeqBase[]) {
    super('SeqMul', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return SeqMul(...args.map((a) => cast(a, SeqBase, 'sequence')));
  }
  coeff(pt0: ExprLike): Expr {
    const pt = this.point(pt0);
    return mul(...this.seqs.map((a) => a.coeff(pt)));
  }
}

/**
 * SymPy SeqAdd(*args): the term-wise sum of the sequences on their common
 * interval, combined where a rule applies (formulas add, periodic
 * sequences add over the common period); EmptySequence when the common
 * interval is empty.
 */
export function SeqAdd(...seqs: (SeqBase | readonly SeqBase[])[]): SeqBase {
  const args = flattenSeqs(seqs, SeqAddNode).filter((a) => a !== EmptySequence);
  if (!args.length || commonInterval(args) === EmptySet) return EmptySequence;
  const r = reduce(args, (s, t) => combineRule(s, t, add));
  return r.length === 1 ? at(r, 0) : new SeqAddNode(ordered(r));
}

/**
 * SymPy SeqMul(*args): the term-wise product of the sequences on their
 * common interval, combined where a rule applies; EmptySequence when the
 * common interval is empty.
 */
export function SeqMul(...seqs: (SeqBase | readonly SeqBase[])[]): SeqBase {
  const args = flattenSeqs(seqs, SeqMulNode);
  if (!args.length || commonInterval(args) === EmptySet) return EmptySequence;
  const r = reduce(args, (s, t) => combineRule(s, t, mul));
  return r.length === 1 ? at(r, 0) : new SeqMulNode(ordered(r));
}
