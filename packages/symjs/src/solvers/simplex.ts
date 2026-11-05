// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 solvers/simplex.py, BSD-3-Clause; see LICENSE.

/**
 * @file Linear programming with the simplex method (SymPy
 * `sympy.solvers.simplex`): `lpmin` and `lpmax` of a linear objective under
 * linear constraints, and `linprog` in the matrix form of scipy's linprog.
 * The tableau holds exact rationals (or Floats); ties are broken with
 * Bland's rule as in SymPy.
 */

import type { Expr, ExprLike, Num } from '../core/nodes';
import { Dummy, Float, Rational, Rel, S, Sym } from '../core/nodes';
import { at, first, getOrThrow } from '../core/guard';
import { add, mul, sympify } from '../core/ops';
import { Eq, Ge, Le } from '../core/logic';
import { numAdd, numCmp, numInv, numMul, numNeg } from '../core/num';
import { ordered } from '../core/match';
import { isPositive } from '../core/assumptions';
import { xreplace } from '../core/traverse';
import { ExprMap } from '../core/exprmap';
import { Matrix } from '../matrices/matrix';
import { numberedSymbols } from '../utilities/iterables';
import { EmptySet, inf, intersection, sup, type SetExpr } from '../sets/sets';
import { asSet } from './inequalities';
import { linearEqToMatrix } from './public';

/** SymPy UnboundedLPError: the objective is unbounded on the feasible region. */
// oxlint-disable-next-line no-restricted-globals -- SymPy's LP errors derive from Exception, like NonlinearError
export class UnboundedLPError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'UnboundedLPError';
  }
}

/** SymPy InfeasibleLPError: the constraints have no common solution. */
// oxlint-disable-next-line no-restricted-globals -- SymPy's LP errors derive from Exception, like NonlinearError
export class InfeasibleLPError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'InfeasibleLPError';
  }
}

/** A matrix argument: a Matrix, a list of rows or a flat list (a column, as SymPy's Matrix(list)). */
export type LPMatrixLike = Matrix | readonly ExprLike[] | readonly (readonly ExprLike[])[];

/** The bounds (lower, upper) of a variable; null is no bound (SymPy None). */
export type LPBound = readonly [ExprLike | null, ExprLike | null];

/** The bounds of linprog: one pair for all variables, a pair per variable, or pairs by variable index. */
export type LPBounds = LPBound | readonly LPBound[] | ReadonlyMap<number, LPBound>;

const isNum = (e: Expr): e is Num => e instanceof Rational || e instanceof Float;
const neg = (a: Num): boolean => a.isNegative;
const pos = (a: Num): boolean => a.isPositive;
const isZeroNum = (e: Expr): boolean => isNum(e) && e.isZero;
const isBoundMap = (b: LPBounds): b is ReadonlyMap<number, LPBound> => b instanceof Map;

/** Bland's-rule labels: x variables (false) come before y variables (true), then by index. */
type Label = readonly [boolean, number];
const labelCmp = (a: Label, b: Label): number => (a[0] === b[0] ? a[1] - b[1] : a[0] ? 1 : -1);

/** SymPy _pivot: pivot the tableau about entry (i, j). */
function pivotAbout(M: readonly (readonly Num[])[], i: number, j: number): Num[][] {
  const Mi = at(M, i);
  const inv = numInv(at(Mi, j));
  return M.map((row, r) =>
    row.map((v, c) => {
      const Mrj = at(row, j);
      if (r === i) return c === j ? inv : numMul(v, inv);
      if (c === j) return numNeg(numMul(Mrj, inv));
      return numAdd(v, numNeg(numMul(Mrj, numMul(at(Mi, c), inv))));
    }),
  );
}

/** SymPy _choose_pivot_row: the smallest ratio B[i]/A[i, c], ties broken by Bland's rule. */
function choosePivotRow(M: readonly (readonly Num[])[], rows: readonly number[], c: number, n: number, Y: readonly Label[]): number {
  const ratio = (i: number): Num => numMul(at(at(M, i), n), numInv(at(at(M, i), c)));
  let best = first(rows);
  for (const i of rows.slice(1)) {
    const d = numCmp(ratio(i), ratio(best));
    if (d < 0 || (d === 0 && labelCmp(at(Y, i), at(Y, best)) < 0)) best = i;
  }
  return best;
}

/** Bland's rule for the pivot column: the smallest label among the candidates. */
function chooseColumn(cols: readonly number[], X: readonly Label[]): number {
  let best = first(cols);
  for (const j of cols.slice(1)) if (labelCmp(at(X, j), at(X, best)) < 0) best = j;
  return best;
}

const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);

/**
 * SymPy _simplex: minimize C*x + D subject to A*x <= B and x >= 0. Returns
 * the optimum, the argmin and the argmax of the dual.
 */
function simplexTableau(A: readonly (readonly Expr[])[], B: readonly Expr[], C: readonly Expr[], D: Expr = S.Zero): [Num, Num[], Num[]] {
  // (B has a value for each row of A)
  const rows: Expr[][] = [...A.map((row, i) => [...row, at(B, i)]), [...C, D]];
  if (!rows.every((r) => r.every(isNum))) {
    throw new TypeError('Only rationals and floats are allowed.');
  }
  // (every entry was checked to be a number above)
  let M = rows.map((r) => r.filter(isNum));
  const n = C.length;
  const m = A.length;
  const X: Label[] = range(n).map((j) => [false, j]);
  const Y: Label[] = range(m).map((i) => [true, i]);
  const entry = (i: number, j: number): Num => at(at(M, i), j);
  const swap = (r: number, c: number): void => {
    const t = at(X, c);
    X[c] = at(Y, r);
    Y[r] = t;
  };

  // Phase 1: find a feasible solution or determine that none exists
  let last: [number, number] | undefined;
  let oscillating = false;
  for (;;) {
    const k = range(m).find((i) => neg(entry(i, n)));
    if (k === undefined) break;
    const pivCols = range(n).filter((j) => neg(entry(k, j)));
    if (pivCols.length === 0) throw new InfeasibleLPError('The constraint set is empty!');
    const c = chooseColumn(pivCols, X);
    const pivRows = range(m).filter((i) => pos(entry(i, c)) && pos(entry(i, n)));
    pivRows.push(k);
    const r = choosePivotRow(M, pivRows, c, n, Y);
    if (last?.[0] === r && last[1] === c) {
      // SymPy: oscillation; the solution is checked before the return
      oscillating = true;
      break;
    }
    last = [r, c];
    M = pivotAbout(M, r, c);
    swap(r, c);
  }

  // Phase 2: from a feasible solution, pivot to the optimum
  for (;;) {
    const pivCols = range(n).filter((j) => neg(entry(m, j)));
    if (pivCols.length === 0) break;
    const c = chooseColumn(pivCols, X);
    const pivRows = range(m).filter((i) => pos(entry(i, c)));
    if (pivRows.length === 0) throw new UnboundedLPError('Objective function can assume arbitrarily large values!');
    const r = choosePivotRow(M, pivRows, c, n, Y);
    M = pivotAbout(M, r, c);
    swap(r, c);
  }

  const argmax: Num[] = range(n).map(() => S.Zero);
  const argminDual: Num[] = range(m).map(() => S.Zero);
  X.forEach(([v, j], i) => {
    if (v) argminDual[j] = entry(m, i);
  });
  Y.forEach(([v, j], i) => {
    if (!v) argmax[j] = entry(i, n);
  });
  if (oscillating && [...argmax, ...argminDual].some(neg)) {
    throw new InfeasibleLPError('Oscillating system led to invalid solution.');
  }
  return [numNeg(entry(m, n)), argmax, argminDual];
}

/**
 * The values of the expressions that must be nonpositive at the solution
 * (symjs addition: SymPy checks only the signs after an oscillation, and
 * returns a point that violates the constraints for some infeasible
 * problems, such as (3, [1]) for 2*x <= 0, 3*x <= 1, -x <= -1).
 */
function assertFeasible(values: readonly Expr[]): void {
  if (values.some((v) => isPositive(v) === true)) throw new InfeasibleLPError('Oscillating system led to invalid solution.');
}

/** The nonpositive expressions, the change of variables and the auxiliary symbols of _rel_as_nonpos. */
type Nonpos = [Expr[], ExprMap<Expr>, Dummy[], Expr[]];

/**
 * SymPy _rel_as_nonpos: the constraints as nonpositive expressions in
 * nonnegative variables. Univariate constraints become a change of
 * variables (x = a + u, x = b - u, x = u - x for an unbounded x). Undefined
 * when the constraints cannot be satisfied.
 */
function relAsNonpos(constr: readonly Expr[], syms: readonly Sym[]): Nonpos | undefined {
  const r = new ExprMap<Expr>();
  const np: Expr[] = [];
  const all: Expr[] = [];
  const aux: Dummy[] = [];
  const ui = numberedSymbols('z', { start: 1, cls: Dummy });
  const univariate = new Map<string, SetExpr>();
  for (const c of constr) {
    if (c === S.true) continue;
    if (c === S.false) return undefined;
    if (c.has(S.Infinity) || c.has(S.NegativeInfinity)) throw new RangeError('only finite bounds are permitted');
    if (!(c instanceof Rel && (c.op === 'Le' || c.op === 'Ge'))) {
      throw new TypeError(`only equalities like Eq(x, y) or non-strict inequalities like x >= y are allowed in lp, not ${String(c)}`);
    }
    const i = c.op === 'Le' ? add(c.lhs, mul(-1, c.rhs)) : add(c.rhs, mul(-1, c.lhs));
    all.push(i);
    const freei = [...i.freeSymbols()];
    if (freei.length > 1) {
      np.push(i);
      continue;
    }
    // (a constraint without symbols evaluates to True or False)
    const x = first(freei);
    const ivl = asSet(new Rel('Le', i, S.Zero));
    const prev = univariate.get(x.key);
    univariate.set(x.key, prev === undefined ? ivl : intersection(prev, ivl));
  }
  const unbound: Sym[] = [];
  for (const x of syms) {
    const ivl = univariate.get(x.key);
    if (ivl === undefined) {
      unbound.push(x);
      continue;
    }
    if (ivl === EmptySet) return undefined;
    const [a, b] = [inf(ivl), sup(ivl)];
    if (a === S.NegativeInfinity) {
      const u = ui.next().value;
      r.set(x, add(b, mul(-1, u)));
      aux.push(u);
    } else if (b === S.Infinity) {
      if (!isZeroNum(a)) {
        const u = ui.next().value;
        r.set(x, add(a, u));
        aux.push(u);
      }
    } else {
      const u = ui.next().value;
      aux.push(u);
      r.set(x, add(u, a));
      np.push(add(u, mul(-1, add(b, mul(-1, a)))));
    }
  }
  for (const x of unbound) {
    const u = ui.next().value;
    r.set(x, add(u, mul(-1, x)));
    aux.push(u);
  }
  return [np, r, aux, all];
}

/** SymPy _lp_matrices: the matrices of the system in nonnegative variables. */
function lpMatrices(objective: ExprLike, constraints: readonly ExprLike[]): [Matrix, Matrix, Matrix, Matrix, ExprMap<Expr>, Sym[], Dummy[], Expr[]] {
  let F = sympify(objective);
  const np = constraints.map((c) => sympify(c));
  const symSet = new Map<string, Sym>();
  for (const e of [F, ...np]) for (const s of e.freeSymbols()) symSet.set(s.key, s);
  // (ordered gives the symbols back)
  const syms = ordered([...symSet.values()]).filter((s): s is Sym => s instanceof Sym);
  // Eq(x, y) is x - y <= 0 and y - x <= 0
  const len = np.length;
  for (let i = 0; i < len; i++) {
    const c = at(np, i);
    if (c instanceof Rel && c.op === 'Eq') {
      const d = add(c.lhs, mul(-1, c.rhs));
      np[i] = Le(d, 0);
      np.push(Le(mul(-1, d), 0));
    }
  }
  const nonpos = relAsNonpos(np, syms);
  if (nonpos === undefined) throw new InfeasibleLPError('Inconsistent/False constraint');
  const [ineqs0, r, aux, all] = nonpos;
  F = xreplace(F, [...r]);
  const ineqs = ineqs0.map((e) => xreplace(e, [...r]));
  const xx: Sym[] = [...syms, ...aux];
  const [A, B] = linearEqToMatrix(ineqs, xx);
  const [C, D] = linearEqToMatrix([F], xx);
  return [A, B, C, D, r, xx, aux, all];
}

function lp(max: boolean, f: ExprLike, constr: readonly ExprLike[]): [Expr, ExprMap<Expr>] {
  const [A, B, C, D, r, xx, aux, all] = lpMatrices(f, constr);
  const a = A.tolist();
  const b = B.tolist().map((row) => first(row));
  const c = first(C.tolist());
  const d = first(first(D.tolist()));
  // _simplex minimizes, so a maximum is the negated minimum of -f
  const sgn = max ? -1 : 1;
  const [o, x] = simplexTableau(a, b, c.map((e) => mul(sgn, e)), mul(sgn, d));
  let p = new ExprMap<Expr>(xx.map((s, i) => [s, at(x, i)] as const));
  if (r.size > 0) {
    // the values of the original symbols from those of the auxiliary ones
    const values = [...p];
    for (const [k, v] of r) p.set(k, xreplace(v, values));
    const auxKeys = new Set(aux.map((s) => s.key));
    p = new ExprMap(ordered([...p.keys()]).filter((k) => !auxKeys.has(k.key)).map((k) => [k, getOrThrow(p, k)] as const));
  }
  const values = [...p];
  assertFeasible(all.map((e) => xreplace(e, values)));
  return [mul(sgn, o), p];
}

/**
 * SymPy lpmin: the minimum of the linear objective f under linear
 * constraints (non-strict inequalities and Eq) and the values of the
 * variables where it is attained. Variables without a lower bound may be
 * negative. Throws UnboundedLPError or InfeasibleLPError.
 */
export function lpmin(f: ExprLike, constr: readonly ExprLike[]): [Expr, ExprMap<Expr>] {
  return lp(false, f, constr);
}

/** SymPy lpmax: the maximum of the linear objective f under linear constraints (see {@link lpmin}). */
export function lpmax(f: ExprLike, constr: readonly ExprLike[]): [Expr, ExprMap<Expr>] {
  return lp(true, f, constr);
}

/** Matrix(x) of SymPy: a flat list is a column. */
function toMatrix(x: LPMatrixLike): Matrix {
  if (x instanceof Matrix) return x;
  const rows = x.map((e) => (Array.isArray(e) ? e : [e]));
  return Matrix.of(rows);
}

const isEmpty = (x: LPMatrixLike): boolean => (x instanceof Matrix ? x.rows * x.cols === 0 : x.length === 0);

const isPair = (b: unknown): b is LPBound => Array.isArray(b) && b.length === 2 && !Array.isArray(b[0]) && !Array.isArray(b[1]);

/** SymPy _handle_bounds: the constraint rows and right sides of the bounds, with auxiliary columns. */
function handleBounds(bounds: readonly LPBound[]): [Expr[][], Expr[]] {
  let width = bounds.length;
  const rows: [number, [number, number][]][] = [];
  const rhs: Expr[] = [];
  // index -1 is the last column at the time the row is made (Python's negative index)
  const row = (pairs: [number, number][]): void => {
    rows.push([width, pairs]);
  };
  const unbound: number[] = [];
  bounds.forEach(([lo, hi], x) => {
    if (lo === null) {
      if (hi === null) {
        unbound.push(x);
        return;
      }
      // x = b - u
      width += 1;
      row([[x, 1], [-1, 1]]);
      row([[x, -1], [-1, -1]]);
      const b = sympify(hi);
      rhs.push(b, mul(-1, b));
    } else {
      const a = sympify(lo);
      if (hi === null && isZeroNum(a)) return;
      // x = a + u
      width += 1;
      row([[x, 1], [-1, -1]]);
      row([[x, -1], [-1, 1]]);
      rhs.push(a, mul(-1, a));
      if (hi !== null) {
        // u <= b - a
        row([[-1, 1]]);
        rhs.push(add(hi, mul(-1, a)));
      }
    }
  });
  for (const x of unbound) {
    // x = u - v
    width += 2;
    row([[x, 1], [-1, 1], [-2, -1]]);
    row([[x, -1], [-1, -1], [-2, 1]]);
    rhs.push(S.Zero, S.Zero);
  }
  const out = rows.map(([len, pairs]) => {
    const r: Expr[] = Array.from({ length: width }, () => S.Zero);
    for (const [i, v] of pairs) r[i < 0 ? len + i : i] = Rational.of(v);
    return r;
  });
  return [out, rhs];
}

/** The bounds of linprog as a pair per variable; none for the default (0, None) of every variable. */
function boundList(bounds: LPBounds | undefined, n: number): LPBound[] {
  if (bounds === undefined) return [];
  if (isBoundMap(bounds)) {
    if (bounds.size === 0) return [];
    const out: LPBound[] = range(n).map(() => [0, null]);
    for (const [i, b] of bounds) {
      if (i < 0 || i >= n) throw new RangeError(`bound index ${i} out of range`);
      out[i] = b;
    }
    return out;
  }
  if (isPair(bounds)) {
    if (bounds[1] === null && bounds[0] !== null && isZeroNum(sympify(bounds[0]))) return [];
    return range(n).map(() => bounds);
  }
  if (bounds.length === n && bounds.every(isPair)) return [...bounds];
  throw new RangeError(`unexpected bounds ${String(bounds)}`);
}

/**
 * SymPy linprog: minimize c*x subject to A*x <= b, Aeq*x = beq and the
 * bounds (x >= 0 by default; a pair (lo, hi) with null for no bound, for all
 * variables, a list of pairs, or a Map from variable index to pair). Returns
 * the minimum and the values of x. SymPy drops the values when every bound
 * is given as (0, None) in a list; symjs returns them.
 */
export function linprog(
  c: LPMatrixLike,
  A?: LPMatrixLike,
  b?: LPMatrixLike,
  AEq?: LPMatrixLike,
  bEq?: LPMatrixLike,
  bounds?: LPBounds,
): [Expr, Expr[]] {
  let C = toMatrix(c);
  if (C.rows !== 1 && C.cols === 1) C = C.transpose();
  if (C.rows !== 1) throw new RangeError('C must be a single row.');
  const n = C.cols;
  let a: Expr[][];
  let rhs: Expr[];
  if (A === undefined || isEmpty(A)) {
    if (b !== undefined && !isEmpty(b)) throw new RangeError('A and b must both be given');
    // the bounds alone constrain the variables
    a = [];
    rhs = [];
  } else {
    if (b === undefined) throw new RangeError('A and b must both be given');
    const Am = toMatrix(A);
    if (Am.cols !== n) throw new RangeError('number of columns in A and C must match');
    a = Am.tolist();
    rhs = toMatrix(b).tolist().flat();
  }
  if (AEq === undefined) {
    if (bEq !== undefined) throw new RangeError('A_eq and b_eq must both be given');
  } else {
    if (bEq === undefined) throw new RangeError('A_eq and b_eq must both be given');
    // x == y is x <= y and -x <= -y
    const ae = toMatrix(AEq).tolist();
    const be = toMatrix(bEq).tolist().flat();
    a = [...a, ...ae, ...ae.map((r) => r.map((e) => mul(-1, e)))];
    rhs = [...rhs, ...be, ...be.map((e) => mul(-1, e))];
  }
  let cost = first(C.tolist());
  const list = boundList(bounds, n);
  const [ab, bb] = handleBounds(list);
  const original = a.map((row, i) => [row, at(rhs, i)] as const);
  if (ab.length > 0) {
    const width = first(ab).length;
    const pad = (r: readonly Expr[]): Expr[] => [...r, ...Array.from({ length: width - r.length }, () => S.Zero)];
    if (a.length > 0) {
      a = [...a.map(pad), ...ab];
      rhs = [...rhs, ...bb];
    } else {
      a = ab;
      rhs = bb;
    }
    cost = pad(cost);
  }
  // (SymPy: no constraints at all is an error of linprog, unlike lpmin)
  if (a.length === 0) throw new RangeError('must give A and B');
  const [o, p] = simplexTableau(a, rhs, cost);
  const x = p.slice(0, n);
  const dot = (row: readonly Expr[]): Expr => add(...x.map((v, j) => mul(v, at(row, j))));
  const lower = list.length > 0 ? list : x.map((): LPBound => [0, null]);
  assertFeasible([
    ...original.map(([row, v]) => add(dot(row), mul(-1, v))),
    ...lower.flatMap(([lo, hi], j) => [lo === null ? S.Zero : add(lo, mul(-1, at(x, j))), hi === null ? S.Zero : add(at(x, j), mul(-1, hi))]),
  ]);
  return [o, x];
}

/**
 * SymPy show_linprog: the objective and the constraints of a linprog
 * problem in the variables x1, x2, ... (SymPy fails without A_eq or bounds;
 * symjs leaves them out).
 */
export function showLinprog(
  c: LPMatrixLike,
  A?: LPMatrixLike,
  b?: LPMatrixLike,
  AEq?: LPMatrixLike,
  bEq?: LPMatrixLike,
  bounds?: LPBounds,
): [Expr, Expr[]] {
  let C = toMatrix(c);
  if (C.rows !== 1 && C.cols === 1) C = C.transpose();
  if (C.rows !== 1) throw new RangeError('C must be a single row.');
  const n = C.cols;
  const x = range(n).map((i) => new Sym(`x${i + 1}`));
  const dot = (r: readonly Expr[]): Expr => add(...r.map((e, i) => mul(e, at(x, i))));
  const f = dot(first(C.tolist()));
  const cons: Expr[] = [];
  const relations = (M: LPMatrixLike | undefined, v: LPMatrixLike | undefined, rel: (a: Expr, b: Expr) => Expr): void => {
    if (M === undefined || isEmpty(M)) return;
    if (v === undefined) throw new RangeError('A and b must both be given');
    const bs = toMatrix(v).tolist().flat();
    toMatrix(M).tolist().forEach((r, i) => cons.push(rel(dot(r), at(bs, i))));
  };
  relations(A, b, Le);
  relations(AEq, bEq, Eq);
  boundList(bounds, n).forEach(([lo, hi], i) => {
    if (lo !== null) cons.push(Ge(at(x, i), lo));
    if (hi !== null) cons.push(Le(at(x, i), hi));
  });
  return [f, cons];
}
