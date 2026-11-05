// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/repr.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's `srepr` (`ReprPrinter`): the tree of an expression as the
 * SymPy constructor calls that rebuild it (`Add(Symbol('x'), Integer(2))`),
 * and the view of an expression as SymPy's class names and arguments that
 * the tree printers (`srepr`, `print_tree`, `dotprint`) share.
 */

import { Add, BoolAtom, Constant, Derivative, Dummy, Expr, ExtensionExpr, Float, Integral, Limit, Mul, Order, Piecewise, Rational, Rel, S, Special, Sym, UndefFn, Wild, WildFunction, impl, isNum } from '../core/nodes';
import { numNeg } from '../core/num';
import { BoolOp } from '../core/boolalg';
import { Concrete } from '../core/concrete';
import { sympyArgs, sympyClassName } from '../core/compare';
import { precToDps, toStr } from '../numeric/mpf';
import { asOrderedFactors, asOrderedTerms } from './sortkey';
import { setArgsOrdered, setClass } from './sets';
import { str } from './str';
import { at } from '../core/guard';

/**
 * A node of an expression as SymPy sees it: its class name, its arguments
 * (with SymPy's containers: `Tuple` limits, `ExprCondPair` pieces, ...),
 * whether its class derives from `Expr`, its `str()` form and, for an atom,
 * its srepr form.
 */
export interface BasicView {
  /** SymPy's class name (`type(e).__name__`). */
  readonly cls: string;
  /** The arguments (`e.args`). */
  readonly args: readonly BasicView[];
  /** The class derives from Expr (not only Basic, like Tuple, sets, relations and booleans). */
  readonly isExpr: boolean;
  /** SymPy's str() of the node. */
  readonly str: string;
  /** The srepr form of an atom (a node without arguments) or of a node printed whole (a matrix). */
  readonly repr?: string;
  /** The constructor srepr prints when it is not the class (`Function('f')` of an applied undefined function). */
  readonly head?: string;
  /** The expression itself; absent for the containers SymPy adds (Tuple, ExprCondPair, ...). */
  readonly expr?: Expr;
}

/** A container node SymPy has where symjs keeps the items flat (limits, pieces). */
function container(cls: string, args: readonly BasicView[], text: string): BasicView {
  return { cls, args, isExpr: false, str: text };
}

/** A SymPy Tuple of the views. */
const tuple = (items: readonly BasicView[]): BasicView => container('Tuple', items, items.length === 1 ? `(${at(items, 0).str},)` : `(${items.map((i) => i.str).join(', ')})`);

/** Python's repr of a string. */
export function pyRepr(s: string): string {
  if (s.includes("'") && !s.includes('"')) return `"${s}"`;
  return `'${s.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n')}'`;
}

/** mpmath `repr_dps`: the digits that make a float's repr round-trip. */
const reprDps = (prec: number): number => {
  const dps = precToDps(prec);
  return dps === 15 ? 17 : dps + 3;
};

/**
 * The assumptions given to a symbol (SymPy `_assumptions_orig`), as few as
 * imply the ones it keeps (symjs stores them with their consequences).
 */
function givenAssumptions(e: Sym): [string, boolean][] {
  const a = e.assumptions;
  const out: [string, boolean][] = [];
  if (a.integer === true && a.zero !== true) out.push(['integer', true]);
  if (a.zero === true) out.push(['zero', true]);
  else if (a.positive === true) out.push(['positive', true]);
  else if (a.negative === true) out.push(['negative', true]);
  else {
    if (a.nonnegative === true) out.push(['nonnegative', true]);
    if (a.nonpositive === true) out.push(['nonpositive', true]);
    if (a.real === true && a.integer !== true && a.nonnegative !== true && a.nonpositive !== true) out.push(['real', true]);
  }
  if (a.integer === false) out.push(['integer', false]);
  if (a.zero === false && a.positive !== true && a.negative !== true && a.integer !== false) out.push(['zero', false]);
  if (a.commutative === false) out.push(['commutative', false]);
  if (a.polar === true) out.push(['polar', true]);
  return out;
}

/**
 * The assumptions a symbol is created with in SymPy (the given ones, and
 * commutative unless it is not); undefined for other nodes.
 */
export function symbolAssumptionFacts(e: Expr): Record<string, boolean> | undefined {
  if (!(e instanceof Sym) || e instanceof WildFunction) return undefined;
  return { commutative: true, ...Object.fromEntries(givenAssumptions(e)) };
}

/** SymPy `_print_Symbol` of the repr printer (Dummy adds its index like an assumption). */
function symbolRepr(e: Sym, cls: string): string {
  const items = [pyRepr(e.name), ...givenAssumptions(e).map(([k, v]) => `${k}=${v ? 'True' : 'False'}`)];
  if (e instanceof Dummy) items.push(`dummy_index=${e.dummyIndex}`);
  return `${cls}(${items.join(', ')})`;
}

/** SymPy `_print_Float`: the digits that round-trip and the precision. */
function floatRepr(e: Float): string {
  return `Float('${toStr(e.mpf, reprDps(e.prec))}', precision=${e.prec})`;
}

function numberRepr(e: Rational): string {
  if (e.q === 1n) return `Integer(${e.p})`;
  return `Rational(${e.p}, ${e.q})`;
}

const SYMBOL_PLUS = (dir: string): BasicView => ({ cls: 'Symbol', args: [], isExpr: true, str: dir, repr: `Symbol(${pyRepr(dir)})` });

/** The free symbols of an expression in SymPy's order (sorted by name). */
const sortedFreeSymbols = (e: Expr): Sym[] => [...impl.freeSymbols(e)].sort((u, v) => Number(u.name > v.name) - Number(u.name < v.name));

/** The integrand and the limits of nested integrals (SymPy keeps them in one Integral, innermost first). */
function integralLimits(e: Integral): [Expr, Expr[][]] {
  const limits: Expr[][] = [];
  let cur: Expr = e;
  while (cur instanceof Integral) {
    const lim = cur.limits;
    limits.push(lim ? [cur.variable, ...lim] : [cur.variable]);
    cur = cur.integrand;
  }
  return [cur, limits.reverse()];
}

/** The view of a node whose arguments SymPy groups differently (limits, pieces, ...); undefined for the others. */
function structured(e: Expr, v: (x: Expr) => BasicView): [string, BasicView[], boolean] | undefined {
  if (e instanceof Piecewise) {
    const pairs = e.pairs.map(([x, c]) => {
      const [vx, vc] = [v(x), v(c)];
      return container('ExprCondPair', [vx, vc], `(${vx.str}, ${vc.str})`);
    });
    return ['Piecewise', pairs, true];
  }
  if (e instanceof Integral) {
    const [f, limits] = integralLimits(e);
    return ['Integral', [v(f), ...limits.map((l) => tuple(l.map(v)))], true];
  }
  if (e instanceof Derivative) return ['Derivative', [v(e.expr), ...e.variableCount.map(([x, n]) => tuple([v(x), v(Rational.of(BigInt(n)))]))], true];
  if (e instanceof Limit) return ['Limit', [v(e.expr), v(e.variable), v(e.point), SYMBOL_PLUS(e.dir)], true];
  if (e instanceof Order) {
    // the arguments are the expression, then the variables and the point (all the free symbols at 0 when absent)
    const rest = e.args.slice(1);
    const vars = rest.length ? rest.slice(0, -1) : sortedFreeSymbols(e.expr);
    const point = rest.length ? at(rest, rest.length - 1) : S.Zero;
    return ['Order', [v(e.expr), ...vars.map((x) => tuple([v(x), v(point)]))], true];
  }
  if (e instanceof Concrete) return [e.kind2, [v(e.function), ...e.limits.map((l) => tuple(l.map(v)))], true];
  if (e instanceof ExtensionExpr) {
    if (e.name === 'Lambda') return ['Lambda', [tuple(e.args.slice(0, -1).map(v)), v(at(e.args, e.args.length - 1))], true];
    if (e.name === 'Subs') {
      const n = (e.args.length - 1) / 2;
      return ['Subs', [v(at(e.args, 0)), tuple(e.args.slice(1, 1 + n).map(v)), tuple(e.args.slice(1 + n).map(v))], true];
    }
    if (e.name.startsWith('Q.')) {
      const pred: BasicView = { cls: 'Predicate', args: [], isExpr: false, str: e.name, repr: e.name };
      return ['AppliedPredicate', [pred, ...e.args.map(v)], false];
    }
  }
  const cls = setClass(e);
  if (cls === 'ImageSet') {
    const [x, f, base] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
    const vx = v(x);
    const vf = v(f);
    const lambda: BasicView = { cls: 'Lambda', args: [tuple([vx]), vf], isExpr: true, str: `Lambda(${vx.str}, ${vf.str})` };
    return ['ImageSet', [lambda, v(base)], false];
  }
  return undefined;
}

/** SymPy `args_cnc(split_1=True)`: a negative numeric coefficient other than -1 is split into -1 and its absolute value. */
function splitNegativeOne(factors: Expr[]): Expr[] {
  const [c, ...rest] = factors;
  if (c === undefined || !isNum(c) || !c.isNegative || (c instanceof Rational && c.p === -1n && c.q === 1n)) return factors;
  return [S.NegOne, numNeg(c), ...rest];
}

/** A matrix as the repr printer sees it (the matrices layer is above this one). */
export interface ReprMatrix {
  readonly rows: number;
  readonly cols: number;
  get(i: number, j: number): Expr;
}
const isMatrixLike = (m: unknown): m is ReprMatrix => typeof m === 'object' && m !== null && 'rows' in m && 'cols' in m && 'get' in m && typeof m.get === 'function';

/** SymPy `_print_MatrixBase`: the class and the rows (or the shape of an empty matrix). */
function matrixRepr(m: ReprMatrix, cls: string, item: (e: Expr) => string): string {
  if ((m.rows === 0) !== (m.cols === 0)) return `${cls}(${m.rows}, ${m.cols}, [])`;
  const rows: string[] = [];
  for (let i = 0; i < m.rows; i++) {
    const row: string[] = [];
    for (let j = 0; j < m.cols; j++) row.push(item(m.get(i, j)));
    rows.push(`[${row.join(', ')}]`);
  }
  return `${cls}([${rows.join(', ')}])`;
}

/**
 * SymPy's view of an expression ({@link BasicView}). With `printOrder` the
 * terms of sums and the factors of products are in printing order (as
 * srepr prints them); otherwise they are in SymPy's argument order.
 */
export function basicView(e: Expr, printOrder = false): BasicView {
  const v = (x: Expr): BasicView => basicView(x, printOrder);
  const text = str(e);
  const atom = (cls: string, repr: string, isExpr = true): BasicView => ({ cls, args: [], isExpr, str: text, repr, expr: e });
  const node = (cls: string, args: readonly BasicView[], isExpr = true): BasicView => ({ cls, args, isExpr, str: text, expr: e });
  if (e instanceof Rational) return atom(sympyClassName(e), numberRepr(e));
  if (e instanceof Float) return atom('Float', floatRepr(e));
  if (e instanceof Constant || e instanceof Special) return atom(sympyClassName(e), text);
  if (e instanceof BoolAtom) return atom(sympyClassName(e), e.value ? 'true' : 'false', false);
  if (e instanceof Sym) {
    // SymPy _print_WildFunction: only the name
    if (e instanceof WildFunction) return atom('WildFunction', `WildFunction(${pyRepr(e.name)})`);
    const cls = e instanceof Wild ? 'Wild' : e instanceof Dummy ? 'Dummy' : 'Symbol';
    return atom(cls, symbolRepr(e, cls));
  }
  if (e instanceof Add && printOrder) return node('Add', asOrderedTerms(e).map(v));
  if (e instanceof Mul && printOrder) return node('Mul', splitNegativeOne(asOrderedFactors(e)).map(v));
  if (e instanceof Rel || e instanceof BoolOp) return node(e instanceof Rel ? sympyClassName(e) : e.className, e.args.map(v), false);
  if (e instanceof UndefFn) return { ...node(e.name, e.args.map(v)), head: `Function(${pyRepr(e.name)})` };
  const s = structured(e, v);
  if (s) return node(s[0], s[1], s[2]);
  if (e instanceof ExtensionExpr) {
    const m: unknown = Reflect.get(e, 'matrix');
    if (isMatrixLike(m)) return { ...node('ImmutableDenseMatrix', []), repr: matrixRepr(m, 'ImmutableDenseMatrix', (x) => srepr(x)) };
    if (e.atomClass) return atom(e.name, `${e.name}(${pyRepr(text)})`, false);
  }
  const set = setClass(e);
  // SymPy keeps the sets of a union or an intersection sorted (by their infimum)
  if (set !== undefined) return e.args.length === 0 ? atom(set, set, false) : node(set, (set === 'Union' || set === 'Intersection' ? setArgsOrdered(e.args) : e.args).map(v), false);
  if (e instanceof ExtensionExpr) return node(e.name, e.args.map(v), e.name !== 'Tuple' && e.name !== 'Dict');
  // Add, Mul, Pow, exp and the functions
  return node(sympyClassName(e), sympyArgs(e).map(v));
}

/** The srepr form of a view. */
const viewRepr = (view: BasicView): string => view.repr ?? `${view.head ?? view.cls}(${view.args.map(viewRepr).join(', ')})`;

const isList = (v: ReprPrintable): v is readonly ReprPrintable[] => Array.isArray(v);

/** What `srepr` prints: expressions, matrices, lists, dicts, sets, strings, numbers, booleans and null (Python None). */
export type ReprPrintable = Expr | number | bigint | boolean | string | null | ReprMatrix | readonly ReprPrintable[] | ReadonlyMap<ReprPrintable, ReprPrintable> | ReadonlySet<ReprPrintable>;

/**
 * SymPy `srepr(expr)`: the expression as the SymPy constructor calls that
 * rebuild it (`eval(srepr(expr)) == expr` in Python):
 * `srepr(x + 2)` is `Add(Symbol('x'), Integer(2))`.
 *
 * Lists print as lists, `Map`s as dicts and `Set`s as sets, with their items
 * in srepr form; a JS number is a Python int (`2`), a string prints with its
 * quotes, booleans and null as `True`, `False` and `None`.
 */
export function srepr(expr: ReprPrintable): string {
  if (typeof expr === 'string') return pyRepr(expr);
  if (typeof expr === 'number' || typeof expr === 'bigint') return String(expr);
  if (typeof expr === 'boolean') return expr ? 'True' : 'False';
  if (expr === null) return 'None';
  if (expr instanceof Expr) return viewRepr(basicView(expr, true));
  if (isList(expr)) return `[${expr.map(srepr).join(', ')}]`;
  if (isMatrixLike(expr)) return matrixRepr(expr, 'MutableDenseMatrix', (x) => srepr(x));
  if (expr instanceof Map) return `{${[...expr].map(([k, v]) => `${srepr(k)}: ${srepr(v)}`).join(', ')}}`;
  return expr.size ? `{${[...expr].map(srepr).join(', ')}}` : 'set()';
}
