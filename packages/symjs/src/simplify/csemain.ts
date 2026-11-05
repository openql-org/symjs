// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/simplify/cse_main.py and cse_opts.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file Common subexpression elimination (a port of SymPy's cse_main):
 * cse with tree_cse, opt_cse, match_common_args and FuncArgTracker, and the
 * postprocessors cse_separate and cse_release_variables.
 */

import type { ExprLike, RelOp, SpecialName } from '../core/nodes';
import { Add, Expr, Constant, Dummy, ExtensionExpr, Float, Mul, Order, Pow, Rational, Rel, S, Special, Sym, UndefFn, Wild } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sympify } from '../core/ops';
import { ordered } from '../core/match';
import { argsCncSplit } from '../core/methods';
import { freeSymbols, rebuild } from '../core/traverse';
import { BoolAtom } from '../core/nodes';
import { str } from '../printing/str';
import { parse as parseExpr } from '../parsing/parser';
import { numberedSymbols, topologicalSort } from '../utilities/iterables';
import { Matrix } from '../matrices/matrix';
import { MutableDenseMatrix } from '../matrices/mutable';
import {
  ImmutableMatrixNode,
  InverseNode,
  MatAddNode,
  MatMulNode,
  MatPowNode,
  MatrixElementNode,
  MatrixExpr,
  MatrixSymbolNode,
} from '../matrices/expressions/matexpr';
import { CRootOf } from '../polys/rootof';
import { Indexed } from '../core/indexed';
import { className } from './rewrite';
import { factorTerms, subPost, subPre } from './exprtools';
import { at, cast, expectType, first, getOrThrow } from '../core/guard';

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/** A symbol that names a common subexpression: a Sym, or a MatrixSymbol for a matrix expression. */
export type CseSymbol = Sym | MatrixSymbolNode;
/** One replacement of {@link cse}: the symbol and the subexpression it stands for. */
export type CseReplacement = [CseSymbol, Expr];
/** An expression handed to {@link cse}: an expression (or a value sympify accepts) or an explicit matrix. */
export type CseItem = ExprLike | Matrix;
/** A reduced expression: an expression, or a matrix of the same kind as the input matrix. */
export type CseReduced = Expr | Matrix;
/** The result of {@link cse}: the replacements and the reduced expressions. */
export type CseResult = [CseReplacement[], CseReduced[]];
/** A (preprocessor, postprocessor) pair; `null` stands for no transformation. */
export type CseOptimization = readonly [((e: Expr) => Expr) | null, ((e: Expr) => Expr) | null];
/** The input of {@link cse} with `list: false`. */
export type CseHomogeneousInput = CseItem | string | readonly CseItem[] | ReadonlySet<CseItem> | ReadonlyMap<unknown, CseItem>;
/** The reduced expressions of {@link cse} with `list: false`: the same kind of value as the input. */
export type CseHomogeneous<T> = T extends string
  ? string
  : T extends Matrix
    ? Matrix
    : T extends ReadonlyMap<infer K, CseItem>
      ? Map<K, CseReduced>
      : T extends ReadonlySet<CseItem>
        ? Set<CseReduced>
        : T extends readonly CseItem[]
          ? CseReduced[]
          : Expr;

/** Options of {@link cse} (SymPy's keyword arguments). */
export interface CseOptions {
  /** The symbols naming the subexpressions (default `x0, x1, ...`); must not run out. */
  symbols?: Iterable<Sym>;
  /** (preprocessor, postprocessor) pairs, or 'basic' for sub_pre/sub_post and factor_terms. */
  optimizations?: readonly CseOptimization[] | 'basic';
  /** 'canonical' (default) orders the arguments of sums and products; 'none' keeps their internal order. */
  order?: 'canonical' | 'none';
  /** Subexpressions containing any of these symbols are not replaced. */
  ignore?: Iterable<Expr>;
  /** false: the reduced expressions have the type of the input (default true: a list). */
  list?: boolean;
}

// ---------------------------------------------------------------------------
// SymPy's view of an expression: class names, argument order (Basic.compare)
// ---------------------------------------------------------------------------

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

const CONSTANT_CLASSES: Readonly<Record<string, string>> = { E: 'Exp1', pi: 'Pi', I: 'ImaginaryUnit' };
const SPECIAL_CLASSES: Readonly<Record<SpecialName, string>> = { oo: 'Infinity', '-oo': 'NegativeInfinity', zoo: 'ComplexInfinity', nan: 'NaN' };
const REL_CLASSES: Readonly<Record<RelOp, string>> = {
  Eq: 'Equality',
  Ne: 'Unequality',
  Lt: 'StrictLessThan',
  Gt: 'StrictGreaterThan',
  Le: 'LessThan',
  Ge: 'GreaterThan',
};

/** SymPy's class name of an expression (`type(e).__name__`). */
export function sympyClassName(e: Expr): string {
  if (e instanceof Rational) {
    if (e.isZero) return 'Zero';
    if (e.p === 1n && e.q === 1n) return 'One';
    if (e.p === -1n && e.q === 1n) return 'NegativeOne';
    if (e.p === 1n && e.q === 2n) return 'Half';
    return e.isInteger ? 'Integer' : 'Rational';
  }
  if (e instanceof Float) return 'Float';
  if (e instanceof Constant) return CONSTANT_CLASSES[e.name] ?? e.name;
  if (e instanceof Special) return SPECIAL_CLASSES[e.name];
  if (e instanceof Wild) return 'Wild';
  if (e instanceof Dummy) return 'Dummy';
  if (e instanceof Sym) return 'Symbol';
  if (e instanceof BoolAtom) return e.value ? 'BooleanTrue' : 'BooleanFalse';
  if (e instanceof Rel) return REL_CLASSES[e.op];
  return className(e);
}

/** The superclasses of a SymPy class (its mro after the class itself), by the kind of node. */
export function sympyClassBases(e: Expr): string[] {
  const atomic = ['AtomicExpr', 'Atom', 'Expr', 'Basic'];
  if (e instanceof Rational) {
    const n = sympyClassName(e);
    if (n === 'Integer') return ['Rational', 'Number', ...atomic];
    if (n === 'Rational') return ['Number', ...atomic];
    if (n === 'Half') return ['RationalConstant', 'Rational', 'Number', ...atomic];
    return ['IntegerConstant', 'Integer', 'Rational', 'Number', ...atomic];
  }
  if (e instanceof Float) return ['Number', ...atomic];
  if (e instanceof Constant) return e.name === 'I' ? atomic : ['NumberSymbol', ...atomic];
  if (e instanceof Special) return e.name === 'zoo' ? atomic : ['Number', ...atomic];
  if (e instanceof Sym) return [...(e instanceof Wild || e instanceof Dummy ? ['Symbol'] : []), 'AtomicExpr', 'Atom', 'Expr', 'Boolean', 'Basic'];
  if (e instanceof BoolAtom) return ['BooleanAtom', 'Boolean', 'Basic'];
  if (e instanceof Rel) return ['Relational', 'Boolean', 'Basic'];
  if (e instanceof Add || e instanceof Mul) return ['Expr', 'AssocOp', 'Basic'];
  if (isExp(e)) return ['ExpBase', 'DefinedFunction', 'Function', 'Application', 'Expr', 'Basic'];
  if (e instanceof Pow) return ['Expr', 'Basic'];
  if (e.kind === 'Fn' || e.kind === 'Piecewise') return ['DefinedFunction', 'Function', 'Application', 'Expr', 'Basic'];
  if (e instanceof UndefFn) return ['AppliedUndef', 'Function', 'Application', 'Expr', 'Basic'];
  return ['Expr', 'Basic'];
}

/** SymPy's basic.ordering_of_classes (the canonical order of Add and Mul arguments). */
const ORDERING_OF_CLASSES = [
  'Zero', 'One', 'Half', 'Infinity', 'NaN', 'NegativeOne', 'NegativeInfinity',
  'Integer', 'Rational', 'Float',
  'Exp1', 'Pi', 'ImaginaryUnit',
  'Symbol', 'Wild',
  'Pow', 'Mul', 'Add',
  'Derivative', 'Integral',
  'Abs', 'Sign', 'Sqrt',
  'Floor', 'Ceiling',
  'Re', 'Im', 'Arg',
  'Conjugate',
  'Exp', 'Log',
  'Sin', 'Cos', 'Tan', 'Cot', 'ASin', 'ACos', 'ATan', 'ACot',
  'Sinh', 'Cosh', 'Tanh', 'Coth', 'ASinh', 'ACosh', 'ATanh', 'ACoth',
  'RisingFactorial', 'FallingFactorial',
  'factorial', 'binomial',
  'Gamma', 'LowerGamma', 'UpperGamma', 'PolyGamma',
  'Erf',
  'Chebyshev', 'Chebyshev2',
  'Function', 'WildFunction',
  'Lambda',
  'Order',
  'Equality', 'Unequality', 'StrictGreaterThan', 'StrictLessThan',
  'GreaterThan', 'LessThan',
];

const cmp = <T extends string | number | bigint>(a: T, b: T): number => (a > b ? 1 : a < b ? -1 : 0);

/** SymPy _cmp_name: by ordering_of_classes when either name is listed, else by name. */
function cmpName(n1: string, n2: string): number {
  if (n1 === n2) return 0;
  const unknown = ORDERING_OF_CLASSES.length + 1;
  const i = (n: string) => {
    const k = ORDERING_OF_CLASSES.indexOf(n);
    return k < 0 ? unknown : k;
  };
  const [i1, i2] = [i(n1), i(n2)];
  if (i1 === unknown && i2 === unknown) return cmp(n1, n2);
  return cmp(i1, i2);
}

type Content = Expr | string | number | bigint;

/** SymPy _hashable_content (symbol names, number values, otherwise the arguments in SymPy's order). */
function hashableContent(e: Expr): Content[] {
  if (e instanceof Rational) return [e.p, e.q];
  if (e instanceof Float) return [e.toNumber()];
  if (e instanceof Sym) return [e.name];
  // an atom of an extension (a matrix name Str, ...) by its printed form (SymPy Str._hashable_content is (name,))
  if (e instanceof ExtensionExpr && e.args.length === 0) return [str(e)];
  return [...sympyArgs(e)];
}

/** SymPy Basic.compare: class names, then the length and items of the hashable content. */
export function basicCompare(a: Expr, b: Expr): number {
  if (a === b) return 0;
  const c = cmpName(sympyClassName(a), sympyClassName(b));
  if (c) return c;
  const st = hashableContent(a);
  const ot = hashableContent(b);
  if (st.length !== ot.length) return cmp(st.length, ot.length);
  for (let i = 0; i < st.length; i++) {
    const l = at(st, i);
    const r = at(ot, i);
    const d = typeof l === 'object' && typeof r === 'object' ? basicCompare(l, r) : cmp(String(l), String(r));
    if (d) return d;
  }
  return 0;
}

/** SymPy's `expr.args`: exp(x) has the argument x; sums and products are in Basic.compare order. */
export function sympyArgs(e: Expr): readonly Expr[] {
  if (isExp(e)) return [at(e.args, 1)];
  if (e instanceof Add) return [...e.args].sort(basicCompare);
  if (e instanceof Mul) {
    const c = e.args.filter((a) => a.isCommutative).sort(basicCompare);
    return [...c, ...e.args.filter((a) => !a.isCommutative)];
  }
  return e.args;
}

/** SymPy `expr.func(*args)` for the arguments of {@link sympyArgs}. */
export function sympyRebuild(e: Expr, args: readonly Expr[]): Expr {
  if (isExp(e)) return exp(first(args));
  return rebuild(e, args);
}

// ---------------------------------------------------------------------------
// Unevaluated nodes and the tree of cse
// ---------------------------------------------------------------------------

type Head = 'Add' | 'Mul' | 'Pow' | 'MatAdd' | 'MatPow';

let unevaluatedCount = 0;

/** SymPy cse_main.Unevaluated: a head with arguments, compared by identity. */
class Unevaluated {
  readonly id = ++unevaluatedCount;
  constructor(
    readonly head: Head,
    readonly args: readonly Node[],
  ) {}
  /** The evaluated node of these (rebuilt) arguments. */
  build(args: readonly Expr[]): Expr {
    switch (this.head) {
      case 'Add':
        return add(...args);
      case 'Mul':
        return mul(...args);
      case 'Pow':
        return pow(at(args, 0), at(args, 1));
      case 'MatAdd':
        return new MatAddNode(args);
      case 'MatPow':
        return new MatPowNode(at(args, 0), at(args, 1));
    }
  }
}

/** A Tuple of the entries of a matrix (SymPy Tuple(*m.flat())). */
class Entries {
  constructor(readonly items: readonly Node[]) {}
}

/**
 * SymPy Mul(c, Mul(*nc), evaluate=False): a product with its commutative
 * part split off. Compared like an expression.
 */
class SplitMul {
  constructor(readonly args: readonly [Expr, Expr]) {}
}

type Node = Expr | Unevaluated;
type Sub = Node | SplitMul;
type Top = Node | Entries;

/** Map key of a node: expressions compare structurally, unevaluated nodes by identity. */
const keyOf = (n: Node): string => (n instanceof Unevaluated ? `\u0000${n.id}` : n.key);

function nodeFreeSymbolKeys(n: Node, out = new Set<string>()): Set<string> {
  if (n instanceof Unevaluated) for (const a of n.args) nodeFreeSymbolKeys(a, out);
  else for (const s of freeSymbols(n)) out.add(s.key);
  return out;
}

/** A dictionary keyed by nodes (SymPy dict / set of Basic and Unevaluated objects). */
class NodeMap<V> {
  readonly #m = new Map<string, V>();
  get(n: Node): V | undefined {
    return this.#m.get(keyOf(n));
  }
  set(n: Node, v: V): void {
    this.#m.set(keyOf(n), v);
  }
}

const isMatrixExpr = (e: Expr): boolean => e instanceof MatrixExpr;
const negate = (e: Expr): Expr => mul(-1, e);

/**
 * The shape of a matrix-valued expression (sums, products and powers of
 * matrices are MatAdd, MatMul and MatPow, which the arithmetic builds as in SymPy).
 */
function matrixShape(e: Expr): [Expr, Expr] | undefined {
  return e instanceof MatrixExpr ? e.shape : undefined;
}

// ---------------------------------------------------------------------------
// Pre- and postprocessing
// ---------------------------------------------------------------------------

/** SymPy basic_optimizations: (sub_pre, sub_post) and (factor_terms, None). */
const BASIC_OPTIMIZATIONS: readonly CseOptimization[] = [
  [subPre, subPost],
  [(e) => factorTerms(e), null],
];

/** SymPy preprocess_for_cse: the preprocessors in order. */
export function preprocessForCse(expr: Expr, optimizations: readonly CseOptimization[]): Expr {
  let e = expr;
  for (const [pre] of optimizations) if (pre) e = pre(e);
  return e;
}

/** SymPy postprocess_for_cse: the postprocessors in reverse order. */
export function postprocessForCse(expr: Expr, optimizations: readonly CseOptimization[]): Expr {
  let e = expr;
  for (const [, post] of [...optimizations].reverse()) if (post) e = post(e);
  return e;
}

// ---------------------------------------------------------------------------
// FuncArgTracker and match_common_args
// ---------------------------------------------------------------------------

/** OrderedSet intersection / difference (keeping the order of a). */
const inter = (a: ReadonlySet<number>, b: ReadonlySet<number>): Set<number> => new Set([...a].filter((x) => b.has(x)));
const diff = (a: ReadonlySet<number>, b: ReadonlySet<number>): Set<number> => new Set([...a].filter((x) => !b.has(x)));

/**
 * SymPy FuncArgTracker: maps functions to their arguments and arguments to
 * the functions using them, with arguments numbered by value.
 */
export class FuncArgTracker {
  readonly valueNumbers = new NodeMap<number>();
  readonly valueNumberToValue: Node[] = [];
  readonly argToFuncset: Set<number>[] = [];
  readonly funcToArgset: Set<number>[] = [];

  constructor(funcs: readonly Expr[]) {
    for (const [funcI, func] of funcs.entries()) {
      const funcArgset = new Set<number>();
      for (const funcArg of sympyArgs(func)) {
        const n = this.getOrAddValueNumber(funcArg);
        funcArgset.add(n);
        at(this.argToFuncset, n).add(funcI);
      }
      this.funcToArgset.push(funcArgset);
    }
  }

  /** The arguments of argset ordered by their value numbers. */
  getArgsInValueOrder(argset: ReadonlySet<number>): Node[] {
    return [...argset].sort((a, b) => a - b).map((n) => at(this.valueNumberToValue, n));
  }

  /** The value number of value, assigned when it is new. */
  getOrAddValueNumber(value: Node): number {
    const n = this.valueNumbers.get(value);
    if (n !== undefined) return n;
    const k = this.valueNumberToValue.length;
    this.valueNumbers.set(value, k);
    this.valueNumberToValue.push(value);
    this.argToFuncset.push(new Set());
    return k;
  }

  /** Remove the function funcI from the argument-to-function mapping. */
  stopArgTracking(funcI: number): void {
    for (const arg of at(this.funcToArgset, funcI)) at(this.argToFuncset, arg).delete(funcI);
  }

  /**
   * The functions (numbered at least minFuncI) with at least two arguments in
   * common with argset, mapped to the number of common arguments.
   */
  getCommonArgCandidates(argset: ReadonlySet<number>, minFuncI = 0): Map<number, number> {
    const countMap = new Map<number, number>();
    if (!argset.size) return countMap;
    const funcsets = [...argset].map((arg) => at(this.argToFuncset, arg));
    let largest = first(funcsets);
    for (const f of funcsets) if (f.size > largest.size) largest = f;
    for (const funcset of funcsets) {
      if (funcset === largest) continue;
      for (const funcI of funcset) if (funcI >= minFuncI) countMap.set(funcI, (countMap.get(funcI) ?? 0) + 1);
    }
    // the smaller of the two containers is iterated
    // (sorted by size, stable: the largest funcset first on a tie)
    const largestFirst = largest.size <= countMap.size;
    const smaller: Iterable<number> = largestFirst ? [...largest] : [...countMap.keys()];
    for (const funcI of smaller) {
      const n = countMap.get(funcI);
      // a function not counted yet cannot be in the output
      if (n === undefined || (!largestFirst && !largest.has(funcI))) continue;
      countMap.set(funcI, n + 1);
    }
    return new Map([...countMap].filter(([, v]) => v >= 2));
  }

  /** The functions whose arguments contain argset, optionally only those of restrictToFuncset. */
  getSubsetCandidates(argset: ReadonlySet<number>, restrictToFuncset?: ReadonlySet<number>): Set<number> {
    const args = [...argset];
    let indices = new Set(at(this.argToFuncset, first(args)));
    if (restrictToFuncset !== undefined) indices = inter(indices, restrictToFuncset);
    for (const arg of args.slice(1)) indices = inter(indices, at(this.argToFuncset, arg));
    return indices;
  }

  /** Give the function funcI the arguments newArgset. */
  updateFuncArgset(funcI: number, newArgset: Iterable<number>): void {
    const newArgs = new Set(newArgset);
    const oldArgs = at(this.funcToArgset, funcI);
    for (const deleted of diff(oldArgs, newArgs)) at(this.argToFuncset, deleted).delete(funcI);
    for (const added of diff(newArgs, oldArgs)) at(this.argToFuncset, added).add(funcI);
    oldArgs.clear();
    for (const a of newArgs) oldArgs.add(a);
  }
}

/**
 * SymPy match_common_args: extract the common arguments of the given sums
 * (or products) as new unevaluated sums (products), recorded in optSubs.
 */
function matchCommonArgs(head: 'Add' | 'Mul', funcsIn: readonly Expr[], optSubs: NodeMap<Sub>): void {
  // whole-function subexpressions come before the functions using them
  const funcs = funcsIn
    .map((f, i) => [f, i] as const)
    .sort((a, b) => sympyArgs(a[0]).length - sympyArgs(b[0]).length || a[1] - b[1])
    .map(([f]) => f);
  const tracker = new FuncArgTracker(funcs);
  const changed = new Set<number>();
  // (the products are commutative, so never matrix products)
  const headOf = (f: Expr): Head => (f instanceof MatAddNode ? 'MatAdd' : head);
  for (let i = 0; i < funcs.length; i++) {
    const fi = at(funcs, i);
    const counts = tracker.getCommonArgCandidates(at(tracker.funcToArgset, i), i + 1);
    // smaller matches are combined first
    const candidates = new Set([...counts.keys()].sort((a, b) => getOrThrow(counts, a) - getOrThrow(counts, b) || a - b));
    while (candidates.size) {
      const j = first([...candidates]);
      candidates.delete(j);
      const comArgs = inter(at(tracker.funcToArgset, i), at(tracker.funcToArgset, j));
      // a set of common arguments may have been combined in a previous iteration
      if (comArgs.size <= 1) continue;
      const diffI = diff(at(tracker.funcToArgset, i), comArgs);
      let comFuncNumber: number;
      if (diffI.size) {
        // the common function is unevaluated to allow recursive matches
        const comFunc = new Unevaluated(headOf(fi), tracker.getArgsInValueOrder(comArgs));
        comFuncNumber = tracker.getOrAddValueNumber(comFunc);
        tracker.updateFuncArgset(i, [...diffI, comFuncNumber]);
        changed.add(i);
      } else {
        // the whole expression is a common subexpression
        comFuncNumber = tracker.getOrAddValueNumber(fi);
      }
      const diffJ = diff(at(tracker.funcToArgset, j), comArgs);
      tracker.updateFuncArgset(j, [...diffJ, comFuncNumber]);
      changed.add(j);
      for (const k of tracker.getSubsetCandidates(comArgs, candidates)) {
        const diffK = diff(at(tracker.funcToArgset, k), comArgs);
        tracker.updateFuncArgset(k, [...diffK, comFuncNumber]);
        changed.add(k);
      }
    }
    if (changed.has(i)) optSubs.set(fi, new Unevaluated(headOf(fi), tracker.getArgsInValueOrder(at(tracker.funcToArgset, i))));
    tracker.stopArgTracking(i);
  }
}

// ---------------------------------------------------------------------------
// opt_cse
// ---------------------------------------------------------------------------

/** SymPy is_Atom: no arguments (an Indexed object is an atom too). */
export const isSympyAtom = (e: Expr): boolean => sympyArgs(e).length === 0 || e instanceof Indexed;
const isAtom = isSympyAtom;

/** An ordered set of expressions (SymPy OrderedSet). */
class ExprSet {
  readonly #m = new Map<string, Expr>();
  add(e: Expr): void {
    if (!this.#m.has(e.key)) this.#m.set(e.key, e);
  }
  values(): Expr[] {
    return [...this.#m.values()];
  }
}

/**
 * SymPy opt_cse: substitutions that give cse more opportunities (negated
 * sums and products, negative powers, common arguments of sums and products).
 */
function optCse(exprs: readonly Top[]): NodeMap<Sub> {
  const optSubs = new NodeMap<Sub>();
  const adds = new ExprSet();
  const muls = new ExprSet();
  const seen = new Set<string>();
  const collapsible = new ExprSet();

  const findOpts = (n: Top): void => {
    if (n instanceof Entries) {
      n.items.forEach(findOpts);
      return;
    }
    // (cse only meets unevaluated nodes in the tree it builds)
    const e = cast(n, Expr);
    if (isAtom(e) || e instanceof Order) return;
    // an explicit matrix is iterable: its entries are searched
    if (e instanceof ImmutableMatrixNode) {
      e.args.forEach(findOpts);
      return;
    }
    if (seen.has(e.key)) return;
    seen.add(e.key);
    sympyArgs(e).forEach(findOpts);
    let expr = e;
    if (!isMatrixExpr(expr) && couldExtractMinusSign(expr)) {
      const negExpr = expr instanceof Add ? add(...expr.args.map(negate)) : negate(expr);
      if (!isAtom(negExpr)) {
        optSubs.set(expr, new Unevaluated('Mul', [S.NegOne, negExpr]));
        seen.add(negExpr.key);
        expr = negExpr;
      }
    }
    if (expr instanceof Mul || expr instanceof MatMulNode) {
      if (expr.args.length === 1) collapsible.add(expr);
      else muls.add(expr);
    } else if (expr instanceof Add || expr instanceof MatAddNode) {
      if (expr.args.length === 1) collapsible.add(expr);
      else adds.add(expr);
    } else if (expr instanceof InverseNode) {
      // an Inverse is not treated as a MatPow
    } else if ((expr instanceof Pow && !isExp(expr)) || expr instanceof MatPowNode) {
      const [base, e2] = [at(expr.args, 0), at(expr.args, 1)];
      if (couldExtractMinusSign(e2)) {
        const inv = expr instanceof MatPowNode ? new MatPowNode(base, negate(e2)) : pow(base, negate(e2));
        optSubs.set(expr, new Unevaluated(expr instanceof MatPowNode ? 'MatPow' : 'Pow', [inv, S.NegOne]));
      }
    }
  };
  exprs.forEach(findOpts);

  // collapse sums and products of a single argument
  const coll = collapsible.values();
  const collKeys = new Set(coll.map((c) => c.key));
  const edges = coll.filter((s) => collKeys.has(first(s.args).key)).map((s) => [s, first(s.args)] as const);
  for (const e of topologicalSort([coll, edges]).reverse()) {
    const a = first(e.args);
    optSubs.set(e, optSubs.get(a) ?? a);
  }

  // split products into their commutative and noncommutative parts
  const commutativeMuls = new ExprSet();
  for (const m of muls.values()) {
    const [c, nc] = m instanceof MatMulNode ? [m.args.filter((a) => a.isCommutative), m.args.filter((a) => !a.isCommutative)] : argsCncSplit(m);
    if (!c.length) continue;
    const cMul = mul(...c);
    if (nc.length) {
      if (m instanceof MatMulNode) optSubs.set(m, new MatMulNode([cMul, ...nc]));
      else optSubs.set(m, cMul instanceof Rational && cMul.isOne ? mul(...nc) : new SplitMul([cMul, mul(...nc)]));
    }
    if (c.length > 1) commutativeMuls.add(cMul);
  }

  matchCommonArgs('Add', adds.values(), optSubs);
  matchCommonArgs('Mul', commutativeMuls.values(), optSubs);
  return optSubs;
}

// ---------------------------------------------------------------------------
// tree_cse
// ---------------------------------------------------------------------------

const argsOf = (n: Sub): readonly Node[] => (n instanceof Expr ? sympyArgs(n) : n.args);

/** SymPy tree_cse: replace the subexpressions met more than once, taking optSubs into account. */
function treeCse(
  exprs: readonly Top[],
  symbolsIn: Iterator<Sym>,
  optSubs: NodeMap<Sub>,
  order: 'canonical' | 'none',
  ignore: readonly Expr[],
): [CseReplacement[], Top[]] {
  const toEliminate = new Set<string>();
  const seen = new Set<string>();
  const excludedSymbols = new Set<string>();
  const ignoreKeys = ignore.map((s) => s.key);

  const findRepeated = (n: Node | Entries): void => {
    if (n instanceof Entries) {
      n.items.forEach(findRepeated);
      return;
    }
    if (n instanceof CRootOf) return;
    if (n instanceof Expr && (isAtom(n) || n instanceof Order || n instanceof MatrixSymbolNode || n instanceof MatrixElementNode)) {
      if (n instanceof Sym) excludedSymbols.add(n.name);
      return;
    }
    if (n instanceof ImmutableMatrixNode) {
      n.args.forEach(findRepeated);
      return;
    }
    const k = keyOf(n);
    if (seen.has(k)) {
      const free = ignoreKeys.length ? nodeFreeSymbolKeys(n) : new Set<string>();
      if (!ignoreKeys.some((ign) => free.has(ign))) {
        toEliminate.add(k);
        return;
      }
    }
    seen.add(k);
    argsOf(optSubs.get(n) ?? n).forEach(findRepeated);
  };
  exprs.forEach(findRepeated);

  // symbols that conflict with names in the expressions are skipped
  const nextSymbol = (): Sym => {
    for (;;) {
      const r = symbolsIn.next();
      if (r.done === true) throw new RangeError('Symbols iterator ran out of symbols.');
      if (!excludedSymbols.has(r.value.name)) return r.value;
    }
  };
  const replacements: CseReplacement[] = [];
  const subs = new Map<string, CseSymbol>();

  const orderedArgs = (expr: Sub): readonly Node[] => {
    if (order === 'none') return argsOf(expr);
    // SymPy splits a negative coefficient off (args_cnc); a product with one was negated by opt_cse first
    if (expr instanceof SplitMul) return expr.args;
    if (expr instanceof Mul || expr instanceof MatMulNode) {
      const [c, nc] = expr instanceof Mul ? argsCncSplit(expr) : [expr.args.filter((a) => a.isCommutative), expr.args.filter((a) => !a.isCommutative)];
      return c.length === 1 && first(c).equals(S.One) ? nc : [...ordered(c), ...nc];
    }
    if (expr instanceof Add || expr instanceof MatAddNode) return ordered(expr.args);
    return argsOf(expr);
  };

  const rebuildNode = (n: Node): Expr => {
    if (n instanceof Expr && isAtom(n)) return n;
    if (n instanceof ImmutableMatrixNode) return rebuild(n, n.args.map(rebuildNode));
    const k = keyOf(n);
    const s = subs.get(k);
    if (s !== undefined) return s;
    const expr = optSubs.get(n) ?? n;
    const args = orderedArgs(expr);
    const newArgs = args.map(rebuildNode);
    let newExpr: Expr;
    if (expr instanceof Unevaluated) newExpr = expr.build(newArgs);
    else if (expr instanceof SplitMul) newExpr = mul(...newArgs);
    else newExpr = newArgs.some((a, i) => a !== at(args, i)) ? sympyRebuild(expr, newArgs) : expr;
    if (!toEliminate.has(k)) return newExpr;
    const sym0 = nextSymbol();
    const shape = n instanceof Expr ? matrixShape(n) : undefined;
    const sym = shape ? new MatrixSymbolNode(sym0.name, shape[0], shape[1]) : sym0;
    subs.set(k, sym);
    replacements.push([sym, newExpr]);
    return sym;
  };
  const rebuildTop = (n: Top): Top => (n instanceof Entries ? new Entries(n.items.map(rebuildNode)) : rebuildNode(n));
  return [replacements, exprs.map(rebuildTop)];
}

// ---------------------------------------------------------------------------
// cse
// ---------------------------------------------------------------------------

/** The cse of a list of expressions (SymPy cse with list=True, without postprocess). */
const isItem = (v: unknown): v is CseItem => typeof v === 'number' || typeof v === 'bigint' || v instanceof Expr || v instanceof Matrix;
const isIterable = (v: unknown): v is Iterable<unknown> => typeof v === 'object' && v !== null && Symbol.iterator in v;

function cseList(exprsIn: unknown, options: CseOptions): CseResult {
  const xs = isItem(exprsIn) ? [exprsIn] : isIterable(exprsIn) ? [...exprsIn] : [exprsIn];
  if (!xs.every(isItem)) throw new TypeError('cse: expected expressions or matrices');
  const exprs: CseItem[] = xs;
  const items: Top[] = exprs.map((e) => (e instanceof Matrix ? new Entries(e.data) : sympify(e)));
  const opt = options.optimizations;
  const optimizations = opt === 'basic' ? BASIC_OPTIMIZATIONS : (opt ?? []);
  const each = (t: Top, f: (e: Expr) => Expr): Top => (t instanceof Entries ? new Entries(t.items.map((x) => f(cast(x, Expr)))) : f(cast(t, Expr)));
  const reduced = items.map((t) => each(t, (e) => preprocessForCse(e, optimizations)));
  const symbols = options.symbols === undefined ? numberedSymbols('x') : options.symbols[Symbol.iterator]();
  const optSubs = optCse(reduced);
  const [reps, red] = treeCse(reduced, symbols, optSubs, options.order ?? 'canonical', [...(options.ignore ?? [])]);
  const replacements = reps.map(([s, v]): CseReplacement => [s, postprocessForCse(v, optimizations)]);
  const out = red.map((t, i): CseReduced => {
    const p = each(t, (e) => postprocessForCse(e, optimizations));
    const m = at(exprs, i);
    if (!(p instanceof Entries) || !(m instanceof Matrix)) return cast(p, Expr);
    const f = (r: number, c: number): Expr => cast(at(p.items, r * m.cols + c), Expr);
    return m instanceof MutableDenseMatrix ? MutableDenseMatrix.fromFunction(m.rows, m.cols, f) : Matrix.fromFunction(m.rows, m.cols, f);
  });
  return [replacements, out];
}

const isCseResult = (v: unknown): v is CseResult => Array.isArray(v) && v.length === 2 && Array.isArray(v[0]);

/**
 * SymPy `cse(exprs, symbols=None, optimizations=None, postprocess=None,
 * order='canonical', ignore=(), list=True)`: common subexpression
 * elimination. Returns the replacements `[symbol, subexpression]` (a
 * subexpression may use the symbols of earlier ones) and the reduced
 * expressions. A single expression gives a list of one reduced expression;
 * with `list: false` the reduced expressions have the type of the input (an
 * expression, an array, a Set, a Map of expressions, a matrix or a string).
 * Explicit matrices keep their mutability. `postprocess` receives the two
 * results and its value is returned instead.
 */
export function cse(exprs: CseItem | Iterable<CseItem>, options?: CseOptions & { list?: true; postprocess?: undefined }): CseResult;
export function cse<R>(exprs: CseItem | Iterable<CseItem>, options: CseOptions & { list?: true; postprocess: (replacements: CseReplacement[], reduced: CseReduced[]) => R }): R;
export function cse<T extends CseHomogeneousInput>(
  exprs: T,
  options: CseOptions & { list: false; postprocess?: (replacements: CseReplacement[], reduced: CseReduced[]) => CseResult },
): [CseReplacement[], CseHomogeneous<T>];
export function cse(
  exprs: CseHomogeneousInput | Iterable<CseItem>,
  options: CseOptions & { postprocess?: (replacements: CseReplacement[], reduced: CseReduced[]) => unknown } = {},
): unknown {
  const run = (x: unknown): unknown => {
    const [r, e] = cseList(x, options);
    return options.postprocess ? options.postprocess(r, e) : [r, e];
  };
  if (options.list !== false) return run(exprs);
  // SymPy _cse_homogeneous: the reduced expressions in the type of the input
  const pairOf = (x: unknown): CseResult => expectType(run(x), isCseResult, 'the postprocess result');
  if (typeof exprs === 'string') {
    const [r, e] = pairOf(parseExpr(exprs));
    return [r, str(cast(first(e), Expr))];
  }
  if (exprs instanceof Map) {
    const entries = [...exprs.entries()];
    const [r, e] = pairOf(entries.map(([, v]) => v));
    return [r, new Map(entries.map(([k], i) => [k, at(e, i)]))];
  }
  if (exprs instanceof Set) {
    const [r, e] = pairOf(exprs);
    return [r, new Set(e)];
  }
  if (Array.isArray(exprs)) return pairOf(exprs);
  const [r, e] = pairOf(exprs);
  return [r, first(e)];
}

// ---------------------------------------------------------------------------
// postprocessors
// ---------------------------------------------------------------------------

/**
 * SymPy reps_toposort: the replacements ordered so that [k1, v1] comes
 * before [k2, v2] when k1 is a free symbol of v2.
 */
export function repsToposort(r: readonly (readonly [Expr, Expr])[]): [Expr, Expr][] {
  const edges: [number, number][] = [];
  for (const [c1, [k1]] of r.entries()) {
    for (const [c2, [, v2]] of r.entries()) if (nodeFreeSymbolKeys(v2).has(k1.key)) edges.push([c1, c2]);
  }
  return topologicalSort([[...r.keys()], edges]).map((i) => {
    const [k, v] = at(r, i);
    return [k, v];
  });
}

/**
 * SymPy cse_separate (a postprocess for {@link cse}): the reduced
 * expressions Eq(symbol, value) become replacements, all sorted by
 * {@link repsToposort}.
 */
export function cseSeparate(r: readonly (readonly [Expr, Expr])[], e: readonly CseReduced[]): [[Expr, Expr][], CseReduced[]] {
  const isDef = (w: CseReduced): w is Rel => w instanceof Rel && w.op === 'Eq' && w.lhs instanceof Sym;
  const defs = e.filter(isDef);
  return [repsToposort([...r, ...defs.map((w): [Expr, Expr] => [w.lhs, w.rhs])]), e.filter((w) => !isDef(w))];
}
