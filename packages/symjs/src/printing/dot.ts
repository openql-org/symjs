// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/dot.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's Graphviz printer: `dotprint` draws the tree of an
 * expression in the DOT language (one node per subexpression, an edge to
 * each argument), with the helpers `purestr`, `styleof`, `attrprint`,
 * `dotnode` and `dotedges`.
 */

import type { Expr } from '../core/nodes';
import type { BasicView } from './repr';
import { basicView } from './repr';
import { str } from './str';

/** The classes a style applies to: every node ('Basic'), the expressions ('Expr'), or the nodes a predicate selects. */
export type DotClass = 'Basic' | 'Expr' | ((e: Expr) => boolean);
/** Graphviz attributes of the nodes of the classes (SymPy `styles`: (class, attributes) pairs, later ones override). */
export type DotStyles = readonly (readonly [DotClass, Readonly<Record<string, string>>])[];

/** SymPy `default_styles`: blue ellipses, black for expressions. */
export const defaultStyles: DotStyles = [
  ['Basic', { color: 'blue', shape: 'ellipse' }],
  ['Expr', { color: 'black' }],
];

/** Python's str of a position tuple: `()`, `(0,)`, `(0, 1)`. */
const posStr = (pos: readonly number[]): string => (pos.length === 1 ? `(${pos[0]},)` : `(${pos.join(', ')})`);

/** SymPy `purestr` of a view: srepr of an atom, `Class(args...)` of the other nodes. */
function viewPurestr(v: BasicView): string {
  if (v.args.length === 0) return v.repr ?? `${v.cls}()`;
  return `${v.cls}(${v.args.map(viewPurestr).join(', ')})`;
}

/**
 * SymPy `purestr(x)`: a string that rebuilds the expression like srepr,
 * with the arguments in SymPy's order (`Add(Integer(2), Symbol('x'))`).
 */
export function purestr(x: Expr): string {
  return viewPurestr(basicView(x));
}

/** SymPy `purestr(x, with_args=True)`: the purestr of the expression and those of its arguments. */
export function purestrWithArgs(x: Expr): [string, string[]] {
  const v = basicView(x);
  return [viewPurestr(v), v.args.map(viewPurestr)];
}

const matches = (v: BasicView, cls: DotClass): boolean => {
  if (cls === 'Basic') return true;
  if (cls === 'Expr') return v.isExpr;
  return v.expr !== undefined && cls(v.expr);
};

function viewStyle(v: BasicView, styles: DotStyles): Record<string, string> {
  const style: Record<string, string> = {};
  for (const [cls, sty] of styles) if (matches(v, cls)) Object.assign(style, sty);
  return style;
}

/** SymPy `styleof(expr, styles)`: the merged attributes of the styles whose class the expression has. */
export function styleof(expr: Expr, styles: DotStyles = defaultStyles): Record<string, string> {
  return viewStyle(basicView(expr), styles);
}

/** SymPy `attrprint(d, delimiter=', ')`: `"key"="value"` pairs sorted by key. */
export function attrprint(d: Readonly<Record<string, string>>, delimiter = ', '): string {
  return Object.entries(d)
    .sort(([a], [b]) => Number(a > b) - Number(a < b))
    .map(([k, v]) => `"${k}"="${v}"`)
    .join(delimiter);
}

/** The options of {@link dotnode}. */
export interface DotNodeOptions {
  /** The styles (default {@link defaultStyles}). */
  readonly styles?: DotStyles;
  /** The label of an atom (default `str`). */
  readonly labelfunc?: (e: Expr) => string;
  /** The position of the node in the tree (the argument indices from the root). */
  readonly pos?: readonly number[];
  /** Distinguish equal subexpressions by their position (default true). */
  readonly repeat?: boolean;
}

function viewNode(v: BasicView, options: DotNodeOptions): string {
  const style = viewStyle(v, options.styles ?? defaultStyles);
  const labelfunc = options.labelfunc ?? str;
  // an atom is labelled with its str form, another node with its class
  style['label'] = v.args.length ? v.cls : v.expr ? labelfunc(v.expr) : v.str;
  let s = viewPurestr(v);
  if (options.repeat ?? true) s += `_${posStr(options.pos ?? [])}`;
  return `"${s}" [${attrprint(style)}];`;
}

/** SymPy `dotnode(expr, styles, labelfunc, pos, repeat)`: the DOT line of one node. */
export function dotnode(expr: Expr, options: DotNodeOptions = {}): string {
  return viewNode(basicView(expr), options);
}

/** The options of {@link dotedges}. */
export interface DotEdgesOptions {
  /** The nodes not to descend into (default: none, every node is a SymPy Basic). */
  readonly atom?: (e: Expr) => boolean;
  /** The position of the node in the tree. */
  readonly pos?: readonly number[];
  /** Distinguish equal subexpressions by their position (default true). */
  readonly repeat?: boolean;
}

const isAtom = (v: BasicView, atom: ((e: Expr) => boolean) | undefined): boolean => atom !== undefined && v.expr !== undefined && atom(v.expr);

function viewEdges(v: BasicView, options: DotEdgesOptions): string[] {
  if (isAtom(v, options.atom)) return [];
  const pos = options.pos ?? [];
  const repeat = options.repeat ?? true;
  const self = viewPurestr(v) + (repeat ? `_${posStr(pos)}` : '');
  return v.args.map((a, i) => `"${self}" -> "${viewPurestr(a)}${repeat ? `_${posStr([...pos, i])}` : ''}";`);
}

/** SymPy `dotedges(expr, atom, pos, repeat)`: the DOT lines of the edges from the node to its arguments. */
export function dotedges(expr: Expr, options: DotEdgesOptions = {}): string[] {
  return viewEdges(basicView(expr), options);
}

/** The options of {@link dotprint}. */
export interface DotprintOptions {
  /** The styles (default {@link defaultStyles}). */
  readonly styles?: DotStyles;
  /** The nodes not to descend into. */
  readonly atom?: (e: Expr) => boolean;
  /** The depth below which no edges are drawn. */
  readonly maxdepth?: number;
  /** Distinguish equal subexpressions by their position (default true): false draws a DAG. */
  readonly repeat?: boolean;
  /** The label of an atom (default `str`). */
  readonly labelfunc?: (e: Expr) => string;
  /** Graphviz graph attributes (default `rankdir="TD"`, `ordering="out"`). */
  readonly graphAttributes?: Readonly<Record<string, string>>;
}

/**
 * SymPy `dotprint(expr, ...)`: the DOT description of the expression tree,
 * for Graphviz (`dot -Tpng`).
 */
export function dotprint(expr: Expr, options: DotprintOptions = {}): string {
  const graphstyle = { rankdir: 'TD', ordering: 'out', ...options.graphAttributes };
  const nodes: string[] = [];
  const edges: string[] = [];
  const { styles, atom, maxdepth, repeat, labelfunc } = options;
  const traverse = (v: BasicView, depth: number, pos: number[]): void => {
    nodes.push(viewNode(v, { styles, labelfunc, pos, repeat }));
    if (maxdepth !== undefined && maxdepth > 0 && depth >= maxdepth) return;
    edges.push(...viewEdges(v, { atom, pos, repeat }));
    v.args.forEach((a, i) => {
      if (!isAtom(a, atom)) traverse(a, depth + 1, [...pos, i]);
    });
  };
  traverse(basicView(expr), 0, []);
  // SymPy's template
  return [
    'digraph{',
    '',
    '# Graph style',
    attrprint(graphstyle, '\n'),
    '',
    '#########',
    '# Nodes #',
    '#########',
    '',
    nodes.join('\n'),
    '',
    '#########',
    '# Edges #',
    '#########',
    '',
    edges.join('\n'),
    '}',
  ].join('\n');
}
