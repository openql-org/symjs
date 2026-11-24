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
/** Graphviz attributes of the nodes of the classes. */
export type DotStyles = readonly (readonly [DotClass, Readonly<Record<string, string>> | ReadonlyMap<string, string>])[];

/**
 * Blue ellipses, black for expressions.
 *
 * @see SymPy `sympy.printing.dot.default_styles`
 */
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
 * Formats a value using structural names for use as a graph node identifier.
 *
 * @param x - The value to format.
 * @returns The structural node identifier, with operand identifiers if requested.
 * @see SymPy `sympy.printing.dot.purestr`
 * @example
 * ```ts
 * import { ex, purestr } from '@symjs/symjs';
 * purestr(ex`x`); // => Symbol('x')
 * ```
 */
export function purestr(x: Expr): string;
/**
 * Formats a value using structural names for use as a graph node identifier.
 *
 * @param x - The value to format.
 * @param options - `withArgs` includes operand labels.
 * @returns The structural node identifier, with operand identifiers if requested.
 * @see SymPy `sympy.printing.dot.purestr`
 */
export function purestr(x: Expr, options: { readonly withArgs: true }): [string, string[]];
/**
 * Formats a value using structural names for use as a graph node identifier.
 *
 * @param x - The value to format.
 * @param options - `withArgs` includes operand labels.
 * @returns The structural node identifier, with operand identifiers if requested.
 * @see SymPy `sympy.printing.dot.purestr`
 */
export function purestr(x: Expr, options: { readonly withArgs?: boolean }): string | [string, string[]];
/**
 * Formats a value using structural names for use as a graph node identifier.
 *
 * @param x - The value to format.
 * @param options - `withArgs` includes operand labels.
 * @returns The structural node identifier, with operand identifiers if requested.
 * @see SymPy `sympy.printing.dot.purestr`
 */
export function purestr(x: Expr, options: { readonly withArgs?: boolean } = {}): string | [string, string[]] {
  return options.withArgs ? purestrWithArgs(x) : viewPurestr(basicView(x));
}

/**
 * Returns the purestr of the expression and those of its arguments.
 *
 * @param x - The expression whose operator and operands identify the DOT node.
 * @returns The purestr of the expression and those of its arguments.
 * @see SymPy `sympy.printing.dot.purestr`
 * @example
 * ```ts
 * import { ex, purestrWithArgs } from '@symjs/symjs';
 * purestrWithArgs(ex`x + 1`); // => [Add(Integer(1), Symbol('x')), [Integer(1), Symbol('x')]]
 * ```
 */
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
  for (const [cls, sty] of styles) if (matches(v, cls)) Object.assign(style, sty instanceof Map ? Object.fromEntries(sty) : sty);
  return style;
}

/**
 * Returns the merged attributes of the styles whose class the expression has.
 *
 * @param expr - The value to format.
 * @param styles - The mapping of expression types to DOT attributes.
 * @returns The merged attributes of the styles whose class the expression has.
 * @see SymPy `sympy.printing.dot.styleof`
 * @example
 * ```ts
 * import { defaultStyles, ex, styleof } from '@symjs/symjs';
 * styleof(ex`x`, defaultStyles).get('color'); // => black
 * ```
 */
export function styleof(expr: Expr, styles: DotStyles = defaultStyles): Map<string, string> {
  return new Map(Object.entries(viewStyle(basicView(expr), styles)));
}

/**
 * Formats DOT attributes as quoted key-value pairs sorted by key.
 *
 * @param d - The attribute names and values to format.
 * @param delimiter - The text inserted between adjacent entries.
 * @returns The formatted text.
 * @see SymPy `sympy.printing.dot.attrprint`
 * @example
 * ```ts
 * import { attrprint } from '@symjs/symjs';
 * attrprint(new Map([['color', 'blue'], ['shape', 'ellipse']])); // => "color"="blue", "shape"="ellipse"
 * ```
 */
export function attrprint(d: Readonly<Record<string, string>> | ReadonlyMap<string, string>, delimiter = ', '): string {
  return (d instanceof Map ? [...d] : Object.entries(d))
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

/**
 * Returns the DOT line of one node.
 *
 * @param expr - The value to format.
 * @param options - The dot node settings.
 * @returns The DOT line of one node.
 * @see SymPy `sympy.printing.dot.dotnode`
 * @example
 * ```ts
 * import { dotnode, ex } from '@symjs/symjs';
 * dotnode(ex`x`); // => "Symbol('x')_()" ["color"="black", "label"="x", "shape"="ellipse"];
 * ```
 */
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

/**
 * Returns the DOT lines of the edges from the node to its arguments.
 *
 * @param expr - The value to format.
 * @param options - The dot edges settings.
 * @returns The DOT lines of the edges from the node to its arguments.
 * @see SymPy `sympy.printing.dot.dotedges`
 * @example
 * ```ts
 * import { dotedges, ex } from '@symjs/symjs';
 * dotedges(ex`x + 1`).length; // => 2
 * ```
 */
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
 * The DOT description of the expression tree,
 * for Graphviz (`dot -Tpng`).
 *
 * @param expr - The value to format.
 * @param options - The dotprint settings.
 * @returns The graph in DOT syntax.
 * @see SymPy `sympy.printing.dot.dotprint`
 * @example
 * ```ts
 * import { dotprint, ex } from '@symjs/symjs';
 * dotprint(ex`x + 1`).includes('digraph'); // => True
 * ```
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
