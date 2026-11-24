// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy core.symbol: names that distinguish otherwise similar symbols. */
import type { Assumptions, ExprLike } from './nodes';
import { Expr, Sym, UndefFn } from './nodes';
import { sympify } from './ops';
import { preorderTraversal, xreplace } from './traverse';
import { compareKeys, sortKey } from '../printing/sortkey';
import { TupleNode } from './containers';

/** Rules for comparing and modifying a candidate symbol name to avoid collisions. */
export interface UniqueSymbolOptions extends Assumptions {
  /** Normalize candidate names for comparison. */
  readonly compare?: (name: string) => string;
  /** Produce the next candidate name after a collision. */
  readonly modify?: (name: string) => string;
}

/**
 * Creates a symbol whose name is unused in the supplied expressions.
 *
 * @param xname - The proposed symbol name or name and fallback symbol.
 * @param exprs - The expressions to process.
 * @param options - The comparison and renaming callbacks in {@link UniqueSymbolOptions}.
 * @returns A symbol whose name is distinct from those in the given expressions.
 * @see SymPy `sympy.core.symbol.uniquely_named_symbol`
 * @example
 * ```ts
 * import { ex, uniquelyNamedSymbol } from '@symjs/symjs';
 *
 * uniquelyNamedSymbol('x', ex`x`); // => x0
 * uniquelyNamedSymbol('x', [ex`x`, ex`x0`]); // => x1
 * ```
 */
export function uniquelyNamedSymbol(xname: string | Sym | readonly [string | Sym, Sym], exprs: ExprLike | readonly ExprLike[] = [], options: UniqueSymbolOptions = {}): Sym {
  const { compare = (name: string): string => name, modify, ...assumptions } = options;
  const base = typeof xname === 'string' || xname instanceof Sym ? xname : xname[0];
  const fallback = typeof xname === 'string' || xname instanceof Sym ? undefined : xname[1];
  const expressions = exprs instanceof Expr || typeof exprs !== 'object' ? [exprs] : exprs;
  const used = new Set<string>();
  for (const e of expressions) for (const node of preorderTraversal(sympify(e))) {
    if (node instanceof Sym || node instanceof UndefFn) used.add(compare(node.name));
  }
  const increment = (name: string): string => name.replace(/(\d*)$/, (digits: string) => String(digits === '' ? 0 : BigInt(digits) + 1n));
  let name = compare(typeof base === 'string' ? base : base.name);
  while (used.has(name)) name = (modify ?? increment)(name);
  if (fallback?.name === name) return fallback;
  return new Sym(name, assumptions);
}

/**
 * Gives distinct symbols unique printed names across the expressions and replaces dummy symbols with
 * ordinary symbols.
 *
 * @param exprs - The expressions to process.
 * @returns The expressions with conflicting symbol names distinguished.
 * @see SymPy `sympy.core.symbol.disambiguate`
 * @example
 * ```ts
 * import { disambiguate, ex } from '@symjs/symjs';
 *
 * disambiguate(ex`x`, ex`y`); // => (x, y)
 * ```
 */
export function disambiguate(...exprs: ExprLike[]): TupleNode {
  const tuple = new TupleNode(exprs.map(sympify));
  const groups = new Map<string, Sym[]>();
  const facts = (s: Sym): string => JSON.stringify([...s.assumptions0].sort(([a], [b]) => a.localeCompare(b)));
  for (const s of [...tuple.freeSymbols()].filter((s) => s instanceof Sym).sort((a, b) => facts(a).localeCompare(facts(b)) || compareKeys(sortKey(a), sortKey(b)))) {
    const name = s.name.replace(/^_+/, '');
    groups.set(name, [...(groups.get(name) ?? []), s]);
  }
  const replacements = new Map<Expr, Expr>();
  for (const [name, symbols] of groups) {
    let suffix = 1;
    symbols.forEach((s, i) => {
      let next = name;
      if (i > 0) {
        while (groups.has(`${name}_${suffix}`)) suffix++;
        next = `${name}_${suffix++}`;
      }
      replacements.set(s, new Sym(next, s.assumptions));
    });
  }
  return new TupleNode(tuple.args.map((e) => xreplace(e, replacements)));
}
