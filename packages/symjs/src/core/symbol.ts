// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy core.symbol: names that distinguish otherwise similar symbols. */
import type { Assumptions, ExprLike } from './nodes';
import { Expr, Sym, UndefFn } from './nodes';
import { sympify } from './ops';
import { preorderTraversal, xreplace } from './traverse';
import { compareKeys, sortKey } from '../printing/sortkey';
import { TupleNode } from './containers';

export interface UniqueSymbolOptions extends Assumptions {
  readonly compare?: (name: string) => string;
  readonly modify?: (name: string) => string;
}

/** SymPy uniquely_named_symbol: increment a suffix until the name is unused. */
export function uniquelyNamedSymbol(xname: string | Sym, exprs: ExprLike | readonly ExprLike[] = [], options: UniqueSymbolOptions = {}): Sym {
  const { compare = (name: string): string => name, modify, ...assumptions } = options;
  const expressions = exprs instanceof Expr || typeof exprs !== 'object' ? [exprs] : exprs;
  const used = new Set<string>();
  for (const e of expressions) for (const node of preorderTraversal(sympify(e))) {
    if (node instanceof Sym || node instanceof UndefFn) used.add(compare(node.name));
  }
  const increment = (name: string): string => name.replace(/(\d*)$/, (digits: string) => String(digits === '' ? 0 : BigInt(digits) + 1n));
  let name = compare(typeof xname === 'string' ? xname : xname.name);
  while (used.has(name)) name = (modify ?? increment)(name);
  return new Sym(name, assumptions);
}

/** SymPy disambiguate: unique printed names, replacing Dummy symbols by ordinary symbols. */
export function disambiguate(...exprs: ExprLike[]): TupleNode {
  const tuple = new TupleNode(exprs.map(sympify));
  const groups = new Map<string, Sym[]>();
  const facts = (s: Sym): string => JSON.stringify([...s.assumptions0].sort(([a], [b]) => a.localeCompare(b)));
  for (const s of [...tuple.freeSymbols()].sort((a, b) => facts(a).localeCompare(facts(b)) || compareKeys(sortKey(a), sortKey(b)))) {
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
