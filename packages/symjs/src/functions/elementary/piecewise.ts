// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { BoolOp, and } from '../../core/boolalg';
import { first } from '../../core/guard';
import { Le, Lt } from '../../core/logic';
import { Rel, S, Sym } from '../../core/nodes';
import type { Expr } from '../../core/nodes';
import { Max } from '../special/special';

/** Orient an inequality as a bound on x, with the bound independent of x. */
function boundOn(test: Expr, x: Sym): { upper: boolean; strict: boolean; end: Expr } | undefined {
  if (!(test instanceof Rel) || test.op === 'Eq' || test.op === 'Ne') return undefined;
  const left = test.lhs.equals(x);
  if (!left && !test.rhs.equals(x)) return undefined;
  const end = left ? test.rhs : test.lhs;
  if (end.has(x)) return undefined;
  return { end, upper: left === (test.op === 'Lt' || test.op === 'Le'), strict: test.op === 'Lt' || test.op === 'Gt' };
}

/** Simplify symbolic intervals in first-match order (SymPy piecewise_simplify_arguments). */
export function simplifySymbolicIntervals(pairs: [Expr, Expr][], simplify: (condition: Expr) => Expr): [Expr, Expr][] {
  const symbols = first(pairs)[1].freeSymbols();
  const [x] = symbols;
  if (!(x instanceof Sym) || symbols.size !== 1) return pairs;

  const covered: Expr[] = [];
  return pairs.map(([value, condition]) => {
    let test = condition;
    if (condition instanceof BoolOp && condition.op === 'And') {
      test = simplify(condition);
      if (test instanceof BoolOp && test.op === 'And') {
        const bounds = test.args.map((part) => boundOn(part, x));
        if (bounds.every((bound) => bound !== undefined)) {
          const lower = bounds.filter((bound) => !bound.upper).map((bound) => bound.end);
          // Outside the covered half-lines, every such lower test already holds.
          if (lower.length && lower.every((a) => covered.some((end) => Le(a, end) === S.true))) {
            const start = Max(...lower);
            test = and(...bounds.filter((bound) => bound.upper).map((bound) => {
              // SymPy gives reversed symbolic intervals zero width.
              const end = Le(start, bound.end) === S.true ? bound.end : Max(start, bound.end);
              return bound.strict ? Lt(x, end) : Le(x, end);
            }));
          }
        }
      }
    }
    const bound = boundOn(test, x);
    if (bound?.upper && !bound.strict) covered.push(bound.end);
    return [value, test];
  });
}
