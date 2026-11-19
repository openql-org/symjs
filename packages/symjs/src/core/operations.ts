// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 core/operations.py (BSD-3-Clause).

import type { Expr, ExprLike } from './nodes';
import { ExtensionExpr } from './nodes';
import { first } from './guard';
import { sympify } from './ops';
import { ordered } from './match';

/** A commutative, associative and idempotent operation with identity and absorbing elements. */
export interface LatticeOperation {
  (...args: ExprLike[]): Expr;
  makeArgs(expression: ExprLike): Set<Expr>;
}

class LatticeNode extends ExtensionExpr {
  constructor(name: string, args: readonly Expr[], readonly operation: LatticeOperation, readonly family: string) {
    super(name, args);
  }

  protected override computeKey(): string {
    return `Lattice(${this.family},${this.args.map((arg) => arg.key).join(',')})`;
  }

  withArgs(args: readonly Expr[]): Expr {
    return this.operation(...args);
  }
}

/** Create a symbolic lattice operation with the specified identity and absorbing element. */
export function LatticeOp(name: string, identity: ExprLike, zero: ExprLike): LatticeOperation {
  const unit = sympify(identity);
  const absorbing = sympify(zero);
  const family = JSON.stringify([name, unit.key, absorbing.key]);
  const operation = (...values: ExprLike[]): Expr => {
    const terms = new Map<string, Expr>();
    for (const value of values) {
      const e = sympify(value);
      if (e.equals(absorbing)) return absorbing;
      if (e.equals(unit)) continue;
      const items = e instanceof LatticeNode && e.family === family ? e.args : [e];
      for (const item of items) terms.set(item.key, item);
    }
    if (!terms.size) return unit;
    const args = [...terms.values()];
    return args.length === 1 ? first(args) : new LatticeNode(name, ordered(args), lattice, family);
  };
  const makeArgs = (expression: ExprLike): Set<Expr> => {
    const e = sympify(expression);
    return new Set(e instanceof LatticeNode && e.family === family ? e.args : [e]);
  };
  const lattice: LatticeOperation = Object.assign(operation, { makeArgs });
  return lattice;
}
