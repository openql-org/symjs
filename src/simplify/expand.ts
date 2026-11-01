// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expand(): distribute products over sums and expand integer powers of sums.
 */

import { Add, Expr, ExprLike, Mul, Pow, Rational, impl } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';

const termsOf = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);

/** Multiply two expanded expressions, distributing over sums. */
function distribute(a: Expr, b: Expr): Expr {
  const ta = termsOf(a);
  const tb = termsOf(b);
  if (ta.length === 1 && tb.length === 1) return mul(a, b);
  const out: Expr[] = [];
  for (const x of ta) for (const y of tb) out.push(mul(x, y));
  return add(...out);
}

function expandPowInt(base: Expr, n: bigint): Expr {
  let result: Expr = Rational.of(1n);
  let b = base;
  let k = n;
  while (k > 0n) {
    if (k & 1n) result = distribute(result, b);
    k >>= 1n;
    if (k > 0n) b = distribute(b, b);
  }
  return result;
}

function expandNode(e: Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map(expandNode);
  const node = args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;

  if (node instanceof Mul) {
    if (!node.args.some((a) => a instanceof Add)) return node;
    return node.args.reduce<Expr>((acc, f) => distribute(acc, f), Rational.of(1n));
  }
  if (node instanceof Pow) {
    const [b, x] = node.args;
    if (b instanceof Add && x instanceof Rational && x.isInteger) {
      if (x.p > 0n) return expandPowInt(b, x.p);
      if (x.p < 0n) return pow(expandPowInt(b, -x.p), -1);
    }
    return node;
  }
  return node;
}

/** Expand products and integer powers of sums (recursively, including function arguments). */
export function expand(e: ExprLike): Expr {
  let cur = sympify(e);
  // Iterate to a fixed point: re-canonicalization can expose new sums.
  for (let i = 0; i < 8; i++) {
    const next = expandNode(cur);
    if (next.key === cur.key) return next;
    cur = next;
  }
  return cur;
}

impl.expand = expand;
