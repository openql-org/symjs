// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The DIMACS CNF format of SymPy (sympy.logic.utilities.dimacs): a
 * formula in conjunctive normal form from its DIMACS text, with the
 * variable n as the symbol cnf_n.
 */

import type { Expr } from '../../core/nodes';
import { Sym } from '../../core/nodes';
import { andFn, notFn, orFn } from '../boolalg';

/**
 * SymPy load: the CNF formula of a DIMACS text (comment lines `c ...` and the
 * problem line `p cnf ...` are skipped, 0 ends a clause).
 */
export function load(s: string): Expr {
  const clauses: Expr[] = [];
  for (const line of s.split('\n')) {
    if (line.startsWith('c') || /^p\s*cnf\s*(\d*)\s*(\d*)/.test(line)) continue;
    const lits: Expr[] = [];
    for (const tok of line.split(' ')) {
      if (tok === '') continue;
      const n = parseInt(tok, 10);
      if (Number.isNaN(n)) throw new RangeError(`invalid literal in DIMACS input: '${tok}'`);
      if (n === 0) continue;
      const v = new Sym(`cnf_${Math.abs(n)}`);
      lits.push(n < 0 ? notFn(v) : v);
    }
    if (lits.length) clauses.push(orFn(...lits));
  }
  return andFn(...clauses);
}
