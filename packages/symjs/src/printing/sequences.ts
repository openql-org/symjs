// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Parts ported from SymPy (sympy/printing/latex.py and pretty/pretty.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Sequences as the printers see them: series/ is a higher layer, so
 * the printers recognize a sequence (SeqFormula, SeqPer, SeqAdd, SeqMul) by
 * its name and the members it has.
 */

import type { Expr } from '../core/nodes';
import { ExtensionExpr, Special, impl } from '../core/nodes';
import { DOTS } from './sets';

/** The members of SymPy's SeqBase the printers use. */
interface SequenceLike {
  readonly start: Expr;
  readonly stop: Expr;
  readonly length: Expr;
  coeff(pt: Expr): Expr;
  getItem(i: number): Expr;
}

const SEQUENCES = new Set(['SeqFormula', 'SeqPer', 'SeqAdd', 'SeqMul']);

/** True for the sequences printed by their terms (SymPy `_print_SeqFormula` and its aliases). */
export const isSequence = (e: Expr): e is ExtensionExpr & SequenceLike => e instanceof ExtensionExpr && SEQUENCES.has(e.name) && 'coeff' in e && 'getItem' in e;

/** True when the start or the stop of the sequence has free symbols. */
export const hasSymbolicBounds = (s: SequenceLike): boolean => impl.freeSymbols(s.start).size > 0 || impl.freeSymbols(s.stop).size > 0;

/**
 * The terms SymPy's printers show for a sequence with numeric bounds: the
 * last four after an ellipsis for a sequence unbounded below, the first four
 * and an ellipsis for an infinite or a longer one, else all of them.
 */
export function sequencePrintset(s: SequenceLike): (Expr | typeof DOTS)[] {
  if (s.start instanceof Special) return [DOTS, ...[3, 2, 1, 0].map((k) => s.coeff(impl.add(s.stop, -k)))];
  const len = s.length;
  if (len instanceof Special || len.toNumber() > 4) return [...[0, 1, 2, 3].map((i) => s.getItem(i)), DOTS];
  return Array.from({ length: len.toNumber() }, (_, i) => s.getItem(i));
}
