// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { createContext, Script } from 'node:vm';
import type { Outcome } from '../harness.js';

declare module 'vitest' {
  export interface ProvidedContext { corpusCategory: string; corpusResults: string }
}

export interface TestGaps { cases: string[]; timeouts?: string[] }

/** Allow slower machines to complete replay without changing the corpus or ratchet. */
export function replayDeadlineMs(category: string, override = process.env['COMPAT_TESTS_TIMEOUT_MS']): number {
  if (!override) return category === 'core' || category === 'polys' ? 30_000 : 5000;
  const milliseconds = Number(override);
  if (!Number.isSafeInteger(milliseconds) || milliseconds <= 0) throw new RangeError('COMPAT_TESTS_TIMEOUT_MS must be a positive integer');
  return milliseconds;
}

/** A deadline gives no completed assertion to compare with a correctness baseline. */
export function ratchetDifferences(known: TestGaps, failing: string[], timeouts: string[]): { regressions: string[]; fixed: string[] } {
  const baseline = new Set(known.cases);
  const actual = new Set(failing);
  const unfinished = new Set(timeouts);
  const previouslyUnfinished = new Set(known.timeouts ?? []);
  return {
    regressions: failing.filter((id) => !baseline.has(id) && !unfinished.has(id)),
    fixed: known.cases.filter((id) => !actual.has(id) && !previouslyUnfinished.has(id)),
  };
}

/** Vitest's async timeout cannot interrupt a synchronous case. */
export function replayWithDeadline<C, O extends Outcome>(run: (c: C) => O, category: string) {
  const context = createContext({ run, current: undefined });
  const script = new Script('run(current)');
  const timeout = replayDeadlineMs(category);
  return (c: C): O | { status: 'error'; reason: string } => {
    context['current'] = c;
    try {
      return script.runInContext(context, { timeout });
    } catch (error) {
      if (typeof error !== 'object' || error === null || !('code' in error) || error.code !== 'ERR_SCRIPT_EXECUTION_TIMEOUT') throw error;
      return { status: 'error', reason: `Replay deadline exceeded (${timeout / 1000} s)` };
    }
  };
}
