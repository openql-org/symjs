// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { refreshScopeReport } from '../tools/sympy-reference/scope-report';
import type { TestOutcome } from '../tools/sympy-corpus/tests-harness.js';

export interface Counts { cases: number; exact: number; equivalent: number; fail: number; unsupported: number; error: number }
export interface Audit {
  examined: number; cases: number; reasons: Record<string, number>; sourceSites: number;
  seconds: number; retainedModules: number; testStatuses: Record<string, number>;
  shards: { file: string; cases: number; bytes: number }[]; auditFile: string; auditBytes: number; modules: string[];
}
export interface CorpusIndex {
  sympy: string; categories: Record<string, Audit>;
  excludedFiles: { file: string; reason: string }[]; timeoutSeconds: number; jobs: number; lastRunSeconds: number;
}
export interface CategoryResult {
  category: string; seconds: number; total: Counts; modules: Record<string, Counts>;
  failureGroups: Record<string, number>; apiGroups: Record<string, number>;
  failures: { id: string; fn: string; expected: string; outcome: TestOutcome }[];
  exclusions?: { id: string; reason: string }[];
  exceptionMismatches: { id: string; expected: string; actual: string }[];
}
export const emptyCounts = (): Counts => ({ cases: 0, exact: 0, equivalent: 0, fail: 0, unsupported: 0, error: 0 });
export const ratio = (a: number, b: number): string => b === 0 ? '-' : `${(100 * a / b).toFixed(2)}%`;
export const corpusIndex = (): CorpusIndex => JSON.parse(readFileSync(new URL('../tools/sympy-corpus/tests-corpus/index.json', import.meta.url), 'utf8'));

export function failureKind(o: TestOutcome): string {
  if (o.status === 'fail') return o.got === 'did not raise' ? 'exception not raised' : 'wrong result';
  if (o.status === 'unsupported') return /no adapter|method |attribute |operator |not callable/.test(o.reason) ? 'missing API/adapter' : 'unsupported value/input type';
  if (o.status === 'error') return o.reason.startsWith('Replay deadline') ? 'replay timeout' : o.phase === 'input' ? 'input conversion exception' : o.phase === 'result' ? 'result comparison exception' : 'unexpected exception';
  return 'agreement';
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

/** A single coordinator writes reports and the shared ratchet after isolated projects finish. */
export function writeTestsReport(directory: string, suiteSeconds: number): void {
  const index = corpusIndex();
  const names = Object.keys(index.categories).sort();
  if (!names.every((name) => existsSync(join(directory, `${name}.json`)))) return;
  const results: CategoryResult[] = names.map((name) => JSON.parse(readFileSync(join(directory, `${name}.json`), 'utf8')));
  const total = emptyCounts();
  for (const result of results) for (const k of Object.keys(total) as (keyof Counts)[]) total[k] += result.total[k];
  const failing = results.flatMap((r) => r.failures.map((f) => f.id)).sort();
  const timeouts = results.flatMap((r) => r.failures.filter((f) => f.outcome.status === 'error' && f.outcome.reason.startsWith('Replay deadline')).map((f) => f.id)).sort();
  const exclusions = results.flatMap((r) => r.exclusions ?? []);
  const mismatch = results.flatMap((r) => r.exceptionMismatches);
  const seconds = results.reduce((n, r) => n + r.seconds, 0);
  const lines = [
    '# SymPy unit-test compatibility', '',
    `Reference: SymPy ${index.sympy}. Independent of the doctest corpus and its ratchet.`, '',
    `Measured **${total.cases}** cases: **${total.exact} exact**, **${total.equivalent} equivalent**, **${failing.length} failing**. Agreement: **${ratio(total.exact + total.equivalent, total.cases)}**.`, '',
    `Compatibility suite wall time: **${suiteSeconds.toFixed(2)} s**. Sum of category replay times: **${seconds.toFixed(2)} s** (projects run in parallel).`, '',
    `Extraction wall time: **${index.lastRunSeconds.toFixed(2)} s**, ${index.jobs} processes, ${index.timeoutSeconds} s per upstream test. Retained modules reuse established observations; their time covers loading and auditing, not re-execution.`, '',
    `Synchronous replay has a ${replayDeadlineMs('core') / 1000} s deadline per core/polys case and ${replayDeadlineMs('tensor') / 1000} s elsewhere. Deadlines remain visible as failing/inconclusive observations and are never accepted as expected exceptions. Their IDs are stored separately in the ratchet: an unfinished assertion cannot establish or resolve a correctness regression.`, '',
    'Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the shared doctest deserializer, adapters and equivalence rules. Exception class mismatches are accepted and counted separately; missing adapters and deserialization errors never prove an expected exception.', '',
    `${exclusions.length} assertions excluded from replay with explicit Python class execution reasons in tools/sympy-reference/unit-exclusions.json. Their corpus records are retained.`, '',
    '## Agreement by category', '', '| Category | Measured | Exact | Equivalent | Failing | Agreement | Replay s |', '|---|---:|---:|---:|---:|---:|---:|',
  ];
  for (const r of results) lines.push(`| ${r.category} | ${r.total.cases} | ${r.total.exact} | ${r.total.equivalent} | ${r.failures.length} | ${ratio(r.total.exact + r.total.equivalent, r.total.cases)} | ${r.seconds.toFixed(2)} |`);
  lines.push('', '## Extraction audit', '',
    'Executed loop instances count individually. Duplicates count as omissions; never-reached sites count once. Partial observations from timed-out upstream tests are discarded. Detailed source locations and test statuses are in each category audit file.', '',
    '| Category | Source sites | Examined | Cases | Omitted | Wall s | Retained modules |', '|---|---:|---:|---:|---:|---:|---:|');
  for (const [name, a] of Object.entries(index.categories)) lines.push(`| ${name} | ${a.sourceSites} | ${a.examined} | ${a.cases} | ${Object.values(a.reasons).reduce((x, y) => x + y, 0)} | ${a.seconds.toFixed(2)} | ${a.retainedModules} |`);
  lines.push('', '| Category | Omission reason | Count |', '|---|---|---:|');
  for (const [name, a] of Object.entries(index.categories)) for (const [reason, n] of Object.entries(a.reasons).sort()) lines.push(`| ${name} | ${reason} | ${n} |`);
  lines.push('', '| Category | Test execution status | Count |', '|---|---|---:|');
  for (const [name, a] of Object.entries(index.categories)) for (const [reason, n] of Object.entries(a.testStatuses).sort()) lines.push(`| ${name} | ${reason} | ${n} |`);
  lines.push('', '## Main failure groups', '', '| Category | Kind | Count |', '|---|---|---:|');
  for (const r of results) {
    for (const [kind, n] of Object.entries(r.failureGroups).sort()) lines.push(`| ${r.category} | ${kind} | ${n} |`);
    lines.push(`| ${r.category} | exception class mismatch (accepted) | ${r.exceptionMismatches.length} |`);
  }
  lines.push('', '## Most frequent failing APIs per category', '', '| Category | API and outcome | Cases |', '|---|---|---:|');
  for (const r of results) for (const [api, n] of Object.entries(r.apiGroups).sort((a, b) => b[1] - a[1]).slice(0, 10)) lines.push(`| ${r.category} | ${api} | ${n} |`);
  lines.push('', '## Corpus files', '', '| Category | Cases bytes | Audit bytes | Shards |', '|---|---:|---:|---:|');
  for (const [name, a] of Object.entries(index.categories)) lines.push(`| ${name} | ${a.shards.reduce((n, s) => n + s.bytes, 0)} | ${a.auditBytes} | ${a.shards.length} |`);
  lines.push('', 'Case shards contain one JSON case per line, with ASCII escapes and finite JSON numbers. Shards are at most 25 MB. tests-report.json contains summaries only; tests-results/*.jsonl contains one failure per line.', '',
    '## Out-of-scope test files', '', '| File (relative to sympy/) | Technical reason |', '|---|---|');
  for (const { file, reason } of index.excludedFiles) lines.push(`| ${file} | ${reason} |`);
  lines.push('', `Accepted exception class mismatches: **${mismatch.length}**. Their case IDs and classes are retained in tests-report.json.`, '');
  writeFileSync(new URL('./TESTS-REPORT.md', import.meta.url), lines.join('\n'));
  writeFileSync(new URL('./tests-report.json', import.meta.url), JSON.stringify({
    sympy: index.sympy, suiteSeconds, seconds, total,
    categories: Object.fromEntries(results.map((r) => [r.category, { ...r, failures: r.failures.length }])),
    extraction: index,
  }, null, 1) + '\n');
  if (process.env['UPDATE_KNOWN_GAPS']) writeFileSync(new URL('../tools/sympy-corpus/tests-known-gaps.json', import.meta.url), JSON.stringify({ cases: failing, timeouts }, null, 1) + '\n');
  refreshScopeReport();
}
