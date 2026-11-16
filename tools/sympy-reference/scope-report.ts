// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';

export interface ScopeInventory {
  reference: { sympy: string };
  modules: { module: string; status: string; selectedForExtraction: boolean; hasCorpusCases: boolean }[];
}
const STATUSES = ['complete', 'partial', 'unassessed', 'extend', 'excluded'];

export function scopeSummary(inventory: ScopeInventory): { modules: number; statuses: Record<string, number>; completeModules: string[] } {
  return {
    modules: inventory.modules.length,
    statuses: Object.fromEntries(STATUSES.map((status) => [status, inventory.modules.filter((m) => m.status === status).length])),
    completeModules: inventory.modules.filter((m) => m.status === 'complete').map((m) => m.module),
  };
}

export function scopeLines(inventory: ScopeInventory): string[] {
  const summary = scopeSummary(inventory);
  const packageOf = (module: string): string => module.split('.')[1] ?? 'sympy';
  const packages = [...new Set(inventory.modules.map((m) => packageOf(m.module)))].sort();
  return [
    '## Whole-reference scope', '',
    `Pinned inventory: **${summary.modules} production modules** in SymPy ${inventory.reference.sympy}. ${inventory.modules.filter((m) => m.selectedForExtraction).length} selected for extraction; ${inventory.modules.filter((m) => m.hasCorpusCases).length} have recorded calls. No whole-SymPy behavioral percentage is established.`, '',
    '| Inventory status | Modules |', '|---|---:|',
    ...Object.entries(summary.statuses).map(([status, n]) => `| ${status} | ${n} |`), '',
    'Complete means public exports and class members are present, doctest and unit-test evidence passes strict omission and gap checks, and no limitation is recorded. A module without an upstream SymPy test file has no applicable unit-test criterion and relies on the per-file 100% coverage of its own tests. Partial means a source correspondence exists but one or more criteria fail. Per-module reasons are recorded in the inventory. Unassessed modules remain visible. Extend modules are planned for an extend package (physics) instead of the base module. Exclusions and source hashes are recorded in `scope-inventory.json`; symbolic mathematical features are not excluded merely because they are difficult.', '',
    '| Package | Complete | Partial | Unassessed | Extend | Excluded |',
    '|---|---:|---:|---:|---:|---:|',
    ...packages.map((p) => `| ${p} | ${STATUSES.map((status) => inventory.modules.filter((m) => packageOf(m.module) === p && m.status === status).length).join(' | ')} |`), '',
    '### Complete modules', '',
    ...(summary.completeModules.length ? summary.completeModules.map((m) => `- \`${m}\``) : ['None meet all four criteria.']), '',
  ];
}

/** Refresh after the coordinator writes both ratchets, so every generated report
 * uses the same measurements even when this run removes a unit-test gap. */
export function refreshScopeReport(): void {
  const root = new URL('../..', import.meta.url);
  execFileSync('python3', ['tools/sympy-reference/inventory.py'], { cwd: root, stdio: 'pipe' });
  const inventory: ScopeInventory = JSON.parse(readFileSync(new URL('./scope-inventory.json', import.meta.url), 'utf8'));
  const markdownFile = new URL('../../compat/REPORT.md', import.meta.url);
  const markdown = readFileSync(markdownFile, 'utf8');
  writeFileSync(markdownFile, markdown.replace(/## Whole-reference scope\n[\s\S]*?(?=## Extraction audit\n)/, scopeLines(inventory).join('\n') + '\n'));
  const jsonFile = new URL('../../compat/report.json', import.meta.url);
  if (existsSync(jsonFile)) {
    const report = JSON.parse(readFileSync(jsonFile, 'utf8'));
    report.scope = scopeSummary(inventory);
    writeFileSync(jsonFile, JSON.stringify(report, null, 1) + '\n');
  }
}
