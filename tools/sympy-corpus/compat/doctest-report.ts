// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';

import { execFileSync } from 'node:child_process';
import { join } from 'node:path';
import { doctestExtraction, readIndex, type Api, type DoctestIndex } from '../corpus.js';
import type { Case, Outcome } from '../harness.js';
import type { Evidence, adapterInventory } from '../adapter-audit.js';
import type { BaseCheckResult } from './base-scope.js';
import type { OdeCheckResult } from '../ode-checks.js';
import { writeEquivalentCases } from './equivalent-cases.js';

export interface DoctestResult {
  results: { c: Pick<Case, 'module' | 'src' | 'fn' | 'category' | 'expected'>; o: Outcome; evidence: Evidence }[];
  apiEvidence: (Api & { counterpart: string | null; status: string; directCases: number })[];
  failing: string[];
  timeouts: string[];
  missingApi: string[];
  ported: number;
}
export interface ScopeChecks {
  base: BaseCheckResult[];
  ode: OdeCheckResult[];
  adapters: ReturnType<typeof adapterInventory>;
}

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

type FileCoverage = {
  path: string;
  category: string;
  statements: number;
  pct: Record<'statements' | 'branches' | 'functions' | 'lines', number>;
  full: boolean;
};

/** Map a source file to a compatibility category. */
function categoryOf(fullPath: string): string {
  // the SymPy categories apply to the base module; other packages are extend modules
  if (!fullPath.startsWith('packages/symjs/src/')) return 'extend';
  const path = fullPath.replace(/^packages\/symjs\/src\//, 'src/');
  if (path.startsWith('src/functions/special')) return 'special';
  if (path.startsWith('src/functions/')) return 'functions';
  if (path.startsWith('src/simplify/')) return 'simplify';
  if (path.startsWith('src/polys/')) return 'polys';
  if (path === 'src/solvers/pde.ts') return 'pde';
  if (path === 'src/solvers/ode.ts') return 'ode';
  if (path.startsWith('src/solvers/')) return 'solvers';
  if (/^src\/(calculus|series|integrals)\//.test(path)) return 'calculus';
  if (path.startsWith('src/matrices/')) return 'matrices';
  if (path.startsWith('src/quantum/')) return 'quantum';
  const sub = /^src\/(discrete|algebras|strategies|unify|geometry|vector|stats|categories|tensor|combinatorics|crypto|liealgebras|codegen|diffgeom|parsing|plotting)[/.]/.exec(path);
  if (sub) return sub[1]!;
  return 'core';
}

/** Per-file coverage from coverage/coverage-summary.json (written by `bun run coverage`). */
function readCoverage(): { files: FileCoverage[] } | undefined {
  const url = new URL('../../../coverage/coverage-summary.json', import.meta.url);
  if (!existsSync(url)) return undefined;
  const data = JSON.parse(readFileSync(url, 'utf8')) as Record<string, Record<string, { total: number; pct: number }>>;
  const root = new URL('../../..', import.meta.url).pathname;
  const files: FileCoverage[] = [];
  for (const [abs, v] of Object.entries(data)) {
    if (abs === 'total') continue;
    const path = abs.startsWith(root) ? abs.slice(root.length) : abs;
    // entry points only re-export
    if (path.endsWith('/src/index.ts') || /^packages\/symjs\/src\/[^/]+\.ts$/.test(path)) continue;
    const p = { statements: v['statements']!.pct, branches: v['branches']!.pct, functions: v['functions']!.pct, lines: v['lines']!.pct };
    files.push({ path, category: categoryOf(path), statements: v['statements']!.total, pct: p, full: Object.values(p).every((x) => x === 100) });
  }
  return { files };
}
const CATEGORY_ORDER = ['core', 'functions', 'simplify', 'polys', 'solvers', 'ode', 'pde', 'calculus', 'matrices', 'special', 'logic', 'tensor', 'ntheory', 'assumptions', 'utilities', 'combinatorics', 'sets', 'printing', 'discrete', 'algebras', 'holonomic', 'strategies', 'unify', 'geometry', 'vector', 'stats', 'categories', 'crypto', 'liealgebras', 'diffgeom', 'parsing', 'plotting'];

// a rate below 100% never prints as 100.0%
const pct = (a: number, b: number) => (b === 0 ? '-' : `${(a < b ? Math.min((100 * a) / b, 99.9) : 100).toFixed(1)}%`);

/**
 * Explicit doctest exclusions, by case label and reason. Excluded cases do not
 * establish passing behavior; the inventory rejects non-Python exclusions.
 * The null-input entry covers sympify(null), which throws SympifyError.
 * For dist.pmf(x), SymPy returns a Lambda and ignores x; symjs evaluates the
 * probability mass function at x. Sampling examples require external libraries
 * and are omitted by the extractor as random output or explicit +SKIP examples.
 */
export const OUT_OF_SCOPE: Readonly<Record<string, string>> = JSON.parse(readFileSync(new URL('../../sympy-reference/doctest-exclusions.json', import.meta.url), 'utf8'));

/**
 * SymPy public names outside the scope of symjs, by API key, with the reason. They are
 * not counted in the API presence (tools/sympy-reference/extract_doctest.py no longer lists them; this keeps an older corpus
 * consistent). Their modules are 'excluded' in scope-inventory.json with the same reason.
 */
export const OUT_OF_SCOPE_API: Readonly<Record<string, string>> = {};

export function writeDoctestReport(directory: string): boolean {
  const index = readIndex<DoctestIndex>('doctest');
  const files = Object.keys(index.categories).map(name => join(directory, `${name}.json`));
  if (!files.every(file => existsSync(file))) return false;
  const categories: DoctestResult[] = files.map(file => JSON.parse(readFileSync(file, 'utf8')));
  const results = categories.flatMap(r => r.results);
  const apiEvidence = categories.flatMap(r => r.apiEvidence);
  const extractedCalls = Object.values(index.categories).reduce((n, summary) => n + summary.cases, 0);
  const ported = categories.reduce((n, r) => n + r.ported, 0);
  const extraction = doctestExtraction(index);
  const { base, ode, adapters }: ScopeChecks = JSON.parse(readFileSync(join(directory, 'scope.json'), 'utf8'));
  const verifiedPass = results.filter(({ o, evidence }) => (o.status === 'pass' || o.status === 'equivalent') && (evidence === 'public-call' || evidence === 'reviewed-conversion')).length;
  const inventory: ScopeInventory = JSON.parse(readFileSync(new URL('../../sympy-reference/scope-inventory.json', import.meta.url), 'utf8'));
  const capabilities = JSON.parse(readFileSync(new URL('../../sympy-reference/capabilities.json', import.meta.url), 'utf8')) as { areas: { area: string; status: string; tested: string[]; remaining: string[]; outOfScope?: string[]; tests: string[] }[] };
  const evidenceCounts = Object.fromEntries(['public-call', 'reviewed-conversion', 'harness-computation', 'unreviewed-adapter', 'unreviewed-translation'].map((evidence) => [evidence, results.filter((r) => r.evidence === evidence).length]));
  type Row = { cases: number; pass: number; equivalent: number; fail: number; unsupported: number; error: number; api: number; apiDone: number };
  const rows = new Map<string, Row>();
  const row = (cat: string) => {
    let r = rows.get(cat);
    if (!r) {
      r = { cases: 0, pass: 0, equivalent: 0, fail: 0, unsupported: 0, error: 0, api: 0, apiDone: 0 };
      rows.set(cat, r);
    }
    return r;
  };
  for (const { c, o } of results) {
    const r = row(c.category);
    r.cases++;
    r[o.status]++;
  }
  for (const a of apiEvidence) {
    const r = row(a.category);
    r.api++;
    if (a.counterpart !== null) r.apiDone++;
  }

  // impact list: unsupported functions by number of cases
  const missing = new Map<string, { n: number; category: string }>();
  for (const { c, o } of results) {
    if (o.status === 'pass' || o.status === 'equivalent') continue;
    const k = c.fn;
    const m = missing.get(k) ?? { n: 0, category: c.category };
    m.n++;
    missing.set(k, m);
  }

  const total = [...rows.values()].reduce(
    (acc, r) => ({
      cases: acc.cases + r.cases,
      pass: acc.pass + r.pass,
      equivalent: acc.equivalent + r.equivalent,
      api: acc.api + r.api,
      apiDone: acc.apiDone + r.apiDone,
    }),
    { cases: 0, pass: 0, equivalent: 0, api: 0, apiDone: 0 },
  );

  const cats = [...rows.keys()].sort((a, b) => CATEGORY_ORDER.indexOf(a) - CATEGORY_ORDER.indexOf(b));
  const lines: string[] = [];
  lines.push('# SymPy doctest agreement and API presence (`bun run corpus:compat`)', '');
  lines.push(`Reference: SymPy ${index.sympy}.`, '');
  lines.push(
    '- **Corpus result agreement** (includes unaudited harness code): share of SymPy doctest examples (public API calls in the in-scope modules) for which symjs gives the same result as SymPy: either the same `str()` output (**exact**) or a mathematically equivalent value in another form (**equivalent**: equal at test points respecting the symbol assumptions, or `simplify(a - b) == 0`; sets and solution lists compared without regard to order; for `dsolve`, a solution that satisfies the equations with as many integration constants, like SymPy `checkodesol`, which also accepts a correct solution where SymPy prints a wrong one). A result left unevaluated (`Integral`, `Limit`, `Sum`, ...) where SymPy computes a value is a failure, as are cases whose arguments symjs cannot represent. The **exact** rate is reported alongside (`packages/symjs/tests/sympy-equivalent.ts`).',
    '- **JavaScript translations**: doctests whose setup is Python code the extractor cannot serialize (user-defined classes, Python lambdas and functions as arguments, SymPy-internal containers) run as hand-written translations to the symjs public API (`tools/sympy-corpus/ports.ts`) and are compared with SymPy\'s output like the other cases.',
    '- **API presence** (not behavioral compatibility): share of in-scope public SymPy names (functions, classes, `Expr`/`Matrix` methods) that have a symjs counterpart.',
    '- **Base scope checks**: behaviors the base module is meant to guarantee (assumptions, non-commutativity, bound variables, unevaluated objects, extension nodes, ...), checked against SymPy output (`tools/sympy-corpus/compat/base-scope.ts`).',
    '- **ODE checks**: representative equations for each SymPy `dsolve` hint (`tools/sympy-corpus/ode-checks.json`, generated by `tools/sympy-reference/generators/gen_ode_checks.py`). A check passes when the solution is printed like SymPy\'s (**exact**) or, in another form, satisfies the equation with as many integration constants (**equivalent**, like SymPy `checkodesol`).',
    '- **Fully covered**: source files whose unit tests reach 100% coverage. This measures test coverage, not SymPy behavior.',
    '',
  );
  lines.push(
    `**Measured corpus only: result agreement ${pct(total.pass + total.equivalent, total.cases)} (${total.pass + total.equivalent}/${total.cases}; exact ${pct(total.pass, total.cases)} ${total.pass}, equivalent ${total.equivalent}; ${ported} run as JavaScript translations), API presence ${pct(total.apiDone, total.api)} (${total.apiDone}/${total.api})**`,
    'The equivalent cases are listed in [doctest-equivalent-cases.md](doctest-equivalent-cases.md).',
    '',
  );
  lines.push(
    `**Verified public-call results: ${verifiedPass}/${total.cases} (${pct(verifiedPass, total.cases)})**. This conservative count includes automatic public calls and reviewed conversion adapters. Results depending on harness computations, unaudited adapters or translations are unverified. It is not the coverage of all SymPy functionality.`,
    '',
    ...scopeLines(inventory),
    '## Extraction audit', '',
    `Examined ${extraction.examined} doctest statements including setup. Kept ${results.length} in-scope calls; ${extractedCalls - results.length} calls excluded by ${Object.keys(OUT_OF_SCOPE).length} explicit case labels are listed in the runner, as are ${Object.keys(OUT_OF_SCOPE_API).length} public names excluded from the API presence (${[...new Set(Object.values(OUT_OF_SCOPE_API))].join('; ')}). The detailed omitted list records ${extraction.omitted.length} examples with expected output.`, '',
    '| Reason | Statements |', '|---|---:|',
    ...Object.entries(extraction.reasons).map(([reason, n]) => `| ${reason} | ${n} |`), '',
    '## Public API evidence', '',
    `Names without a directly named corpus case: ${apiEvidence.filter((a) => a.directCases === 0).length}/${apiEvidence.length}. A method exercised under another name may still have unit tests; name presence alone does not establish correctness. Concrete export/member paths are recorded in tools/sympy-corpus/compat/results/doctest-report.json; an unmapped name is unverified or absent, not proof that the mathematical operation is unavailable.`, '',
    '| Execution route | Cases |', '|---|---:|',
    ...Object.entries(evidenceCounts).map(([kind, n]) => `| ${kind} | ${n} |`), '',
    'Every manual adapter is listed in `adapter-inventory.json`. Remaining mathematical helpers are quarantined from the verified count until migrated into public APIs. A change to adapters must update that inventory.', '',
    '## Capability conditions', '',
    '| Area | Status | Tested conditions | Remaining scope | Outside SymPy 1.14\'s scope |', '|---|---|---|---|---|',
    ...capabilities.areas.map((a) => `| ${a.area} | ${a.status} | ${a.tested.join('; ')} | ${a.remaining.join('; ')} | ${(a.outOfScope ?? []).join('; ')} |`), '',
    'Direct regression-test paths are maintained in `capabilities.json`. Remaining items block the completeness of the listed modules; items outside SymPy 1.14\'s scope (not in SymPy, Python-specific, deprecated by SymPy or undecidable in general) do not.', '',
  );
  const basePass = base.filter((b) => b.pass).length;
  lines.push(`**Base scope checks: ${pct(basePass, base.length)} (${basePass}/${base.length})**`, '');
  const odePass = ode.filter((o) => o.pass).length;
  const odeExact = ode.filter((o) => o.exact).length;
  lines.push(`**ODE checks: ${pct(odePass, ode.length)} (${odePass}/${ode.length}; exact ${odeExact}, equivalent ${odePass - odeExact})**`, '');
  const cov = readCoverage();
  if (cov) {
    const full = cov.files.filter((f) => f.full);
    const fullStmts = full.reduce((n, f) => n + f.statements, 0);
    const allStmts = cov.files.reduce((n, f) => n + f.statements, 0);
    lines.push(
      `**Fully covered (100% test coverage): ${pct(full.length, cov.files.length)} of source files (${full.length}/${cov.files.length}), ${pct(fullStmts, allStmts)} of statements (${fullStmts}/${allStmts})**`,
      '',
    );
  }
  lines.push('| Category | Behavior | Exact | Exact rate | Equivalent | Fail | Unsupported | Error | Cases | API coverage | Fully covered files |');
  lines.push('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|');
  for (const cat of cats) {
    const r = rows.get(cat)!;
    const cf = cov?.files.filter((f) => f.category === cat) ?? [];
    const fc = cf.length ? `${pct(cf.filter((f) => f.full).length, cf.length)} (${cf.filter((f) => f.full).length}/${cf.length})` : '-';
    lines.push(
      `| ${cat} | ${pct(r.pass + r.equivalent, r.cases)} | ${r.pass} | ${pct(r.pass, r.cases)} | ${r.equivalent} | ${r.fail} | ${r.unsupported} | ${r.error} | ${r.cases} | ${pct(r.apiDone, r.api)} (${r.apiDone}/${r.api}) | ${fc} |`,
    );
  }
  if (cov) {
    lines.push('', '## Test coverage by source file', '');
    lines.push(
      'A source file counts as **fully covered** when the unit tests (`bun run coverage`, `tests/`) cover 100% of its statements, branches, functions and lines.',
      '',
    );
    lines.push('| File | Category | Statements | Branches | Functions | Lines | Fully covered |', '|---|---|---:|---:|---:|---:|:---:|');
    for (const f of [...cov.files].sort((a, b) => a.category.localeCompare(b.category) || a.path.localeCompare(b.path))) {
      lines.push(`| \`${f.path}\` | ${f.category} | ${f.pct.statements}% | ${f.pct.branches}% | ${f.pct.functions}% | ${f.pct.lines}% | ${f.full ? 'yes' : ''} |`);
    }
  }
  lines.push('', '## Base scope checks', '');
  lines.push('| Area | Pass | Checks |', '|---|---:|---:|');
  const areas = [...new Set(base.map((b) => b.area))];
  for (const a of areas) {
    const bs = base.filter((b) => b.area === a);
    lines.push(`| ${a} | ${bs.filter((b) => b.pass).length} | ${bs.length} |`);
  }
  const baseFail = base.filter((b) => !b.pass);
  if (baseFail.length) {
    lines.push('', '| Failing check | Area | Expected (SymPy) | symjs |', '|---|---|---|---|');
    for (const b of baseFail) lines.push(`| ${b.name} | ${b.area} | \`${b.expected}\` | \`${b.got}\` |`);
  }
  lines.push('', '## ODE checks', '');
  lines.push('| Hint | Pass | Checks |', '|---|---:|---:|');
  for (const h of [...new Set(ode.map((o) => o.hint))]) {
    const os = ode.filter((o) => o.hint === h);
    lines.push(`| ${h} | ${os.filter((o) => o.pass).length} | ${os.length} |`);
  }
  const odeFail = ode.filter((o) => !o.pass);
  if (odeFail.length) {
    lines.push('', '| Equation (= 0) | Hint | Expected (SymPy) | symjs |', '|---|---|---|---|');
    for (const o of odeFail) lines.push(`| \`${o.eq}\` | ${o.hint} | \`${o.expected}\` | \`${o.got.replace(/\|/g, '\\|')}\` |`);
  }
  lines.push('', '## Highest-impact gaps', '', 'API names with the most non-passing cases.', '');
  lines.push('| API | Category | Non-passing cases |', '|---|---|---:|');
  for (const [fn, m] of [...missing].sort((a, b) => b[1].n - a[1].n).slice(0, 40)) {
    lines.push(`| \`${fn}\` | ${m.category} | ${m.n} |`);
  }
  lines.push('');
  mkdirSync(new URL('./results/', import.meta.url), { recursive: true });
  writeFileSync(new URL('../../../docs/doctest-compat-report.md', import.meta.url), lines.join('\n'));
  writeFileSync(
    new URL('./results/doctest-report.json', import.meta.url),
    JSON.stringify(
      {
        sympy: index.sympy,
        overall: { ...total, ported, verifiedPublicPass: verifiedPass },
        scope: scopeSummary(inventory),
        extraction,
        apiEvidence,
        adapterEvidence: { counts: evidenceCounts, adapters },
        capabilities,
        baseScope: { pass: basePass, total: base.length, failures: baseFail },
        ode: { pass: odePass, exact: odeExact, total: ode.length, failures: odeFail },
        categories: Object.fromEntries(cats.map((c) => [c, rows.get(c)])),
        equivalents: results.filter(({ o }) => o.status === 'equivalent').map(({ c, o, evidence }) => ({ module: c.module, src: c.src, fn: c.fn, category: c.category, expected: c.expected, evidence, ...o })),
        failures: results
          .filter(({ o }) => o.status !== 'pass' && o.status !== 'equivalent')
          .map(({ c, o, evidence }) => ({ module: c.module, src: c.src, fn: c.fn, category: c.category, expected: c.expected, evidence, ...o })),
      },
      null,
      1,
    ) + '\n',
  );

  writeEquivalentCases('doctest', results.flatMap(({ c, o }) => o.status === 'equivalent' ? [{ id: `${c.module}: ${c.src}`, fn: c.fn, got: o.got, expected: c.expected }] : []));
  const failing = categories.flatMap(r => r.failing).sort();
  const api = categories.flatMap(r => r.missingApi).sort();
  const timeouts = categories.flatMap(r => r.timeouts).sort();
  const gapsFile = new URL('../doctest-known-gaps.json', import.meta.url);
  if (process.env['UPDATE_KNOWN_GAPS'] === '1') {
    writeFileSync(gapsFile, JSON.stringify({ cases: failing, api, ...(timeouts.length ? { timeouts } : {}) }, null, 1) + '\n');
  } else {
    // A removed case or API may no longer have a category project to claim its key.
    const gaps: { cases: string[]; api: string[]; timeouts?: string[] } = JSON.parse(readFileSync(gapsFile, 'utf8'));
    const stale = [...gaps.cases.filter(k => !failing.includes(k) && !gaps.timeouts?.includes(k)), ...gaps.api.filter(k => !api.includes(k))];
    if (stale.length) throw new RangeError(`Fixed doctest gaps still listed: ${stale.join(', ')}`);
  }
  return true;
}

/** Refresh after the coordinator writes both ratchets, so every generated report
 * uses the same measurements even when this run removes a unit-test gap. */
export function refreshScopeReport(): void {
  const root = new URL('../../..', import.meta.url);
  execFileSync('python3', ['-B', 'tools/sympy-reference/inventory.py'], { cwd: root, stdio: 'pipe' });
  const inventory: ScopeInventory = JSON.parse(readFileSync(new URL('../../sympy-reference/scope-inventory.json', import.meta.url), 'utf8'));
  const markdownFile = new URL('../../../docs/doctest-compat-report.md', import.meta.url);
  const markdown = readFileSync(markdownFile, 'utf8');
  writeFileSync(markdownFile, markdown.replace(/## Whole-reference scope\n[\s\S]*?(?=## Extraction audit\n)/, scopeLines(inventory).join('\n') + '\n'));
  const jsonFile = new URL('./results/doctest-report.json', import.meta.url);
  if (existsSync(jsonFile)) {
    const report = JSON.parse(readFileSync(jsonFile, 'utf8'));
    report.scope = scopeSummary(inventory);
    writeFileSync(jsonFile, JSON.stringify(report, null, 1) + '\n');
  }
}
