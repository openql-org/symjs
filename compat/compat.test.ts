// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Computes the SymPy compatibility metrics and writes compat/REPORT.md and
 * compat/report.json. Run with `pnpm compat`.
 */

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { runBaseChecks } from './base-scope';
import { runOdeChecks } from './ode-checks';
import { evidenceFor, adapterInventory } from './adapter-audit';

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
  const sub = /^src\/(discrete|algebras|strategies|unify|geometry|vector|stats|categories|tensor|combinatorics|crypto|liealgebras|parsing)[/.]/.exec(path);
  if (sub) return sub[1]!;
  return 'core';
}

/** Per-file coverage from coverage/coverage-summary.json (written by `pnpm coverage`). */
function readCoverage(): { files: FileCoverage[] } | undefined {
  const url = new URL('../coverage/coverage-summary.json', import.meta.url);
  if (!existsSync(url)) return undefined;
  const data = JSON.parse(readFileSync(url, 'utf8')) as Record<string, Record<string, { total: number; pct: number }>>;
  const root = new URL('..', import.meta.url).pathname;
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
import { expect, it } from 'vitest';
import { Case, Outcome, counterpartFor, hasCounterpart, runCase } from './harness';
import { PORTS } from './ports';

interface Corpus {
  sympy: string;
  api: { name: string; category: string; owner?: string }[];
  cases: Case[];
  extraction: { examined: number; reasons: Record<string, number>; omitted: { module: string; src: string; reason: string }[] };
}

const CATEGORY_ORDER = ['core', 'functions', 'simplify', 'polys', 'solvers', 'ode', 'pde', 'calculus', 'matrices', 'special', 'logic', 'tensor', 'ntheory', 'assumptions', 'utilities', 'combinatorics', 'sets', 'printing', 'discrete', 'algebras', 'strategies', 'unify', 'geometry', 'vector', 'stats', 'categories', 'crypto', 'liealgebras', 'parsing'];

// a rate below 100% never prints as 100.0%
const pct = (a: number, b: number) => (b === 0 ? '-' : `${(a < b ? Math.min((100 * a) / b, 99.9) : 100).toFixed(1)}%`);

/** Cases and APIs that symjs does not support yet (compat/known-gaps.json). */
interface KnownGaps {
  cases: string[];
  api: string[];
}
const caseLabel = (c: Case): string => `${c.module}: ${c.src}`;
const caseKey = (c: Case): string => `${caseLabel(c)} #${createHash('sha256').update(JSON.stringify([c.args, c.kwargs, c.self, c.expected, c.assume])).digest('hex').slice(0, 16)}`;

/**
 * Doctests outside the scope of symjs, by case key, with the reason. They are not run or counted:
 * they exercise no symjs functionality, so a "pass" would say nothing.
 */
const OUT_OF_SCOPE: Readonly<Record<string, string>> = {
  // plotting is not ported (FourierSeries plot objects)
  'sympy.series.fourier: p.show()': 'plotting',
  // a TensorFlow setting from the lambdify docstring; lambdify for TensorFlow is not ported
  'sympy.utilities.lambdify: tf.compat.v1.enable_eager_execution()': 'TensorFlow',
  // sympy.stats sampling (sample, sample_iter, sampling_density, numsamples=) needs an external sampling library
  // (numpy/scipy/pymc) and is out of scope; its doctests print random values or are marked +SKIP, so the
  // extractor (compat/extract.py) keeps none of them and no entry is needed here
  // Python's in-place list.sort() from a docstring setup line, no SymPy call
  'sympy.utilities.iterables: a.sort()': 'Python list method',
  // Python threads from the global_parameters docstring (SymPy's evaluate flag is thread-local); no SymPy call
  'sympy.core.parameters: thread.start()': 'Python threading',
  'sympy.core.parameters: thread.join()': 'Python threading',
  // the LaTeX of the Python class int (a Python type object, not a SymPy expression)
  'sympy.printing.latex: print(latex(int))': 'Python type object',
};
const apiKey = (a: { name: string; category: string; owner?: string }): string => `${a.category}: ${a.owner ? a.owner + ':' : ''}${a.name}`;
/**
 * SymPy public names outside the scope of symjs by user decision, by API key, with the reason. They are
 * not counted in the API presence (compat/extract.py no longer lists them; this keeps an older corpus
 * consistent). Their modules are 'excluded' in scope-inventory.json with the same reason.
 */
const OUT_OF_SCOPE_API: Readonly<Record<string, string>> = {
  // sympy.categories.diagram_drawing: drawing category diagrams is deferred like plotting
  'categories: DiagramGrid': 'diagram drawing (decided later)',
  'categories: XypicDiagramDrawer': 'diagram drawing (decided later)',
  'categories: xypic_draw_diagram': 'diagram drawing (decided later)',
};

it('computes SymPy compatibility metrics', () => {
  const corpus: Corpus = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8'));
  const extractedCalls = corpus.cases.length;
  corpus.cases = corpus.cases.filter((c) => OUT_OF_SCOPE[caseLabel(c)] === undefined);
  corpus.api = corpus.api.filter((a) => OUT_OF_SCOPE_API[apiKey(a)] === undefined);
  const results = corpus.cases.map((c) => ({ c, o: runCase(c) as Outcome, evidence: evidenceFor(c) }));
  const verifiedPass = results.filter(({ o, evidence }) => (o.status === 'pass' || o.status === 'equivalent') && (evidence === 'public-call' || evidence === 'reviewed-conversion')).length;
  const inventory = JSON.parse(readFileSync(new URL('./scope-inventory.json', import.meta.url), 'utf8')) as { reference: { sympy: string }; modules: { module: string; status: string; selectedForExtraction: boolean; hasCorpusCases: boolean; documentedExamples: number; reason?: string }[] };
  const scopeCounts = Object.fromEntries(['partial', 'unimplemented', 'unassessed', 'excluded'].map((status) => [status, inventory.modules.filter((m) => m.status === status).length]));
  const capabilities = JSON.parse(readFileSync(new URL('./capabilities.json', import.meta.url), 'utf8')) as { areas: { area: string; status: string; tested: string[]; remaining: string[]; tests: string[] }[] };
  const evidenceCounts = Object.fromEntries(['public-call', 'reviewed-conversion', 'harness-computation', 'unreviewed-adapter', 'unreviewed-translation'].map((evidence) => [evidence, results.filter((r) => r.evidence === evidence).length]));
  const apiEvidence = corpus.api.map((a) => ({ ...a, counterpart: counterpartFor(a) ?? null, status: counterpartFor(a) ? 'present' : 'unverified-or-absent', directCases: corpus.cases.filter((c) => c.category === a.category && c.fn === a.name).length }));
  const ported = corpus.cases.filter((c) => PORTS[`${c.module}:${c.src}`]).length;

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
  for (const a of corpus.api) {
    const r = row(a.category);
    r.api++;
    if (hasCounterpart(a)) r.apiDone++;
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
  lines.push('# SymPy compatibility report', '');
  lines.push(`Reference: SymPy ${corpus.sympy}. Generated by \`pnpm compat\`.`, '');
  lines.push(
    '- **Corpus result agreement** (includes unaudited harness code): share of SymPy doctest examples (public API calls in the in-scope modules) for which symjs gives the same result as SymPy: either the same `str()` output (**exact**) or a mathematically equivalent value in another form (**equivalent**: equal at test points respecting the symbol assumptions, or `simplify(a - b) == 0`; sets and solution lists compared without regard to order; for `dsolve`, a solution that satisfies the equations with as many integration constants, like SymPy `checkodesol`, which also accepts a correct solution where SymPy prints a wrong one). A result left unevaluated (`Integral`, `Limit`, `Sum`, ...) where SymPy computes a value is a failure, as are cases whose arguments symjs cannot represent. The **exact** rate is reported alongside (`compat/equivalence.ts`).',
    '- **JavaScript translations**: doctests whose setup is Python code the extractor cannot serialize (user-defined classes, Python lambdas and functions as arguments, SymPy-internal containers) run as hand-written translations to the symjs public API (`compat/ports.ts`) and are compared with SymPy\'s output like the other cases.',
    '- **API presence** (not behavioral compatibility): share of in-scope public SymPy names (functions, classes, `Expr`/`Matrix` methods) that have a symjs counterpart.',
    '- **Base scope checks**: behaviors the base module is meant to guarantee (assumptions, non-commutativity, bound variables, unevaluated objects, extension nodes, ...), checked against SymPy output (`compat/base-scope.ts`).',
    '- **ODE checks**: representative equations for each SymPy `dsolve` hint (`compat/ode-checks.json`, generated by `compat/gen-ode-checks.py`). A check passes when the solution is printed like SymPy\'s (**exact**) or, in another form, satisfies the equation with as many integration constants (**equivalent**, like SymPy `checkodesol`).',
    '- **Fully covered**: source files whose unit tests reach 100% coverage. This measures test coverage, not SymPy behavior.',
    '',
  );
  lines.push(
    `**Measured corpus only: result agreement ${pct(total.pass + total.equivalent, total.cases)} (${total.pass + total.equivalent}/${total.cases}; exact ${pct(total.pass, total.cases)} ${total.pass}, equivalent ${total.equivalent}; ${ported} run as JavaScript translations), API presence ${pct(total.apiDone, total.api)} (${total.apiDone}/${total.api})**`,
    '',
  );
  lines.push(
    `**Verified public-call results: ${verifiedPass}/${total.cases} (${pct(verifiedPass, total.cases)})**. This conservative count includes automatic public calls and reviewed conversion adapters. Results depending on harness computations, unaudited adapters or translations are unverified. It is not the coverage of all SymPy functionality.`,
    '',
    '## Whole-reference scope', '',
    `Pinned inventory: **${inventory.modules.length} production modules** in SymPy ${inventory.reference.sympy}. ${inventory.modules.filter((m) => m.selectedForExtraction).length} selected for extraction; ${inventory.modules.filter((m) => m.hasCorpusCases).length} have recorded calls. No whole-SymPy behavioral percentage is established.`, '',
    '| Inventory status | Modules |', '|---|---:|',
    ...Object.entries(scopeCounts).map(([status, n]) => `| ${status} | ${n} |`), '',
    'Partial means a source correspondence exists, not that the module is complete. Unassessed modules remain visible. Exclusions and source hashes are recorded in `scope-inventory.json`; symbolic mathematical features are not excluded merely because they are difficult.', '',
    '## Extraction audit', '',
    `Examined ${corpus.extraction.examined} doctest statements including setup. Kept ${corpus.cases.length} in-scope calls; ${extractedCalls - corpus.cases.length} calls excluded by ${Object.keys(OUT_OF_SCOPE).length} explicit case labels are listed in the runner, as are ${Object.keys(OUT_OF_SCOPE_API).length} public names excluded from the API presence by user decision (${[...new Set(Object.values(OUT_OF_SCOPE_API))].join('; ')}). The detailed omitted list records ${corpus.extraction.omitted.length} examples with expected output.`, '',
    '| Reason | Statements |', '|---|---:|',
    ...Object.entries(corpus.extraction.reasons).map(([reason, n]) => `| ${reason} | ${n} |`), '',
    '## Public API evidence', '',
    `Names without a directly named corpus case: ${apiEvidence.filter((a) => a.directCases === 0).length}/${apiEvidence.length}. A method exercised under another name may still have unit tests; name presence alone does not establish correctness. Concrete export/member paths are recorded in report.json; an unmapped name is unverified or absent, not proof that the mathematical operation is unavailable.`, '',
    '| Execution route | Cases |', '|---|---:|',
    ...Object.entries(evidenceCounts).map(([kind, n]) => `| ${kind} | ${n} |`), '',
    'Every manual adapter is listed in `adapter-inventory.json`. Remaining mathematical helpers are quarantined from the verified count until migrated into public APIs. A change to adapters must update that inventory.', '',
    '## Capability conditions', '',
    '| Area | Status | Tested conditions | Remaining scope |', '|---|---|---|---|',
    ...capabilities.areas.map((a) => `| ${a.area} | ${a.status} | ${a.tested.join('; ')} | ${a.remaining.join('; ')} |`), '',
    'Direct regression-test paths are maintained in `capabilities.json`. Tensor differential operators, category diagram drawing (deferred by decision, like plotting) and unsupported PDE classes remain explicit gaps.', '',
  );
  const base = runBaseChecks();
  const basePass = base.filter((b) => b.pass).length;
  lines.push(`**Base scope checks: ${pct(basePass, base.length)} (${basePass}/${base.length})**`, '');
  const ode = runOdeChecks();
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
      'A source file counts as **fully covered** when the unit tests (`pnpm coverage`, `tests/`) cover 100% of its statements, branches, functions and lines.',
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
  writeFileSync(new URL('./REPORT.md', import.meta.url), lines.join('\n'));
  writeFileSync(
    new URL('./report.json', import.meta.url),
    JSON.stringify(
      {
        sympy: corpus.sympy,
        overall: { ...total, ported, verifiedPublicPass: verifiedPass },
        scope: { modules: inventory.modules.length, statuses: scopeCounts },
        extraction: corpus.extraction,
        apiEvidence,
        adapterEvidence: { counts: evidenceCounts, adapters: adapterInventory() },
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
  console.log(lines.slice(0, 8 + cats.length + 4).join('\n'));
  expect(total.cases).toBeGreaterThan(0);
  // Known gaps (compat/known-gaps.json): cases and APIs not supported yet. A failure that is not listed is a
  // regression; a listed entry that now passes must be removed from the list, so the list only shrinks.
  const gapsFile = new URL('./known-gaps.json', import.meta.url);
  const failing = results.filter(({ o }) => o.status !== 'pass' && o.status !== 'equivalent').map(({ c }) => caseKey(c)).sort();
  const missingApi = corpus.api.filter((a) => !hasCounterpart(a)).map(apiKey).sort();
  if (process.env['UPDATE_KNOWN_GAPS']) writeFileSync(gapsFile, JSON.stringify({ cases: failing, api: missingApi }, null, 1) + '\n');
  const gaps: KnownGaps = JSON.parse(readFileSync(gapsFile, 'utf8'));
  const knownCases = new Set(gaps.cases);
  const knownApi = new Set(gaps.api);
  expect(failing.filter((k) => !knownCases.has(k)), 'SymPy behavior regressions (not in known-gaps.json)').toEqual([]);
  expect(gaps.cases.filter((k) => !failing.includes(k)), 'fixed cases still listed in known-gaps.json').toEqual([]);
  expect(missingApi.filter((k) => !knownApi.has(k)), 'SymPy API coverage regressions (not in known-gaps.json)').toEqual([]);
  expect(gaps.api.filter((k) => !missingApi.includes(k)), 'APIs now supported but still listed in known-gaps.json').toEqual([]);
  expect(baseFail, 'base scope regressions').toEqual([]);
  expect(odeFail, 'ODE regressions').toEqual([]);
});
