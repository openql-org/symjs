// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Measures what a consumer's bundle contains for typical imports of the built
 * package (dist/): minified ESM bundles made with esbuild, which honours the
 * `sideEffects` field of package.json.
 *
 *   pnpm build && node scripts/size.mjs           print the table
 *   node scripts/size.mjs --check                 also fail when a budget is exceeded
 *   node scripts/size.mjs --json                  machine-readable output
 */

import { createRequire } from 'node:module';
import { gzipSync } from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { join } from 'node:path';

const root = fileURLToPath(new URL('..', import.meta.url));
const require = createRequire(import.meta.url);
const esbuild = createRequire(require.resolve('tsup'))('esbuild');

/**
 * [entry, imported names ('*' for the namespace), budget in KiB (minified)].
 * The budgets are the sizes measured when they were set plus about 10%:
 * raise one only together with the change that needs it.
 */
// Symbol metadata, relation accessors, function arities and special-function
// queries add at most 2 KiB to the affected core/special/printing consumers.
// Assumption-aware solve loads the predicate engine; keep its cost explicit.
// Order containment and AccumBounds interval comparisons add at most 1 KiB
// to consumers of core; pretty also gains symbolic-tuple layout.
// Public comparison, symbol-naming and numeric helpers add about 5 KiB to the
// core namespace; shared arithmetic and symbol introspection add <1 KiB to strategies.
// Precision-aware comparability, bound-variable hashing and full free-symbol
// sets add up to 2 KiB to core consumers. Reduced ODE solvers also reach stats.
// Dummit's quintic coefficient tables and branch selection add at most 80 KiB
// to consumers that load radical polynomial solving.
const CASES = [
  ['core', 'Rational', 190],
  ['core', 'parse, str', 204],
  ['core', 'parse, diff, expand, str, latex', 204],
  ['core', '*', 288],
  // B-spline interpolation and multiset counting add approximately 5 KiB.
  ['special', '*', 383],
  // The standalone simplify entry now loads doit, including integral/sum evaluation.
  ['simplify', 'simplify', 970],
  // The polys entry re-exports the sparse domain matrices through a
  // side-effect-free module, and the matrices that number fields use call
  // simplify late-bound, so factor loads neither (measured 542 KiB, was 701).
  ['polys', 'factor', 676],
  // Finite-domain Poly arithmetic/cancellation adds the shared GF algorithms
  // to consumers of the polynomial engine.
  ['calculus', 'integrate', 997],
  ['solvers', 'solve', 1055],
  ['solvers', 'dsolve', 1070],
  ['sets', '*', 353],
  ['matrices', 'Matrix', 749],
  ['printing', 'pretty', 230],
  ['discrete', '*', 285],
  ['strategies', '*', 203],
  // LaTeX parsing includes explicit matrix expressions and both hand-written grammars.
  ['parsing', '*', 800],
  ['unify', '*', 228],
  // Matrices of numbers (quaternions, ciphers, Lie algebras) no longer bring
  // the simplification engine (measured 497/334/314 KiB, was 577/581/577).
  ['algebras', 'Quaternion', 547],
  ['holonomic', 'exprToHolonomic', 1140],
  ['geometry', '*', 1078],
  ['vector', '*', 1176],
  ['stats', '*', 1285],
  // Diagram layout, pretty grids and Xy-pic text generation.
  ['categories', '*', 442],
  // Numeric meshing plus symbolic discontinuities and finite-sum evaluation.
  ['plotting', '*', 1005],
  ['crypto', '*', 367],
  ['liealgebras', '*', 345],
  // The root is side-effect free: a named import brings only the entry points
  // of the names used (measured 177 KiB, the core entry; was 1312).
  ['index', 'Rational', 195],
  // The finitely presented groups, coset enumeration and homomorphisms of combinatorics (measured 2292 KiB).
  // Galois resolvents, Tschirnhausen transformations and the S6 subgroup search add about 10 KiB.
  ['index', '*', 2635],
  // Differential geometry includes symbolic inversion and curvature calculations.
  ['diffgeom', '*', 1200],
];

async function measure(entry, names) {
  const file = join(root, 'dist', `${entry}.js`);
  const code = names === '*' ? `import * as m from ${JSON.stringify(file)}; console.log(m);` : `import { ${names} } from ${JSON.stringify(file)}; console.log(${names});`;
  const r = await esbuild.build({
    stdin: { contents: code, resolveDir: root, loader: 'js' },
    bundle: true,
    minify: true,
    format: 'esm',
    platform: 'neutral',
    write: false,
    metafile: true,
    logLevel: 'silent',
  });
  const out = r.outputFiles[0].contents;
  const modules = Object.keys(Object.values(r.metafile.outputs)[0].inputs).length;
  return { bytes: out.length, gzip: gzipSync(out).length, modules };
}

const rows = [];
for (const [entry, names, budget] of CASES) rows.push({ entry, names, budget, ...(await measure(entry, names)) });
if (process.argv.includes('--json')) console.log(JSON.stringify(rows, null, 2));
else {
  const kib = (n) => (n / 1024).toFixed(0).padStart(5);
  console.log('entry      import                              KiB   gzip  modules  budget');
  for (const r of rows) console.log(`${r.entry.padEnd(10)} ${r.names.padEnd(34)} ${kib(r.bytes)}  ${kib(r.gzip)}  ${String(r.modules).padStart(7)}  ${String(r.budget).padStart(6)}${r.bytes > r.budget * 1024 ? '  OVER' : ''}`);
}
if (process.argv.includes('--check') && rows.some((r) => r.bytes > r.budget * 1024)) process.exit(1);
