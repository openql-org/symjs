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
// Assumption-aware solve loads the predicate engine; keep its cost explicit.
const CASES = [
  ['core', 'Rational', 170],
  ['core', 'parse, str', 185],
  ['core', 'parse, diff, expand, str, latex', 185],
  ['core', '*', 255],
  ['special', '*', 330],
  ['simplify', 'simplify', 520],
  ['polys', 'factor', 380],
  ['calculus', 'integrate', 660],
  ['solvers', 'solve', 780],
  ['solvers', 'dsolve', 790],
  ['sets', '*', 315],
  ['matrices', 'Matrix', 450],
  ['printing', 'pretty', 210],
  ['discrete', '*', 265],
  ['strategies', '*', 185],
  ['unify', '*', 210],
  ['algebras', 'Quaternion', 460],
  ['holonomic', 'exprToHolonomic', 815],
  ['geometry', '*', 790],
  ['vector', '*', 900],
  ['stats', '*', 855],
  ['index', 'Rational', 1005],
  ['index', '*', 1710],
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
