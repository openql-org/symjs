// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Lists the modules with top-level side effects (registrations into the core
 * registries) and writes them to the `sideEffects` field of package.json.
 * The feature entry points (src/*.ts) are listed too: importing an entry point
 * makes every feature it contains available, including the late-bound ones
 * reached only through re-exports (e.g. `.integrate()` after importing the
 * calculus entry). The root (src/index.ts) only re-exports the feature entry
 * points and is side-effect free: a bundler keeps the feature entry points
 * whose exports are used (and all of them for a namespace import), so that
 * `import { Rational } from '@symjs/symjs'` costs what the core entry costs.
 * Every other module is side-effect free, so bundlers may drop it when none
 * of its exports is used; this includes the side-effect-free re-exporting
 * modules (`index.ts` of a directory) through which an entry point reaches
 * optional engines that register themselves on load.
 *
 *   bun scripts/side-effects.mjs          update package.json
 *   bun scripts/side-effects.mjs --check  fail when package.json is stale
 *
 * Top-level code is recognised by formatting: a statement starting at column
 * 0 that is not a declaration, an import or an export.
 */

import { readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../packages/symjs/', import.meta.url));
const src = join(root, 'src');
const DECL = /^(import |export |const |let |var |function\*? |async function |class |abstract class |type |interface |enum |declare |[\s/*})\]@]|$)/;

function* walk(dir) {
  for (const d of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, d.name);
    if (d.isDirectory()) yield* walk(p);
    else if (d.name.endsWith('.ts')) yield p;
  }
}

export function sideEffectModules() {
  const out = [];
  for (const f of walk(src)) {
    const lines = readFileSync(f, 'utf8').split('\n');
    const rel = relative(src, f);
    const entry = !rel.includes('/') && !rel.includes('\\') && rel !== 'index.ts';
    if (entry || lines.some((l) => !DECL.test(l))) out.push(relative(src, f).replace(/\\/g, '/').replace(/\.ts$/, ''));
  }
  return out.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

export function sideEffectsField(mods = sideEffectModules()) {
  return mods.flatMap((m) => [`./src/${m}.ts`, `./dist/${m}.js`, `./dist/${m}.cjs`]);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const pkgPath = join(root, 'package.json');
  const pkg = JSON.parse(readFileSync(pkgPath, 'utf8'));
  const field = sideEffectsField();
  if (process.argv.includes('--check')) {
    if (JSON.stringify(pkg.sideEffects) !== JSON.stringify(field)) {
      console.error('package.json sideEffects is stale: run bun scripts/side-effects.mjs');
      process.exit(1);
    }
  } else {
    pkg.sideEffects = field;
    writeFileSync(pkgPath, JSON.stringify(pkg, null, 2) + '\n');
    console.log(`${field.length / 3} modules with side effects`);
  }
}
