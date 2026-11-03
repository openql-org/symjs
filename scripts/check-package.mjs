// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Exercise the files shipped to users, outside the workspace's source aliases.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const require = createRequire(import.meta.url);
const esbuild = createRequire(require.resolve('tsup'))('esbuild');
const dir = mkdtempSync(join(tmpdir(), 'symjs-package-'));
const entries = [];
try {
  for (const name of ['symjs', 'mathjs', 'physics-quantum']) {
    const source = join(root, 'packages', name);
    const pkg = JSON.parse(readFileSync(join(source, 'package.json'), 'utf8'));
    const dest = join(dir, 'node_modules', pkg.name);
    mkdirSync(dest, { recursive: true });
    for (const file of ['package.json', ...pkg.files]) cpSync(join(source, file), join(dest, file), { recursive: true });
    for (const key of Object.keys(pkg.exports)) {
      if (key === './package.json') continue;
      entries.push(key === '.' ? pkg.name : pkg.name + key.slice(1));
    }
  }
  const assertions = `
    const [x] = sj.symbols('x');
    const u = new sj.Dummy('u');
    assert.equal(String(sj.diff(x.pow(3), x)), '3*x**2');
    assert.equal(sj.dummyEq(u.pow(2).add(1), x.pow(2).add(1)), true);
    assert.equal(sj.find(u.add(x), { type: 'Dummy' }).includes(u), true);
    assert.equal(String(sj.integrate(x.pow(-2), x, [-1, 1])), 'oo');
    const [n] = sj.symbols('n', { integer: true });
    assert.deepEqual(sj.solve(n.pow(2).sub(2), n), []);
    assert.equal(gates.H().mul(gates.H()).equals(sj.Matrix.eye(2)), true);
    assert.equal(String(fromMathjsValue(3)), '3');
  `;
  const esm = `import assert from 'node:assert/strict';
    import * as sj from '@symjs/symjs';
    import { Sym } from '@symjs/symjs/core';
    import { gates } from '@symjs/physics-quantum';
    import { fromMathjsValue } from '@symjs/mathjs';
    assert.equal(sj.Sym, Sym);
    ${assertions}
    ${entries.map((e) => `await import(${JSON.stringify(e)});`).join('\n')}
  `;
  const cjs = `const assert = require('node:assert/strict');
    const sj = require('@symjs/symjs');
    const { Sym } = require('@symjs/symjs/core');
    const { gates } = require('@symjs/physics-quantum');
    const { fromMathjsValue } = require('@symjs/mathjs');
    assert.equal(sj.Sym, Sym);
    ${assertions}
    ${entries.map((e) => `require(${JSON.stringify(e)});`).join('\n')}
  `;
  for (const [file, text] of [['consumer.mjs', esm], ['consumer.cjs', cjs]]) {
    writeFileSync(join(dir, file), text);
    execFileSync(process.execPath, [file], { cwd: dir, stdio: 'pipe' });
  }
  // Bundlers are free to rename classes: test both ordinary and minified output.
  for (const minify of [false, true]) {
    const outfile = join(dir, `bundle-${minify}.mjs`);
    await esbuild.build({ entryPoints: [join(dir, 'consumer.mjs')], outfile, bundle: true, minify, platform: 'node', format: 'esm', logLevel: 'silent' });
    execFileSync(process.execPath, [outfile], { cwd: dir, stdio: 'pipe' });
  }
  const types = `import { symbols, diff, Dummy, dummyEq } from '@symjs/symjs';
    import { gates } from '@symjs/physics-quantum';
    import { fromMathjsValue } from '@symjs/mathjs';
    const [x] = symbols('x');
    const answer: string = diff(x.pow(2), x).toString();
    const equal: boolean = dummyEq(new Dummy('u'), x);
    gates.H(); fromMathjsValue(3);
    ${entries.map((e, i) => `import * as entry${i} from ${JSON.stringify(e)}; void entry${i};`).join('\n')}
    void [answer, equal];
  `;
  for (const file of ['consumer.mts', 'consumer.cts']) writeFileSync(join(dir, file), types);
  for (const [module, moduleResolution] of [['NodeNext', 'NodeNext'], ['ESNext', 'Bundler']]) {
    writeFileSync(join(dir, 'tsconfig.json'), JSON.stringify({
      compilerOptions: { target: 'ES2022', module, moduleResolution, strict: true, noEmit: true, skipLibCheck: false, types: [] },
      files: ['consumer.mts', 'consumer.cts'],
    }));
    execFileSync(join(root, 'node_modules/.bin/tsc'), ['-p', join(dir, 'tsconfig.json')], { cwd: dir, stdio: 'pipe' });
  }
  assert.ok(entries.length > 2);
  console.log(`Package checks passed: ${entries.length} entry points, ESM/CJS, bundled/minified, NodeNext/Bundler declarations.`);
} catch (error) {
  if (error.stdout) process.stderr.write(error.stdout);
  if (error.stderr) process.stderr.write(error.stderr);
  throw error;
} finally {
  rmSync(dir, { recursive: true, force: true });
}
