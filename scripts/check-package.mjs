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
    assert.equal('Manifold' in sj, false);
    assert.equal('parseLatex' in sj, false);
    assert.equal(String(parsing.parseLatexLark('x^2')), 'x**2');
    assert.notEqual(sj.Point, dg.Point);
    assert.equal(String(sj.rcall(dg.Differential(dg.R2.x), dg.R2.eX)), '1');
    assert.equal(dg.metricToRicciComponents(dg.TensorProduct(dg.R2.dx, dg.R2.dx).add(dg.TensorProduct(dg.R2.dy, dg.R2.dy))).flatElements().every(e => e.equals(0)), true);
    const object = new sj.SymObject('A');
    assert.equal(sj.IdentityMorphism(object).compose(sj.IdentityMorphism(object)).domain.equals(object), true);
    assert.equal(sj.SymmetricGroup(8).order(), 40320n);
    const field = sj.toNumberField(sj.sqrt(2), sj.add(sj.sqrt(2), sj.sqrt(3)));
    assert.equal(String(field.coeffs()), '1/2,0,-9/2,0');
    const L = sj.TensorIndexType('L', { dim: 4 }), i = sj.TensorIndex('i', L);
    assert.equal(String(sj.contractMetric(L.metric.at(i, i.neg()), L.metric)), '4');
    const [y] = sj.symbols('y'), f = sj.SymFunction('f')(x, y);
    const pde = sj.add(sj.diff(f, x), sj.diff(f, y));
    assert.equal(sj.checkpdesol(pde, sj.pdsolve(pde), f)[0], true);
    assert.equal(sj.encipherShift('ABC', 1), 'BCD');
    assert.equal(String(sj.CartanMatrix('A2')), 'Matrix([[2, -1], [-1, 2]])');
  `;
  const esm = `import assert from 'node:assert/strict';
    import * as sj from '@symjs/symjs';
    import * as dg from '@symjs/symjs/diffgeom';
    import * as parsing from '@symjs/symjs/parsing';
    import { Sym } from '@symjs/symjs/core';
    import { Diagram } from '@symjs/symjs/categories';
    import { encipherShift } from '@symjs/symjs/crypto';
    import { CartanType } from '@symjs/symjs/liealgebras';
    import { expm1 } from '@symjs/symjs/codegen';
    import { gates } from '@symjs/physics-quantum';
    import { fromMathjsValue } from '@symjs/mathjs';
    assert.equal(sj.Sym, Sym);
    assert.equal(sj.Diagram, Diagram);
    assert.equal(sj.encipherShift, encipherShift);
    assert.equal(CartanType('A3').dimension(), 4);
    assert.equal(sj.expm1, expm1);
    assert.equal(String(expm1(0)), '0');
    ${assertions}
    ${entries.map((e) => `await import(${JSON.stringify(e)});`).join('\n')}
  `;
  const cjs = `const assert = require('node:assert/strict');
    const sj = require('@symjs/symjs');
    const dg = require('@symjs/symjs/diffgeom');
    const parsing = require('@symjs/symjs/parsing');
    const { Sym } = require('@symjs/symjs/core');
    const { Diagram } = require('@symjs/symjs/categories');
    const { encipherShift } = require('@symjs/symjs/crypto');
    const { CartanType } = require('@symjs/symjs/liealgebras');
    const { expm1 } = require('@symjs/symjs/codegen');
    const { gates } = require('@symjs/physics-quantum');
    const { fromMathjsValue } = require('@symjs/mathjs');
    assert.equal(sj.Sym, Sym);
    assert.equal(sj.Diagram, Diagram);
    assert.equal(sj.encipherShift, encipherShift);
    assert.equal(CartanType('A3').dimension(), 4);
    assert.equal(sj.expm1, expm1);
    assert.equal(String(expm1(0)), '0');
    ${assertions}
    ${entries.map((e) => `require(${JSON.stringify(e)});`).join('\n')}
  `;
  for (const [file, text] of [['consumer.mjs', esm], ['consumer.cjs', cjs]]) {
    writeFileSync(join(dir, file), text);
    execFileSync(process.execPath, [file], { cwd: dir, stdio: 'pipe' });
  }
  // The subpath must initialize its engines without importing the root entry.
  const standaloneChecks = `
    const { R2, R2R, R2P, R2Origin, CoordSystem, TensorProduct, metricToRicciComponents } = dg;
    assert.equal(R2R.point([3, 4]).coords(R2P).get(0, 0).equals(5), true);
    const x = R2R.coordinateNames[0];
    const y = R2R.coordinateNames[1];
    const relations = new Map([[['A', 'B'], [[x, y], [x.mul(2), y.add(1)]]]]);
    const a = new CoordSystem('A', R2Origin, [x, y], relations);
    const b = new CoordSystem('B', R2Origin, [x, y], relations);
    assert.deepEqual(b.transform(a, [4, 3]).data.map(String), ['2', '2']);
    const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
    assert.equal(metricToRicciComponents(metric).flatElements().every(e => e.equals(0)), true);
  `;
  for (const [file, imports] of [
    ['diffgeom.mjs', "import assert from 'node:assert/strict'; import * as dg from '@symjs/symjs/diffgeom';"],
    ['diffgeom.cjs', "const assert = require('node:assert/strict'); const dg = require('@symjs/symjs/diffgeom');"],
  ]) {
    writeFileSync(join(dir, file), imports + standaloneChecks);
    execFileSync(process.execPath, [file], { cwd: dir, stdio: 'pipe' });
  }
  // Bundlers are free to rename classes: test both ordinary and minified output.
  for (const minify of [false, true]) {
    const outfile = join(dir, `bundle-${minify}.mjs`);
    await esbuild.build({ entryPoints: [join(dir, 'consumer.mjs')], outfile, bundle: true, minify, platform: 'node', format: 'esm', logLevel: 'silent' });
    execFileSync(process.execPath, [outfile], { cwd: dir, stdio: 'pipe' });
    const standalone = join(dir, `diffgeom-bundle-${minify}.mjs`);
    await esbuild.build({ entryPoints: [join(dir, 'diffgeom.mjs')], outfile: standalone, bundle: true, minify, platform: 'node', format: 'esm', logLevel: 'silent' });
    execFileSync(process.execPath, [standalone], { cwd: dir, stdio: 'pipe' });
  }
  const types = `import { symbols, diff, Dummy, dummyEq } from '@symjs/symjs';
    import { gates } from '@symjs/physics-quantum';
    import { fromMathjsValue } from '@symjs/mathjs';
    import { SymObject, NamedMorphism, Diagram } from '@symjs/symjs/categories';
    const a = new SymObject('A'); const diagram = Diagram([NamedMorphism(a, a, 'f')]);
    void diagram.objects;
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
