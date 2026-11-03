// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// tsc emits declarations once; publish separate ESM and CommonJS declaration
// graphs so NodeNext resolves both the conditional exports and relative imports.
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';

const root = resolve(process.argv[2]);
function files(dir) {
  return readdirSync(dir, { withFileTypes: true }).flatMap((e) =>
    e.isDirectory() ? files(join(dir, e.name)) : e.name.endsWith('.d.ts') ? [join(dir, e.name)] : []);
}
for (const file of files(root)) {
  const source = readFileSync(file, 'utf8');
  const rewrite = (extension) => source.replace(/(\bfrom\s+|\bimport\s*\(\s*|\bimport\s*)(['"])(\.[^'"]+)\2/g, (_match, prefix, quote, specifier) => {
    let path = specifier.replace(/\.(?:c?js)$/, '');
    if (!existsSync(resolve(dirname(file), path + '.d.ts'))) {
      path += '/index';
      if (!existsSync(resolve(dirname(file), path + '.d.ts'))) throw new Error(`Unresolved declaration import: ${file}: ${specifier}`);
    }
    return `${prefix}${quote}${path}${extension}${quote}`;
  });
  writeFileSync(file, rewrite('.js'));
  writeFileSync(file.replace(/\.d\.ts$/, '.d.cts'), rewrite('.cjs'));
}
