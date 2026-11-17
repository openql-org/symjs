// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Build every package with its own build script, the base package before the
// extend packages that import its declarations.
import { execSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const bin = join(root, 'node_modules', '.bin');
const path = [bin, process.env.PATH].filter(Boolean).join(delimiter);
for (const name of ['symjs', 'mathjs', 'physics-quantum']) {
  const cwd = join(root, 'packages', name);
  const { scripts } = JSON.parse(readFileSync(join(cwd, 'package.json'), 'utf8'));
  console.log(`build packages/${name}`);
  execSync(scripts.build, { cwd, stdio: 'inherit', env: { ...process.env, PATH: path } });
}
