// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { spawnSync } from 'node:child_process';
import { readIndex } from '../corpus';

const [kind, category, ...options] = process.argv.slice(2).filter(arg => arg !== '--');
if ((kind !== 'doctest' && kind !== 'unittest') || !category || !Object.hasOwn(readIndex(kind).categories, category)) {
  throw new RangeError('Use corpus:compat:doctest or corpus:compat:unittest with a category name');
}
const run = spawnSync('vitest', ['run', '--config', 'tools/sympy-corpus/compat/vitest.config.ts',
  '--project', `${kind}-${category}`, ...options], { stdio: 'inherit' });
if (run.error) throw run.error;
process.exitCode = run.status ?? 1;
