// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Generate the corpus and verify the emitted tests in successive Vitest runs. */
import { spawnSync } from 'node:child_process';
import { readFileSync, rmSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../../../', import.meta.url));
const args = process.argv.slice(2);
if (!args.some(arg => /^--maxWorkers(?:=|$)/.test(arg))) args.push('--maxWorkers=2');
const vitest = `${root}node_modules/.bin/vitest`;
const generate = spawnSync(vitest, ['run', '--config', 'tools/sympy-corpus/totests/vitest.config.ts',
  'tools/sympy-corpus/totests/generate.test.ts', '--silent=false', ...args],
{ cwd: root, stdio: 'inherit', env: { ...process.env, UPDATE_CORPUS_TESTS: '1' } });
if (generate.status !== 0) process.exit(generate.status ?? 1);

const rangesFile = `${root}node_modules/.corpus-ranges.json`;
const ranges = new Map<string, [number, number, string][]>(JSON.parse(readFileSync(rangesFile, 'utf8')));
rmSync(rangesFile);
const report = `${root}node_modules/.corpus-tests.json`;
rmSync(report, { force: true });
const check = spawnSync(vitest, ['run', '--reporter=json', `--outputFile=${report}`, '--includeTaskLocation',
  '.corpus.test.ts', ...args], { cwd: root, stdio: 'inherit' });
const UNREPRODUCED = `${root}tools/sympy-corpus/totests/unreproduced.json`;
const unreproduced: string[] = process.env['CORPUS_RECHECK_TYPES'] ? [] : JSON.parse(readFileSync(UNREPRODUCED, 'utf8'));
const results = JSON.parse(readFileSync(report, 'utf8')) as { testResults: { name: string; message?: string; assertionResults: { status: string; location?: { line: number } }[] }[] };
rmSync(report);
const stale = new Set<string>();
const failedFiles: string[] = [];
for (const file of results.testResults) {
  if (file.message) failedFiles.push(`${file.name}: ${file.message.split('\n')[0] ?? ''}`);
  for (const a of file.assertionResults) {
    if (a.status !== 'failed') continue;
    const line = a.location?.line ?? 0;
    const hit = ranges.get(file.name)?.find(([x, y]) => line >= x && line <= y);
    if (hit) stale.add(hit[2]);
    else failedFiles.push(`${file.name}:${line}`);
  }
}
if (failedFiles.length > 0) console.log(`failures outside the cases:\n${failedFiles.join('\n')}`);
writeFileSync(UNREPRODUCED, JSON.stringify([...new Set([...unreproduced, ...stale])].sort(), null, 1) + '\n');
console.log(`unreproduced: ${stale.size}`);
if (check.status !== 0) process.exit(check.status ?? 1);
