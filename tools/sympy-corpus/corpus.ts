// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { readFileSync } from 'node:fs';
import type { Case } from './harness.js';

export type Kind = 'doctest' | 'unittest';
export interface Shard { file: string; cases: number; bytes: number }
export interface Category { shards: Shard[]; cases: number; auditFile: string; auditBytes: number }
export interface Index { sympy: string; categories: Record<string, Category> }
export interface Api { name: string; category: string; owner?: string }
interface Omission { module: string; src: string; reason: string }
export interface DoctestIndex extends Index {
  caseOrder: [string, number][];
  api: Api[];
  extraction: { examined: number; reasons: Record<string, number> };
}

export function readCorpusFile<T>(kind: Kind, file: string): T {
  return JSON.parse(readFileSync(new URL(`./${kind}/${file}`, import.meta.url), 'utf8'));
}

export function readIndex<T extends Index = Index>(kind: Kind): T {
  return readCorpusFile(kind, 'index.json');
}

function* categoryCases<T>(kind: Kind, summary: Category): Generator<T> {
  for (const shard of summary.shards) {
    const cases = readCorpusFile<T[]>(kind, shard.file);
    if (cases.length !== shard.cases) throw new RangeError(`Unexpected case count in ${kind}/${shard.file}`);
    yield* cases;
  }
}

export function* readCases<T = Case>(kind: Kind, category?: string): Generator<T> {
  if (kind === 'doctest' && category === undefined) {
    const index = readIndex<DoctestIndex>(kind);
    const records = new Map(Object.entries(index.categories).map(([name, entry]) => [name, categoryCases<T>(kind, entry)]));
    for (const [name, count] of index.caseOrder) {
      const cases = records.get(name);
      if (!cases) throw new RangeError(`Unknown doctest category ${name}`);
      for (let i = 0; i < count; i++) {
        const record = cases.next();
        if (record.done) throw new RangeError(`Missing doctest records in ${name}`);
        yield record.value;
      }
    }
    for (const [name, cases] of records) {
      if (!cases.next().done) throw new RangeError(`Unconsumed doctest records in ${name}`);
    }
    return;
  }
  const index = readIndex(kind);
  for (const name of category === undefined ? Object.keys(index.categories) : [category]) {
    const summary = index.categories[name];
    if (!summary) throw new RangeError(`Unknown ${kind} category ${name}`);
    yield* categoryCases<T>(kind, summary);
  }
}

export function doctestExtraction(index: DoctestIndex) {
  const omitted: Omission[] = [];
  const preservedReferences: Omission[] = [];
  for (const { auditFile } of Object.values(index.categories)) {
    const audit = readCorpusFile<{ omitted: Omission[]; preservedReferences?: Omission[] }>('doctest', auditFile);
    omitted.push(...audit.omitted);
    preservedReferences.push(...audit.preservedReferences ?? []);
  }
  return { ...index.extraction, omitted, preservedReferences };
}
