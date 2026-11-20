// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { ATTRIBUTE_FUNCTIONS, JS_GLOBAL_RENAMES } from '../sympy-corpus/harness';
import { PUBLIC_ALIASES, MEMBER_FUNCTIONS, MATRIX_MEMBER_ALIASES } from '../sympy-corpus/doctest-harness';

export interface ApiExport {
  entries: string[];
  kind: string;
  prototype: string[];
  static: string[];
}
export interface ApiMembers {
  schema: number;
  exports: Record<string, ApiExport>;
  policy?: {
    renames: Record<string, string>;
    aliases: Readonly<Record<string, string>>;
    attributeFunctions: Readonly<Record<string, string>>;
    memberFunctions: Readonly<Record<string, readonly string[]>>;
    matrixMemberAliases: Readonly<Record<string, string>>;
  };
}

/** JavaScript's built-in constructors and prototypes. Their members differ between
 * runtime versions (Error.isError, Map.prototype.getOrInsert), so they stay out of
 * the snapshot. */
const BUILTINS: ReadonlySet<unknown> = new Set(
  [Object, Function, Error, TypeError, RangeError, Map, Set, WeakMap, WeakSet, Array, Promise, RegExp, Date, Number, String, Boolean, Symbol, BigInt, ArrayBuffer, Uint8Array, Float64Array]
    .flatMap((ctor) => [ctor, ctor.prototype, Object.getPrototypeOf(ctor.prototype)])
    .filter((value) => value !== null && value !== undefined));

/** Inspect descriptors without constructing objects or invoking getters. Include
 * inherited members, but never members of JavaScript's built-in classes. */
function members(value: unknown): string[] {
  const names = new Set<string>();
  let current = value;
  while (current !== null && (typeof current === 'object' || typeof current === 'function') && !BUILTINS.has(current)) {
    for (const name of Object.getOwnPropertyNames(current)) {
      if (name === 'constructor' || name.startsWith('_') || typeof current === 'function' && ['prototype', 'length', 'name', 'arguments', 'caller'].includes(name)) continue;
      const descriptor = Object.getOwnPropertyDescriptor(current, name);
      if (descriptor && (descriptor.get || descriptor.set || descriptor.value !== undefined)) names.add(name);
    }
    current = Object.getPrototypeOf(current);
  }
  return [...names].sort();
}

export function collectApiMembers(entries: Record<string, Record<string, unknown>>): ApiMembers {
  const exports: Record<string, ApiExport> = {};
  for (const [entry, values] of Object.entries(entries).sort(([a], [b]) => a.localeCompare(b))) {
    for (const [name, value] of Object.entries(values)) {
      if (value === undefined || value === null) continue;
      const prototype = typeof value === 'function' ? members(value.prototype) : [];
      const row = exports[name] ?? { entries: [], kind: typeof value, prototype: [], static: [] };
      row.entries.push(entry);
      row.entries.sort();
      row.prototype = [...new Set([...row.prototype, ...prototype])].sort();
      row.static = [...new Set([...row.static, ...members(value)])].sort();
      exports[name] = row;
    }
  }
  return { schema: 1, exports: Object.fromEntries(Object.entries(exports).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)) };
}

/** The package manifest, including subpath-only entries, defines the denominator.
 * Vitest loads the sources through the same entry modules as the package build. */
export async function generateApiMembers(): Promise<ApiMembers> {
  const manifest = JSON.parse(readFileSync(new URL('../../packages/symjs/package.json', import.meta.url), 'utf8')) as { exports: Record<string, unknown> };
  const entries: Record<string, Record<string, unknown>> = {};
  for (const entry of Object.keys(manifest.exports).sort()) {
    if (entry === './package.json') continue;
    const name = entry === '.' ? 'index' : entry.slice(2);
    entries[entry] = await import(/* @vite-ignore */ new URL(`../../packages/symjs/src/${name}.ts`, import.meta.url).href) as Record<string, unknown>;
  }
  const api = collectApiMembers(entries);
  api.policy = { renames: JS_GLOBAL_RENAMES, aliases: PUBLIC_ALIASES, attributeFunctions: ATTRIBUTE_FUNCTIONS, memberFunctions: MEMBER_FUNCTIONS, matrixMemberAliases: MATRIX_MEMBER_ALIASES };
  return api;
}

/** One export per line keeps inherited-member snapshots compact and reviewable. */
export function formatApiMembers(api: ApiMembers): string {
  return '{\n "schema": 1,\n "exports": {\n' + Object.entries(api.exports).map(([name, row]) => `  ${JSON.stringify(name)}: ${JSON.stringify(row)}`).join(',\n') + '\n }' + (api.policy ? ',\n "policy": ' + JSON.stringify(api.policy) : '') + '\n}\n';
}
