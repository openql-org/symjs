// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/**
 * Documentation comment coverage of the public API of `@symjs/symjs`.
 *
 * Emits the declarations of `packages/symjs` with `tsc` into a temporary
 * directory, follows every entry point of `package.json` `exports` to the
 * declaration of each export, and checks the documentation comment of the
 * declaration and of the public members of exported classes against the rules
 * of docs/api-policy.md ("Documentation comments").
 *
 * Usage: `bun tools/api-docs/coverage.ts [--json <file>] [--markdown <file>]`.
 * Without options it prints the summary per entry point.
 */
import { writeFileSync } from 'node:fs';
import { withDeclarations, callParameters } from './declarations';
import type { Member } from './declarations';

export interface DocCheck {
  /** Documentation comment present. */
  doc: boolean;
  /** `@see SymPy ...` present. */
  sympy: boolean;
  /** `@example` present. */
  example: boolean;
  /** Parameters without `@param` (functions and methods). */
  missingParams: string[];
  /** A non-void function or method without `@returns`. */
  missingReturns: boolean;
}

export interface MemberRecord extends DocCheck {
  name: string;
  line: number;
}

export interface ExportRecord extends DocCheck {
  /** Public name. */
  name: string;
  /** Entry points that export the name (`core`, `polys`, ...; the root is omitted). */
  entries: string[];
  /** Name in the declaring module. */
  local: string;
  /** `function`, `class`, `const`, `type`, `interface`, `enum`, `namespace`. */
  kind: string;
  /** Source file of the declaration, relative to the repository. */
  file: string;
  /** Line of the declaration in the emitted `.d.ts` (the source line differs). */
  line: number;
  /** Public members of a class. */
  members: MemberRecord[];
}

function returnsVoid(signature: string): boolean {
  return /\)\s*:\s*(void|never)\s*;?\s*$/.test(signature) || /^\s*(?:constructor|set )/.test(signature);
}

export function check(docs: string[], signatures: string[], callable: boolean): DocCheck {
  const text = docs.join('\n');
  const params = callable ? [...new Set(signatures.flatMap(callParameters))] : [];
  const documented = new Set([...text.matchAll(/@param\s+(?:\{[^}]*\}\s*)?\[?([A-Za-z_$][\w$]*)/g)].map((m) => m[1]!));
  return {
    doc: docs.some(Boolean),
    sympy: /@see\s+SymPy\b/.test(text),
    example: /@example\b/.test(text),
    missingParams: params.filter((p) => !documented.has(p)),
    missingReturns: callable && docs.some(Boolean) && !/@returns?\b/.test(text) && !signatures.every(returnsVoid),
  };
}

function coverageMember(member: Member): MemberRecord {
  return {
    name: (member.static ? 'static ' : '') + member.name, line: member.line,
    ...check(member.docs, member.signatures, member.callable),
  };
}

export function collect(): ExportRecord[] {
  return withDeclarations((graph) => {
    const records = new Map<string, ExportRecord>();
    for (const entry of graph.entries) {
      if (!entry.path) continue;
      for (const [name, r] of entry.exports) {
        const decl = r?.declaration;
        const file = r ? graph.source(r.file) : '?';
        const local = r?.local ?? name;
        const id = `${file}#${local}#${name}`;
        const existing = records.get(id);
        if (existing) { existing.entries.push(entry.path); continue; }
        const callable = decl?.kind === 'function' || (decl?.kind === 'const' && decl.signatures.some((s) => /^.*?const [\w$]+: [<(]/.test(s)));
        records.set(id, {
          name, entries: [entry.path], local, kind: decl?.kind ?? 'unresolved', file, line: decl?.line ?? 0,
          members: decl?.kind === 'class' ? decl.members.filter((m) => !m.protected && !m.name.startsWith('[') && !m.name.startsWith('_')).map(coverageMember) : [],
          ...check(decl?.docs ?? [], decl?.signatures ?? [], callable),
        });
      }
    }
    return [...records.values()].sort((a, b) => a.file.localeCompare(b.file) || a.line - b.line || a.name.localeCompare(b.name));
  });
}

function percent(n: number, d: number): string {
  return d === 0 ? '-' : `${(100 * n / d).toFixed(1)}%`;
}

export function markdown(records: ExportRecord[]): string {
  const area = (r: ExportRecord) => r.file.split('/')[3]?.replace(/\.ts$/, '') ?? '?';
  const groups = new Map<string, ExportRecord[]>();
  for (const r of records) groups.set(area(r), [...(groups.get(area(r)) ?? []), r]);
  const members = records.flatMap((r) => r.members);
  const row = (label: string, rs: ExportRecord[]) => {
    const ms = rs.flatMap((r) => r.members);
    const complete = rs.filter((r) => r.doc && r.missingParams.length === 0 && !r.missingReturns).length;
    return `| ${label} | ${rs.length} | ${percent(rs.filter((r) => r.doc).length, rs.length)} | ${percent(complete, rs.length)} | ${percent(rs.filter((r) => r.sympy).length, rs.length)} | ${percent(rs.filter((r) => r.example).length, rs.length)} | ${ms.length} | ${percent(ms.filter((m) => m.doc).length, ms.length)} |`;
  };
  const lines = [
    '# API documentation coverage',
    '',
    'Generated by `bun tools/api-docs/coverage.ts --markdown docs/api-docs-coverage.md`. The rules are in [api-policy.md](api-policy.md#documentation-comments).',
    '',
    `Exports: **${records.length}**, documented **${records.filter((r) => r.doc).length}**. Public class members: **${members.length}**, documented **${members.filter((m) => m.doc).length}**.`,
    '',
    '"Signature" counts the documented exports whose comment has `@param` for every parameter and `@returns` for a non-void result.',
    '',
    '| Source area | Exports | Documented | Signature | `@see SymPy` | `@example` | Members | Documented |',
    '|---|---:|---:|---:|---:|---:|---:|---:|',
    ...[...groups].sort(([a], [b]) => a.localeCompare(b)).map(([g, rs]) => row(g, rs)),
    row('**total**', records),
    '',
  ];
  return lines.join('\n');
}

if (import.meta.main) {
  const args = process.argv.slice(2);
  const records = collect();
  const option = (flag: string) => { const k = args.indexOf(flag); return k < 0 ? undefined : args[k + 1]; };
  const json = option('--json');
  if (json) writeFileSync(json, JSON.stringify(records, null, 1) + '\n');
  const md = option('--markdown');
  if (md) writeFileSync(md, markdown(records));
  if (!json && !md) process.stdout.write(markdown(records));
}
