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
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '../..');
const PACKAGE = join(ROOT, 'packages/symjs');

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

interface Declaration {
  kind: string;
  line: number;
  docs: string[];
  signatures: string[];
  members: MemberRecord[];
}

interface ModuleInfo {
  declarations: Map<string, Declaration>;
  /** Exported name -> [module, name in module] (re-exports and local renames). */
  links: Map<string, [string | undefined, string]>;
  /** Targets of `export * from`. */
  stars: string[];
  /** `export * as ns from` -> module. */
  namespaces: Map<string, string>;
}

const DECLARATION = /^(export )?(?:declare )?(?:default )?(?:abstract )?(function|class|const|let|var|interface|type|enum|namespace) ([A-Za-z_$][\w$]*)/;

/** The documentation comment ending right before line `i`. */
function precedingDoc(lines: string[], i: number): string | undefined {
  let j = i - 1;
  if (j < 0 || !lines[j]!.trimEnd().endsWith('*/')) return undefined;
  const end = j;
  while (j >= 0 && !lines[j]!.trimStart().startsWith('/**')) {
    if (j < end && lines[j]!.includes('*/')) return undefined;
    j--;
  }
  return j < 0 ? undefined : lines.slice(j, end + 1).join('\n');
}

/** Statement text from line `i` until its end (balanced brackets, then `;` or `{`). */
function statement(lines: string[], i: number): { text: string; end: number } {
  let depth = 0;
  let text = '';
  for (let j = i; j < lines.length; j++) {
    const line = lines[j]!;
    text += (j > i ? '\n' : '') + line;
    for (const ch of line) {
      if (ch === '(' || ch === '[' || ch === '<') depth++;
      else if (ch === ')' || ch === ']' || ch === '>') depth = Math.max(0, depth - 1);
    }
    if (depth === 0 && /[;{]\s*$/.test(line)) return { text, end: j };
  }
  return { text, end: lines.length - 1 };
}

/** Top-level parameter names of a signature text. */
function parameters(signature: string): string[] {
  const open = signature.indexOf('(');
  if (open < 0) return [];
  let depth = 0;
  let current = '';
  const names: string[] = [];
  for (let k = open + 1; k < signature.length; k++) {
    const ch = signature[k]!;
    if (depth === 0 && (ch === ',' || ch === ')')) {
      const m = /^\s*(?:\.\.\.)?([A-Za-z_$][\w$]*)/.exec(current);
      if (m) names.push(m[1]!);
      current = '';
      if (ch === ')') break;
      continue;
    }
    if ('([{<'.includes(ch)) depth++;
    else if (')]}>'.includes(ch) && !(ch === '>' && signature[k - 1] === '=')) depth--;
    current += ch;
  }
  return names;
}

function returnsVoid(signature: string): boolean {
  return /\)\s*:\s*(void|never)\s*;?\s*$/.test(signature) || /^\s*(?:constructor|set )/.test(signature);
}

export function check(docs: string[], signatures: string[], callable: boolean): DocCheck {
  const text = docs.join('\n');
  const params = callable ? [...new Set(signatures.flatMap(parameters))] : [];
  const documented = new Set([...text.matchAll(/@param\s+(?:\{[^}]*\}\s*)?\[?([A-Za-z_$][\w$]*)/g)].map((m) => m[1]!));
  return {
    doc: docs.length > 0,
    sympy: /@see\s+SymPy\b/.test(text),
    example: /@example\b/.test(text),
    missingParams: params.filter((p) => !documented.has(p)),
    missingReturns: callable && docs.length > 0 && !/@returns?\b/.test(text) && !signatures.every(returnsVoid),
  };
}

/** Public members of a class body starting after line `start`. */
function classMembers(lines: string[], start: number): { members: MemberRecord[]; end: number } {
  const members: MemberRecord[] = [];
  const byName = new Map<string, { docs: string[]; signatures: string[]; line: number; callable: boolean }>();
  let j = start + 1;
  for (; j < lines.length; j++) {
    const line = lines[j]!;
    if (/^}/.test(line)) break;
    if (!/^ {4}\S/.test(line) || /^ {4}(\*|\/\*\*|\/\/)/.test(line)) continue;
    const m = /^ {4}(?:(?:static|readonly|abstract|override|declare|accessor|public|get|set)\s+)*(\[[^\]]+\]|#?[A-Za-z_$][\w$]*|"[^"]+"|'[^']+')(\??)(\s*[(<:;]?)/.exec(line);
    if (!m || /^ {4}(private|protected)\b/.test(line) || m[1]!.startsWith('#') || m[1]!.startsWith('_') || m[1]!.startsWith('[')) {
      j = statement(lines, j).end;
      continue;
    }
    const { text, end } = statement(lines, j);
    const name = (/\bstatic\s/.test(line.slice(0, line.indexOf(m[1]!))) ? 'static ' : '') + m[1]!;
    const doc = precedingDoc(lines, j);
    const callable = /^\s*(?:\(|<)/.test(text.slice(text.indexOf(m[1]!) + m[1]!.length + m[2]!.length)) || m[1] === 'constructor';
    const row = byName.get(name) ?? { docs: [], signatures: [], line: j + 1, callable };
    if (doc !== undefined) row.docs.push(doc);
    row.signatures.push(text);
    byName.set(name, row);
    j = end;
  }
  for (const [name, row] of byName) {
    // TypeDoc documents an undocumented constructor of a documented class through the class.
    members.push({ name, line: row.line, ...check(row.docs, row.signatures, row.callable) });
  }
  return { members, end: j };
}

function moduleSpecifier(from: string, specifier: string): string {
  return resolve(dirname(from), specifier.replace(/\.js$/, '') + '.d.ts');
}

export function parseModule(file: string): ModuleInfo {
  const text = readFileSync(file, 'utf8');
  const lines = text.split('\n');
  const info: ModuleInfo = { declarations: new Map(), links: new Map(), stars: [], namespaces: new Map() };
  const imports = new Map<string, [string, string]>();
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (/^import\s+(type\s+)?[\w${*]/.test(line) || /^export\s+(type\s+)?\{|^export\s+\*/.test(line)) {
      const { text: stmt, end } = /[;]\s*$/.test(line) ? { text: line, end: i } : (() => {
        let j = i, t = line;
        while (!/;\s*$/.test(lines[j]!) && j < lines.length - 1) t += '\n' + lines[++j]!;
        return { text: t, end: j };
      })();
      const fromMatch = /from\s+['"]([^'"]+)['"]/.exec(stmt);
      const target = fromMatch ? moduleSpecifier(file, fromMatch[1]!) : undefined;
      const braces = /\{([^}]*)\}/.exec(stmt);
      const items = braces ? braces[1]!.split(',').map((s) => s.trim().replace(/^type\s+/, '')).filter(Boolean) : [];
      if (stmt.startsWith('import')) {
        if (target) for (const item of items) {
          const [a, b] = item.split(/\s+as\s+/);
          imports.set((b ?? a)!, [target, a!]);
        }
        const ns = /import\s+\*\s+as\s+([\w$]+)/.exec(stmt);
        if (ns && target) imports.set(ns[1]!, [target, '*']);
      } else if (/^export\s+\*\s+as\s+([\w$]+)/.test(stmt)) {
        info.namespaces.set(/^export\s+\*\s+as\s+([\w$]+)/.exec(stmt)![1]!, target!);
      } else if (/^export\s+\*/.test(stmt)) {
        info.stars.push(target!);
      } else if (braces) {
        for (const item of items) {
          const [a, b] = item.split(/\s+as\s+/);
          info.links.set((b ?? a)!, [target, a!]);
        }
      }
      i = end;
      continue;
    }
    const m = DECLARATION.exec(line);
    if (!m) continue;
    const [, exported, kind, name] = m;
    const { text: sig, end } = statement(lines, i);
    const doc = precedingDoc(lines, i);
    const decl = info.declarations.get(name!) ?? { kind: kind!, line: i + 1, docs: [], signatures: [], members: [] };
    if (doc !== undefined) decl.docs.push(doc);
    decl.signatures.push(sig);
    if (kind === 'class' && /\{\s*$/.test(sig)) {
      const body = classMembers(lines, end);
      decl.members.push(...body.members);
      i = body.end;
    } else if ((kind === 'namespace' || kind === 'interface' || kind === 'enum') && /\{\s*$/.test(sig) && !/\}\s*;?\s*$/.test(sig)) {
      let j = end + 1;
      while (j < lines.length && !/^}/.test(lines[j]!)) j++;
      i = j;
    } else i = end;
    info.declarations.set(name!, decl);
    if (exported) info.links.set(name!, [undefined, name!]);
  }
  // `export { local }` of an imported binding re-exports the import.
  for (const [name, [target, local]] of info.links) {
    if (target === undefined && !info.declarations.has(local) && imports.has(local)) info.links.set(name, imports.get(local)!);
  }
  return info;
}

const modules = new Map<string, ModuleInfo>();
function moduleInfo(file: string): ModuleInfo {
  let info = modules.get(file);
  if (!info) modules.set(file, info = parseModule(file));
  return info;
}

interface Resolved { file: string; local: string; declaration?: Declaration }

function resolveExport(file: string, name: string, seen = new Set<string>()): Resolved | undefined {
  const key = `${file}#${name}`;
  if (seen.has(key)) return undefined;
  seen.add(key);
  const info = moduleInfo(file);
  const link = info.links.get(name);
  if (link) {
    const [target, local] = link;
    if (target === undefined) return { file, local, declaration: info.declarations.get(local) };
    if (local === '*') return { file: target, local: name, declaration: { kind: 'namespace', line: 1, docs: [], signatures: [], members: [] } };
    return resolveExport(target, local, seen);
  }
  if (info.namespaces.has(name)) return { file: info.namespaces.get(name)!, local: name, declaration: { kind: 'namespace', line: 1, docs: [], signatures: [], members: [] } };
  for (const star of info.stars) {
    const r = resolveExport(star, name, seen);
    if (r) return r;
  }
  return undefined;
}

function exportedNames(file: string, seen = new Set<string>()): string[] {
  if (seen.has(file)) return [];
  seen.add(file);
  const info = moduleInfo(file);
  return [...new Set([...info.links.keys(), ...info.namespaces.keys(), ...info.stars.flatMap((s) => exportedNames(s, seen))])];
}

export function collect(): ExportRecord[] {
  const out = mkdtempSync(join(tmpdir(), 'symjs-api-docs-'));
  try {
    execFileSync(join(ROOT, 'node_modules/.bin/tsc'), ['-p', join(PACKAGE, 'tsconfig.build.json'), '--emitDeclarationOnly', '--declaration', '--declarationMap', 'false', '--outDir', out], { stdio: 'inherit' });
    const pkg = JSON.parse(readFileSync(join(PACKAGE, 'package.json'), 'utf8')) as { exports: Record<string, unknown> };
    const records = new Map<string, ExportRecord>();
    for (const key of Object.keys(pkg.exports)) {
      if (key === '.' || key.includes('*') || key.endsWith('.json')) continue;
      const entry = key.slice(2);
      const file = join(out, `${entry}.d.ts`);
      for (const name of exportedNames(file)) {
        const r = resolveExport(file, name);
        const declaration = r?.declaration;
        const source = r ? relative(ROOT, join(PACKAGE, 'src', relative(out, r.file).replace(/\.d\.ts$/, '.ts'))) : '?';
        const id = `${source}#${r?.local ?? name}#${name}`;
        const existing = records.get(id);
        if (existing) { existing.entries.push(entry); continue; }
        const callable = declaration?.kind === 'function' || (declaration?.kind === 'const' && declaration.signatures.some((s) => /:\s*(\(|<)/.test(s) || /=>/.test(s)));
        records.set(id, {
          name, entries: [entry], local: r?.local ?? name, kind: declaration?.kind ?? 'unresolved', file: source, line: declaration?.line ?? 0,
          members: declaration?.members ?? [],
          ...check(declaration?.docs ?? [], declaration?.signatures ?? [], callable),
        });
      }
    }
    return [...records.values()].sort((a, b) => a.file.localeCompare(b.file) || a.line - b.line || a.name.localeCompare(b.name));
  } finally {
    rmSync(out, { recursive: true, force: true });
  }
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
