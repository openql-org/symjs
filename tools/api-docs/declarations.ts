// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { execFileSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '../..');
const PACKAGE = join(ROOT, 'packages/symjs');

export interface Signatures {
  line: number;
  /** One comment per signature. Undocumented signatures have an empty string. */
  docs: string[];
  signatures: string[];
}

export interface Member extends Signatures {
  name: string;
  static: boolean;
  callable: boolean;
  protected: boolean;
}

export interface Declaration extends Signatures {
  kind: string;
  members: Member[];
}

interface ModuleInfo {
  comment: string;
  imports: Map<string, [string, string, boolean?]>;
  declarations: Map<string, Declaration>;
  /** Exported name -> [module, local binding, type-only flag]. */
  links: Map<string, [string | undefined, string, boolean?]>;
  /** Targets of `export * from`. */
  stars: string[];
  namespaces: Map<string, { file: string; doc: string; signature: string }>;
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

/** Offsets at the outermost level of an emitted TypeScript type or signature. */
function outerOffsets(text: string, token: string): number[] {
  const found: number[] = [];
  let depth = 0;
  for (const m of text.matchAll(/"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|`(?:\\.|[^`\\])*`|=>|[()[\]{}<>&|,]/g)) {
    if (!depth && m[0] === token) found.push(m.index);
    if ('([{<'.includes(m[0])) depth++;
    else if (')]}>'.includes(m[0])) depth--;
  }
  return found;
}

export function cleanSignature(sig: string, hide?: (comment: string) => boolean): string {
  const lines = sig.split('\n');
  const result: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    if (!lines[i]!.trimStart().startsWith('/**')) {
      result.push(lines[i]!.trimEnd());
      continue;
    }
    const start = i;
    while (i + 1 < lines.length && !lines[i]!.includes('*/')) i++;
    if (hide?.(lines.slice(start, i + 1).join('\n')) && i + 1 < lines.length) i = statementEnd(lines, i + 1);
  }
  return result.join('\n').trim();
}

export function callParameters(signature: string): string[] {
  const sig = cleanSignature(signature);
  const open = outerOffsets(sig, '(')[0];
  if (open === undefined) return [];
  const body = sig.slice(open + 1);
  const close = outerOffsets(body, ')')[0] ?? body.length;
  const args = body.slice(0, close);
  const names: string[] = [];
  let start = 0;
  for (const end of [...outerOffsets(args, ','), args.length]) {
    const name = /^\s*(?:\.\.\.)?([\w$]+)/.exec(args.slice(start, end))?.[1];
    if (name) names.push(name);
    start = end + 1;
  }
  return names;
}

/** A callable type or overload displayed under its exported name. */
export function namedCall(name: string, signature: string): string {
  const arrow = outerOffsets(signature, '=>')[0];
  if (arrow === undefined) return name + signature;
  return name + signature.slice(0, arrow).trimEnd() + ': ' + signature.slice(arrow + 2).trimStart() + ';';
}

export interface CallSignature { file: string; text: string }

/** tsc aligns a multiline declaration's terminator with its opening line. */
function statementEnd(lines: string[], start: number, terminator = /;$/): number {
  const indent = /^ */.exec(lines[start]!)![0];
  for (let i = start; i < lines.length; i++) {
    const line = lines[i]!;
    if (line.startsWith(indent) && /^\S/.test(line.slice(indent.length)) && terminator.test(line.trimEnd())) return i;
  }
  throw new Error(`Unterminated declaration at line ${start + 1}: ${lines[start]}`);
}

const MEMBER = /^    ((?:(?:static|readonly|abstract|override|declare|accessor|public|protected|get|set)\s+)*)(\[[^\]]+\]|[A-Za-z_$][\w$]*|"[^"]+"|'[^']+')(\??)/;

function membersOf(lines: string[], start: number, end: number, kind: string): Member[] {
  const members = new Map<string, Member>();
  for (let i = start + 1; i < end; i++) {
    const line = lines[i]!;
    if (!/^ {4}\S/.test(line) || /^ {4}(?:\/|\*)/.test(line)) continue;
    if (/^ {4}(?:#|private\b|protected (?!constructor\())/.test(line)) {
      i = statementEnd(lines, i);
      continue;
    }
    const match = MEMBER.exec(line);
    const call = /^    [<(]/.test(line);
    if (!match && !call) continue;
    const [, modifiers, spelling] = match ?? ['', '', '(call)'];
    const name = spelling!.replace(/^(?:"(.*)"|'(.*)')$/, (_, double?: string, single?: string) => double ?? single!);
    const isStatic = /\bstatic\b/.test(modifiers!);
    const key = (isStatic ? 'static ' : '') + name;
    const last = kind === 'enum' ? i : statementEnd(lines, i);
    const member = members.get(key) ?? {
      name, static: isStatic, protected: /\bprotected\b/.test(modifiers!), line: i + 1, docs: [], signatures: [],
      callable: call || /^[<(]/.test(line.slice(match![0].length).trimStart()),
    };
    const doc = precedingDoc(lines, i);
    member.docs.push(doc ?? '');
    member.signatures.push(lines.slice(i, last + 1).map((l) => l.slice(4)).join('\n'));
    members.set(key, member);
    i = last;
  }
  return [...members.values()];
}

export function moduleSpecifier(from: string, specifier: string): string {
  const base = resolve(dirname(from), specifier.replace(/\.js$/, ''));
  return existsSync(base + '.d.ts') ? base + '.d.ts' : join(base, 'index.d.ts');
}

export function parseModule(file: string): ModuleInfo {
  const text = readFileSync(file, 'utf8');
  const lines = text.split('\n');
  const info: ModuleInfo = { comment: /^\/\*\*[\s\S]*?\*\//.exec(text)?.[0] ?? '', imports: new Map(), declarations: new Map(), links: new Map(), stars: [], namespaces: new Map() };
  const imports = info.imports;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (/^import\s+(type\s+)?[\w${*]/.test(line) || /^export\s+(type\s+)?\{|^export\s+\*/.test(line)) {
      const end = statementEnd(lines, i);
      const stmt = lines.slice(i, end + 1).join('\n');
      const fromMatch = /from\s+['"]([^'"]+)['"]/.exec(stmt);
      const target = fromMatch ? moduleSpecifier(file, fromMatch[1]!) : undefined;
      const braces = /\{([^}]*)\}/.exec(stmt);
      const typeOnly = /^(?:import|export) type\s/.test(stmt);
      const ns = /^(?:import|export) (?:type )?\* as ([\w$]+)/.exec(stmt);
      if (ns && target) {
        if (stmt.startsWith('import')) imports.set(ns[1]!, [target, '*', typeOnly]);
        else info.namespaces.set(ns[1]!, { file: target, doc: precedingDoc(lines, i) ?? '', signature: stmt });
      } else if (braces) {
        for (const item of braces[1]!.split(',').map((s) => s.trim()).filter(Boolean)) {
          const [local, alias] = item.replace(/^type\s+/, '').split(/\s+as\s+/);
          const name = (alias ?? local)!;
          const onlyType = typeOnly || item.startsWith('type ');
          if (stmt.startsWith('export')) info.links.set(name, [target, local!, onlyType]);
          else if (target) imports.set(name, [target, local!, onlyType]);
        }
      } else if (stmt.startsWith('export *') && target) info.stars.push(target);
      i = end;
      continue;
    }
    const m = DECLARATION.exec(line);
    if (!m) continue;
    const [, exported, kind, name] = m;

    const hasBody = ['class', 'interface', 'namespace', 'enum'].includes(kind!);
    const end = statementEnd(lines, i, hasBody ? /^}$/ : /;$/);
    const sig = hasBody ? line.replace(/\s*\{$/, '') : lines.slice(i, end + 1).join('\n');
    const doc = precedingDoc(lines, i);
    const decl: Declaration = info.declarations.get(name!) ?? { kind: kind!, line: i + 1, docs: [], signatures: [], members: [] };
    decl.docs.push(doc ?? '');
    decl.signatures.push(sig);
    if (hasBody || ((kind === 'type' || kind === 'const') && line.endsWith('{') && !line.includes(' extends {'))) decl.members.push(...membersOf(lines, i, end, kind!));
    i = end;
    info.declarations.set(name!, decl);
    if (exported) info.links.set(name!, [undefined, name!]);
  }
  // `export { local }` of an imported binding re-exports the import.
  for (const [name, [target, local, typeOnly]] of info.links) {
    const imported = imports.get(local);
    if (target === undefined && !info.declarations.has(local) && imported) {
      info.links.set(name, [imported[0], imported[1], typeOnly || imported[2]]);
    }
  }
  return info;
}

export interface Resolved {
  file: string;
  local: string;
  declaration?: Declaration;
  namespace?: string;
  typeOnly?: boolean;
}

export interface Entry {
  path: string;
  comment: string;
  exports: Map<string, Resolved | undefined>;
}

export class DeclarationGraph {
  readonly entries: Entry[];
  constructor(private out: string) {
    const pkg = JSON.parse(readFileSync(join(PACKAGE, 'package.json'), 'utf8')) as {
      exports: Record<string, { import?: { types: string } } | string>;
    };
    this.entries = Object.entries(pkg.exports).flatMap(([key, value]) => {
      if (typeof value === 'string' || !value.import?.types) return [];
      const file = resolve(out, relative('./dist', value.import.types));
      return [{ path: key === '.' ? '' : key.slice(2), comment: this.moduleInfo(file).comment, exports: this.exportsOf(file) }];
    });
  }

  exportsOf(file: string): Map<string, Resolved | undefined> {
    return new Map(this.exportedNames(file).map((name) => [name, this.resolveExport(file, name)]));
  }

  source(file: string): string {
    return relative(ROOT, join(PACKAGE, 'src', relative(this.out, file).replace(/\.d\.ts$/, '.ts')));
  }

  binding(file: string, name: string): Resolved | undefined {
    const info = this.moduleInfo(file);
    const declaration = info.declarations.get(name);
    if (declaration) return { file, local: name, declaration };
    const binding = info.imports.get(name);
    return binding && this.resolveExport(binding[0], binding[1]);
  }

  /** Call signatures of values, including the types behind aliases and callable factories. */
  calls(file: string, decl: Declaration, hidden: (doc: string) => boolean, seen = new Set<Declaration>()): CallSignature[] {
    if (seen.has(decl)) return [];
    const visited = new Set(seen).add(decl);
    const result: CallSignature[] = [];
    const inspectType = (type: string) => {
      const value = type.trim();
      const arrow = outerOffsets(value, '=>')[0] ?? value.length;
      const prefix = value.slice(0, arrow);
      const parts = [...outerOffsets(prefix, '&'), ...outerOffsets(prefix, '|')].sort((a, b) => a - b);
      if (parts.length) {
        let start = 0;
        for (const end of [...parts, value.length]) {
          inspectType(value.slice(start, end));
          start = end + 1;
        }
      } else if (arrow < value.length) {
        result.push({ file, text: value });
      } else if (value.startsWith('(') && value.endsWith(')')) {
        inspectType(value.slice(1, -1));
      } else {
        const match = /^(?:typeof )?([\w$]+)(?:\.([\w$]+))?(?:<.*>)?$/s.exec(value);
        const imported = match && this.moduleInfo(file).imports.get(match[1]!);
        if (match?.[2] && imported?.[1] === '*') {
          const target = this.resolveExport(imported[0], match[2]);
          if (target?.declaration) result.push(...this.calls(target.file, target.declaration, hidden, visited));
          return;
        }
        const target = match && this.binding(file, match[1]!);
        if (!target?.declaration) return;
        if (match![2]) {
          const member = target.declaration.members.find((m) => m.name === match![2] && m.static);
          for (const [index, sig] of member?.signatures.entries() ?? []) {
            if (!hidden(member!.docs[index] ?? '')) result.push({ file: target.file, text: cleanSignature(sig).replace(/^static [\w$]+/, '') });
          }
        } else result.push(...this.calls(target.file, target.declaration, hidden, visited));
      }
    };
    for (const [index, signature] of decl.signatures.entries()) {
      if (hidden(decl.docs[index] ?? '')) continue;
      const sig = cleanSignature(signature);
      const fn = /^(?:export )?(?:declare )?function [\w$]+([<(][\s\S]*)/.exec(sig);
      const value = /^(?:export )?(?:declare )?(?:const|let|var) [\w$]+: ([\s\S]*);$/.exec(sig);
      const alias = /^(?:export )?type [\w$]+(?:<[^=]*>)? = ([\s\S]*);$/.exec(sig);
      if (fn) result.push({ file, text: fn[1]! });
      else if (value || (alias && decl.kind === 'type')) inspectType((value ?? alias)![1]!);
    }
    if (decl.kind === 'interface' || decl.kind === 'type') {
      for (const m of decl.members.filter((m) => m.name === '(call)')) {
        for (const [index, text] of m.signatures.entries()) {
          if (!hidden(m.docs[index] ?? '')) result.push({ file, text });
        }
      }
    }
    return result;
  }

  private modules = new Map<string, ModuleInfo>();
  moduleInfo(file: string): ModuleInfo {
    let info = this.modules.get(file);
    if (!info) this.modules.set(file, info = parseModule(file));
    return info;
  }

  resolveExport(file: string, name: string, seen = new Set<string>()): Resolved | undefined {
    const key = `${file}#${name}`;
    if (seen.has(key)) return undefined;
    seen.add(key);
    const info = this.moduleInfo(file);
    const link = info.links.get(name);
    if (link) {
      const [target, local, typeOnly] = link;
      if (target === undefined) return { file, local, typeOnly, declaration: info.declarations.get(local) };
      if (local === '*') return { namespace: target, file: target, local: name, typeOnly, declaration: { kind: 'namespace', line: 1, docs: [], signatures: [], members: [] } };
      const r = this.resolveExport(target, local, seen);
      return r && typeOnly ? { ...r, typeOnly } : r;
    }
    const ns = info.namespaces.get(name);
    if (ns) return { namespace: ns.file, file: ns.file, local: name, declaration: {
      kind: 'namespace', line: 1, docs: [ns.doc], signatures: [ns.signature], members: [],
    } };
    for (const star of info.stars) {
      const r = this.resolveExport(star, name, seen);
      if (r) return r;
    }
    return undefined;
  }

  exportedNames(file: string, seen = new Set<string>()): string[] {
    if (seen.has(file)) return [];
    seen.add(file);
    const info = this.moduleInfo(file);
    return [...new Set([...info.links.keys(), ...info.namespaces.keys(), ...info.stars.flatMap((s) => this.exportedNames(s, seen))])];
  }
}

export function withDeclarations<T>(read: (graph: DeclarationGraph) => T): T {
  const out = mkdtempSync(join(tmpdir(), 'symjs-api-docs-'));
  try {
    execFileSync(join(ROOT, 'node_modules/.bin/tsc'), ['-p', join(PACKAGE, 'tsconfig.build.json'), '--emitDeclarationOnly', '--declaration', '--declarationMap', 'false', '--outDir', out], { stdio: 'inherit' });
    return read(new DeclarationGraph(out));
  } finally {
    rmSync(out, { recursive: true, force: true });
  }
}
