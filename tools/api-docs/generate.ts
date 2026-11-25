// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { callParameters, cleanSignature, moduleSpecifier, namedCall, withDeclarations } from './declarations';
import type { Declaration, DeclarationGraph, Member, Resolved, Signatures } from './declarations';
import { escape, inline, markdown, namedTag, parseComment } from './tsdoc';
import type { Comment, Link } from './tsdoc';

interface Route { entry: string; names: string[]; typeOnly?: boolean }
interface DocumentedMember extends Member { doc: Comment; anchor: string }
interface Owner {
  name: string;
  url?: string;
  decl: Declaration;
  members: DocumentedMember[];
}
interface Page extends Owner {
  file: string;
  local: string;
  url: string;
  doc: Comment;
  routes: Route[];
  children: Set<Page>;
}

const packageName = (entry: string) => '@symjs/symjs' + (entry ? '/' + entry : '');
const entryUrl = (entry: string) => `entry-${entry || 'root'}.html`;
const bindingKey = (file: string, local: string) => `${file}#${local}`;
const firstParagraph = (doc: Comment) => doc.summary.split(/\n\s*\n/)[0]!.replace(/\s+/g, ' ').trim();
const tag = (doc: Comment, name: string) => doc.blocks.get(name) ?? [];
const anchorLink = (url: string, label: string) => `<a href="${escape(url)}">${escape(label)}</a>`;
const byName = (a: Page, b: Page) => a.name.localeCompare(b.name) || a.file.localeCompare(b.file);

const symbolUrl = (page: Page) => page.url.slice('symbols/'.length);
const inheritedAnchor = (m: Member) => `inherited-${m.static ? 'static' : 'instance'}-${m.name}`;

const internal = (doc: string) => doc.includes('@internal') && parseComment([doc]).blocks.has('internal');

function publicForms<T extends Signatures>(row: T): T | undefined {
  if (!row.docs.some(internal)) return row;
  const signatures = row.signatures.filter((_, i) => !internal(row.docs[i] ?? ''));
  if (signatures.length) return { ...row, signatures, docs: row.docs.filter((doc) => !internal(doc)) };
  return undefined;
}

function documentedMembers(decl: Declaration): DocumentedMember[] {
  const visible = decl.members.flatMap((member) => {
    const m = publicForms(member);
    return m ? [{ ...m, doc: parseComment(m.docs) }] : [];
  });
  const instance = new Set(visible.filter((m) => !m.static).map((m) => m.name));
  return visible.map((m) => ({ ...m, anchor: (m.static && instance.has(m.name) ? 'static-' : '') + m.name }));
}

class Reference {
  pages = new Map<string, Page>();
  names = new Map<string, Page[]>();
  bindings = new Map<string, Page>();
  problems = new Set<string>();
  private namespaces = new Map<string, Map<string, Resolved | undefined>>();

  constructor(readonly graph: DeclarationGraph) {
    for (const entry of graph.entries) {
      for (const [name, r] of entry.exports) this.add(r, { entry: entry.path, names: [name], typeOnly: r?.typeOnly }, new Set());
    }
    const filenames = new Set<string>();
    for (const page of [...this.pages.values()].sort(byName)) {
      let stem = page.name;
      let suffix = 1;
      while (filenames.has(stem.toLowerCase())) stem = `${page.name}-${++suffix}`;
      filenames.add(stem.toLowerCase());
      page.url = `symbols/${stem}.html`;
      page.routes.sort((a, b) => a.names.length - b.names.length || a.entry.localeCompare(b.entry));
      for (const name of new Set(page.routes.map((r) => r.names.join('.')))) {
        const candidates = this.names.get(name) ?? [];
        candidates.push(page);
        this.names.set(name, candidates);
      }
      const key = bindingKey(page.file, page.local);
      if (!this.bindings.has(key) || page.name === page.local) this.bindings.set(key, page);
    }
  }

  private add(r: Resolved | undefined, route: Route, ancestors: Set<string>): Page | undefined {
    const name = route.names.at(-1)!;
    if (!r?.declaration) {
      this.problems.add(`Export without a declaration or page: ${packageName(route.entry)} ${route.names.join('.')}`);
      return undefined;
    }
    const key = bindingKey(r.file, r.local) + '#' + name;
    let page = this.pages.get(key);
    if (!page) {
      const decl = publicForms(r.declaration);
      if (!decl) return undefined;
      const doc = parseComment(decl.docs);
      page = { file: r.file, local: r.local, name, decl, doc, routes: [], members: documentedMembers(decl), children: new Set(), url: '' };
      this.pages.set(key, page);
    }
    page.routes.push(route);
    if (r.namespace && !ancestors.has(r.namespace)) {
      let exports = this.namespaces.get(r.namespace);
      if (!exports) this.namespaces.set(r.namespace, exports = this.graph.exportsOf(r.namespace));
      const seen = new Set(ancestors).add(r.namespace);
      for (const [child, target] of exports) {
        const nested = this.add(target, { entry: route.entry, names: [...route.names, child], typeOnly: route.typeOnly }, seen);
        if (nested) page.children.add(nested);
      }
    }
    return page;
  }

  binding(file: string, name: string): Page | undefined {
    const r = this.graph.binding(file, name);
    return r && this.bindings.get(bindingKey(r.file, r.local));
  }

  ancestors(page: Page): Owner[] {
    const parents: Owner[] = [];
    const seen = new Set<Declaration>([page.decl]);
    let { file, decl } = page;
    while (decl.kind === 'class') {
      const base = /\bextends\s+([\w$]+)(?:<[^<>]*>)?(?: implements .*)?$/.exec(decl.signatures[0] ?? '')?.[1];
      const r = base && this.graph.binding(file, base);
      if (!r || !r.declaration || seen.has(r.declaration)) break;
      seen.add(r.declaration);
      const parent = this.bindings.get(bindingKey(r.file, r.local));
      parents.push(parent ?? { name: r.local, decl: r.declaration, members: documentedMembers(r.declaration) });
      file = r.file;
      decl = r.declaration;
    }
    return parents;
  }

  link(target: string, context?: Page): string | undefined {
    if (/^https?:\/\//.test(target)) return target;
    const names = target.split('.');
    for (let length = names.length; length > 0; length--) {
      const name = names.slice(0, length).join('.');
      const candidates = this.names.get(name) ?? [];
      const local = context && this.binding(context.file, name);
      const page = candidates.find((p) => p.decl === local?.decl)
        ?? candidates.find((p) => context?.routes.some((r) => r.entry && p.routes.some((s) => s.entry === r.entry)))
        ?? candidates[0] ?? local;
      if (!page) continue;
      if (length === names.length) return page.url;
      const member = names.slice(length).join('.');
      for (const owner of [page, ...this.ancestors(page)]) {
        const m = owner.members.find((m) => m.name === member);
        if (m) return `${owner.url ?? page.url}#${encodeURIComponent(owner.url ? m.anchor : inheritedAnchor(m))}`;
      }
    }
    return undefined;
  }
}

function section(title: string, body: string): string {
  return body ? `<section><h2>${escape(title)}</h2>\n${body}</section>` : '';
}

function definitionList(rows: { name: string; description: string }[], link: Link, nested = false): string {
  const render = (name: string, description: string, children = '') => `<dt><code>${escape(name)}</code></dt><dd>${markdown(description, link)}${children}</dd>`;
  if (!rows.length) return '';
  if (!nested) return `<dl>${rows.map((r) => render(r.name, r.description)).join('')}</dl>`;
  const parents = new Set(rows.map((r) => r.name.split('.')[0]!));
  return `<dl>${[...parents].map((name) => {
    const children = rows.filter((r) => r.name.startsWith(name + '.'));
    return render(name, rows.filter((r) => r.name === name).map((r) => r.description).join('\n\n'), definitionList(children, link));
  }).join('')}</dl>`;
}

function documentation(doc: Comment, link: Link, heading: 'h2' | 'h4'): string {
  const parts = [markdown(doc.summary, link)];
  const block = (title: string, html: string) => {
    if (html) parts.push(`<${heading}>${title}</${heading}>${html}`);
  };
  for (const [key, label] of [['deprecated', 'Deprecated'], ['experimental', 'Experimental']] as const) {
    if (doc.blocks.has(key)) parts.push(`<aside class="notice"><strong>${label}</strong>${tag(doc, key).map((v) => markdown(v, link)).join('')}</aside>`);
  }
  const render = (key: string) => tag(doc, key).map((v) => markdown(v, link)).join('\n');
  block('Remarks', render('remarks'));
  block('Type parameters', definitionList(tag(doc, 'typeParam').map(namedTag), link));
  block('Parameters', definitionList(tag(doc, 'param').map(namedTag), link, true));
  block('Returns', render('returns'));
  block('Throws', render('throws'));
  block('Default value', render('defaultValue'));
  block('Examples', render('example'));
  block('SymPy counterpart', doc.sympy.map((p) => `<p>${anchorLink(`https://docs.sympy.org/latest/search.html?q=${encodeURIComponent(p)}`, p)}</p>`).join(''));
  block('See also', tag(doc, 'see').map((v) => /^https?:\/\/\S+$/.test(v) ? `<p>${anchorLink(v, v)}</p>` : markdown(v, link)).join('\n'));
  return parts.join('\n');
}

function signatures(source: string[], page: Page, ref: Reference, top: boolean, file = page.file): string {
  const printed = source.map((sig) => {
    let code = cleanSignature(sig, internal).replace(/^export (?!\*)(?:declare )?/, '');
    if (top) {
      code = code.replace(/^(?:(?:declare|abstract) )?(?:function|class|const|let|var|interface|type|enum) ([\w$]+)/, (s: string, name: string) => s.slice(0, -name.length) + page.name);
    }
    const tokens = /\bimport\(["']([^"']+)["']\)\.([\w$]+)|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|`[^`]*`|[A-Za-z_$][\w$]*/g;
    let html = '', start = 0;
    for (const m of code.matchAll(tokens)) {
      html += escape(code.slice(start, m.index));
      const token = m[0];
      let target: Page | undefined;
      if (m[1] && m[2] && m[1].startsWith('.')) {
        const imported = moduleSpecifier(file, m[1]);
        const r = ref.graph.resolveExport(imported, m[2]);
        if (r) target = ref.bindings.get(bindingKey(r.file, r.local));
      } else if (/^[A-Za-z_$]/.test(token) && !/^\??\s*:/.test(code.slice(m.index + token.length)) && !/\b(?:function|class|interface|type|const|enum) $/.test(code.slice(0, m.index))) {
        target = ref.binding(file, token);
      }
      html += target ? anchorLink(symbolUrl(target), token) : escape(token);
      start = m.index + token.length;
    }
    return html + escape(code.slice(start));
  });
  return printed.length ? `<pre><code>${printed.join('\n')}</code></pre>` : '';
}

function checkedLink(ref: Reference, label: string, fromSymbol: boolean, context?: Page): Link {
  return (target) => {
    const url = ref.link(target, context);
    if (!url) ref.problems.add(`${label}: unresolved {@link ${target}}`);
    if (url?.startsWith('symbols/') && fromSymbol) return url.slice('symbols/'.length);
    return url;
  };
}

function validate(doc: Comment, signatures: string[], label: string, ref: Reference) {
  for (const bad of doc.unknown) ref.problems.add(`${label}: unknown tag ${bad}`);
  const names = new Set(signatures.flatMap(callParameters));
  for (const value of tag(doc, 'param')) {
    const { name } = namedTag(value);
    if (!names.has(name.split('.')[0]!)) ref.problems.add(`${label}: @param ${name} is absent from the signatures`);
  }
}

function listings(pages: Page[], ref: Reference, fromSymbol = false): string {
  const kinds: Record<string, string> = { function: 'Functions', class: 'Classes', const: 'Constants', let: 'Constants', var: 'Constants',
    interface: 'Interfaces and types', type: 'Interfaces and types', enum: 'Enums', namespace: 'Namespaces' };
  const groups = new Map<string, Page[]>();
  for (const title of [...Object.values(kinds), 'Deprecated']) groups.set(title, []);
  for (const page of pages.sort(byName)) {
    const title = page.doc.blocks.has('deprecated') ? 'Deprecated' : kinds[page.decl.kind]!;
    groups.get(title)!.push(page);
  }
  return [...groups].map(([title, group]) => section(title, group.length ? `<ul class="exports">\n${group.map((page) => {
    const link = checkedLink(ref, `${ref.graph.source(page.file)} ${page.name}`, fromSymbol, page);
    const summary = title === 'Deprecated' ? tag(page.doc, 'deprecated')[0] || firstParagraph(page.doc) : firstParagraph(page.doc);
    return `<li>${anchorLink(fromSymbol ? symbolUrl(page) : page.url, page.name)} ${inline(summary, link)}</li>`;
  }).join('\n')}</ul>` : '')).join('\n');
}

function importLine(route: Route, kind: string): string {
  const exported = route.names[0]!;
  const alias = new Map([['var', 'symbolVar'], ['switch', 'switchRule'], ['public', 'publicName']]).get(exported);
  const binding = exported + (alias ? ` as ${alias}` : '');
  const type = route.typeOnly || (['interface', 'type'].includes(kind) && route.names.length === 1) ? 'type ' : '';
  return `import ${type}{ ${binding} } from '${packageName(route.entry)}'` + (route.names.length > 1 ? `  // ${(alias ?? exported)}.${route.names.slice(1).join('.')}` : '');
}

function exportPage(page: Page, ref: Reference): string {
  const label = `${ref.graph.source(page.file)} ${page.name}`;
  const link = checkedLink(ref, label, true, page);
  const constructor = page.members.find((m) => m.name === 'constructor');
  const calls = ref.graph.calls(page.file, page.decl, internal);
  validate(page.doc, [...(constructor?.signatures ?? []), ...calls.map((s) => s.text)], label, ref);
  const html = [
    `<h1>${escape(page.routes[0]!.names.join('.'))}</h1>`,
    `<pre><code>${page.routes.map((r) => escape(importLine(r, page.decl.kind))).join('\n')}</code></pre>`,
    signatures(page.decl.signatures, page, ref, true),
  ];
  if (page.decl.kind === 'const') {
    const extra = calls.filter((s) => !page.decl.signatures.some((sig) => sig.includes(s.text)));
    html.push(section('Call signatures', extra.map((s) => signatures([namedCall(page.name, s.text)], page, ref, false, s.file)).join('\n')));
  }
  html.push(documentation(page.doc, link, 'h2'));
  const members = (rows: DocumentedMember[]) => rows.map((m) => {
    validate(m.doc, m.signatures, `${label}.${m.name}`, ref);
    return `<article id="${escape(m.anchor)}"><h3>${anchorLink('#' + encodeURIComponent(m.anchor), m.name)}</h3>\n${signatures(m.signatures, page, ref, false)}\n${documentation(m.doc, checkedLink(ref, `${label}.${m.name}`, true, page), 'h4')}</article>`;
  }).join('\n');
  if (page.decl.kind === 'class') {
    if (constructor) html.push(section('Constructor', members([constructor])));
    html.push(section('Static members', members(page.members.filter((m) => m.static))));
    html.push(section('Instance members', members(page.members.filter((m) => !m.static && m !== constructor))));
    const memberKey = (m: Member) => (m.static ? 'static ' : '') + m.name;
    const seen = new Set(page.decl.members.map(memberKey));
    const inherited: string[] = [];
    for (const parent of ref.ancestors(page)) {
      const links: string[] = [];
      for (const m of parent.members) {
        const key = memberKey(m);
        if (m.name !== 'constructor' && !seen.has(key)) {
          links.push(parent.url ? anchorLink(parent.url.slice('symbols/'.length) + '#' + encodeURIComponent(m.anchor), key)
            : `<span id="${escape(inheritedAnchor(m))}">${escape(key)}</span>`);
        }
        seen.add(key);
      }
      if (links.length) inherited.push(`<p>From ${parent.url ? anchorLink(parent.url.slice('symbols/'.length), parent.name) : escape(parent.name)}</p><p>${links.join(', ')}</p>`);
    }
    html.push(section('Inherited members', inherited.join('\n')));
  } else html.push(section(page.decl.kind === 'enum' ? 'Members' : 'Properties', members(page.members)));
  if (page.children.size) html.push(listings([...page.children], ref, true));
  return html.join('\n');
}

const search = `<label for="query">Search the API</label>
<input type="search" id="query" placeholder="Name, entry point, or description" autocomplete="off">
<p id="count" aria-live="polite"></p><ul id="results"></ul>
<script src="search-index.js"></script>
<script>
const input = document.getElementById('query');
function filter() {
  const query = input.value.trim().toLowerCase();
  const matches = query ? apiIndex.filter(item => [item.name, item.kind, ...item.entryPoints, item.summary].join(' ').toLowerCase().includes(query)) : [];
  const results = document.getElementById('results');
  results.replaceChildren();
  for (const item of matches) {
    const row = document.createElement('li');
    const link = document.createElement('a');
    link.href = item.url;
    link.textContent = item.name;
    row.append(link, ' · ' + item.kind + ' · ' + item.summary);
    results.append(row);
  }
  document.getElementById('count').textContent = query ? matches.length + ' results' : '';
}
input.addEventListener('input', filter);
filter();
</script>`;

function build(out: string, check: boolean): void {
  const start = performance.now();
  withDeclarations((graph) => {
    const ref = new Reference(graph);
    mkdirSync(join(out, 'symbols'), { recursive: true });
    const pages = [...ref.pages.values()];
    const index = pages.sort(byName).map((p) => ({
      name: p.routes[0]!.names.join('.'), kind: p.decl.kind,
      entryPoints: [...new Set(p.routes.map((r) => packageName(r.entry)))],
      summary: firstParagraph(p.doc).replace(/\{@link\s+([^|}]+?)(?:\s*\|\s*([^}]+))?\}/g, (_, target: string, label?: string) => label ?? target).replaceAll('`', ''), url: p.url,
    }));
    const sidebars = ['', '../'].map((prefix) => `<nav aria-label="API navigation">${anchorLink(prefix + 'index.html', 'API reference')}<details open><summary>Entry points</summary><ul>${graph.entries.map((entry) => `<li>${anchorLink(prefix + entryUrl(entry.path), entry.path ? '/' + entry.path : '@symjs/symjs')}</li>`).join('\n')}</ul></details></nav>`);
    let count = 0;
    function write(url: string, title: string, content: string) {
      const nested = url.startsWith('symbols/');
      const html = `<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>${escape(title)} · symjs API</title><link rel="stylesheet" href="${nested ? '../' : ''}style.css"></head><body>\n<a class="skip" href="#main-content">Skip to content</a>${sidebars[nested ? 1 : 0]}\n<main id="main-content">${content}</main></body></html>\n`;
      if (check) {
        const ids = new Set<string>();
        for (const m of html.matchAll(/\sid="([^"]+)"/g)) {
          if (ids.has(m[1]!)) ref.problems.add(`${url}: duplicate anchor ${m[1]}`);
          ids.add(m[1]!);
        }
      }
      writeFileSync(join(out, url), html);
      count++;
    }
    const modules: string[] = [];
    for (const entry of graph.entries) {
      const name = packageName(entry.path);
      const link = checkedLink(ref, name, false);
      const doc = parseComment([entry.comment]);
      validate(doc, [], name, ref);
      modules.push(`<li>${anchorLink(entryUrl(entry.path), name)}${markdown(doc.summary, link)}</li>`);
      const exported = pages.filter((p) => p.routes.some((r) => r.names.length === 1 && r.entry === entry.path));
      write(entryUrl(entry.path), name, `<h1>${escape(name)}</h1>${documentation(doc, link, 'h2')}${listings(exported, ref)}`);
    }
    write('index.html', 'API reference', `<h1>symjs API reference</h1><p>@symjs/symjs is a symbolic computer algebra system for TypeScript, compatible with SymPy.</p>${search}${section('Entry points', `<ul class="exports">${modules.join('\n')}</ul>`)}`);
    for (const page of pages) write(page.url, page.routes[0]!.names.join('.'), exportPage(page, ref));
    const indexPath = join(out, 'search-index.json');
    if (existsSync(indexPath)) {
      const current = new Set(index.map((item) => item.url.toLowerCase()));
      for (const item of JSON.parse(readFileSync(indexPath, 'utf8')) as { url: string }[]) {
        if (/^symbols\/[\w$-]+\.html$/.test(item.url) && !current.has(item.url.toLowerCase())) rmSync(join(out, item.url), { force: true });
      }
    }
    const json = JSON.stringify(index);
    writeFileSync(indexPath, json + '\n');
    writeFileSync(join(out, 'search-index.js'), `const apiIndex = ${json};\n`);
    writeFileSync(join(out, 'style.css'), readFileSync(join(import.meta.dirname, 'style.css')));
    if (check) {
      for (const page of pages) if (!existsSync(join(out, page.url))) ref.problems.add(`${page.name}: missing page ${page.url}`);
      for (const problem of [...ref.problems].sort()) console.error(problem);
      if (ref.problems.size) process.exitCode = 1;
    }
    console.log(`${count} pages, ${pages.length} public exports, ${graph.entries.length} entry points in ${((performance.now() - start) / 1000).toFixed(2)} s${check ? `, ${ref.problems.size} problems` : ''}.`);
  });
}

if (import.meta.main) {
  let out = resolve(import.meta.dirname, '../../site/api');
  let check = false;
  const args = process.argv.slice(2);
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--check') check = true;
    else if (args[i] === '--out' && args[i + 1] && !args[i + 1]!.startsWith('--')) out = resolve(args[++i]!);
    else throw new Error('Usage: bun tools/api-docs/generate.ts [--out <dir>] [--check]');
  }
  if (check) {
    const temp = mkdtempSync(join(tmpdir(), 'symjs-reference-'));
    try { build(temp, true); } finally { rmSync(temp, { recursive: true, force: true }); }
  } else build(out, false);
}
