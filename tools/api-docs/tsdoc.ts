// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Block tags and Markdown in the documentation comments retained by tsc. */
export interface Comment {
  summary: string;
  blocks: Map<string, string[]>;
  sympy: string[];
  unknown: string[];
}

const tags = new Set(('remarks param typeParam returns throws defaultValue example see deprecated experimental internal '
  + 'category module packageDocumentation public private protected alpha beta override virtual sealed readonly '
  + 'abstract group hidden ignore inheritDoc eventProperty event hideconstructor overload interface '
  + 'type namespace enum class function document expand expandType preventExpand inline useDeclaredType '
  + 'showCategories hideCategories showGroups hideGroups categoryDescription groupDescription sortStrategy '
  + 'disableGroups primaryExport reexport privateRemarks default return summary since author license prop property template this '
  + 'callback typedef satisfies import augments extends yields jsx inlineType preventInline mergeModuleWith').split(' '));

export function parseComment(comments: string[]): Comment {
  const result: Comment = { summary: '', blocks: new Map(), sympy: [], unknown: [] };
  const summaries: string[] = [];
  for (const raw of new Set(comments)) {
    let tag = '';
    let lines: string[] = [];
    let fenced = false;
    function finish() {
      const value = lines.join('\n').trim();
      if (tag === '' || tag === 'summary') {
        if (value && !summaries.includes(value)) summaries.push(value);
      } else {
        const path = tag === 'see' && /^SymPy\s+`([\w.]+)`\.?$/.exec(value);
        if (path) {
          if (!result.sympy.includes(path[1]!)) result.sympy.push(path[1]!);
        } else {
          const values = result.blocks.get(tag) ?? [];
          if (!values.includes(value)) values.push(value);
          result.blocks.set(tag, values);
        }
      }
      lines = [];
    }
    const body = raw.trim().replace(/^\/\*\* ?/, '').replace(/\s*\*\/$/, '');
    for (const line of body.split('\n').map((s, i) => i === 0 ? s : s.replace(/^\s*\* ?/, ''))) {
      if (/^\s*```/.test(line)) { fenced = !fenced; lines.push(line); continue; }
      if (fenced) { lines.push(line); continue; }
      let start = 0;
      // Code spans and scoped package names can both contain an at sign.
      for (const m of line.matchAll(/`[^`]*`|(?:^|\s)@([A-Za-z][\w-]*)(?=\s|$)/g)) {
        if (!m[1]) continue;
        lines.push(line.slice(start, m.index));
        finish();
        tag = m[1] === 'return' ? 'returns' : m[1] === 'default' ? 'defaultValue' : m[1];
        if (!tags.has(tag)) result.unknown.push('@' + tag);
        start = m.index + m[0].length;
      }
      lines.push(line.slice(start));
      for (const m of line.matchAll(/`[^`]*`|\{@(\w+)/g)) {
        if (m[1] && !['link', 'linkcode', 'linkplain', 'inheritDoc', 'label', 'include', 'includeCode'].includes(m[1])) result.unknown.push('@' + m[1]);
      }
    }
    finish();
  }
  result.summary = summaries.join('\n\n');
  return result;
}

export function namedTag(value: string): { name: string; description: string } {
  const m = /^(\S+)\s*(?:-\s*)?([\s\S]*)$/.exec(value);
  return { name: m?.[1] ?? '', description: m?.[2] ?? '' };
}

export function escape(text: string): string {
  return text.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&#39;');
}

export type Link = (target: string) => string | undefined;

export function inline(text: string, link: Link): string {
  const tokens = /`([^`\n]+)`|\{@(?:link|linkcode|linkplain)\s+([^\s|}]+)\s*(?:\|\s*([^}]+?))?\s*\}|\*\*(\S(?:[^*]*?\S)?)\*\*|(?<!\w)\*(\S(?:[^*\n]*?\S)?)\*(?!\w)|(?<!\w)_(\S(?:[^_\n]*?\S)?)_(?!\w)/g;
  let html = '', start = 0;
  for (const m of text.matchAll(tokens)) {
    html += escape(text.slice(start, m.index));
    if (m[1]) html += `<code>${escape(m[1])}</code>`;
    else if (m[2]) {
      const url = link(m[2]);
      const label = escape(m[3] ?? m[2]);
      html += url ? `<a href="${escape(url)}">${label}</a>` : label;
    } else if (m[4]) html += `<strong>${inline(m[4], link)}</strong>`;
    else html += `<em>${inline((m[5] ?? m[6])!, link)}</em>`;
    start = m.index + m[0].length;
  }
  return html + escape(text.slice(start));
}

export function markdown(text: string, link: Link): string {
  const lines = text.trim().split('\n');
  const html: string[] = [];
  const fence = /^\s*```/;
  const list = /^\s*([-*+]|\d+\.)\s+(.*)/;
  const table = (i: number) => lines[i]?.includes('|') && /^\s*\|?\s*:?-{3,}/.test(lines[i + 1] ?? '');
  for (let i = 0; i < lines.length;) {
    const line = lines[i++]!;
    if (!line.trim()) continue;
    if (fence.test(line)) {
      const start = i;
      while (i < lines.length && !fence.test(lines[i]!)) i++;
      html.push(`<pre><code>${escape(lines.slice(start, i++).join('\n'))}</code></pre>`);
    } else if (list.test(line)) {
      const tag = /^\d/.test(line.trimStart()) ? 'ol' : 'ul';
      const items = [list.exec(line)![2]!];
      while (i < lines.length && lines[i]!.trim()) {
        const item = list.exec(lines[i]!);
        if (item) items.push(item[2]!);
        else if (/^\s+/.test(lines[i]!)) items[items.length - 1] += ' ' + lines[i]!.trim();
        else break;
        i++;
      }
      html.push(`<${tag}>${items.map((s) => `<li>${inline(s, link)}</li>`).join('')}</${tag}>`);
    } else if (table(i - 1)) {
      const row = (s: string, tag: string) => '<tr>' + s.trim().replace(/^\||\|$/g, '').split('|').map((v) => `<${tag}>${inline(v.trim(), link)}</${tag}>`).join('') + '</tr>';
      html.push('<table><thead>', row(line, 'th'), '</thead><tbody>');
      i++;
      while (i < lines.length && lines[i]!.includes('|')) html.push(row(lines[i++]!, 'td'));
      html.push('</tbody></table>');
    } else {
      const paragraph = [line];
      while (i < lines.length && lines[i]!.trim() && !fence.test(lines[i]!) && !list.test(lines[i]!) && !table(i)) paragraph.push(lines[i++]!);
      html.push(`<p>${inline(paragraph.join(' '), link)}</p>`);
    }
  }
  return html.join('\n');
}
