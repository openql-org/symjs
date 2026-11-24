// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/**
 * Checks the `@example` blocks of the documentation comments of `packages/symjs/src`.
 *
 * Every example is a fenced `ts` block that imports from the package entry points
 * (docs/api-policy.md, "Documentation comments"). Each block is written to its own
 * module in a temporary directory, type-checked with `tsc` against the sources
 * (through the `paths` of the root tsconfig), and run with `bun`: a statement
 * followed by `// => result` (continuation lines `//   ...`) must give `result`,
 * a string as it is and any other value printed by `sstr` (SymPy's `str()`);
 * spaces at the ends of lines are ignored.
 *
 * Usage: `bun tools/api-docs/examples.ts [path filter...] [--no-run]`.
 */
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative, resolve } from 'node:path';

const ROOT = resolve(import.meta.dirname, '../..');
const SRC = join(ROOT, 'packages/symjs/src');

export interface Example {
  /** Source file relative to the repository. */
  file: string;
  /** Line of the opening fence in the source file. */
  line: number;
  code: string;
}

export interface Malformed {
  file: string;
  line: number;
  reason: string;
}

function sources(dir: string): string[] {
  return readdirSync(dir).flatMap((name) => {
    const path = join(dir, name);
    return statSync(path).isDirectory() ? sources(path) : name.endsWith('.ts') && !name.endsWith('.d.ts') ? [path] : [];
  });
}

/** Fenced `ts` blocks of the `@example` tags of every documentation comment of a file. */
export function extract(path: string): { examples: Example[]; malformed: Malformed[] } {
  const file = relative(ROOT, path);
  const lines = readFileSync(path, 'utf8').split('\n');
  const examples: Example[] = [];
  const malformed: Malformed[] = [];
  let inDoc = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (!inDoc && /^\s*\/\*\*/.test(line)) inDoc = true;
    if (inDoc && /@example\b/.test(line)) {
      // the block follows the tag, possibly after a title on the same line
      let j = i + 1;
      while (j < lines.length && /^\s*\*\s*$/.test(lines[j]!)) j++;
      const fence = /^\s*\*\s?```(\w*)\s*$/.exec(lines[j] ?? '');
      if (!fence || (fence[1] !== 'ts' && fence[1] !== 'typescript')) {
        malformed.push({ file, line: i + 1, reason: 'no fenced ts block after @example' });
      } else {
        const body: string[] = [];
        let k = j + 1;
        for (; k < lines.length && !/^\s*\*\s?```\s*$/.test(lines[k]!); k++) {
          if (/\*\//.test(lines[k]!)) break;
          body.push(lines[k]!.replace(/^\s*\*( |$)/, ''));
        }
        if (!/^\s*\*\s?```\s*$/.test(lines[k] ?? '')) malformed.push({ file, line: j + 1, reason: 'unterminated fence' });
        else examples.push({ file, line: j + 1, code: body.join('\n') });
        i = k;
      }
    }
    if (inDoc && /\*\//.test(line)) inDoc = false;
  }
  return { examples, malformed };
}

/**
 * The module run for an example: every `statement; // => expected` becomes a check
 * of `String(value)` against the expected text.
 */
export function instrument(example: Example): string {
  const lines = example.code.split('\n');
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const m = /^(\s*)(.*?);?\s*\/\/ => (.*)$/.exec(lines[i]!);
    if (!m || m[2]!.trim() === '') { out.push(lines[i]!); continue; }
    const expected = [m[3]!];
    while (i + 1 < lines.length && /^\s*\/\/ {3}/.test(lines[i + 1]!)) expected.push(lines[++i]!.replace(/^\s*\/\/ {3}/, ''));
    const statement = m[2]!;
    const declared = /^(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*(?::[^=]+)?=/.exec(statement);
    const where = JSON.stringify(`${example.file}:${example.line + i + 1}`);
    if (declared) {
      out.push(`${m[1]}${statement};`, `${m[1]}__check(${declared[1]}, ${JSON.stringify(expected.join('\n'))}, ${where});`);
    } else {
      out.push(`${m[1]}__check((${statement}), ${JSON.stringify(expected.join('\n'))}, ${where});`);
    }
  }
  return `declare function __check(value: unknown, expected: string, where: string): void;\n${out.join('\n')}\nexport {};\n`;
}

const RUNNER = `
const { sstr } = await import(process.argv[3]);
let failures = 0;
globalThis.__check = (value, expected, where) => {
  const got = typeof value === 'string' ? value : sstr(value);
  const trim = (t) => t.split('\\n').map((l) => l.trimEnd()).join('\\n');
  if (trim(got) !== trim(expected)) { failures++; console.log(\`\${where}: expected \${JSON.stringify(expected)}, got \${JSON.stringify(got)}\`); }
};
const files = JSON.parse(process.argv[2]);
for (const [file, origin] of files) {
  try { await import(file); } catch (e) { failures++; console.log(\`\${origin}: threw \${e instanceof Error ? e.name + ': ' + e.message : String(e)}\`); }
}
process.exit(failures === 0 ? 0 : 1);
`;

if (import.meta.main) {
  const args = process.argv.slice(2);
  const run = !args.includes('--no-run');
  const filters = args.filter((a) => !a.startsWith('--')).map((a) => resolve(a));
  const files = sources(SRC).filter((f) => filters.length === 0 || filters.some((p) => f.startsWith(p)));
  const examples: Example[] = [];
  const malformed: Malformed[] = [];
  for (const f of files) {
    const r = extract(f);
    examples.push(...r.examples);
    malformed.push(...r.malformed);
  }
  for (const m of malformed) console.log(`${m.file}:${m.line}: ${m.reason}`);
  const dir = mkdtempSync(join(tmpdir(), 'symjs-examples-'));
  let failed = malformed.length > 0;
  try {
    const paths = examples.map((e, k) => {
      const path = join(dir, `example${k}.ts`);
      writeFileSync(path, instrument(e));
      return [path, `${e.file}:${e.line}`] as const;
    });
    writeFileSync(join(dir, 'tsconfig.json'), JSON.stringify({
      extends: join(ROOT, 'tsconfig.json'),
      compilerOptions: { noEmit: true, noUnusedLocals: false, noUncheckedIndexedAccess: false, types: ['node'], typeRoots: [join(ROOT, 'node_modules/@types')] },
      include: ['*.ts'],
    }));
    if (paths.length > 0) {
      const tsc = spawnSync(join(ROOT, 'node_modules/.bin/tsc'), ['-p', join(dir, 'tsconfig.json')], { encoding: 'utf8' });
      if (tsc.status !== 0) {
        failed = true;
        const origin = new Map(paths.map(([p, o]) => [p, o]));
        for (const line of (tsc.stdout + tsc.stderr).split('\n')) {
          const m = /^(?:.*[\\/])?(example\d+\.ts)\((\d+),(\d+)\): (.*)$/.exec(line);
          if (m) {
            const where = origin.get(join(dir, m[1]!))!;
            // line 1 of the module is the __check declaration
            const [file, start] = [where.slice(0, where.lastIndexOf(':')), Number(where.slice(where.lastIndexOf(':') + 1))];
            console.log(`${file}:${start + Number(m[2]) - 1}: ${m[4]}`);
          } else if (line.trim()) console.log(line);
        }
      }
      if (run) {
        writeFileSync(join(dir, 'runner.mjs'), RUNNER);
        try {
          execFileSync('bun', [join(dir, 'runner.mjs'), JSON.stringify(paths), join(SRC, 'index.ts')], { stdio: 'inherit', cwd: dir });
        } catch {
          failed = true;
        }
      }
    }
    console.log(`${examples.length} examples in ${files.length} files, ${malformed.length} malformed${failed ? '' : ', all passed'}.`);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
  process.exit(failed ? 1 : 0);
}
