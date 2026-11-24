// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Hand-written port of SymPy 1.14 latex.lark and greek_symbols.lark (BSD-3-Clause).

import { at, cast } from '../../../../core/guard';
import { LaTeXParsingError } from '../../errors';
import { larkTokenizations, tokenizeLatex } from '../../lexer';
import type { LatexToken } from '../../lexer';
import { LatexTree } from '../../tree';

import { GREEK } from './greek_symbols';

type Rule = 'expression' | 'mul' | 'power' | 'func' | 'core' | 'atomic' | 'symbol' | 'number' | 'round' | 'curly' | 'square' | 'fraction' | 'binomial' | 'function' | 'integral' | 'limit' | 'summation' | 'product' | 'matrix' | 'list';

/** Terminal overrides supported by the hand-written grammar; no parser generator is needed. */
export interface LatexGrammarOptions {
  /** The character separating integer and fractional digits. */
  readonly decimalSeparator?: '.' | ',';
  /** The tokens accepted as multiplication operators. */
  readonly multiplicationSymbols?: readonly string[];
  /** The tokens accepted as division operators. */
  readonly divisionSymbols?: readonly string[];
}

const RELATIONS = new Map([['=', 'eq'], ['\\neq', 'ne'], ['\\ne', 'ne'], ['<', 'lt'], ['\\leq', 'lte'], ['\\le', 'lte'], ['\\leqslant', 'lte'], ['>', 'gt'], ['\\geq', 'gte'], ['\\ge', 'gte'], ['\\geqslant', 'gte']]);
const FUNCTIONS = new Map([
  ['\\sin', 'sin'], ['\\cos', 'cos'], ['\\tan', 'tan'], ['\\csc', 'csc'], ['\\sec', 'sec'], ['\\cot', 'cot'],
  ['\\arcsin', 'arcsin'], ['\\arccos', 'arccos'], ['\\arctan', 'arctan'], ['\\arccsc', 'arccsc'], ['\\arcsec', 'arcsec'], ['\\arccot', 'arccot'],
  ['\\sinh', 'sinh'], ['\\cosh', 'cosh'], ['\\tanh', 'tanh'], ['\\arsinh', 'asinh'], ['\\arcosh', 'acosh'], ['\\artanh', 'atanh'],
  ['\\exp', 'exponential'], ['\\ln', 'log'], ['\\lg', 'log'], ['\\log', 'log'], ['\\det', 'determinant'], ['\\trace', 'trace'], ['\\adjugate', 'adjugate'],
]);
const FRACTIONS = new Set(['\\frac', '\\dfrac', '\\tfrac', '\\nicefrac']);
const BINOMIALS = new Set(['\\binom', '\\dbinom', '\\tbinom']);
const ARROWS = new Set(['\\to', '\\rightarrow', '\\Rightarrow', '\\longrightarrow', '\\Longrightarrow']);
const COMMANDS = new Set([...FUNCTIONS.keys(), ...FRACTIONS, ...BINOMIALS, ...ARROWS, ...RELATIONS.keys(), ...[...GREEK].map(g => `\\${g}`), '\\int', '\\intop', '\\sum', '\\prod', '\\lim', '\\sqrt', '\\overline', '\\min', '\\max', '\\langle', '\\rangle', '\\lfloor', '\\rfloor', '\\lceil', '\\rceil', '\\mathit', '\\infty', '\\imaginaryunit', '\\prime', '\\ast', '\\times', '\\cdot', '\\div']);
const TERMINAL_GROUPS = ['ne', 'lte', 'gte'].map(name => new Set([...RELATIONS].filter(([, rule]) => rule === name).map(([token]) => token)));
const DIFFERENTIAL = new Set(['d', '\\mathrm{d}', '\\text{d}']);

/**
 * Memoized recursive descent over token intervals. Trying every legal split preserves
 * the explicit ambiguities of Earley parsing, including f(x) and unbraced function
 * arguments. Each recursive production consumes a terminal or a smaller interval.
 * Rule names below correspond to latex.lark; helper rules beginning with `_` are inlined.
 */
export class LarkLatexGrammar {
  private readonly tokens: readonly LatexToken[];
  private readonly memo = new Map<string, LatexTree[]>();
  private readonly multiplication: ReadonlySet<string>;
  private readonly division: ReadonlySet<string>;
  constructor(private readonly source: string, private readonly options: LatexGrammarOptions = {}, tokens?: readonly LatexToken[]) {
    this.tokens = tokens ?? tokenizeLatex(source, 'lark');
    this.multiplication = new Set(options.multiplicationSymbols ?? ['*', '\\times', '\\cdot']);
    this.division = new Set(options.divisionSymbols ?? ['/', '\\div']);
  }
  private text(i: number): string { return this.tokens[i]?.text ?? ''; }
  private raw(a: number, b: number): string { return this.source.slice(at(this.tokens, a).start, at(this.tokens, b - 1).end); }
  private tree(data: string, ...children: (LatexTree | string)[]): LatexTree { return new LatexTree(data, children); }
  private combine(data: string, left: readonly LatexTree[], right: readonly LatexTree[], middle = ''): LatexTree[] {
    return left.flatMap(l => right.map(r => this.tree(data, l, ...(middle ? [middle] : []), r)));
  }
  private group(a: number, b: number, open: string, close: string, name: string): LatexTree[] {
    return this.text(a) === open && this.text(b - 1) === close ? this.rule('expression', a + 1, b - 1).map(e => this.tree(name, open, e, close)) : [];
  }
  /** NUMBER is greedy; DIGIT in fractions can consume the first digits of a number. */
  private number(a: number, b: number): LatexTree[] {
    if (b === a + 1 && this.text(a) === '\\imaginaryunit') return [this.tree('number', this.text(a))];
    const sep = this.options.decimalSeparator ?? '.';
    let end = a;
    while (/^\d$/.test(this.text(end)) && (end === a || at(this.tokens, end - 1).end === at(this.tokens, end).start)) end++;
    if (end === a) return [];
    if (this.text(end) === sep && at(this.tokens, end - 1).end === at(this.tokens, end).start) {
      end++;
      while (/^\d$/.test(this.text(end)) && at(this.tokens, end - 1).end === at(this.tokens, end).start) end++;
    }
    return end === b ? [this.tree('number', this.raw(a, b))] : [];
  }
  /** _one_letter_symbol and its five subscript/prime terminal variants. */
  private symbol(a: number, b: number): LatexTree[] {
    const raw = this.raw(a, b);
    const match = /^(\\[a-z]+|[a-zA-Z])('*)(?:_(\\[a-z]+|[A-Za-z]|[0-9]|\{(?:\\[a-z]+'*|[a-zA-Z]+'*|[0-9])\}))?('*)$/.exec(raw);
    if (!match || match[3] && match[4]) return [];
    const base = at(match, 1);
    const sub = match[3] ?? '';
    if (base.startsWith('\\') && !GREEK.has(base.slice(1))) return [];
    const greek = /\\([a-z]+)/.exec(sub);
    if (greek && !GREEK.has(at(greek, 1))) return [];
    return [this.tree('symbol', raw)];
  }
  private fractionPart(a: number, b: number, first: boolean): LatexTree[] {
    const groups = this.rule('curly', a, b);
    if (b === a + 1 && /^\d$/.test(this.text(a))) groups.push(this.tree('number', this.text(a)));
    if (!first) groups.push(...this.rule('symbol', a, b).filter(() => !this.raw(a, b).includes('_')));
    return groups;
  }
  private fraction(a: number, b: number, binomial: boolean): LatexTree[] {
    if (!(binomial ? BINOMIALS : FRACTIONS).has(this.text(a))) return [];
    const out: LatexTree[] = [];
    for (let i = a + 2; i < b; i++) out.push(...this.combine(binomial ? 'binomial' : 'fraction', this.fractionPart(a + 1, i, true), this.fractionPart(i, b, false)));
    return out;
  }
  private rule(name: Rule, a: number, b: number): LatexTree[] {
    if (a >= b) return [];
    const key = `${name}:${a}:${b}`;
    const known = this.memo.get(key);
    if (known) return known;
    const out: LatexTree[] = [];
    this.memo.set(key, out);
    switch (name) {
      case 'symbol': out.push(...this.symbol(a, b)); break;
      case 'number': out.push(...this.number(a, b)); break;
      case 'atomic': {
        out.push(...this.rule('symbol', a, b), ...this.rule('number', a, b));
        if (b === a + 1 && this.text(a) === '\\infty') out.push(this.tree('infinity'));
        if (this.text(a) === '\\mathit' && this.text(a + 1) === '{') {
          const prime = /^'+$/.test(this.text(b - 1)) ? this.text(b - 1) : '';
          const end = b - (prime ? 2 : 1);
          if (this.text(end) === '}' && a + 2 < end && /^[a-zA-Z]+(?:\s+[a-zA-Z]+)*'*$/.test(this.raw(a + 2, end))) out.push(this.tree('multi_letter_symbol', this.raw(a + 2, end) + prime));
        }
        break;
      }
      case 'core': out.push(...this.rule('atomic', a, b), ...this.rule('curly', a, b)); break;
      case 'round': out.push(...this.group(a, b, '(', ')', 'group_round_parentheses')); break;
      case 'curly': out.push(...this.group(a, b, '{', '}', 'group_curly_parentheses')); break;
      case 'square': out.push(...this.group(a, b, '[', ']', 'group_square_brackets')); break;
      case 'fraction': out.push(...this.fraction(a, b, false)); break;
      case 'binomial': out.push(...this.fraction(a, b, true)); break;
      case 'func':
        for (const r of ['core', 'round', 'fraction', 'binomial', 'function', 'integral', 'limit', 'matrix'] as const) out.push(...this.rule(r, a, b));
        break;
      case 'power': {
        out.push(...this.rule('func', a, b));
        for (let i = a + 1; i < b - 1; i++) {
          if (this.text(i) !== '^') continue;
          out.push(...this.combine('superscript', this.rule('func', a, i), this.rule('power', i + 1, b), '^'));
          const raw = this.tokens.slice(i + 1, b).map(t => t.text).join('');
          if (/^(?:\\prime|\\ast|\{(?:'+|\*+|(?:\\prime)+|(?:\\ast)+)\})$/.test(raw)) {
            for (const base of this.rule('func', a, i)) out.push(this.tree('superscript', base, '^', raw));
          }
        }
        if (/^'+$/.test(this.text(b - 1))) {
          for (const base of this.rule('symbol', a, b - 1)) if (this.raw(a, b - 1).includes('_')) out.push(this.tree('symbol_prime', base, this.text(b - 1)));
          for (const base of [...this.rule('matrix', a, b - 1), ...this.rule('round', a, b - 1)]) out.push(this.tree('matrix_prime', base, this.text(b - 1)));
        }
        break;
      }
      case 'mul': {
        out.push(...this.rule('power', a, b), ...this.rule('summation', a, b), ...this.rule('product', a, b));
        for (let i = a + 1; i < b; i++) {
          const op = this.text(i);
          if (this.multiplication.has(op) || this.division.has(op)) out.push(...this.combine(this.multiplication.has(op) ? 'mul' : 'div', this.rule('mul', a, i), this.rule('power', i + 1, b), op));
          // adjacent_expressions: the left operand's grammar category matters.
          for (const left of ['symbol', 'number', 'fraction'] as const) out.push(...this.combine('adjacent_expressions', this.rule(left, a, i), this.rule('mul', i, b)));
          out.push(...this.combine('adjacent_expressions', this.rule('round', a, i), [...this.rule('round', i, b), ...this.rule('symbol', i, b)]));
          out.push(...this.combine('adjacent_expressions', this.rule('function', a, i), this.rule('function', i, b)));
        }
        break;
      }
      case 'expression': {
        out.push(...this.rule('mul', a, b));
        if (['+', '-'].includes(this.text(a))) for (const arg of this.rule('mul', a + 1, b)) out.push(this.tree(this.text(a) === '+' ? 'add' : 'sub', this.text(a), arg));
        for (let i = a + 1; i < b - 1; i++) if (['+', '-'].includes(this.text(i))) out.push(...this.combine(this.text(i) === '+' ? 'add' : 'sub', this.rule('expression', a, i), this.rule('mul', i + 1, b), this.text(i)));
        break;
      }
      case 'list': {
        for (const e of this.rule('expression', a, b)) out.push(this.tree('list_of_expressions', e));
        for (let i = a + 1; i < b - 1; i++) if (this.text(i) === ',') {
          for (const e of this.rule('expression', a, i)) for (const rest of this.rule('list', i + 1, b)) out.push(this.tree('list_of_expressions', e, ...rest.children.map(c => cast(c, LatexTree))));
        }
        break;
      }
      case 'function': out.push(...this.functionRule(a, b)); break;
      case 'integral': out.push(...this.integral(a, b)); break;
      case 'limit': out.push(...this.limit(a, b)); break;
      case 'summation': case 'product': out.push(...this.sumProduct(a, b, name)); break;
      case 'matrix': out.push(...this.matrix(a, b)); break;
    }
    const unique = [...new Map(out.map(t => [JSON.stringify(t), t])).values()];
    this.memo.set(key, unique);
    return unique;
  }
  private functionRule(a: number, b: number): LatexTree[] {
    const out: LatexTree[] = [];
    const command = this.text(a);
    const name = FUNCTIONS.get(command);
    if (name) {
      for (const arg of this.rule('expression', a + 1, b)) out.push(this.tree(name, command, arg));
      if (this.text(a + 1) === '^' && /^(sin|cos|tan|csc|sec|cot)$/.test(name)) {
        for (let i = a + 3; i < b; i++) for (const e of this.rule('core', a + 2, i)) for (const x of this.rule('expression', i, b)) out.push(this.tree(`${name}_power`, command, '^', e, x));
      }
      if (command === '\\log' && this.text(a + 1) === '_') {
        for (let i = a + 3; i < b; i++) for (const e of this.fractionPart(a + 2, i, false)) for (const x of this.rule('expression', i, b)) out.push(this.tree('log', command, '_', e, x));
      }
    }
    for (const [open, close, rule] of [['|', '|', 'abs'], ['\\lfloor', '\\rfloor', 'floor'], ['\\lceil', '\\rceil', 'ceil'], ['\\langle', '|', 'bra'], ['|', '\\rangle', 'ket']] as const) {
      if (command === open && this.text(b - 1) === close) for (const arg of this.rule('expression', a + 1, b - 1)) out.push(this.tree(rule, open, arg, close));
    }
    if (command === '\\langle' && this.text(b - 1) === '\\rangle') {
      for (let i = a + 2; i < b - 2; i++) if (this.text(i) === '|') out.push(...this.combine('inner_product', this.rule('expression', a + 1, i), this.rule('expression', i + 1, b - 1)));
    }
    if (this.text(b - 1) === '!') for (const arg of this.rule('func', a, b - 1)) out.push(this.tree('factorial', arg, '!'));
    if (command === '\\overline') for (const arg of this.fractionPart(a + 1, b, true)) out.push(this.tree('conjugate', command, arg));
    if (command === '\\sqrt') {
      for (const arg of this.rule('curly', a + 1, b)) out.push(this.tree('square_root', command, arg));
      for (let i = a + 4; i < b; i++) for (const root of this.rule('square', a + 1, i)) for (const arg of this.rule('curly', i, b)) out.push(this.tree('square_root', command, root, arg));
    }
    if (this.text(b - 1) === ')') for (let i = a + 1; i < b - 2; i++) if (this.text(i) === '(') {
      const names = i === a + 1 && ['\\min', '\\max'].includes(command) ? [this.tree(command.slice(1))] : this.rule('symbol', a, i);
      for (const s of names) for (const args of this.rule('list', i + 1, b - 1)) out.push(this.tree(s.data === 'symbol' ? 'function_applied' : s.data, s, args));
    }
    out.push(...this.matrix(a, b, true));
    return out;
  }
  /** Both bound orders in normal_integral and group_curly_parentheses_special. */
  private bounds(a: number, b: number, sum = false): { end: number; lower: LatexTree; upper: LatexTree }[] {
    const out: { end: number; lower: LatexTree; upper: LatexTree }[] = [];
    const lowerAt = (start: number, end: number): LatexTree[] => {
      if (!sum) return this.rule('core', start, end);
      if (this.text(start) !== '{' || this.text(end - 1) !== '}') return [];
      const result: LatexTree[] = [];
      for (let i = start + 2; i < end - 2; i++) if (this.text(i) === '=') result.push(...this.combine('index_limits', this.rule('atomic', start + 1, i), this.rule('atomic', i + 1, end - 1)));
      return result;
    };
    if (!['_', '^'].includes(this.text(a))) return out;
    for (let i = a + 2; i < b - 1; i++) {
      if (this.text(i) !== (this.text(a) === '_' ? '^' : '_')) continue;
      for (let end = i + 2; end <= b; end++) {
        const lower = this.text(a) === '_' ? lowerAt(a + 1, i) : lowerAt(i + 1, end);
        const upper = this.text(a) === '^' ? this.rule('core', a + 1, i) : this.rule('core', i + 1, end);
        for (const l of lower) for (const u of upper) out.push({ end, lower: l, upper: u });
      }
    }
    return out;
  }
  private integral(a: number, b: number): LatexTree[] {
    if (!['\\int', '\\intop'].includes(this.text(a))) return [];
    const out: LatexTree[] = [];
    const limits = [{ end: a + 1, children: [] as LatexTree[] }, ...this.bounds(a + 1, b).map(l => ({ end: l.end, children: [l.lower, l.upper] }))];
    for (const l of limits) {
      for (let i = l.end; i < b - 1; i++) if (DIFFERENTIAL.has(this.text(i))) {
        const integrands = i === l.end ? [this.tree('number', '1')] : this.rule('expression', l.end, i);
        for (const variable of this.rule('symbol', i + 1, b)) for (const arg of integrands) out.push(this.tree('normal_integral', arg, variable, ...l.children));
      }
      // integral_with_special_fraction: the differential is inside its numerator.
      if (!FRACTIONS.has(this.text(l.end)) || this.text(l.end + 1) !== '{') continue;
      for (let i = l.end + 3; i < b - 3; i++) if (this.text(i) === '}') {
        for (let d = l.end + 2; d < i - 1; d++) if (DIFFERENTIAL.has(this.text(d))) {
          const numerators = d === l.end + 2 ? [this.tree('number', '1')] : this.rule('expression', l.end + 2, d);
          for (const v of this.rule('symbol', d + 1, i)) for (const n of numerators) for (const den of this.rule('curly', i + 1, b)) out.push(this.tree('integral_with_special_fraction', this.tree('fraction', n, den), v, ...l.children));
        }
      }
    }
    return out;
  }
  private sumProduct(a: number, b: number, name: 'summation' | 'product'): LatexTree[] {
    if (this.text(a) !== (name === 'summation' ? '\\sum' : '\\prod')) return [];
    const out: LatexTree[] = [];
    for (const l of this.bounds(a + 1, b, true)) for (const arg of this.rule('expression', l.end, b)) out.push(this.tree(name, arg, l.lower, l.upper));
    return out;
  }
  private limit(a: number, b: number): LatexTree[] {
    if (this.text(a) !== '\\lim' || this.text(a + 1) !== '_' || this.text(a + 2) !== '{') return [];
    const out: LatexTree[] = [];
    for (let arrow = a + 4; arrow < b - 2; arrow++) if (ARROWS.has(this.text(arrow))) {
      for (let end = arrow + 2; end < b - 1; end++) if (this.text(end) === '}') {
        const destinations: LatexTree[] = [...this.rule('expression', arrow + 1, end).map(e => this.tree('limit_destination', e, '+-'))];
        for (let caret = arrow + 2; caret < end - 1; caret++) if (this.text(caret) === '^') {
          const dir = this.tokens.slice(caret + 1, end).map(t => t.text).join('');
          if (/^(?:[+-]|\{[+-]\})$/.test(dir)) for (const e of this.rule('expression', arrow + 1, caret)) destinations.push(this.tree('limit_destination', e, dir.includes('+') ? '+' : '-'));
        }
        for (const v of this.rule('expression', a + 3, arrow)) for (const to of destinations) for (const e of this.rule('expression', end + 1, b)) out.push(this.tree('limit', e, v, to));
      }
    }
    return out;
  }
  private matrix(a: number, b: number, determinant = false): LatexTree[] {
    let start = a;
    let end = b - 1;
    const open = this.text(a);
    if (determinant ? open === '|' : ['(', '['].includes(open)) {
      if (this.text(end) !== (open === '(' ? ')' : open === '[' ? ']' : '|')) return [];
      start++; end--;
      while (this.text(start) === '{') start++;
      while (this.text(end) === '}') end--;
      if (!/^\\begin\{(?:matrix|array)\}/.test(this.text(start)) || !/^\\end\{(?:matrix|array)\}/.test(this.text(end))) return [];
    } else {
      if (!(determinant ? /^\\begin\{vmatrix\}$/ : /^\\begin\{[pb]matrix\}$/).test(open)) return [];
      if (!(determinant ? /^\\end\{vmatrix\}$/ : /^\\end\{[pb]matrix\}$/).test(this.text(end))) return [];
    }
    const rows = (left: number, right: number): LatexTree[] => {
      if (this.text(right - 1) === '\\\\') return rows(left, right - 1);
      const result: LatexTree[] = [];
      for (const row of columns(left, right)) result.push(this.tree('matrix_body', row));
      for (let i = left + 1; i < right - 1; i++) if (this.text(i) === '\\\\') for (const row of columns(left, i)) for (const rest of rows(i + 1, right)) result.push(this.tree('matrix_body', row, ...rest.children.filter((c): c is LatexTree => c instanceof LatexTree)));
      return result;
    };
    const columns = (left: number, right: number): LatexTree[] => {
      const result = this.rule('expression', left, right).map(e => this.tree('matrix_row', e));
      for (let i = left + 1; i < right - 1; i++) if (this.text(i) === '&') for (const e of this.rule('expression', left, i)) for (const rest of columns(i + 1, right)) result.push(this.tree('matrix_row', e, ...rest.children.filter((c): c is LatexTree => c instanceof LatexTree)));
      return result;
    };
    return rows(start + 1, end).map(body => this.tree(determinant ? 'determinant_matrix' : 'matrix', body));
  }
  private parseTokens(): LatexTree[] {
    const end = this.tokens.length;
    const choices = this.rule('expression', 0, end);
    for (let i = 1; i < end - 1; i++) {
      const name = RELATIONS.get(this.text(i));
      if (name) choices.push(...this.combine(name, this.rule('expression', 0, i), this.rule('expression', i + 1, end), this.text(i)));
    }
    return choices;
  }
  parse(): LatexTree {
    const choices = larkTokenizations(this.source, COMMANDS, [...TERMINAL_GROUPS, new Set(['\\int', '\\intop'])]).flatMap(tokens => new LarkLatexGrammar(this.source, this.options, tokens).parseTokens());
    if (!choices.length) throw new LaTeXParsingError(`Invalid LaTeX: ${this.source}`);
    return choices.length === 1 ? this.tree('latex_string', at(choices, 0)) : this.tree('_ambig', ...choices.map(t => this.tree('latex_string', t)));
  }
}
