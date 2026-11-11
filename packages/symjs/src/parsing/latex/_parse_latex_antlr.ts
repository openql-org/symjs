// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Hand-written port of SymPy 1.14 LaTeX.g4 and _parse_latex_antlr.py (BSD-3-Clause).

import { at, cast, getOrThrow } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { Sym } from '../../core/nodes';
import { str } from '../../printing/str';
import { LaTeXParsingError } from './errors';
import { tokenizeLatex } from './lexer';
import type { LatexToken } from './lexer';
import { TransformToSymPyExpr } from './lark/transformer';
import { LatexTree } from './tree';

const RELATIONS = new Map([['=', 'eq'], ['\\neq', 'ne'], ['<', 'lt'], ['\\leq', 'lte'], ['\\le', 'lte'], ['\\leqq', 'lte'], ['\\leqslant', 'lte'], ['>', 'gt'], ['\\geq', 'gte'], ['\\ge', 'gte'], ['\\geqq', 'gte'], ['\\geqslant', 'gte']]);
const NORMAL = new Map([
  ['\\sin', 'sin'], ['\\cos', 'cos'], ['\\tan', 'tan'], ['\\csc', 'csc'], ['\\sec', 'sec'], ['\\cot', 'cot'],
  ['\\arcsin', 'arcsin'], ['\\arccos', 'arccos'], ['\\arctan', 'arctan'], ['\\arccsc', 'arccsc'], ['\\arcsec', 'arcsec'], ['\\arccot', 'arccot'],
  ['\\sinh', 'sinh'], ['\\cosh', 'cosh'], ['\\tanh', 'tanh'], ['\\arsinh', 'asinh'], ['\\arcosh', 'acosh'], ['\\artanh', 'atanh'],
  ['\\exp', 'exponential'], ['\\ln', 'log'], ['\\lg', 'log'], ['\\log', 'log'],
]);
const MULTIPLY = new Set(['*', '\\times', '\\cdot']);
const DIVIDE = new Set(['/', '\\div', ':']);
const FRACTION = new Set(['\\frac', '\\dfrac', '\\tfrac']);
const BINOMIAL = new Set(['\\binom', '\\dbinom', '\\tbinom']);
const GROUPS = new Map([['(', ')'], ['[', ']'], ['{', '}'], ['\\{', '\\}']]);
const SPECIAL = new Set(['\\int', '\\sum', '\\prod', '\\lim', '\\sqrt', '\\overline']);
const ARROWS = new Set(['\\to', '\\rightarrow', '\\Rightarrow', '\\longrightarrow', '\\Longrightarrow']);

/** Recursive descent following relation/additive/mp/unary/postfix/exp/comp/atom. */
class AntlrLatexGrammar {
  private pos = 0;
  private stopDifferential = false;
  private readonly tokens: readonly LatexToken[];
  private readonly transformer = new TransformToSymPyExpr('antlr');
  constructor(private readonly source: string, private readonly strict: boolean) { this.tokens = tokenizeLatex(source, 'antlr'); }
  private text(offset = 0): string { return this.tokens[this.pos + offset]?.text ?? ''; }
  private tree(data: string, ...children: (LatexTree | string)[]): LatexTree { return new LatexTree(data, children); }
  private consume(text: string): void {
    if (this.text() !== text) throw new LaTeXParsingError(`Expected ${text} at index ${this.tokens[this.pos]?.start ?? this.source.length}`);
    this.pos++;
  }
  private value(tree: LatexTree): Expr {
    const result = this.transformer.transform(tree);
    if (result instanceof LatexTree) throw new LaTeXParsingError('Expected expression for derivative');
    return result;
  }
  private starts(noFunction = false): boolean {
    const token = this.text();
    if (token === '(' && [')', ','].includes(this.text(1))) return false;
    if (noFunction && (NORMAL.has(token) || SPECIAL.has(token))) return false;
    return /^[A-Za-z0-9]$/.test(token) || /^\\[A-Za-z]+$/.test(token) && !RELATIONS.has(token) && !MULTIPLY.has(token) && !DIVIDE.has(token) && !['\\rangle', '\\rfloor', '\\rceil'].includes(token) || GROUPS.has(token) || token === '|' || token === '\\left|';
  }
  private differential(): boolean { return this.text() === 'd' && /^(?:[a-zA-Z]|\\[a-zA-Z]+)$/.test(this.text(1)); }
  private relation(): LatexTree {
    let left = this.additive();
    while (RELATIONS.has(this.text()) || this.text() === '&' && this.text(1) === '=') {
      if (this.text() === '&') this.pos++;
      const op = this.text();
      this.pos++;
      if (this.text() === '&') this.pos++;
      left = this.tree(getOrThrow(RELATIONS, op), left, op, this.additive());
    }
    return left;
  }
  private additive(): LatexTree {
    let left = this.mp();
    while (['+', '-'].includes(this.text())) {
      const start = this.pos;
      const op = this.text(); this.pos++;
      if (!this.starts() && !['+', '-'].includes(this.text())) { this.pos = start; break; }
      left = this.tree(op === '+' ? 'add' : 'sub', left, op, this.mp());
    }
    return left;
  }
  private mp(noFunction = false): LatexTree {
    let left = this.unary(noFunction);
    while (MULTIPLY.has(this.text()) || DIVIDE.has(this.text())) {
      const start = this.pos;
      const op = this.text(); this.pos++;
      if (!this.starts(noFunction) && !['+', '-'].includes(this.text())) { this.pos = start; break; }
      left = this.tree(MULTIPLY.has(op) ? 'mul' : 'div', left, op, this.unary(noFunction));
    }
    return left;
  }
  private hasSymbol(expr: Expr): boolean { return expr instanceof Sym || expr.args.some(e => this.hasSymbol(e)); }
  private unary(noFunction: boolean): LatexTree {
    if (['+', '-'].includes(this.text())) {
      const op = this.text(); this.pos++;
      return this.tree(op === '+' ? 'add' : 'sub', op, this.unary(noFunction));
    }
    const parts = [this.postfix()];
    while (this.starts(noFunction) && !(this.stopDifferential && this.differential())) {
      const start = this.pos;
      try { parts.push(this.postfix()); }
      catch (e) {
        if (!(e instanceof LaTeXParsingError) || !NORMAL.has(at(this.tokens, start).text)) throw e;
        this.pos = start; break;
      }
    }
    // convert_postfix_list associates implicit products to the right.
    let result = at(parts, parts.length - 1);
    for (let i = parts.length - 2; i >= 0; i--) {
      const current = at(parts, i);
      // The ANTLR converter treats a numeric "2 x 3" as multiplication.
      if (i > 0 && current.data === 'symbol' && current.children[0] === 'x' && !this.hasSymbol(this.value(at(parts, i - 1))) && !this.hasSymbol(this.value(at(parts, i + 1)))) continue;
      result = this.tree('adjacent_expressions', current, result);
    }
    return result;
  }
  private postfix(): LatexTree {
    let result = this.exponent();
    while (this.text() === '!' || this.text() === '|' && ['_', '^'].includes(this.text(1))) {
      if (this.text() === '!') { this.pos++; result = this.tree('factorial', result, '!'); continue; }
      this.pos++;
      const bounds: LatexTree[] = [];
      do {
        this.pos++;
        this.consume('{');
        const lhs = this.additive();
        if (this.text() === '=') { this.pos++; bounds.push(this.tree('bound', lhs, this.additive())); }
        else bounds.push(this.tree('bound', lhs));
        this.consume('}');
      } while (bounds.length === 1 && this.text() === '_');
      result = this.tree('eval_at', result, ...bounds);
    }
    return result;
  }
  private exponent(): LatexTree {
    let base = this.comp();
    while (this.text() === '^') {
      // A one-sided limit marker is consumed by limit_sub, not exp.
      if (['+', '-'].includes(this.text(1)) || this.text(1) === '{' && ['+', '-'].includes(this.text(2)) && this.text(3) === '}') break;
      const start = this.pos++;
      try { base = this.tree('superscript', base, '^', this.script()); }
      catch { this.pos = start; break; }
      if (this.text() === '_') { this.pos++; this.script(); }
    }
    return base;
  }
  private script(stopSubscript = false): LatexTree { return this.text() === '{' ? this.group() : this.atom(!stopSubscript); }
  private group(): LatexTree {
    const open = this.text();
    const close = getOrThrow(GROUPS, open);
    this.pos++;
    const old = this.stopDifferential; this.stopDifferential = false;
    const inner = this.additive();
    this.stopDifferential = old;
    this.consume(close);
    return this.tree('group_curly_parentheses', open, inner, close);
  }
  private comp(): LatexTree {
    if (GROUPS.has(this.text())) return this.group();
    if (this.text() === '|') {
      const start = this.pos++;
      // A complete interval lets nested bars use the same grammar as the outside.
      for (let end = this.tokens.length - 1; end >= start + 2; end--) {
        const close = at(this.tokens, end).text;
        if (close !== '|' && close !== '\\rangle') continue;
        try {
          const innerSource = this.source.slice(at(this.tokens, start).end, at(this.tokens, end).start);
          const inner = new AntlrLatexGrammar(innerSource.trim(), true).parseTree();
          this.pos = end + 1;
          return this.tree(close === '|' ? 'abs' : 'ket', '|', inner, close);
        } catch { /* This bar does not close a complete expression. */ }
      }
      throw new LaTeXParsingError('Unclosed absolute value or ket');
    }
    if (this.text() === '\\lfloor' || this.text() === '\\lceil' || this.text() === '\\langle') {
      const open = this.text(); this.pos++;
      const close = open === '\\lfloor' ? '\\rfloor' : open === '\\lceil' ? '\\rceil' : '|';
      const start = this.pos;
      let depth = 0;
      while (this.pos < this.tokens.length && !(this.text() === close && depth === 0)) {
        if (GROUPS.has(this.text())) depth++;
        if ([...GROUPS.values()].includes(this.text())) depth--;
        this.pos++;
      }
      if (this.pos === start) throw new LaTeXParsingError('Empty group');
      const inner = new AntlrLatexGrammar(this.source.slice(at(this.tokens, start).start, at(this.tokens, this.pos - 1).end).trim(), true).parseTree();
      this.consume(close);
      return this.tree(open === '\\lfloor' ? 'floor' : open === '\\lceil' ? 'ceil' : 'bra', open, inner, close);
    }
    if (NORMAL.has(this.text())) return this.normal();
    if (SPECIAL.has(this.text())) return this.special();
    return this.atom();
  }
  private atom(allowSubscript = true): LatexTree {
    const token = this.text();
    if (/^\d$/.test(token)) {
      let digits = '';
      while (/^\d$/.test(this.text()) || this.text() === ',' && [1, 2, 3].every(i => /^\d$/.test(this.text(i)))) { digits += this.text(); this.pos++; }
      if (this.text() === '.' && /^\d$/.test(this.text(1))) {
        digits += '.'; this.pos++;
        while (/^\d$/.test(this.text())) { digits += this.text(); this.pos++; }
      }
      // A trailing decimal point does not change the integer part. SymPy's
      // error recovery drops the final digit of a multi-digit input such as 12.
      return this.tree('number', digits);
    }
    if (FRACTION.has(token)) return this.fraction();
    if (BINOMIAL.has(token)) {
      this.pos++;
      this.requireGroup(); const n = this.group(); this.requireGroup();
      return this.tree('binomial', n, this.group());
    }
    if (token === '\\mathit') {
      this.pos++; this.consume('{');
      const start = this.pos;
      while (/^[a-zA-Z]$/.test(this.text())) this.pos++;
      const value = this.pos === start ? '' : this.source.slice(at(this.tokens, start).start, at(this.tokens, this.pos - 1).end);
      this.consume('}');
      return this.tree('multi_letter_symbol', value);
    }
    if (this.differential()) {
      this.pos += 2;
      return this.tree('symbol', 'd' + at(this.tokens, this.pos - 1).text.replace('\\', ''));
    }
    if (!/^(?:[A-Za-z]|\\[A-Za-z]+)$/.test(token) || NORMAL.has(token) || SPECIAL.has(token) || RELATIONS.has(token) || MULTIPLY.has(token) || DIVIDE.has(token)) throw new LaTeXParsingError(`Expected an atom at index ${this.tokens[this.pos]?.start ?? this.source.length}`);
    this.pos++;
    let name = token.replace('\\', '');
    let primes = '';
    let sub: LatexTree | false = false;
    for (let i = 0; i < 2; i++) {
      if (this.text() === '_' && sub === false && allowSubscript) { this.pos++; sub = this.script(); }
      else if (/^'+$/.test(this.text()) && !primes) { primes = this.text(); this.pos++; }
    }
    if (name === 'infty') return this.tree('infinity');
    if (sub !== false) name += `_{${str(this.value(sub))}}`;
    const functionCall = this.text() === '(' && ![')', ',', ''].includes(this.text(1));
    if (!token.startsWith('\\') || functionCall) name += primes;
    const symbol = this.tree('symbol', name);
    if (!functionCall) return symbol;
    this.pos++;
    const args = [this.additive()];
    while (this.text() === ',') { this.pos++; args.push(this.additive()); }
    this.consume(')');
    return this.tree('function_applied', symbol, this.tree('list_of_expressions', ...args));
  }
  private requireGroup(): void { if (this.text() !== '{') throw new LaTeXParsingError('Expected {'); }
  private fraction(): LatexTree {
    this.pos++;
    const start = this.pos;
    const part = (): LatexTree => {
      if (/^\d$/.test(this.text())) { const n = this.text(); this.pos++; return this.tree('number', n); }
      this.requireGroup(); return this.group();
    };
    const numerator = part();
    const middle = this.pos;
    const denominator = part();
    const raw = (a: number, b: number): string => this.source.slice(at(this.tokens, a).start, at(this.tokens, b - 1).end);
    const den = raw(middle, this.pos);
    const derivative = /^\{\s*(d\s*|\\partial\s*)([a-zA-Z]|\\[a-zA-Z]+)\s*\}$/.exec(den);
    if (derivative) {
      const upper = raw(start, middle).slice(1, -1).trim();
      const d = at(derivative, 1).trim();
      if (upper.startsWith(d)) {
        const variable = this.tree('symbol', at(derivative, 2).replace('\\', ''));
        const expression = upper.slice(d.length).trim();
        return expression ? this.tree('derivative', new AntlrLatexGrammar(expression, false).parseTree(), variable) : this.tree('derivative_operator', variable);
      }
    }
    return this.tree('fraction', numerator, denominator);
  }
  private normal(): LatexTree {
    const command = this.text(); this.pos++;
    const name = getOrThrow(NORMAL, command);
    let exponent: LatexTree | false = false;
    let base: LatexTree | false = false;
    for (let i = 0; i < 2; i++) {
      if (this.text() === '^' && exponent === false) { this.pos++; exponent = this.script(); }
      else if (this.text() === '_' && base === false) { this.pos++; base = this.script(); }
    }
    let arg: LatexTree;
    if (this.text() === '(') {
      this.pos++; arg = this.additive();
      while (this.text() === ',') { this.pos++; this.additive(); }
      this.consume(')');
    } else arg = this.mp(true);
    let result = name === 'log' && base !== false ? this.tree(name, command, '_', base, arg) : this.tree(name, command, arg);
    if (exponent !== false) {
      // A zero exponent denotes 1; SymPy's truthiness check discards it.
      if (/^(sin|cos|tan|csc|sec|cot|sinh|cosh|tanh)$/.test(name)) result = this.tree(`${name}_power`, command, '^', exponent, arg);
      else result = this.tree('superscript', result, '^', exponent);
    }
    return result;
  }
  private special(): LatexTree {
    const command = this.text(); this.pos++;
    if (command === '\\sqrt') {
      const root = this.text() === '[' ? this.group() : false;
      this.requireGroup();
      return this.tree('square_root', command, ...(root !== false ? [root] : []), this.group());
    }
    if (command === '\\overline') { this.requireGroup(); return this.tree('conjugate', command, this.group()); }
    if (command === '\\lim') return this.limit();
    let lower: LatexTree | false = false;
    let upper: LatexTree | false = false;
    const sum = command !== '\\int';
    for (let i = 0; i < 2; i++) {
      if (this.text() === '_' && lower === false) {
        this.pos++;
        if (sum) {
          this.consume('{'); const v = this.additive(); this.consume('=');
          lower = this.tree('index_limits', v, this.additive()); this.consume('}');
        } else lower = this.script();
      } else if (this.text() === '^' && upper === false) { this.pos++; upper = this.script(lower === false); }
    }
    if (Boolean(lower) !== Boolean(upper) || sum && lower === false) throw new LaTeXParsingError('Both lower and upper bounds are required');
    if (sum) return this.tree(command === '\\sum' ? 'summation' : 'product', this.mp(), cast(lower, LatexTree), cast(upper, LatexTree));
    const old = this.stopDifferential; this.stopDifferential = true;
    let integrand = this.differential() ? this.tree('number', '1') : this.additive();
    this.stopDifferential = old;
    let variable: LatexTree;
    if (this.differential()) { variable = this.tree('symbol', this.text(1).replace('\\', '')); this.pos += 2; }
    else {
      const expr = this.value(integrand);
      const differential = [...expr.freeSymbols()].find(s => s instanceof Sym && s.name.startsWith('d') && s.name.length > 1);
      variable = this.tree('symbol', differential instanceof Sym ? differential.name.slice(1) : 'x');
      if (differential instanceof Sym) {
        // handle_integral substitutes the differential inside a fraction, evaluating it.
        const replaced = expr.subs(differential, 1);
        integrand = new LatexTree('expression_value', [replaced]);
      }
    }
    return this.tree('normal_integral', integrand, variable, ...(lower !== false && upper !== false ? [lower, upper] : []));
  }
  private limit(): LatexTree {
    this.consume('_'); this.consume('{');
    if (!/^(?:[A-Za-z]|\\[A-Za-z]+)$/.test(this.text())) throw new LaTeXParsingError('Expected limit variable');
    const variable = this.tree('symbol', this.text().replace('\\', '')); this.pos++;
    if (!ARROWS.has(this.text())) throw new LaTeXParsingError('Expected limit arrow');
    this.pos++;
    const destination = this.additive();
    let direction = '+-';
    if (this.text() === '^') {
      this.pos++;
      const braces = this.text() === '{'; if (braces) this.pos++;
      if (!['+', '-'].includes(this.text())) throw new LaTeXParsingError('Expected limit direction');
      direction = this.text(); this.pos++;
      if (braces) this.consume('}');
    }
    this.consume('}');
    return this.tree('limit', this.mp(), variable, this.tree('limit_destination', destination, direction));
  }
  parseTree(): LatexTree {
    const tree = this.relation();
    if (this.strict && (this.pos !== this.tokens.length || this.tokens[0]?.start !== 0 || this.tokens.at(-1)?.end !== this.source.length)) throw new LaTeXParsingError('Invalid LaTeX');
    return tree;
  }
  parse(): Expr { return this.value(this.parseTree()); }
}

/** @internal ANTLR grammar semantics without an ANTLR runtime. */
export function parseLatexAntlr(source: string, strict = false): Expr { return new AntlrLatexGrammar(source.trim(), strict).parse(); }
