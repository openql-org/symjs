// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Parser of Wolfram Mathematica expressions (SymPy
 * sympy.parsing.mathematica): the code is tokenized (with the omitted
 * multiplication signs added), sorted into a syntax tree of nested lists
 * equivalent to Mathematica's FullForm, and the nodes with an equivalent in
 * SymPy are converted; the other nodes become undefined functions.
 *
 * Ported from SymPy 1.14 (sympy/parsing/mathematica.py, BSD-3-Clause,
 * Copyright (c) SymPy Development Team).
 */

import type { Expr, RelOp } from '../core/nodes';
import { Dummy, Rational, S, UndefFn, impl } from '../core/nodes';
import { add, div, exp, mul, pow, sqrt } from '../core/ops';
import { at, expectType, pair } from '../core/guard';
import { xreplace } from '../core/traverse';
import { and, or } from '../core/boolalg';
import { rel } from '../core/logic';
import { Lambda, LambdaNode } from '../core/lambda';
import { Tuple, TupleNode } from '../core/containers';
import { UnevaluatedExpr } from '../core/classes';
import { SymFunction } from '../core/undef';
import { fn, log } from '../functions/elementary/elementary';
import { Mod } from '../functions/mod';
import { isprime } from '../functions/combinatorial/numbers';
import { prime } from '../ntheory/generate';
import { expand, expand_trig as expandTrig } from '../simplify/expand';
import { parse, parserHooks } from './parser';

/** A node of the FullForm syntax tree: an atom (a name, a number, an operator) or [head, ...arguments]. */
export type FullForm = string | FullForm[];

/** The FullForm builder of an operator: the name of the head, or a function of the operands. */
type OpBuilder = string | ((...xs: FullForm[]) => FullForm);

interface OpLevel {
  readonly type: 'Infix' | 'Prefix' | 'Postfix';
  /** The grouping of an infix operator: a flat list of operands, right or left associative, or none. */
  readonly strat?: 'Flat' | 'Right' | 'Left';
  readonly ops: Readonly<Record<string, OpBuilder>>;
}

const LITERAL = '[A-Za-z][A-Za-z0-9]*';
const NUMBER = '(?:[0-9]+(?:\\.[0-9]*)?|\\.[0-9]+)';
const LITERAL_START = new RegExp(`^${LITERAL}`);
const NUMBER_START = new RegExp(`^-?${NUMBER}`);
const NUMBER_FULL = new RegExp(`^${NUMBER}`);

const ENCLOSURE_OPEN = ['(', '[', '[[', '{'];
const ENCLOSURE_CLOSE = [')', ']', ']]', '}'];

/** -x: a negative number literal, or Times[-1, x]. */
const neg = (x: FullForm): FullForm => (typeof x === 'string' && NUMBER_FULL.test(x) ? `-${x}` : ['Times', '-1', x]);
const inv = (x: FullForm): FullForm => ['Power', x, '-1'];

/** The operator levels, from the lowest precedence to the highest (SymPy _mathematica_op_precedence). */
const OP_PRECEDENCE: readonly OpLevel[] = [
  { type: 'Postfix', ops: { ';': (x) => (Array.isArray(x) && x[0] === 'CompoundExpression' ? [...x, 'Null'] : ['CompoundExpression', x, 'Null']) } },
  { type: 'Infix', strat: 'Flat', ops: { ';': 'CompoundExpression' } },
  { type: 'Infix', strat: 'Right', ops: { '=': 'Set', ':=': 'SetDelayed', '+=': 'AddTo', '-=': 'SubtractFrom', '*=': 'TimesBy', '/=': 'DivideBy' } },
  { type: 'Infix', strat: 'Left', ops: { '//': (x, y) => [y, x] } },
  { type: 'Postfix', ops: { '&': 'Function' } },
  { type: 'Infix', strat: 'Left', ops: { '/.': 'ReplaceAll' } },
  { type: 'Infix', strat: 'Right', ops: { '->': 'Rule', ':>': 'RuleDelayed' } },
  { type: 'Infix', strat: 'Left', ops: { '/;': 'Condition' } },
  { type: 'Infix', strat: 'Flat', ops: { '|': 'Alternatives' } },
  { type: 'Postfix', ops: { '..': 'Repeated', '...': 'RepeatedNull' } },
  { type: 'Infix', strat: 'Flat', ops: { '||': 'Or' } },
  { type: 'Infix', strat: 'Flat', ops: { '&&': 'And' } },
  { type: 'Prefix', ops: { '!': 'Not' } },
  { type: 'Infix', strat: 'Flat', ops: { '===': 'SameQ', '=!=': 'UnsameQ' } },
  { type: 'Infix', strat: 'Flat', ops: { '==': 'Equal', '!=': 'Unequal', '<=': 'LessEqual', '<': 'Less', '>=': 'GreaterEqual', '>': 'Greater' } },
  { type: 'Infix', ops: { ';;': 'Span' } },
  { type: 'Infix', strat: 'Flat', ops: { '+': 'Plus', '-': 'Plus' } },
  { type: 'Infix', strat: 'Flat', ops: { '*': 'Times', '/': 'Times' } },
  { type: 'Infix', strat: 'Flat', ops: { '.': 'Dot' } },
  { type: 'Prefix', ops: { '-': neg, '+': (x) => x } },
  { type: 'Infix', strat: 'Right', ops: { '^': 'Power' } },
  { type: 'Infix', strat: 'Right', ops: { '@@': 'Apply', '/@': 'Map', '//@': 'MapAll', '@@@': (x, y) => ['Apply', x, y, ['List', '1']] } },
  { type: 'Postfix', ops: { "'": 'Derivative', '!': 'Factorial', '!!': 'Factorial2', '--': 'Decrement' } },
  { type: 'Infix', ops: { '[': (x, y) => [x, ...asList(y)], '[[': (x, y) => ['Part', x, ...asList(y)] } },
  { type: 'Prefix', ops: { '{': (x) => ['List', ...asList(x)], '(': (x) => at(asList(x), 0) } },
  { type: 'Infix', ops: { '?': 'PatternTest' } },
  {
    type: 'Postfix',
    ops: {
      _: (x) => ['Pattern', x, ['Blank']],
      '_.': (x) => ['Optional', ['Pattern', x, ['Blank']]],
      __: (x) => ['Pattern', x, ['BlankSequence']],
      ___: (x) => ['Pattern', x, ['BlankNullSequence']],
    },
  },
  { type: 'Infix', ops: { _: (x, y) => ['Pattern', x, ['Blank', y]] } },
  { type: 'Prefix', ops: { '#': 'Slot', '##': 'SlotSequence' } },
];

/** The levels from the highest precedence to the lowest, with their operators by token. */
const LEVELS: readonly (OpLevel & { readonly byToken: ReadonlyMap<string, OpBuilder> })[] = /* @__PURE__ */ [...OP_PRECEDENCE]
  .reverse()
  .map((l) => ({ ...l, byToken: new Map(Object.entries(l.ops)) }));

/** The argument of an operator without an operand: #, ## (SymPy _missing_arguments_default). */
function missingArgument(token: string): FullForm {
  if (token === '#') return ['Slot', '1'];
  if (token === '##') return ['SlotSequence', '1'];
  throw new SyntaxError(`missing operand of ${token}`);
}

/** The contents of an enclosure (a list of nodes). */
const asList = (x: FullForm): FullForm[] => expectType(x, (v): v is FullForm[] => Array.isArray(v), 'a FullForm node');

/** The operand after a - (negated) or a / (inverted). */
const operand = (op: string, x: FullForm): FullForm => (op === '/' ? inv(x) : op === '-' ? neg(x) : x);

const build = (op: OpBuilder, args: FullForm[]): FullForm => (typeof op === 'string' ? [op, ...args] : op(...args));

const escapeRegExp = (s: string): string => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

/** The tokenizer: names, numbers, operators and enclosures (longest first), commas and newlines. */
const TOKENIZER = /* @__PURE__ */ (() => {
  const escaped = [...ENCLOSURE_OPEN, ...ENCLOSURE_CLOSE, ...OP_PRECEDENCE.flatMap((l) => Object.keys(l.ops))].sort((a, b) => b.length - a.length);
  return new RegExp(`(${[LITERAL, NUMBER, ...escaped.map(escapeRegExp), ',', '\n'].join('|')})`, 'g');
})();

/** An operator token (not a node, a name or a number). */
function isOp(token: FullForm): boolean {
  if (Array.isArray(token)) return false;
  return !LITERAL_START.test(token) && !NUMBER_START.test(token);
}

const isValidStar1 = (token: FullForm): boolean => token === ')' || token === '}' || !isOp(token);
const isValidStar2 = (token: FullForm): boolean => token === '(' || token === '{' || !isOp(token);

/** Operators of the same kind (+ and -, * and /) that a flat operator collects. */
function opCompatible(op1: FullForm, op2: string): boolean {
  if (op1 === op2) return true;
  const muldiv = ['*', '/'];
  const addsub = ['+', '-'];
  if (typeof op1 !== 'string') return false;
  return (muldiv.includes(op1) && muldiv.includes(op2)) || (addsub.includes(op1) && addsub.includes(op2));
}

/**
 * An instance converts a string of a Wolfram Mathematica expression to a
 * SymPy expression (SymPy MathematicaParser), in three stages: the
 * tokenizer, the FullForm syntax tree and the conversion of its nodes.
 */
export class MathematicaParser {
  /** The expression for the Mathematica code s. */
  parse(s: string): Expr {
    return this.fromFullformlistToSympy(this.fromTokensToFullformlist(this.fromMathematicaToTokens(s)));
  }

  /** The tokens of the code: strings become ['_Str', text] nodes, comments are removed. @internal */
  fromMathematicaToTokens(codeIn: string): FullForm[] {
    let code = codeIn;
    const splits: FullForm[] = [];
    // strings
    for (;;) {
      const start = code.indexOf('"');
      if (start === -1) {
        if (code.length > 0) splits.push(code);
        break;
      }
      const m = /(?<!\\)"/.exec(code.slice(start + 1));
      if (m === null) throw new SyntaxError('mismatch in string "  " expression');
      const end = start + m.index + 1;
      if (start > 0) splits.push(code.slice(0, start));
      splits.push(['_Str', code.slice(start + 1, end).replaceAll('\\"', '"')]);
      code = code.slice(end + 1);
    }
    // comments
    const parts = splits.map((part) => {
      if (Array.isArray(part)) return part;
      let p = part;
      for (let i = p.indexOf('(*'); i !== -1; i = p.indexOf('(*')) {
        const j = p.indexOf('*)');
        if (j === -1 || j < i) throw new SyntaxError('mismatch in comment (*  *) code');
        p = p.slice(0, i) + p.slice(j + 2);
      }
      return p;
    });
    const isAscii = (p: string): boolean => Array.from({ length: p.length }, (_, i) => p.charCodeAt(i)).every((c) => c < 128);
    const tokens = parts.flatMap((p): FullForm[] => (typeof p === 'string' && isAscii(p) ? [...p.matchAll(TOKENIZER)].map((m) => at(m, 1)) : [p]));
    // newlines at the beginning and at the end
    while (tokens.length && tokens[0] === '\n') tokens.shift();
    while (tokens.length && tokens.at(-1) === '\n') tokens.pop();
    return tokens;
  }

  /** The FullForm syntax tree of the tokens. @internal */
  fromTokensToFullformlist(tokens: FullForm[]): FullForm {
    // the open enclosures, each with the parsed arguments (an argument replaces its tokens after a comma)
    const stack: FullForm[] = [[]];
    const openSeq: string[] = [];
    const top = (): FullForm[] => asList(at(stack, -1));
    // Python's x[-1] of a node or a string
    const lastOf = (x: FullForm): FullForm => at(x, -1);
    for (let pointer = 0; pointer < tokens.length; pointer++) {
      const token = at(tokens, pointer);
      if (typeof token === 'string' && ENCLOSURE_OPEN.includes(token)) {
        top().push(token);
        openSeq.push(token);
        stack.push([]);
      } else if (token === ',') {
        if (top().length === 0 && lastOf(at(stack, -2)) === at(openSeq, -1)) throw new SyntaxError(`${at(openSeq, -1)} cannot be followed by comma ,`);
        stack[stack.length - 1] = this.parseAfterBraces(top());
        stack.push([]);
      } else if (typeof token === 'string' && ENCLOSURE_CLOSE.includes(token)) {
        const open = at(openSeq, -1);
        if (ENCLOSURE_OPEN[ENCLOSURE_CLOSE.indexOf(token)] !== open) {
          // a ]] that closes two [ (or a [ and a [[)
          if (token !== ']]' || open !== '[') throw new SyntaxError('unmatched enclosure');
          const open2 = at(openSeq, -2);
          if (open2 === '[') tokens.splice(pointer + 1, 0, ']');
          else if (open2 === '[[') {
            const next = at(tokens, pointer + 1);
            if (next === ']') tokens[pointer + 1] = ']]';
            else if (next === ']]') tokens.splice(pointer + 2, 0, ']');
            else throw new SyntaxError('unmatched enclosure');
          } else throw new SyntaxError('unmatched enclosure');
        }
        if (top().length === 0 && lastOf(at(stack, -2)) === '(') throw new SyntaxError('( ) not valid syntax');
        stack[stack.length - 1] = this.parseAfterBraces(top(), true);
        const element: FullForm[] = [];
        while (lastOf(at(stack, -1)) !== open) element.unshift(...stack.splice(-1, 1));
        if (open === '(' && element.length !== 1) throw new SyntaxError(`( must be followed by one expression, ${element.length} detected`);
        top().push(element);
        openSeq.pop();
      } else {
        top().push(token);
      }
    }
    if (stack.length !== 1) throw new SyntaxError('Stack should have only one element');
    return this.parseAfterBraces(top());
  }

  /** Splits the tokens at the newlines outside enclosures into the lines of a compound expression. */
  private removeNewlines(lines: FullForm[], tokens: FullForm[], insideEnclosure: boolean): void {
    let pointer = 0;
    while (pointer < tokens.length) {
      if (at(tokens, pointer) !== '\n') {
        pointer++;
        continue;
      }
      if (insideEnclosure || pointer === 0) {
        // newlines inside enclosures are ignored
        tokens.splice(pointer, 1);
        continue;
      }
      let prev: FullForm;
      if (pointer > 1) {
        try {
          prev = this.parseAfterBraces(tokens.slice(0, pointer), insideEnclosure);
        } catch (e) {
          if (!(e instanceof SyntaxError)) throw e;
          tokens.splice(pointer, 1);
          continue;
        }
      } else prev = at(tokens, 0);
      if (Array.isArray(prev) && prev[0] === 'CompoundExpression') lines.push(...prev.slice(1));
      else lines.push(prev);
      tokens.splice(0, pointer);
      pointer = 0;
    }
  }

  /** Adds the omitted * between two operands. */
  private addMissingAsterisks(tokens: FullForm[]): void {
    for (let pointer = 1; pointer < tokens.length; pointer++) {
      if (!isValidStar1(at(tokens, pointer - 1)) || !isValidStar2(at(tokens, pointer))) continue;
      // (SymPy also handles a ( here, but the enclosures are already parsed at the level of *)
      tokens.splice(pointer, 0, '*');
      pointer++;
    }
  }

  /** The FullForm node of tokens whose enclosures are already parsed. @internal */
  parseAfterBraces(tokens: FullForm[], insideEnclosure = false): FullForm {
    let changed = false;
    const lines: FullForm[] = [];
    this.removeNewlines(lines, tokens, insideEnclosure);
    for (const level of LEVELS) {
      if (level.byToken.has('*')) this.addMissingAsterisks(tokens);
      for (let pointer = 0; pointer < tokens.length; pointer++) {
        const token = at(tokens, pointer);
        if (typeof token !== 'string') continue;
        const op = level.byToken.get(token);
        if (op === undefined) continue;
        // a + b and a - b are infix
        if (level.type === 'Prefix' && (token === '+' || token === '-') && pointer > 0 && !isOp(at(tokens, pointer - 1))) continue;
        if (level.type === 'Infix' && (pointer === 0 || pointer === tokens.length - 1 || isOp(at(tokens, pointer - 1)) || isOp(at(tokens, pointer + 1)))) continue;
        changed = true;
        if (level.type === 'Infix') {
          const arg1 = at(tokens, pointer - 1);
          let arg2 = operand(token, at(tokens, pointer + 1));
          tokens.splice(pointer - 1, 3);
          pointer--;
          let node: FullForm;
          if (level.strat === 'Flat') {
            const args = [arg1];
            while (pointer + 1 < tokens.length && opCompatible(at(tokens, pointer), token)) {
              args.push(arg2);
              const [other, next] = pair(tokens.splice(pointer, 2));
              arg2 = operand(String(other), next);
            }
            node = build(op, [...args, arg2]);
          } else if (level.strat === 'Right') {
            // a = b = c is Set[a, Set[b, c]]
            const args = [arg1, arg2];
            while (pointer + 1 < tokens.length && tokens[pointer] === token) args.push(at(tokens.splice(pointer, 2), 1));
            node = args.reduceRight((acc, x) => build(op, [x, acc]));
          } else if (level.strat === 'Left') {
            // a /. b /. c is ReplaceAll[ReplaceAll[a, b], c]
            let acc = arg1;
            while (pointer < tokens.length && tokens[pointer] === token) {
              acc = build(op, [acc, arg2]);
              arg2 = at(tokens.splice(pointer, 2), 1);
            }
            node = build(op, [acc, arg2]);
          } else node = build(op, [arg1, arg2]);
          tokens.splice(pointer, 0, node);
        } else if (level.type === 'Prefix') {
          if (pointer === tokens.length - 1 || isOp(at(tokens, pointer + 1))) tokens[pointer] = missingArgument(token);
          else tokens.splice(pointer, 2, build(op, [at(tokens, pointer + 1)]));
        } else if (pointer === 0 || isOp(at(tokens, pointer - 1))) tokens[pointer] = missingArgument(token);
        else {
          tokens.splice(pointer - 1, 2, build(op, [at(tokens, pointer - 1)]));
          pointer--;
        }
      }
    }
    if (tokens.length > 1 || (lines.length === 0 && tokens.length === 0)) {
      // an operator of lower precedence that must be transformed first (#&[x])
      if (changed) return this.parseAfterBraces(tokens, insideEnclosure);
      throw new SyntaxError('unable to create a single AST for the expression');
    }
    if (lines.length > 0) {
      const t0 = at(tokens, 0);
      const rest = Array.isArray(t0) && t0[0] === 'CompoundExpression' ? t0.slice(1) : tokens;
      return ['CompoundExpression', ...lines, ...rest];
    }
    return at(tokens, 0);
  }

  /** The expression of a FullForm syntax tree. @internal */
  fromFullformlistToSympy(tree: FullForm): Expr {
    const recurse = (e: FullForm): Expr => {
      // an atom is sympified (a name is a symbol, a number a number)
      if (!Array.isArray(e)) return ATOM_CONVERSIONS.get(e) ?? parse(e);
      const h = at(e, 0);
      const head: ExprFunction = Array.isArray(h) ? callable(recurse(h)) : (NODE_CONVERSIONS.get(h) ?? SymFunction(h));
      return head(...e.slice(1).map(recurse));
    };
    return recurse(tree);
  }
}

type ExprFunction = (...args: Expr[]) => Expr;

/** An expression applied as the head of a node: a Lambda. */
function callable(e: Expr): ExprFunction {
  if (e instanceof LambdaNode) return (...args) => e.call(...args);
  throw new TypeError(`'${String(e)}' object is not callable`);
}

const oneArg =
  (f: (x: Expr) => Expr): ExprFunction =>
  (...args) => {
    if (args.length !== 1) throw new TypeError(`expected 1 argument, got ${args.length}`);
    return f(at(args, 0));
  };
const named = (name: Parameters<typeof fn>[0]): ExprFunction => (...args) => fn(name, args);
const relation = (op: RelOp): ExprFunction => (...args) => {
  if (args.length !== 2) throw new TypeError(`expected 2 arguments, got ${args.length}`);
  return rel(op, at(args, 0), at(args, 1));
};

/** The applications of Slot in e (SymPy e.atoms(Slot)). */
function slots(e: Expr, out: Map<string, Expr> = new Map()): Map<string, Expr> {
  if (e instanceof UndefFn && e.name === 'Slot') out.set(e.key, e);
  for (const a of e.args) slots(a, out);
  return out;
}

/** SymPy _parse_Function: Function[body] with the slots #1, #2, ..., or Function[variables, body]. */
function parseFunction(...args: Expr[]): Expr {
  if (args.length === 2) {
    const [vars, body] = pair(args);
    return Lambda(vars instanceof TupleNode ? vars.args : vars, body);
  }
  if (args.length !== 1) throw new SyntaxError('Function node expects 1 or 2 arguments');
  const arg = at(args, 0);
  // the greatest slot number (Python's max of the slot numbers)
  const numbers = [...slots(arg).values()].map((a) => at(a.args, 0));
  if (!numbers.length) throw new RangeError('max() arg is an empty sequence');
  const ints = numbers.filter((n): n is Rational => n instanceof Rational && n.isInteger);
  if (ints.length !== numbers.length) {
    if (numbers.length > 1) throw new TypeError('cannot determine the greatest slot number');
    return Lambda([], arg);
  }
  const count = Number(ints.reduce((m, n) => (n.p > m ? n.p : m), at(ints, 0).p));
  const variables = Array.from({ length: Math.max(0, count) }, (_, i) => new Dummy(`dummy0${i}`));
  const slot = SymFunction('Slot');
  return Lambda(variables, xreplace(arg, new Map(variables.map((v, i) => [slot(i + 1), v]))));
}

/** The heads with an equivalent in SymPy (SymPy _node_conversions). */
const NODE_CONVERSIONS: ReadonlyMap<string, ExprFunction> = /* @__PURE__ */ new Map(Object.entries({
  Times: (...a) => mul(...a),
  Plus: (...a) => add(...a),
  Power: (...a) => {
    if (a.length !== 2) throw new TypeError(`Pow expects 2 arguments, got ${a.length}`);
    return pow(at(a, 0), at(a, 1));
  },
  Rational: (...a) => {
    const [p, q] = a;
    if (a.length !== 2 || !(p instanceof Rational) || !(q instanceof Rational)) throw new TypeError('Rational expects two rational numbers');
    return div(p, q);
  },
  Log: (...a) => (a.length === 2 ? log(at(a, 1), at(a, 0)) : oneArg(log)(...a)),
  Log2: oneArg((x) => log(x, 2)),
  Log10: oneArg((x) => log(x, 10)),
  Exp: oneArg(exp),
  Sqrt: oneArg(sqrt),
  Sin: named('sin'),
  Cos: named('cos'),
  Tan: named('tan'),
  Cot: named('cot'),
  Sec: named('sec'),
  Csc: named('csc'),
  ArcSin: named('asin'),
  ArcCos: named('acos'),
  ArcTan: (...a) => (a.length === 2 ? fn('atan2', [at(a, 1), at(a, 0)]) : fn('atan', a)),
  ArcCot: named('acot'),
  ArcSec: named('asec'),
  ArcCsc: named('acsc'),
  Sinh: named('sinh'),
  Cosh: named('cosh'),
  Tanh: named('tanh'),
  Coth: named('coth'),
  Sech: named('sech'),
  Csch: named('csch'),
  ArcSinh: named('asinh'),
  ArcCosh: named('acosh'),
  ArcTanh: named('atanh'),
  ArcCoth: named('acoth'),
  ArcSech: named('asech'),
  ArcCsch: named('acsch'),
  Expand: oneArg((x) => expand(x)),
  Im: named('im'),
  Re: named('re'),
  Flatten: oneArg((x) => {
    const leaves = (e: Expr): Expr[] => (e instanceof TupleNode ? e.args.flatMap(leaves) : [e]);
    return Tuple(...leaves(x));
  }),
  Polylog: named('polylog'),
  Cancel: (...a) => {
    const cancel = parserHooks.constructors.get('cancel');
    if (cancel === undefined) throw new TypeError("Cancel needs SymPy's cancel: import '@symjs/symjs/simplify' (or '@symjs/symjs')");
    return cancel(a);
  },
  TrigExpand: oneArg(expandTrig),
  Sign: named('sign'),
  Simplify: oneArg((x) => impl.simplify(x)),
  Defer: oneArg((x) => new UnevaluatedExpr(x)),
  Identity: oneArg((x) => x),
  Null: () => S.Zero,
  Mod: (...a) => Mod(...a),
  Max: named('Max'),
  Min: named('Min'),
  Pochhammer: named('rf'),
  ExpIntegralEi: named('Ei'),
  SinIntegral: named('Si'),
  CosIntegral: named('Ci'),
  AiryAi: named('airyai'),
  AiryAiPrime: named('airyaiprime'),
  AiryBi: named('airybi'),
  AiryBiPrime: named('airybiprime'),
  LogIntegral: named('li'),
  PrimePi: named('primepi'),
  Prime: oneArg((x) => Rational.of(prime(x))),
  PrimeQ: oneArg((x) => (isprime(x) ? S.true : S.false)),
  List: (...a) => Tuple(...a),
  Greater: relation('Gt'),
  GreaterEqual: relation('Ge'),
  Less: relation('Lt'),
  LessEqual: relation('Le'),
  Equal: relation('Eq'),
  Or: (...a) => or(...a),
  And: (...a) => and(...a),
  Function: parseFunction,
} satisfies Record<string, ExprFunction>));

/** The atoms with an equivalent in SymPy. */
const ATOM_CONVERSIONS: ReadonlyMap<string, Expr> = /* @__PURE__ */ new Map([
  ['I', S.I],
  ['Pi', S.Pi],
]);

/**
 * The expression of a string of Wolfram Mathematica code (SymPy
 * parse_mathematica). Both the standard input form and the FullForm are
 * supported; nodes without an equivalent become undefined functions, as in
 * Mathematica's FullForm.
 *
 * Example: parseMathematica('Sin[x]^2 Tan[y]') is sin(x)**2*tan(y);
 * parseMathematica('x_.') is Optional(Pattern(x, Blank())).
 */
export function parseMathematica(s: string): Expr {
  return new MathematicaParser().parse(s);
}
