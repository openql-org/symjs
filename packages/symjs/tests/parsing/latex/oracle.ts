// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { Expr, ExtensionExpr, Float, Rational, Sym, Fn, UndefFn, Constant, Special, BoolAtom, Limit } from '../../../src/core/nodes';
import { Concrete } from '../../../src/core/concrete';
import { ImmutableMatrixNode } from '../../../src/matrices/expressions/matexpr';
import { LatexTree } from '../../../src/parsing/latex/tree';

export interface Case {
  group: string; index: number; evaluate: boolean; src: string; strict?: boolean;
  expected?: unknown; correctExpected?: unknown; difference?: string; error?: string; latex?: string;
}
export function cases(backend: string): Case[] {
  return JSON.parse(readFileSync(new URL(`./fixtures/${backend}.json`, import.meta.url), 'utf8')) as Case[];
}
export function shape(e: Expr | LatexTree): unknown {
  if (e instanceof LatexTree) return [e.data, ...e.children.map(c => typeof c === 'string' ? ['text', c] : shape(c))];
  if (e instanceof Rational) return ['Rational', String(e.p), String(e.q)];
  if (e instanceof Float) return ['Float', Number(e.value)];
  if (e instanceof Sym) return ['Symbol', e.name];
  if (e instanceof Constant || e instanceof Special) return [e.name];
  if (e instanceof BoolAtom) return [e.value ? 'True' : 'False'];
  if (e instanceof ImmutableMatrixNode) return ['Matrix', e.matrix.rows, e.matrix.cols, ...e.matrix.data.map(shape)];
  if (e instanceof Limit) return ['Limit', ...e.args.map(shape), e.dir];
  const name = e instanceof Concrete ? e.kind2 : e instanceof Fn ? e.name === 'abs' ? 'Abs' : e.name : e instanceof ExtensionExpr || e instanceof UndefFn ? e.name : e.kind;
  const relation = new Map([['Eq', 'Equality'], ['Ne', 'Unequality'], ['Lt', 'StrictLessThan'], ['Le', 'LessThan'], ['Gt', 'StrictGreaterThan'], ['Ge', 'GreaterThan']]);
  if (e.kind === 'Rel' && 'op' in e) return [relation.get(String(e.op)), ...e.args.map(shape)];
  return [name, ...e.args.map(shape)];
}
/** Ignore only commutative argument order and the ordering of ambiguity alternatives. */
export function normalize(value: unknown): unknown {
  if (!Array.isArray(value)) return value;
  if (value[0] === 'tuple' && Array.isArray(value[1]) && value[1][1] === 'derivative') return ['derivative_operator', normalize(value[2])];
  const [head, ...raw] = value;
  const args = raw.map(normalize);
  if (['Add', 'Mul', 'Min', 'Max', '_ambig'].includes(String(head))) args.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
  return [head, ...args];
}
