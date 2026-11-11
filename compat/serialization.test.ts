// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { deserialize, runCase } from './harness';
import type { Case } from './harness';
import * as sj from '../packages/symjs/src';

const corpus = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8')) as { cases: Case[] };

it('replays the supported receiver families through the public API', () => {
  const modules = [
    'sympy.combinatorics.subsets', 'sympy.combinatorics.graycode', 'sympy.combinatorics.prufer',
    'sympy.logic.algorithms.dpll2', 'sympy.core.rules', 'sympy.ntheory.ecm', 'sympy.assumptions.wrapper',
  ];
  const tags = new Set(['PublicObject', 'GrayCode', 'SATSolver', 'SATLevel', 'Transform', 'ECMPoint']);
  const cases = corpus.cases.filter((c) => modules.includes(c.module) && c.self !== undefined && tags.has(c.self.t));
  expect(cases.length).toBeGreaterThan(90);
  for (const c of cases) expect(runCase(c), `${c.module}: ${c.src}`).toEqual({ status: 'pass' });
});

it('preserves expression keys in factor dictionaries', () => {
  const one = { t: 'Rational', p: '1', q: '1' };
  const two = { t: 'Rational', p: '2', q: '1' };
  const result = deserialize({ t: 'PublicObject', cls: 'Factors', args: [{ t: 'Dict', items: [[two, one]] }] });
  expect(result).toBeInstanceOf(sj.Factors);
  if (!(result instanceof sj.Factors)) throw new TypeError('Factors expected');
  expect(String(result.asExpr())).toBe('2');
  expect([...result.factors.keys()][0]).toBeInstanceOf(sj.Rational);
});

it('keeps unsupported constructors explicit', () => {
  expect(() => deserialize({ t: 'PublicObject', cls: 'MissingClass', args: [] })).toThrow('class MissingClass');
});
