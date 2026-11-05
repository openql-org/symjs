// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/categories/pretty.ts; expected values from SymPy 1.14's pretty().
import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { prettyCategories } from '../../src/categories/pretty';
import { PrettyPrinter } from '../../src/printing/pretty/pretty';

const [A, B, C] = ['A', 'B', 'C'].map((n) => sj.categoryObject(n)) as [sj.SymObject, sj.SymObject, sj.SymObject];
const f = sj.NamedMorphism(A, B, 'f');
const g = sj.NamedMorphism(B, C, 'g');
const alpha = sj.NamedMorphism(A, B, 'alpha');
const K = sj.Category('K', sj.FiniteSet.of(A, B));
const d = sj.Diagram([f, g], new Map([[g.compose(f), 'unique']]));

describe('pretty forms of sympy.categories', () => {
  it('prints in ASCII', () => {
    const p = (e: sj.Expr) => sj.pretty(e, { useUnicode: false });
    expect([f, sj.IdentityMorphism(A), g.compose(f), alpha, K, sj.Diagram()].map(p)).toEqual(['f:A-->B', 'id:A-->A', 'g*f:A-->C', 'alpha:A-->B', 'K', 'EmptySet']);
    expect(p(sj.Diagram([f]))).toBe('{id:A-->A: EmptySet, id:B-->B: EmptySet, f:A-->B: EmptySet}');
    expect(p(d)).toBe('{g*f:A-->C: EmptySet, id:A-->A: EmptySet, id:B-->B: EmptySet, id:C-->C: EmptyS >\n\n> et, f:A-->B: EmptySet, g:B-->C: EmptySet} ==> {g*f:A-->C: {unique}}');
  });

  it('prints in unicode', () => {
    const p = (e: sj.Expr) => sj.pretty(e, { useUnicode: true });
    expect([f, sj.IdentityMorphism(A), g.compose(f), alpha, K, sj.Diagram()].map(p)).toEqual(['f:A——▶B', 'id:A——▶A', 'g∘f:A——▶C', 'α:A——▶B', 'K', '∅']);
    expect(p(sj.Diagram([f]))).toBe('{id:A——▶A: ∅, id:B——▶B: ∅, f:A——▶B: ∅}');
  });

  it('leaves other nodes to the printer', () => {
    expect(prettyCategories(sj.symbol('x'), new PrettyPrinter())).toBeUndefined();
  });
});
