// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/dot.ts. Expected values from SymPy 1.14 (sympy.printing.dot).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Float, Integral, S, Sym } from '../../src/core/nodes';
import { attrprint, defaultStyles, dotedges, dotnode, dotprint, purestr, purestrWithArgs, styleof } from '../../src/printing/dot';
import { srepr } from '../../src/printing/repr';

const [x, y] = sj.symbols('x y') as [Sym, Sym];
const head = (rankdir = 'TD'): string => `digraph{\n\n# Graph style\n"ordering"="out"\n"rankdir"="${rankdir}"\n\n#########\n# Nodes #\n#########\n\n`;
const EDGES = '\n\n#########\n# Edges #\n#########\n\n';
const ADD = "Add(Integer(2), Symbol('x'))";

describe('dotprint (SymPy doctests and options)', () => {
  it('dotprint(x + 2)', () => {
    expect(dotprint(sj.add(x, 2))).toBe(
      `${head()}"${ADD}_()" ["color"="black", "label"="Add", "shape"="ellipse"];\n"Integer(2)_(0,)" ["color"="black", "label"="2", "shape"="ellipse"];\n"Symbol('x')_(1,)" ["color"="black", "label"="x", "shape"="ellipse"];${EDGES}"${ADD}_()" -> "Integer(2)_(0,)";\n"${ADD}_()" -> "Symbol('x')_(1,)";\n}`,
    );
  });
  it('repeat=False', () => {
    expect(dotprint(sj.add(x, 2), { repeat: false })).toBe(
      `${head()}"${ADD}" ["color"="black", "label"="Add", "shape"="ellipse"];\n"Integer(2)" ["color"="black", "label"="2", "shape"="ellipse"];\n"Symbol('x')" ["color"="black", "label"="x", "shape"="ellipse"];${EDGES}"${ADD}" -> "Integer(2)";\n"${ADD}" -> "Symbol('x')";\n}`,
    );
  });
  it('maxdepth', () => {
    const M = "Mul(Symbol('y'), sin(Symbol('x')))";
    expect(dotprint(sj.mul(sj.sin(x), y), { maxdepth: 1 })).toBe(
      `${head()}"${M}_()" ["color"="black", "label"="Mul", "shape"="ellipse"];\n"Symbol('y')_(0,)" ["color"="black", "label"="y", "shape"="ellipse"];\n"sin(Symbol('x'))_(1,)" ["color"="black", "label"="sin", "shape"="ellipse"];${EDGES}"${M}_()" -> "Symbol('y')_(0,)";\n"${M}_()" -> "sin(Symbol('x'))_(1,)";\n}`,
    );
  });
  it('atom, labelfunc and graph attributes', () => {
    expect(dotprint(sj.add(x, 2), { atom: (e) => e.isAtom })).toBe(`${head()}"${ADD}_()" ["color"="black", "label"="Add", "shape"="ellipse"];${EDGES}"${ADD}_()" -> "Integer(2)_(0,)";\n"${ADD}_()" -> "Symbol('x')_(1,)";\n}`);
    expect(dotprint(sj.add(x, 2), { labelfunc: (e) => srepr(e), graphAttributes: { rankdir: 'LR' } })).toBe(
      `${head('LR')}"${ADD}_()" ["color"="black", "label"="Add", "shape"="ellipse"];\n"Integer(2)_(0,)" ["color"="black", "label"="Integer(2)", "shape"="ellipse"];\n"Symbol('x')_(1,)" ["color"="black", "label"="Symbol('x')", "shape"="ellipse"];${EDGES}"${ADD}_()" -> "Integer(2)_(0,)";\n"${ADD}_()" -> "Symbol('x')_(1,)";\n}`,
    );
  });
  it('styles by class (a predicate stands for a class)', () => {
    const I = "Integral(Symbol('x'), Tuple(Symbol('x'), Integer(0), Integer(1)))";
    const T = "Tuple(Symbol('x'), Integer(0), Integer(1))";
    expect(dotprint(new Integral([x, x, S.Zero, S.One]), { styles: [['Basic', { color: 'red' }], [(e) => e instanceof Sym, { shape: 'box' }]] })).toBe(
      `${head()}"${I}_()" ["color"="red", "label"="Integral"];\n"Symbol('x')_(0,)" ["color"="red", "label"="x", "shape"="box"];\n"${T}_(1,)" ["color"="red", "label"="Tuple"];\n"Symbol('x')_(1, 0)" ["color"="red", "label"="x", "shape"="box"];\n"Integer(0)_(1, 1)" ["color"="red", "label"="0"];\n"Integer(1)_(1, 2)" ["color"="red", "label"="1"];${EDGES}"${I}_()" -> "Symbol('x')_(0,)";\n"${I}_()" -> "${T}_(1,)";\n"${T}_(1,)" -> "Symbol('x')_(1, 0)";\n"${T}_(1,)" -> "Integer(0)_(1, 1)";\n"${T}_(1,)" -> "Integer(1)_(1, 2)";\n}`,
    );
  });
});

describe('the helpers', () => {
  it('dotnode', () => {
    expect(dotnode(x)).toBe('"Symbol(\'x\')_()" ["color"="black", "label"="x", "shape"="ellipse"];');
    expect(dotnode(x, { repeat: false })).toBe('"Symbol(\'x\')" ["color"="black", "label"="x", "shape"="ellipse"];');
    expect(dotnode(sj.add(x, 1), { pos: [0, 1] })).toBe('"Add(Integer(1), Symbol(\'x\'))_(0, 1)" ["color"="black", "label"="Add", "shape"="ellipse"];');
  });
  it('dotedges', () => {
    expect(dotedges(sj.add(x, 2))).toEqual([`"${ADD}_()" -> "Integer(2)_(0,)";`, `"${ADD}_()" -> "Symbol('x')_(1,)";`]);
    expect(dotedges(sj.add(x, 2), { repeat: false })).toEqual([`"${ADD}" -> "Integer(2)";`, `"${ADD}" -> "Symbol('x')";`]);
    expect(dotedges(x)).toEqual([]);
    expect(dotedges(sj.add(x, 2), { atom: () => true })).toEqual([]);
  });
  it('purestr', () => {
    expect(purestr(sj.add(x, 2))).toBe(ADD);
    expect(purestr(new Float(2))).toBe("Float('2.0', precision=53)");
    expect(purestrWithArgs(sj.add(x, 2))).toEqual([ADD, ['Integer(2)', "Symbol('x')"]]);
    expect(purestr(sj.MatrixSymbol('x', 2, 2))).toBe("MatrixSymbol(Str('x'), Integer(2), Integer(2))");
    expect(purestr(sj.Tuple())).toBe('Tuple()');
  });
  it('a node without an expression of its own (a predicate) is labelled with its str form', () => {
    const A = "AppliedPredicate(Q.positive, Symbol('x'))";
    expect(dotprint(sj.Q.positive(x))).toBe(
      `${head()}"${A}_()" ["color"="blue", "label"="AppliedPredicate", "shape"="ellipse"];\n"Q.positive_(0,)" ["color"="blue", "label"="Q.positive", "shape"="ellipse"];\n"Symbol('x')_(1,)" ["color"="black", "label"="x", "shape"="ellipse"];${EDGES}"${A}_()" -> "Q.positive_(0,)";\n"${A}_()" -> "Symbol('x')_(1,)";\n}`,
    );
  });
  it('styleof and attrprint', () => {
    expect(styleof(sj.add(x, 1))).toEqual({ color: 'black', shape: 'ellipse' });
    expect(styleof(sj.Eq(x, 1), defaultStyles)).toEqual({ color: 'blue', shape: 'ellipse' });
    expect(styleof(sj.Tuple(x))).toEqual({ color: 'blue', shape: 'ellipse' });
    expect(attrprint({ shape: 'ellipse', color: 'blue' })).toBe('"color"="blue", "shape"="ellipse"');
    expect(attrprint({ b: '2', a: '1' }, '\n')).toBe('"a"="1"\n"b"="2"');
  });
});
