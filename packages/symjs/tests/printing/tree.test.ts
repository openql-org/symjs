// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/tree.ts. Expected values from SymPy 1.14 (sympy.printing.tree).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Integral, S, Sym } from '../../src/core/nodes';
import { pprintNodes, printNode, printTree, tree } from '../../src/printing/tree';

const [x, y] = sj.symbols('x y') as [Sym, Sym];

describe('pprint_nodes', () => {
  it('SymPy doctest', () => {
    expect(pprintNodes(['a', 'b1\nb2', 'c'])).toBe('+-a\n+-b1\n| b2\n+-c\n');
  });
  it('no subtrees, blank lines', () => {
    expect(pprintNodes([])).toBe('');
    expect(pprintNodes(['a\n\nb'])).toBe('+-a\n  b\n');
  });
});

describe('tree, print_tree and print_node', () => {
  it('SymPy doctest print_tree(y**x, assumptions=False)', () => {
    expect(printTree(sj.pow(y, x), { assumptions: false })).toBe('Pow: y**x\n+-Symbol: y\n+-Symbol: x\n\n');
  });
  it('the assumptions of symbols (the facts SymPy deduces from those given)', () => {
    const p = sj.symbol('p', { positive: true });
    expect(tree(p)).toBe(
      'Symbol: p\ncommutative: True\ncomplex: True\nextended_negative: False\nextended_nonnegative: True\nextended_nonpositive: False\nextended_nonzero: True\nextended_positive: True\nextended_real: True\nfinite: True\nhermitian: True\nimaginary: False\ninfinite: False\nnegative: False\nnonnegative: True\nnonpositive: False\nnonzero: True\npositive: True\nreal: True\nzero: False\n',
    );
    expect(tree(sj.symbol('n', { integer: true }))).toBe(
      'Symbol: n\nalgebraic: True\ncommutative: True\ncomplex: True\nextended_real: True\nfinite: True\nhermitian: True\nimaginary: False\ninfinite: False\ninteger: True\nirrational: False\nnoninteger: False\nrational: True\nreal: True\ntranscendental: False\n',
    );
    expect(tree(new Sym('A', { commutative: false }))).toBe(
      'Symbol: A\nalgebraic: False\ncommutative: False\ncomplex: False\ncomposite: False\neven: False\nextended_negative: False\nextended_nonnegative: False\nextended_nonpositive: False\nextended_nonzero: False\nextended_positive: False\nextended_real: False\nimaginary: False\ninteger: False\nirrational: False\nnegative: False\nnoninteger: False\nnonnegative: False\nnonpositive: False\nnonzero: False\nodd: False\npositive: False\nprime: False\nrational: False\nreal: False\ntranscendental: False\nzero: False\n',
    );
    expect(printNode(x)).toBe('Symbol: x\ncommutative: True\n');
    expect(printNode(x, { assumptions: false })).toBe('Symbol: x\n');
  });
  it('the arguments in SymPy order, with the containers SymPy has', () => {
    expect(tree(sj.add(sj.mul(x, y), sj.symbol('p', { positive: true })), { assumptions: false })).toBe('Add: p + x*y\n+-Symbol: p\n+-Mul: x*y\n  +-Symbol: x\n  +-Symbol: y\n');
    expect(tree(new Integral([x, x, S.Zero, S.One]), { assumptions: false })).toBe('Integral: Integral(x, (x, 0, 1))\n+-Symbol: x\n+-Tuple: (x, 0, 1)\n  +-Symbol: x\n  +-Zero: 0\n  +-One: 1\n');
    expect(tree(sj.Piecewise([x, sj.Lt(x, 0)], [1, true]), { assumptions: false })).toBe(
      'Piecewise: Piecewise((x, x < 0), (1, True))\n+-ExprCondPair: (x, x < 0)\n| +-Symbol: x\n| +-StrictLessThan: x < 0\n|   +-Symbol: x\n|   +-Zero: 0\n+-ExprCondPair: (1, True)\n  +-One: 1\n  +-BooleanTrue: True\n',
    );
    // the containers SymPy adds (Tuple) have no assumptions
    expect(tree(new Integral([x, x, S.Zero, S.One]))).toBe('Integral: Integral(x, (x, 0, 1))\n+-Symbol: x\n| commutative: True\n+-Tuple: (x, 0, 1)\n  +-Symbol: x\n  | commutative: True\n  +-Zero: 0\n  +-One: 1\n');
    // SymPy shows the cached facts of other nodes; here they show none
    expect(tree(sj.add(x, 2))).toBe('Add: x + 2\n+-Integer: 2\n+-Symbol: x\n  commutative: True\n');
  });
});
