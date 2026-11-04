// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/branch/core.ts (SymPy sympy/strategies/branch/core.py).
// Cases from sympy/strategies/branch/tests/test_core.py; expected values are SymPy 1.14's.

import { afterEach, describe, expect, it, vi } from 'vitest';
import { branch } from '../../../src/strategies';

const { chain, condition, debug, doOne, exhaust, identity, multiplex, notempty, onaction, sfilter, yieldify } = branch;

function* posdec(x: number): Generator<number> {
  yield x > 0 ? x - 1 : x;
}

function* branch5(x: number): Generator<number> {
  if (0 < x && x < 5) yield x - 1;
  else if (5 < x && x < 10) yield x + 1;
  else if (x === 5) {
    yield x + 1;
    yield x - 1;
  } else yield x;
}

const even = (x: number): boolean => x % 2 === 0;

function* inc(x: number): Generator<number> {
  yield x + 1;
}

function* oneToN(n: number): Generator<number> {
  for (let i = 0; i < n; i++) yield i;
}

describe('branching strategies', () => {
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it('exhaust', () => {
    const brl = exhaust(branch5);
    expect(new Set(brl(3))).toEqual(new Set([0]));
    expect(new Set(brl(7))).toEqual(new Set([10]));
    expect(new Set(brl(5))).toEqual(new Set([0, 10]));
  });

  it('debug', () => {
    let log = '';
    const rl = debug(posdec, { write: (s) => void (log += s) });
    void [...rl(5)];
    expect(log).toContain(posdec.name);
    expect(log).toContain('5');
    expect(log).toContain('4');
    expect(log).toBe('Rule: posdec\nIn: 5\nOut: 4\n\n');
    // the default file is the standard output
    const spy = vi.spyOn(process.stdout, 'write').mockImplementation(() => true);
    void [...debug(posdec)(2)];
    expect(spy).toHaveBeenCalledWith('Rule: posdec\n');
  });

  it('multiplex', () => {
    const brl = multiplex(posdec, branch5);
    expect(new Set(brl(3))).toEqual(new Set([2]));
    expect(new Set(brl(7))).toEqual(new Set([6, 8]));
    expect(new Set(brl(5))).toEqual(new Set([4, 6]));
    expect([...brl(3)]).toEqual([2]);
  });

  it('condition', () => {
    const brl = condition(even, branch5);
    expect(new Set(brl(4))).toEqual(new Set(branch5(4)));
    expect(new Set(brl(5))).toEqual(new Set());
  });

  it('sfilter', () => {
    const brl = sfilter(even, oneToN);
    expect(new Set(brl(10))).toEqual(new Set([0, 2, 4, 6, 8]));
  });

  it('notempty', () => {
    function* identIfEven(x: number): Generator<number> {
      if (even(x)) yield x;
    }
    const brl = notempty(identIfEven);
    expect(new Set(brl(4))).toEqual(new Set([4]));
    expect(new Set(brl(5))).toEqual(new Set([5]));
  });

  it('chain', () => {
    expect([...chain<number>()(2)]).toEqual([2]); // identity
    expect([...chain(inc, inc)(2)]).toEqual([4]);
    expect([...chain(branch5, inc)(4)]).toEqual([4]);
    expect(new Set(chain(branch5, inc)(5))).toEqual(new Set([5, 7]));
    expect([...chain(inc, branch5)(5)]).toEqual([7]);
  });

  it('onaction', () => {
    const L: [number, number][] = [];
    const record = (_fn: unknown, input: number, output: number): void => void L.push([input, output]);
    void [...onaction(inc, record)(2)];
    expect(L).toEqual([[2, 3]]);
    void [...onaction(identity, record)(2)];
    expect(L).toEqual([[2, 3]]);
  });

  it('yieldify', () => {
    const yinc = yieldify((x: number) => x + 1);
    expect([...yinc(3)]).toEqual([4]);
  });

  it('do_one', () => {
    // eslint-disable-next-line require-yield
    function* bad(): Generator<number> {
      throw new RangeError('ValueError');
    }
    expect([...doOne(inc)(3)]).toEqual([4]);
    expect([...doOne(inc, bad)(3)]).toEqual([4]);
    expect([...doOne(inc, posdec)(3)]).toEqual([4]);
    // a rule that yields nothing passes on to the next one
    expect([...doOne(sfilter((x: number) => !even(x), inc), posdec)(3)]).toEqual([2]);
    expect([...doOne<number>()(3)]).toEqual([]);
  });
});
