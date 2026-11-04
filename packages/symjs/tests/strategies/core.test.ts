// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/core.ts (SymPy sympy/strategies/core.py).
// Cases from sympy/strategies/tests/test_core.py and the doctests; expected values are SymPy 1.14's.

import { afterEach, describe, expect, it, vi } from 'vitest';
import { Rational, S } from '../../src';
import { chain, condition, debug, doOne, exhaust, memoize, minimize, nullSafe, switch as switchRule, tryit } from '../../src/strategies';
import { identity, minBy, stdout } from '../../src/strategies/core';

const posdec = (x: number): number => (x > 0 ? x - 1 : x);
const inc = (x: number): number => x + 1;
const dec = (x: number): number => x - 1;

/** A Python StringIO. */
const stringIO = () => {
  let text = '';
  return {
    write: (s: string) => {
      text += s;
    },
    getvalue: () => text,
  };
};

describe('generic strategies', () => {
  it('null_safe', () => {
    const rl = (expr: number): number | undefined => (expr === 1 ? 2 : undefined);
    const safeRl = nullSafe(rl);
    expect(safeRl(1)).toBe(rl(1));
    expect(rl(3)).toBeUndefined();
    expect(safeRl(3)).toBe(3);
    expect(nullSafe((): number | null => null)(4)).toBe(4);
  });

  it('exhaust', () => {
    const sink = exhaust(posdec);
    expect(sink(5)).toBe(0);
    expect(sink(10)).toBe(0);
  });

  it('memoize', () => {
    const calls: number[] = [];
    const rl = memoize((x: number) => {
      calls.push(x);
      return posdec(x);
    });
    expect(rl(5)).toBe(posdec(5));
    expect(rl(5)).toBe(posdec(5));
    expect(rl(-2)).toBe(posdec(-2));
    expect(calls).toEqual([5, -2]);
  });

  it('condition', () => {
    const rl = condition((x: number) => x % 2 === 0, posdec);
    expect(rl(5)).toBe(5);
    expect(rl(4)).toBe(3);
  });

  it('chain', () => {
    const rl = chain(posdec, posdec);
    expect(rl(5)).toBe(3);
    expect(rl(1)).toBe(0);
  });

  it('tryit', () => {
    const rl = (): ReturnType<typeof S.One.add> => {
      throw new RangeError('assert False');
    };
    const safeRl = tryit(rl, RangeError);
    expect(safeRl(S.One).equals(S.One)).toBe(true);
    // an error of another class is not caught
    expect(() => tryit(rl, TypeError)(S.One)).toThrow(RangeError);
  });

  it('do_one', () => {
    const rl = doOne(posdec, posdec);
    expect(rl(5)).toBe(4);
    const rl1 = (x: number): number => (x === 1 ? 2 : x);
    const rl2 = (x: number): number => (x === 2 ? 3 : x);
    const rule = doOne(rl1, rl2);
    expect(rule(1)).toBe(2);
    expect(rule(rule(1))).toBe(3);
    expect(rule(7)).toBe(7);
  });

  it('debug', () => {
    const file = stringIO();
    const rl = debug(posdec, file);
    rl(5);
    rl(0);
    const log = file.getvalue();
    expect(log).toContain(posdec.name);
    expect(log).toContain('5');
    expect(log).toContain('4');
    expect(log).toBe('Rule: posdec\nIn:   5\nOut:  4\n\n');
  });

  it('switch', () => {
    const key = (x: number): number => x % 3;
    const rl = switchRule(key, new Map([
      [0, inc],
      [1, dec],
    ]));
    expect(rl(3)).toBe(4);
    expect(rl(4)).toBe(3);
    expect(rl(5)).toBe(5);
    // an object keyed by strings
    const byName = switchRule((x: number) => (x > 0 ? 'pos' : 'neg'), { pos: dec });
    expect(byName(3)).toBe(2);
    expect(byName(-3)).toBe(-3);
  });

  it('minimize', () => {
    const key = (x: number): number => -x;
    expect(minimize(inc, dec)(4)).toBe(3);
    expect(minimize(inc, dec, { objective: key })(4)).toBe(5);
    expect(() => minimize()(4)).toThrow(RangeError);
    // expressions are ordered by value; the first minimum wins on ties
    expect(minimize((x: number) => Rational.of(x), (x: number) => Rational.of(x - 1))(3).equals(2)).toBe(true);
    expect(minBy(['b', 'a', 'a2'], (s) => s.length)).toBe('b');
  });

  it('identity', () => {
    expect(identity(3)).toBe(3);
  });
});

describe('stdout', () => {
  afterEach(() => {
    vi.unstubAllGlobals();
  });
  it('writes to the standard output of Node.js', () => {
    const spy = vi.spyOn(process.stdout, 'write').mockImplementation(() => true);
    stdout().write('text');
    expect(spy).toHaveBeenCalledWith('text');
    spy.mockRestore();
  });
  it('writes nothing where there is no standard output', () => {
    vi.stubGlobal('process', undefined);
    expect(() => stdout().write('text')).not.toThrow();
    // the default file of debug
    expect(debug(posdec)(3)).toBe(2);
  });
});
