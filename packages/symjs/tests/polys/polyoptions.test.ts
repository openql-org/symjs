// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.polyoptions doctests and tests/test_polyoptions.py).

import { describe, expect, it } from 'vitest';
import { I, Sym, sqrt } from '../../src/index';
import { NotImplementedError } from '../../src/core/errors';
import { EX, QQ, RR, ZZ } from '../../src/polys/domains';
import { FlagError, GeneratorsError, OptionError } from '../../src/polys/polyerrors';
import { lex } from '../../src/polys/orderings';
import { Options, allowedFlags, buildOptions, preprocessDomain } from '../../src/polys/polyoptions';

const [x, y, z] = [new Sym('x'), new Sym('y'), new Sym('z')];
const show = (o: Options): string => `{${[...o].map(([k, v]) => `'${k}': ${typeof v === 'boolean' ? (v ? 'True' : 'False') : String(v)}`).join(', ')}}`;

describe('Options', () => {
  it('SymPy doctests', () => {
    expect(show(new Options([x, y, z], { domain: 'ZZ' }))).toBe("{'domain': ZZ, 'gens': (x, y, z), 'auto': False}");
    expect(show(buildOptions([x, y, z], new Map([['domain', 'ZZ']])))).toBe("{'domain': ZZ, 'gens': (x, y, z), 'auto': False}");
    expect(allowedFlags({ domain: ZZ }, [])).toBeUndefined();
    expect(allowedFlags({ domain: ZZ, frac: true }, ['frac'])).toBeUndefined();
    expect(() => allowedFlags({ frac: true }, [])).toThrow(FlagError);
    expect(() => allowedFlags({ bogus: true }, [])).toThrow(OptionError);
  });
  it('derived options', () => {
    expect(show(new Options([x], { modulus: 5 }))).toBe("{'modulus': 5, 'gens': (x,), 'domain': GF(5)}");
    expect(show(new Options([x], { gaussian: true }))).toBe("{'gaussian': True, 'gens': (x,), 'domain': QQ_I, 'auto': False}");
    expect(show(new Options([], { extension: [sqrt(2), sqrt(2)] }))).toBe("{'extension': sqrt(2), 'domain': QQ<sqrt(2)>, 'auto': False}");
    expect(show(new Options([x], { domain: 'QQ[y]' }))).toBe("{'domain': QQ[y], 'gens': (x,), 'auto': False}");
    expect(show(new Options([x], { field: true }))).toBe("{'field': True, 'gens': (x,), 'auto': False}");
    expect(String(new Options([x], { modulus: 5, symmetric: false }).domain)).toBe('GF(5)');
    expect(new Options([], { extension: true }).extension).toBe(true);
    expect(new Options([], { extension: new Set([sqrt(2)]) }).extension?.toString()).toBe('sqrt(2)');
    expect(new Options([], { extension: [] }).extension).toBeNull();
    expect(new Options([], { extension: I }).extension?.toString()).toBe('I');
  });
  it('getters and defaults', () => {
    const o = new Options(null, { gens: [[x, y]], composite: true, order: 'grlex', method: 'ABC', sort: 'x > y', wrt: 'x, y' });
    expect([o.gens.map(String), o.domain, o.field, o.composite, o.auto, o.get('method'), o.get('sort'), o.get('wrt')]).toEqual([['x', 'y'], null, false, true, true, 'abc', ['x', 'y'], ['x', 'y']]);
    expect([new Options([], {}).composite, new Options([], {}).extension, new Options([], {}).option('order')]).toEqual([null, null, lex]);
    expect(new Options([], {}).option('polys')).toBeNull();
    const e = new Options([], {});
    expect(['expand', 'strict', 'auto', 'frac', 'formal', 'include', 'all', 'gen', 'series', 'sort'].map((k) => e.option(k))).toEqual([true, true, true, false, false, false, false, 0, false, []]);
    expect(new Options([], { gens: [null] }).gens).toEqual([]);
    expect(new Options([], { gens: x }).gens).toEqual([x]);
    expect([...new Options([], { domain: 'QQ', frac: true, polys: null }).args.keys()]).toEqual(['domain']);
    const c = new Options([x], { domain: ZZ }).clone({ domain: QQ });
    expect([String(c.domain), String(c.gens)]).toEqual(['QQ', 'x']);
    expect(buildOptions([], { opt: c })).toBe(c);
    expect(new Options([], { sort: [x, y], wrt: [x], gen: 1, symbols: [x], series: true, all: true, include: true, formal: true, expand: false, strict: true, greedy: false, order: lex }).get('wrt')).toEqual(['x']);
    expect(new Options([], { wrt: x, polys: undefined }).get('wrt')).toEqual(['x']);
  });
  it('domain specifications', () => {
    expect(['Z', 'QQ', 'ZZ_I', 'QQ_I', 'EX', 'R', 'RR', 'CC', 'GF(7)', 'FF(3)', 'ZZ[x,y]', 'QQ(x)', 'QQ<sqrt(2)>'].map((d) => String(preprocessDomain(d)))).toEqual(['ZZ', 'QQ', 'ZZ_I', 'QQ_I', 'EX', 'RR', 'RR', 'CC', 'GF(7)', 'GF(3)', 'ZZ[x,y]', 'QQ(x)', 'QQ<sqrt(2)>']);
    expect(preprocessDomain(RR)).toBe(RR);
    expect(() => preprocessDomain('RR_100')).toThrow(NotImplementedError);
    expect(() => preprocessDomain('foo')).toThrow(OptionError);
    expect(() => preprocessDomain(3)).toThrow(OptionError);
  });
  it('errors', () => {
    expect(() => new Options([x], { gens: [y] })).toThrow(OptionError);
    expect(() => new Options([x, x], {})).toThrow(GeneratorsError);
    expect(() => new Options([new Sym('A', { commutative: false })], {})).toThrow(GeneratorsError);
    expect(() => new Options([], { bogus: 1 })).toThrow(OptionError);
    expect(() => new Options([], { frac: true }, null, true)).toThrow(OptionError);
    expect(new Options([], { frac: true }, ['frac'], true).get('frac')).toBe(true);
    expect(() => new Options([], { field: 2 })).toThrow(OptionError);
    expect(() => new Options([], { symmetric: true })).toThrow(OptionError);
    expect(() => new Options([], { domain: ZZ, field: true })).toThrow(OptionError);
    expect(() => new Options([x], { domain: 'ZZ[x]' })).toThrow(GeneratorsError);
    expect(() => new Options([], { domain: EX })).toThrow(GeneratorsError);
    expect(() => new Options([], { split: true })).toThrow(NotImplementedError);
    expect(() => new Options([], { extension: false })).toThrow(OptionError);
    expect(() => new Options([], { modulus: -2 })).toThrow(OptionError);
    expect(() => new Options([], { gens: ['a'] })).toThrow(OptionError);
    expect(() => new Options([], { wrt: 'x,' })).toThrow(OptionError);
    expect(new Options([], { wrt: ' ' }).get('wrt')).toEqual([]);
    expect(() => new Options([], { wrt: 1 })).toThrow(OptionError);
    expect(() => new Options([], { sort: 1 })).toThrow(OptionError);
    expect(() => new Options([], { gen: 'a' })).toThrow(OptionError);
    expect(() => new Options([], { symbols: 1 })).toThrow(OptionError);
    expect(() => new Options([], { method: 1 })).toThrow(OptionError);
  });
});
