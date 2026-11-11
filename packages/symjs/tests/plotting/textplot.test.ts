import { expect, it } from 'vitest';
import { parse } from '../../src/core';
import { textplot, textplotStr } from '../../src/plotting';
import { reference } from './reference-helpers';
import { upstream } from './upstream-helpers';
for (const f of reference.text) it(`SymPy textplot ${f.expr} ${f.width}x${f.height}`, () => { expect([...textplotStr(parse(f.expr), f.a, f.b, f.width, f.height)]).toEqual(f.lines); expect(textplot(parse(f.expr), f.a, f.b, f.width, f.height)).toBe(f.lines.join('\n') + '\n'); });
it('rejects ambiguous variables and invalid dimensions', () => { expect(() => [...textplotStr(parse('x+y'), 0, 1)]).toThrow(RangeError); expect(() => [...textplotStr(parse('x'), 0, 1, 1)]).toThrow(RangeError); });
for (const [i, f] of upstream.texts.entries()) it(`SymPy ${f.test}, call ${i}`, () => expect([...textplotStr(parse(f.expr), f.a, f.b, f.width, f.height)]).toEqual(f.lines));
