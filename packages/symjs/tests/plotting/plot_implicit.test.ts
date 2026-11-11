import { expect, it } from 'vitest';
import { symbol, Eq, Gt, And, parse } from '../../src/core';
import { BoolOp } from '../../src/core/boolalg';
import { plotImplicit } from '../../src/plotting';
const x = symbol('x'), y = symbol('y');
it('keeps equality and inequality contour data without a backend', () => { for (const [expr, mode] of [[Eq(y, x), 'contour'], [Gt(y, x), 'contourf']] as const) { const plot = plotImplicit(expr, [x, -1, 1], [y, -2, 2], { adaptive: false, n: 3, lineColor: 'red' }); expect(plot.get(0).getData().at(-1)).toBe(mode); expect(plot.toData().series[0]!.style.color).toBe('red'); } });
it('returns adaptive regions for boolean expressions', () => { const p = plotImplicit(And(Gt(y, 0), Gt(x, 0)), [x, -1, 1], [y, -1, 1], { depth: 0 }); expect(p.get(0).getData().at(-1)).toBe('fill'); expect(p.get(0).getData()[0]!.length).toBeGreaterThan(0); });
it.skip('Matplotlib display and saved image assertions: rendering is performed by connector packages', () => {});
it('ports implicit default domains, bare variables and interval fallback', () => {
  const p = plotImplicit(Eq(y, x)); expect(p.get(0).ranges).toEqual([[x, -5, 5], [y, -5, 5]]); expect(p.get(0).n.slice(0, 2)).toEqual([300, 300]); expect(p.get(0).lineColor).toBe('blue');
  expect(plotImplicit(Eq(y, x), x, y).get(0).ranges).toEqual(p.get(0).ranges);
  expect(plotImplicit(Eq(y, x), [x, -2, 2]).get(0).ranges).toEqual([[x, -2, 2], [y, -5, 5]]);
  const fallback = plotImplicit(parse('Eq(y, re(cos(x) + I*sin(x)))'), x, y, { n: 5 }); expect(fallback.get(0).getData().at(-1)).toBe('contour');
  expect(() => plotImplicit(new BoolOp('And', [x, y]), x, y).get(0).getData()).toThrow('intervalMembership');
  expect(() => plotImplicit(And(Eq(y, parse('gamma(x)')), Gt(x, 0)), x, y).get(0).getData()).toThrow('not implemented');
});
for (const expr of ['Eq(y, cos(x))', 'Eq(y**2, x**3-x)', 'y > 1/x', 'y < 1/tan(x)', 'y >= 2*sin(x)*cos(x)', 'y <= x**2', 'And(Gt(y, exp(x)), Gt(y, x+2))', 'Or(Gt(y, x), Gt(y, -x))', 'x**2-1', 'And(Gt(y, cos(x)), Or(Gt(y, x), Eq(y, x)))', 'y-cos(pi/x)']) it(`SymPy implicit construction: ${expr}`, () => {
  const s = plotImplicit(parse(expr), [x, -5, 5], [y, -5, 5], { n: 5 }).get(0);
  expect(s.getData().at(-1)).toBe('fill'); expect(JSON.parse(JSON.stringify(s.toData()))).toEqual(s.toData());
});
