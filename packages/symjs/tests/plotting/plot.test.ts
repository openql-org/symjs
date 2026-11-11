// Data-side ports of SymPy plotting/tests/test_plot.py; rendering belongs to connectors.
import { expect, it } from 'vitest';
import { parse, symbol } from '../../src/core';
import { plot, plotParametric, plot3d, plot3dParametricLine, plot3dParametricSurface, plotContour, Plot, LineOver1DRangeSeries } from '../../src/plotting';
import * as plotting from '../../src/plotting';
import { upstream, decode } from './upstream-helpers';
import { numericEqual } from './reference-helpers';
const x = symbol('x'), y = symbol('y');
it('parses single and multiple Cartesian expressions, explicit ranges and per-series labels', () => {
  expect(plot().length).toBe(0);
  const p = plot(x, x.pow(2), [x, -1, 1], { n: 3, title: 'Title', xlabel: 'X', ylabel: 'Y', zlabel: 'Z', xlim: [-1, 1], ylim: [-2, 2], zlim: [0, 1], aspectRatio: [1, 2], axisCenter: [0, 0], legend: true, size: [4, 3], annotations: [{ text: 'point' }], markers: [1], rectangles: [], fill: [], xscale: 'linear', yscale: 'linear', zscale: 'linear', backend: 'ignored', show: true });
  expect(p.length).toBe(2); expect(p.get(0).getData()).toEqual([[-1, 0, 1], [-1, 0, 1]]); expect(p.toData().options['title']).toBe('Title'); expect(p.toData().options).not.toHaveProperty('backend'); expect(p).not.toHaveProperty('show'); expect(p).not.toHaveProperty('save');
  expect(JSON.parse(JSON.stringify(p.toData()))).toEqual(p.toData());
  const labeled = plot([x, [x, -1, 1], 'linear'], [x.pow(2), [x, 0, 1], 'square'], { n: 3 }); expect([...labeled].map((s) => s.label)).toEqual(['linear', 'square']);
  expect(plot(x, { label: 'A' }).get(0).label).toBe('A'); expect(plot(x, x.pow(2), { label: ['A', 'B'] }).get(1).label).toBe('B');
  expect(plot(x, 'common').get(0).label).toBe('common'); expect(plot([x, { renderingKw: { width: 2 } }]).get(0).renderingKw).toEqual({ width: 2 });
  expect(plot(x, { color: 'red' }).get(0).renderingKw).toEqual({ color: 'red' });
});
it('supports all parametric and surface plot factories', () => {
  const cases = [plotParametric(x, x.pow(2), [x, 0, 1], { n: 3 }), plot3dParametricLine(x, x.pow(2), x.pow(3), [x, 0, 1], { n: 3 }), plot3d(x.add(y), [x, 0, 1], [y, 0, 2], { n: [3, 4] }), plotContour(x.add(y), [x, 0, 1], [y, 0, 2], { n: [3, 4] }), plot3dParametricSurface(x, y, x.mul(y), [x, 0, 1], [y, 0, 2], { n: [3, 4] })];
  expect(cases.map((p) => p.get(0).kind)).toEqual(['parametric2d', 'parametric3d', 'surface', 'contour', 'parametricSurface']);
  for (const p of cases) expect(p.toData().series).toHaveLength(1);
  expect(plotParametric([x, x.pow(2)], [x, x.pow(3)], [x, 0, 1]).length).toBe(2);
});
it('mutates the collection without rendering and validates input', () => {
  const p = new Plot(), s = new LineOver1DRangeSeries(x, [x, -1, 1]); p.append(s); p.extend(plot(x)); p.extend([s]); expect(p.length).toBe(3); p.set(-1, s); expect(p.get(-1)).toBe(s); p.delete(-1); expect(p.length).toBe(2); p.delete(0); expect(p.length).toBe(1); expect(p.toString()).toContain('cartesian line');
  p.set(0, plotParametric(x, x).get(0)); expect(p.toString()).toContain('parametric2d');
  expect(() => p.get(10)).toThrow(); expect(() => p.append(1 as never)).toThrow(TypeError); expect(() => new Plot([], { size: [0, 1] })).toThrow(RangeError); expect(() => new Plot([], { xlim: [0, Infinity] })).toThrow(RangeError);
  expect(() => plotParametric(x)).toThrow(RangeError); expect(() => plot([x], 1)).toThrow(TypeError); expect(() => plot(parse('x+y'))).toThrow(RangeError);
});
it.skip('Matplotlib figures, axes, show/save, backend selection and deprecated renderer segments: rendering is performed by connector packages', () => {});
it('normalizes legacy argument tuples', async () => { const { checkArguments } = await import('../../src/plotting'); expect(checkArguments([x, x.pow(2)], 1, 1)).toEqual([[x, [x, -10, 10]], [x.pow(2), [x, -10, 10]]]); });
for (const [index, fixture] of upstream.factories.entries()) it(`SymPy ${fixture.test}, call ${index}`, () => {
  const name = fixture.factory.replace(/_([a-z])/g, (_, c: string) => c.toUpperCase());
  const factory = (plotting as unknown as Record<string, (...args: unknown[]) => Plot>)[name]!;
  const p = factory(...decode(fixture.args), { ...decode(fixture.options), n: 5, adaptive: false });
  expect(p.length).toBe(fixture.series.length);
  p.series.forEach((actual, i) => {
    const expected = fixture.series[i]!;
    expect(actual.constructor.name).toBe(expected.class);
    if (!expected.label.includes('Dummy')) expect(actual.getLabel()).toBe(expected.label);
    expect(actual.renderingKw).toEqual(expected.renderingKw);
    actual.ranges.forEach((range, j) => {
      const ref = expected.ranges[j]!;
      if (!String((ref[0] as { expr: string }).expr).includes('Dummy')) expect(range[0].toString()).toBe(String((ref[0] as { expr: string }).expr));
      expect(range.slice(1).map(String)).toEqual(ref.slice(1).map((v) => String(decode(v))));
    });
    numericEqual(actual.getData(), expected.data);
  });
});
