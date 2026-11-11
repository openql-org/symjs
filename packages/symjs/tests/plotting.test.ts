import { expect, it } from 'vitest';
import * as root from '../src/index';
import { parse, symbol } from '../src/core';
import { plot, PlotGrid, intervalmath } from '../src/plotting';

it('provides a standalone connector data entry with lossless gap serialization', () => {
  const x = symbol('x');
  const grid = new PlotGrid(1, 1, plot(parse('sqrt(x)'), [x, -1, 1], { n: 3, title: 'Roots' }));
  const data = grid.toData();
  expect(data.version).toBe(1);
  expect(data.plots[0]!.options['title']).toBe('Roots');
  expect(data.plots[0]!.series[0]!.coordinates).toEqual({ x: [-1, 0, 1], y: ['NaN', 0, 1] });
  expect(JSON.parse(JSON.stringify(data))).toEqual(data);
  expect(intervalmath.sin(new intervalmath.interval(0, Math.PI / 2)).end).toBeCloseTo(1);
  expect(root).not.toHaveProperty('plot');
  expect(root).not.toHaveProperty('DiagramGrid');
});
