import { expect, it } from 'vitest';
import { symbol } from '../../src/core';
import { plot, PlotGrid } from '../../src/plotting';
it('nests plot descriptions by row and column without creating figures', () => { const p = plot(symbol('x'), { n: 3 }), grid = new PlotGrid(2, 2, p, p, { size: [8, 6], show: true }); expect(grid.get(0)).toBe(p); expect(grid.toData().plots).toHaveLength(2); expect(grid.toData().size).toEqual([8, 6]); expect(grid.toString()).toContain('Plot[1]'); expect(JSON.parse(JSON.stringify(grid.toData()))).toEqual(grid.toData()); expect(new PlotGrid(1, 1).toData().size).toEqual([]); });
it('rejects invalid grid layouts', () => { expect(() => new PlotGrid(0, 1)).toThrow(RangeError); expect(() => new PlotGrid(1, 1, plot(), plot())).toThrow(RangeError); expect(() => new PlotGrid(1, 1, { size: [1, -1] })).toThrow(RangeError); });
