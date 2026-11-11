import { describe, expect, it } from 'vitest';
import { parse, symbol, NoMatch, Eq, And, Gt, Lt, I } from '../../src/core';
import * as p from '../../src/plotting';
import { discretize, encodePlotData, intervalEvaluate } from '../../src/plotting/series';
import { BoolOp } from '../../src/core/boolalg';
import { reference, fromFixture, numericEqual } from './reference-helpers';
import { upstreamSeries, decode } from './upstream-helpers';
const x = symbol('x'), y = symbol('y'), t = symbol('t'), a = symbol('a');
for (const [index, fixture] of upstreamSeries.fixtures.entries()) it(`SymPy ${fixture.test}, series ${index}`, () => {
  const constructor = (p as unknown as Record<string, new (...args: unknown[]) => p.BaseSeries>)[fixture.class]!;
  const args = decode(fixture.args) as unknown[];
  const n = fixture.class === 'List2DSeries' ? 2 : fixture.class === 'ParametricSurfaceSeries' ? 5 : fixture.class === 'Parametric3DLineSeries' ? 4 : ['Parametric2DLineSeries', 'SurfaceOver2DRangeSeries', 'ContourSeries', 'ImplicitSeries'].includes(fixture.class) ? 3 : 2;
  if (args.length === n) args.push('');
  const series = new constructor(...args, decode(fixture.options));
  for (const [name, value] of Object.entries(fixture.expected)) {
    const actual = name === 'latexLabel' ? series.getLabel(true) : Reflect.get(series, name);
    expect(actual, `${fixture.test}: ${name}`).toEqual(value);
  }
  if (fixture.str) expect(series.toString()).toBe(fixture.str);
});
for (const [i, f] of reference.series.entries()) it(`SymPy series reference ${i}: ${f.cls} ${f.exprs.join(', ')}`, () => {
  const series = fromFixture(f);
  numericEqual(series.getData(), f.data);
  expect(series.getLabel()).toBe(f.label);
  expect(series.n).toEqual(f.n);
  expect(JSON.parse(JSON.stringify(series.toData()))).toEqual(series.toData());
});
describe('adaptive properties (random SymPy points are not compared exactly)', () => {
  for (const series of [new p.LineOver1DRangeSeries(parse('sin(x)'), [x, -2, 2], '', { adaptive: true, depth: 8 }), new p.Parametric2DLineSeries(parse('cos(t)'), parse('sin(t)'), [t, -2, 2], '', { adaptive: true, depth: 8 }), new p.Parametric3DLineSeries(t, t.pow(2), t.pow(3), [t, -2, 2], '', { adaptive: true, depth: 8 })]) {
    it(`keeps endpoints and bounded monotone parameters for ${series.kind}`, () => { const d = series.getData(), ts = series.isParametric ? d.at(-1)! : d[0]!; expect(ts[0]).toBe(-2); expect(ts.at(-1)).toBe(2); expect(ts.every((v, i) => i === 0 || v > ts[i - 1]!)).toBe(true); expect(ts.length).toBeLessThanOrEqual(257); expect(d.every((values) => values.length === ts.length)).toBe(true); });
  }
});
it('updates symbolic parameters and range endpoints without stale caches', () => {
  const s = new p.LineOver1DRangeSeries(a.mul(x), [x, a.neg(), a], '', { n: 3, params: new Map([[a, 2]]) });
  expect(s.getData()).toEqual([[-2, 0, 2], [-4, 0, 4]]); s.params = new Map([[a, 3]]); expect(s.getData()).toEqual([[-3, 0, 3], [-9, 0, 9]]);
  expect(s.isInteractive).toBe(true); expect(s.var).toBe(x); expect(s.start).toEqual({ re: -3, im: 0 }); expect(s.end).toEqual({ re: 3, im: 0 });
  s.nbOfPoints = 5; expect(s.nbOfPoints).toBe(5); s.n = [3, 4, 5]; expect(s.n).toEqual([3, 4, 5]);
  expect(s.getPoints()).toEqual(s.getData()); expect(s.toString()).toContain('cartesian line');
});
it('returns callable, list and generic series data with styling', () => {
  const line = new p.LineOver1DRangeSeries((z) => ({ re: z, im: 0 }), [x, 0, 1], 'f', { n: 3, lineColor: 2, renderingKw: { width: 3 } });
  expect(line.getData()).toEqual([[0, 0.5, 1], [0, 0.5, 1]]); expect(line.getColorArray()).toEqual([2, 2]); expect(line.getLabel(true)).toBe('f');
  line.label = 'new'; expect(line.label).toBe('new'); expect(line.toData().style.color).toBe(2);
  const list = new p.List2DSeries([0, a, 3], [1, 2, 3], 'points', { params: new Map([[a, 2]]), isPoint: true, isFilled: false, useCm: true, colorFunc: (x, y) => x + y });
  expect(list.getData()).toEqual([[0, 2, 3], [1, 2, 3], [1, 4, 6]]); expect(list.var).toBe(NoMatch); expect(list.start).toBe(NoMatch); expect(list.end).toBe(NoMatch);
  expect(list.toData().style.isFilled).toBe(false);
  const generic = new p.GenericDataSeries('markers', [[1, 2], [3, 4]], { marker: 'o' }); expect(generic.isGeneric).toBe(true); expect(generic.getData()).toEqual([[1, 2], [3, 4]]);
  expect(() => new p.List2DSeries([1], [1, 2])).toThrow(RangeError);
});
it('handles logarithmic meshes, integer domains and invalid ranges', () => {
  expect(discretize(-1, -100, 3, 'log')).toEqual([-1, -10.000000000000002, -100]);
  expect(discretize(3.2, -1.2, 4, 'linear', true)).toEqual([3, 2, 1, 0, -1]);
  expect(() => discretize(0, 1, 3, 'log')).toThrow(RangeError); expect(() => discretize(1, Infinity, 3)).toThrow(RangeError); expect(() => discretize(0, 1, 1)).toThrow(RangeError);
  expect(() => new p.LineOver1DRangeSeries(x, [x, 0, I])).toThrow(RangeError);
  expect(() => new p.LineOver1DRangeSeries(y, [x, 0, 1])).toThrow('Unknown'); expect(() => new p.LineOver1DRangeSeries(x, [x, x, 1])).toThrow('range');
  expect(() => new p.LineOver1DRangeSeries(x, [x, 0, 1], '', { depth: -1 })).toThrow(RangeError);
  expect(() => new p.LineOver1DRangeSeries(x, [x, 0, 1], '', { n: [] })).toThrow(RangeError);
});
it('keeps exclusion gaps and phase unwrapping in the numeric result', () => {
  const s = new p.LineOver1DRangeSeries(x, [x, -2, 2], '', { n: 5, exclude: [0, 10] });
  const data = s.getData(); expect(data[0]).toContain(0); expect(data[1]!.filter(Number.isNaN)).toHaveLength(1);
  expect(data[0]!.length).toBe(data[1]!.length);
  const descending = new p.LineOver1DRangeSeries(x, [x, 2, -2], '', { n: 5, exclude: 0 }).getData(); expect(descending[0]!.length).toBe(descending[1]!.length); expect(descending[1]!.filter(Number.isNaN)).toHaveLength(1);
  const unwrapped = new p.LineOver1DRangeSeries((t) => t > 0 ? -3 : 3, [x, -1, 1], '', { n: 3, unwrap: true });
  expect(unwrapped.getData()[1]![2]).toBeCloseTo(2 * Math.PI - 3);
});
it('computes implicit enclosures and predicates directly', () => {
  const s = new p.ImplicitSeries(Eq(x.pow(2).add(y.pow(2)), 1), [x, -2, 2], [y, -2, 2], '', { adaptive: true, depth: 1 });
  const [boxes, mode] = s.getData(); expect(mode).toBe('fill'); expect((boxes as p.IntervalBox[]).length).toBeGreaterThan(0);
  for (const [a, b] of boxes as p.IntervalBox[]) expect(a.pow(2).add(b.pow(2)).contains(1)).toBe(true);
  const region = new p.ImplicitSeries(And(Gt(x, 0), Lt(y, 0)), [x, -1, 1], [y, -1, 1], '', { adaptive: true }); expect(region.toData().coordinates['mode']).toBe('fill');
  expect(() => intervalEvaluate(x, new Map())).toThrow('Missing');
  expect(encodePlotData([NaN, Infinity, -Infinity])).toEqual(['NaN', 'Infinity', '-Infinity']); expect(() => encodePlotData(undefined)).toThrow(TypeError);
});
it('exposes surface counts, ranges, colors and parameter meshes', () => {
  const s = new p.ParametricSurfaceSeries(x, y, x.add(y), [x, 0, 2], [y, 0, 3], '', { n: [3, 4], surfaceColor: 7 });
  expect([s.varU, s.varV, s.startU, s.endU, s.startV, s.endV]).toEqual([x, y, 0, 2, 0, 3]); expect(s.nbOfPointsU).toBe(3); expect(s.nbOfPointsV).toBe(4);
  s.nbOfPointsU = 4; s.nbOfPointsV = 3; expect(s.n.slice(0, 2)).toEqual([4, 3]);
  expect(s.getMeshes()).toEqual(s.getData().slice(0, 3)); expect(s.getParameterMeshes()).toEqual(s.getData().slice(3)); expect(s.getColorArray()).toEqual([[7, 7, 7], [7, 7, 7]]);
  expect(p.centersOfSegments([0, 2, 4])).toEqual([1, 3]); expect(p.centersOfFaces([[0, 2], [2, 4]])).toEqual([[2]]); expect(p.flat([0, 0], [1, 1], [2, 2])).toBe(true); expect(p.flat([0, 0], [0, 0], [1, 2])).toBe(true); expect(p.flat([0, 0], [1, 1], [1, 2])).toBe(false);
});
it('preserves computed labels, scalar callbacks and serialized metadata', () => {
  const f = new p.LineOver1DRangeSeries((v) => v * v, [x, 0, 1], '', { n: 3 });
  expect(f.getLabel()).toBe(''); expect(f.expr).toBeTypeOf('function');
  const param = new p.Parametric2DLineSeries(x, x.pow(2), [x, 0, 1], NoMatch, { n: 3, useCm: false });
  expect(param.getLabel()).toBe('(x, x**2)'); expect(param.getLabel(true)).toContain('$'); expect(param.expr).toHaveLength(2); expect(param.getPoints()).toHaveLength(2); expect(param.getParameterPoints()).toEqual([0, 0.5, 1]);
  expect(new p.LineOver1DRangeSeries(x, [x, 0, 1], NoMatch).getLabel(true, '<%s>')).toBe('<x>');
  expect(encodePlotData(new Map([[x, [Infinity]]]))).toEqual([['x', ['Infinity']]]); expect(encodePlotData({ flag: true, omitted: undefined, fn: () => 1 })).toEqual({ flag: true });
  expect(encodePlotData('name')).toBe('name');
  expect(new p.ContourSeries(x.add(y), [x, 0, 1], [y, 0, 1]).isContour).toBe(true);
  expect(new p.ImplicitSeries(x.add(y), [x, 0, 1], [y, 0, 1]).isImplicit).toBe(true);
});
it('evaluates numeric and symbolic color functions on line and surface meshes', () => {
  const cartesian = new p.LineOver1DRangeSeries(x, [x, 0, 1], '', { n: 3, lineColor: (x, y) => x + y });
  expect(cartesian.getColorArray()).toEqual([0.5, 1.5]); expect(cartesian.toData().style.color).toEqual([0, 1, 2]);
  const symbolic = new p.LineOver1DRangeSeries(x, [x, 0, 1], '', { n: 3, params: new Map([[a, 2]]), colorFunc: a.mul(x) }); expect(symbolic.evalColorFunc([0, 0.5, 1], [0, 0.5, 1])).toEqual([0, 1, 2]);
  const constant = new p.LineOver1DRangeSeries(x, [x, 0, 1], '', { n: 3, colorFunc: () => 4 }); expect(constant.toData().style.color).toEqual([4, 4, 4]);
  const surface = new p.SurfaceOver2DRangeSeries(x.add(y), [x, 0, 1], [y, 0, 1], '', { n: [3, 3], surfaceColor: (x, y) => x + y, tx: (x) => x + 1, tz: (z) => z * 2 });
  expect(surface.getColorArray()).toEqual([[1.5, 2], [2, 2.5]]); expect(surface.toData().style.color).toHaveLength(3);
  const param = new p.ParametricSurfaceSeries(x, y, x.add(y), [x, 0, 1], [y, 0, 1], '', { n: [3, 3], colorFunc: x.add(y) }); expect(param.evalColorFunc(...param.getData())).toEqual(param.getData()[2]);
  expect(new p.List2DSeries([], [], '', { useCm: false }).getData()).toEqual([[], []]);
  expect(new p.LineOver1DRangeSeries(x, [x, 0, 1]).evalColorFunc()).toEqual([]);
});
it('handles adaptive logarithmic and non-real regions, steps, and exclusions', () => {
  const logarithmic = new p.LineOver1DRangeSeries(parse('sqrt(x)'), [x, 1, 10], '', { adaptive: true, depth: 2, xscale: 'log' }); expect(logarithmic.getData()[0]).toHaveLength(5);
  const imaginary = new p.LineOver1DRangeSeries(parse('sqrt(x)'), [x, -2, -1], '', { adaptive: true, depth: 2 }); expect(imaginary.getData()[1]!.every(Number.isNaN)).toBe(true);
  const curve = new p.Parametric2DLineSeries(x, x.pow(2), [x, -1, 1], '', { n: 5, exclude: 0.2 }); expect(curve.getData()[0]!.some(Number.isNaN)).toBe(true);
  const space = new p.Parametric3DLineSeries(x, x, x, [x, 0, 1], '', { n: 3, steps: true }); expect(space.getData()[0]).toHaveLength(7);
  const step = new p.Parametric2DLineSeries(x, x, [x, 0, 1], '', { n: 3, steps: true }); expect(step.getData()[0]).toHaveLength(5);
  const poles = new p.LineOver1DRangeSeries(parse('1/x'), [x, -1, 1], '', { n: 10, detectPoles: true, eps: 1 }); expect(poles.getData()[1]!.some(Number.isNaN)).toBe(true);
  const unwrap = new p.LineOver1DRangeSeries((v) => v > 0 ? -3 : 3, [x, -1, 1], '', { n: 3, unwrap: { period: 2 * Math.PI, discont: 4 } }); expect(unwrap.getData()[1]![2]).toBeCloseTo(2 * Math.PI - 3);
  expect(() => new p.List2DSeries([0, 1, 2], [0, 1, 2], '', { exclude: 0.5 }).getData()).toThrow('continuous parameter');
});
it('validates complex ranges, callback errors and repeated variables', () => {
  const s = new p.LineOver1DRangeSeries(x, [x, { re: 1, im: 1 }, { re: 2, im: 1 }], '', { n: 3, return: 'real' }); expect(s.getData()[1]).toEqual([1, 1.5, 2]);
  expect(() => new p.SurfaceOver2DRangeSeries(x, [x, 0, 1], [x, 0, 1])).toThrow('same symbol');
  expect(() => new p.Parametric2DLineSeries(x, x, [x, 0, I], '', { n: 3 }).getData()).toThrow('imaginary');
  expect(() => new p.LineOver1DRangeSeries(() => { throw new TypeError('invalid callback'); }, [x, 0, 1], '', { n: 3 }).getData()).toThrow('invalid callback');
});
it('evaluates interval function domains, boolean relations and parameterized predicates', () => {
  const env = new Map([[x.key, new p.intervalmath.interval(0.25, 0.5)], [y.key, new p.intervalmath.interval(1, 2)]]);
  for (const expr of ['sin(x)', 'cos(x)', 'log(x)', 'exp(x)', 'x*y', 'x**y', 'Ne(x, y)', 'x <= y', 'x >= y', 'Not(Lt(x, y))', 'Or(Lt(x, y), Gt(x, y))', 'Xor(Lt(x, y), Gt(x, y))', 'True']) expect(intervalEvaluate(parse(expr), env)).toBeDefined();
  expect(() => intervalEvaluate(parse('gamma(x)'), env)).toThrow('not implemented');
  const s = new p.ImplicitSeries(Gt(x, a), [x, -1, 1], [y, -1, 1], '', { adaptive: true, params: new Map([[a, 0]]) }); expect(s.getData()[0]!.length).toBeGreaterThan(0);
  expect(new p.ImplicitSeries(x.add(y), [x, -1, 1], [y, -1, 1], '', { adaptive: true }).getData().at(-1)).toBe('fill');
});
it('handles unprojected implicit expressions, callback descriptions and generic channels', () => {
  expect(new p.LineOver1DRangeSeries((x) => x, [x, 0, 1]).toString()).toContain('cartesian line: ');
  expect(new p.GenericDataSeries('custom', [[1], [2], [3], [4]]).toData().coordinates['data3']).toEqual([4]);
  expect(new p.ImplicitSeries(x.add(y), [x, 0, 1], [y, 0, 1], '', { n: 3 }).getData().at(-1)).toBe('contour');
  // Not on a symbol remains a Boolean node rather than simplifying a relational complement.
  const env = new Map([[x.key, new p.intervalmath.interval(0, 1)]]);
  expect(intervalEvaluate(new BoolOp('Not', [Eq(x, 0)]), env)).toBeDefined();
  expect(intervalEvaluate(new BoolOp('ITE', [Gt(x, 0), Eq(x, 1), Lt(x, 0)]), env)).toBeDefined();
  expect(new p.LineOver1DRangeSeries(parse('log(1/x)'), [x, 0, 1], '', { n: 3 }).getData()[1]![0]).toBeNaN();
});
it('serializes the sampled color channel once and retains generic primitives', () => {
  const curve = new p.Parametric2DLineSeries(t, t.pow(2), [t, 0, 2], '', { n: 3, colorFunc: (t) => t * t });
  expect(curve.toData().style.color).toEqual([0, 1, 4]);
  expect(curve.toData().coordinates['color']).toEqual([0, 1, 4]); expect(curve.getColorArray()).toEqual([0.5, 2.5]);
  const space = new p.Parametric3DLineSeries(t, t, t.pow(2), [t, 0, 2], '', { n: 3 }); expect(space.getColorArray()).toEqual([0.5, 1.5]); expect(space.evalColorFunc()).toEqual([]);
  const transformed = new p.Parametric2DLineSeries(t, t, [t, 0, 2], '', { n: 3, tp: (t) => t * 2 });
  expect(transformed.getParameterPoints()).toEqual([0, 2, 4]);
  expect(new p.GenericDataSeries('markers', [[1], [2]]).toData().coordinates['type']).toBe('markers');
  const region = new p.ImplicitSeries(And(Eq(x, y), Gt(x, 0)), [x, -1, 1], [y, -1, 1]);
  expect(region.hasEquality).toBe(true);
  expect(region.getData()[0]!.length).toBeGreaterThan(0);
});
it('ports symbolic pole and step discontinuity detection with parameter substitution', () => {
  const s = new p.LineOver1DRangeSeries(parse('tan(a*x)'), [x, -Math.PI, Math.PI], '', { n: 1000, detectPoles: 'symbolic', params: new Map([[a, 1]]) });
  expect(s.getData()[1]!.some(Number.isNaN)).toBe(true);
  numericEqual(s.polesLocations, [-Math.PI / 2, Math.PI / 2]);
  const step = new p.LineOver1DRangeSeries(parse('frac(x)'), [x, -10, 10], '', { n: 1000, detectPoles: 'symbolic' });
  step.getData(); expect(step.polesLocations).toEqual(Array.from({ length: 21 }, (_, i) => i - 10));
  const reciprocal = new p.LineOver1DRangeSeries(parse('1/x'), [x, -1, 1], '', { n: 5, detectPoles: 'symbolic', tx: (x) => x + 1 });
  reciprocal.getData(); expect(reciprocal.polesLocations).toEqual([1]);
  expect(() => new p.LineOver1DRangeSeries((x) => x, [x, 0, 1], '', { n: 3, detectPoles: 'symbolic' }).getData()).toThrow(TypeError);
  for (const expr of ['1/(x+sin(x))', 'floor(1/x)']) expect(() => new p.LineOver1DRangeSeries(parse(expr), [x, -1, 1], '', { n: 3, detectPoles: 'symbolic' }).getData()).toThrow();
  expect(() => new p.LineOver1DRangeSeries(parse('floor(x)'), [x, 0, 1000002], '', { n: 3, detectPoles: 'symbolic' }).getData()).toThrow('Too many');
});
it('ports test_sums with integer meshes and parameterized finite summations', () => {
  const sum = new p.LineOver1DRangeSeries(parse('Sum(1/x, (x, 1, y))'), [y, 2, 10], '', { onlyIntegers: true });
  const parameterized = new p.LineOver1DRangeSeries(parse('Sum(a/x, (x, 1, y))'), [y, 2, 10], '', { onlyIntegers: true, params: new Map([[a, 1]]) });
  const expected = Array.from({ length: 9 }, (_, i) => Array.from({ length: i + 2 }, (_, k) => 1 / (k + 1)).reduce((a, b) => a + b, 0));
  numericEqual(sum.getData()[1], expected); numericEqual(parameterized.getData(), sum.getData());
});
it('describes discrete primitives, callable functions and complex ranges', () => {
  expect(new p.List2DSeries([1], [2]).toString()).toBe('2D list plot');
  expect(new p.GenericDataSeries('markers', [[1], [2]]).toString()).toBe('Generic data series');
  for (const im of [-1, 1]) expect(new p.LineOver1DRangeSeries(x, [x, { re: 0.5, im }, { re: 1.5, im }]).toString()).toContain(`${im}j`);
  expect(new p.LineOver1DRangeSeries(x, [x, 0.5, 1.5]).toString()).toContain('(0.5, 1.5)');
  expect(new p.LineOver1DRangeSeries((x) => x, [x, 0, 1], NoMatch).getLabel(true)).toBe('');
});
it('ports line/surface color setters, list colormaps and scalar sampling updates', () => {
  const line = new p.LineOver1DRangeSeries(x, [x, 0, 2], '', { n: 3, lineColor: (x) => x * x });
  expect(line.lineColor).toBe(NoMatch); expect(line.colorFunc).toBeTypeOf('function'); expect(line.toData().style.color).toEqual([0, 1, 4]);
  line.lineColor = x.mul(2); expect(line.toData().style.color).toEqual([0, 2, 4]); line.lineColor = 'blue'; expect(line.colorFunc).toBe(NoMatch); expect(line.toData().style.color).toBe('blue');
  const surface = new p.SurfaceOver2DRangeSeries(x.add(y), [x, 0, 1], [y, 0, 1], '', { n: 3, surfaceColor: x.add(y) }); expect(surface.surfaceColor).toBe(NoMatch); expect(surface.toData().style.color).toEqual([[0, 0.5, 1], [0.5, 1, 1.5], [1, 1.5, 2]]);
  surface.n = 5; expect(surface.n).toEqual([5, 3, 100]); surface.surfaceColor = 'red'; expect(surface.colorFunc).toBe(NoMatch);
  const list = new p.List2DSeries([0, 1], [1, 2], '', { useCm: true, colorFunc: (x) => x }); expect(list.isParametric).toBe(true); expect(list.getPoints()).toEqual([[0, 1], [1, 2]]);
  expect(() => new p.List2DSeries([0], [1], '', { useCm: true, colorFunc: x })).toThrow(TypeError);
  // A real-only optimization must not discard the imaginary part of sqrt(x)
  // before im() is applied; SymPy's NumPy backend returns zero in that case.
  const expr = parse('im(sqrt(x)*exp(-x**2))');
  const complex = new p.LineOver1DRangeSeries(expr, [x, -1, 1], '', { n: 3 });
  const hint = new p.LineOver1DRangeSeries(expr, [x, -1, 1], '', { n: 3, forceRealEval: true });
  numericEqual(hint.getData(), complex.getData()); expect(hint.getData()[1]![0]).toBeCloseTo(Math.exp(-1));
});
