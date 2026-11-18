// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/series.py (BSD-3-Clause).
import type { ComplexValue, ExprLike } from '../core/nodes';
import { Expr, Sym, Add, Mul, Pow, Fn, Rational, Rel, BoolAtom, S } from '../core/nodes';
import { at, first, last, cast, defined } from '../core/guard';
import { BoolOp } from '../core/boolalg';
import { TupleNode } from '../core/containers';
import { Concrete } from '../core/concrete';
import { NoMatch, NoMatchResult } from '../core/truth';
import { NotImplementedError } from '../core/errors';
import { sympify, sub, add, mul } from '../core/ops';
import { freeSymbols, subs, mapBottomUp, some } from '../core/traverse';
import { lambdify, toComplex } from '../numeric/evalf';
import { doit } from '../calculus/doit';
import { latex } from '../printing/latex';
import { FiniteSet, EmptySet, Interval, interval as setInterval } from '../sets/sets';
import type { SetExpr } from '../sets/sets';
import { singularities, solveset } from '../solvers/inequalities';
import { functionRange } from '../solvers/calculusutil';
import { interval } from './intervalmath/interval_arithmetic';
import { intervalMembership } from './intervalmath/interval_membership';
import * as li from './intervalmath/lib_interval';

export type NumericFunction = (...values: number[]) => number | ComplexValue;
export type PlotExpression = ExprLike | NumericFunction;
export type PlotBound = ExprLike | ComplexValue;
export type PlotRange = readonly [Sym, PlotBound, PlotBound];
export type PlotParameters = ReadonlyMap<Sym, PlotBound>;
export type NumericArray = number[] | number[][];
export type IntervalBox = [interval, interval];
export type SeriesValues = (NumericArray | IntervalBox[] | string)[];
export type JsonValue = string | number | boolean | JsonValue[] | { [key: string]: JsonValue };
export type RenderingOptions = Readonly<Record<string, JsonValue>>;
export type PlotScale = 'linear' | 'log';
export type SeriesKind = 'line' | 'parametric2d' | 'parametric3d' | 'surface' | 'parametricSurface' | 'contour' | 'implicit' | 'list' | 'generic';
export interface SeriesOptions {
  adaptive?: boolean; depth?: number; n?: number | readonly number[]; n1?: number; n2?: number; n3?: number;
  nbOfPoints?: number; nbOfPointsX?: number; nbOfPointsY?: number; nbOfPointsU?: number; nbOfPointsV?: number;
  xscale?: PlotScale; yscale?: PlotScale; zscale?: PlotScale; params?: PlotParameters;
  isPolar?: boolean; isPoint?: boolean; isFilled?: boolean; useCm?: boolean; showInLegend?: boolean;
  renderingKw?: RenderingOptions; contourKw?: RenderingOptions; clabels?: boolean;
  colorFunc?: PlotExpression; lineColor?: string | number | Expr | NumericFunction; surfaceColor?: string | number | Expr | NumericFunction;
  detectPoles?: boolean | 'symbolic'; eps?: number; exclude?: number | readonly number[];
  onlyIntegers?: boolean; steps?: boolean; unwrap?: boolean | { period?: number; discont?: number };
  return?: 'real' | 'imag' | 'abs' | 'arg';
  /** Backend optimization hint; symjs preserves analytic complex values in either mode. */
  forceRealEval?: boolean;
  tx?: (x: number) => number; ty?: (y: number) => number; tz?: (z: number) => number; tp?: (p: number) => number;
}
export interface SeriesDescription {
  kind: SeriesKind;
  label: string;
  coordinates: Record<string, JsonValue>;
  style: { isPoint: boolean; isFilled: boolean; useCm: boolean; showInLegend: boolean; renderingKw: RenderingOptions; color: JsonValue };
}
const isVector = (v: NumericArray): v is number[] => v.every((x) => typeof x === 'number');
const isComplex = (v: unknown): v is ComplexValue => typeof v === 'object' && v !== null && 're' in v && 'im' in v && typeof v.re === 'number' && typeof v.im === 'number';
const complex = (v: PlotBound): ComplexValue => isComplex(v) ? v : toComplex(v);
const real = (v: ComplexValue): number => Math.abs(v.im) <= 1e-8 ? v.re : NaN;
const expression = (v: PlotExpression): Expr | NumericFunction => typeof v === 'function' ? v : sympify(v);
const exprString = (e: Expr | NumericFunction): string => typeof e === 'function' ? '' : e.toString();
const checkedN = (n: number): number => { if (!Number.isInteger(n) || n < 2 || n > 1000000) throw new RangeError('Sampling count must be an integer between 2 and 1000000.'); return n; };
/** Encode NaN and infinities without JSON's lossy conversion to null. */
export function encodePlotData(value: unknown): JsonValue {
  if (typeof value === 'number') return Number.isFinite(value) ? (value === 0 ? 0 : value) : String(value);
  if (typeof value === 'string' || typeof value === 'boolean') return value;
  if (value instanceof interval) return [encodePlotData(value.start), encodePlotData(value.end)];
  if (Array.isArray(value)) return value.map(encodePlotData);
  if (value instanceof Expr) return value.toString();
  if (value instanceof Map) return [...value].map(([k, v]) => [encodePlotData(k), encodePlotData(v)]);
  if (typeof value === 'object' && value !== null) return Object.fromEntries(Object.entries(value).filter(([, v]) => v !== undefined && typeof v !== 'function').map(([k, v]) => [k, encodePlotData(v)]));
  throw new TypeError('Plot data must be serializable.');
}
/** Inclusive linear or geometric mesh; integer meshes contain all integers in the range. */
export function discretize(start: number, end: number, n: number, scale: PlotScale = 'linear', onlyIntegers = false): number[] {
  checkedN(n);
  if (!Number.isFinite(start) || !Number.isFinite(end)) throw new RangeError('Plot ranges must be finite.');
  if (onlyIntegers) { const a = Math.ceil(Math.min(start, end)), b = Math.floor(Math.max(start, end)); const xs = Array.from({ length: Math.max(0, b - a + 1) }, (_, i) => a + i); return start > end ? xs.reverse() : xs; }
  if (scale === 'log' && (start === 0 || end === 0 || Math.sign(start) !== Math.sign(end))) throw new RangeError('Logarithmic endpoints must have the same nonzero sign.');
  return Array.from({ length: n }, (_, i) => i === 0 ? start : i === n - 1 ? end : scale === 'log' ? Math.sign(start) * Math.exp(Math.log(Math.abs(start)) + i / (n - 1) * Math.log(Math.abs(end / start))) : start + i / (n - 1) * (end - start));
}

/** Common numeric sampling and metadata for renderer-independent series. */
export abstract class BaseSeries {
  abstract readonly kind: SeriesKind;
  readonly expressions: (Expr | NumericFunction)[];
  ranges: PlotRange[];
  params: PlotParameters;
  renderingKw: RenderingOptions;
  protected options: SeriesOptions;
  private counts: number[];
  private labelValue: string;
  private automaticLabel: boolean;
  adaptive: boolean;
  depth: number;
  xscale: PlotScale;
  yscale: PlotScale;
  zscale: PlotScale;
  isPolar: boolean;
  isPoint: boolean;
  isFilled: boolean;
  useCm: boolean;
  showInLegend: boolean;
  colorFunc: PlotExpression | NoMatchResult;
  private lineColorValue: string | number | NoMatchResult = NoMatch;
  private surfaceColorValue: string | number | NoMatchResult = NoMatch;
  constructor(exprs: readonly PlotExpression[], ranges: readonly PlotRange[], label: string | NoMatchResult = '', options: SeriesOptions = {}, defaultN = 100) {
    this.expressions = exprs.map(expression); this.ranges = [...ranges]; this.options = options;
    this.params = options.params ?? new Map(); this.renderingKw = options.renderingKw ?? {};
    this.counts = [defaultN, defaultN, defaultN]; if (options.n !== undefined) this.n = typeof options.n === 'number' ? Array<number>(Math.max(1, ranges.length)).fill(options.n) : options.n;
    this.counts[0] = checkedN(options.n1 ?? options.nbOfPoints ?? options.nbOfPointsX ?? options.nbOfPointsU ?? first(this.counts));
    this.counts[1] = checkedN(options.n2 ?? options.nbOfPointsY ?? options.nbOfPointsV ?? at(this.counts, 1));
    this.counts[2] = checkedN(options.n3 ?? at(this.counts, 2));
    this.adaptive = options.adaptive ?? false; this.depth = options.depth ?? 12;
    if (!Number.isInteger(this.depth) || this.depth < 0 || this.depth > 20) throw new RangeError('Adaptive depth must be an integer from 0 to 20.');
    this.xscale = options.xscale ?? 'linear'; this.yscale = options.yscale ?? 'linear'; this.zscale = options.zscale ?? 'linear';
    this.isPolar = options.isPolar ?? false; this.isPoint = options.isPoint ?? false; this.isFilled = options.isFilled ?? true; this.useCm = options.useCm ?? false; this.showInLegend = options.showInLegend ?? true;
    this.colorFunc = options.colorFunc ?? NoMatch; this.lineColor = options.lineColor ?? NoMatch; this.surfaceColor = options.surfaceColor ?? NoMatch;
    this.automaticLabel = label instanceof NoMatchResult; this.labelValue = typeof label === 'string' ? label : '';
    this.validateSymbols();
  }
  get n(): number[] { return [...this.counts]; }
  set n(value: number | readonly number[]) { const ns = typeof value === 'number' ? [value] : [...value]; if (!ns.length || ns.length > 3) throw new RangeError('n requires one to three counts.'); ns.forEach((n, i) => { this.counts[i] = checkedN(n); }); }
  get lineColor(): string | number | NoMatchResult { return this.lineColorValue; }
  set lineColor(value: string | number | Expr | NumericFunction | NoMatchResult) {
    if (typeof value === 'function' || value instanceof Expr) { this.colorFunc = value; this.lineColorValue = NoMatch; }
    else { this.lineColorValue = value; if (!(value instanceof NoMatchResult)) this.colorFunc = NoMatch; }
  }
  get surfaceColor(): string | number | NoMatchResult { return this.surfaceColorValue; }
  set surfaceColor(value: string | number | Expr | NumericFunction | NoMatchResult) {
    if (typeof value === 'function' || value instanceof Expr) { this.colorFunc = value; this.surfaceColorValue = NoMatch; }
    else { this.surfaceColorValue = value; if (!(value instanceof NoMatchResult)) this.colorFunc = NoMatch; }
  }
  get expr(): Expr | NumericFunction | readonly (Expr | NumericFunction)[] { return this.expressions.length === 1 ? first(this.expressions) : this.expressions; }
  get label(): string { return this.getLabel(); }
  set label(value: string) { this.labelValue = value; this.automaticLabel = false; }
  get isInteractive(): boolean { return this.params.size > 0; }
  get is2Dline(): boolean { return ['line', 'parametric2d', 'list'].includes(this.kind); }
  get is3Dline(): boolean { return this.kind === 'parametric3d'; }
  get is3Dsurface(): boolean { return this.kind === 'surface' || this.kind === 'parametricSurface'; }
  get isContour(): boolean { return this.kind === 'contour'; }
  get isImplicit(): boolean { return this.kind === 'implicit'; }
  get isParametric(): boolean { return ['parametric2d', 'parametric3d', 'parametricSurface'].includes(this.kind) || this.kind === 'list' && this.useCm && !(this.colorFunc instanceof NoMatchResult); }
  get isGeneric(): boolean { return this.kind === 'generic'; }
  getLabel(useLatex = false, wrapper = '$%s$'): string {
    if (!this.automaticLabel) return this.labelValue;
    const exprs = this.isParametric && this.useCm && this.ranges.length === 1 ? [first(this.ranges)[0]] : this.expressions;
    if (!exprs.every((e): e is Expr => e instanceof Expr)) return '';
    const values = exprs.map((e) => useLatex ? latex(e) : e.toString());
    const text = values.length === 1 ? first(values) : useLatex ? latex(new TupleNode(exprs)) : `(${values.join(', ')})`;
    return useLatex ? wrapper.replace('%s', text) : text;
  }
  protected validateSymbols(): void {
    const allowed = new Set([...this.ranges.map((r) => r[0].key), ...[...this.params.keys()].map((s) => s.key)]);
    if (new Set(this.ranges.map((r) => r[0].key)).size !== this.ranges.length) throw new RangeError('Multiple ranges use the same symbol.');
    for (const e of this.expressions) if (e instanceof Expr) for (const s of freeSymbols(e)) if (!allowed.has(s.key)) throw new RangeError(`Unknown plotting symbol ${s.toString()}.`);
    for (const [, a, b] of this.ranges) for (const v of [a, b]) if (v instanceof Expr) for (const s of freeSymbols(v)) if (![...this.params.keys()].some((p) => p.equals(s))) throw new RangeError(`Unknown symbol in plotting range: ${s.toString()}.`);
  }
  protected bound(value: PlotBound): ComplexValue {
    if (value instanceof Expr && freeSymbols(value).size) return lambdify(value, [...this.params.keys()])(...[...this.params.values()].map(complex));
    return complex(value);
  }
  protected bounds(index: number): [ComplexValue, ComplexValue] { const r = at(this.ranges, index); return [this.bound(r[1]), this.bound(r[2])]; }
  protected mesh(index: number): number[] { const [a, b] = this.bounds(index); if (a.im !== b.im) throw new RangeError('Range endpoints must have equal imaginary parts.'); return discretize(a.re, b.re, at(this.counts, index), at([this.xscale, this.yscale, this.zscale], index), this.options.onlyIntegers); }
  protected evaluator(e: Expr | NumericFunction): (...values: number[]) => ComplexValue {
    if (e instanceof Expr && some(e, (node) => node instanceof Concrete)) return (...values) => {
      const env = new Map([...this.params].map(([s, v]): [Sym, ComplexValue] => [s, complex(v)]));
      this.ranges.forEach(([s], i) => env.set(s, { re: at(values, i), im: this.bounds(i)[0].im }));
      return toComplex(doit(subs(e, new Map([...env].map(([s, z]) => [s, add(z.re, mul(z.im, S.I))])))));
    };
    const params = [...this.params], fn = typeof e === 'function' ? undefined : lambdify(mapBottomUp(e, (node) => node instanceof Fn && node.name === 'frac' ? sub(first(node.args), new Fn('floor', node.args)) : node), [...this.ranges.map((r) => r[0]), ...params.map(([s]) => s)]);
    const shifts = this.ranges.map((_, i) => this.bounds(i)[0].im), parameterValues = params.map(([, v]) => complex(v));
    return (...values) => {
      try {
        const v = typeof e === 'function' ? e(...values) : defined(fn)(...values.map((x, i) => ({ re: x, im: at(shifts, i) })), ...parameterValues);
        const result = typeof v === 'number' ? { re: v, im: 0 } : v;
        return result;
      } catch (error) { if (error instanceof RangeError) { if (e instanceof Fn && e.name === 'log' && e.args.length === 1) { const z = this.evaluator(first(e.args))(...values); if (z.re === 0 && z.im === 0) return { re: -Infinity, im: 0 }; } return { re: NaN, im: NaN }; } throw error; }
    };
  }
  protected project(v: ComplexValue): number {
    switch (this.options.return) { case 'real': return v.re; case 'imag': return v.im; case 'abs': return Math.hypot(v.re, v.im); case 'arg': return Math.atan2(v.im, v.re); default: return real(v); }
  }
  protected transform(data: number[][]): number[][];
  protected transform(data: number[][][]): number[][][];
  protected transform(data: NumericArray[]): NumericArray[] { return data.map((values, i) => { const f = at([this.options.tx, this.options.ty, this.kind === 'parametric2d' ? this.options.tp : this.options.tz, this.options.tp, this.options.tp], i); if (!f) return values; return isVector(values) ? values.map(f) : values.map((row) => row.map(f)); }); }
  abstract getData(): SeriesValues;
  toString(): string {
    if (this.kind === 'list') return '2D list plot';
    if (this.kind === 'generic') return 'Generic data series';
    const prefixes = { line: 'cartesian line', parametric2d: 'parametric cartesian line', parametric3d: '3D parametric cartesian line', surface: 'cartesian surface', parametricSurface: 'parametric cartesian surface', contour: 'contour', implicit: 'Implicit expression' };
    const boundText = (value: PlotBound): string => {
      if (value instanceof Expr && freeSymbols(value).size) return value.toString();
      const z = complex(value);
      return z.im ? `${z.re}${z.im < 0 ? '' : '+'}${z.im}j` : Number.isInteger(z.re) ? z.re.toFixed(1) : String(z.re);
    };
    let value = this.expressions.map(exprString).join(', ');
    if (this.expressions.length > 1) value = `(${value})`;
    if (this.kind === 'line' && this.options.return) value = `${this.options.return === 'real' ? 're' : this.options.return === 'imag' ? 'im' : this.options.return}(${value})`;
    const ranges = this.ranges.map(([s, a, b]) => `${s.toString()} over (${boundText(a)}, ${boundText(b)})`).join(' and ');
    const parameters = [...this.params.keys()].map(String);
    return `${this.isInteractive ? 'interactive ' : ''}${prefixes[this.kind]}: ${value} for ${ranges}${parameters.length ? ` and parameters (${parameters.join(', ')}${parameters.length === 1 ? ',' : ''})` : ''}`;
  }
  toData(): SeriesDescription {
    const data = this.getData();
    const parameterName = this.colorFunc instanceof NoMatchResult ? 'parameter' : 'color';
    const names = this.kind === 'implicit' && data.length === 2 ? ['boxes', 'mode'] : this.kind === 'implicit' ? ['x', 'y', 'z', 'mode'] : this.kind === 'parametricSurface' ? ['x', 'y', 'z', 'u', 'v'] : this.kind === 'parametric3d' ? ['x', 'y', 'z', parameterName] : this.kind === 'parametric2d' ? ['x', 'y', parameterName] : ['x', 'y', 'z'];
    let color: JsonValue = '';
    const c = this.is3Dsurface ? this.surfaceColor : this.lineColor;
    if (typeof c === 'string' || typeof c === 'number') color = encodePlotData(c);
    if (!(this.colorFunc instanceof NoMatchResult)) color = encodePlotData(this instanceof ParametricLineBaseSeries || this instanceof List2DSeries && this.useCm ? last(data) : this.evalColorFunc(...data.filter((a): a is NumericArray => Array.isArray(a) && (a.length === 0 || typeof a[0] === 'number' || Array.isArray(a[0]) && (a[0].length === 0 || typeof a[0][0] === 'number')))));
    return { kind: this.kind, label: this.getLabel(), coordinates: Object.fromEntries(data.map((v, i) => [names[i] ?? `data${i}`, encodePlotData(v)])), style: { isPoint: this.isPoint, isFilled: this.isFilled, useCm: this.useCm, showInLegend: this.showInLegend, renderingKw: this.renderingKw, color } };
  }
  evalColorFunc(...data: number[][]): number[];
  evalColorFunc(...data: number[][][]): number[][];
  evalColorFunc(...data: NumericArray[]): NumericArray;
  evalColorFunc(...data: NumericArray[]): NumericArray {
    const input = this.colorFunc;
    if (input instanceof NoMatchResult) return this.isParametric && this.ranges.length === 1 ? data[data.length - 1] ?? [] : data[2] ?? data[1] ?? [];
    const fn = typeof input === 'function' ? input : this.evaluator(sympify(input));
    const useParams = typeof input === 'function' && this.isParametric && input.length <= this.ranges.length;
    const arrays = useParams ? data.slice(-this.ranges.length) : data;
    const evaluate = (values: number[]): number => {
      const args = typeof input === 'function' ? values.slice(0, input.length || values.length) : this.isParametric ? values.slice(-this.ranges.length) : values.slice(0, this.ranges.length);
      const c = fn(...args); return typeof c === 'number' ? c : real(c);
    };
    const template = first(arrays);
    const point = (i: number, j = 0): number[] => arrays.map((a) => isVector(a) ? at(a, i) : at(at(a, i), j));
    return isVector(template) ? template.map((_, i) => evaluate(point(i))) : template.map((row, i) => row.map((_, j) => evaluate(point(i, j))));
  }
}

/** Line sampling, exclusions, discontinuities and coordinate transforms. */
export abstract class Line2DBaseSeries extends BaseSeries {
  polesLocations: number[] = [];
  get var(): Sym | NoMatchResult { return this.ranges[0]?.[0] ?? NoMatch; }
  get start(): ComplexValue | NoMatchResult { return this.ranges.length ? this.bounds(0)[0] : NoMatch; }
  get end(): ComplexValue | NoMatchResult { return this.ranges.length ? this.bounds(0)[1] : NoMatch; }
  get nbOfPoints(): number { return first(this.n); }
  set nbOfPoints(n: number) { this.n = n; }
  protected abstract sample(): number[][];
  protected colorData(data: number[][]): number[][] { return data; }
  protected pointAt(_t: number): number[] { throw new NotImplementedError('This series has no continuous parameter.'); }
  getData(): number[][] {
    let data = this.sample();
    if (this.kind === 'line' && this.options.detectPoles === 'symbolic') {
      const expr = first(this.expressions);
      if (typeof expr === 'function') throw new TypeError('Symbolic pole detection requires a symbolic expression.');
      const parameters = new Map([...this.params].map(([s, v]) => { const z = complex(v); return [s, add(z.re, mul(z.im, S.I))]; }));
      const e = subs(expr, parameters), x = first(this.ranges)[0], [a, b] = this.bounds(0), domain = setInterval(Math.min(a.re, b.re), Math.max(a.re, b.re));
      const points = new Set<number>();
      const collect = (solutions: SetExpr): void => {
        if (solutions === EmptySet) return;
        if (!(solutions instanceof FiniteSet)) throw new NotImplementedError('Cannot enumerate symbolic discontinuities in this range.');
        for (const p of solutions.args) points.add(real(toComplex(p)));
      };
      collect(singularities(e, x, domain));
      const visit = (node: Expr): void => {
        if (node instanceof Fn && ['frac', 'floor', 'ceiling'].includes(node.name)) {
          const argument = first(node.args), values = functionRange(argument, x, domain);
          if (!(values instanceof Interval)) throw new NotImplementedError('Cannot bound step discontinuities in this range.');
          const low = Math.ceil(real(toComplex(values.start))), high = Math.floor(real(toComplex(values.end)));
          if (high - low > 1000000) throw new RangeError('Too many symbolic discontinuities.');
          for (let k = low; k <= high; k++) collect(solveset(sub(argument, k), x, domain));
        }
        node.args.forEach(visit);
      };
      visit(e);
      this.polesLocations = [...points].sort((a, b) => a - b).map((p) => this.options.tx ? this.options.tx(p) : p);
    }
    const excludes = this.options.exclude === undefined ? [] : typeof this.options.exclude === 'number' ? [this.options.exclude] : [...this.options.exclude];
    const parameter = this.isParametric ? data.length - 1 : 0;
    for (const e of excludes.sort((a, b) => a - b)) {
      const axis = at(data, parameter), direction = first(axis) > last(axis) ? -1 : 1, i = axis.findIndex((v) => direction * v >= direction * e);
      if (i <= 0 || i >= axis.length) continue;
      const delta = Math.min(Math.abs(e - at(axis, i - 1)), Math.abs(e - at(axis, i))) / 100 || Math.abs(at(axis, i) - at(axis, i - 1)) / 100;
      const before = this.pointAt(e - direction * delta), after = this.pointAt(e + direction * delta), count = at(axis, i) === e ? 1 : 0;
      data.forEach((values, k) => values.splice(i, count, at(before, k), k === parameter ? e : NaN, at(after, k)));
    }
    data = this.transform(this.colorData(data));
    if (this.options.detectPoles !== undefined && this.options.detectPoles !== false && this.is2Dline) {
      const x = first(data), y = at(data, 1), original = [...y];
      for (let i = 1; i < y.length; i++) if (Math.atan(Math.abs((at(original, i) - at(original, i - 1)) / (at(x, i) - at(x, i - 1)))) >= Math.PI / 2 - (this.options.eps ?? 0.01)) y[i] = NaN;
    }
    if (this.options.unwrap !== undefined && this.options.unwrap !== false && this.is2Dline) {
      const y = at(data, 1), opts = this.options.unwrap === true ? {} : this.options.unwrap, period = opts.period ?? 2 * Math.PI, discont = Math.max(opts.discont ?? period / 2, period / 2); let offset = 0;
      for (let i = 1; i < y.length; i++) { const delta = at(y, i) - (at(y, i - 1) - offset); if (Math.abs(delta) > discont) offset -= Math.round(delta / period) * period; y[i] = at(y, i) + offset; }
    }
    // Repeat the parameter/color channel with the step vertices so connectors
    // receive aligned arrays; SymPy leaves this channel at its original length.
    if (this.options.steps) data = data.map((a, k) => { const repeated = a.flatMap((v) => Array<number>(this.is3Dline ? 3 : 2).fill(v)); return this.is3Dline ? repeated.slice(k === 0 ? 2 : k === 2 ? 1 : 0, repeated.length - (k === 0 ? 0 : k === 2 ? 1 : 2)) : k === 0 ? repeated.slice(1) : repeated.slice(0, -1); });
    return data;
  }
  getPoints(): number[][] { const data = this.getData(); return this.isParametric ? data.slice(0, -1) : data; }
  getColorArray(): NumericArray {
    const data = this.getData().map(centersOfSegments);
    if (this.isParametric && !(this.colorFunc instanceof NoMatchResult)) return last(data);
    if (typeof this.lineColor === 'number') return first(data).map(() => Number(this.lineColor));
    return this.evalColorFunc(...data);
  }
}
function adaptiveMesh(start: number, end: number, evaluate: (t: number) => number[], depth: number, logarithmic: boolean): number[] {
  const output = [start];
  const refine = (a: number, b: number, pa: number[], pb: number[], level: number): void => {
    const middle = logarithmic ? Math.sign(a) * Math.sqrt(a * b) : (a + b) / 2, pm = evaluate(middle);
    const finite = [...pa, ...pb, ...pm].every(Number.isFinite);
    const deviation = Math.max(...pm.map((v, i) => Math.abs(v - (at(pa, i) + at(pb, i)) / 2) / (1 + Math.abs(v))));
    if (level < Math.min(6, depth) || level < depth && (!finite || deviation > 0.001)) { refine(a, middle, pa, pm, level + 1); refine(middle, b, pm, pb, level + 1); } else output.push(b);
  };
  refine(start, end, evaluate(start), evaluate(end), 0); return output;
}
/** Cartesian line; complex values are masked unless a real/imag/abs/arg projection is requested. */
export class LineOver1DRangeSeries extends Line2DBaseSeries {
  readonly kind = 'line';
  constructor(expr: PlotExpression, range: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([expr], [range], label, options, 1000); this.bounds(0); if (this.bounds(0)[0].im !== this.bounds(0)[1].im) throw new RangeError('Range endpoints must have equal imaginary parts.'); if (options.return) this.adaptive = false; }
  protected override pointAt(t: number): number[] { return [t, this.project(this.evaluator(first(this.expressions))(t))]; }
  protected sample(): number[][] { const f = this.evaluator(first(this.expressions)); const evaluate = (t: number): number[] => [t, this.project(f(t))]; const [a, b] = this.bounds(0); const xs = this.adaptive && !this.options.onlyIntegers ? adaptiveMesh(a.re, b.re, evaluate, this.depth, this.xscale === 'log') : this.mesh(0); return [xs, xs.map((x) => this.project(f(x)))]; }
}
export abstract class ParametricLineBaseSeries extends Line2DBaseSeries {
  protected override pointAt(t: number): number[] { return [...this.expressions.map((e) => real(this.evaluator(e)(t))), t]; }
  protected sample(): number[][] {
    const fs = this.expressions.map((e) => this.evaluator(e)), point = (t: number): number[] => fs.map((f) => real(f(t))), [a, b] = this.bounds(0);
    const ts = this.adaptive && !this.options.onlyIntegers ? adaptiveMesh(a.re, b.re, point, this.depth, this.xscale === 'log') : this.mesh(0);
    const data = [...fs.map((f) => ts.map((t) => real(f(t)))), ts];
    if (this.is2Dline && this.isPolar) { const x = first(data), y = at(data, 1); data[0] = x.map((v, i) => Math.atan2(at(y, i), v)); data[1] = x.map((v, i) => Math.hypot(v, at(y, i))); }
    return data;
  }
  protected override colorData(data: number[][]): number[][] { if (!(this.colorFunc instanceof NoMatchResult)) data[data.length - 1] = this.evalColorFunc(...data); return data; }
  getParameterPoints(): number[] { return last(this.getData()); }
}
export class Parametric2DLineSeries extends ParametricLineBaseSeries {
  readonly kind = 'parametric2d';
  constructor(x: PlotExpression, y: PlotExpression, range: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([x, y], [range], label, { ...options, useCm: options.useCm ?? true }, 1000); }
}
export abstract class Line3DBaseSeries extends ParametricLineBaseSeries {}
export class Parametric3DLineSeries extends Line3DBaseSeries {
  readonly kind = 'parametric3d';
  constructor(x: PlotExpression, y: PlotExpression, z: PlotExpression, range: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([x, y, z], [range], label, { ...options, useCm: options.useCm ?? true }, 1000); }
}
export class List2DSeries extends Line2DBaseSeries {
  readonly kind = 'list';
  constructor(readonly listX: readonly PlotBound[], readonly listY: readonly PlotBound[], label: string | NoMatchResult = '', options: SeriesOptions = {}) {
    super([], [], label, options, 1000);
    if (!Array.isArray(listX) || !Array.isArray(listY)) throw new TypeError('List series require coordinate arrays.');
    if (listX.length !== listY.length) throw new RangeError('Coordinate lists must have equal length.');
    const allowed = new Set([...this.params.keys()].map((s) => s.key));
    for (const value of [...listX, ...listY]) if (value instanceof Expr) for (const s of freeSymbols(value)) if (!allowed.has(s.key)) throw new RangeError(`Unknown plotting symbol ${s.toString()}.`);
    if (this.useCm && this.colorFunc instanceof Expr) throw new TypeError('List series require a numeric callback for the color function.');
  }
  protected sample(): number[][] { const data = [this.listX.map((v) => real(this.bound(v))), this.listY.map((v) => real(this.bound(v)))]; if (this.useCm && !(this.colorFunc instanceof NoMatchResult)) { const colors = this.evalColorFunc(...data); data.push(colors); } return data; }
}
export abstract class SurfaceBaseSeries extends BaseSeries {
  protected meshData(): number[][][] {
    const xs = this.mesh(0), ys = this.mesh(1), X = ys.map(() => [...xs]), Y = ys.map((y) => xs.map(() => y));
    const values = this.expressions.map((e) => { const f = this.evaluator(e); return ys.map((y) => xs.map((x) => real(f(x, y)))); });
    return [X, Y, ...values];
  }
  getMeshes(): number[][][] { return this.getData().slice(0, 3); }
  abstract override getData(): number[][][];
  getColorArray(): NumericArray { const data = this.getData().map(centersOfFaces); if (typeof this.surfaceColor === 'number') return first(data).map((row) => row.map(() => Number(this.surfaceColor))); return this.evalColorFunc(...data); }
  get varX(): Sym { return first(this.ranges)[0]; }
  get varY(): Sym { return at(this.ranges, 1)[0]; }
  get startX(): number { return this.bounds(0)[0].re; }
  get endX(): number { return this.bounds(0)[1].re; }
  get startY(): number { return this.bounds(1)[0].re; }
  get endY(): number { return this.bounds(1)[1].re; }
  get nbOfPointsX(): number { return first(this.n); }
  set nbOfPointsX(n: number) { this.n = [n, at(this.n, 1)]; }
  get nbOfPointsY(): number { return at(this.n, 1); }
  set nbOfPointsY(n: number) { this.n = [first(this.n), n]; }
  protected transformed(data: number[][][]): number[][][] { return this.transform(data); }
}
export class SurfaceOver2DRangeSeries extends SurfaceBaseSeries {
  readonly kind: SeriesKind = 'surface';
  constructor(expr: PlotExpression, x: PlotRange, y: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([expr], [x, y], label, options); }
  getData(): number[][][] { const data = this.meshData(); if (this.isPolar && this.is3Dsurface) { const r = first(data), theta = at(data, 1); data[0] = r.map((row, i) => row.map((v, j) => v * Math.cos(at(at(theta, i), j)))); data[1] = r.map((row, i) => row.map((v, j) => v * Math.sin(at(at(theta, i), j)))); } return this.transformed(data); }
}
export class ParametricSurfaceSeries extends SurfaceBaseSeries {
  readonly kind = 'parametricSurface';
  constructor(x: PlotExpression, y: PlotExpression, z: PlotExpression, u: PlotRange, v: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([x, y, z], [u, v], label, options); }
  getData(): number[][][] { const data = this.meshData(); return this.transformed([...data.slice(2), ...data.slice(0, 2)]); }
  getParameterMeshes(): number[][][] { return this.getData().slice(3); }
  get varU(): Sym { return this.varX; } get varV(): Sym { return this.varY; }
  get startU(): number { return this.startX; } get endU(): number { return this.endX; }
  get startV(): number { return this.startY; } get endV(): number { return this.endY; }
  get nbOfPointsU(): number { return this.nbOfPointsX; } set nbOfPointsU(n: number) { this.nbOfPointsX = n; }
  get nbOfPointsV(): number { return this.nbOfPointsY; } set nbOfPointsV(n: number) { this.nbOfPointsY = n; }
}
export class ContourSeries extends SurfaceOver2DRangeSeries {
  override readonly kind = 'contour';
  readonly showClabels: boolean;
  constructor(expr: PlotExpression, x: PlotRange, y: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super(expr, x, y, label, { ...options, renderingKw: options.contourKw ?? options.renderingKw }); this.showClabels = options.clabels ?? true; }
}
export class GenericDataSeries extends BaseSeries {
  readonly kind = 'generic';
  constructor(readonly type: string, readonly args: NumericArray[], renderingKw: RenderingOptions = {}) { super([], [], '', { renderingKw }); }
  getData(): NumericArray[] { return this.args; }
  override toData(): SeriesDescription { const data = super.toData(); data.coordinates['type'] = this.type; return data; }
}
/** Evaluate an expression as an enclosure, without Python code generation. */
export function intervalEvaluate(e: Expr, values: ReadonlyMap<string, interval>): interval | intervalMembership {
  if (e instanceof Sym) { const v = values.get(e.key); if (!v) throw new RangeError(`Missing interval for ${e.name}.`); return v; }
  if (e instanceof BoolAtom) return new intervalMembership(e.value, true);
  if (e instanceof Rel) { const a = cast(intervalEvaluate(e.lhs, values), interval), b = cast(intervalEvaluate(e.rhs, values), interval); switch (e.op) { case 'Eq': return a.eq(b); case 'Ne': return a.ne(b); case 'Lt': return a.lt(b); case 'Le': return a.le(b); case 'Gt': return a.gt(b); case 'Ge': return a.ge(b); } }
  if (e instanceof BoolOp) { const args = e.args.map((a) => cast(intervalEvaluate(a, values), intervalMembership)); if (e.op === 'Not') return first(args).not(); if (e.op === 'ITE') return first(args).and(at(args, 1)).or(first(args).not().and(at(args, 2))); return args.slice(1).reduce((a, b) => e.op === 'And' ? a.and(b) : e.op === 'Or' ? a.or(b) : a.xor(b), first(args)); }
  if (e instanceof Add) return e.args.reduce((a, b) => a.add(cast(intervalEvaluate(b, values), interval)), new interval(0));
  if (e instanceof Mul) return e.args.reduce((a, b) => a.mul(cast(intervalEvaluate(b, values), interval)), new interval(1));
  if (e instanceof Pow) return cast(intervalEvaluate(e.base, values), interval).pow(e.exp instanceof Rational ? e.exp.value : cast(intervalEvaluate(e.exp, values), interval));
  if (e instanceof Fn) { const f = Reflect.get(li, e.name); if (typeof f !== 'function') throw new NotImplementedError(`Interval function ${e.name} is not implemented.`); const v: unknown = Reflect.apply(f, li, e.args.map((a) => cast(intervalEvaluate(a, values), interval))); return cast(v, interval); }
  return new interval(real(toComplex(e)));
}
export class ImplicitSeries extends BaseSeries {
  readonly kind = 'implicit';
  readonly hasEquality: boolean;
  constructor(expr: Expr, x: PlotRange, y: PlotRange, label: string | NoMatchResult = '', options: SeriesOptions = {}) { super([expr], [x, y], label, { ...options, depth: 4 + Math.min(4, Math.max(0, options.depth ?? 0)) }); const hasEquality = (e: Expr): boolean => e instanceof BoolOp ? e.args.some(hasEquality) : e instanceof Rel ? e.op === 'Eq' || e.op === 'Ge' || e.op === 'Le' : true; this.hasEquality = hasEquality(expr); }
  getData(): SeriesValues {
    const e = cast(first(this.expressions), Expr);
    if (this.adaptive || e instanceof BoolOp) {
      const [a, b] = this.bounds(0), [c, d] = this.bounds(1), boxes: IntervalBox[] = [], env = new Map([...this.params].map(([s, v]) => [s.key, new interval(real(complex(v)))]));
      const visit = (x: interval, y: interval, depth: number): void => {
        env.set(first(this.ranges)[0].key, x); env.set(at(this.ranges, 1)[0].key, y);
        const value = intervalEvaluate(e, env), predicate = value instanceof interval ? value.eq(0) : value;
        if (predicate.isValid === false || predicate.value === false) return;
        if (predicate.value === true && predicate.isValid === true || depth === 0 && predicate.isValid === true && this.hasEquality) { boxes.push([x, y]); return; }
        if (!depth) return;
        for (const xx of [new interval(x.start, x.mid), new interval(x.mid, x.end)]) for (const yy of [new interval(y.start, y.mid), new interval(y.mid, y.end)]) visit(xx, yy, depth - 1);
      };
      try { visit(new interval(a.re, b.re), new interval(c.re, d.re), this.depth); return [boxes, 'fill']; }
      catch (error) { if (!(error instanceof NotImplementedError) || e instanceof BoolOp) throw error; }
    }
    const equality = !(e instanceof Rel) || e.op === 'Eq';
    const expr = e instanceof Rel ? e.op === 'Lt' || e.op === 'Le' ? sub(e.rhs, e.lhs) : sub(e.lhs, e.rhs) : e;
    const f = this.evaluator(expr), xs = this.mesh(0), ys = this.mesh(1);
    return [ys.map(() => [...xs]), ys.map((y) => xs.map(() => y)), ys.map((y) => xs.map((x) => real(f(x, y)))), equality ? 'contour' : 'contourf'];
  }
}
export const centersOfSegments = (array: readonly number[]): number[] => array.slice(1).map((v, i) => (v + at(array, i)) / 2);
export const centersOfFaces = (array: readonly (readonly number[])[]): number[][] => array.slice(1).map((row, i) => row.slice(1).map((v, j) => (v + at(row, j) + at(at(array, i), j) + at(at(array, i), j + 1)) / 4));
export function flat(x: readonly number[], y: readonly number[], z: readonly number[], eps = 1e-3): boolean { const a = y.map((v, i) => v - at(x, i)), b = z.map((v, i) => v - at(y, i)); const norm = Math.hypot(...a) * Math.hypot(...b); return norm === 0 || Math.abs(a.reduce((s, v, i) => s + v * at(b, i), 0) / norm - 1) < eps; }
