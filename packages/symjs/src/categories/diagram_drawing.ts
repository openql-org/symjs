// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 categories/diagram_drawing.py (BSD-3-Clause).

import { Expr, Sym } from '../core/nodes';
import { at, cast, first, getOrThrow } from '../core/guard';
import { NoMatch, NoMatchResult } from '../core/truth';
import { ExprMap } from '../core/exprmap';
import { PrettyPrinter } from '../printing/pretty/pretty';
import { PrettyForm } from '../printing/pretty/stringpict';
import { latex } from '../printing/latex';
import { compareValues } from '../utilities/values';
import { EmptySet, FiniteSet, SetExpr, finiteSet } from '../sets/sets';
import { CompositeMorphismNode, Diagram, IdentityMorphism, IdentityMorphismNode, Morphism, NamedMorphism } from './baseclasses';

type Point = readonly [number, number];
type Edge = readonly [Point, Point];
type Triangle = readonly [Expr, Expr, Expr];
type Skeleton = Map<string, Morphism[]>;
type Cell = Expr | NoMatchResult;

/** A rectangular mutable grid. Empty cells are NoMatch. @internal */
export class GrowableGrid<T = Expr> {
  private rows: (T | NoMatchResult)[][];
  constructor(private columns: number, height: number) {
    if (!Number.isInteger(columns) || !Number.isInteger(height) || columns < 0 || height < 0) throw new RangeError('Grid dimensions must be nonnegative integers.');
    this.rows = Array.from({ length: height }, () => Array<T | NoMatchResult>(columns).fill(NoMatch));
  }
  get width(): number { return this.columns; }
  get height(): number { return this.rows.length; }
  get(i: number, j: number): T | NoMatchResult { return at(at(this.rows, i), j); }
  set(i: number, j: number, value: T | NoMatchResult): void { at(this.rows, i); this.get(i, j); at(this.rows, i)[j] = value; }
  appendRow(): void { this.rows.push(Array<T | NoMatchResult>(this.width).fill(NoMatch)); }
  prependRow(): void { this.rows.unshift(Array<T | NoMatchResult>(this.width).fill(NoMatch)); }
  appendColumn(): void { this.columns++; for (const row of this.rows) row.push(NoMatch); }
  prependColumn(): void { this.columns++; for (const row of this.rows) row.unshift(NoMatch); }
}

/** Layout hints understood by DiagramGrid. */
export interface DiagramHints { layout?: 'sequential'; transpose?: boolean; }
export type DiagramGroup = Expr | readonly Expr[];
export type DiagramGroups = SetExpr | readonly DiagramGroup[] | ReadonlyMap<DiagramGroup, DiagramHints>;
export interface DiagramGridOptions extends DiagramHints { groups?: DiagramGroups; }

const eq = (a: Expr, b: Expr): boolean => a.equals(b);
const edgeKey = (a: Expr, b: Expr): string => JSON.stringify([a.key, b.key].sort());
const edgesOf = (t: Triangle): [Expr, Expr][] => [[t[0], t[1]], [t[0], t[2]], [t[1], t[2]]];
const hasEdge = (t: Triangle, a: Expr, b: Expr): boolean => t.some((o) => eq(o, a)) && t.some((o) => eq(o, b));
const empty = (g: GrowableGrid, p: Point): boolean => p[0] < 0 || p[1] < 0 || p[0] >= g.height || p[1] >= g.width || g.get(...p) instanceof NoMatchResult;
const shift = (p: Point, offset: Point): Point => [p[0] + offset[0], p[1] + offset[1]];

function put(g: GrowableGrid, p: Point, o: Expr, fringe: Edge[]): Point {
  const offset: Point = [p[0] === -1 ? 1 : 0, p[1] === -1 ? 1 : 0];
  if (p[0] === -1) g.prependRow(); else if (p[0] === g.height) g.appendRow();
  if (p[1] === -1) g.prependColumn(); else if (p[1] === g.width) g.appendColumn();
  for (let k = 0; k < fringe.length; k++) { const [a, b] = at(fringe, k); fringe[k] = [shift(a, offset), shift(b, offset)]; }
  const target = shift(p, offset); g.set(...target, o);
  return offset;
}

function choose(p: Point, q: Point, edge: Edge, o: Expr, skeleton: Skeleton, g: GrowableGrid): Point | NoMatchResult {
  if (empty(g, p) && empty(g, q)) return skeleton.get(edgeKey(cast(g.get(...edge[0]), Expr), o))?.length ? p : q;
  if (empty(g, p)) return p;
  return empty(g, q) ? q : NoMatch;
}

function weld(t: Triangle, edge: Edge, fringe: Edge[], g: GrowableGrid, skeleton: Skeleton): boolean {
  const [a, b] = edge;
  const o = first(t.filter((v) => !eq(v, cast(g.get(...a), Expr)) && !eq(v, cast(g.get(...b), Expr))));
  let p: Point | NoMatchResult;
  if (a[0] !== b[0] && a[1] !== b[1]) {
    const corners: Point[] = [[a[0], b[1]], [b[0], a[1]]];
    p = corners.find((corner) => empty(g, corner)) ?? NoMatch;
  } else if (a[0] === b[0]) {
    p = choose([a[0] + 1, a[1]], [a[0] + 1, b[1]], edge, o, skeleton, g);
    if (p instanceof NoMatchResult) p = choose([a[0] - 1, a[1]], [a[0] - 1, b[1]], edge, o, skeleton, g);
  } else {
    p = choose([a[0], a[1] + 1], [b[0], a[1] + 1], edge, o, skeleton, g);
    if (p instanceof NoMatchResult) p = choose([a[0], a[1] - 1], [b[0], a[1] - 1], edge, o, skeleton, g);
  }
  if (p instanceof NoMatchResult) { fringe.splice(fringe.indexOf(edge), 1); return false; }
  const offset = put(g, p, o, fringe), target = shift(p, offset);
  fringe.push([shift(a, offset), target], [shift(b, offset), target]);
  return true;
}

function joinGrids(grids: readonly GrowableGrid[]): GrowableGrid {
  const result = new GrowableGrid(grids.reduce((n, g) => n + g.width, 0), Math.max(0, ...grids.map((g) => g.height)));
  let column = 0;
  for (const g of grids) { for (let i = 0; i < g.height; i++) for (let j = 0; j < g.width; j++) result.set(i, column + j, g.get(i, j)); column += g.width; }
  return result;
}

function genericLayout(diagram: Diagram, morphisms: readonly Morphism[]): GrowableGrid {
  const objects = [...diagram.objects.args].sort(compareValues);
  const g = new GrowableGrid(Math.min(2, objects.length), objects.length ? 1 : 0);
  if (!objects.length) return g;
  g.set(0, 0, first(objects));
  if (objects.length === 1) return g;
  g.set(0, 1, at(objects, 1));
  if (objects.length === 2) return g;
  const skeleton: Skeleton = new Map();
  for (const m of morphisms) { const k = edgeKey(m.domain, m.codomain); skeleton.set(k, [...(skeleton.get(k) ?? []), m]); }
  const realEdges = new Set(skeleton.keys());
  for (const a of objects) for (const b of objects) if (!eq(a, b) && objects.some((o) => realEdges.has(edgeKey(a, o)) && realEdges.has(edgeKey(o, b)))) {
    const key = edgeKey(a, b); if (!skeleton.has(key)) skeleton.set(key, []);
  }
  let triangles: Triangle[] = [];
  for (let i = 0; i < objects.length; i++) for (let j = i + 1; j < objects.length; j++) for (let k = j + 1; k < objects.length; k++) {
    const t: Triangle = [at(objects, i), at(objects, j), at(objects, k)], keys = edgesOf(t).map(([a, b]) => edgeKey(a, b));
    if (keys.every((e) => skeleton.has(e)) && keys.filter((e) => realEdges.has(e)).length >= 2) triangles.push(t);
  }
  const size = (t: Triangle): number => edgesOf(t).reduce((n, [a, b]) => n + Math.max(0, ...getOrThrow(skeleton, edgeKey(a, b)).map((m) => m instanceof CompositeMorphismNode ? m.components.length : 1)), 0);
  triangles.sort((a, b) => size(a) - size(b) || compareValues(a, b));
  const root = first(edgesOf(first(triangles)).filter(([a, b]) => realEdges.has(edgeKey(a, b))).sort(compareValues));
  g.set(0, 0, root[0]); g.set(0, 1, root[1]);
  const placed = new Set(root.map((o) => o.key)), fringe: Edge[] = [[[0, 0], [0, 1]]];
  while (placed.size !== objects.length) {
    let found = false;
    for (const t of triangles) {
      const edge = fringe.find(([a, b]) => hasEdge(t, cast(g.get(...a), Expr), cast(g.get(...b), Expr)));
      if (edge) { if (weld(t, edge, fringe, g, skeleton)) for (const o of t) placed.add(o.key); found = true; break; }
    }
    if (!found) {
      outer: for (let i = 0; i < g.height; i++) for (let j = 0; j < g.width; j++) {
        const o = g.get(i, j); if (!(o instanceof Expr)) continue;
        const t = triangles.find((tri) => tri.some((v) => eq(v, o)) && tri.every((v) => eq(v, o) || !placed.has(v.key)));
        if (!t) continue;
        const edge = first(edgesOf(t).filter(([a, b]) => realEdges.has(edgeKey(a, b)) && (eq(a, o) || eq(b, o))).sort(compareValues));
        const other = eq(edge[0], o) ? edge[1] : edge[0];
        const neighbours: Point[] = [[i - 1, j], [i, j + 1], [i + 1, j], [i, j - 1], [i - 1, j - 1], [i - 1, j + 1], [i + 1, j - 1], [i + 1, j + 1]];
        const p = neighbours.find((pt) => empty(g, pt));
        if (p) { const offset = put(g, p, other, fringe); fringe.push([shift([i, j], offset), shift(p, offset)]); placed.add(other.key); found = true; break outer; }
      }
      // Copy rows by height and columns by width; SymPy interchanges them here.
      if (!found) return joinGrids([g, new DiagramGrid(diagram.subdiagramFromObjects(finiteSet(...objects.filter((o) => !placed.has(o.key))))).grid]);
    }
    triangles = triangles.filter((t) => !t.every((o) => placed.has(o.key)));
  }
  return g;
}

function adjacency(objects: readonly Expr[], morphisms: readonly Morphism[]): ExprMap<Expr[]> {
  const result = new ExprMap<Expr[]>(objects.map((o) => [o, []]));
  for (const m of morphisms) { getOrThrow(result, m.domain).push(m.codomain); getOrThrow(result, m.codomain).push(m.domain); }
  for (const neighbours of result.values()) neighbours.sort(compareValues);
  return result;
}

function sequentialLayout(diagram: Diagram, morphisms: readonly Morphism[]): GrowableGrid {
  const objects = [...diagram.objects.args].sort(compareValues);
  if (!objects.length) return new GrowableGrid(0, 0);
  const adj = adjacency(objects, morphisms);
  const root = first(objects.sort((a, b) => getOrThrow(adj, a).length - getOrThrow(adj, b).length));
  const g = new GrowableGrid(1, 1), placed = new Set([root.key]); g.set(0, 0, root);
  const visit = (p: Point): void => {
    let i = p[0]; const j = p[1] + 1;
    for (const o of getOrThrow(adj, cast(g.get(...p), Expr))) if (!placed.has(o.key)) { put(g, [i, j], o, []); placed.add(o.key); visit([i, j]); i++; }
  };
  visit([0, 0]); return g;
}

function groupLayout(diagram: Diagram, groups: DiagramGroups, morphisms: readonly Morphism[], hints: DiagramHints): GrowableGrid {
  const isGroupList = (g: DiagramGroups): g is readonly DiagramGroup[] => Array.isArray(g);
  const rows: [DiagramGroup, DiagramHints][] = groups instanceof SetExpr ? groups.args.map((g) => [g, hints]) : isGroupList(groups) ? groups.map((g: DiagramGroup) => [g, hints]) : [...groups];
  const groupOf = new ExprMap<Expr>(), grids = new ExprMap<GrowableGrid>();
  for (const [input, local] of rows) {
    const group = input instanceof Expr ? input : finiteSet(...input);
    if (group instanceof FiniteSet) { for (const o of group.args) groupOf.set(o, group); grids.set(group, new DiagramGrid(diagram.subdiagramFromObjects(group), local).grid); }
    else groupOf.set(group, group);
  }
  for (const o of diagram.objects.args) if (!groupOf.has(o)) groupOf.set(o, o);
  const arrows: Morphism[] = morphisms.flatMap((m) => { const a = getOrThrow(groupOf, m.domain), b = getOrThrow(groupOf, m.codomain); return eq(a, b) ? [] : [NamedMorphism(a, b, 'dummy')]; });
  for (const group of new Set(groupOf.values())) arrows.push(IdentityMorphism(group));
  const top = new DiagramGrid(Diagram(arrows));
  const localGrid = (cell: Cell): GrowableGrid | undefined => cell instanceof Expr ? grids.get(cell) : undefined;
  const heights = Array.from({ length: top.height }, (_, i) => Math.max(1, ...Array.from({ length: top.width }, (_, j) => localGrid(top.get(i, j))?.height ?? 1)));
  const widths = Array.from({ length: top.width }, (_, j) => Math.max(1, ...Array.from({ length: top.height }, (_, i) => localGrid(top.get(i, j))?.width ?? 1)));
  const result = new GrowableGrid(widths.reduce((a, b) => a + b, 0), heights.reduce((a, b) => a + b, 0));
  let row = 0;
  for (let i = 0; i < top.height; i++) {
    let column = 0;
    for (let j = 0; j < top.width; j++) { const cell = top.get(i, j), g = localGrid(cell); if (g) { for (let r = 0; r < g.height; r++) for (let c = 0; c < g.width; c++) result.set(row + r, column + c, g.get(r, c)); } else result.set(row, column, cell); column += at(widths, j); }
    row += at(heights, i);
  }
  return result;
}

/** Deterministic grid layout of a category diagram, with optional groups and hints. */
export class DiagramGrid {
  readonly morphisms: ExprMap<SetExpr>;
  /** Mutable cells support explicit placement before drawing. */
  readonly grid: GrowableGrid;
  constructor(diagram: Diagram, options: DiagramGridOptions = {}) {
    this.morphisms = new ExprMap();
    for (const dict of [diagram.premises, diagram.conclusions]) for (const [arrow, properties] of dict.items()) {
      const m = cast(arrow, Morphism), props = cast(properties, SetExpr);
      if (!(m instanceof IdentityMorphismNode) && (!(m instanceof CompositeMorphismNode) || !props.equals(EmptySet))) this.morphisms.set(m, props);
    }
    const all = [...this.morphisms.keys()].map((m) => cast(m, Morphism)), arrows = all.filter((m) => !eq(m.domain, m.codomain));
    const adj = adjacency(diagram.objects.args, all), visited = new Set<string>(), components: Diagram[] = [];
    for (const object of adj.keys()) if (!visited.has(object.key)) {
      const objects: Expr[] = [];
      const visit = (o: Expr): void => { if (visited.has(o.key)) return; visited.add(o.key); objects.push(o); for (const n of getOrThrow(adj, o)) visit(n); };
      visit(object);
      const members = new Set(objects.map((o) => o.key));
      const premises = new Map<Morphism, SetExpr>([...this.morphisms].filter(([m]) => members.has(cast(m, Morphism).domain.key)).map(([m, p]) => [cast(m, Morphism), p]));
      if (objects.length === 1) premises.set(IdentityMorphism(first(objects)), EmptySet);
      components.push(Diagram(premises));
    }
    let g: GrowableGrid;
    if (options.groups && (!(options.groups instanceof SetExpr) || !options.groups.equals(diagram.objects))) g = groupLayout(diagram, options.groups, arrows, { layout: options.layout, transpose: options.transpose });
    else if (components.length > 1) g = joinGrids(components.sort(compareValues).map((d) => new DiagramGrid(d, options).grid));
    else g = options.layout === 'sequential' ? sequentialLayout(diagram, arrows) : genericLayout(diagram, arrows);
    if (options.transpose) { const transposed = new GrowableGrid(g.height, g.width); for (let i = 0; i < g.height; i++) for (let j = 0; j < g.width; j++) transposed.set(j, i, g.get(i, j)); g = transposed; }
    this.grid = g;
  }
  get width(): number { return this.grid.width; }
  get height(): number { return this.grid.height; }
  get(i: number, j: number): Cell { return this.grid.get(i, j); }
  /** Matrix-style pretty form without enclosing brackets. */
  toPretty(): string {
    const printer = new PrettyPrinter();
    const cells = Array.from({ length: this.height }, (_, i) => Array.from({ length: this.width }, (_, j) => { const c = this.get(i, j); return printer.print(c instanceof Expr ? new Sym(c instanceof Sym ? c.name : c.toString()) : ' '); }));
    const widths = Array.from({ length: this.width }, (_, j) => Math.max(...cells.map((r) => at(r, j).width())));
    let result = new PrettyForm('');
    for (let i = 0; i < this.height; i++) {
      let row = new PrettyForm('');
      for (let j = 0; j < this.width; j++) { const c = at(at(cells, i), j), pad = at(widths, j) - c.width(); const cell = PrettyForm.of(c.left(' '.repeat(Math.floor(pad / 2)))); row = PrettyForm.of(row.right(j ? '  ' : '', cell, ' '.repeat(Math.ceil(pad / 2)))); }
      result = i ? PrettyForm.of(result.below(' ', row)) : row;
    }
    return result.picture.join('\n');
  }
  toString(): string { return '[' + Array.from({ length: this.height }, (_, i) => '[' + Array.from({ length: this.width }, (_, j) => { const c = this.get(i, j); return c instanceof Expr ? c.toString() : 'None'; }).join(', ') + ']').join(', ') + ']'; }
}

/** Mutable Xy-pic arrow description supplied to property formatters. */
export class ArrowStringDescription {
  labelDisplacement = '';
  arrowStyle = '';
  forcedLabelPosition = false;
  constructor(public unit: string, public curving: string, public curvingAmount: number | NoMatchResult, public loopingStart: string, public loopingEnd: string, public horizontalDirection: string, public verticalDirection: string, public labelPosition: string, public label: string) {}
  toString(): string {
    const curve = this.curving ? `@/${this.curving}${String(this.curvingAmount)}${this.unit}/` : '';
    const loop = this.loopingStart && this.loopingEnd ? `@(${this.loopingStart},${this.loopingEnd})` : '';
    return `\\ar${curve}${loop}${this.arrowStyle ? '@' + this.arrowStyle : ''}[${this.horizontalDirection}${this.verticalDirection}]${this.labelPosition}${this.labelDisplacement}{${this.label}}`;
  }
}

export type ArrowFormatter = (arrow: ArrowStringDescription) => void;
export interface XypicDrawOptions { masked?: readonly Morphism[]; diagramFormat?: string; }
export interface XypicDiagramOptions extends XypicDrawOptions, DiagramGridOptions {}
type ArrowInfo = Map<Morphism, ArrowStringDescription>;
type Coordinates = ExprMap<Point>;
const direction = (n: number, positive: string, negative: string): string => (n > 0 ? positive : negative).repeat(Math.abs(n));
const loopDirections: [string, string][] = [['r', 'u'], ['u', 'l'], ['l', 'd'], ['d', 'r']];

function loopPosition(o: Expr, p: Point, infos: ArrowInfo, coords: Coordinates): [string, string] {
  const counts = [0, 0, 0, 0];
  const bump = (k: number): void => { counts[k] = at(counts, k) + 1; };
  for (const [m, info] of infos) {
    if (eq(m.domain, o) && eq(m.codomain, o)) { const k = loopDirections.findIndex(([a, b]) => a === info.loopingStart && b === info.loopingEnd); if (k >= 0) bump(k); continue; }
    const outgoing = eq(m.domain, o);
    if (!outgoing && !eq(m.codomain, o)) continue;
    const end = getOrThrow(coords, outgoing ? m.codomain : m.domain), di = end[0] - p[0], dj = end[1] - p[1];
    if (di && dj) { bump(di > 0 ? (dj > 0 ? 0 : 1) : (dj < 0 ? 2 : 3)); continue; }
    let upper: number, lower: number;
    if (!di) { [upper, lower] = dj > 0 ? (outgoing ? [0, 3] : [3, 0]) : (outgoing ? [2, 1] : [1, 2]); }
    else { [upper, lower] = di < 0 ? (outgoing ? [1, 0] : [0, 1]) : (outgoing ? [3, 2] : [2, 3]); }
    if (!info.curving || info.curving === '^') bump(upper);
    if (!info.curving || info.curving === '_') bump(lower);
  }
  return at(loopDirections, counts.indexOf(Math.min(...counts)));
}

function longArrow(p: Point, q: Point, g: DiagramGrid, infos: ArrowInfo, coords: Coordinates): string {
  const horizontal = p[0] === q[0], axis = horizontal ? 1 : 0, fixed = horizontal ? 0 : 1;
  let negative = 0, positive = 0; const straight: Morphism[] = [];
  for (let k = Math.min(p[axis], q[axis]) + 1; k < Math.max(p[axis], q[axis]); k++) {
    const o = horizontal ? g.get(p[0], k) : g.get(k, p[1]); if (!(o instanceof Expr)) continue;
    for (const [m, info] of infos) {
      let end: Point;
      if (eq(m.domain, o)) end = getOrThrow(coords, m.codomain);
      else if (eq(m.codomain, o)) end = getOrThrow(coords, m.domain);
      else continue;
      if (end[fixed] < p[fixed]) negative++; else if (end[fixed] > p[fixed]) positive++; else if (!info.curving) straight.push(m);
    }
  }
  const before = negative < positive, backwards = q[axis] < p[axis];
  const curve = (before !== backwards) === horizontal ? '^' : '_';
  for (const m of straight) { const info = getOrThrow(infos, m), forward = getOrThrow(coords, m.domain)[axis] < getOrThrow(coords, m.codomain)[axis]; info.labelPosition = (forward === before) === horizontal ? '_' : '^'; info.forcedLabelPosition = true; }
  return curve;
}

function freeSpace(p: Point, q: Point, g: DiagramGrid): [boolean, boolean, boolean, string, string] {
  if (p[0] === q[0]) {
    const columns = Array.from({ length: Math.abs(q[1] - p[1]) + 1 }, (_, k) => Math.min(p[1], q[1]) + k);
    // Match SymPy's label placement convention, including its occupied upper row rule.
    const up = p[0] === 0 || columns.every((j) => g.get(p[0] - 1, j) instanceof Expr);
    const down = p[0] === g.height - 1 || columns.every((j) => !(g.get(p[0] + 1, j) instanceof Expr));
    return [up, down, p[1] > q[1], '^', '_'];
  }
  if (p[1] === q[1]) {
    const rows = Array.from({ length: Math.abs(q[0] - p[0]) + 1 }, (_, k) => Math.min(p[0], q[0]) + k);
    return [p[1] === 0 || rows.every((i) => !(g.get(i, p[1] - 1) instanceof Expr)), p[1] === g.width - 1 || rows.every((i) => !(g.get(i, p[1] + 1) instanceof Expr)), p[0] > q[0], '_', '^'];
  }
  const [a, b] = p[0] < q[0] ? [p, q] : [q, p], slope = Math.abs((b[0] - a[0]) / (b[1] - a[1]));
  let up = true, down = true;
  for (let i = a[0]; i <= b[0]; i++) for (let j = Math.min(a[1], b[1]); j <= Math.max(a[1], b[1]); j++) {
    if (i === a[0] && j === a[1] || !(g.get(i, j) instanceof Expr)) continue;
    const angle = j === a[1] ? Infinity : Math.abs((i - a[0]) / (j - a[1]));
    if (angle > slope) down = false; else if (angle < slope) up = false;
  }
  return [up, down, p[1] > q[1], '^', '_'];
}

/** Generate Xy-pic text without invoking TeX or a rendering backend. */
export class XypicDiagramDrawer {
  unit = 'mm';
  defaultCurvingAmount = 3;
  defaultCurvingStep = 4;
  arrowFormatters = new Map<string, ArrowFormatter>();
  defaultArrowFormatter: ArrowFormatter | NoMatchResult = NoMatch;
  draw(_diagram: Diagram, grid: DiagramGrid, options: XypicDrawOptions = {}): string {
    const coords = new ExprMap<Point>();
    for (let i = 0; i < grid.height; i++) for (let j = 0; j < grid.width; j++) { const o = grid.get(i, j); if (o instanceof Expr) coords.set(o, [i, j]); }
    const morphisms = [...grid.morphisms.keys()].map((m) => cast(m, Morphism)).filter((m) => !options.masked?.some((v) => eq(m, v)));
    const order = (m: Morphism): [number, number, string, unknown] => {
      const a = getOrThrow(coords, m.domain), b = getOrThrow(coords, m.codomain);
      const kind = eq(m.domain, m.codomain) ? 3 : a[0] === b[0] || a[1] === b[1] ? 1 : 2;
      return [kind, kind === 1 ? Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]) : 0, m instanceof CompositeMorphismNode ? 'CompositeMorphism' : 'NamedMorphism', m instanceof CompositeMorphismNode ? m.components : [m.domain, m.codomain, m.name]];
    };
    morphisms.sort((a, b) => compareValues(order(a), order(b)));
    const infos: ArrowInfo = new Map();
    for (const m of morphisms) {
      const p = getOrThrow(coords, m.domain), q = getOrThrow(coords, m.codomain), di = q[0] - p[0], dj = q[1] - p[1];
      let curve = '', start = '', end = '', position = '^';
      if (!di && !dj) [start, end] = loopPosition(m.domain, p, infos, coords);
      else if (!di && Math.abs(dj) > 1 || !dj && Math.abs(di) > 1) { curve = longArrow(p, q, grid, infos, coords); position = curve; }
      const count = [...infos.keys()].filter((a) => edgeKey(a.domain, a.codomain) === edgeKey(m.domain, m.codomain)).length;
      let amount = 0;
      if (curve) amount = this.defaultCurvingAmount + count * this.defaultCurvingStep;
      else if (count) { curve = '^'; amount = this.defaultCurvingAmount + [...infos].filter(([a, info]) => eq(a.domain, m.domain) && eq(a.codomain, m.codomain) && info.curving === '^').length * this.defaultCurvingStep; }
      const label = m instanceof CompositeMorphismNode ? [...m.components].reverse().map((v) => latex(new Sym(v.name))).join('\\circ ') : latex(new Sym(m.name));
      const info = new ArrowStringDescription(this.unit, curve, amount, start, end, direction(dj, 'r', 'l'), direction(di, 'd', 'u'), position, label);
      if (typeof this.defaultArrowFormatter === 'function') this.defaultArrowFormatter(info);
      for (const property of getOrThrow(grid.morphisms, m).args) if (property instanceof Sym) this.arrowFormatters.get(property.name)?.(info);
      infos.set(m, info);
    }
    for (const [m, info] of infos) if (!info.curving && !info.forcedLabelPosition && !eq(m.domain, m.codomain)) {
      const [free1, free2, backwards, pos1, pos2] = freeSpace(getOrThrow(coords, m.domain), getOrThrow(coords, m.codomain), grid);
      if (free1 !== free2) info.labelPosition = free1 !== backwards ? pos1 : pos2;
    }
    let result = `\\xymatrix${options.diagramFormat ?? ''}{\n`;
    for (let i = 0; i < grid.height; i++) {
      for (let j = 0; j < grid.width; j++) {
        const o = grid.get(i, j);
        if (o instanceof Expr) { result += (o instanceof Sym ? latex(new Sym(o.name)) : latex(o)) + ' '; for (const m of morphisms) if (eq(m.domain, o)) result += getOrThrow(infos, m).toString() + ' '; }
        if (j < grid.width - 1) result += '& ';
      }
      if (i < grid.height - 1) result += '\\\\';
      result += '\n';
    }
    return result + '}\n';
  }
}

/** Lay out a diagram and return its Xy-pic source. */
export function xypicDrawDiagram(diagram: Diagram, options: XypicDiagramOptions = {}): string {
  return new XypicDiagramDrawer().draw(diagram, new DiagramGrid(diagram, options), options);
}
