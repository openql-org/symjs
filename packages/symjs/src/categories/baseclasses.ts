// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, categories/baseclasses.py, BSD-3-Clause; see LICENSE.

import type { Assumptions, Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Sym } from '../core/nodes';
import { callableClass } from '../core/callable';
import { Dict, DictNode, Tuple } from '../core/containers';
import { ExprMap } from '../core/exprmap';
import { at, cast, first, last } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import { EmptySet, FiniteSet, SetExpr, containsQ, finiteSet, union } from '../sets/sets';

/** SymPy categories.Object; the prefix avoids the JavaScript Object global. */
export class SymObject extends Sym {
  override get printName(): string { return `Object(${JSON.stringify(this.name)})`; }
  override get sortClass(): string { return 'Object'; }
  override get latexForm(): string { return this.name; }
  protected override computeKey(): string { return `Object(${super.computeKey()})`; }
}
export const categoryObject = (name: string, assumptions: Assumptions = {}): SymObject => new SymObject(name, assumptions);

/** A directed arrow. Construct an identity, named or composite morphism. */
export abstract class Morphism extends ExtensionExpr {
  constructor(head: string, args: readonly Expr[]) {
    super(head, args);
    if (new.target === Morphism) throw new NotImplementedError('Cannot instantiate Morphism; use a derived class.');
  }
  get domain(): Expr { return first(this.args); }
  get codomain(): Expr { return at(this.args, 1); }
  compose(other: Morphism): Morphism { return compositeMorphism([other, this]); }
  override mul(other: ExprLike): Morphism { return this.compose(cast(other, Morphism, 'composition requires a morphism')); }
  override get isScalar(): boolean { return false; }
  protected override computeCommutative(): boolean { return false; }
}

export class IdentityMorphismNode extends Morphism {
  constructor(domain: Expr) { super('IdentityMorphism', [domain]); }
  override get codomain(): Expr { return this.domain; }
  override printLatex(print: (e: Expr) => string): string { return `id:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
  withArgs(args: readonly Expr[]): Expr { return new IdentityMorphismNode(first(args)); }
}
export const IdentityMorphism = /* @__PURE__ */ callableClass(IdentityMorphismNode, (domain: Expr): IdentityMorphismNode => new IdentityMorphismNode(domain));
export type IdentityMorphism = IdentityMorphismNode;

export class NamedMorphismNode extends Morphism {
  constructor(domain: Expr, codomain: Expr, name: string) {
    if (!name) throw new RangeError('Empty morphism names are not allowed.');
    super(name, [domain, codomain]);
  }
  protected override computeKey(): string { return `NamedMorphism(${JSON.stringify(this.name)};${this.args.map((x) => x.key).join(';')})`; }
  withArgs(args: readonly Expr[]): Expr { return new NamedMorphismNode(first(args), at(args, 1), this.name); }
  override printStr(print: (e: Expr) => string): string { return `NamedMorphism(${print(this.domain)}, ${print(this.codomain)}, ${JSON.stringify(this.name)})`; }
  override printLatex(print: (e: Expr) => string): string { return `${this.name}:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
}
export const NamedMorphism = /* @__PURE__ */ callableClass(NamedMorphismNode, (domain: Expr, codomain: Expr, name: string): NamedMorphismNode => new NamedMorphismNode(domain, codomain, name));
export type NamedMorphism = NamedMorphismNode;

export class CompositeMorphismNode extends Morphism {
  constructor(readonly components: readonly Morphism[]) { super('CompositeMorphism', [Tuple(...components)]); }
  override get domain(): Expr { return first(this.components).domain; }
  override get codomain(): Expr { return last(this.components).codomain; }
  withArgs(args: readonly Expr[]): Expr { return compositeMorphism(first(args).args.map((m) => cast(m, Morphism))); }
  flatten(name: string): NamedMorphismNode { return new NamedMorphismNode(this.domain, this.codomain, name); }
  override printLatex(print: (e: Expr) => string): string { return `${[...this.components].reverse().map((m) => m.name).join('\\circ ')}:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
}

function compositeMorphism(components: readonly Morphism[]): Morphism {
  if (!components.length) throw new RangeError('A composite needs at least one morphism.');
  const normalized: Morphism[] = [];
  for (let i = 0; i < components.length; i++) {
    const m = cast(at(components, i), Morphism, 'All components must be morphisms.');
    if (i && !at(components, i - 1).codomain.equals(m.domain)) throw new RangeError('Uncomposable morphisms.');
    if (m instanceof CompositeMorphismNode) normalized.push(...m.components);
    else if (!(m instanceof IdentityMorphismNode)) normalized.push(m);
  }
  return normalized.length > 1 ? new CompositeMorphismNode(normalized) : first(normalized.length ? normalized : components);
}
export const CompositeMorphism = /* @__PURE__ */ callableClass(CompositeMorphismNode, (...components: Morphism[] | [readonly Morphism[]]): Morphism =>
  compositeMorphism(Array.isArray(components[0]) ? components[0] : components.map((m) => cast(m, Morphism))));
export type CompositeMorphism = CompositeMorphismNode;

/** The symbolic class of category objects (SymPy categories.baseclasses.Class). */
export class CategoryClass extends ExtensionExpr {
  readonly isProper = false;
  constructor(readonly objects: SetExpr) { super('Class', [objects]); }
  withArgs(args: readonly Expr[]): Expr { return new CategoryClass(cast(first(args), SetExpr)); }
}

export class CategoryNode extends ExtensionExpr {
  constructor(name: string, objects: SetExpr = EmptySet, readonly commutativeDiagrams: SetExpr = EmptySet) {
    if (!name) throw new RangeError('A Category cannot have an empty name.');
    super(name, [new CategoryClass(objects), commutativeDiagrams]);
  }
  get objects(): CategoryClass { return cast(first(this.args), CategoryClass); }
  protected override computeKey(): string { return `Category(${JSON.stringify(this.name)};${this.args.map((x) => x.key).join(';')})`; }
  withArgs(args: readonly Expr[]): Expr { return new CategoryNode(this.name, cast(first(args), CategoryClass).objects, cast(at(args, 1), SetExpr)); }
  override printStr(): string { return `Category(${JSON.stringify(this.name)})`; }
  override printLatex(): string { return `\\mathbf{${this.name}}`; }
  hom(_a: Expr, _b: Expr): never { throw new NotImplementedError('hom-sets are not implemented in Category, as in SymPy.'); }
  allMorphisms(): never { throw new NotImplementedError('Obtaining the class of morphisms is not implemented in Category, as in SymPy.'); }
}
export const Category = /* @__PURE__ */ callableClass(CategoryNode, (name: string, objects: SetExpr = EmptySet, diagrams: readonly DiagramNode[] = []): CategoryNode =>
  new CategoryNode(name, objects, finiteSet(...diagrams)));
export type Category = CategoryNode;

export type MorphismProperties = string | readonly (ExprLike | string)[] | SetExpr;
export type DiagramInput = readonly Morphism[] | ReadonlyMap<Morphism, MorphismProperties> | DictNode;
const properties = (value: MorphismProperties): SetExpr => value instanceof SetExpr ? value : finiteSet(...(typeof value === 'string' ? [value] : value).map((v) => typeof v === 'string' ? new Sym(v) : v));
const isMorphismList = (input: DiagramInput): input is readonly Morphism[] => Array.isArray(input);
function entries(input: DiagramInput): [Morphism, SetExpr][] {
  if (input instanceof DictNode) return input.items().map(([m, p]) => [cast(m, Morphism), p instanceof SetExpr ? p : finiteSet(p)]);
  if (isMorphismList(input)) return input.map((m) => [m, EmptySet]);
  return [...input].map(([m, p]) => [m, properties(p)]);
}

function addClosure(map: ExprMap<SetExpr>, m: Morphism, props: SetExpr, identities: boolean, components: boolean): void {
  const existing = map.get(m);
  map.set(m, existing ? union(existing, props) : props);
  if (existing) return;
  if (m instanceof IdentityMorphismNode) {
    if (!props.equals(EmptySet)) throw new RangeError('Identity morphisms cannot have properties.');
    return;
  }
  if (identities) {
    for (const o of [m.domain, m.codomain]) {
      const identity = new IdentityMorphismNode(o);
      map.set(identity, map.get(identity) ?? EmptySet);
    }
  }
  const put = (arrow: Morphism, p: SetExpr): void => { const previous = map.get(arrow); map.set(arrow, previous ? union(previous, p) : p); };
  for (const [e, p] of [...map]) {
    const other = cast(e, Morphism);
    const shared = finiteSet(...p.args.filter((x) => props.args.some((y) => x.equals(y))));
    if (m.domain.equals(other.codomain)) put(m.compose(other), shared);
    if (m.codomain.equals(other.domain)) put(other.compose(m), shared);
  }
  if (components && m instanceof CompositeMorphismNode) for (const component of m.components) addClosure(map, component, EmptySet, identities, true);
}

export class DiagramNode extends ExtensionExpr {
  readonly premises: DictNode;
  readonly conclusions: DictNode;
  readonly objects: SetExpr;
  constructor(premises: DiagramInput = [], conclusions: DiagramInput = []) {
    const p = new ExprMap<SetExpr>();
    const c = new ExprMap<SetExpr>();
    const objects: Expr[] = [];
    for (const [m, props] of entries(premises)) { objects.push(m.domain, m.codomain); addClosure(p, m, props, true, true); }
    const objectSet = finiteSet(...objects);
    for (const [m, props] of entries(conclusions)) if (containsQ(objectSet, m.domain) === true && containsQ(objectSet, m.codomain) === true) addClosure(c, m, props, false, false);
    const pd = Dict(p), cd = Dict(c);
    super('Diagram', [pd, cd, objectSet]);
    this.premises = pd; this.conclusions = cd; this.objects = objectSet;
  }
  withArgs(args: readonly Expr[]): Expr { return new DiagramNode(cast(first(args), DictNode), cast(at(args, 1), DictNode)); }
  override printLatex(print: (e: Expr) => string): string { return print(this.premises); }
  hom(a: Expr, b: Expr): [SetExpr, SetExpr] {
    const arrows = (d: DictNode): SetExpr => finiteSet(...d.items().map(([m]) => cast(m, Morphism)).filter((m) => m.domain.equals(a) && m.codomain.equals(b)));
    return [arrows(this.premises), arrows(this.conclusions)];
  }
  /** SymPy convention: whether the supplied diagram is contained in this one. */
  isSubdiagram(diagram: DiagramNode): boolean {
    const includes = (a: DictNode, b: DictNode): boolean => b.items().every(([m, props]) => a.containsKey(m) && a.get(m).equals(props));
    return includes(this.premises, diagram.premises) && includes(this.conclusions, diagram.conclusions);
  }
  subdiagramFromObjects(objects: SetExpr): DiagramNode {
    if (!(objects instanceof FiniteSet) && !objects.equals(EmptySet)) throw new RangeError('A subdiagram requires a finite set of objects.');
    if (objects.args.some((o) => containsQ(this.objects, o) !== true)) throw new RangeError('Supplied objects should all belong to the diagram.');
    const restrict = (d: DictNode): DictNode => Dict(d.items().filter(([m]) => { const f = cast(m, Morphism); return containsQ(objects, f.domain) === true && containsQ(objects, f.codomain) === true; }));
    return new DiagramNode(restrict(this.premises), restrict(this.conclusions));
  }
}
export const Diagram = /* @__PURE__ */ callableClass(DiagramNode, (premises: DiagramInput = [], conclusions: DiagramInput = []): DiagramNode => new DiagramNode(premises, conclusions));
export type Diagram = DiagramNode;
