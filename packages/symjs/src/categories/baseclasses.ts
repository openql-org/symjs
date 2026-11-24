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

/**
 * A named object of an abstract category.
 *
 * @see SymPy `sympy.categories.baseclasses.Object`
 */
export class SymObject extends Sym {
  /**
   * Supplies the name the printer displays for this expression.
   *
   * @returns The display name.
   */
  override get printName(): string { return `Object(${JSON.stringify(this.name)})`; }
  /**
   * Identifies the class used to sort this expression.
   *
   * @returns The ordering class name.
   */
  override get sortClass(): string { return 'Object'; }
  protected override computeKey(): string { return `Object(${super.computeKey()})`; }
}
/**
 * Creates a named object of an abstract category.
 *
 * @param name - Symbolic name.
 * @param assumptions - Assumptions to attach to the symbol.
 * @returns The named category object.
 * @see SymPy `sympy.categories.baseclasses.Object`
 */
export const categoryObject = (name: string, assumptions: Assumptions = {}): SymObject => new SymObject(name, assumptions);

/**
 * A directed arrow. Construct an identity, named or composite morphism.
 *
 * @see SymPy `sympy.categories.baseclasses.Morphism`
 */
export abstract class Morphism extends ExtensionExpr {
  /**
   * Constructs an instance of `Morphism`.
   *
   * @param head - Name of the morphism expression.
   * @param args - Operands in their defining order.
   * @throws NotImplementedError when the abstract morphism class is instantiated directly.
   */
  constructor(head: string, args: readonly Expr[]) {
    super(head, args);
    if (new.target === Morphism) throw new NotImplementedError('Cannot instantiate Morphism; use a derived class.');
  }
  /**
   * Identifies the object at which the arrow starts.
   *
   * @returns The source object.
   * @see SymPy `sympy.categories.baseclasses.Morphism.domain`
   */
  get domain(): Expr { return first(this.args); }
  /**
   * Identifies the object at which the arrow ends.
   *
   * @returns The target object.
   * @see SymPy `sympy.categories.baseclasses.Morphism.codomain`
   */
  get codomain(): Expr { return at(this.args, 1); }
  /**
   * Composes this morphism after the supplied morphism.
   *
   * @param other - Arrow applied first in the composition.
   * @returns The composite morphism, with the source of `other` and target of this morphism.
   * @throws RangeError when the codomain of the supplied arrow differs from this arrow’s domain.
   * @see SymPy `sympy.categories.baseclasses.Morphism.compose`
   * @example
   * ```ts
   * import { NamedMorphism, categoryObject } from '@symjs/symjs';
   *
   * const a = categoryObject('A'), b = categoryObject('B'), c = categoryObject('C');
   * const f = NamedMorphism(a, b, 'f'), g = NamedMorphism(b, c, 'g');
   * g.compose(f).domain.equals(a); // => True
   * g.compose(f).codomain.equals(c); // => True
   * ```
   */
  compose(other: Morphism): Morphism { return compositeMorphism([other, this]); }
  /**
   * Composes this arrow after the given arrow.
   *
   * @param other - Arrow applied first in the composition.
   * @returns The resulting morphism.
   * @throws RangeError when the arrows have incompatible endpoints.
   * @see SymPy `sympy.categories.baseclasses.Morphism.__mul__`
   */
  override mul(other: ExprLike): Morphism { return this.compose(cast(other, Morphism, 'composition requires a morphism')); }
  /**
   * Indicates whether the expression represents a scalar.
   *
   * @returns The scalar flag.
   */
  override get isScalar(): boolean { return false; }
  protected override computeCommutative(): boolean { return false; }
}

/**
 * The identity arrow from an object to itself.
 *
 * @see SymPy `sympy.categories.baseclasses.IdentityMorphism`
 */
export class IdentityMorphismNode extends Morphism {
  /**
   * Constructs an instance of `IdentityMorphismNode`.
   *
   * @param domain - Object at the source of the arrow.
   */
  constructor(domain: Expr) { super('IdentityMorphism', [domain]); }
  /**
   * Identifies the object at which the arrow ends.
   *
   * @returns The target object.
   * @see SymPy `sympy.categories.baseclasses.IdentityMorphism.codomain`
   */
  override get codomain(): Expr { return this.domain; }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return `id:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new IdentityMorphismNode(first(args)); }
}
/**
 * Constructs the identity arrow of the supplied object.
 *
 * @param domain - Object at the source of the arrow.
 * @returns The resulting `IdentityMorphism` expression.
 * @see SymPy `sympy.categories.baseclasses.IdentityMorphism`
 * @example
 * ```ts
 * import { IdentityMorphism, NamedMorphism, categoryObject } from '@symjs/symjs';
 *
 * const A = categoryObject('A'), B = categoryObject('B');
 * const f = NamedMorphism(A, B, 'f');
 * f.compose(IdentityMorphism(A)).equals(f); // => True
 * ```
 */
export const IdentityMorphism = /* @__PURE__ */ callableClass(IdentityMorphismNode, (domain: Expr): IdentityMorphismNode => new IdentityMorphismNode(domain));
export type IdentityMorphism = IdentityMorphismNode;

/**
 * A named arrow from its domain to its codomain.
 *
 * @see SymPy `sympy.categories.baseclasses.NamedMorphism`
 */
export class NamedMorphismNode extends Morphism {
  /**
   * Constructs an instance of `NamedMorphismNode`.
   *
   * @param domain - Object at the source of the arrow.
   * @param codomain - Object at the target of the arrow.
   * @param name - Symbolic name.
   * @throws RangeError when the morphism name is empty.
   */
  constructor(domain: Expr, codomain: Expr, name: string) {
    if (!name) throw new RangeError('Empty morphism names are not allowed.');
    super(name, [domain, codomain]);
  }
  protected override computeKey(): string { return `NamedMorphism(${JSON.stringify(this.name)};${this.args.map((x) => x.key).join(';')})`; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new NamedMorphismNode(first(args), at(args, 1), this.name); }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string { return `NamedMorphism(${print(this.domain)}, ${print(this.codomain)}, ${JSON.stringify(this.name)})`; }
  /**
   * Formats the morphism name as a symbol followed by its arrow.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return `${print(new Sym(this.name))}:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
}
/**
 * Constructs a named arrow between the supplied objects.
 *
 * @param domain - Object at the source of the arrow.
 * @param codomain - Object at the target of the arrow.
 * @param name - Symbolic name.
 * @returns The resulting `NamedMorphism` expression.
 * @throws RangeError when the morphism name is empty.
 * @see SymPy `sympy.categories.baseclasses.NamedMorphism`
 * @example
 * ```ts
 * import { NamedMorphism, categoryObject } from '@symjs/symjs';
 *
 * const A = categoryObject('A'), B = categoryObject('B');
 * const f = NamedMorphism(A, B, 'f');
 * f.name; // => f
 * ```
 */
export const NamedMorphism = /* @__PURE__ */ callableClass(NamedMorphismNode, (domain: Expr, codomain: Expr, name: string): NamedMorphismNode => new NamedMorphismNode(domain, codomain, name));
export type NamedMorphism = NamedMorphismNode;

/**
 * A composition of arrows in the order in which they act.
 *
 * @see SymPy `sympy.categories.baseclasses.CompositeMorphism`
 */
export class CompositeMorphismNode extends Morphism {
  /**
   * Constructs an instance of `CompositeMorphismNode`.
   *
   * @param components - Arrows listed in the order of composition.
   */
  constructor(
    /**
     * Returns the components of this composite morphism.
     *
     * @see SymPy `sympy.categories.baseclasses.CompositeMorphism.components`
     */
    readonly components: readonly Morphism[]) { super('CompositeMorphism', [Tuple(...components)]); }
  /**
   * Identifies the source of the first arrow in the composition.
   *
   * @returns The source object.
   * @see SymPy `sympy.categories.baseclasses.CompositeMorphism.domain`
   */
  override get domain(): Expr { return first(this.components).domain; }
  /**
   * Identifies the target of the final arrow in the composition.
   *
   * @returns The target object.
   * @see SymPy `sympy.categories.baseclasses.CompositeMorphism.codomain`
   */
  override get codomain(): Expr { return last(this.components).codomain; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return compositeMorphism(first(args).args.map((m) => cast(m, Morphism))); }
  /**
   * Forgets the composite structure of this morphism.
   *
   * @param name - Symbolic name.
   * @returns A single named arrow with the endpoints of this composite.
   * @see SymPy `sympy.categories.baseclasses.CompositeMorphism.flatten`
   */
  flatten(name: string): NamedMorphismNode { return new NamedMorphismNode(this.domain, this.codomain, name); }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return `${[...this.components].reverse().map((m) => print(new Sym(m.name))).join('\\circ ')}:${print(this.domain)}\\rightarrow ${print(this.codomain)}`; }
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
/**
 * Composes arrows in the order in which they act.
 *
 * @param components - Composable arrows in the order they act, separately or as a list.
 * @returns The composite arrow, simplified by removing identities and flattening nested composites.
 * @throws RangeError when there are no components or adjacent arrows have incompatible endpoints.
 * @see SymPy `sympy.categories.baseclasses.CompositeMorphism`
 * @example
 * ```ts
 * import { CompositeMorphism, NamedMorphism, categoryObject } from '@symjs/symjs';
 *
 * const A = categoryObject('A'), B = categoryObject('B');
 * const f = NamedMorphism(A, B, 'f');
 * const g = NamedMorphism(B, categoryObject('C'), 'g');
 * CompositeMorphism(f, g).equals(g.compose(f)); // => True
 * ```
 */
export const CompositeMorphism = /* @__PURE__ */ callableClass(CompositeMorphismNode, (...components: Morphism[] | [readonly Morphism[]]): Morphism =>
  compositeMorphism(Array.isArray(components[0]) ? components[0] : components.map((m) => cast(m, Morphism))));
export type CompositeMorphism = CompositeMorphismNode;

/**
 * A symbolic class containing a set of category objects.
 *
 * @see SymPy `sympy.categories.baseclasses.Class`
 */
export class CategoryClass extends ExtensionExpr {
  /**
   * Whether this collection is a proper class.
   *
   * @see SymPy `sympy.categories.baseclasses.Class.is_proper`
   */
  readonly isProper = false;
  /**
   * Constructs an instance of `CategoryClass`.
   *
   * @param objects - Objects belonging to the category or subdiagram.
   */
  constructor(
    /** Objects belonging to the category or subdiagram. */
    readonly objects: SetExpr) { super('Class', [objects]); }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new CategoryClass(cast(first(args), SetExpr)); }
}

/**
 * A named category with a class of objects and a set of commutative diagrams.
 *
 * @see SymPy `sympy.categories.baseclasses.Category`
 */
export class CategoryNode extends ExtensionExpr {
  /**
   * Constructs an instance of `CategoryNode`.
   *
   * @param name - Symbolic name.
   * @param objects - Objects belonging to the category or subdiagram.
   * @param commutativeDiagrams - Diagrams required to commute in this category.
   * @throws RangeError when the category name is empty.
   */
  constructor(name: string, objects: SetExpr = EmptySet,
    /**
     * Returns the `FiniteSet` of diagrams which are known to be commutative in this category.
     *
     * @see SymPy `sympy.categories.baseclasses.Category.commutative_diagrams`
     */
    readonly commutativeDiagrams: SetExpr = EmptySet) {
    if (!name) throw new RangeError('A Category cannot have an empty name.');
    super(name, [new CategoryClass(objects), commutativeDiagrams]);
  }
  /**
   * Identifies the objects belonging to this category.
   *
   * @returns The object class.
   * @see SymPy `sympy.categories.baseclasses.Category.objects`
   */
  get objects(): CategoryClass { return cast(first(this.args), CategoryClass); }
  protected override computeKey(): string { return `Category(${JSON.stringify(this.name)};${this.args.map((x) => x.key).join(';')})`; }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new CategoryNode(this.name, cast(first(args), CategoryClass).objects, cast(at(args, 1), SetExpr)); }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string { return `Category(${JSON.stringify(this.name)})`; }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string { return `\\mathbf{${print(new Sym(this.name))}}`; }
  /**
   * The morphisms from the source object to the target object.
   *
   * @param _a - Source object.
   * @param _b - Target object.
   * @throws NotImplementedError when the category is asked for a hom-set.
   * @see SymPy `sympy.categories.baseclasses.Category.hom`
   */
  hom(_a: Expr, _b: Expr): never { throw new NotImplementedError('hom-sets are not implemented in Category, as in SymPy.'); }
  /**
   * The class of all morphisms of the category.
   *
   * @throws NotImplementedError when the category is asked for its entire class of morphisms.
   * @see SymPy `sympy.categories.baseclasses.Category.all_morphisms`
   */
  allMorphisms(): never { throw new NotImplementedError('Obtaining the class of morphisms is not implemented in Category, as in SymPy.'); }
}
/**
 * Constructs a named category from its objects and commutative diagrams.
 *
 * @param name - Symbolic name.
 * @param objects - Objects belonging to the category or subdiagram.
 * @param diagrams - Diagrams required to commute.
 * @returns The resulting `Category` expression.
 * @throws RangeError when the category name is empty.
 * @see SymPy `sympy.categories.baseclasses.Category`
 * @example
 * ```ts
 * import { Category, Diagram, EmptySet, NamedMorphism, categoryObject, finiteSet } from '@symjs/symjs';
 *
 * const A = categoryObject('A'), B = categoryObject('B');
 * const f = NamedMorphism(A, B, 'f');
 * const d = Diagram([f]);
 * Category('K', EmptySet, [d]).commutativeDiagrams.equals(finiteSet(d)); // => True
 * ```
 */
export const Category = /* @__PURE__ */ callableClass(CategoryNode, (name: string, objects: SetExpr = EmptySet, diagrams: readonly DiagramNode[] = []): CategoryNode =>
  new CategoryNode(name, objects, finiteSet(...diagrams)));
export type Category = CategoryNode;

/** A property name or collection of properties attached to a morphism. */
export type MorphismProperties = string | readonly (ExprLike | string)[] | SetExpr;
/** Diagram arrows, optionally paired with the properties they satisfy. */
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

/**
 * A collection of morphisms and properties divided into premises and conclusions.
 *
 * @see SymPy `sympy.categories.baseclasses.Diagram`
 */
export class DiagramNode extends ExtensionExpr {
  /**
   * Returns the premises of this diagram.
   *
   * @see SymPy `sympy.categories.baseclasses.Diagram.premises`
   */
  readonly premises: DictNode;
  /**
   * Returns the conclusions of this diagram.
   *
   * @see SymPy `sympy.categories.baseclasses.Diagram.conclusions`
   */
  readonly conclusions: DictNode;
  /**
   * Returns the `FiniteSet` of objects that appear in this diagram.
   *
   * @see SymPy `sympy.categories.baseclasses.Diagram.objects`
   */
  readonly objects: SetExpr;
  /**
   * Constructs an instance of `DiagramNode`.
   *
   * @param premises - Arrows and properties assumed in the diagram.
   * @param conclusions - Arrows and properties asserted by the diagram.
   */
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
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr { return new DiagramNode(cast(first(args), DictNode), cast(at(args, 1), DictNode)); }
  /**
   * Formats the premises and conclusions on either side of an arrow, displaying an empty diagram as the
   * empty set.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    if (this.premises.args.length === 0) return print(EmptySet);
    const premises = print(this.premises);
    return this.conclusions.args.length ? `${premises}\\Longrightarrow ${print(this.conclusions)}` : premises;
  }
  /**
   * Finds the arrows from the source to the target in both parts of the diagram.
   *
   * @param a - Source object.
   * @param b - Target object.
   * @returns The premise and conclusion morphism sets.
   * @see SymPy `sympy.categories.baseclasses.Diagram.hom`
   */
  hom(a: Expr, b: Expr): [SetExpr, SetExpr] {
    const arrows = (d: DictNode): SetExpr => finiteSet(...d.items().map(([m]) => cast(m, Morphism)).filter((m) => m.domain.equals(a) && m.codomain.equals(b)));
    return [arrows(this.premises), arrows(this.conclusions)];
  }
  /**
   * Tests whether this diagram includes the supplied diagram and its morphism properties.
   *
   * @param diagram - Diagram to lay out or draw.
   * @returns True if it is a subdiagram.
   * @see SymPy `sympy.categories.baseclasses.Diagram.is_subdiagram`
   */
  isSubdiagram(diagram: DiagramNode): boolean {
    const includes = (a: DictNode, b: DictNode): boolean => b.items().every(([m, props]) => a.containsKey(m) && a.get(m).equals(props));
    return includes(this.premises, diagram.premises) && includes(this.conclusions, diagram.conclusions);
  }
  /**
   * Restricts the premises and conclusions to arrows between the selected objects.
   *
   * @param objects - Objects belonging to the category or subdiagram.
   * @returns The diagram induced by the selected objects.
   * @throws RangeError when the objects do not form a finite set or a selected object does not belong to the diagram.
   * @see SymPy `sympy.categories.baseclasses.Diagram.subdiagram_from_objects`
   */
  subdiagramFromObjects(objects: SetExpr): DiagramNode {
    if (!(objects instanceof FiniteSet) && !objects.equals(EmptySet)) throw new RangeError('A subdiagram requires a finite set of objects.');
    if (objects.args.some((o) => containsQ(this.objects, o) !== true)) throw new RangeError('Supplied objects should all belong to the diagram.');
    const restrict = (d: DictNode): DictNode => Dict(d.items().filter(([m]) => { const f = cast(m, Morphism); return containsQ(objects, f.domain) === true && containsQ(objects, f.codomain) === true; }));
    return new DiagramNode(restrict(this.premises), restrict(this.conclusions));
  }
}
/**
 * Constructs a diagram from its premise and conclusion morphisms and their properties.
 *
 * @param premises - Arrows and properties assumed in the diagram.
 * @param conclusions - Arrows and properties asserted by the diagram.
 * @returns The resulting `Diagram` expression.
 * @throws RangeError when a premise or conclusion assigns properties to an identity morphism.
 * @see SymPy `sympy.categories.baseclasses.Diagram`
 * @example
 * ```ts
 * import { Diagram, NamedMorphism, categoryObject } from '@symjs/symjs';
 *
 * const A = categoryObject('A'), B = categoryObject('B');
 * const f = NamedMorphism(A, B, 'f');
 * Diagram([f]).objects; // => {Object("A"), Object("B")}
 * ```
 */
export const Diagram = /* @__PURE__ */ callableClass(DiagramNode, (premises: DiagramInput = [], conclusions: DiagramInput = []): DiagramNode => new DiagramNode(premises, conclusions));
export type Diagram = DiagramNode;
