// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/polyhedron.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.polyhedron: Polyhedron, the corners and
 * faces of a polyhedron moved by the permutations of a group.
 */

import { TupleNode } from '../core/containers';
import { at, cast } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Rational, Sym, asRational } from '../core/nodes';
import { sympify } from '../core/ops';
import type { SetExpr } from '../sets/sets';
import { finiteSet } from '../sets/sets';
import { minlex } from '../utilities/iterables';
import { Permutation } from './permutations';
import { PermutationGroupNode } from './permgroups';

const faceTuple = (f: readonly number[]): TupleNode => new TupleNode(f.map((i) => Rational.of(BigInt(i))));
const faceIndices = (t: Expr): number[] => cast(t, TupleNode).args.map((e) => Number(asRational(e).p));

/**
 * SymPy Polyhedron(corners, faces, pgroup): corners (any expressions; a
 * string is a Symbol) whose positions the permutations of pgroup move.
 * Faces are lists of corner indices, stored in their minimal rotation.
 */
export class Polyhedron extends ExtensionExpr {
  #corners: Expr[];
  readonly pgroup: PermutationGroupNode;
  constructor(corners: readonly (ExprLike | string)[], faces: readonly (readonly number[])[] = [], pgroup: readonly Permutation[] = []) {
    // a string corner is a Symbol (SymPy sympifies the corners)
    const c = new TupleNode(corners.map((x) => (typeof x === 'string' ? new Sym(x) : sympify(x))));
    const f = new TupleNode(faces.map((face) => faceTuple(minlex(face, { directed: false }))));
    const g = new TupleNode(pgroup);
    if (pgroup.length && at(pgroup, 0).size !== corners.length) throw new RangeError('Permutation size unequal to number of corners.');
    super('Polyhedron', [c, f, g]);
    this.#corners = [...c.args];
    this.pgroup = new PermutationGroupNode(pgroup.length ? [...pgroup] : [new Permutation(Array.from({ length: corners.length }, (_, i) => i))]);
  }

  withArgs(args: readonly Expr[]): Expr {
    const [c, f, g] = args;
    return new Polyhedron(cast(c, TupleNode).args, cast(f, TupleNode).args.map(faceIndices), cast(g, TupleNode).args.map((p) => cast(p, Permutation)));
  }

  /** SymPy corners (vertices): the corners in their current positions. */
  get corners(): Expr[] {
    return [...this.#corners];
  }

  /** SymPy vertices: the same as corners. */
  get vertices(): Expr[] {
    return this.corners;
  }

  /** SymPy array_form: the original index of the corner now at each position. */
  get arrayForm(): number[] {
    const original = cast(at(this.args, 0), TupleNode).args;
    return this.#corners.map((c) => original.findIndex((o) => o.key === c.key));
  }

  /** SymPy cyclic_form: the cycles of the array form. */
  get cyclicForm(): number[][] {
    return new Permutation(this.arrayForm).cyclicForm;
  }

  /** SymPy size: the number of corners. */
  get size(): number {
    return this.#corners.length;
  }

  /** SymPy faces: the set of faces, each a tuple of corner indices in its minimal rotation. */
  get faces(): SetExpr {
    return finiteSet(...cast(at(this.args, 1), TupleNode).args);
  }

  /** SymPy edges: the set of sorted index pairs of consecutive corners of the faces. */
  get edges(): SetExpr {
    const out = new Map<string, number[]>();
    for (const face of cast(at(this.args, 1), TupleNode).args.map(faceIndices)) {
      face.forEach((v, i) => {
        const edge = [v, at(face, (i - 1 + face.length) % face.length)].sort((a, b) => a - b);
        out.set(edge.join(','), edge);
      });
    }
    return finiteSet(...[...out.values()].map(faceTuple));
  }

  /**
   * SymPy rotate(perm): move the corners by a permutation of the size, or by
   * the generator of pgroup with that index (in place, as in SymPy).
   */
  rotate(perm: Permutation | number): void {
    const p = typeof perm === 'number' ? this.pgroup.getItem(perm) : perm;
    if (p.size !== this.size) throw new RangeError('Polyhedron and Permutation sizes differ.');
    const a = p.arrayForm;
    const corners = this.#corners;
    this.#corners = corners.map((_, i) => at(corners, at(a, i)));
  }

  /** SymPy reset(): return the corners to their original positions. */
  reset(): void {
    this.#corners = [...cast(at(this.args, 0), TupleNode).args];
  }
}
