// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, printing/pretty/pretty.py (the printers of sympy.categories), BSD-3-Clause; see LICENSE.

/**
 * @file The pretty forms of morphisms, categories and diagrams (SymPy PrettyPrinter._print_Morphism,
 * _print_NamedMorphism, _print_IdentityMorphism, _print_CompositeMorphism, _print_Category and
 * _print_Diagram): `f:A-->B`, `id:A-->A`, `g*f:A-->C` in ASCII (`g∘f:A——▶C` in unicode).
 */

import type { Expr } from '../core/nodes';
import { Sym } from '../core/nodes';
import type { PrettyPrinter } from '../printing/pretty/pretty';
import { PrettyForm, StringPict } from '../printing/pretty/stringpict';
import { prettySymbol, xsym } from '../printing/pretty/symbology';
import { EmptySet } from '../sets/sets';
import { CategoryNode, CompositeMorphismNode, DiagramNode, IdentityMorphismNode, Morphism } from './baseclasses';

/** SymPy _print_Morphism: domain-->codomain. */
function arrowForm(m: Morphism, printer: PrettyPrinter): StringPict {
  return new StringPict(...printer.print(m.domain).right(xsym('-->'), printer.print(m.codomain)));
}

/** SymPy _print_NamedMorphism: name:domain-->codomain. */
function namedForm(name: string, m: Morphism, printer: PrettyPrinter): PrettyForm {
  return PrettyForm.of(printer.print(new Sym(prettySymbol(name))).right(':', arrowForm(m, printer)));
}

/** The pretty form of a morphism, category or diagram, or undefined for another node. */
export function prettyCategories(e: Expr, printer: PrettyPrinter): PrettyForm | undefined {
  if (e instanceof IdentityMorphismNode) return namedForm('id', e, printer);
  if (e instanceof CompositeMorphismNode) {
    const names = [...e.components].reverse().map((c) => prettySymbol(c.name)).join(xsym('.'));
    return PrettyForm.of(new StringPict(`${names}:`).right(arrowForm(e, printer)));
  }
  if (e instanceof Morphism) return namedForm(e.name, e, printer);
  if (e instanceof CategoryNode) return printer.print(new Sym(prettySymbol(e.name)));
  if (e instanceof DiagramNode) {
    if (!e.premises.args.length) return printer.print(EmptySet);
    const premises = printer.print(e.premises);
    if (!e.conclusions.args.length) return premises;
    return PrettyForm.of(premises.right(` ${xsym('==>')} `, printer.print(e.conclusions)));
  }
  return undefined;
}
