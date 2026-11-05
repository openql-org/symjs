// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/printing`: 2D pretty printing (SymPy
 * sympy.printing.pretty: pretty, pprint, pretty_print, pager_print), srepr,
 * the tree printers (print_tree, dotprint), MathML and TableForm. The str
 * and LaTeX printers are part of the core entry.
 */

// every entry point brings the core with its registrations
import './core';

export { pretty, pprint, prettyPrint, pagerPrint, pprintUseUnicode, pprintTryUseUnicode, PrettyPrinter, PrettyTuple, prettyHooks, StringPict, PrettyForm } from './printing/pretty/index';
export type { PrettyOptions, Printable, MatrixLike } from './printing/pretty/index';
export { srepr } from './printing/repr';
export type { ReprPrintable, ReprMatrix } from './printing/repr';
// SymPy's tree() is not a top-level name; strategies.tree is the module of that name
export { printTree, printNode, pprintNodes } from './printing/tree';
export type { TreeOptions } from './printing/tree';
export { dotprint, dotnode, dotedges, purestr, purestrWithArgs, styleof, attrprint, defaultStyles } from './printing/dot';
export type { DotClass, DotStyles, DotNodeOptions, DotEdgesOptions, DotprintOptions } from './printing/dot';
export { mathml, printMathml, MathMLContentPrinter, MathMLPresentationPrinter, MathMLElement } from './printing/mathml';
export type { MathMLOptions, MathMLPrintOptions, MathMLPrintable, MathMLMatrix } from './printing/mathml';
export { TableForm } from './printing/tableform';
export type { TableFormOptions, TableData, TableEntry, TableHeading, TableColumnFormat } from './printing/tableform';
