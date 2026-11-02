// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/printing`: 2D pretty printing (SymPy
 * sympy.printing.pretty: pretty, pprint, pretty_print, pager_print). The
 * str and LaTeX printers are part of the core entry.
 */

// every entry point brings the core with its registrations
import './core';

export { pretty, pprint, prettyPrint, pagerPrint, PrettyPrinter, PrettyTuple, prettyHooks, StringPict, PrettyForm } from './printing/pretty/index';
export type { PrettyOptions, Printable, MatrixLike } from './printing/pretty/index';
