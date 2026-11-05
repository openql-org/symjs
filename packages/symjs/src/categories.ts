// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Category objects, morphisms and diagrams (SymPy sympy.categories). */
import './core';
export { SymObject, categoryObject, Morphism, IdentityMorphism, NamedMorphism, CompositeMorphism, Category, CategoryClass, Diagram } from './categories/baseclasses';
export type { DiagramInput, MorphismProperties } from './categories/baseclasses';

import { prettyHooks as _prettyHooks_ } from './printing/pretty/pretty';
import { prettyCategories as _prettyCategories_ } from './categories/pretty';

_prettyHooks_.extensionFallbacks.push(_prettyCategories_);
