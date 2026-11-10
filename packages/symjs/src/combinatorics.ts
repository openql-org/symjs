// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/combinatorics`: permutations and permutation groups, free and finitely presented groups, coset enumeration, polycyclic groups and group homomorphisms (SymPy sympy.combinatorics).
 */

// every entry point brings the core with its registrations
import './core';

import { permutationGroupHooks } from './combinatorics/permgroups';
import { polycyclicGroupOf } from './combinatorics/pcgroups';
import { presentationOf, strongPresentationOf } from './combinatorics/permpresentation';

export * from './combinatorics/index';

// the permutation group algorithms that use finitely presented groups
permutationGroupHooks.presentation = presentationOf;
permutationGroupHooks.strongPresentation = strongPresentationOf;
permutationGroupHooks.polycyclicGroup = polycyclicGroupOf;
