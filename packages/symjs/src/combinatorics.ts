// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Entry point `@symjs/symjs/combinatorics`: permutations and permutation groups, free and finitely presented groups, coset enumeration, polycyclic groups and group homomorphisms (SymPy sympy.combinatorics).
 * @module
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
export { TransitiveSubgroup, S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups, fourGroup, M20, S3InS6, A4InS6, S4m, S4p, A4xC2, S4xC2, G18, G36m, G36p, G72, PSL2F5, PGL2F5, findTransitiveSubgroupsOfS6 } from './combinatorics/galois';
export type { FindTransitiveSubgroupsOptions } from './combinatorics/galois';
