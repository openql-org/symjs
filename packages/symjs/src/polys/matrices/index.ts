// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The sparse domain matrices (SymPy sympy.polys.matrices.sdm) as the
 * polys entry re-exports them. The sdm module registers the DDM to SDM
 * conversion when loaded; re-exporting it through this side-effect-free
 * module lets a bundle include it only when it is used (DomainMatrix and the
 * rref algorithms import it themselves), not with every import of the polys
 * entry.
 */

export { SDM, sdmBerk, sdmIrref, sdmRrefDen, sdmMatmul, sdmTranspose, sdmDotvec, sdmMatvecmul, sdmNullspaceFromRref, sdmParticularFromRref, binopDict, unopDict } from './sdm';
