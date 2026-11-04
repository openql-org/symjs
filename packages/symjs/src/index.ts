// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point of the base module `@symjs/symjs`: the whole computer
 * algebra system. Each feature area is also available as its own entry point
 * (`@symjs/symjs/core`, `/special`, `/simplify`, `/polys`, `/calculus`,
 * `/solvers`, `/sets`, `/matrices`, `/logic`, `/ntheory`, `/combinatorics`, `/utilities`,
 * `/tensor`, `/printing`, `/discrete`, `/algebras`, `/holonomic`, `/geometry`, `/vector`) for smaller bundles. Domain-specific
 * extend modules are separate packages (packages/* in the repository).
 */

export * from './core';
export * from './special';
export * from './simplify';
export * from './polys';
export * from './calculus';
export * from './solvers';
export * from './sets';
export * from './matrices';
export * from './logic';
export * from './ntheory';
export * from './combinatorics';
export * from './utilities';
export * from './tensor';
export * from './printing';
export * from './strategies';
export * from './unify';
export * from './discrete';
export * from './holonomic';
export * from './algebras';
export * from './geometry';
export * from './vector';
export type { PermutationLike } from './tensor';
