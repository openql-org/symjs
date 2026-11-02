// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point of the base module `@symjs/symjs`: the whole computer
 * algebra system. Each feature area is also available as its own entry point
 * (`@symjs/symjs/core`, `/special`, `/simplify`, `/polys`, `/calculus`,
 * `/solvers`, `/sets`, `/matrices`) for smaller bundles. Domain-specific
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
