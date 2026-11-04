// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/discrete`: functions on discrete sequences
 * (SymPy sympy.discrete: discrete Fourier, number theoretic, Walsh Hadamard
 * and Mobius transforms, convolutions, linear recurrences).
 */

// every entry point brings the core with its registrations
import './core';

export * from './discrete/index';
