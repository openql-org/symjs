// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The known facts between unary predicates, compiled from
 * sympy.assumptions.facts (SymPy sympy.assumptions.ask_generated): the CNF
 * clauses of the number and matrix facts used by satask, and the predicates
 * implied and rejected by each predicate.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE); the tables are
 * SymPy's, written compactly: a clause lists its predicates, "!" marks a
 * negated literal.
 */

import type { Predicate } from '../core/refine';
import { Literal } from './cnf';
import { predicateNamed } from './facts';

const NUMBER_FACTS = [
  'algebraic !imaginary transcendental',
  'algebraic !negative transcendental',
  'algebraic !positive transcendental',
  'algebraic !rational',
  'algebraic transcendental !zero',
  '!algebraic finite',
  '!algebraic !transcendental',
  'antihermitian hermitian !zero',
  'antihermitian !imaginary',
  'commutative !finite',
  'commutative !infinite',
  'composite !even !positive prime',
  '!composite even odd',
  '!composite positive',
  '!composite !prime',
  'even odd !prime',
  'even !zero',
  '!even !odd',
  '!even rational',
  'finite !transcendental',
  '!finite !infinite',
  'hermitian !negative',
  'hermitian !positive',
  'hermitian !zero',
  '!imaginary !negative',
  '!imaginary !positive',
  '!imaginary !zero',
  'infinite !negative_infinite',
  'infinite !positive_infinite',
  'irrational !negative rational',
  'irrational !positive rational',
  'irrational rational !zero',
  '!irrational negative positive zero',
  '!irrational !rational',
  'negative positive !rational zero',
  '!negative !negative_infinite',
  '!negative !positive',
  '!negative !positive_infinite',
  '!negative !zero',
  '!negative_infinite !positive',
  '!negative_infinite !positive_infinite',
  '!negative_infinite !zero',
  '!odd rational',
  'positive !prime',
  '!positive !positive_infinite',
  '!positive !zero',
  '!positive_infinite !zero',
];

const MATRIX_FACTS = [
  'complex_elements !real_elements',
  'diagonal !lower_triangular !upper_triangular',
  '!diagonal lower_triangular',
  '!diagonal normal',
  '!diagonal symmetric',
  '!diagonal upper_triangular',
  'fullrank !invertible',
  '!fullrank invertible !square',
  '!integer_elements real_elements',
  'invertible !positive_definite',
  'invertible singular',
  'invertible !unitary',
  '!invertible !singular',
  '!invertible square',
  'lower_triangular !triangular upper_triangular',
  '!lower_triangular triangular',
  'normal !unitary',
  '!normal square',
  'orthogonal !real_elements !unitary',
  '!orthogonal positive_definite',
  '!orthogonal unitary',
  'square !symmetric',
  'triangular !unit_triangular',
  'triangular !upper_triangular',
];

const KNOWN_FACTS_DICT: Readonly<Record<string, readonly [string, string]>> = {
  algebraic: ['algebraic commutative complex finite', 'infinite negative_infinite positive_infinite transcendental'],
  antihermitian: ['antihermitian', ''],
  commutative: ['commutative', ''],
  complex: ['commutative complex finite', 'infinite negative_infinite positive_infinite'],
  complex_elements: ['complex_elements', ''],
  composite: ['algebraic commutative complex composite extended_nonnegative extended_nonzero extended_positive extended_real finite hermitian integer nonnegative nonzero positive rational real', 'extended_negative extended_nonpositive imaginary infinite irrational negative negative_infinite nonpositive positive_infinite prime transcendental zero'],
  diagonal: ['diagonal lower_triangular normal square symmetric triangular upper_triangular', ''],
  even: ['algebraic commutative complex even extended_real finite hermitian integer rational real', 'imaginary infinite irrational negative_infinite odd positive_infinite transcendental'],
  extended_negative: ['commutative extended_negative extended_nonpositive extended_nonzero extended_real', 'composite extended_nonnegative extended_positive imaginary nonnegative positive positive_infinite prime zero'],
  extended_nonnegative: ['commutative extended_nonnegative extended_real', 'extended_negative imaginary negative negative_infinite'],
  extended_nonpositive: ['commutative extended_nonpositive extended_real', 'composite extended_positive imaginary positive positive_infinite prime'],
  extended_nonzero: ['commutative extended_nonzero extended_real', 'imaginary zero'],
  extended_positive: ['commutative extended_nonnegative extended_nonzero extended_positive extended_real', 'extended_negative extended_nonpositive imaginary negative negative_infinite nonpositive zero'],
  extended_real: ['commutative extended_real', 'imaginary'],
  finite: ['commutative finite', 'infinite negative_infinite positive_infinite'],
  fullrank: ['fullrank', ''],
  hermitian: ['hermitian', ''],
  imaginary: ['antihermitian commutative complex finite imaginary', 'composite even extended_negative extended_nonnegative extended_nonpositive extended_nonzero extended_positive extended_real infinite integer irrational negative negative_infinite nonnegative nonpositive nonzero odd positive positive_infinite prime rational real zero'],
  infinite: ['commutative infinite', 'algebraic complex composite even finite imaginary integer irrational negative nonnegative nonpositive nonzero odd positive prime rational real transcendental zero'],
  integer: ['algebraic commutative complex extended_real finite hermitian integer rational real', 'imaginary infinite irrational negative_infinite positive_infinite transcendental'],
  integer_elements: ['complex_elements integer_elements real_elements', ''],
  invertible: ['fullrank invertible square', 'singular'],
  irrational: ['commutative complex extended_nonzero extended_real finite hermitian irrational nonzero real', 'composite even imaginary infinite integer negative_infinite odd positive_infinite prime rational zero'],
  is_true: ['is_true', ''],
  lower_triangular: ['lower_triangular triangular', ''],
  negative: ['commutative complex extended_negative extended_nonpositive extended_nonzero extended_real finite hermitian negative nonpositive nonzero real', 'composite extended_nonnegative extended_positive imaginary infinite negative_infinite nonnegative positive positive_infinite prime zero'],
  negative_infinite: ['commutative extended_negative extended_nonpositive extended_nonzero extended_real infinite negative_infinite', 'algebraic complex composite even extended_nonnegative extended_positive finite imaginary integer irrational negative nonnegative nonpositive nonzero odd positive positive_infinite prime rational real transcendental zero'],
  noninteger: ['noninteger', ''],
  nonnegative: ['commutative complex extended_nonnegative extended_real finite hermitian nonnegative real', 'extended_negative imaginary infinite negative negative_infinite positive_infinite'],
  nonpositive: ['commutative complex extended_nonpositive extended_real finite hermitian nonpositive real', 'composite extended_positive imaginary infinite negative_infinite positive positive_infinite prime'],
  nonzero: ['commutative complex extended_nonzero extended_real finite hermitian nonzero real', 'imaginary infinite negative_infinite positive_infinite zero'],
  normal: ['normal square', ''],
  odd: ['algebraic commutative complex extended_nonzero extended_real finite hermitian integer nonzero odd rational real', 'even imaginary infinite irrational negative_infinite positive_infinite transcendental zero'],
  orthogonal: ['fullrank invertible normal orthogonal positive_definite square unitary', 'singular'],
  positive: ['commutative complex extended_nonnegative extended_nonzero extended_positive extended_real finite hermitian nonnegative nonzero positive real', 'extended_negative extended_nonpositive imaginary infinite negative negative_infinite nonpositive positive_infinite zero'],
  positive_definite: ['fullrank invertible positive_definite square', 'singular'],
  positive_infinite: ['commutative extended_nonnegative extended_nonzero extended_positive extended_real infinite positive_infinite', 'algebraic complex composite even extended_negative extended_nonpositive finite imaginary integer irrational negative negative_infinite nonnegative nonpositive nonzero odd positive prime rational real transcendental zero'],
  prime: ['algebraic commutative complex extended_nonnegative extended_nonzero extended_positive extended_real finite hermitian integer nonnegative nonzero positive prime rational real', 'composite extended_negative extended_nonpositive imaginary infinite irrational negative negative_infinite nonpositive positive_infinite transcendental zero'],
  rational: ['algebraic commutative complex extended_real finite hermitian rational real', 'imaginary infinite irrational negative_infinite positive_infinite transcendental'],
  real: ['commutative complex extended_real finite hermitian real', 'imaginary infinite negative_infinite positive_infinite'],
  real_elements: ['complex_elements real_elements', ''],
  singular: ['singular', 'invertible orthogonal positive_definite unitary'],
  square: ['square', ''],
  symmetric: ['square symmetric', ''],
  transcendental: ['commutative complex finite transcendental', 'algebraic composite even infinite integer negative_infinite odd positive_infinite prime rational zero'],
  triangular: ['triangular', ''],
  unit_triangular: ['triangular unit_triangular', ''],
  unitary: ['fullrank invertible normal square unitary', 'singular'],
  upper_triangular: ['triangular upper_triangular', ''],
  zero: ['algebraic commutative complex even extended_nonnegative extended_nonpositive extended_real finite hermitian integer nonnegative nonpositive rational real zero', 'composite extended_negative extended_nonzero extended_positive imaginary infinite irrational negative negative_infinite nonzero odd positive positive_infinite prime transcendental'],
};

const clauses = (table: readonly string[]): Literal[][] =>
  table.map((c) => c.split(' ').map((l) => (l.startsWith('!') ? new Literal(predicateNamed(l.slice(1)), true) : new Literal(predicateNamed(l)))));

/** Known facts between unary predicates as CNF clauses (SymPy get_all_known_facts). */
export function getAllKnownFacts(): Literal[][] {
  return clauses([...NUMBER_FACTS, ...MATRIX_FACTS]);
}

/** Known facts between unary predicates for matrices as CNF clauses (SymPy get_all_known_matrix_facts). */
export function getAllKnownMatrixFacts(): Literal[][] {
  return clauses(MATRIX_FACTS);
}

/** Known facts between unary predicates for numbers as CNF clauses (SymPy get_all_known_number_facts). */
export function getAllKnownNumberFacts(): Literal[][] {
  return clauses(NUMBER_FACTS);
}

const predicates = (names: string): Set<Predicate> => new Set(names === '' ? [] : names.split(' ').map(predicateNamed));

/**
 * The predicates implied and rejected by each unary predicate (SymPy
 * get_known_facts_dict).
 */
export function getKnownFactsDict(): Map<Predicate, [Set<Predicate>, Set<Predicate>]> {
  return new Map(Object.entries(KNOWN_FACTS_DICT).map(([k, [implied, rejected]]) => [predicateNamed(k), [predicates(implied), predicates(rejected)]] as const));
}
