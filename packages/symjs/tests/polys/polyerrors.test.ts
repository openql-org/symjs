// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/polyerrors.ts: SymPy's polynomial exception classes.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('polynomial errors', () => {
  it('have SymPy names and hierarchy', () => {
    const classes = [
      sj.BasePolynomialError, sj.PolynomialDivisionFailed, sj.OperationNotSupported, sj.HeuristicGCDFailed, sj.ModularGCDFailed,
      sj.HomomorphismFailed, sj.IsomorphismFailed, sj.ExtraneousFactors, sj.EvaluationFailed, sj.RefinementFailed, sj.NotReversible,
      sj.NotAlgebraic, sj.UnificationFailed, sj.UnsolvableFactorError, sj.GeneratorsError, sj.GeneratorsNeeded, sj.ComputationFailed,
      sj.UnivariatePolynomialError, sj.MultivariatePolynomialError, sj.OptionError, sj.FlagError,
    ];
    for (const C of classes) {
      const e = new C('msg');
      expect(e.name).toBe(C.name);
      expect(e.message).toBe('msg');
      expect(e).toBeInstanceOf(TypeError);
    }
    expect(new sj.GeneratorsNeeded()).toBeInstanceOf(sj.GeneratorsError);
    expect(new sj.FlagError()).toBeInstanceOf(sj.OptionError);
    expect(new sj.UnivariatePolynomialError()).toBeInstanceOf(sj.PolynomialError);
    expect(new sj.MultivariatePolynomialError().message).toBe('');
    expect(new sj.HeuristicGCDFailed()).toBeInstanceOf(sj.BasePolynomialError);
  });
});
