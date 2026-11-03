// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/odesystem.ts: solvers/odesystem.ts loaded without solvers/ode.ts, which registers the single-equation solver.

import { expect, it } from 'vitest';
import { NotImplementedError } from '../../src/core/errors';
import { Derivative, S, Sym, UndefFn } from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';
import { dsolveSystem } from '../../src/solvers/odesystem';

it('a triangular system needs the single-equation solver', () => {
  const t = new Sym('t');
  const f = new UndefFn('f', [t]);
  const g = new UndefFn('g', [t]);
  const eqs = [add(new Derivative([f, t, S.One]), mul(-1, pow(f, 2))), add(new Derivative([g, t, S.One]), mul(-1, f))];
  expect(() => dsolveSystem(eqs, [f, g])).toThrow(NotImplementedError);
});
