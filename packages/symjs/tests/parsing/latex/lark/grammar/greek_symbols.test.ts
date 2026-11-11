// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { GREEK } from '../../../../../src/parsing/latex/lark/grammar/greek_symbols';
import { parseLatexLark } from '../../../../../src/parsing';
import { Sym } from '../../../../../src/core/nodes';
it('uses exactly the Greek symbols and variants in the upstream grammar', () => {
  expect([...GREEK]).toEqual(['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'varepsilon', 'zeta', 'eta', 'theta', 'vartheta', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'rho', 'varrho', 'tau', 'upsilon', 'phi', 'varphi', 'chi', 'psi', 'omega']);
  for (const name of GREEK) expect((parseLatexLark(`\\${name}`) as Sym).name).toBe(name.replace('var', ''));
});
