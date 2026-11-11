// SPDX-License-Identifier: MIT
import { expect, it } from 'vitest';
import * as api from '../src';
import { CoordSystem } from '../src/diffgeom';
import { R2R } from '../src/rn';
it('exports one definition for each public name', () => {
  expect(api.CoordSystem).toBe(CoordSystem);
  expect(api.R2R).toBe(R2R);
});
