// SPDX-License-Identifier: MIT
import { expect, it } from 'vitest';
import * as api from '../src/diffgeom';
import { CoordSystem } from '../src/diffgeom/diffgeom';
import { R2R } from '../src/diffgeom/rn';
it('exports one definition for each public name', () => {
  expect(api.CoordSystem).toBe(CoordSystem);
  expect(api.R2R).toBe(R2R);
});
