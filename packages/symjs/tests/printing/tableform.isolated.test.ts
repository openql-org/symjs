// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/tableform.ts without the matrices entry point (no matrix constructor registered).

import { describe, expect, it } from 'vitest';
import { TableForm } from '../../src/printing/tableform';

describe('TableForm without the matrices', () => {
  it('asMatrix needs the matrices entry point', () => {
    expect(() => new TableForm([[1]]).asMatrix()).toThrow('import @symjs/symjs/matrices');
  });
});
