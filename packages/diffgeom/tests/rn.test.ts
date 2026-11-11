// SPDX-License-Identifier: MIT
import { expect, it } from 'vitest';
import { pi, rcall, simplify, sub } from '@symjs/symjs';
import { R2, R2R, R2P, R2Origin, R3, R3R, R3C, R3S, R3Origin, relations2d, relations3d } from '../src/rn';

it('exposes the Euclidean manifolds, charts and field shortcuts', () => {
  expect(R2.dim).toBe(2); expect(R3.dim).toBe(3); expect(R3Origin.manifold).toBe(R3);
  expect(R2Origin.x).toBe(R2.x); expect(R2R.x).toBe(R2.x); expect(R2P.r).toBe(R2.r);
  expect(relations2d.size).toBe(2); expect(relations3d.size).toBe(6);
  for (const chart of [R2R, R2P, R3R, R3C, R3S]) {
    chart.baseScalars().forEach((field, i) => {
      expect(chart.baseVectors()[i]!.call(field).equals(1)).toBe(true);
      expect(rcall(chart.baseOneforms()[i]!, chart.baseVectors()[i]!).equals(1)).toBe(true);
    });
  }
  expect(R3R.eZ.equals(R3R.baseVector(2))).toBe(true);
  expect(R3C.drho.equals(R3C.baseOneform(0))).toBe(true);
  expect(R3S.ePhi.equals(R3S.baseVector(2))).toBe(true);
});
it('transforms all three-dimensional coordinate pairs', () => {
  const point = [2, 3, 4];
  for (const chart of [R3C, R3S]) {
    const recovered = chart.transform(R3R, R3R.transform(chart, point));
    expect(recovered.data.every((v, i) => simplify(sub(v, point[i]!)).equals(0))).toBe(true);
  }
  expect(R3S.transform(R3C, [2, pi.div(2), 0]).data.map(String)).toEqual(['2', '0', '0']);
  expect(R3C.transform(R3S, [2, 0, 0]).data.map(String)).toEqual(['2', 'pi/2', '0']);
});
