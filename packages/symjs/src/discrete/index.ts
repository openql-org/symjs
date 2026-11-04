// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Functions on discrete sequences (SymPy sympy.discrete): transforms
 * (fft, ifft, ntt, intt, fwht, ifwht, mobiusTransform,
 * inverseMobiusTransform), convolutions (convolution, convolutionFft,
 * convolutionNtt, convolutionFwht, convolutionSubset, coveringProduct,
 * intersectingProduct) and linear recurrences (linrec).
 */

export { fft, ifft, ntt, intt, fwht, ifwht, mobiusTransform, inverseMobiusTransform } from './transforms';
export type { FftOptions, MobiusTransformOptions } from './transforms';
export { convolution, convolutionFft, convolutionNtt, convolutionFwht, convolutionSubset, coveringProduct, intersectingProduct } from './convolutions';
export type { ConvolutionOptions } from './convolutions';
export { linrec } from './recurrences';
