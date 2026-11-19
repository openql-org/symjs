// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { createHash } from 'node:crypto';
import type { Case } from './harness';
import * as categories from '../../packages/symjs/src/categories';
import * as plotting from '../../packages/symjs/src/plotting';
import * as diffgeomNamespace from '@symjs/symjs/diffgeom';
import { camel, camelIn, JS_GLOBAL_RENAMES, publicApi } from './harness';

/** Explicit public aliases: an adapter by itself is never evidence of an API. */
export const PUBLIC_ALIASES: Readonly<Record<string, string>> = {
  _linear_eq_to_dict: '_linearEqToDict', _lin_eq2dict: '_linEq2dict',
  Catalan: 'S.Catalan', EulerGamma: 'S.EulerGamma', GoldenRatio: 'S.GoldenRatio', TribonacciConstant: 'S.TribonacciConstant',
  Integer: 'Rational.of', Equality: 'Eq', Unequality: 'Ne', GreaterThan: 'Ge', LessThan: 'Le', StrictGreaterThan: 'Gt', StrictLessThan: 'Lt',
  N: 'evalf', ln: 'log', minpoly: 'minimalPolynomial', poly: 'Poly.from',
  heugcd: 'IPolys.prototype.dmpZzHeuGcd',
  zeros: 'Matrix.zeros', ones: 'Matrix.ones', eye: 'Matrix.eye', diag: 'Matrix.diag',
  true: 'S.true', false: 'S.false', FallingFactorial: 'ff', RisingFactorial: 'rf',
};
function publicPathExists(path: string): boolean {
  let value: unknown = publicApi;
  for (const key of path.split('.')) {
    if (value === null || (typeof value !== 'object' && typeof value !== 'function') || !(key in value)) return false;
    value = (value as Record<string, unknown>)[key];
  }
  return value !== undefined;
}
const exprMethods = ['diff', 'integrate', 'limit', 'series', 'expand', 'simplify', 'factor', 'collect', 'cancel', 'apart', 'ratsimp', 'together', 'trigsimp', 'powsimp', 'radsimp', 'nsimplify', 'logcombine', 'powdenest', 'rewrite', 'refine', 'evalf',
      'adjoint', 'argsCnc', 'asBaseExp', 'asCoeffAdd', 'asCoeffMul', 'asCoeffExponent', 'asCoefficient', 'asCoefficientsDict', 'asContentPrimitive', 'asDummy', 'asIndependent', 'asLeadingTerm', 'asNumerDenom', 'asPoly', 'asPowersDict', 'asRealImag', 'asTerms', 'aseries', 'atoms', 'classKey', 'coeff', 'combsimp', 'compare', 'couldExtractMinusSign', 'count', 'countOps', 'dir', 'doit', 'dummyEq', 'extractAdditively', 'extractBranchFactor', 'extractMultiplicatively', 'find', 'fourierSeries', 'fps', 'gammasimp', 'getO', 'getn', 'hasFree', 'hasXfree', 'invert', 'isAlgebraicExpr', 'isConstant', 'isHypergeometric', 'isMeromorphic', 'isPolynomial', 'isRationalFunction', 'isSame', 'leadterm', 'lseries', 'match', 'matches', 'normal', 'primitive', 'rcall', 'removeO', 'replace', 'round', 'separate', 'sortKey', 'taylorTerm', 'transpose', 'xreplace',
      'asExpr', 'asOrderedFactors', 'asOrderedTerms', 'copy', 'nseries'];
export const MEMBER_FUNCTIONS: Readonly<Record<string, readonly string[]>> = {
    Expr: exprMethods,
    Matrix: ['doit', 'berkowitz', 'berkowitzEigenvals', 'berkowitzMinors', 'companion', 'connectedComponents', 'elementaryColOp', 'elementaryRowOp', 'inverseADJ', 'inverseBLOCK', 'inverseCH', 'inverseGE', 'inverseLDL', 'inverseLU', 'inverseQR', 'irregular', 'iterItems', 'iterValues', 'jordanBlock', 'jordanCell', 'key2bounds', 'key2ij', 'per', 'permuteBkwd', 'permuteFwd', 'printNonzero', 'refine', 'singularValueDecomposition', 'stronglyConnectedComponents', 'table', 'toDM', 'upperHessenbergDecomposition', 'wilkinson', 'analyticFunc', 'bidiagonalDecomposition', 'bidiagonalize', 'cholesky', 'choleskySolve', 'cofactor', 'colInsert', 'columnspace', 'conditionNumber', 'connectedComponentsDecomposition', 'cramerSolve', 'cross', 'diagonal', 'diagonalSolve', 'diagonalize', 'dot', 'dual', 'echelonForm', 'eigenvects', 'extract', 'gaussJordanSolve', 'getDiagBlocks', 'hat', 'invMod', 'isAntiSymmetric', 'isDiagonal', 'isDiagonalizable', 'isNilpotent', 'isSymmetric', 'jacobian', 'jordanCells', 'jordanForm', 'leftEigenvects', 'lll', 'lllTransform', 'lowerTriangular', 'lowerTriangularSolve', 'minorSubmatrix', 'multiplyElementwise', 'norm', 'normalized', 'nullspace', 'orthogonalize', 'permanent', 'permuteCols', 'permuteRows', 'pinv', 'pinvSolve', 'project', 'rank', 'rankDecomposition', 'rref', 'rrefRhs', 'rowInsert', 'rowspace', 'singularValues', 'solveLeastSquares', 'stronglyConnectedComponentsDecomposition', 'upperTriangular', 'upperTriangularSolve', 'vech', 'vec'],
    MatrixExpr: ['fromIndexSummation', ...exprMethods],
  };
export const MATRIX_MEMBER_ALIASES: Readonly<Record<string, string>> = {
    LUdecomposition: 'luDecomposition', LDLdecomposition: 'ldl', QRdecomposition: 'qrDecomposition', LUdecompositionFF: 'LUdecompositionFF', LUdecompositionSimple: 'LUdecompositionSimple',
    LUsolve: 'matrixSolve', QRsolve: 'matrixSolve', LDLsolve: 'matrixSolve', solve: 'matrixSolve', exp: 'matrixExp', log: 'matrixLog',
    applyfunc: 'Matrix.prototype.map', colJoin: 'Matrix.prototype.vstack', rowJoin: 'Matrix.prototype.hstack',
    berkowitzCharpoly: 'Matrix.prototype.charpoly', berkowitzDet: 'Matrix.prototype.det', detLUDecomposition: 'Matrix.prototype.det', detBareis: 'Matrix.prototype.det',
  };

/** The actual public export/member supporting a name, or undefined when absent. */
export function counterpartFor(a: { name: string; owner?: string; category?: string }): string | undefined {
  if (camel(a.name) in categories && ['DiagramGrid', 'XypicDiagramDrawer', 'xypicDrawDiagram', 'ArrowStringDescription'].includes(camel(a.name))) return 'categories.' + camel(a.name);
  if (a.category === 'plotting' && camel(a.name) in plotting) return 'plotting.' + camel(a.name);
  const camelMethod = (n: string): string => n.replace(/_([a-zA-Z0-9])/g, (_m, c: string) => c.toUpperCase());
  if (a.category === 'diffgeom' && !a.name.startsWith('.')) {
    const name = camel(a.name);
    return name in diffgeomNamespace ? `@symjs/symjs/diffgeom.${name}` : undefined;
  }
  if (!a.name.startsWith('.')) {
    const alias = PUBLIC_ALIASES[a.name];
    const candidates = [camelIn(a.name, a.category), ...(alias ? [alias] : [])];
    if (!(a.name in JS_GLOBAL_RENAMES)) candidates.push(a.name);
    if (a.category === 'polys') candidates.push('Poly.prototype.' + camelMethod(a.name));
    return candidates.find(publicPathExists);
  }
  const m = camelMethod(a.name.slice(1));
  const owners: Record<string, string> = { Expr: 'Expr', MutableDenseMatrix: 'Matrix', Matrix: 'Matrix', ImmutableDenseNDimArray: 'ImmutableDenseNDimArray', Permutation: 'Permutation', MatrixExpr: 'MatrixExpr' };
  const owner = owners[a.owner ?? ''];
  if (!owner) return undefined;
  const candidates = [`${owner}.prototype.${m}`, `${owner}.${m}`, `${owner}.prototype.${a.name.slice(1)}`];
  // SymPy's mutable matrix methods (row_swap, fill, ...) are members of the mutable class
  if (a.owner === 'MutableDenseMatrix') candidates.push(`MutableDenseMatrix.prototype.${m}`, `MutableDenseMatrix.prototype.${a.name.slice(1)}`);
  // Expression operations may be exposed as free functions. Their concrete path
  // is reported, so a function counterpart is not confused with a fluent method.
  // SymPy's MatrixExpr derives from Expr: its Expr methods are the same functions
  if (MEMBER_FUNCTIONS[owner]?.includes(m)) candidates.push(m);
  if (owner === 'Matrix' && MATRIX_MEMBER_ALIASES[m]) candidates.push(MATRIX_MEMBER_ALIASES[m]!);
  return candidates.find(publicPathExists);
}
export function hasCounterpart(a: { name: string; owner?: string; category?: string }): boolean {
  return counterpartFor(a) !== undefined;
}


export const caseLabel = (c: Case): string => `${c.module}: ${c.src}`;
// Keep established hashes unchanged; different unpacked components are distinct cases.
export const caseKey = (c: Case): string => `${caseLabel(c)} #${createHash('sha256').update(JSON.stringify([c.args, c.kwargs, c.self, c.expected, c.assume, ...(c.pick === undefined ? [] : [c.pick])])).digest('hex').slice(0, 16)}`;

export const apiKey = (a: { name: string; category: string; owner?: string }): string => `${a.category}: ${a.owner ? a.owner + ':' : ''}${a.name}`;
