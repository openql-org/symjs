"""Generate array-expression results independently with SymPy 1.14.0."""
import json
from pathlib import Path
import sympy as s
from sympy.tensor.array.expressions import (ArraySymbol, ArrayTensorProduct as TP,
    ArrayContraction as C, ArrayDiagonal as D, ArrayAdd, PermuteDims as P,
    Reshape, ZeroArray, array_derive, convert_matrix_to_array,
    convert_array_to_matrix, convert_indexed_to_array)

assert s.__version__ == '1.14.0'
A = ArraySymbol('A', (2, 2))
B = ArraySymbol('B', (2, 2))
T = ArraySymbol('T', (2, 2, 2))
M, N = (s.MatrixSymbol(name, 2, 2) for name in ['M', 'N'])
i, j, k, n = s.symbols('i j k n')
references = {}
def record(name, value):
    references[name] = str(value)

nodes = {
    'symbol': A, 'rank3': T, 'empty': ArraySymbol('E', (0, 2)),
    'product': TP(A, B), 'scaled': TP(s.Integer(3), A),
    'trace': C(A, (0, 1)), 'chain': C(TP(M, N), (1, 2)),
    'diagonal': D(A, (0, 1)), 'double_diagonal': D(TP(A, B), (0, 2), (1, 3)),
    'permuted': P(T, [2, 0, 1]), 'reshape': Reshape(A, (4,)),
    'sum': ArrayAdd(A, B), 'zero': ZeroArray(2, 2),
    'nested_contraction': C(C(TP(M, N), (1, 2)), (0, 1)),
    'single_axis': C(T, (1,)),
}
for name, value in nodes.items():
    record(name, value)
    record(name + '_explicit', value.as_explicit())
    record(name + '_doit', value.doit())
    record(name + '_latex', s.latex(value))
for name, expr in {
    'matrix_product': M*N, 'matrix_trace': s.Trace(M*N),
    'matrix_transpose': M.T, 'matrix_sum': M+N,
    'matrix_power': M**3, 'matrix_scaled': 3*M*N,
    'matrix_long': M*N*M*N,
}.items():
    array = convert_matrix_to_array(expr)
    record(name, array)
    record(name + '_back', convert_array_to_matrix(array))
for name, expr, order in [
    ('indexed', A[i,j], [i,j]), ('indexed_transpose', A[i,j], [j,i]),
    ('indexed_add', A[i,j] + B[j,i], [i,j]),
    ('indexed_diagonal', A[i,i], []),
    ('indexed_trace', s.Sum(A[i,i], (i,0,1)), []),
    ('indexed_product', s.Sum(A[i,j]*B[j,k], (j,0,1)), []),
    ('indexed_reversed', s.Sum(M[i,j]*N[j,k], (j,0,1)), [k]),
]: record(name, convert_indexed_to_array(expr, order))
for name, expr in {
    'derive_self': M, 'derive_other': N, 'derive_product': M*N,
    'derive_square': M*M, 'derive_transpose': M.T,
    'derive_trace': s.Trace(M), 'derive_sum': M+N,
    'derive_tensor': TP(M,N), 'derive_diagonal': D(M,(0,1)),
}.items():
    derivative = array_derive(expr, M)
    record(name + '_explicit', derivative.as_explicit())
    if name == 'derive_self': record(name, derivative)
record('derive_trace_correct', s.derive_by_array(M.as_explicit().trace(), s.Array(M.as_explicit())))
record('fractional_index', A[s.Rational(1, 2), 0])
for shape in [(3,), (2, 3), (2, 3, 4)]:
    a = ArraySymbol('R', shape)
    d = array_derive(a, a)
    record('derive_shape_' + '_'.join(map(str, shape)), d.as_explicit())
    record('derive_shape_repr_' + '_'.join(map(str, shape)), d)
path = Path(__file__).resolve().parents[3] / 'packages/symjs/tests/tensor/array/expressions/references.json'
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps(references, indent=2) + '\n')
