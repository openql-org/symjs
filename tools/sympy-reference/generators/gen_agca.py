"""Regenerate exact AGCA references with SymPy 1.14.0."""
import json
from pathlib import Path
import sympy
from sympy import QQ
from sympy.abc import x, y
from sympy.polys.agca import homomorphism

assert sympy.__version__ == '1.14.0'
R = QQ.old_poly_ring(x, y)
F = R.free_module(2)
M = F.submodule([x, x + y])
N = F.submodule([y, y])
Q = F.quotient_module(F.submodule([x, x]))
S = F.submodule([1, 0], [1, 1])
h = homomorphism(F, F, [[1, 0], [x, 0]])
references = {
    'free': str(F), 'basis': str(F.basis()),
    'module': str(M), 'zero': str(F.convert(0)),
    'quotient': str(Q), 'coset': str(Q.convert([1, 0])),
    'subquotient': str(F.submodule([x, 1]).quotient_module(F.submodule([x*x, x]))),
    'syzygy': str(F.submodule([1, 0], [x, 0]).syzygy_module()),
    'injective_syzygy': str(S.syzygy_module()),
    'intersection': str(F.submodule([x, x]).intersect(N)),
    'coefficients': str([R.to_sympy(c) for c in S.in_terms_of_generators([x, x*x])]),
    'quotient_ideal': str(F.submodule([x*y, x*y]).module_quotient(F.submodule([x, x]))),
    'ideal_intersection': str(R.ideal(x).intersect(R.ideal(y))),
    'ideal_quotient': str(R.ideal(x*y).quotient(R.ideal(x, y))),
    'kernel': str(h.kernel()), 'image': str(h.image()),
    'apply': str(h([1, 1])),
    'quotient_ring': str(R.quotient_ring([x*x-y*y])),
    'quotient_ring_free': str(R.quotient_ring([x*x-y*y]).free_module(2)),
}
path = Path(__file__).resolve().parents[3] / 'packages/symjs/tests/polys/agca/references.json'
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps(references, indent=2) + '\n')

# Independent exact results for nontrivial generating sets and zero columns.
cases = []
for left, right in [
    ([[x, y], [y, x]], [[x+y, x+y]]),
    ([[x, 0], [0, y]], [[y, 0], [0, x]]),
    ([[x, x], [y, y]], [[x*y, x*y]]),
    ([[0, 0], [x, 1], [x*x, x]], [[y, 0]]),
    ([[1, x], [x, x*x], [y, x*y]], [[1, 0], [0, 1]]),
    ([], [[1, 0]]),
]:
    A, B = F.submodule(*left), F.submodule(*right)
    intersection = A.intersect(B)
    # SymPy's quotient implementation raises ValueError for an explicit zero
    # generator. Removing that redundant generator preserves the submodule.
    quotient = F.submodule(*(g for g in left if any(g))).module_quotient(B)
    cases.append({
        'left': [[str(v) for v in g] for g in left],
        'right': [[str(v) for v in g] for g in right],
        'syzygies': [[str(R.to_sympy(v)) for v in g] for g in A.syzygy_module().gens],
        'intersection': [[str(R.to_sympy(v)) for v in g] for g in intersection.gens],
        'quotient': [str(R.to_sympy(v)) for v in quotient.gens],
    })
path.with_name('modules.references.json').write_text(json.dumps(cases, indent=2) + '\n')
