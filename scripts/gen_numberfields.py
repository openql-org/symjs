"""Regenerate the references of the number-field modules (sympy.polys.numberfields.modules, basis,
primes, utilities and the number-field methods of AlgebraicField) with SymPy 1.14.0.

Polynomials are written as strings in x; results are compared by str() and repr().
"""
import json
from pathlib import Path

import sympy
from sympy import Poly, QQ, ZZ, FF, cyclotomic_poly, symbols, sqrt, AlgebraicNumber
from sympy.polys.matrices import DM, DomainMatrix
from sympy.polys.numberfields.basis import round_two, nilradical_mod_p
from sympy.polys.numberfields.modules import PowerBasis, to_col, find_min_poly, ModuleHomomorphism, ModuleEndomorphism
from sympy.polys.numberfields.primes import prime_decomp, prime_valuation, _two_elt_rep
from sympy.polys.numberfields.utilities import AlgIntPowers, coeff_search, supplement_a_subspace
from sympy.polys.numberfields.basis import _apply_Dedekind_criterion
from sympy.polys.numberfields.utilities import extract_fundamental_discriminant
from sympy.ntheory import primefactors
from sympy.polys.polyerrors import CoercionFailed

assert sympy.__version__ == '1.14.0'

# SymPy asserts that the kernel N of x -> x**p - x starts with 1, which fails when the nullspace basis vector
# of 1 is a multiple of it (prime_decomp(7, Poly(x**2 - 588))); symjs splits with the first basis vector of N
# that is not a multiple of 1, which is N(1) whenever SymPy's assertion holds. The references use the same rule.
import sympy.polys.numberfields.primes as _primes
from sympy.polys.numberfields.modules import ModuleEndomorphism as _ME
_orig_split = _primes._prime_decomp_split_ideal


def _compute_kernel(I, p, ZK):
    W = I.matrix
    n, r = W.shape
    B = W.eye(n, ZZ) if r == 0 else W.hstack(W.eye(n, ZZ)[:, 0])
    if B.shape[1] < n:
        B = supplement_a_subspace(B.convert_to(FF(p))).convert_to(ZZ)
    G = ZK.submodule_from_matrix(B)
    G.compute_mult_tab()
    G = G.discard_before(r)
    N = _ME(G, lambda y: y**p - y).kernel(modulus=p)
    return N, G


def _split(I, p, N, G, ZK):
    j = next(j for j in range(N.n) if any(c != 0 for c in N.matrix[:, j].flat()[1:]))
    return _orig_split(I, p, _Shift(N, j), G, ZK)


class _Shift:
    # N with N(1) the j-th basis vector (the original split reads only N(1))
    def __init__(self, N, j):
        self.N, self.j = N, j

    def __call__(self, k):
        return self.N(self.j if k == 1 else k)

    @property
    def parent(self):
        return self.N.parent


_primes._prime_decomp_compute_kernel = _compute_kernel
_primes._prime_decomp_split_ideal = _split
x, zeta, theta = symbols('x zeta theta')


def col(e):
    return [str(c) for c in e.coeffs], str(e.denom)


def radicals_reliable(T):
    """SymPy stores its last nilradical under the last prime of the loop: only reliable when that prime is the
    last one with a second enlargement (see basis.ts)."""
    _, F = extract_fundamental_discriminant(T.discriminant())
    order = list(F.items())[::-1]
    second = [p for p, e in order if (lambda m: m != 0 and e > m)(_apply_Dedekind_criterion(T, p)[1])]
    return not second or second[-1] == order[-1][0]


POLYS = [
    x**3 + x**2 - 2*x + 8, x**2 - 5, x**2 + 3, x**2 + 1, x**2 - 588, cyclotomic_poly(5, x), cyclotomic_poly(7, x),
    cyclotomic_poly(8, x), cyclotomic_poly(9, x), cyclotomic_poly(12, x), x**3 - 2, x**3 - 10, x**3 - 19,
    x**3 + 15*x**2 - 9*x + 13, x**4 - 10*x**2 + 1, x**3 + 3*x**2 + 5, x**4 + 4*x**2 + 2, x**3 - x - 1, x**4 - 2,
    x**3 - 30*x - 16,
]
fields = []
for f in POLYS:
    T = Poly(f, x)
    rad = {}
    ZK, dK = round_two(T, radicals=rad)
    reliable = radicals_reliable(T)
    dT = T.discriminant()
    primes = []
    for p in sorted(set(primefactors(dT)) | {2, 3, 5, 7, 11}):
        # where SymPy's stored radical is not reliable, the radical is computed (as symjs does)
        radical = None if reliable else nilradical_mod_p(ZK, p)
        P = prime_decomp(p, T, ZK=ZK, dK=dK, radical=radical) if not reliable else prime_decomp(p, T)
        ideals = []
        for Q in P:
            ideals.append({
                'repr': repr(Q), 'str': str(Q), 'gens': Q.repr(field_gen=theta, just_gens=True), 'e': Q.e, 'f': Q.f,
                'inert': Q.is_inert, 'alpha': col(Q.alpha), 'test_factor': col(Q.test_factor()),
                'submodule': str(Q.as_submodule()), 'square': str(Q**2), 'sum': str(Q + p*ZK),
                # v_Q(R) is 1 for R = Q and 0 for the other primes; v_Q(p**2*ZK) = 2e (SymPy's prime_valuation
                # raises CoercionFailed for some of these, see primes.ts)
                'valuations': [1 if R == Q else 0 for R in P],
                'valuation_p2': 2 * Q.e,
                'reduce': str(Q.reduce_element(ZK.parent(to_col(list(range(3, 3 + ZK.n)))))),
            })
        primes.append({'p': p, 'ideals': ideals})
    fields.append({
        'T': str(f), 'ZK': str(ZK), 'dK': str(dK), 'radicals': {str(p): str(r) for p, r in rad.items()} if reliable else None,
        'multab': [[ZK.mult_tab()[u][v] for v in range(u, ZK.n)] for u in range(ZK.n)], 'primes': primes,
    })

# non-monic polynomials: round_two scales the roots (the primes are computed for the monic polynomial)
nonmonic = []
for f in [2*x**2 - 3, 3*x**3 - 2, 9*x**2 - 2, x**2/4 - QQ(3, 2)]:
    T = Poly(f, x)
    ZK, dK = round_two(T)
    nonmonic.append({'T': str(f), 'ZK': str(ZK), 'dK': str(dK), 'parent': str(ZK.parent)})

# algebraic fields
def alg_basis(K):
    try:
        return [str(b.as_expr()) for b in K.integral_basis(fmt='alg')]
    except CoercionFailed:
        return None


algebraic = []
for name, K in [
    ('sqrt5', QQ.algebraic_field(sqrt(5))),
    ('sqrt2_sqrt3', QQ.algebraic_field(sqrt(2), sqrt(3))),
    ('alpha', QQ.algebraic_field(AlgebraicNumber(sqrt(5), alias='alpha'))),
    ('theta', QQ.algebraic_field((Poly(x**3 + x**2 - 2*x + 8), theta))),
    ('zeta7', QQ.algebraic_field((Poly(cyclotomic_poly(7, x)), zeta))),
    ('cyc5', QQ.cyclotomic_field(5)),
]:
    B = K.integral_basis()
    algebraic.append({
        'name': name, 'K': str(K), 'ZK': str(K.maximal_order()), 'dK': str(K.discriminant()),
        'basis': [str(b) for b in B], 'sympy': [str(b) for b in K.integral_basis(fmt='sympy')],
        # SymPy's to_alg_num fails for a field given by an integer polynomial and a symbol (1/2 is not in ZZ):
        # the algebraic numbers are then checked against the expressions
        'alg': alg_basis(K),
        'primes': {str(p): [repr(P) for P in K.primes_above(p)] for p in (2, 3, 5, 7)},
    })

# modules
T5 = Poly(cyclotomic_poly(5, x))
A = PowerBasis(T5)
B = A.submodule_from_matrix(2 * DomainMatrix.eye(4, ZZ), denom=3)
C = A.submodule_from_matrix(3 * DomainMatrix.eye(4, ZZ))
e = A(to_col([0, 2, 0, 0]), denom=3)
f_ = A(to_col([0, 0, 0, 7]), denom=5)
g = C(to_col([1, 1, 1, 1]))
h = A(to_col([1, 2, 3, 4]), denom=6)
D = B.submodule_from_matrix(DM([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 1, 1]], ZZ).transpose())
d = D(to_col([1, 2, 3, 4]))
k = QQ.alg_field_from_poly(Poly(x**3 + x**2 - 2*x + 8))
Zk = k.maximal_order()
Ak = Zk.parent
Bk = (Ak(2) - 3*Ak(0))*Zk
gens = [A(0), 2*A(1), 3*A(2), 4*A(3)//5]
modules = {
    'A': str(A), 'B': str(B), 'multab': [[A.mult_tab()[u][v] for v in range(u, 4)] for u in range(4)],
    'ops': {
        'e+f': str(e + f_), 'e-f': str(e - f_), 'e-g': str(e - g), 'e+7/10': str(e + QQ(7, 10)), 'e*f': str(e * f_),
        'e**2': str(e**2), 'e**0': str(e**0), 'e**5': str(e**5), 'e**-2': str(e**-2), 'f//g': str(f_ // g), 'f*2/3': str(f_ * QQ(2, 3)),
        'f//3': str(f_ // 3), 'h.reduced': str(h.reduced()), 'h%2': str(h % 2), 'g*g': str(g * g), 'g+1': str(g + 1),
        'd+h': str(d + h), 'd*e': str(d * e), 'd.to_parent': str(d.to_parent()), 'd.over': str(d.over_power_basis()),
        'h.mod3': str(h.reduced_mod_p(3)), 'B(1)': str(B(1)), 'B(1)+B(2)': str(B(1) + B(2)),
    },
    'h_poly': str(h.poly().as_expr()), 'h_numerator': str(h.numerator().as_expr()), 'h_norm': str(sympy.Rational(int(T5.resultant(h.numerator())), h.denom**4)),  # SymPy floors it (see modules.ts)
    'h_inverse': str(h.inverse()), 'h_anp': str(h.to_ANP()), 'h_rational': h.is_rational,
    'g_equiv': [g.equiv(A(to_col([3, 3, 3, 3]))), g.equiv(e), (A(0) * 3).equiv(3), (C(0) * 1).equiv(3)],
    'B_represent': str(B.represent(A(to_col([2, 4, 6, 8]), denom=3))),
    'D_represent': str(D.represent(A(to_col([2, 4, 6, 8]), denom=3))),
    'gens': str(A.submodule_from_gens(gens)), 'gens_nohnf': str(A.submodule_from_gens(gens, hnf=False)),
    'gens_mod': str(A.submodule_from_gens([2*A(i) for i in range(4)], hnf_modulus=16)),
    'B+C': str(B + C), 'B*C': str(B * C), 'B*e': str(B * e), 'B*2/3': str(B * QQ(2, 3)), 'B**2': str(B**2), 'B**3': str(B**3),
    'B_reduced': str(A.submodule_from_matrix(6 * DomainMatrix.eye(4, ZZ), denom=4).reduced()),
    'C_discard': str(C.discard_before(2)), 'C_discard_multab': [[C.discard_before(2).mult_tab()[u][v] for v in range(u, 2)] for u in range(2)],
    'C_multab': [[C.mult_tab()[u][v] for v in range(u, 4)] for u in range(4)],
    'B_eq_C': B == C, 'B_eq_B': B == A.submodule_from_matrix(2 * DomainMatrix.eye(4, ZZ), denom=3),
    'Bk_reduce': str(Bk.reduce_element(Ak(2))), 'Bk': str(Bk),
    'endo': str(ModuleEndomorphism(A, lambda y: y * A(1)).matrix()),
    'endo_mod': [[int(v) for v in r] for r in ModuleEndomorphism(A, lambda y: y * A(1)).matrix(modulus=3).to_list()],
    'kernel': str(ModuleEndomorphism(A, lambda y: y**5).kernel(modulus=5)),
    'kernel_qq': str(ModuleHomomorphism(A, A, lambda y: y * (A(0) - A(1))).kernel()),
    'endring': str(A.endomorphism_ring().represent(A.endomorphism_ring().inner_endomorphism(A(1))).transpose()),
}
n13 = 13
C13 = PowerBasis(Poly(cyclotomic_poly(n13, x)))
eta = sum(C13(gg) for gg in [2**(2*kk+1) % n13 for kk in range(6)])
pw = []
minpolys = {
    'eta': str(find_min_poly(eta, QQ, x=x, powers=pw).as_expr()), 'eta_powers': [str(q) for q in pw],
    'zeta2': str(find_min_poly(A(2), QQ, x=x).as_expr()), 'one': str(find_min_poly(A(0), QQ, x=x).as_expr()),
    'ff': str(find_min_poly(A(1) + A(2), FF(7), x=x).as_expr()),
}

utilities = {
    'powers': [AlgIntPowers(T5)[i] for i in range(12)],
    'powers_mod': [AlgIntPowers(Poly(x**3 - 2*x + 7), 5)[i] for i in range(9)],
    'search': [c for c, _ in zip(coeff_search(2, 1), range(30))],
    'search3': [c for c, _ in zip(coeff_search(3, 2), range(40))],
    'supplement': str(supplement_a_subspace(DM([[1, 7, 0], [2, 3, 4]], QQ).transpose()).to_Matrix()),
    'supplement_ff': str(supplement_a_subspace(DM([[1, 7, 0], [2, 3, 4]], QQ).transpose().convert_to(FF(7))).to_Matrix()),
}

out = {'fields': fields, 'nonmonic': nonmonic, 'algebraic': algebraic, 'modules': modules, 'minpolys': minpolys, 'utilities': utilities}
path = Path(__file__).resolve().parents[1] / 'packages/symjs/tests/polys/numberfields/numberfields.references.json'
path.write_text(json.dumps(out, indent=1, default=str) + '\n')
