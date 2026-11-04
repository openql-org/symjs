#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Extract a SymPy compatibility corpus from SymPy's own doctests.

For every doctest example in the in-scope modules whose source is a single
call ``f(args...)`` or method call ``obj.m(args...)``, the arguments are
evaluated in the doctest namespace and serialized to a JSON tree. The
expected output is ``str()`` of the result computed by the installed SymPy.

Usage: PYTHONHASHSEED=0 python3 compat/extract.py compat/corpus.json
(the fixed hash seed keeps the order of printed sets reproducible)
"""

import os

os.environ.setdefault("MPLBACKEND", "Agg")  # doctests that plot must not open windows

import ast
import re
import doctest
import signal
import importlib
import json
import sys
import warnings

import sympy
from sympy import Basic, MatrixBase

# module -> category
MODULES = {
    # core
    "sympy.core.add": "core",
    "sympy.core.mul": "core",
    "sympy.core.power": "core",
    "sympy.core.expr": "core",
    "sympy.core.basic": "core",
    "sympy.core.function": "core",
    "sympy.core.numbers": "core",
    "sympy.core.symbol": "core",
    "sympy.core.relational": "core",
    "sympy.core.evalf": "core",
    "sympy.core.exprtools": "core",
    "sympy.core.sympify": "core",
    "sympy.core.intfunc": "core",
    # elementary functions
    "sympy.functions.elementary.complexes": "functions",
    "sympy.functions.elementary.exponential": "functions",
    "sympy.functions.elementary.trigonometric": "functions",
    "sympy.functions.elementary.hyperbolic": "functions",
    "sympy.functions.elementary.miscellaneous": "functions",
    "sympy.functions.elementary.integers": "functions",
    "sympy.functions.elementary.piecewise": "functions",
    # simplification
    "sympy.simplify.simplify": "simplify",
    "sympy.simplify.radsimp": "simplify",
    "sympy.simplify.trigsimp": "simplify",
    "sympy.simplify.powsimp": "simplify",
    "sympy.simplify.ratsimp": "simplify",
    "sympy.simplify.sqrtdenest": "simplify",
    "sympy.polys.rationaltools": "simplify",
    "sympy.polys.partfrac": "simplify",
    # polynomials
    "sympy.polys.polytools": "polys",
    "sympy.polys.polyroots": "polys",
    "sympy.polys.polyfuncs": "polys",
    # solvers
    "sympy.solvers.solvers": "solvers",
    "sympy.solvers.solveset": "solvers",
    "sympy.solvers.ode.ode": "ode",
    "sympy.solvers.recurr": "solvers",
    "sympy.solvers.polysys": "solvers",
    "sympy.solvers.inequalities": "solvers",
    # calculus
    "sympy.integrals.integrals": "calculus",
    "sympy.series.limits": "calculus",
    "sympy.series.series": "calculus",
    "sympy.series.order": "calculus",
    "sympy.concrete.summations": "calculus",
    "sympy.concrete.products": "calculus",
    "sympy.calculus.util": "calculus",
    "sympy.calculus.singularities": "calculus",
    # linear algebra
    "sympy.matrices.matrixbase": "matrices",
    "sympy.matrices.dense": "matrices",
    "sympy.matrices.eigen": "matrices",
    "sympy.matrices.decompositions": "matrices",
    "sympy.matrices.solvers": "matrices",
    "sympy.matrices.determinant": "matrices",
    "sympy.matrices.reductions": "matrices",
    "sympy.matrices.subspaces": "matrices",
    "sympy.matrices.inverse": "matrices",
    # combinatorial / special functions (second tier)
    "sympy.functions.combinatorial.factorials": "special",
    "sympy.functions.combinatorial.numbers": "special",
    "sympy.functions.special.gamma_functions": "special",
    "sympy.functions.special.error_functions": "special",
    # general-purpose packages that many SymPy packages depend on (base candidates)
    "sympy.logic.boolalg": "logic",
    "sympy.logic.inference": "logic",
    "sympy.tensor.array.dense_ndim_array": "tensor",
    "sympy.tensor.array.ndim_array": "tensor",
    "sympy.tensor.array.arrayop": "tensor",
    "sympy.tensor.array.array_derivatives": "tensor",
    "sympy.tensor.indexed": "tensor",
    "sympy.ntheory.factor_": "ntheory",
    "sympy.ntheory.primetest": "ntheory",
    "sympy.ntheory.generate": "ntheory",
    "sympy.ntheory.residue_ntheory": "ntheory",
    "sympy.ntheory.continued_fraction": "ntheory",
    "sympy.ntheory.partitions_": "ntheory",
    "sympy.ntheory.modular": "ntheory",
    "sympy.ntheory.multinomial": "ntheory",
    "sympy.ntheory.digits": "ntheory",
    "sympy.ntheory.egyptian_fraction": "ntheory",
    "sympy.assumptions.ask": "assumptions",
    "sympy.assumptions.refine": "assumptions",
    "sympy.assumptions.assume": "assumptions",
    "sympy.utilities.iterables": "utilities",
    "sympy.combinatorics.permutations": "combinatorics",
    "sympy.printing.pretty.pretty": "printing",
    "sympy.integrals.transforms": "calculus",
    "sympy.integrals.laplace": "calculus",
    "sympy.calculus.accumulationbounds": "calculus",
    "sympy.matrices.expressions.matexpr": "matrices",
    "sympy.matrices.expressions.matmul": "matrices",
    "sympy.matrices.expressions.matadd": "matrices",
    "sympy.matrices.expressions.inverse": "matrices",
    "sympy.matrices.expressions.trace": "matrices",
    "sympy.matrices.expressions.determinant": "matrices",
    "sympy.matrices.expressions.blockmatrix": "matrices",
    "sympy.matrices.expressions.transpose": "matrices",
    # sets
    "sympy.sets.sets": "sets",
    "sympy.sets.fancysets": "sets",
    "sympy.sets.conditionset": "sets",
    "sympy.sets.contains": "sets",
    # special
    "sympy.functions.special.bessel": "special",
    "sympy.functions.special.zeta_functions": "special",
    "sympy.functions.special.hyper": "special",
    "sympy.functions.special.polynomials": "special",
    "sympy.functions.special.delta_functions": "special",
    "sympy.functions.special.beta_functions": "special",
    "sympy.functions.special.elliptic_integrals": "special",
    "sympy.functions.special.spherical_harmonics": "special",
    "sympy.functions.special.tensor_functions": "special",
    "sympy.functions.special.singularity_functions": "special",
    "sympy.functions.special.mathieu_functions": "special",
    # printing
    "sympy.printing.latex": "printing",
    "sympy.printing.str": "printing",
    # core
    "sympy.core.mod": "core",
    "sympy.core.containers": "core",
    "sympy.core.traversal": "core",
    "sympy.core.sorting": "core",
    # simplify
    "sympy.simplify.fu": "simplify",
    "sympy.simplify.cse_main": "simplify",
    "sympy.simplify.hyperexpand": "simplify",
    "sympy.simplify.combsimp": "simplify",
    "sympy.simplify.gammasimp": "simplify",
    "sympy.simplify.epathtools": "simplify",
    # polys
    "sympy.polys.orthopolys": "polys",
    "sympy.polys.specialpolys": "polys",
    "sympy.polys.numberfields.minpoly": "polys",
    "sympy.polys.polyutils": "polys",
    # solvers
    "sympy.solvers.diophantine.diophantine": "solvers",
    # ode
    "sympy.solvers.deutils": "ode",
    "sympy.solvers.ode.systems": "ode",
    # calculus
    "sympy.series.formal": "calculus",
    "sympy.series.fourier": "calculus",
    "sympy.series.limitseq": "calculus",
    "sympy.series.sequences": "calculus",
    "sympy.series.residues": "calculus",
    "sympy.concrete.gosper": "calculus",
    "sympy.concrete.delta": "calculus",
    "sympy.calculus.euler": "calculus",
    "sympy.calculus.finite_diff": "calculus",
    "sympy.integrals.manualintegrate": "calculus",
    "sympy.integrals.meijerint": "calculus",
    "sympy.integrals.heurisch": "calculus",
    "sympy.integrals.risch": "calculus",
    "sympy.integrals.rationaltools": "calculus",
    "sympy.integrals.singularityfunctions": "calculus",
    "sympy.integrals.trigonometry": "calculus",
    "sympy.integrals.deltafunctions": "calculus",
    # matrices
    "sympy.matrices.expressions.hadamard": "matrices",
    "sympy.matrices.expressions.kronecker": "matrices",
    "sympy.matrices.expressions.matpow": "matrices",
    "sympy.matrices.expressions.special": "matrices",
    "sympy.matrices.expressions.diagonal": "matrices",
    "sympy.matrices.expressions.funcmatrix": "matrices",
    "sympy.matrices.expressions.fourier": "matrices",
    "sympy.matrices.expressions.permutation": "matrices",
    "sympy.matrices.expressions.dotproduct": "matrices",
    "sympy.matrices.expressions.adjoint": "matrices",
    "sympy.matrices.expressions.slice": "matrices",
    "sympy.matrices.expressions.companion": "matrices",
    "sympy.matrices.sparse": "matrices",
    "sympy.matrices.immutable": "matrices",
    "sympy.matrices.normalforms": "matrices",
    # logic
    "sympy.logic.algorithms.dpll2": "logic",
    # combinatorics
    "sympy.combinatorics.partitions": "combinatorics",
    "sympy.combinatorics.subsets": "combinatorics",
    "sympy.combinatorics.graycode": "combinatorics",
    "sympy.combinatorics.prufer": "combinatorics",
    # ntheory
    "sympy.ntheory.qs": "ntheory",
    "sympy.ntheory.ecm": "ntheory",
    "sympy.ntheory.bbp_pi": "ntheory",
    # utilities
    "sympy.utilities.lambdify": "utilities",
    "sympy.utilities.misc": "utilities",
    "sympy.utilities.enumerative": "utilities",
    # tensor
    "sympy.tensor.array.mutable_ndim_array": "tensor",
    "sympy.tensor.array.sparse_ndim_array": "tensor",
    "sympy.tensor.index_methods": "tensor",
    # packages ported to the base module later
    "sympy.discrete.transforms": "discrete",
    "sympy.discrete.convolutions": "discrete",
    "sympy.discrete.recurrences": "discrete",
    "sympy.algebras.quaternion": "algebras",
    "sympy.strategies.core": "strategies",
    "sympy.strategies.rl": "strategies",
    "sympy.strategies.tools": "strategies",
    "sympy.strategies.traverse": "strategies",
    "sympy.strategies.tree": "strategies",
    "sympy.strategies.util": "strategies",
    "sympy.strategies.branch.core": "strategies",
    "sympy.strategies.branch.tools": "strategies",
    "sympy.strategies.branch.traverse": "strategies",
    "sympy.unify.core": "unify",
    "sympy.unify.rewrite": "unify",
    "sympy.unify.usympy": "unify",
    "sympy.geometry.entity": "geometry",
    "sympy.geometry.point": "geometry",
    "sympy.geometry.line": "geometry",
    "sympy.geometry.plane": "geometry",
    "sympy.geometry.polygon": "geometry",
    "sympy.geometry.ellipse": "geometry",
    "sympy.geometry.curve": "geometry",
    "sympy.geometry.parabola": "geometry",
    "sympy.geometry.util": "geometry",
    "sympy.geometry.exceptions": "geometry",
    "sympy.vector.basisdependent": "vector",
    "sympy.vector.coordsysrect": "vector",
    "sympy.vector.deloperator": "vector",
    "sympy.vector.dyadic": "vector",
    "sympy.vector.functions": "vector",
    "sympy.vector.implicitregion": "vector",
    "sympy.vector.integrals": "vector",
    "sympy.vector.kind": "vector",
    "sympy.vector.operators": "vector",
    "sympy.vector.orienters": "vector",
    "sympy.vector.parametricregion": "vector",
    "sympy.vector.point": "vector",
    "sympy.vector.scalar": "vector",
    "sympy.vector.vector": "vector",
}

# subpackages whose public names are not top-level sympy names (sympy.discrete.linrec,
# sympy.strategies.rm_id, sympy.unify.unify, ...): calls of them count as public API calls in
# the modules of that subpackage
SUBPACKAGE_PUBLIC = {
    "sympy.discrete.": ("sympy.discrete", "sympy.discrete.recurrences"),
    "sympy.strategies.branch.": ("sympy.strategies.branch",),
    "sympy.strategies.": ("sympy.strategies",),
    "sympy.unify.": ("sympy.unify",),
    # sympy.vector exports orthogonalize only from sympy.vector.functions
    "sympy.vector.": ("sympy.vector", "sympy.vector.functions"),
}


def subpackage_public(modname):
    """The public names of the subpackage of modname."""
    for prefix, pkgs in SUBPACKAGE_PUBLIC.items():
        if modname.startswith(prefix):
            names = set()
            for pkg in pkgs:
                m = importlib.import_module(pkg)
                # a package's __all__, or the public functions a module defines
                names |= set(getattr(m, "__all__", None) or [n for n in dir(m) if not n.startswith("_") and getattr(getattr(m, n), "__module__", None) == pkg])
            return names
    return set()

ASSUMPTION_KEYS = ["real", "positive", "negative", "nonnegative", "nonpositive", "integer", "commutative", "polar"]


DUMMY_IDS = {}


class Unsupported(Exception):
    pass


def _same_series(diff):
    """The series rebuilt from its function has the same leading terms."""
    try:
        return diff().expand() == 0
    except Exception:
        return False


def ser(o):
    """Serialize a SymPy object (or Python value) into a JSON tree."""
    from sympy import Float, Integer, Rational, Symbol, Tuple
    from sympy.core.relational import Relational

    if o is None or isinstance(o, bool):
        return {"t": "Js", "v": o}
    from sympy.assumptions.assume import AssumptionsContext as _AC
    from sympy.assumptions.ask import AssumptionKeys as _AK
    if isinstance(o, _AC):
        return {"t": "AssumptionsContext", "items": [ser(a) for a in o]}
    if isinstance(o, _AK):
        return {"t": "QKeys"}
    from sympy.ntheory.generate import Sieve as _Sieve
    if isinstance(o, _Sieve):
        return {"t": "Sieve"}
    from sympy.combinatorics import Permutation as _Perm
    from sympy.combinatorics.permutations import Cycle as _Cycle
    if isinstance(o, _Perm):
        return {"t": "Permutation", "array": [int(i) for i in o.array_form]}
    if isinstance(o, _Cycle):
        return {"t": "Cycle", "cycles": [[int(i) for i in c] for c in _Perm(o).cyclic_form], "size": int(o.size)}
    from sympy.tensor.array import NDimArray as _NDA
    if isinstance(o, _NDA):
        return {"t": "NDimArray", "cls": type(o).__name__, "shape": [int(k) for k in o.shape], "flat": [ser(i) for i in o._array] if hasattr(o, "_array") else [ser(o[i]) for i in __import__("itertools").product(*[range(k) for k in o.shape])]}
    if isinstance(o, sympy.Idx):
        return {"t": "Idx", "label": ser(o.label), "lower": ser(o.lower) if o.lower is not None else None, "upper": ser(o.upper) if o.upper is not None else None}
    from sympy.logic.inference import PropKB as _PropKB
    if isinstance(o, _PropKB):
        return {"t": "PropKB", "clauses": [ser(c) for c in sorted(o.clauses, key=sympy.default_sort_key)]}
    if isinstance(o, (sympy.Not, sympy.Xor, sympy.Implies, sympy.Equivalent, sympy.Nand, sympy.Nor, sympy.logic.boolalg.Xnor, sympy.ITE)):
        return {"t": "Logic", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    if isinstance(o, int):
        return {"t": "Rational", "p": str(o), "q": "1"}
    if isinstance(o, float):
        return {"t": "Float", "v": o, "py": True}
    if isinstance(o, str):
        return {"t": "Str", "v": o}
    import types as _types
    if isinstance(o, (_types.GeneratorType, zip, map, filter)) or type(o).__name__.endswith("iterator"):
        # iterators are materialized (their values are what the call sees)
        return {"t": "Tuple", "items": [ser(i) for i in list(o)], "list": True}
    if isinstance(o, (_types.FunctionType, _types.BuiltinFunctionType)):
        # a library function passed as an argument (equal_valued, factor, math.isclose, ...)
        mod = getattr(o, "__module__", "") or ""
        if mod.startswith("sympy") or mod == "math":
            return {"t": "JsFunc", "name": ("math." if mod == "math" else "") + o.__name__}
        raise Unsupported("function")
    from sympy.calculus.accumulationbounds import AccumulationBounds as _AB
    if isinstance(o, _AB):
        return {"t": "AccumBounds", "min": ser(o.min), "max": ser(o.max)}
    if (type(o).__module__ or "").startswith("sympy.vector."):
        return ser_vector(o)
    from sympy.geometry.entity import GeometryEntity as _GE
    if isinstance(o, _GE):
        # rebuilt by the class constructor from its arguments
        return {"t": "Geom", "cls": type(o).__name__, "args": [ser(a) for a in o.args]}
    if isinstance(o, sympy.Indexed):
        return {"t": "Indexed", "base": ser(o.base.label), "indices": [ser(i) for i in o.indices]}
    if isinstance(o, sympy.IndexedBase):
        return {"t": "IndexedBase", "label": ser(o.label)}
    if isinstance(o, sympy.CRootOf):
        return {"t": "CRootOf", "poly": ser(o.expr), "index": int(o.index)}
    if isinstance(o, sympy.RootSum):
        return {"t": "RootSum", "poly": ser(o.expr), "fun": ser(o.fun), "var": ser(o.poly.gen)}
    if isinstance(o, sympy.MatrixSymbol):
        return {"t": "MatrixSymbol", "name": o.name, "rows": ser(o.shape[0]), "cols": ser(o.shape[1])}
    if (isinstance(o, sympy.MatrixExpr) or (type(o).__module__ or "").startswith("sympy.matrices.expressions")) and not isinstance(o, MatrixBase):
        name = type(o).__name__
        if name == "MatrixSlice":
            sl = lambda t: [ser(t[0]), ser(t[1]), ser(t[2])]
            return {"t": "MatExpr", "cls": name, "args": [ser(o.args[0])], "slices": [sl(o.args[1]), sl(o.args[2])]}
        return {"t": "MatExpr", "cls": name, "args": [ser(a) for a in o.args]}
    if isinstance(o, (set, frozenset)):
        return {"t": "JsSet", "items": [ser(i) for i in o]}
    if isinstance(o, list):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, range):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, (tuple, Tuple)):
        return {"t": "Tuple", "items": [ser(i) for i in o]}
    if isinstance(o, dict):
        return {"t": "Dict", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, MatrixBase):
        return {"t": "Matrix", "rows": [[ser(o[i, j]) for j in range(o.cols)] for i in range(o.rows)], "shape": [o.rows, o.cols]}
    from sympy.core.function import UndefinedFunction as _UF
    if isinstance(o, _UF):
        return {"t": "UFnClass", "name": o.__name__}
    if isinstance(o, sympy.polys.polytools.GroebnerBasis):
        return {"t": "Groebner", "exprs": [ser(e) for e in o.exprs], "gens": [ser(g) for g in o.gens], "order": str(o.order)}
    if isinstance(o, sympy.Poly):
        return {"t": "Poly", "expr": ser(o.as_expr()), "gens": [ser(g) for g in o.gens], "domain": str(o.get_domain()), "pure": isinstance(o, sympy.PurePoly)}
    if isinstance(o, type) and issubclass(o, Basic) and not isinstance(o, sympy.FunctionClass):
        return {"t": "Type", "name": o.__name__}
    if isinstance(o, type) and o.__name__ in ("Matrix", "MutableDenseMatrix", "ImmutableMatrix", "ImmutableDenseMatrix"):
        return {"t": "Type", "name": "Matrix"}
    from sympy.core.function import WildFunction as _WF
    if isinstance(o, sympy.FunctionClass) and not isinstance(o, _UF):
        return {"t": "FnClass", "name": o.__name__}
    from sympy.polys.domains.domain import Domain as _Domain
    if isinstance(o, _Domain) and str(o) in ("ZZ", "QQ"):
        return {"t": "Domain", "name": str(o)}
    from sympy.utilities.enumerative import MultisetPartitionTraverser as _MPT
    if type(o) is _MPT:
        # a stateless helper object: constructed anew
        return {"t": "New", "cls": "MultisetPartitionTraverser"}
    if not isinstance(o, Basic):
        raise Unsupported(type(o).__name__)
    from sympy.algebras.quaternion import Quaternion as _Q
    if isinstance(o, _Q):
        return {"t": "Quaternion", "args": [ser(a) for a in o.args], "realField": bool(o.real_field),
                "norm": None if o._norm is None else ser(o._norm)}
    if type(o) is Basic:
        # a bare Basic node (the strategies and unify doctests build trees of them)
        return {"t": "Basic", "args": [ser(a) for a in o.args]}
    from sympy.series.fourier import FourierSeries as _FS
    from sympy.series.formal import FormalPowerSeries as _FPS
    if type(o) is _FS:
        # rebuilt by fourier_series(f, (x, a, b)), which a shifted or scaled series is not
        x, a, b = o.args[1]
        if not _same_series(lambda: sympy.fourier_series(o.function, o.args[1]).truncate(8) - o.truncate(8)):
            raise Unsupported("FourierSeries")
        return {"t": "FourierSeries", "f": ser(o.function), "x": ser(x), "a": ser(a), "b": ser(b)}
    if type(o) is _FPS:
        # rebuilt by fps(f, x, x0, dir)
        if not _same_series(lambda: sympy.fps(o.function, o.x, o.x0, o.dir).polynomial(8) - o.polynomial(8)):
            raise Unsupported("FormalPowerSeries")
        return {"t": "FormalPowerSeries", "f": ser(o.function), "x": ser(o.x), "x0": ser(o.x0), "dir": "+" if o.dir == 1 else "-"}
    from sympy.series import sequences as _seqs
    if o is sympy.S.EmptySequence:
        return {"t": "EmptySequence"}
    if type(o) in (_seqs.SeqFormula, _seqs.SeqPer):
        x, start, stop = o.args[1]
        items = [ser(i) for i in o.periodical] if type(o) is _seqs.SeqPer else [ser(o.formula)]
        return {"t": type(o).__name__, "items": items, "x": ser(x), "start": ser(start), "stop": ser(stop)}
    if type(o) in (_seqs.SeqAdd, _seqs.SeqMul):
        return {"t": "SeqOp", "op": type(o).__name__, "args": [ser(a) for a in o.args]}
    if type(o) is _seqs.RecursiveSeq:
        return {"t": "RecursiveSeq", "recurrence": ser(o.args[0]), "yn": ser(o.yn), "n": ser(o.n),
                "initial": [ser(i) for i in o.initial], "start": ser(o.start)}
    if isinstance(o, sympy.ImageSet):
        return {"t": "ImageSet", "lamda": ser(o.lamda), "sets": [ser(i) for i in o.base_sets]}
    if isinstance(o, sympy.ConditionSet):
        return {"t": "ConditionSet", "sym": ser(o.sym), "condition": ser(o.condition), "base": ser(o.base_set)}
    if isinstance(o, sympy.AlgebraicNumber):
        return {"t": "AlgebraicNumber", "root": ser(o.root), "coeffs": [ser(c) for c in o.coeffs()]}
    if isinstance(o, sympy.Interval):
        return {"t": "Interval", "a": ser(o.start), "b": ser(o.end), "lo": bool(o.left_open), "ro": bool(o.right_open)}
    if isinstance(o, sympy.FiniteSet):
        return {"t": "FiniteSet", "items": [ser(i) for i in o.args]}
    if isinstance(o, (sympy.Union, sympy.Intersection, sympy.Complement)):
        return {"t": "SetOp", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    named_sets = {sympy.S.Reals: "Reals", sympy.S.Integers: "Integers", sympy.S.Naturals: "Naturals",
                  sympy.S.Naturals0: "Naturals0", sympy.S.Complexes: "Complexes", sympy.S.EmptySet: "EmptySet",
                  sympy.S.UniversalSet: "UniversalSet"}
    for k, v in named_sets.items():
        if o is k:
            return {"t": "NamedSet", "name": v}
    if isinstance(o, (sympy.And, sympy.Or)):
        return {"t": "BoolOp", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    if isinstance(o, sympy.Not) and isinstance(o.args[0], sympy.AppliedPredicate):
        return {"t": "BoolOp", "op": "Not", "args": [ser(o.args[0])]}
    if isinstance(o, sympy.AppliedPredicate):
        return {"t": "Pred", "name": str(o.function).removeprefix("Q."), "args": [ser(a) for a in o.arguments]}
    if isinstance(o, sympy.Wild):
        props = []
        for f in o.properties:
            # only predicates of the form lambda k: k.is_X
            names = getattr(getattr(f, "__code__", None), "co_names", ())
            if len(names) != 1 or not names[0].startswith("is_"):
                raise Unsupported("Wild properties")
            props.append(names[0])
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        return {"t": "Wild", "name": o.name, "exclude": [ser(e) for e in o.exclude], "assume": a, "props": props}
    if isinstance(o, _WF):
        nargs = o.nargs
        lst = None if nargs == sympy.S.Naturals0 else sorted(int(n) for n in nargs)
        return {"t": "WildFunction", "name": o.name, "nargs": lst}
    if isinstance(o, sympy.Dummy):
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        # indices are renumbered per case so that the corpus is reproducible
        idx = DUMMY_IDS.setdefault(o.dummy_index, len(DUMMY_IDS))
        # a default name carries the global index, which depends on what ran before
        name = f"Dummy_{idx}" if o.name == f"Dummy_{o.dummy_index}" else o.name
        return {"t": "Dummy", "name": name, "index": idx, "assume": a}
    if o.is_Symbol and type(o) is Symbol:
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        if o._assumptions_orig.get("zero") is False:
            a["zero"] = False
        if o._assumptions_orig.get("commutative") is False:
            a["commutative"] = False
        a.pop("commutative", None) if a.get("commutative") is True else None
        return {"t": "Symbol", "name": o.name, "assume": a}
    if isinstance(o, (Integer, Rational)) and o.is_Rational:
        return {"t": "Rational", "p": str(o.p), "q": str(o.q)}
    if isinstance(o, Float):
        sgn, man, exp, _bc = o._mpf_
        return {"t": "Float", "v": float(o), "man": str(-man if sgn else man), "exp": int(exp), "prec": int(o._prec)}
    named = {sympy.pi: "pi", sympy.E: "E", sympy.I: "I", sympy.oo: "oo", -sympy.oo: "-oo", sympy.zoo: "zoo", sympy.nan: "nan",
             sympy.EulerGamma: "EulerGamma", sympy.Catalan: "Catalan", sympy.GoldenRatio: "GoldenRatio",
             sympy.TribonacciConstant: "TribonacciConstant"}
    for k, v in named.items():
        if o == k and type(o) is type(k):
            return {"t": "Const", "name": v}
    from sympy.core.function import AppliedUndef, UndefinedFunction
    if isinstance(o, UndefinedFunction):
        return {"t": "UFnClass", "name": o.__name__}
    if isinstance(o, AppliedUndef):
        return {"t": "UFn", "name": type(o).__name__, "args": [ser(a) for a in o.args]}
    if isinstance(o, sympy.Subs):
        return {"t": "Subs", "expr": ser(o.expr), "vars": [ser(v) for v in o.variables], "point": [ser(p) for p in o.point]}
    if isinstance(o, sympy.Derivative):
        return {"t": "Derivative", "expr": ser(o.expr), "vc": [[ser(v), int(n)] for v, n in o.variable_count]}
    if o is sympy.true or o is sympy.false:
        return {"t": "Js", "v": bool(o)}
    if isinstance(o, Relational):
        return {"t": "Rel", "op": type(o).__name__, "args": [ser(a) for a in o.args]}
    name = type(o).__name__
    if o.is_Add or o.is_Mul or o.is_Pow:
        return {"t": name, "args": [ser(a) for a in o.args]}
    if isinstance(o, sympy.exp):
        return {"t": "Fn", "name": "exp", "args": [ser(a) for a in o.args]}
    if isinstance(o, (sympy.Sum, sympy.Product)):
        return {"t": "Fn", "name": name, "args": [ser(o.function)] + [ser(tuple(l)) for l in o.limits]}
    if o.is_Function or name in ("Piecewise", "Integral", "Derivative", "Limit", "Order", "Sum", "Product"):
        return {"t": "Fn", "name": name, "args": [ser(a) for a in o.args]}
    raise Unsupported(name)


def ser_vector(o):
    """Serialize a sympy.vector object: rebuilt by its class constructor from its arguments."""
    from sympy.core.symbol import Str
    name = type(o).__name__
    if name == "CoordSys3D":
        tr = o._transformation
        tr = {"t": "Str", "v": tr.name} if isinstance(tr, Str) else ser(tr)
        return {"t": "Vec", "cls": name, "name": o._name, "transformation": tr,
                "parent": None if o._parent is None else ser(o._parent),
                "vectorNames": list(o._vector_names), "variableNames": list(o._variable_names)}
    if name == "Del":
        return {"t": "Vec", "cls": name, "args": []}
    return {"t": "Vec", "cls": name, "args": [{"t": "Str", "v": a.name} if isinstance(a, Str) else ser(a) for a in o.args]}


import sympy.combinatorics as _combinatorics
PUBLIC = set(sympy.__all__) | {"Permutation", "Cycle"}
setattr(sympy, "Permutation", _combinatorics.Permutation)
setattr(sympy, "Cycle", _combinatorics.permutations.Cycle)


def api_inventory():
    """In-scope public API: top-level names from the in-scope modules plus public Expr/Matrix methods."""
    out = []
    for name in sorted(PUBLIC):
        obj = getattr(sympy, name)
        mod = getattr(obj, "__module__", None) or ""
        cat = MODULES.get(mod)
        if cat is None:
            # also accept submodules of an in-scope package (e.g. sympy.solvers.ode.*)
            for m, c in MODULES.items():
                if mod.startswith(m + "."):
                    cat = c
        if cat:
            out.append({"name": name, "category": cat})
    import sympy.vector as _vector
    for name in sorted(_vector.__all__):
        # sympy.vector is a subpackage whose names are not top-level sympy names
        out.append({"name": name, "category": "vector"})
    owners = ((sympy.Expr, "core"), (sympy.Matrix, "matrices"), (sympy.ImmutableDenseNDimArray, "tensor"),
              (_combinatorics.Permutation, "combinatorics"), (sympy.MatrixExpr, "matrices"))
    for cls, cat in owners:
        for name in sorted(dir(cls)):
            if name.startswith("_"):
                continue
            attr = getattr(cls, name, None)
            if callable(attr):
                out.append({"name": "." + name, "category": cat, "owner": cls.__name__})
    return out


class Timeout(Exception):
    pass


def ser_arg(node, globs):
    """Serialize a call argument; a lambda whose body evaluates to an expression
    when applied to dummies becomes {"t": "JsLambda", params, body}."""
    if isinstance(node, ast.Lambda) and not node.args.vararg and not node.args.kwonlyargs and not node.args.kwarg:
        names = [a.arg for a in node.args.args]
        b = node.body
        if (len(names) == 1 and isinstance(b, ast.Attribute) and isinstance(b.value, ast.Name)
                and b.value.id == names[0] and b.attr.startswith("is_")):
            # a predicate such as lambda e: e.is_Mul
            return {"t": "JsPred", "attr": b.attr}
        ds = [sympy.Dummy(n) for n in names]
        loc = dict(globs)
        loc.update(zip(names, ds))
        try:
            body = eval(compile(ast.Expression(node.body), "<lambda>", "eval"), loc)
        except Exception:
            raise Unsupported("function")
        if not isinstance(body, Basic) or isinstance(body, sympy.logic.boolalg.BooleanAtom):
            raise Unsupported("function")
        return {"t": "JsLambda", "params": [ser(d) for d in ds], "body": ser(body)}
    return ser(eval(compile(ast.Expression(node), "<a>", "eval"), globs))


# per-example limit, generous so that the corpus does not depend on the machine load
ALARM_SECONDS = 30


def _alarm(signum, frame):
    raise Timeout()


def main(dst):
    import random
    random.seed(0)  # randMatrix and friends: keep the corpus reproducible
    warnings.filterwarnings("ignore")
    signal.signal(signal.SIGALRM, _alarm)
    finder = doctest.DocTestFinder(exclude_empty=True)
    cases = []
    skipped = {}
    for modname, category in MODULES.items():
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        extra_public = subpackage_public(modname)
        for test in finder.find(mod):
            globs = {}
            exec("from sympy import *", globs)
            for ex in test.examples:
                src = ex.source.strip()
                if ex.options.get(doctest.SKIP):
                    # SymPy does not run these either (random or illustrative output)
                    continue
                if re.fullmatch(r"[\w.]+\(\.\.\.\)", ex.want.strip()):
                    # only the class of the result is shown (random output elided with ELLIPSIS)
                    continue
                try:
                    tree = ast.parse(src, mode="eval")
                except SyntaxError:
                    # statements (assignments, imports): just execute
                    try:
                        signal.alarm(ALARM_SECONDS)
                        exec(compile(src, "<doctest>", "exec"), globs)
                    except (Exception, Timeout):
                        pass
                    finally:
                        signal.alarm(0)
                    continue
                call = tree.body
                record = None
                if isinstance(call, ast.Call) and not any(isinstance(a, ast.Starred) for a in call.args):
                    if isinstance(call.func, ast.Name):
                        record = {"fn": call.func.id}
                    elif isinstance(call.func, ast.Attribute):
                        record = {"fn": "." + call.func.attr, "selfSrc": ast.unparse(call.func.value)}
                from sympy.assumptions import global_assumptions as _ga
                assumed = list(_ga)
                try:
                    signal.alarm(ALARM_SECONDS)
                    result = eval(compile(tree, "<doctest>", "eval"), globs)
                except (Exception, Timeout):
                    continue
                finally:
                    signal.alarm(0)
                if record is None or "print" in record["fn"] or record["fn"] in ("str", "srepr", "latex", "repr"):
                    continue
                fn = record["fn"]
                # only the public API: top-level sympy names and public methods
                if fn.startswith("."):
                    if fn[1:].startswith("_"):
                        continue
                elif (fn not in PUBLIC and fn not in extra_public) or fn in globs and getattr(globs[fn], "__module__", "").startswith("__"):
                    continue
                DUMMY_IDS.clear()
                try:
                    if "selfSrc" in record:
                        record["self"] = ser(eval(record.pop("selfSrc"), globs))
                    record["args"] = [ser_arg(a, globs) for a in call.args]
                    record["kwargs"] = {k.arg: ser_arg(k.value, globs) for k in call.keywords}
                    if assumed:
                        # the global assumptions in force (SymPy global_assumptions)
                        record["assume"] = [ser(a) for a in assumed]
                except Unsupported as e:
                    # keep the case (it counts as a failure) so the rate is not inflated
                    skipped[str(e)] = skipped.get(str(e), 0) + 1
                    record.pop("selfSrc", None)
                    record["unsupportedArg"] = str(e)
                except Exception:
                    continue
                from sympy.polys.monomials import Monomial as _Monomial
                if isinstance(result, (MatrixBase,)):
                    expected = str(result)
                elif isinstance(result, tuple) and any(isinstance(i, _Monomial) for i in result):
                    # a Monomial's repr is its address; its str is x**2*y**0
                    expected = "(" + ", ".join(str(i) for i in result) + ")"
                elif isinstance(result, (Basic, list, tuple, dict, set, int, float, bool)) or result is None:
                    expected = str(result)
                else:
                    continue
                if "\n" in expected:
                    continue
                record.update({"category": category, "module": modname, "src": src, "expected": expected})
                cases.append(record)
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "api": api_inventory(), "cases": cases}, f, indent=1, ensure_ascii=False)
        f.write("\n")
    by_cat = {}
    for c in cases:
        by_cat[c["category"]] = by_cat.get(c["category"], 0) + 1
    print(f"TOTAL {len(cases)} cases", by_cat, file=sys.stderr)
    print("skipped (unsupported arg types):", dict(sorted(skipped.items(), key=lambda kv: -kv[1])[:15]), file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1])
