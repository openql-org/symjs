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
import contextlib
import io
import types
import re
import doctest
import signal
import importlib
import json
import random
import sys
import warnings

import sympy
from sympy import Basic, MatrixBase

# module -> category
MODULES = {
    # Category theory and previously unmeasured mathematical modules remain in
    # the denominator even while their implementations are incomplete.
    "sympy.categories.baseclasses": "categories",
    "sympy.polys.numberfields.subfield": "polys",
    "sympy.combinatorics.perm_groups": "combinatorics",
    "sympy.combinatorics.named_groups": "combinatorics",
    "sympy.tensor.tensor": "tensor",
    "sympy.solvers.pde": "pde",
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
    # sympy.stats, part 1: random symbols and the single-variable distributions
    "sympy.stats.rv": "stats",
    "sympy.stats.rv_interface": "stats",
    "sympy.stats.crv": "stats",
    "sympy.stats.crv_types": "stats",
    "sympy.stats.drv": "stats",
    "sympy.stats.drv_types": "stats",
    "sympy.stats.frv": "stats",
    "sympy.stats.frv_types": "stats",
    "sympy.stats.compound_rv": "stats",
    "sympy.stats.error_prop": "stats",
    "sympy.stats.symbolic_probability": "stats",
    # sympy.stats, part 2: joint, matrix and random-matrix distributions, stochastic processes and the
    # symbolic multivariate probability nodes
    "sympy.stats.joint_rv": "stats",
    "sympy.stats.joint_rv_types": "stats",
    "sympy.stats.matrix_distributions": "stats",
    "sympy.stats.random_matrix": "stats",
    "sympy.stats.random_matrix_models": "stats",
    "sympy.stats.stochastic_process": "stats",
    "sympy.stats.stochastic_process_types": "stats",
    "sympy.stats.symbolic_multivariate_probability": "stats",
    # printing: the symbolic printers and the printer framework
    "sympy.printing.repr": "printing",
    "sympy.printing.tree": "printing",
    "sympy.printing.tableform": "printing",
    "sympy.printing.dot": "printing",
    "sympy.printing.mathml": "printing",
    "sympy.printing.precedence": "printing",
    "sympy.printing.printer": "printing",
    "sympy.printing.conventions": "printing",
    "sympy.printing.defaults": "printing",
    "sympy.printing.pretty.pretty_symbology": "printing",
    "sympy.printing.pretty.stringpict": "printing",
    # utilities usable in JavaScript
    "sympy.utilities.decorator": "utilities",
    "sympy.utilities.memoization": "utilities",
    # polys and matrices: the user-level modules, the low-level representation modules, domains,
    # DomainMatrix, agca and numberfields (packages themselves are not selected: api_inventory() would
    # re-attribute the names of their submodules)
    "sympy.matrices.common": "matrices",
    "sympy.matrices.matrices": "matrices",
    "sympy.matrices.repmatrix": "matrices",
    "sympy.matrices.graph": "matrices",
    "sympy.matrices.kind": "matrices",
    "sympy.matrices.exceptions": "matrices",
    "sympy.matrices.utilities": "matrices",
    "sympy.matrices.sparsetools": "matrices",
    "sympy.matrices.expressions.applyfunc": "matrices",
    "sympy.matrices.expressions.factorizations": "matrices",
    "sympy.matrices.expressions.sets": "matrices",
    "sympy.matrices.expressions._shape": "matrices",
    "sympy.polys.appellseqs": "polys",
    "sympy.polys.constructor": "polys",
    "sympy.polys.dispersion": "polys",
    "sympy.polys.fglmtools": "polys",
    "sympy.polys.fields": "polys",
    "sympy.polys.groebnertools": "polys",
    "sympy.polys.heuristicgcd": "polys",
    "sympy.polys.modulargcd": "polys",
    "sympy.polys.monomials": "polys",
    "sympy.polys.multivariate_resultants": "polys",
    "sympy.polys.orderings": "polys",
    "sympy.polys.polyclasses": "polys",
    "sympy.polys.polyconfig": "polys",
    "sympy.polys.polyerrors": "polys",
    "sympy.polys.polymatrix": "polys",
    "sympy.polys.polyoptions": "polys",
    "sympy.polys.polyquinticconst": "polys",
    "sympy.polys.puiseux": "polys",
    "sympy.polys.ring_series": "polys",
    "sympy.polys.rings": "polys",
    "sympy.polys.rootoftools": "polys",
    "sympy.polys.solvers": "polys",
    "sympy.polys.subresultants_qq_zz": "polys",
    "sympy.polys.compatibility": "polys",
    "sympy.polys.domainmatrix": "polys",
    "sympy.polys.densearith": "polys",
    "sympy.polys.densebasic": "polys",
    "sympy.polys.densetools": "polys",
    "sympy.polys.galoistools": "polys",
    "sympy.polys.sqfreetools": "polys",
    "sympy.polys.factortools": "polys",
    "sympy.polys.distributedmodules": "polys",
    "sympy.polys.domains.domain": "polys",
    "sympy.polys.domains.domainelement": "polys",
    "sympy.polys.domains.ring": "polys",
    "sympy.polys.domains.field": "polys",
    "sympy.polys.domains.simpledomain": "polys",
    "sympy.polys.domains.compositedomain": "polys",
    "sympy.polys.domains.characteristiczero": "polys",
    "sympy.polys.domains.integerring": "polys",
    "sympy.polys.domains.rationalfield": "polys",
    "sympy.polys.domains.realfield": "polys",
    "sympy.polys.domains.complexfield": "polys",
    "sympy.polys.domains.mpelements": "polys",
    "sympy.polys.domains.algebraicfield": "polys",
    "sympy.polys.domains.finitefield": "polys",
    "sympy.polys.domains.modularinteger": "polys",
    "sympy.polys.domains.gaussiandomains": "polys",
    "sympy.polys.domains.expressiondomain": "polys",
    "sympy.polys.domains.expressionrawdomain": "polys",
    "sympy.polys.domains.polynomialring": "polys",
    "sympy.polys.domains.fractionfield": "polys",
    "sympy.polys.domains.old_polynomialring": "polys",
    "sympy.polys.domains.old_fractionfield": "polys",
    "sympy.polys.domains.quotientring": "polys",
    "sympy.polys.matrices.domainmatrix": "polys",
    "sympy.polys.matrices.domainscalar": "polys",
    "sympy.polys.matrices.ddm": "polys",
    "sympy.polys.matrices.sdm": "polys",
    "sympy.polys.matrices.dense": "polys",
    "sympy.polys.matrices.eigen": "polys",
    "sympy.polys.matrices.exceptions": "polys",
    "sympy.polys.matrices.linsolve": "polys",
    "sympy.polys.matrices.lll": "polys",
    "sympy.polys.matrices.normalforms": "polys",
    "sympy.polys.matrices.rref": "polys",
    "sympy.polys.agca.extensions": "polys",
    "sympy.polys.agca.homomorphisms": "polys",
    "sympy.polys.agca.ideals": "polys",
    "sympy.polys.agca.modules": "polys",
    "sympy.polys.numberfields.basis": "polys",
    "sympy.polys.numberfields.exceptions": "polys",
    "sympy.polys.numberfields.galois_resolvents": "polys",
    "sympy.polys.numberfields.modules": "polys",
    "sympy.polys.numberfields.primes": "polys",
    "sympy.polys.numberfields.resolvent_lookup": "polys",
    "sympy.polys.numberfields.utilities": "polys",
    # core, assumptions, sets, logic, concrete, crypto, liealgebras, parsing and the other mathematical modules
    "sympy.abc": "core",
    "sympy.core.operations": "core",
    "sympy.core.parameters": "core",
    "sympy.core.random": "core",
    "sympy.core.rules": "core",
    "sympy.core.singleton": "core",
    "sympy.core.facts": "core",
    "sympy.assumptions.cnf": "assumptions",
    "sympy.assumptions.facts": "assumptions",
    "sympy.assumptions.lra_satask": "assumptions",
    "sympy.assumptions.predicates.calculus": "assumptions",
    "sympy.assumptions.predicates.common": "assumptions",
    "sympy.assumptions.predicates.matrices": "assumptions",
    "sympy.assumptions.predicates.ntheory": "assumptions",
    "sympy.assumptions.predicates.order": "assumptions",
    "sympy.assumptions.predicates.sets": "assumptions",
    "sympy.assumptions.relation.binrel": "assumptions",
    "sympy.assumptions.relation.equality": "assumptions",
    "sympy.assumptions.satask": "assumptions",
    "sympy.assumptions.sathandlers": "assumptions",
    "sympy.assumptions.wrapper": "assumptions",
    "sympy.combinatorics.coset_table": "combinatorics",
    "sympy.combinatorics.group_numbers": "combinatorics",
    "sympy.combinatorics.homomorphisms": "combinatorics",
    "sympy.combinatorics.pc_groups": "combinatorics",
    "sympy.combinatorics.schur_number": "combinatorics",
    "sympy.combinatorics.galois": "combinatorics",
    "sympy.concrete.expr_with_intlimits": "calculus",
    "sympy.concrete.expr_with_limits": "calculus",
    "sympy.concrete.guess": "calculus",
    "sympy.crypto.crypto": "crypto",
    "sympy.functions.elementary._trigonometric_special": "functions",
    "sympy.integrals": "calculus",
    "sympy.integrals.intpoly": "calculus",
    "sympy.integrals.quadrature": "calculus",
    "sympy.liealgebras.cartan_matrix": "liealgebras",
    "sympy.liealgebras.cartan_type": "liealgebras",
    "sympy.liealgebras.dynkin_diagram": "liealgebras",
    "sympy.liealgebras.root_system": "liealgebras",
    "sympy.liealgebras.type_a": "liealgebras",
    "sympy.liealgebras.type_b": "liealgebras",
    "sympy.liealgebras.type_c": "liealgebras",
    "sympy.liealgebras.type_d": "liealgebras",
    "sympy.liealgebras.type_e": "liealgebras",
    "sympy.liealgebras.type_f": "liealgebras",
    "sympy.liealgebras.type_g": "liealgebras",
    "sympy.liealgebras.weyl_group": "liealgebras",
    "sympy.logic.algorithms.dpll": "logic",
    "sympy.logic.algorithms.lra_theory": "logic",
    "sympy.logic.utilities.dimacs": "logic",
    "sympy.ntheory.elliptic_curve": "ntheory",
    "sympy.parsing.sympy_parser": "parsing",
    "sympy.parsing.mathematica": "parsing",
    "sympy.series.acceleration": "calculus",
    "sympy.series.approximants": "calculus",
    "sympy.series.kauers": "calculus",
    "sympy.sets.ordinals": "sets",
    "sympy.sets.powerset": "sets",
    "sympy.sets.setexpr": "sets",
    "sympy.solvers": "solvers",
    "sympy.solvers.bivariate": "solvers",
    "sympy.solvers.decompogen": "solvers",
    "sympy.solvers.simplex": "solvers",
    "sympy.solvers.ode.nonhomogeneous": "ode",
    "sympy.solvers.ode.single": "ode",
    "sympy.solvers.ode.subscheck": "ode",
    "sympy.stats": "stats",
    "sympy.tensor.array": "tensor",
    "sympy.tensor.array.array_comprehension": "tensor",
    "sympy.tensor.array.expressions": "tensor",
    "sympy.tensor.array.expressions.array_expressions": "tensor",
    "sympy.tensor.array.expressions.from_array_to_matrix": "tensor",
    "sympy.tensor.array.expressions.from_indexed_to_array": "tensor",
    "sympy.tensor.functions": "tensor",
}

# sympy.categories.diagram_drawing (DiagramGrid, XypicDiagramDrawer, xypic_draw_diagram): drawing category
# diagrams is deferred like plotting, by user decision; the policy is decided later
CATEGORIES_DRAWING = {"DiagramGrid", "XypicDiagramDrawer", "xypic_draw_diagram"}

# names of sympy.stats that need an external sampling library (numpy, scipy, pymc): out of scope
STATS_SAMPLING = {"sample", "sample_iter", "sampling_density", "sample_stochastic_process"}


def stats_public():
    """The public names of sympy.stats defined in the in-scope stats modules (MODULES), without the
    sampling functions."""
    import sympy.stats as _stats
    return {n for n in _stats.__all__ if getattr(getattr(_stats, n), "__module__", "") in MODULES and n not in STATS_SAMPLING}

# subpackages whose public names are not top-level sympy names (sympy.discrete.linrec,
# sympy.strategies.rm_id, sympy.unify.unify, ...): calls of them count as public API calls in
# the modules of that subpackage
# modules whose own public definitions are API of that module (not top-level sympy names): the newly
# selected core/assumptions/logic/... modules and modules whose documented functions live in the module only
# (deltasummation, gosper_sum, dpll_satisfiable, finite_diff, compogen, groups_count, ...)
LOCAL_PUBLIC = {
    "sympy.abc", "sympy.assumptions.assume", "sympy.assumptions.cnf", "sympy.assumptions.facts",
    "sympy.assumptions.lra_satask", "sympy.assumptions.predicates.calculus", "sympy.assumptions.predicates.common",
    "sympy.assumptions.predicates.matrices", "sympy.assumptions.predicates.ntheory",
    "sympy.assumptions.predicates.order", "sympy.assumptions.predicates.sets", "sympy.assumptions.relation.binrel",
    "sympy.assumptions.relation.equality", "sympy.assumptions.satask", "sympy.assumptions.sathandlers",
    "sympy.assumptions.wrapper", "sympy.calculus.accumulationbounds", "sympy.calculus.singularities",
    "sympy.calculus.util", "sympy.combinatorics.coset_table", "sympy.combinatorics.galois",
    "sympy.combinatorics.group_numbers", "sympy.combinatorics.homomorphisms", "sympy.combinatorics.pc_groups",
    "sympy.combinatorics.schur_number", "sympy.concrete.delta", "sympy.concrete.expr_with_intlimits",
    "sympy.concrete.expr_with_limits", "sympy.concrete.gosper", "sympy.concrete.guess", "sympy.concrete.products",
    "sympy.core.exprtools", "sympy.core.facts", "sympy.core.intfunc", "sympy.core.mod",
    "sympy.core.operations", "sympy.core.parameters", "sympy.core.random",
    "sympy.core.rules", "sympy.core.singleton", "sympy.core.sorting", "sympy.crypto.crypto",
    "sympy.functions.combinatorial.factorials", "sympy.functions.elementary._trigonometric_special",
    "sympy.functions.elementary.integers", "sympy.functions.elementary.miscellaneous",
    "sympy.functions.elementary.piecewise", "sympy.functions.special.beta_functions",
    "sympy.functions.special.delta_functions", "sympy.functions.special.singularity_functions", "sympy.integrals",
    "sympy.integrals.intpoly", "sympy.integrals.laplace", "sympy.integrals.quadrature",
    "sympy.integrals.transforms", "sympy.liealgebras.cartan_matrix", "sympy.liealgebras.cartan_type",
    "sympy.liealgebras.dynkin_diagram", "sympy.liealgebras.root_system", "sympy.liealgebras.type_a",
    "sympy.liealgebras.type_b", "sympy.liealgebras.type_c", "sympy.liealgebras.type_d", "sympy.liealgebras.type_e",
    "sympy.liealgebras.type_f", "sympy.liealgebras.type_g", "sympy.liealgebras.weyl_group",
    "sympy.logic.algorithms.dpll", "sympy.logic.algorithms.dpll2", "sympy.logic.algorithms.lra_theory",
    "sympy.logic.utilities.dimacs", "sympy.ntheory.bbp_pi", "sympy.ntheory.continued_fraction",
    "sympy.ntheory.egyptian_fraction", "sympy.ntheory.elliptic_curve", "sympy.ntheory.residue_ntheory",
    "sympy.parsing.mathematica", "sympy.parsing.sympy_parser", "sympy.series.acceleration",
    "sympy.series.approximants", "sympy.series.kauers", "sympy.series.order", "sympy.sets.conditionset",
    "sympy.sets.contains", "sympy.sets.fancysets", "sympy.sets.ordinals", "sympy.sets.powerset",
    "sympy.sets.setexpr", "sympy.simplify.combsimp", "sympy.solvers", "sympy.solvers.bivariate",
    "sympy.solvers.decompogen", "sympy.solvers.deutils", "sympy.solvers.ode.nonhomogeneous",
    "sympy.solvers.ode.single", "sympy.solvers.ode.subscheck", "sympy.solvers.simplex", "sympy.stats",
    "sympy.tensor.array", "sympy.tensor.array.array_comprehension", "sympy.tensor.array.array_derivatives",
    "sympy.tensor.array.dense_ndim_array", "sympy.tensor.array.expressions",
    "sympy.tensor.array.expressions.array_expressions", "sympy.tensor.array.expressions.from_array_to_matrix",
    "sympy.tensor.array.expressions.from_indexed_to_array", "sympy.tensor.array.mutable_ndim_array",
    "sympy.tensor.array.sparse_ndim_array", "sympy.tensor.functions", "sympy.tensor.indexed",
}

# the low-level polys modules: their module-level functions (gf_add, dup_strip, monomial_mul, dispersion,
# sdm_add, rs_series, solve_lin_sys, smith_normal_form, round_two, ...) are their public API
INTERNAL_PUBLIC = {
    "sympy.matrices.expressions._shape", "sympy.matrices.expressions.companion",
    "sympy.matrices.expressions.fourier", "sympy.matrices.kind", "sympy.matrices.normalforms",
    "sympy.matrices.sparsetools", "sympy.polys.agca.extensions", "sympy.polys.agca.homomorphisms",
    "sympy.polys.agca.ideals", "sympy.polys.appellseqs", "sympy.polys.constructor", "sympy.polys.densearith",
    "sympy.polys.densebasic", "sympy.polys.densetools", "sympy.polys.dispersion", "sympy.polys.distributedmodules",
    "sympy.polys.domains.domain", "sympy.polys.factortools", "sympy.polys.galoistools", "sympy.polys.groebnertools",
    "sympy.polys.heuristicgcd", "sympy.polys.matrices.ddm", "sympy.polys.matrices.dense",
    "sympy.polys.matrices.domainmatrix", "sympy.polys.matrices.linsolve", "sympy.polys.matrices.normalforms",
    "sympy.polys.matrices.sdm", "sympy.polys.modulargcd", "sympy.polys.monomials", "sympy.polys.numberfields.basis",
    "sympy.polys.numberfields.galois_resolvents", "sympy.polys.numberfields.modules",
    "sympy.polys.numberfields.primes", "sympy.polys.numberfields.utilities", "sympy.polys.orderings",
    "sympy.polys.polyoptions", "sympy.polys.puiseux", "sympy.polys.ring_series", "sympy.polys.solvers",
    "sympy.polys.sqfreetools",
}

SUBPACKAGE_PUBLIC = {
    "sympy.crypto.": ("sympy.crypto",),
    "sympy.liealgebras.": ("sympy.liealgebras",),
    "sympy.categories.": ("sympy.categories",),
    "sympy.combinatorics.": ("sympy.combinatorics",),
    "sympy.tensor.tensor": ("sympy.tensor.tensor",),
    "sympy.discrete.": ("sympy.discrete", "sympy.discrete.recurrences"),
    "sympy.strategies.branch.": ("sympy.strategies.branch",),
    "sympy.strategies.": ("sympy.strategies",),
    "sympy.unify.": ("sympy.unify",),
    # sympy.vector exports orthogonalize only from sympy.vector.functions
    "sympy.vector.": ("sympy.vector", "sympy.vector.functions"),
}


def subpackage_public(modname):
    """The public names of the subpackage of modname (and of modname itself for LOCAL_PUBLIC and
    INTERNAL_PUBLIC modules)."""
    if modname.startswith("sympy.stats."):
        return stats_public()
    names = set()
    pkgs_all = []
    if modname in LOCAL_PUBLIC:
        # the module's own public definitions are API of that module (not top-level sympy names)
        pkgs_all.append((modname,))
    for prefix, pkgs in SUBPACKAGE_PUBLIC.items():
        if modname.startswith(prefix):
            pkgs_all.append(pkgs)
            break
    for pkgs in pkgs_all:
        for pkg in pkgs:
            m = importlib.import_module(pkg)
            # a package's __all__, or the public functions a module defines
            names |= set(getattr(m, "__all__", None) or [n for n in dir(m) if not n.startswith("_") and getattr(getattr(m, n), "__module__", None) == pkg])
    if modname in INTERNAL_PUBLIC:
        # the module's own public functions are its API (SymPy does not re-export them at top level)
        mod = importlib.import_module(modname)
        names |= {n for n, v in vars(mod).items() if not n.startswith("_") and callable(v) and getattr(v, "__module__", None) == modname}
    return names

ASSUMPTION_KEYS = ["real", "positive", "negative", "nonnegative", "nonpositive", "integer", "commutative", "polar"]


DUMMY_IDS = {}


class Unsupported(Exception):
    pass


class PythonRuntime(Exception):
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
    from sympy.combinatorics.perm_groups import PermutationGroup as _PermGroup
    from sympy.combinatorics.permutations import Cycle as _Cycle
    from sympy.categories import Object as _CatObject, Category as _Category, Diagram as _Diagram, Morphism as _Morphism
    from sympy.categories.baseclasses import Class as _Class
    if isinstance(o, _CatObject):
        return {"t": "CategoryObject", "name": o.name}
    if isinstance(o, _Class):
        return {"t": "CategoryClass", "objects": ser(o.args[0])}
    if isinstance(o, _Category):
        return {"t": "Category", "name": o.name, "objects": ser(o.objects.args[0]), "diagrams": [ser(d) for d in o.commutative_diagrams]}
    if isinstance(o, _Diagram):
        return {"t": "Diagram", "premises": ser(dict(o.premises)), "conclusions": ser(dict(o.conclusions))}
    if isinstance(o, _Morphism):
        from sympy.core.symbol import Str
        return {"t": "Morphism", "cls": type(o).__name__, "args": [ser(a.name if isinstance(a, Str) else a) for a in o.args]}
    if isinstance(o, _Perm):
        return {"t": "Permutation", "array": [int(i) for i in o.array_form]}
    if isinstance(o, _PermGroup):
        return {"t": "PermutationGroup", "generators": [ser(g) for g in o.generators]}
    if isinstance(o, _Cycle):
        return {"t": "Cycle", "cycles": [[int(i) for i in c] for c in _Perm(o).cyclic_form], "size": int(o.size)}
    from sympy.tensor.array import NDimArray as _NDA
    from sympy.tensor.tensor import TensorIndexType as _TIT, TensorIndex as _TI, TensorHead as _TH, TensorSymmetry as _TS, Tensor as _Tensor, TensMul as _TensMul
    from sympy.tensor.tensor import TensAdd as _TensAdd, TensorElement as _TE, WildTensorHead as _WTH, WildTensor as _WT, WildTensorIndex as _WTI
    from sympy.combinatorics.polyhedron import Polyhedron as _Polyhedron
    from sympy.combinatorics.perm_groups import SymmetricPermutationGroup as _SymPermGroup
    if isinstance(o, _SymPermGroup):
        return {"t": "SymmetricPermutationGroup", "deg": int(o.degree)}
    if isinstance(o, _Polyhedron):
        # rebuilt by the constructor from its corners, faces and the permutations of its group
        return {"t": "Polyhedron", "corners": [ser(c) for c in o.args[0]], "faces": [[int(i) for i in f] for f in o.args[1]],
                "pgroup": [ser(g) for g in o.args[2]]}
    if isinstance(o, _WTI):
        return {"t": "WildTensorIndex", "name": o.name, "type": ser(o.tensor_index_type), "up": bool(o.is_up), "ignoreUpdown": bool(o.ignore_updown)}
    if isinstance(o, _WTH):
        if o.comm != 0 or o.symmetry != _TS.no_symmetry(len(o.index_types)):
            raise Unsupported('WildTensorHead with a symmetry or commutation group')
        return {"t": "WildTensorHead", "name": o.name, "types": [ser(t) for t in o.index_types], "unordered": bool(o.unordered_indices)}
    if isinstance(o, _WT):
        return {"t": "WildTensor", "head": ser(o.component), "indices": [ser(i) for i in o.get_indices()]}
    if isinstance(o, _TensAdd):
        return {"t": "TensAdd", "args": [ser(a) for a in o.args]}
    if isinstance(o, _TE):
        return {"t": "TensorElement", "expr": ser(o.expr), "indexMap": ser(dict(o.index_map))}
    if isinstance(o, _TIT):
        if o.args[4] != 1 or str(o.args[5]) != 'metric':
            raise Unsupported('TensorIndexType with a non-default metric')
        return {"t": "TensorIndexType", "name": o.name, "dim": ser(o.dim), "dummyName": o.dummy_name}
    if isinstance(o, _TI):
        return {"t": "TensorIndex", "name": o.name, "type": ser(o.tensor_index_type), "up": bool(o.is_up)}
    if isinstance(o, _TS):
        for sign, candidate in [(0, _TS.no_symmetry(o.rank)), (1, _TS.fully_symmetric(o.rank)), (-1, _TS.fully_symmetric(-o.rank))]:
            if o == candidate:
                return {"t": "TensorSymmetry", "rank": o.rank, "sign": sign}
        # a general slot symmetry by its base and strong generating set
        return {"t": "TensorSymmetry", "base": [int(b) for b in o.base], "generators": [ser(g) for g in o.generators]}
    if isinstance(o, _TH):
        if o.comm != 0:
            raise Unsupported('Noncommuting tensor heads')
        return {"t": "TensorHead", "name": o.name, "types": [ser(t) for t in o.index_types], "symmetry": ser(o.symmetry)}
    if isinstance(o, _Tensor):
        return {"t": "Tensor", "head": ser(o.component), "indices": [ser(i) for i in o.get_indices()]}
    if isinstance(o, _TensMul):
        return {"t": "TensMul", "args": [ser(a) for a in o.args]}
    if isinstance(o, _NDA):
        return {"t": "NDimArray", "cls": type(o).__name__, "shape": [int(k) for k in o.shape], "flat": [ser(i) for i in o._array] if hasattr(o, "_array") else [ser(o[i]) for i in __import__("itertools").product(*[range(k) for k in o.shape])]}
    if isinstance(o, sympy.Idx):
        return {"t": "Idx", "label": ser(o.label), "lower": ser(o.lower) if o.lower is not None else None, "upper": ser(o.upper) if o.upper is not None else None}
    from sympy.logic.inference import PropKB as _PropKB
    if isinstance(o, _PropKB):
        return {"t": "PropKB", "clauses": [ser(c) for c in sorted(o.clauses, key=sympy.default_sort_key)]}
    if isinstance(o, (sympy.Not, sympy.Xor, sympy.Implies, sympy.Equivalent, sympy.Nand, sympy.Nor, sympy.logic.boolalg.Xnor, sympy.ITE)):
        return {"t": "Logic", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    from sympy.liealgebras.cartan_type import Standard_Cartan as _SC
    from sympy.liealgebras.root_system import RootSystem as _RS
    from sympy.liealgebras.weyl_group import WeylGroup as _WG
    if isinstance(o, _SC):
        return {"t": "CartanType", "series": o.series, "n": int(o.n)}
    if isinstance(o, (_RS, _WG)):
        return {"t": type(o).__name__, "cartanType": ser(o.cartan_type)}
    from sympy.polys.domains.modularinteger import ModularInteger as _ModInt
    if isinstance(o, _ModInt):
        # an element of GF(p) (the LFSR sequences of sympy.crypto, galoistools): its value and the modulus
        return {"t": "FFElement", "v": int(o.val) % int(o.mod), "mod": int(o.mod), "symmetric": bool(o.sym)}
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
    if (type(o).__module__ or "").startswith("sympy.stats.") and isinstance(o, Basic):
        # rebuilt by the class constructor from its arguments
        # (a sympy Dict argument, the density of a finite distribution, as a dict)
        return {"t": "Stats", "cls": type(o).__name__, "args": [ser(dict(a) if isinstance(a, sympy.Dict) else a) for a in o.args]}
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
    from sympy.polys.rings import PolyRing as _PolyRing, PolyElement as _PolyElement
    from sympy.polys.fields import FracField as _FracField, FracElement as _FracElement
    from sympy.polys.matrices import DomainMatrix as _DM
    from sympy.polys.matrices.ddm import DDM as _DDM
    from sympy.polys.matrices.sdm import SDM as _SDM
    from sympy.polys.matrices.domainscalar import DomainScalar as _DS
    from sympy.polys.orderings import MonomialOrder as _MO
    if type(o).__name__ in ("PythonMPQ", "mpq"):
        # a QQ element (the ground type of QQ)
        return {"t": "Rational", "p": str(o.numerator), "q": str(o.denominator)}
    if isinstance(o, _Domain):
        d = {"t": "Domain", "name": str(o)}
        if o.is_FiniteField:
            d.update(mod=int(o.mod), symmetric=bool(o.sym))
        elif o.is_AlgebraicField:
            d.update(base=ser(o.dom), ext=ser(o.ext.as_expr()), gens=[ser(e) for e in o.orig_ext])
        elif o.is_PolynomialRing or o.is_FractionField:
            d.update(base=ser(o.domain), symbols=[ser(s) for s in o.symbols], order=str(o.order))
        elif o.is_RealField or o.is_ComplexField:
            d.update(prec=int(o.precision))
        return d
    if isinstance(o, _MO):
        if str(o) not in ("lex", "grlex", "grevlex", "ilex", "igrlex", "igrevlex"):
            raise Unsupported("ProductOrder")
        return {"t": "MonomialOrder", "name": str(o)}
    if isinstance(o, (_PolyRing, _FracField)):
        return {"t": type(o).__name__, "symbols": [ser(s) for s in o.symbols], "domain": ser(o.domain), "order": str(o.order)}
    if isinstance(o, _PolyElement):
        return {"t": "PolyElement", "ring": ser(o.ring), "expr": ser(o.as_expr())}
    if isinstance(o, _FracElement):
        return {"t": "FracElement", "field": ser(o.field), "numer": ser(o.numer.as_expr()), "denom": ser(o.denom.as_expr())}
    if isinstance(o, (_DM, _DDM, _SDM)):
        K = o.domain
        return {"t": "DomainMatrix", "cls": type(o).__name__, "domain": ser(K), "shape": list(o.shape),
                "rows": [[ser(K.to_sympy(e)) for e in r] for r in o.to_list()],
                "fmt": o.rep.fmt if isinstance(o, _DM) else ("dense" if isinstance(o, _DDM) else "sparse")}
    if isinstance(o, _DS):
        return {"t": "DomainScalar", "domain": ser(o.domain), "element": ser(o.domain.to_sympy(o.element))}
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
    if isinstance(o, sympy.Range):
        return {"t": "Range", "start": ser(o.start), "stop": ser(o.stop), "step": ser(o.step)}
    if isinstance(o, sympy.Contains):
        # an unevaluated Contains(x, set) (a condition of sympy.stats stochastic processes)
        return {"t": "Contains", "x": ser(o.args[0]), "set": ser(o.args[1])}
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
    import sympy.categories as _categories
    for name in _categories.__all__:
        if name != 'preview_diagram' and name not in CATEGORIES_DRAWING:
            out.append({"name": name, "category": "categories"})
    for name in sorted(_combinatorics.__all__):
        obj = getattr(_combinatorics, name)
        if getattr(obj, "__module__", "") in MODULES and not any(a["name"] == name and a["category"] == "combinatorics" for a in out):
            out.append({"name": name, "category": "combinatorics"})
    from sympy.tensor.tensor import TensorIndexType, TensorIndex, TensorHead, TensorSymmetry, tensor_indices, tensor_heads, canon_bp, contract_metric
    for obj in (TensorIndexType, TensorIndex, TensorHead, TensorSymmetry, tensor_indices, tensor_heads, canon_bp, contract_metric):
        out.append({"name": obj.__name__, "category": "tensor"})
    for pkg, cat in (("sympy.crypto", "crypto"), ("sympy.liealgebras", "liealgebras")):
        # subpackages whose names are not top-level sympy names
        m = importlib.import_module(pkg)
        for name in sorted(m.__all__):
            out.append({"name": name, "category": cat})
    for name in sorted(stats_public()):
        # sympy.stats is a subpackage too (only the names of the in-scope modules, see stats_public)
        out.append({"name": name, "category": "stats"})
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


# keep printed text output (print(f(...)), pprint(...), print_tree(...), srepr(...)) as text cases
TEXT_OUTPUT = os.environ.get("TEXT_OUTPUT", "1") == "1"
# measure only these modules (comma-separated prefixes) when set
ONLY = [m for m in os.environ.get("ONLY_MODULES", "").split(",") if m]


def main(dst):
    import random
    # SymPy's doctest runner prints in ASCII (pprint_use_unicode(False)); so do the corpus cases
    from sympy.printing.pretty.pretty_symbology import pretty_use_unicode
    pretty_use_unicode(False)
    random.seed(0)  # randMatrix and friends: keep the corpus reproducible
    warnings.filterwarnings("ignore")
    signal.signal(signal.SIGALRM, _alarm)
    finder = doctest.DocTestFinder(exclude_empty=True)
    cases = []
    skipped = {}
    extraction = {"examined": 0, "reasons": {}, "omitted": []}
    def omit(reason, modname, ex):
        extraction["reasons"][reason] = extraction["reasons"].get(reason, 0) + 1
        if ex.want.strip():
            extraction["omitted"].append({"module": modname, "src": ex.source.strip(), "reason": reason})
    for modname, category in MODULES.items():
        if ONLY and not any(modname.startswith(m) for m in ONLY):
            continue
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        extra_public = subpackage_public(modname)
        for test in finder.find(mod):
            # randomized algorithms (Schreier-Sims, random group elements) give reproducible receivers
            random.seed(0)
            sympy.core.random.seed(0)
            globs = {}
            exec("from sympy import *", globs)
            for ex in test.examples:
                extraction["examined"] += 1
                src = ex.source.strip()
                if ex.options.get(doctest.SKIP):
                    omit("upstream-skip", modname, ex)
                    # SymPy does not run these either (random or illustrative output)
                    continue
                if re.fullmatch(r"[\w.]+\(\.\.\.\)", ex.want.strip()):
                    omit("illustrative-output", modname, ex)
                    # only the class of the result is shown (random output elided with ELLIPSIS)
                    continue
                try:
                    tree = ast.parse(src, mode="eval")
                except SyntaxError:
                    omit("statement-or-setup", modname, ex)
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
                # print(f(...)): the printed text of the inner call is the expected output
                printed = (TEXT_OUTPUT and isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == "print"
                           and len(call.args) == 1 and not call.keywords and isinstance(call.args[0], ast.Call))
                if printed:
                    call = call.args[0]
                    tree = ast.Expression(call)
                if isinstance(call, ast.Call) and not any(isinstance(a, ast.Starred) for a in call.args):
                    if isinstance(call.func, ast.Name):
                        record = {"fn": call.func.id}
                    elif isinstance(call.func, ast.Attribute):
                        record = {"fn": "." + call.func.attr, "selfSrc": ast.unparse(call.func.value)}
                from sympy.assumptions import global_assumptions as _ga
                assumed = list(_ga)
                try:
                    signal.alarm(ALARM_SECONDS)
                    _out = io.StringIO()
                    with contextlib.redirect_stdout(_out):
                        result = eval(compile(tree, "<doctest>", "eval"), globs)
                except (Exception, Timeout) as err:
                    omit("reference-timeout" if isinstance(err, Timeout) else "reference-exception", modname, ex)
                    continue
                finally:
                    signal.alarm(0)
                # text output: a printed call, a printing function (pprint, print_tree, ...) or a call returning a str
                text = None
                if TEXT_OUTPUT and record is not None and record["fn"] not in ("str", "repr"):
                    if printed:
                        text = str(result)
                    elif result is None and _out.getvalue() and "print" in record["fn"]:
                        text = _out.getvalue()[:-1] if _out.getvalue().endswith("\n") else _out.getvalue()
                    elif isinstance(result, str):
                        text = result
                    elif (type(result).__module__ or "").startswith("sympy.printing.") and not isinstance(result, Basic):
                        # a printing object (TableForm): the doctest shows its str
                        text = str(result)
                if text is None and (record is None or printed or "print" in record["fn"] or record["fn"] in ("str", "srepr", "latex", "repr")):
                    omit("non-call-expression" if record is None else "printing-expression", modname, ex)
                    continue
                fn = record["fn"]
                # only the public API: top-level sympy names and public methods
                if fn.startswith("."):
                    if fn[1:].startswith("_"):
                        omit("private-api", modname, ex)
                        continue
                elif (fn not in PUBLIC and fn not in extra_public) or fn in globs and (getattr(globs[fn], "__module__", None) or "__").startswith("__"):
                    omit("not-exported-api", modname, ex)
                    continue
                DUMMY_IDS.clear()
                try:
                    if "selfSrc" in record:
                        _self = eval(record.pop("selfSrc"), globs)
                        if printed and isinstance(_self, types.ModuleType):
                            # the printed output of a function of a Python module (inspect.getsource): not SymPy API
                            raise PythonRuntime()
                        record["self"] = ser(_self)
                    record["args"] = [ser_arg(a, globs) for a in call.args]
                    record["kwargs"] = {k.arg: ser_arg(k.value, globs) for k in call.keywords}
                    if assumed:
                        # the global assumptions in force (SymPy global_assumptions)
                        record["assume"] = [ser(a) for a in assumed]
                except PythonRuntime:
                    omit("python-runtime-api", modname, ex)
                    continue
                except Unsupported as e:
                    # keep the case (it counts as a failure) so the rate is not inflated
                    skipped[str(e)] = skipped.get(str(e), 0) + 1
                    record.pop("selfSrc", None)
                    record["unsupportedArg"] = str(e)
                except Exception:
                    omit("serialization-error", modname, ex)
                    continue
                from sympy.polys.monomials import Monomial as _Monomial
                if text is not None:
                    # compared as text (whitespace-normalized where the doctest says NORMALIZE_WHITESPACE)
                    record["text"] = True
                    if ex.options.get(doctest.NORMALIZE_WHITESPACE):
                        record["ws"] = True
                    record.update({"category": category, "module": modname, "src": src, "expected": text.rstrip("\n")})
                    cases.append(record)
                    continue
                if isinstance(result, (MatrixBase,)):
                    expected = str(result)
                elif isinstance(result, tuple) and any(isinstance(i, _Monomial) for i in result):
                    # a Monomial's repr is its address; its str is x**2*y**0
                    expected = "(" + ", ".join(str(i) for i in result) + ")"
                elif isinstance(result, (Basic, list, tuple, dict, set, int, float, bool)) or result is None:
                    expected = str(result)
                elif ((type(result).__module__ or "").startswith(("sympy.polys", "sympy.matrices", "sympy.external"))
                        or type(result).__name__ in ("mpq", "mpz")):
                    # polynomial-ring elements (PolyElement prints as x**2 + 1/2*y), domains (QQ<sqrt(2)>, GF(5)),
                    # DomainMatrix/DDM/SDM, DMP, ANP, ground elements (MPQ(1,2)): compared by str()
                    expected = str(result)
                else:
                    omit("unsupported-result-type", modname, ex)
                    continue
                if "\n" in expected:
                    omit("multiline-output", modname, ex)
                    continue
                record.update({"category": category, "module": modname, "src": src, "expected": expected})
                cases.append(record)
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "api": api_inventory(), "cases": cases, "extraction": extraction}, f, indent=1, ensure_ascii=False)
        f.write("\n")
    by_cat = {}
    for c in cases:
        by_cat[c["category"]] = by_cat.get(c["category"], 0) + 1
    print(f"TOTAL {len(cases)} cases", by_cat, file=sys.stderr)
    print("skipped (unsupported arg types):", dict(sorted(skipped.items(), key=lambda kv: -kv[1])[:15]), file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1])
