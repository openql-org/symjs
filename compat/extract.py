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
import inspect
import json
import random
import sys
import warnings
from collections import Counter, defaultdict

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
    "sympy.series.series_class": "calculus",
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
    "sympy.combinatorics.free_groups": "combinatorics",
    "sympy.combinatorics.fp_groups": "combinatorics",
    "sympy.combinatorics.rewritingsystem": "combinatorics",
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
    'sympy.parsing.latex': "parsing",
    'sympy.parsing.latex._parse_latex_antlr': "parsing",
    'sympy.parsing.latex.errors': "parsing",
    'sympy.parsing.latex.lark': "parsing",
    'sympy.parsing.latex.lark.latex_parser': "parsing",
    'sympy.parsing.latex.lark.transformer': "parsing",
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
    # previously unselected modules with a source counterpart (2026-11-11)
    "sympy.polys.euclidtools": "polys",
    "sympy.polys.rootisolation": "polys",
    "sympy.holonomic.holonomic": "holonomic",
    "sympy.holonomic.recurrence": "holonomic",
    "sympy.combinatorics.polyhedron": "combinatorics",
    "sympy.combinatorics.tensor_can": "combinatorics",
    "sympy.combinatorics.util": "combinatorics",
    "sympy.combinatorics.generators": "combinatorics",
    "sympy.combinatorics.group_constructs": "combinatorics",
    "sympy.core.assumptions": "core",
    "sympy.core.kind": "core",
    "sympy.core.logic": "core",
    "sympy.solvers.ode.lie_group": "ode",
    # Mathematical base modules are measured even before their implementation.
    "sympy.functions.special.bsplines": "special",
    "sympy.polys.numberfields.galoisgroups": "polys",
    "sympy.tensor.toperators": "tensor",
}

# sympy.categories.diagram_drawing (DiagramGrid, XypicDiagramDrawer, xypic_draw_diagram): drawing category
# diagrams is not ported, like plotting
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
    "sympy.calculus.util", "sympy.combinatorics.coset_table", "sympy.combinatorics.fp_groups",
    "sympy.combinatorics.free_groups", "sympy.combinatorics.galois",
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
    'sympy.parsing.latex', 'sympy.parsing.latex._parse_latex_antlr', 'sympy.parsing.latex.errors', 'sympy.parsing.latex.lark', 'sympy.parsing.latex.lark.latex_parser', 'sympy.parsing.latex.lark.transformer',
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
    "sympy.combinatorics.tensor_can", "sympy.combinatorics.util", "sympy.core.assumptions", "sympy.core.kind", "sympy.core.logic", "sympy.holonomic.holonomic", "sympy.holonomic.recurrence", "sympy.solvers.ode.lie_group", "sympy.integrals.deltafunctions", "sympy.integrals.heurisch", "sympy.integrals.meijerint", "sympy.integrals.rationaltools", "sympy.integrals.trigonometry", "sympy.ntheory.digits", "sympy.ntheory.ecm", "sympy.ntheory.modular", "sympy.ntheory.qs", "sympy.polys.orthopolys", "sympy.printing.conventions", "sympy.printing.pretty.pretty_symbology", "sympy.printing.pretty.stringpict", "sympy.stats.error_prop", "sympy.strategies.tree", "sympy.unify.rewrite", "sympy.unify.usympy", "sympy.utilities.decorator", "sympy.utilities.misc", "sympy.matrices.kind",
}

# the low-level polys modules: their module-level functions (gf_add, dup_strip, monomial_mul, dispersion,
# sdm_add, rs_series, solve_lin_sys, smith_normal_form, round_two, ...) are their public API
INTERNAL_PUBLIC = {
    "sympy.combinatorics.coset_table", "sympy.combinatorics.fp_groups", "sympy.combinatorics.free_groups",
    "sympy.combinatorics.homomorphisms", "sympy.combinatorics.pc_groups",
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
    "sympy.polys.euclidtools",
    "sympy.polys.rootisolation",
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
    """Public definitions of a selected module and its subpackage exports."""
    # A documented public function/class belongs to the selected module's API
    # even when it is not re-exported by sympy.__init__. Imported helpers and
    # private definitions do not become public merely by appearing in dir().
    mod = importlib.import_module(modname)
    names = {n for n, v in vars(mod).items()
             if not n.startswith("_") and callable(v)
             and getattr(v, "__module__", None) == modname}
    if modname.startswith("sympy.stats."):
        names -= STATS_SAMPLING
        names |= set(stats_public())
        if modname not in LOCAL_PUBLIC:
            return names
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

def symbol_assumptions(symbol):
    """Constructor facts, including False; inferred facts are rebuilt by the API."""
    return {k: v for k, v in symbol._assumptions_orig.items()
            if isinstance(v, bool) and not (k == "commutative" and v)}


DUMMY_IDS = {}


class Unsupported(Exception):
    pass


class PythonRuntime(Exception):
    pass


class NotSympy(Exception):
    pass


def is_sympy_operand(receiver, args):
    """Whether an operator, attribute or subscript expression involves a SymPy object (not a module,
    the S registry or plain Python values)."""
    from sympy.core.singleton import SingletonRegistry
    if isinstance(receiver, (types.ModuleType, SingletonRegistry)):
        return False
    def sympy_value(v):
        if isinstance(v, (list, tuple, set, frozenset)):
            return any(sympy_value(i) for i in v)
        if isinstance(v, dict):
            return any(sympy_value(k) or sympy_value(i) for k, i in v.items())
        mod = type(v).__module__ or ""
        return mod.startswith(("sympy.", "mpmath.")) or (isinstance(v, type) and (v.__module__ or "").startswith("sympy."))
    return sympy_value(receiver) or any(sympy_value(a) for a in args)


def _same_series(diff):
    """The series rebuilt from its function has the same leading terms."""
    try:
        return diff().expand() == 0
    except Exception:
        return False


def callback_expr(callback, variable):
    """Translate a unary arithmetic Python callback without evaluating its comparisons."""
    import dis
    import operator
    arithmetic = {"+": operator.add, "-": operator.sub, "*": operator.mul,
                  "/": operator.truediv, "**": operator.pow, "%": sympy.Mod}
    comparisons = {"==": sympy.Eq, "!=": sympy.Ne, "<": sympy.Lt,
                   "<=": sympy.Le, ">": sympy.Gt, ">=": sympy.Ge}
    stack = []
    for instruction in dis.get_instructions(callback):
        op = instruction.opname
        if op in ("RESUME", "CACHE", "NOP"):
            continue
        if op == "LOAD_FAST" and instruction.arg == 0:
            stack.append(variable)
        elif op in ("LOAD_CONST", "RETURN_CONST"):
            if not isinstance(instruction.argval, (int, float, bool)):
                raise Unsupported("Transform callback")
            value = sympy.sympify(instruction.argval)
            if op == "RETURN_CONST":
                return value
            stack.append(value)
        elif op in ("BINARY_OP", "COMPARE_OP") and len(stack) >= 2:
            operators = arithmetic if op == "BINARY_OP" else comparisons
            f = operators.get(instruction.argrepr)
            if f is None:
                raise Unsupported("Transform callback")
            right, left = stack.pop(), stack.pop()
            stack.append(f(left, right))
        elif op == "UNARY_NEGATIVE" and stack:
            stack[-1] = -stack[-1]
        elif op == "RETURN_VALUE" and len(stack) == 1:
            return stack[0]
        else:
            raise Unsupported("Transform callback")
    raise Unsupported("Transform callback")


def ser(o):
    """Serialize a SymPy object (or Python value) into a JSON tree."""
    from sympy import Float, Integer, Rational, Symbol, Tuple
    from sympy.core.relational import Relational

    if o is None or isinstance(o, bool):
        return {"t": "Js", "v": o}
    # Constructor data for objects outside the usual Basic expression tree. Keep
    # stateful objects explicit: their args alone do not describe the receiver.
    def public_object(name, *args):
        return {"t": "PublicObject", "cls": name, "args": [ser(a) for a in args]}

    from sympy.tensor.toperators import PartialDerivative
    from sympy.polys.polymatrix import MutablePolyDenseMatrix
    from sympy.polys.multivariate_resultants import DixonResultant, MacaulayResultant
    from sympy.sets.setexpr import SetExpr as ArithmeticSetExpr
    from sympy.combinatorics.galois import (S1TransitiveSubgroups, S2TransitiveSubgroups,
        S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups)
    if isinstance(o, PartialDerivative):
        return public_object("PartialDerivative", *o.args)
    if isinstance(o, MutablePolyDenseMatrix):
        return {"t": "PolyMatrix", "entries": ser(o.to_Matrix().tolist()), "ring": ser(o.ring)}
    if isinstance(o, (DixonResultant, MacaulayResultant)):
        return public_object(type(o).__name__, o.polynomials, o.variables)
    if isinstance(o, ArithmeticSetExpr):
        return public_object("SetExpression", o.set)
    if isinstance(o, (S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups,
                      S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups)):
        return {"t": "TransitiveSubgroup", "degree": int(type(o).__name__[1]), "name": o.name}

    from sympy.combinatorics.subsets import Subset
    from sympy.combinatorics.graycode import GrayCode
    from sympy.combinatorics.prufer import Prufer
    from sympy.combinatorics.perm_groups import Coset
    from sympy.core.exprtools import Factors
    from sympy.core.rules import Transform
    from sympy.core.parameters import _global_parameters
    from sympy.core.containers import TupleKind
    from sympy.core.kind import Kind
    from sympy.assumptions.assume import Predicate
    from sympy.assumptions.wrapper import AssumptionsWrapper
    from sympy.utilities.enumerative import PartComponent
    if isinstance(o, Subset):
        return public_object("Subset", o.subset, o.superset)
    if isinstance(o, GrayCode):
        return {"t": "GrayCode", "n": int(o.n), "current": o.current}
    if isinstance(o, Prufer):
        # Preserve the original edge order, as well as sequence-based inputs.
        return public_object("Prufer", o.args[0].tolist() if hasattr(o.args[0], "tolist") else list(o.args[0]))
    if isinstance(o, (Coset, sympy.UnevaluatedExpr, AssumptionsWrapper)):
        return public_object(type(o).__name__, *o.args)
    if isinstance(o, Factors):
        return public_object("Factors", o.factors)
    if isinstance(o, (sympy.ProductSet, sympy.DisjointUnion)):
        return public_object(type(o).__name__, *o.args)
    if isinstance(o, sympy.ComplexRegion) and o is not sympy.S.Complexes:
        return public_object(type(o).__name__, o.sets)
    if isinstance(o, Predicate):
        return {"t": "Predicate", "name": str(o.name)}
    if isinstance(o, TupleKind):
        return public_object("TupleKind", *o.element_kind)
    if isinstance(o, Kind):
        return {"t": "Kind", "name": str(o)}
    if isinstance(o, _global_parameters):
        return {"t": "GlobalParameters", "evaluate": o.evaluate, "distribute": o.distribute, "expIsPow": o.exp_is_pow}
    if isinstance(o, slice):
        return {"t": "Slice", "start": ser(o.start), "stop": ser(o.stop), "step": ser(o.step)}
    if isinstance(o, Transform):
        # Python == tests structural equality on a dummy. Interpret only a
        # straight-line arithmetic callback so x % 2 == 1 stays a predicate.
        x = sympy.Dummy("transform_arg")
        return {"t": "Transform", "var": ser(x), "body": ser(callback_expr(o._transform, x)),
                "condition": ser(callback_expr(o._filter, x))}
    if isinstance(o, PartComponent):
        return {"t": "PartComponent", "c": int(o.c), "u": int(o.u), "v": int(o.v)}
    from sympy.logic.algorithms.dpll2 import SATSolver, Level
    if isinstance(o, Level):
        return {"t": "SATLevel", "decision": int(o.decision), "flipped": bool(o.flipped), "settings": sorted(o.var_settings)}
    if isinstance(o, SATSolver):
        return {"t": "SATSolver", "clauses": [list(c) for c in o.clauses], "variables": len(o.variable_set) - 1,
                "settings": sorted(o.var_settings), "variableSet": list(o.variable_set),
                "sentinels": [[int(k), sorted(v)] for k, v in sorted(o.sentinels.items())],
                "scores": [[int(k), v] for k, v in sorted(o.lit_scores.items())], "heap": [list(pair) for pair in o.lit_heap],
                "learned": o.num_learned_clauses, "levels": [ser(l) for l in o.levels],
                "queue": list(o._unit_prop_queue), "unsatisfied": bool(o.is_unsatisfied)}
    from sympy.ntheory.ecm import Point as ECMPoint
    if isinstance(o, ECMPoint):
        return {"t": "ECMPoint", "coords": [str(v) for v in (o.x_cord, o.z_cord, o.a_24, o.mod)]}
    from sympy.simplify.hyperexpand import Hyper_Function, G_Function, Formula, Operator
    from sympy.functions.special.hyper import HyperRep
    if isinstance(o, Hyper_Function):
        return {"t": "PublicObject", "cls": "Hyper_Function", "args": [ser(o.ap), ser(o.bq)]}
    if isinstance(o, G_Function):
        return {"t": "PublicObject", "cls": "G_Function", "args": [ser(v) for v in (o.an, o.ap, o.bm, o.bq)]}
    if isinstance(o, Formula):
        return {"t": "PublicObject", "cls": "Formula", "args": [ser(v) for v in (o.func, o.z, list(o.B), list(o.C), o.M.tolist())]}
    if isinstance(o, Operator):
        return {"t": "PublicObject", "cls": "Operator", "args": [ser(o._poly.as_expr()), ser(o._poly.gen)]}
    if isinstance(o, HyperRep):
        return {"t": "PublicObject", "cls": "HyperRep", "args": [ser(type(o).__name__.removeprefix("HyperRep_")), ser(o.args)]}
    from sympy.polys.agca.extensions import ExtensionElement
    from sympy.polys.polyclasses import DMP
    if isinstance(o, ExtensionElement):
        return {"t": "ExtensionElement", "modulus": ser(o.ext.modulus), "expr": ser(o.as_expr())}
    if isinstance(o, DMP):
        return {"t": "DMP", "coeffs": ser(o.to_list()), "level": o.lev, "domain": ser(o.dom)}
    from sympy.polys.agca.modules import FreeModule, SubModule, QuotientModule, FreeModuleElement, QuotientModuleElement
    from sympy.polys.agca.ideals import ModuleImplementedIdeal
    from sympy.polys.agca.homomorphisms import ModuleHomomorphism
    from sympy.polys.domains.quotientring import QuotientRing
    from sympy.polys.domains.old_polynomialring import PolynomialRingBase
    from sympy.holonomic.holonomic import HolonomicFunction as _HF, DifferentialOperator as _DO, DifferentialOperatorAlgebra as _DOA
    from sympy.holonomic.recurrence import HolonomicSequence as _HS, RecurrenceOperator as _RO, RecurrenceOperatorAlgebra as _ROA
    if isinstance(o, (_DOA, _ROA)):
        return {"t": "DifferentialOperatorAlgebra" if isinstance(o, _DOA) else "RecurrenceOperatorAlgebra",
                "base": ser(o.base.dom), "x": ser(o.base.gens[0]), "gen": str(o.gen_symbol)}
    if isinstance(o, (_DO, _RO)):
        return {"t": "DifferentialOperator" if isinstance(o, _DO) else "RecurrenceOperator", "parent": ser(o.parent),
                "coeffs": [ser(o.parent.base.to_sympy(p)) for p in o.listofpoly]}
    if isinstance(o, _HF):
        return {"t": "HolonomicFunction", "op": ser(o.annihilator), "x": ser(o.x), "x0": ser(o.x0), "y0": ser(o.y0)}
    if isinstance(o, _HS):
        return {"t": "HolonomicSequence", "op": ser(o.recurrence), "u0": ser(o.u0)}
    if isinstance(o, PolynomialRingBase):
        return {"t": "Domain", "name": str(o), "base": ser(o.dom), "symbols": [ser(s) for s in o.gens], "order": str(o.order), "oldPolyRing": True}
    if isinstance(o, QuotientRing):
        return {"t": "AGCAQuotientRing", "ring": ser(o.ring), "ideal": ser(o.base_ideal)}
    if isinstance(o, ModuleImplementedIdeal):
        return {"t": "AGCAIdeal", "ring": ser(o.ring), "gens": [ser(o.ring.to_sympy(g)) for g in o.gens]}
    if isinstance(o, ModuleHomomorphism):
        return {"t": "AGCAHomomorphism", "domain": ser(o.domain), "codomain": ser(o.codomain), "matrix": [ser(g) for g in o.matrix]}
    if isinstance(o, (FreeModuleElement, QuotientModuleElement)):
        data = o.data.data if isinstance(o, QuotientModuleElement) else o.data
        return {"t": "AGCAElement", "module": ser(o.module), "data": [ser(o.module.ring.to_sympy(g)) for g in data]}
    if isinstance(o, FreeModule):
        return {"t": "AGCAFreeModule", "ring": ser(o.ring), "rank": o.rank}
    if isinstance(o, QuotientModule):
        return {"t": "AGCAQuotientModule", "base": ser(o.base), "killed": ser(o.killed_module)}
    if isinstance(o, SubModule):
        # Store generator coordinates, not elements carrying the same module.
        return {"t": "AGCASubModule", "container": ser(o.container), "gens": [ser(g) for g in o.gens]}
    from sympy.polys.matrices.ddm import DDM as _DDM0
    from sympy.polys.matrices.sdm import SDM as _SDM0
    if isinstance(o, (_DDM0, _SDM0)):
        # DDM is a list and SDM a dict: serialized as matrices before the containers
        K = o.domain
        return {"t": "DomainMatrix", "cls": type(o).__name__, "domain": ser(K), "shape": list(o.shape),
                "rows": [[ser(K.to_sympy(e)) for e in r] for r in o.to_list()],
                "fmt": "dense" if isinstance(o, _DDM0) else "sparse"}
    from sympy.assumptions.assume import AssumptionsContext as _AC
    from sympy.assumptions.ask import AssumptionKeys as _AK
    if isinstance(o, _AC):
        return {"t": "AssumptionsContext", "items": [ser(a) for a in o]}
    if isinstance(o, _AK):
        return {"t": "QKeys"}
    from sympy.polys.rootisolation import ComplexInterval as _ComplexInterval
    if isinstance(o, _ComplexInterval):
        # the rectangle of the root above the real axis and the polynomial f(x) = Re f(x + I*y) at y = 0
        from sympy.polys.densetools import dmp_eval_in
        from sympy.polys.densebasic import dup_strip
        f = dup_strip(dmp_eval_in(o.f1, o.dom.zero, 1, 1, o.dom))
        return {"t": "ComplexInterval", "coeffs": [ser(o.dom.to_sympy(c)) for c in f],
                "a": [ser(o.dom.to_sympy(c)) for c in o.a], "b": [ser(o.dom.to_sympy(c)) for c in o.b], "conj": bool(o.conj)}
    from sympy.ntheory.generate import Sieve as _Sieve
    if isinstance(o, _Sieve):
        return {"t": "Sieve"}
    from sympy.solvers.ode.single import SingleODEProblem as _SODEP, SingleODESolver as _SODES
    if isinstance(o, _SODEP):
        return {"t": "SingleODEProblem", "eq": ser(o.eq), "func": ser(o.func), "sym": ser(o.sym)}
    if isinstance(o, _SODES):
        return {"t": "SingleODESolver", "cls": type(o).__name__, "problem": ser(o.ode_problem)}
    from sympy.combinatorics.partitions import IntegerPartition as _IntegerPartition, Partition as _Partition
    from sympy.printing.str import StrPrinter as _StrPrinter
    if isinstance(o, _IntegerPartition):
        return {"t": "IntegerPartition", "parts": list(o.partition)}
    if isinstance(o, _Partition):
        return {"t": "Partition", "blocks": [[ser(e) for e in block] for block in o.args]}
    if isinstance(o, _StrPrinter):
        return {"t": "StrPrinter", "settings": ser(o._settings)}
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
    from sympy.combinatorics.free_groups import FreeGroup as _FreeGroup, FreeGroupElement as _FGE
    from sympy.combinatorics.fp_groups import FpGroup as _FpGroup, FpSubgroup as _FpSubgroup
    from sympy.combinatorics.coset_table import CosetTable as _CosetTable
    from sympy.combinatorics.pc_groups import Collector as _Collector, PolycyclicGroup as _PcGroup
    from sympy.combinatorics.homomorphisms import GroupHomomorphism as _GroupHom
    if isinstance(o, _FreeGroup):
        return {"t": "FreeGroup", "symbols": [ser(sym) for sym in o.symbols]}
    if isinstance(o, _FGE):
        return {"t": "FreeGroupElement", "group": ser(o.group), "array": [[ser(sym), int(e)] for sym, e in o.array_form]}
    if isinstance(o, _FpGroup):
        return {"t": "FpGroup", "free": ser(o.free_group), "relators": [ser(r) for r in o.relators]}
    if isinstance(o, _FpSubgroup):
        return {"t": "FpSubgroup", "parent": ser(o.parent), "generators": [ser(g) for g in o.generators], "normal": bool(o.normal)}
    if isinstance(o, _CosetTable):
        # the state of a coset table: the table, the coset classes p and the deduction stack
        return {"t": "CosetTable", "group": ser(o.fp_group), "subgroup": [ser(h) for h in o.subgroup],
                "maxCosets": int(o.coset_table_limit), "table": [[None if v is None else int(v) for v in row] for row in o.table],
                "p": [int(v) for v in o.p], "deductions": [[int(a), ser(x)] for a, x in o.deduction_stack],
                # the Reidemeister-Schreier state left by define_schreier_generators and reidemeister_relators
                **({"schreier": {"free": ser(o._schreier_free_group), "generators": [ser(g) for g in o._schreier_generators],
                                 "relators": [ser(r) for r in getattr(o, "_reidemeister_relators", [])],
                                 "hasRelators": hasattr(o, "_reidemeister_relators"),
                                 "P": [[None if v is None else ser(v) for v in row] for row in o.P]}}
                   if hasattr(o, "_schreier_free_group") else {})}
    if isinstance(o, _Collector):
        return {"t": "Collector", "pcgs": [ser(g) for g in o.pcgs], "series": [ser(g) for g in o.pc_series],
                "relativeOrder": [int(r) for r in o.relative_order]}
    if isinstance(o, _PcGroup):
        return {"t": "PolycyclicGroup", "pcgs": [ser(g) for g in o.pcgs], "series": [ser(g) for g in o.pc_series],
                "relativeOrder": [int(r) for r in o.relative_order]}
    from sympy.polys.numberfields.modules import PowerBasis as _PB, Submodule as _Sub, ModuleElement as _ME
    from sympy.polys.numberfields.primes import PrimeIdeal as _PI
    if isinstance(o, _PB):
        # the power basis of a polynomial, or of the primitive element of a number field
        return {"t": "PowerBasis", "T": ser(o.T), "field": None if o.K is None else ser(o.K)}
    if isinstance(o, _Sub):
        return {"t": "Submodule", "parent": ser(o.parent), "matrix": ser(o.matrix), "denom": str(o.denom)}
    if isinstance(o, _ME):
        # integers as strings (they may exceed the double range)
        return {"t": "ModuleElement", "module": ser(o.module), "col": [str(c) for c in o.coeffs], "denom": str(o.denom)}
    if isinstance(o, _PI):
        return {"t": "PrimeIdeal", "ZK": ser(o.ZK), "p": str(o.p), "alpha": ser(o.alpha), "f": int(o.f), "e": int(o.e)}
    if isinstance(o, _GroupHom):
        return {"t": "GroupHomomorphism", "domain": ser(o.domain), "codomain": ser(o.codomain),
                "images": [[ser(k), ser(v)] for k, v in o.images.items()]}
    if isinstance(o, _PermGroup):
        return {"t": "PermutationGroup", "generators": [ser(g) for g in o.generators]}
    if isinstance(o, _Cycle):
        return {"t": "Cycle", "cycles": [[int(i) for i in c] for c in _Perm(o).cyclic_form], "size": int(o.size)}
    from sympy.tensor.array import NDimArray as _NDA
    from sympy.tensor.array.expressions import array_expressions as _AE
    if isinstance(o, _AE.ArraySymbol):
        return {"t": "ArraySymbol", "name": str(o.name), "shape": [ser(d) for d in o.shape]}
    if isinstance(o, _AE.ArrayElement):
        return {"t": "ArrayElement", "parent": ser(o.name), "indices": [ser(i) for i in o.indices]}
    if isinstance(o, (_AE.ArrayTensorProduct, _AE.ArrayAdd, _AE.ZeroArray)):
        return {"t": "ArrayExpression", "cls": type(o).__name__, "args": [ser(a) for a in o.args]}
    if isinstance(o, (_AE.ArrayContraction, _AE.ArrayDiagonal)):
        return {"t": "ArrayAxes", "cls": type(o).__name__, "expr": ser(o.expr), "axes": [list(map(int, g)) for g in o.args[1:]]}
    if isinstance(o, _AE.PermuteDims):
        return {"t": "PermuteDims", "expr": ser(o.expr), "permutation": list(o.permutation.array_form)}
    if isinstance(o, _AE.Reshape):
        return {"t": "Reshape", "expr": ser(o.expr), "shape": [ser(d) for d in o.shape]}
    from sympy.tensor.tensor import TensorIndexType as _TIT, TensorIndex as _TI, TensorHead as _TH, TensorSymmetry as _TS, Tensor as _Tensor, TensMul as _TensMul
    from sympy.tensor.tensor import TensAdd as _TensAdd, TensorElement as _TE, WildTensorHead as _WTH, WildTensor as _WT, WildTensorIndex as _WTI
    from sympy.combinatorics.polyhedron import Polyhedron as _Polyhedron
    from sympy.combinatorics.perm_groups import SymmetricPermutationGroup as _SymPermGroup
    if isinstance(o, _SymPermGroup):
        return {"t": "SymmetricPermutationGroup", "deg": int(o.degree)}
    if isinstance(o, _Polyhedron):
        # rebuilt by the constructor from its corners, faces and the permutations of its group
        return {"t": "Polyhedron", "corners": [ser(c) for c in o.args[0]], "faces": [[int(i) for i in f] for f in o.args[1]],
                "pgroup": [ser(g) for g in o.args[2]], "rotation": list(o.array_form)}
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
    from sympy.tensor.array.array_comprehension import ArrayComprehension as _ACo, ArrayComprehensionMap as _ACM
    if isinstance(o, _ACM):
        # the lambda of the map (with no or one argument) applied to a dummy
        f = o._lambda
        ds = [sympy.Dummy("x") for _ in range(f.__code__.co_argcount)]
        return {"t": "ArrayComprehensionMap", "function": {"t": "JsLambda", "params": [ser(d) for d in ds], "body": ser(sympy.sympify(f(*ds)))},
                "limits": [ser(tuple(l)) for l in o.limits]}
    if isinstance(o, _ACo):
        return {"t": "ArrayComprehension", "function": ser(o.function), "limits": [ser(tuple(l)) for l in o.limits]}
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
        return {"t": "Rational", "p": str(o), "q": "1", "py": True}
    if isinstance(o, float):
        return {"t": "Float", "v": o, "py": True}
    if isinstance(o, str):
        return {"t": "Str", "v": o}
    import types as _types
    if isinstance(o, type) and o in (str, int, float, bool, list, tuple, dict, _types.GeneratorType):
        return {"t": "Type", "name": o.__name__}
    if isinstance(o, (_types.GeneratorType, zip, map, filter)) or type(o).__name__.endswith("iterator"):
        # Snapshot the values while preserving that this is an iterator, not a sequence.
        return {"t": "Iterator", "items": [ser(i) for i in list(o)]}
    if isinstance(o, (_types.FunctionType, _types.BuiltinFunctionType)):
        # a library function passed as an argument (equal_valued, factor, math.isclose, ...)
        mod = getattr(o, "__module__", "") or ""
        if mod == "sympy.vector.vector" and o.__qualname__ == "Vector.dot.<locals>.directional_derivative":
            return {"t": "DirectionalDerivative", "vector": ser(inspect.getclosurevars(o).nonlocals["self"])}
        # A closure is not a module-level function bearing its local name.
        if "<locals>" in getattr(o, "__qualname__", ""):
            raise Unsupported("function closure")
        if mod.startswith("sympy") or mod == "math":
            return {"t": "JsFunc", "name": ("math." if mod == "math" else "") + o.__name__}
        if (mod, o.__name__) in (("builtins", "len"), ("_operator", "ge")):
            return {"t": "JsFunc", "name": mod + "." + o.__name__}
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
        return {"t": "Indexed", "base": ser(o.base), "indices": [ser(i) for i in o.indices]}
    if isinstance(o, sympy.IndexedBase):
        return {"t": "IndexedBase", "label": ser(o.label),
                **({"shape": [ser(d) for d in o.shape]} if o.shape is not None else {})}
    from sympy.polys.rootoftools import _pure_key_dict
    if isinstance(o, _pure_key_dict):
        return {"t": "PureKeyDict", "items": [[ser(k), ser(v)] for k, v in o._dict.items()]}
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
    # polynomial-ring elements are dicts: serialized with their ring before the dict branch
    from sympy.polys.rings import PolyElement as _PolyEl0
    from sympy.polys.fields import FracElement as _FracEl0
    from sympy.polys.puiseux import PuiseuxRing as _PuiR, PuiseuxPoly as _PuiP
    from sympy.polys.domains.mpelements import RealElement as _RealEl
    if isinstance(o, _PolyEl0):
        return {"t": "PolyElement", "ring": ser(o.ring), "expr": ser(o.as_expr())}
    if isinstance(o, _FracEl0):
        return {"t": "FracElement", "field": ser(o.field), "numer": ser(o.numer.as_expr()), "denom": ser(o.denom.as_expr())}
    if o is _PuiP:
        return {"t": "Type", "name": "PuiseuxPoly"}
    if isinstance(o, _PuiR):
        return {"t": "PuiseuxRing", "symbols": [ser(s) for s in o.symbols], "domain": ser(o.domain)}
    if isinstance(o, _PuiP):
        K = o.ring.domain
        return {"t": "PuiseuxPoly", "ring": ser(o.ring),
                "terms": [[[ser(sympy.Rational(int(e.numerator), int(e.denominator))) for e in m], ser(K.to_sympy(c))] for m, c in o.terms()]}
    if isinstance(o, _RealEl):
        return ser(sympy.Float(o))
    if isinstance(o, (set, frozenset)):
        return {"t": "JsSet", "items": [ser(i) for i in o]}
    if isinstance(o, list):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, range) or type(o).__name__ in ("dict_keys", "dict_values"):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, (tuple, Tuple)):
        return {"t": "Tuple", "items": [ser(i) for i in o]}
    from sympy.stats.frv import FiniteDensity as _FiniteDensity
    if isinstance(o, _FiniteDensity):
        return {"t": "FiniteDensity", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, dict):
        return {"t": "Dict", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, sympy.Dict):
        # a SymPy Dict (Diagram.premises, ...): printed like a dict
        return {"t": "Dict", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, MatrixBase):
        sparse = isinstance(o, sympy.matrices.sparse.SparseRepMatrix)
        return {"t": "Matrix", "rows": [[ser(o[i, j]) for j in range(o.cols)] for i in range(o.rows)], "shape": [o.rows, o.cols], **({"sparse": True} if sparse else {})}
    from sympy.core.function import UndefinedFunction as _UF
    if isinstance(o, _UF):
        return {"t": "UFnClass", "name": o.__name__, **({"nargs": sorted(int(n) for n in o.nargs)} if o.nargs != sympy.S.Naturals0 else {})}
    if isinstance(o, sympy.polys.polytools.GroebnerBasis):
        return {"t": "Groebner", "exprs": [ser(e) for e in o.exprs], "gens": [ser(g) for g in o.gens], "order": str(o.order)}
    if isinstance(o, sympy.Poly):
        return {"t": "Poly", "expr": ser(o.as_expr()), "gens": [ser(g) for g in o.gens], "domain": str(o.get_domain()), "pure": isinstance(o, sympy.PurePoly)}
    if isinstance(o, type) and issubclass(o, Basic) and not isinstance(o, sympy.FunctionClass):
        return {"t": "Type", "name": o.__name__}
    if isinstance(o, type) and o.__name__ in ("Matrix", "MutableDenseMatrix", "ImmutableMatrix", "ImmutableDenseMatrix"):
        return {"t": "Type", "name": "Matrix"}
    if isinstance(o, type) and o.__module__ in ("sympy.polys.matrices.domainmatrix", "sympy.polys.matrices.ddm", "sympy.polys.matrices.sdm") and o.__name__ in ("DomainMatrix", "DDM", "SDM"):
        # the DomainMatrix classes, whose classmethods (eye, diag, zeros, ...) the doctests call
        return {"t": "Type", "name": o.__name__}
    if isinstance(o, type) and o.__module__.startswith("sympy.combinatorics."):
        # combinatorics classes whose classmethods the doctests call (Subset.bitlist_from_subset, ...)
        return {"t": "Type", "name": o.__name__}
    from sympy.core.function import WildFunction as _WF
    if isinstance(o, sympy.FunctionClass) and not isinstance(o, _UF):
        return {"t": "FnClass", "name": o.__name__}
    from sympy.polys.domains.domain import Domain as _Domain
    from sympy.polys.agca.extensions import MonogenicFiniteExtension as _FiniteExtension
    if isinstance(o, _FiniteExtension):
        return {"t": "FiniteExtension", "modulus": ser(o.modulus)}
    from sympy.polys.rings import PolyRing as _PolyRing, PolyElement as _PolyElement
    from sympy.polys.fields import FracField as _FracField, FracElement as _FracElement
    from sympy.polys.matrices import DomainMatrix as _DM
    from sympy.polys.matrices.ddm import DDM as _DDM
    from sympy.polys.matrices.sdm import SDM as _SDM
    from sympy.polys.matrices.domainscalar import DomainScalar as _DS
    from sympy.polys.orderings import MonomialOrder as _MO
    if type(o).__name__ in ("PythonMPQ", "mpq"):
        # a QQ element (the ground type of QQ)
        return {"t": "Rational", "p": str(o.numerator), "q": str(o.denominator), "mpq": True}
    from sympy.polys.domains.gaussiandomains import GaussianElement as _GE
    from sympy.polys.polyclasses import ANP as _ANP
    if isinstance(o, _GE):
        # an element x + y*I of ZZ_I or QQ_I
        return {"t": "GaussianElement", "domain": str(o.parent()), "x": ser(o.x), "y": ser(o.y)}
    if isinstance(o, _ANP):
        # an element of an algebraic number field: coefficients in the primitive element, its minimal polynomial
        return {"t": "ANP", "rep": [ser(c) for c in o.to_list()], "mod": [ser(c) for c in o.mod_to_list()], "dom": ser(o.dom)}
    if isinstance(o, _Domain):
        d = {"t": "Domain", "name": str(o)}
        if o.is_FiniteField:
            d.update(mod=int(o.mod), symmetric=bool(o.sym))
        elif o.is_AlgebraicField:
            d.update(base=ser(o.dom), ext=ser(o.ext.as_expr()), gens=[ser(e) for e in o.orig_ext])
            if o.ext.is_aliased or o.ext.root.is_Symbol:
                # a primitive element given by its minimal polynomial (a symbol root, or an alias such as
                # zeta or theta): the field is rebuilt from the polynomial
                d.update(minpoly=ser(o.ext.minpoly_of_element()), alias=str(o.ext.alias) if o.ext.is_aliased else None)
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
    from sympy.assumptions.cnf import CNF as _CNF, EncodedCNF as _ECNF, Literal as _Lit
    if isinstance(o, _Lit):
        return {"t": "CNFLiteral", "lit": ser(o.lit), "isNot": bool(o.is_Not)}
    if isinstance(o, _CNF):
        # clauses and literals in a deterministic order (they are sets)
        return {"t": "CNF", "clauses": sorted([sorted([ser(l) for l in c], key=json.dumps) for c in o.clauses], key=json.dumps)}
    if isinstance(o, _ECNF):
        return {"t": "EncodedCNF", "data": [sorted(int(i) for i in c) for c in o.data],
                "encoding": [[ser(k), int(v)] for k, v in o.encoding.items()]}
    from sympy.utilities.enumerative import MultisetPartitionTraverser as _MPT
    if type(o) is _MPT:
        # a stateless helper object: constructed anew
        return {"t": "New", "cls": "MultisetPartitionTraverser"}
    from sympy.ntheory.elliptic_curve import EllipticCurve as _EC, EllipticCurvePoint as _ECP
    if isinstance(o, _EC):
        to = o._domain.to_sympy
        return {"t": "EllipticCurve", "coeffs": [ser(to(a)) for a in (o._a4, o._a6, o._a1, o._a2, o._a3)], "modulus": int(o.modulus)}
    if isinstance(o, _ECP):
        to = o._domain.to_sympy
        return {"t": "EllipticCurvePoint", "coords": [ser(to(a)) for a in (o.x, o.y, o.z)], "curve": ser(o._curve)}
    import mpmath as _mpmath
    if isinstance(o, (_mpmath.mpf, _mpmath.ctx_mp_python._constant)):
        # an mpmath real (mpf, or a constant such as mpmath.pi): the Float of its value at the working precision
        return ser(sympy.Float(o))
    if not isinstance(o, Basic):
        raise Unsupported(type(o).__name__)
    from sympy.algebras.quaternion import Quaternion as _Q
    if isinstance(o, _Q):
        return {"t": "Quaternion", "args": [ser(a) for a in o.args], "realField": bool(o.real_field),
                "norm": None if o._norm is None else ser(o._norm)}
    from sympy.sets.ordinals import Ordinal as _Ordinal, OmegaPower as _OmegaPower
    if isinstance(o, _Ordinal):
        return {"t": "Ordinal", "terms": [ser(t) for t in o.terms]}
    if isinstance(o, _OmegaPower):
        return {"t": "OmegaPower", "exp": ser(o.exp), "mult": str(o.mult)}
    if isinstance(o, sympy.PowerSet):
        return {"t": "PowerSet", "set": ser(o.args[0])}
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
    if type(o) is _seqs.SeqExpr:
        return {"t": "SeqExpr", "gen": ser(o.gen), "limits": ser(o.args[1])}
    if type(o) is _seqs.SeqExprOp:
        return {"t": "SeqExprOp", "args": [ser(a) for a in o.args]}
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
        return {"t": "AlgebraicNumber", "root": ser(o.root), "coeffs": [ser(c) for c in o.coeffs()],
                **({"alias": ser(o.alias)} if o.is_aliased else {})}
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
                  sympy.S.UniversalSet: "UniversalSet", sympy.S.Rationals: "Rationals"}
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
        a = symbol_assumptions(o)
        return {"t": "Wild", "name": o.name, "exclude": [ser(e) for e in o.exclude], "assume": a, "props": props}
    if isinstance(o, _WF):
        nargs = o.nargs
        lst = None if nargs == sympy.S.Naturals0 else sorted(int(n) for n in nargs)
        return {"t": "WildFunction", "name": o.name, "nargs": lst}
    if isinstance(o, sympy.Dummy):
        a = symbol_assumptions(o)
        # indices are renumbered per case so that the corpus is reproducible
        idx = DUMMY_IDS.setdefault(o.dummy_index, len(DUMMY_IDS))
        # a default name carries the global index, which depends on what ran before
        name = f"Dummy_{idx}" if o.name == f"Dummy_{o.dummy_index}" else o.name
        return {"t": "Dummy", "name": name, "index": idx, "assume": a}
    if o.is_Symbol and type(o) is Symbol:
        a = symbol_assumptions(o)
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
        return {"t": "UFnClass", "name": o.__name__, **({"nargs": sorted(int(n) for n in o.nargs)} if o.nargs != sympy.S.Naturals0 else {})}
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
    if o.is_Function or name in ("Piecewise", "Integral", "NonElementaryIntegral", "Derivative", "Limit", "Order", "Sum", "Product"):
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
    if isinstance(node, ast.Call):
        factory = eval(compile(ast.Expression(node.func), "<factory>", "eval"), globs)
        from sympy.strategies.tools import subs as strategy_subs
        if factory is strategy_subs and len(node.args) == 1 and not node.keywords:
            return {"t": "StrategySubs", "mapping": ser_arg(node.args[0], globs)}
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
        if isinstance(body, (int, float)) and not isinstance(body, bool):
            body = sympy.sympify(body)
        if not isinstance(body, Basic) or isinstance(body, sympy.logic.boolalg.BooleanAtom):
            raise Unsupported("function")
        return {"t": "JsLambda", "params": [ser(d) for d in ds], "body": ser(body)}
    return ser(eval(compile(ast.Expression(node), "<a>", "eval"), globs))


# functions that mutate their arguments (besides the ddm_i* ones): their arguments are serialized before the call
MUTATING_FUNCTIONS = {"define_schreier_generators", "reidemeister_relators", "elimination_technique_2"}


# the number-field doctests print their modules, elements and ideals (print(A)) and combine them with
# operators (e + f, e ** 2, f // g): these are recorded as the special methods __str__, __add__, ...
VALUE_EXAMPLE_MODULES = {"sympy.polys.numberfields.modules", "sympy.polys.numberfields.primes"}
# These examples display the complete tuple produced by a saved public call.
TUPLE_ASSIGNMENT_MODULES = {"sympy.polys.modulargcd"}
_VALUE_OPS = {ast.Add: "__add__", ast.Sub: "__sub__", ast.Mult: "__mul__", ast.Pow: "__pow__",
              ast.FloorDiv: "__floordiv__", ast.Mod: "__mod__"}


def value_example(node, globs):
    """The record of print(<name or attribute>) or of <a> <op> <b> for a number-field object a, or None."""
    from sympy.polys.numberfields.modules import Module, ModuleElement
    from sympy.polys.numberfields.primes import PrimeIdeal
    objects = (Module, ModuleElement, PrimeIdeal)
    ev = lambda n: eval(compile(ast.Expression(n), "<a>", "eval"), globs)
    DUMMY_IDS.clear()
    try:
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print" and len(node.args) == 1
                and not node.keywords and isinstance(node.args[0], (ast.Name, ast.Attribute))):
            v = ev(node.args[0])
            if isinstance(v, objects):
                return {"fn": ".__str__", "self": ser(v), "args": [], "kwargs": {}, "text": True, "expected": str(v)}
        if isinstance(node, ast.BinOp) and type(node.op) in _VALUE_OPS:
            a = ev(node.left)
            if isinstance(a, objects):
                return {"fn": "." + _VALUE_OPS[type(node.op)], "self": ser(a), "args": [ser(ev(node.right))], "kwargs": {},
                        "expected": str(ev(node))}
    except Exception:
        return None
    return None


# Python operators, comparisons, attribute reads and subscripts of SymPy objects in a doctest
# (g * f, a == b, D.diagonal_length, a[0, 0], Cycle(1, 2)(2, 3)): recorded as calls of the special methods
# (__mul__, __eq__, __getitem__, __call__) or of the attribute (".diagonal_length" with no arguments)
OPERATOR_FNS = {".__add__", ".__sub__", ".__mul__", ".__truediv__", ".__pow__", ".__floordiv__", ".__mod__",
                ".__matmul__", ".__and__", ".__or__", ".__xor__", ".__rshift__", ".__lshift__", ".__eq__", ".__ne__",
                ".__lt__", ".__le__", ".__gt__", ".__ge__", ".__contains__", ".__neg__", ".__invert__", ".__getitem__",
                ".__call__"}
_SYN_BINOPS = {ast.Add: "__add__", ast.Sub: "__sub__", ast.Mult: "__mul__", ast.Div: "__truediv__", ast.Pow: "__pow__",
               ast.FloorDiv: "__floordiv__", ast.Mod: "__mod__", ast.MatMult: "__matmul__", ast.BitAnd: "__and__",
               ast.BitOr: "__or__", ast.BitXor: "__xor__", ast.RShift: "__rshift__", ast.LShift: "__lshift__"}
_SYN_CMPOPS = {ast.Eq: "__eq__", ast.NotEq: "__ne__", ast.Lt: "__lt__", ast.LtE: "__le__", ast.Gt: "__gt__", ast.GtE: "__ge__"}
_SYN_UNOPS = {ast.USub: "__neg__", ast.Invert: "__invert__"}


def synthetic_call(node):
    """An equivalent call (method name, receiver node, argument nodes) of an operator, comparison,
    attribute read or subscript expression, or None."""
    if isinstance(node, ast.Attribute) and not node.attr.startswith("_"):
        return node.attr, node.value, []
    if isinstance(node, ast.Subscript) and not isinstance(node.slice, ast.Slice):
        return "__getitem__", node.value, [node.slice]
    if isinstance(node, ast.BinOp) and type(node.op) in _SYN_BINOPS:
        if isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
            # Python string formatting ('%s' % x)
            return None
        return _SYN_BINOPS[type(node.op)], node.left, [node.right]
    if isinstance(node, ast.UnaryOp) and type(node.op) in _SYN_UNOPS:
        return _SYN_UNOPS[type(node.op)], node.operand, []
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        if type(op) in _SYN_CMPOPS:
            return _SYN_CMPOPS[type(op)], node.left, [node.comparators[0]]
        if isinstance(op, ast.In):
            return "__contains__", node.comparators[0], [node.left]
    if (isinstance(node, ast.Call) and not isinstance(node.func, (ast.Name, ast.Attribute))
            and not any(isinstance(a, ast.Starred) for a in node.args) and not node.keywords):
        return "__call__", node.func, list(node.args)
    return None


# per-example limit, generous so that the corpus does not depend on the machine load
ALARM_SECONDS = 30


def _alarm(signum, frame):
    raise Timeout()


# keep printed text output (print(f(...)), pprint(...), print_tree(...), srepr(...)) as text cases
TEXT_OUTPUT = os.environ.get("TEXT_OUTPUT", "1") == "1"
# measure only these modules (comma-separated prefixes) when set
ONLY = [m for m in os.environ.get("ONLY_MODULES", "").split(",") if m]


def public_api_reason(fn, globs, extra_public):
    """The ordinary-call public API filter, also used for saved assignments."""
    if fn.startswith("."):
        if fn[1:].startswith("_") and fn not in OPERATOR_FNS:
            return "private-api"
    elif ((fn not in PUBLIC and fn not in extra_public)
          or fn in globs and (getattr(globs[fn], "__module__", None) or "__").startswith("__")):
        return "not-exported-api"
    return None


def serialize_call(record, call, globs, assumed, pre_args=None, printed=False):
    """Freeze a call's receiver, arguments and assumptions at the current state."""
    DUMMY_IDS.clear()
    if "selfSrc" in record:
        receiver_src = record.pop("selfSrc")
        receiver = eval(receiver_src, globs)
        if record.pop("synthetic", False) and not is_sympy_operand(
                receiver, [eval(compile(ast.Expression(a), "<a>", "eval"), globs) for a in call.args]):
            raise NotSympy()
        if printed and isinstance(receiver, types.ModuleType):
            raise PythonRuntime()
        record["self"] = ser_arg(ast.parse(receiver_src, mode="eval").body, globs) if callable(receiver) else ser(receiver)
    record["args"] = pre_args if pre_args is not None else [ser_arg(a, globs) for a in call.args]
    record["kwargs"] = {k.arg: ser_arg(k.value, globs) for k in call.keywords}
    if assumed:
        record["assume"] = [ser(a) for a in assumed]


def assignment_bindings(src, globs, extra_public):
    """Capture one direct call before assignment execution, for consecutive displays.

    Nested/starred targets and multiple statements cannot be replayed by one
    optional result index. Unsupported inputs stay measurable, as for calls.
    """
    tree = ast.parse(src, mode="exec")
    if len(tree.body) != 1 or not isinstance(tree.body[0], ast.Assign):
        return {}
    assignment = tree.body[0]
    if len(assignment.targets) != 1 or not isinstance(assignment.value, ast.Call):
        return {}
    target, call = assignment.targets[0], assignment.value
    if isinstance(target, ast.Name):
        names = [target.id]
        unpacked = False
    elif isinstance(target, (ast.Tuple, ast.List)) and all(isinstance(t, ast.Name) for t in target.elts):
        names = [t.id for t in target.elts]
        unpacked = True
    else:
        return {}
    if len(set(names)) != len(names) or any(isinstance(a, ast.Starred) for a in call.args) or any(k.arg is None for k in call.keywords):
        return {}
    if isinstance(call.func, ast.Name):
        record = {"fn": call.func.id}
    elif isinstance(call.func, ast.Attribute):
        record = {"fn": "." + call.func.attr, "selfSrc": ast.unparse(call.func.value)}
    else:
        return {}
    if public_api_reason(record["fn"], globs, extra_public):
        return {}
    from sympy.assumptions import global_assumptions
    try:
        serialize_call(record, call, globs, list(global_assumptions))
    except Unsupported as err:
        record.pop("selfSrc", None)
        record["unsupportedArg"] = str(err)
    return {name: {**record, **({"pick": i} if unpacked else {})} for i, name in enumerate(names)}


def preserve_references(cases, baseline):
    """Keep established inputs when an expansion changes incidental reference state.

    Anonymous Dummy names contain a process-global counter, while their serialized
    index is the actual identity. One existing membership example uses an external
    random sampler. Neither is a reason to replace an established reference input.
    Older corpora omitted sparse storage metadata and could not serialize DMP
    inputs. Match their original representation too, without changing any value
    they did record. Other changes or missing occurrences remain errors.
    """
    def canonical(value):
        if isinstance(value, list):
            return [canonical(v) for v in value]
        if isinstance(value, dict):
            result = {k: canonical(v) for k, v in value.items()}
            if result.get("t") == "Dummy" and re.fullmatch(r"Dummy_\d+", str(result.get("name", ""))):
                result["name"] = "anonymous:" + str(result["index"])
            # Dummy hashes can change a map built from a set's insertion order.
            # xreplace is simultaneous: its mapping order has no semantics.
            if result.get("fn") == ".xreplace":
                args = result.get("args", [])
                if len(args) == 1 and args[0].get("t") == "Dict":
                    args[0]["items"].sort(key=lambda pair: json.dumps(pair, sort_keys=True))
            # Preserve this fixture's original sampled real value. The operation,
            # set, result and all other input properties must still match.
            if (result.get("module"), result.get("src")) == ("sympy.stats.rv", "samp in N.pspace.domain.set"):
                args = result.get("args", [])
                if len(args) == 1 and args[0].get("t") == "Float":
                    args[0]["v"] = "recorded real sample"
            return result
        return value

    key = lambda c: json.dumps(c, sort_keys=True, ensure_ascii=False)

    def legacy_serialization(case):
        def tree(value):
            if isinstance(value, list):
                return [tree(v) for v in value]
            if isinstance(value, dict):
                if value.get("t") == "DMP":
                    raise Unsupported("DMP_Python")
                return {k: tree(v) for k, v in value.items() if not (value.get("t") == "Matrix" and k == "sparse")}
            return value

        # Serialization stops at the first unsupported input, retaining only
        # previously completed fields. Reproduce precisely that legacy shape.
        inputs = ("self", "args", "kwargs", "assume")
        result = {k: v for k, v in case.items() if k not in inputs}
        try:
            for field in inputs:
                if field in case:
                    result[field] = tree(case[field])
        except Unsupported as err:
            result["unsupportedArg"] = str(err)
        return result

    available = defaultdict(list)
    for case in baseline:
        available[key(canonical(case))].append(case)
    result, preserved, added = [], [], []
    for case in cases:
        matches = available.get(key(canonical(case)), [])
        reason = "Preserve established anonymous Dummy names, simultaneous replacement-map order or the recorded external real sample."
        if not matches:
            matches = available.get(key(canonical(legacy_serialization(case))), [])
            reason = "Preserve established inputs from before sparse-matrix metadata and DMP serialization."
        if matches:
            original = matches.pop(0)
            if case != original:
                preserved.append({"module": case["module"], "src": case["src"],
                                  "reason": reason})
            # Keep key order too: compatibility case hashes use JSON.stringify.
            result.append(original)
        else:
            result.append(case)
            added.append(case)
    missing = Counter(key(c) for c in baseline) - Counter(key(c) for c in result)
    if missing:
        labels = sorted({f"{json.loads(k)['module']}: {json.loads(k)['src']}" for k in missing})
        raise ValueError(f"Expansion lost or changed {sum(missing.values())} baseline cases: " + "; ".join(labels))
    # Append new examples after the unchanged baseline. This keeps old corpus
    # diffs small and avoids interleaving additions from concurrent worktrees.
    return list(baseline) + added, preserved


def main(dst, baseline_path=None):
    if sympy.__version__ != "1.14.0":
        raise RuntimeError("The compatibility reference is pinned to SymPy 1.14.0")
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
            bindings = {}
            for ex in test.examples:
                extraction["examined"] += 1
                src = ex.source.strip()
                if ex.options.get(doctest.SKIP):
                    bindings = {}
                    omit("upstream-skip", modname, ex)
                    # SymPy does not run these either (random or illustrative output)
                    continue
                if re.fullmatch(r"[\w.]+\(\.\.\.\)", ex.want.strip()):
                    bindings = {}
                    omit("illustrative-output", modname, ex)
                    # only the class of the result is shown (random output elided with ELLIPSIS)
                    continue
                try:
                    tree = ast.parse(src, mode="eval")
                except SyntaxError:
                    bindings = {}
                    omit("statement-or-setup", modname, ex)
                    # statements (assignments, imports): just execute
                    try:
                        signal.alarm(ALARM_SECONDS)
                        try:
                            bindings = assignment_bindings(src, globs, extra_public)
                        except Exception:
                            # An unserializable setup still has to execute.
                            bindings = {}
                        signal.alarm(ALARM_SECONDS)
                        exec(compile(src, "<doctest>", "exec"), globs)
                    except (Exception, Timeout):
                        bindings = {}
                    finally:
                        signal.alarm(0)
                    continue
                call = tree.body
                bound = bindings.get(call.id) if isinstance(call, ast.Name) and ex.want.strip() else None
                if modname in TUPLE_ASSIGNMENT_MODULES and isinstance(call, ast.Tuple) and ex.want.strip():
                    saved = [bindings.get(n.id) if isinstance(n, ast.Name) else None for n in call.elts]
                    if saved and all(r is not None and r.get("pick") == i for i, r in enumerate(saved)):
                        records = [{k: v for k, v in r.items() if k != "pick"} for r in saved]
                        if all(r == records[0] for r in records) and len(saved) == len(bindings):
                            bound = records[0]
                if bound is None:
                    bindings = {}
                if modname in VALUE_EXAMPLE_MODULES:
                    record = value_example(call, globs)
                    if record is not None:
                        record.update({"category": category, "module": modname, "src": src})
                        cases.append(record)
                        continue
                record = dict(bound) if bound is not None else None
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
                if record is None and not printed:
                    syn = synthetic_call(call)
                    if syn is not None:
                        name, receiver, arg_nodes = syn
                        record = {"fn": "." + name, "selfSrc": ast.unparse(receiver), "synthetic": True}
                        call = ast.Call(func=ast.Attribute(value=receiver, attr=name, ctx=ast.Load()), args=arg_nodes, keywords=[])
                from sympy.assumptions import global_assumptions as _ga
                assumed = list(_ga)
                # the in-place functions of sympy.polys.matrices.dense (ddm_iadd, ddm_idet, ...) mutate their
                # arguments: these are serialized as they are before the call
                pre_args = None
                if bound is None and record is not None and (record["fn"].startswith("ddm_i") or record["fn"] in MUTATING_FUNCTIONS):
                    try:
                        pre_args = [ser_arg(a, globs) for a in call.args]
                    except Exception:
                        pre_args = None
                try:
                    signal.alarm(ALARM_SECONDS)
                    _out = io.StringIO()
                    with contextlib.redirect_stdout(_out):
                        result = eval(compile(tree, "<doctest>", "eval"), globs)
                except (Exception, Timeout) as err:
                    bindings = {}
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
                reason = public_api_reason(fn, globs, extra_public) if bound is None else None
                if reason:
                    omit(reason, modname, ex)
                    continue
                try:
                    if bound is None:
                        serialize_call(record, call, globs, assumed, pre_args, printed)
                    elif "unsupportedArg" in record:
                        skipped[record["unsupportedArg"]] = skipped.get(record["unsupportedArg"], 0) + 1
                except PythonRuntime:
                    omit("python-runtime-api", modname, ex)
                    continue
                except NotSympy:
                    omit("non-call-expression", modname, ex)
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
                elif (type(result).__module__ or "").startswith("sympy.combinatorics.") and " object at 0x" not in str(result):
                    # free and finitely presented group objects (words, groups, coset tables): compared by str()
                    expected = str(result)
                elif ((type(result).__module__ or "").startswith(("sympy.polys", "sympy.matrices", "sympy.external", "sympy.holonomic"))
                        or type(result).__name__ in ("mpq", "mpz")):
                    # polynomial-ring elements (PolyElement prints as x**2 + 1/2*y), domains (QQ<sqrt(2)>, GF(5)),
                    # DomainMatrix/DDM/SDM, DMP, ANP, ground elements (MPQ(1,2)), holonomic functions and
                    # operators: compared by str()
                    expected = str(result)
                else:
                    omit("unsupported-result-type", modname, ex)
                    continue
                if re.search(r"<[^<>\n]*\bat 0x[0-9a-fA-F]+>", expected):
                    # Object identities are process-local, not mathematical
                    # reference values (for example hypergeometric operators).
                    omit("unstable-result-representation", modname, ex)
                    continue
                # Multiline str() output is still a result: matrices nested in
                # lists/tuples and module homomorphisms must remain measurable.
                record.update({"category": category, "module": modname, "src": src, "expected": expected})
                cases.append(record)
    if baseline_path is not None:
        with open(baseline_path, encoding="utf-8") as f:
            baseline = json.load(f)
        if baseline["sympy"] != sympy.__version__:
            raise ValueError("Baseline SymPy version differs from the pinned reference")
        cases, extraction["preservedReferences"] = preserve_references(cases, baseline["cases"])
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "api": api_inventory(), "cases": cases, "extraction": extraction}, f, indent=1, ensure_ascii=False)
        f.write("\n")
    by_cat = {}
    for c in cases:
        by_cat[c["category"]] = by_cat.get(c["category"], 0) + 1
    print(f"TOTAL {len(cases)} cases", by_cat, file=sys.stderr)
    print("skipped (unsupported arg types):", dict(sorted(skipped.items(), key=lambda kv: -kv[1])[:15]), file=sys.stderr)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination")
    parser.add_argument("--baseline", help="Preserve every existing case while expanding this corpus")
    args = parser.parse_args()
    main(args.destination, args.baseline)
