#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Pin the entire SymPy module universe, including unmeasured modules.

This static scan never imports optional backends or executes doctests. Complete
modules satisfy public API, doctest, unit-test and limitation criteria from the
committed measurements. Source size is not a measure of compatibility.
"""
import ast
from collections import Counter, defaultdict
from functools import cache
import doctest
import hashlib
import json
import re
from pathlib import Path
import sys
import sympy

EXCLUSIONS = {
    'sympy.plotting': 'Rendering backends and interactive plotting are separate from the symbolic engine.',
    'sympy.interactive': 'Python REPL/session integration does not apply to the JavaScript runtime.',
    'sympy.testing': 'Upstream test runners are infrastructure, not mathematical APIs.',
    'sympy.external': 'Python bindings to optional external libraries are runtime-specific.',
    'sympy.multipledispatch': 'Python dispatch infrastructure is replaced by TypeScript expression dispatch.',
    'sympy.parsing.autolev._antlr': 'Generated Python parser runtime; an equivalent parser may be supplied separately.',
    'sympy.parsing.latex._antlr': 'Generated Python parser runtime; this does not exclude the LaTeX parsing feature.',
    'sympy.stats.sampling': 'External sampling-library adapters; symbolic probability remains in scope.',
    'sympy.categories.diagram_drawing': 'diagram drawing',
    'sympy.polys.domains.gmpyintegerring': 'Ground-type backend binding gmpy2/python-flint; ZZ itself is in scope (domains.integerring).',
    'sympy.polys.domains.gmpyrationalfield': 'Ground-type backend binding gmpy2/python-flint; QQ itself is in scope (domains.rationalfield).',
    'sympy.polys.domains.gmpyfinitefield': 'Ground-type backend binding gmpy2/python-flint; GF(p) itself is in scope (domains.finitefield).',
    'sympy.polys.domains.pythonintegerring': 'Pure-Python ground-type fallback of ZZ; symjs has a single bigint ground type.',
    'sympy.polys.domains.pythonrationalfield': 'Pure-Python ground-type fallback of QQ; symjs has a single rational ground type.',
    'sympy.polys.domains.pythonfinitefield': 'Pure-Python ground-type fallback of GF(p); symjs has a single ground type.',
    'sympy.polys.domains.pythonrational': 'Pure-Python mpq replacement used when gmpy2 is absent; symjs rationals are Rational.',
    'sympy.polys.domains.groundtypes': 'Selection of the Python ground-type backend (gmpy2/flint/python) at import time.',
    'sympy.polys.matrices._dfm': 'python-flint fmpz_mat/fmpq_mat binding behind DomainMatrix; the DomainMatrix API stays in scope.',
    'sympy.polys.matrices.dfm': 'Import shim for the python-flint DFM backend.',
    'sympy.polys.matrices._typing': 'typing.Protocol declarations for static type checking; no runtime behavior.',
    'sympy.core._print_helpers': 'Python REPL/Jupyter display mixin (_repr_latex_, _repr_png_), runtime-specific.',
    'sympy.core.backend': 'Selects SymEngine or SymPy classes for sympy.physics.mechanics (Python backend switch).',
    'sympy.core.cache': 'Python memoization (cacheit, lazy_function, cached_property), runtime infrastructure.',
    'sympy.core.compatibility': 'Deprecated Python compatibility shim (its live names are in sympy.core.sorting / utilities.iterables).',
    'sympy.core.core': 'Python class Registry base, runtime infrastructure.',
    'sympy.core.decorators': 'Python operator-dispatch decorators (call_highest_priority, sympify_method_args, sympify_return).',
    'sympy.core.multidimensional': 'Python decorator vectorize (function application over nested lists), runtime helper.',
    'sympy.integrals.meijerint_doc': 'Script that generates the documentation table of meijerint formulas (doc tooling).',
    'sympy.logic.algorithms.minisat22_wrapper': 'Python binding to the external MiniSat 2.2 library (like sympy.external).',
    'sympy.logic.algorithms.pycosat_wrapper': 'Python binding to the external pycosat library (like sympy.external).',
    'sympy.logic.algorithms.z3_wrapper': 'Python binding to the external Z3 solver (like sympy.external).',
    'sympy.simplify.hyperexpand_doc': 'Script that generates the documentation table of hyperexpand formulas (doc tooling).',
    'sympy.conftest': 'pytest configuration of the SymPy test suite.',
    'sympy.release': 'Python package version metadata.',
    'sympy.this': 'The Zen of SymPy text printed on import (Python easter egg).',
    'sympy.utilities.runtests': 'SymPy test runner.',
    'sympy.utilities.pytest': 'Deprecated alias of the test helpers.',
    'sympy.utilities.randtest': 'Deprecated alias of the test helpers.',
    'sympy.utilities.tmpfiles': 'Temporary-file helper of the test suite.',
    'sympy.utilities.timeutils': 'Python timing helpers (timed, timethis) for benchmarks.',
    'sympy.utilities.pkgdata': 'Python package resource loading.',
    'sympy.utilities.source': 'Imports Python objects by dotted path (get_class, get_mod_func).',
    'sympy.utilities.magic': 'Injects names into the calling Python namespace (pollute).',
    'sympy.utilities.exceptions': 'Python warnings-module machinery (SymPyDeprecationWarning, ignore_warnings); symjs marks deprecations with @deprecated JSDoc tags checked by TypeScript.',
    'sympy.utilities.matchpy_connector': 'Binding to the optional Python library matchpy (symjs has its own pattern matching).',
    'sympy.utilities.mathml': 'XSLT conversion of MathML with lxml (c2p, apply_xsl); the mathml printer produces presentation MathML directly.',
    'sympy.utilities._compilation': 'Compiler and Python-extension build helpers (used by autowrap).',
    'sympy.printing.preview': 'Renders LaTeX to an image with an external TeX installation and viewer (display, like plotting).',
    'sympy.printing.gtk': 'Opens a MathML viewer through GTK (display).',
    'sympy.printing.tensorflow': 'TensorFlow code for lambdify (not ported).',
    'sympy.printing.pytorch': 'PyTorch code for lambdify (Python numeric framework binding, like TensorFlow).',
    'sympy.printing.aesaracode': 'Aesara graph construction (Python numeric framework binding).',
    'sympy.printing.theanocode': 'Theano graph construction (Python numeric framework binding).',
    'sympy.printing.llvmjitcode': 'LLVM JIT compilation through llvmlite (Python native-code binding).',
    'sympy.parsing.ast_parser': "Alternative parse_expr over Python's own ast module (Python source); the grammar is covered by the sympy_parser port.",
    'sympy.parsing.latex._build_latex_antlr': 'Build script regenerating the ANTLR parser.',
    'sympy.parsing.autolev._build_autolev_antlr': 'Build script regenerating the ANTLR parser.',
    'sympy.parsing.autolev.test-examples': 'Example Autolev inputs and their generated Python (test data).',
    'sympy.galgebra': 'Removed from SymPy: the module only raises ImportError pointing to the external galgebra package.',
    'sympy.printing.pycode': 'Generates or compiles Python code.',
    'sympy.printing.numpy': 'Generates or compiles Python code.',
    'sympy.printing.lambdarepr': 'Generates or compiles Python code.',
    'sympy.printing.python': 'Generates or compiles Python code.',
    'sympy.utilities.autowrap': 'Generates or compiles Python code.',
    'sympy.codegen.pyutils': 'Generates or compiles Python code.',
    'sympy.printing.jscode': 'JavaScript source output; symjs evaluates expressions in JavaScript directly (lambdify) instead of emitting JavaScript code.',
    'sympy.sandbox': 'Experimental modules outside the public SymPy API.',
    'sympy.combinatorics.testutil': 'Naive reference implementations used by the SymPy unit tests (test utility).',
}

# Explicit correspondences for the different kernel layout and combined modules.
CORRESPONDENCES = {
    'sympy.polys.domains.mpelements': ['polys/domains/mpelements.ts'],
    'sympy.core.basic': ['core/basic.ts', 'core/compare.ts', 'core/nodes.ts'],
    'sympy.core.expr': ['core/nodes.ts', 'core/methods.ts', 'core/expr.ts'],
    'sympy.core.add': ['core/ops.ts'],
    'sympy.core.mul': ['core/ops.ts'],
    'sympy.core.power': ['core/ops.ts'],
    'sympy.core.function': ['core/undef.ts', 'core/defun.ts'],
    'sympy.core.symbol': ['core/nodes.ts', 'core/symbol.ts'],
    'sympy.core.numbers': ['core/numbers.ts', 'core/num.ts'],
    'sympy.assumptions.ask': ['core/refine.ts'],
    'sympy.assumptions.refine': ['core/refine.ts', 'assumptions/refine.ts'],
    'sympy.core.relational': ['core/logic.ts', 'core/relational.ts'],
    'sympy.core.sympify': ['core/sympify.ts', 'core/ops.ts', 'parsing/sympify.ts'],
    'sympy.core.traversal': ['core/traverse.ts'],
    'sympy.core.evalf': ['numeric/evalf.ts'],
    'sympy.polys.polytools': ['polys/sympoly.ts'],
    'sympy.polys.densearith': ['polys/densearith.ts'],
    'sympy.polys.modulargcd': ['polys/modulargcd.ts'],
    'sympy.polys.polyquinticconst': ['polys/polyquinticconst.ts'],
    'sympy.polys.polyroots': ['polys/poly.ts', 'polys/polyroots.ts'],
    'sympy.polys.numberfields.minpoly': ['polys/numberfields.ts'],
    'sympy.integrals.integrals': ['integrals/integrate.ts'],
    'sympy.matrices.matrixbase': ['matrices/matrix.ts', 'matrices/more.ts'],
    'sympy.matrices.dense': ['matrices/matrix.ts'],
    'sympy.matrices.eigen': ['matrices/linalg.ts'],
    'sympy.matrices.decompositions': ['matrices/linalg.ts'],
    'sympy.solvers.solvers': ['solvers/solve.ts'],
    'sympy.solvers.ode.ode': ['solvers/ode.ts', 'solvers/dsolve.ts'],
    'sympy.solvers.ode.systems': ['solvers/odesystem.ts'],
    'sympy.solvers.ode.lie_group': ['solvers/liegroup.ts'],
    'sympy.solvers.diophantine.diophantine': ['solvers/diophantine.ts'],
    'sympy.tensor.array.ndim_array': ['tensor/ndimarray.ts'],
    'sympy.tensor.array.arrayop': ['tensor/arrayop.ts'],
    'sympy.combinatorics.tensor_can': ['tensor/tensorcan.ts'],
    'sympy.combinatorics.rewritingsystem_fsm': ['combinatorics/rewritingsystem.ts'],
    'sympy.combinatorics.perm_groups': ['combinatorics/permpresentation.ts'],
    'sympy.functions.elementary.trigonometric': ['functions/elementary/elementary.ts', 'functions/elementary/trigext.ts'],
    'sympy.functions.elementary.hyperbolic': ['functions/elementary/elementary.ts', 'functions/elementary/trigext.ts'],
    'sympy.functions.elementary.exponential': ['functions/elementary/elementary.ts'],
    'sympy.functions.special.gamma_functions': ['functions/special/special.ts'],
    'sympy.functions.special.error_functions': ['functions/special/special.ts'],
    'sympy.matrices': ['matrices.ts'],
    'sympy.matrices.expressions': ['matrices/expressions/index.ts'],
    'sympy.matrices.common': ['matrices/matrix.ts', 'matrices/more.ts'],
    'sympy.matrices.matrices': ['matrices/linalg.ts', 'matrices/matrix.ts', 'matrices/more.ts'],
    'sympy.matrices.repmatrix': ['matrices/matrix.ts', 'matrices/mutable.ts'],
    'sympy.matrices.immutable': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.determinant': ['matrices/linalg.ts', 'matrices/matrix.ts'],
    'sympy.matrices.inverse': ['matrices/linalg.ts'],
    'sympy.matrices.reductions': ['matrices/linalg.ts', 'matrices/linsys.ts'],
    'sympy.matrices.solvers': ['matrices/linalg.ts', 'matrices/linsys.ts'],
    'sympy.matrices.subspaces': ['matrices/linalg.ts'],
    'sympy.matrices.graph': ['matrices/linalg.ts', 'matrices/more.ts'],
    'sympy.matrices.exceptions': ['core/errors.ts'],
    'sympy.matrices.utilities': ['matrices/matrix.ts'],
    'sympy.matrices.sparsetools': ['matrices/sparsetools.ts'],
    'sympy.matrices.expressions._shape': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.adjoint': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.applyfunc': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.companion': ['matrices/expressions/misc.ts'],
    'sympy.matrices.expressions.determinant': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.dotproduct': ['matrices/expressions/misc.ts'],
    'sympy.matrices.expressions.factorizations': ['matrices/expressions/misc.ts'],
    'sympy.matrices.expressions.fourier': ['matrices/expressions/funcmatrix.ts'],
    'sympy.matrices.expressions.inverse': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.matadd': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.matmul': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.matpow': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.sets': ['matrices/expressions/misc.ts'],
    'sympy.matrices.expressions.slice': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.special': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.trace': ['matrices/expressions/matexpr.ts'],
    'sympy.matrices.expressions.transpose': ['matrices/expressions/matexpr.ts'],
    'sympy.polys': ['polys.ts'],
    'sympy.polys.domains': ['polys/domains.ts'],
    'sympy.polys.numberfields': ['polys/numberfields.ts'],
    'sympy.polys.matrices': ['matrices/domainmatrix.ts'],
    'sympy.polys.domainmatrix': ['matrices/domainmatrix.ts'],
    'sympy.polys.matrices.domainmatrix': ['matrices/domainmatrix.ts'],
    'sympy.polys.matrices.rref': ['matrices/linsys.ts'],
    'sympy.polys.matrices.lll': ['matrices/more.ts'],
    'sympy.polys.domains.domain': ['polys/domains.ts'],
    'sympy.polys.domains.domainelement': ['polys/domains.ts'],
    'sympy.polys.domains.ring': ['polys/domains.ts'],
    'sympy.polys.domains.field': ['polys/domains.ts'],
    'sympy.polys.domains.simpledomain': ['polys/domains.ts'],
    'sympy.polys.domains.compositedomain': ['polys/domains.ts'],
    'sympy.polys.domains.characteristiczero': ['polys/domains.ts'],
    'sympy.polys.domains.integerring': ['polys/domains.ts'],
    'sympy.polys.domains.rationalfield': ['polys/domains.ts'],
    'sympy.polys.domains.realfield': ['polys/domains.ts'],
    'sympy.polys.domains.expressiondomain': ['polys/domains.ts'],
    'sympy.polys.domains.polynomialring': ['polys/domains.ts'],
    'sympy.polys.domains.fractionfield': ['polys/domains.ts'],
    'sympy.polys.domains.old_polynomialring': ['polys/domains.ts'],
    'sympy.polys.domains.old_fractionfield': ['polys/domains.ts'],
    'sympy.polys.polyclasses': ['polys/domains.ts', 'polys/polyclasses.ts'],
    'sympy.polys.polyconfig': ['polys/domains.ts'],
    'sympy.polys.polyerrors': ['core/errors.ts', 'polys/polyerrors.ts'],
    'sympy.polys.polyoptions': ['polys/fromexpr.ts'],
    'sympy.polys.polyutils': ['polys/fromexpr.ts'],
    'sympy.polys.rationaltools': ['simplify/rational.ts'],
    'sympy.polys.rootoftools': ['polys/rootof.ts', 'polys/rootsum.ts'],
    'sympy.polys.appellseqs': ['polys/appellseqs.ts'],
    'sympy.polys.groebnertools': ['polys/groebner.ts'],
    'sympy.polys.heuristicgcd': ['polys/mpoly.ts'],
    'sympy.polys.factortools': ['polys/wang.ts', 'polys/zassenhaus.ts'],
    'sympy.polys.sqfreetools': ['polys/sympoly.ts'],
    'sympy.polys.subresultants_qq_zz': ['polys/sympoly.ts'],
    'sympy.polys.monomials': ['polys/monomial.ts'],
    'sympy.polys.orderings': ['polys/orderings.ts'],
    'sympy.polys.galoistools': ['polys/galoistools.ts'],
    'sympy.abc': ['core.ts'],
    'sympy.algebras': ['algebras.ts'],
    'sympy.assumptions': ['core/refine.ts'],
    'sympy.assumptions.ask_generated': ['core/refine.ts'],
    'sympy.assumptions.assume': ['core/refine.ts'],
    'sympy.assumptions.cnf': ['logic/inference.ts'],
    'sympy.assumptions.facts': ['core/refine.ts'],
    'sympy.assumptions.handlers': ['core/refine.ts'],
    'sympy.assumptions.handlers.calculus': ['core/refine.ts'],
    'sympy.assumptions.handlers.common': ['core/refine.ts'],
    'sympy.assumptions.handlers.matrices': ['assumptions/handlers/matrices.ts', 'core/refine.ts'],
    'sympy.assumptions.handlers.ntheory': ['core/refine.ts'],
    'sympy.assumptions.handlers.order': ['core/refine.ts'],
    'sympy.assumptions.handlers.sets': ['core/refine.ts'],
    'sympy.assumptions.predicates': ['core/refine.ts'],
    'sympy.assumptions.predicates.calculus': ['core/refine.ts'],
    'sympy.assumptions.predicates.common': ['core/refine.ts'],
    'sympy.assumptions.predicates.matrices': ['core/refine.ts'],
    'sympy.assumptions.predicates.ntheory': ['core/refine.ts'],
    'sympy.assumptions.predicates.order': ['core/refine.ts'],
    'sympy.assumptions.predicates.sets': ['core/refine.ts'],
    'sympy.assumptions.relation': ['core/refine.ts'],
    'sympy.assumptions.relation.binrel': ['core/refine.ts'],
    'sympy.assumptions.relation.equality': ['core/refine.ts'],
    'sympy.assumptions.sathandlers': ['assumptions/sathandlers.ts'],
    'sympy.assumptions.wrapper': ['assumptions/wrapper.ts'],
    'sympy.calculus': ['calculus.ts'],
    'sympy.calculus.accumulationbounds': ['core/accumbounds.ts', 'functions/elementary/accumbounds.ts'],
    'sympy.calculus.singularities': ['solvers/inequalities.ts', 'solvers/public.ts'],
    'sympy.calculus.util': ['solvers/calculusutil.ts', 'solvers/inequalities.ts', 'solvers/public.ts'],
    'sympy.combinatorics': ['combinatorics.ts', 'combinatorics/index.ts'],
    'sympy.combinatorics.group_numbers': ['combinatorics/groupnumbers.ts'],
    'sympy.combinatorics.schur_number': ['combinatorics/schurnumber.ts'],
    'sympy.concrete': ['concrete/summations.ts', 'core/concrete.ts'],
    'sympy.concrete.delta': ['concrete/delta.ts'],
    'sympy.concrete.expr_with_intlimits': ['core/concrete.ts'],
    'sympy.concrete.expr_with_limits': ['concrete/summations.ts', 'core/concrete.ts'],
    'sympy.concrete.gosper': ['concrete/gosper.ts'],
    'sympy.concrete.products': ['concrete/summations.ts', 'core/concrete.ts'],
    'sympy.core': ['core.ts'],
    'sympy.core.alphabets': ['printing/pretty/symbology.ts'],
    'sympy.core.assumptions_generated': ['core/assumptions.ts', 'core/facts.ts'],
    'sympy.core.coreerrors': ['core/errors.ts'],
    'sympy.core.exprtools': ['core/factors.ts', 'simplify/exprtools.ts'],
    'sympy.core.facts': ['core/assumptions.ts'],
    'sympy.core.intfunc': ['core/numberutils.ts', 'ntheory/intutil.ts'],
    'sympy.core.mod': ['functions/mod.ts'],
    'sympy.core.operations': ['core/nodes.ts', 'core/ops.ts'],
    'sympy.core.random': ['ntheory/random.ts'],
    'sympy.core.singleton': ['core/nodes.ts'],
    'sympy.core.sorting': ['core/match.ts', 'printing/sortkey.ts'],
    'sympy.crypto': ['crypto/index.ts'],
    'sympy.crypto.crypto': ['crypto/crypto.ts'],
    'sympy.discrete': ['discrete.ts', 'discrete/index.ts'],
    'sympy.functions': ['special.ts'],
    'sympy.functions.combinatorial': ['functions/combinatorial/numbers.ts', 'functions/special/special.ts'],
    'sympy.functions.combinatorial.factorials': ['functions/special/special.ts'],
    'sympy.functions.elementary': ['functions/elementary/elementary.ts'],
    'sympy.functions.elementary._trigonometric_special': ['functions/elementary/trigonometricspecial.ts'],
    'sympy.functions.elementary.integers': ['functions/combinatorial/numbers.ts', 'functions/special/special.ts'],
    'sympy.functions.elementary.miscellaneous': ['core/ops.ts', 'functions/special/special.ts'],
    'sympy.functions.elementary.piecewise': ['core/logic.ts', 'core/traverse.ts'],
    'sympy.functions.special': ['special.ts'],
    'sympy.functions.special.beta_functions': ['functions/special/special.ts'],
    'sympy.functions.special.delta_functions': ['integrals/transforms/delta.ts'],
    'sympy.functions.special.singularity_functions': ['integrals/transforms/delta.ts'],
    'sympy.geometry': ['geometry.ts'],
    'sympy.holonomic': ['holonomic.ts'],
    'sympy.integrals': ['integrals/integrate.ts'],
    'sympy.integrals.laplace': ['integrals/transforms/inverse-laplace.ts', 'integrals/transforms/laplace.ts'],
    'sympy.integrals.transforms': ['integrals/transforms/base.ts', 'integrals/transforms/fourier.ts', 'integrals/transforms/index.ts', 'integrals/transforms/mellin.ts'],
    'sympy.liealgebras': ['liealgebras/index.ts'],
    'sympy.liealgebras.cartan_matrix': ['liealgebras/cartanmatrix.ts'],
    'sympy.liealgebras.cartan_type': ['liealgebras/cartantype.ts', 'liealgebras/standard.ts'],
    'sympy.liealgebras.dynkin_diagram': ['liealgebras/dynkindiagram.ts'],
    'sympy.liealgebras.root_system': ['liealgebras/rootsystem.ts'],
    'sympy.liealgebras.type_a': ['liealgebras/typea.ts'],
    'sympy.liealgebras.type_b': ['liealgebras/typeb.ts'],
    'sympy.liealgebras.type_c': ['liealgebras/typec.ts'],
    'sympy.liealgebras.type_d': ['liealgebras/typed.ts'],
    'sympy.liealgebras.type_e': ['liealgebras/typee.ts'],
    'sympy.liealgebras.type_f': ['liealgebras/typef.ts'],
    'sympy.liealgebras.type_g': ['liealgebras/typeg.ts'],
    'sympy.liealgebras.weyl_group': ['liealgebras/weylgroup.ts'],
    'sympy.logic': ['logic.ts', 'logic/index.ts'],
    'sympy.logic.algorithms': ['logic/algorithms/dpll.ts', 'logic/dpll.ts'],
    'sympy.logic.algorithms.dpll': ['logic/algorithms/dpll.ts'],
    'sympy.logic.algorithms.dpll2': ['logic/algorithms/dpll.ts', 'logic/dpll.ts'],
    'sympy.logic.utilities': ['logic/utilities/dimacs.ts'],
    'sympy.logic.utilities.dimacs': ['logic/utilities/dimacs.ts'],
    'sympy.ntheory': ['ntheory.ts', 'ntheory/index.ts'],
    'sympy.ntheory.continued_fraction': ['ntheory/continued.ts'],
    'sympy.ntheory.egyptian_fraction': ['ntheory/egyptian.ts'],
    'sympy.ntheory.residue_ntheory': ['functions/combinatorial/numbers.ts', 'ntheory/residue.ts'],
    'sympy.parsing.sympy_parser': ['parsing/parser.ts'],
    'sympy.parsing.latex': ['parsing/latex/index.ts'],
    'sympy.parsing.latex._parse_latex_antlr': ['parsing/latex/_parse_latex_antlr.ts'],
    'sympy.parsing.latex.errors': ['parsing/latex/errors.ts'],
    'sympy.parsing.latex.lark': ['parsing/latex/lark/latex_parser.ts'],
    'sympy.parsing.latex.lark.latex_parser': ['parsing/latex/lark/latex_parser.ts', 'parsing/latex/lark/grammar/latex.ts', 'parsing/latex/lark/grammar/greek_symbols.ts', 'parsing/latex/lexer.ts', 'parsing/latex/tree.ts'],
    'sympy.parsing.latex.lark.transformer': ['parsing/latex/lark/transformer.ts'],
    'sympy.series': ['calculus.ts'],
    'sympy.series.acceleration': ['numeric/mphyper.ts'],
    'sympy.series.aseries': ['series/series.ts'],
    'sympy.series.kauers': ['series/kauers.ts'],
    'sympy.series.order': ['core/nodes.ts', 'series/series.ts'],
    'sympy.series.series_class': ['series/series_class.ts'],
    'sympy.sets': ['sets.ts', 'sets/sets.ts'],
    'sympy.sets.conditionset': ['sets/sets.ts'],
    'sympy.sets.contains': ['sets/sets.ts'],
    'sympy.sets.fancysets': ['sets/complexregion.ts', 'sets/sets.ts'],
    'sympy.sets.handlers': ['sets/sets.ts'],
    'sympy.sets.handlers.add': ['sets/sets.ts'],
    'sympy.sets.handlers.comparison': ['sets/sets.ts'],
    'sympy.sets.handlers.functions': ['sets/sets.ts'],
    'sympy.sets.handlers.intersection': ['sets/sets.ts'],
    'sympy.sets.handlers.issubset': ['sets/sets.ts'],
    'sympy.sets.handlers.mul': ['sets/sets.ts'],
    'sympy.sets.handlers.power': ['sets/sets.ts'],
    'sympy.sets.handlers.union': ['sets/sets.ts'],
    'sympy.sets.powerset': ['sets/sets.ts'],
    'sympy.sets.setexpr': ['sets/sets.ts'],
    'sympy.simplify': ['simplify.ts'],
    'sympy.simplify._cse_diff': ['simplify/csemain.ts'],
    'sympy.simplify.combsimp': ['simplify/gammasimp.ts'],
    'sympy.simplify.cse_opts': ['simplify/csemain.ts', 'simplify/exprtools.ts'],
    'sympy.simplify.traversaltools': ['core/traverse.ts'],
    'sympy.solvers': ['solvers.ts'],
    'sympy.solvers.decompogen': ['solvers/decompogen.ts'],
    'sympy.solvers.deutils': ['solvers/ode.ts'],
    'sympy.solvers.diophantine': ['solvers/diophantine.ts'],
    'sympy.solvers.ode': ['solvers/dsolve.ts', 'solvers/ode.ts'],
    'sympy.solvers.ode.hypergeometric': ['solvers/dsolve.ts'],
    'sympy.solvers.ode.nonhomogeneous': ['solvers/dsolve.ts', 'solvers/odesimp.ts'],
    'sympy.solvers.ode.riccati': ['solvers/dsolve.ts'],
    'sympy.solvers.ode.single': ['solvers/dsolve.ts', 'solvers/ode.ts'],
    'sympy.solvers.ode.subscheck': ['solvers/odesystem.ts'],
    'sympy.stats': ['stats.ts'],
    'sympy.strategies': ['strategies.ts', 'strategies/index.ts'],
    'sympy.strategies.branch': ['strategies/branch/index.ts'],
    'sympy.tensor': ['tensor.ts', 'tensor/index.ts'],
    'sympy.tensor.array': ['tensor/arrayop.ts', 'tensor/ndimarray.ts'],
    'sympy.tensor.array.array_comprehension': ['tensor/comprehension.ts'],
    'sympy.tensor.array.dense_ndim_array': ['tensor/ndimarray.ts'],
    'sympy.tensor.array.mutable_ndim_array': ['tensor/ndimarray.ts'],
    'sympy.tensor.array.sparse_ndim_array': ['tensor/ndimarray.ts'],
    'sympy.tensor.functions': ['tensor/functions.ts'],
    'sympy.polys.agca': ['polys/agca/extensions.ts', 'polys/agca/homomorphisms.ts', 'polys/agca/ideals.ts', 'polys/agca/modules.ts'],
    'sympy.polys.domains.modularinteger': ['polys/domains/finitefield.ts'],
    'sympy.tensor.array.expressions': ['tensor/array/expressions/arrayexpressions.ts', 'tensor/array/expressions/arrayexprderivatives.ts', 'tensor/array/expressions/fromarraytomatrix.ts', 'tensor/array/expressions/fromindexedtoarray.ts', 'tensor/array/expressions/frommatrixtoarray.ts'],
    'sympy.tensor.array.expressions.conv_array_to_matrix': ['tensor/array/expressions/fromarraytomatrix.ts'],
    'sympy.tensor.array.expressions.conv_indexed_to_array': ['tensor/array/expressions/fromindexedtoarray.ts'],
    'sympy.tensor.array.expressions.conv_matrix_to_array': ['tensor/array/expressions/frommatrixtoarray.ts'],
    'sympy.tensor.indexed': ['core/indexed.ts', 'tensor/idx.ts'],
    'sympy.unify': ['unify.ts', 'unify/index.ts'],
    'sympy.vector': ['vector.ts'],
    'sympy.printing': ['printing.ts'],
    'sympy.printing.precedence': ['printing/str.ts'],
    'sympy.printing.printer': ['printing/printers.ts'],
    'sympy.printing.conventions': ['printing/latex.ts', 'printing/pretty/symbology.ts'],
    'sympy.printing.defaults': ['core/nodes.ts'],
    'sympy.printing.pretty': ['printing/pretty/index.ts'],
    'sympy.printing.pretty.pretty_symbology': ['printing/pretty/symbology.ts'],
    'sympy.utilities': ['utilities.ts', 'utilities/index.ts'],
    'sympy.utilities.lambdify': ['numeric/evalf.ts'],
    'sympy': ['index.ts'],
    'sympy.categories': ['categories.ts'],
    'sympy.parsing': ['parsing/parser.ts'],
    'sympy.physics.quantum.gate': ['../../physics-quantum/src/gates.ts'],
}
# Inspected modules without an implementation yet, with a note on the plan (base module, or the extend
# package that will hold them). Everything else without a correspondence stays unassessed.
NOT_IMPLEMENTED = {
    'sympy.codegen': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.abstract_nodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.algorithms': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.approximations': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.ast': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.cfunctions': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.cnodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.cutils': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.cxxnodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.fnodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.futils': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.matrix_nodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.numpy_nodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.pynodes': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.rewriting': 'extend package @symjs/codegen (planned)',
    'sympy.codegen.scipy_nodes': 'extend package @symjs/codegen (planned)',
    'sympy.combinatorics.galois': 'transitive subgroups of S1..S6 for Galois groups (polys.numberfields.galoisgroups)',
    'sympy.core.trace': 'deprecated alias of sympy.physics.quantum.trace (extend package @symjs/physics-quantum)',
    'sympy.diffgeom': 'extend package (planned): differential geometry',
    'sympy.diffgeom.diffgeom': 'extend package (planned): differential geometry',
    'sympy.diffgeom.rn': 'extend package (planned): differential geometry',
    'sympy.integrals.quadrature': 'Gauss quadrature nodes and weights',
    'sympy.parsing.autolev': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.autolev._listener_autolev_antlr': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.autolev._parse_autolev_antlr': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.c': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.c.c_parser': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.fortran': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.fortran.fortran_parser': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.maxima': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.parsing.sym_expr': 'other input-language parsers (Autolev, C, Fortran, Maxima): not ported',
    'sympy.polys.densetools': 'dense recursive list representation',
    'sympy.polys.fglmtools': 'FGLM change of monomial order; to be ported to ./polys',
    'sympy.polys.matrices.eigen': 'DomainMatrix eigenvalues and eigenvectors; to be ported to ./polys',
    'sympy.polys.matrices.linsolve': 'DomainMatrix linear system solving; to be ported to ./polys',
    'sympy.polys.multivariate_resultants': 'DixonResultant, MacaulayResultant',
    'sympy.polys.numberfields.galois_resolvents': '',
    'sympy.polys.numberfields.galoisgroups': '',
    'sympy.polys.numberfields.resolvent_lookup': '',
    'sympy.polys.polymatrix': 'PolyMatrix',
    'sympy.printing.c': 'extend package @symjs/codegen (planned)',
    'sympy.printing.codeprinter': 'extend package @symjs/codegen (planned)',
    'sympy.printing.cxx': 'extend package @symjs/codegen (planned)',
    'sympy.printing.fortran': 'extend package @symjs/codegen (planned)',
    'sympy.printing.glsl': 'extend package @symjs/codegen (planned)',
    'sympy.printing.julia': 'extend package @symjs/codegen (planned)',
    'sympy.printing.maple': 'extend package @symjs/codegen (planned)',
    'sympy.printing.mathematica': 'extend package @symjs/codegen (planned)',
    'sympy.printing.octave': 'extend package @symjs/codegen (planned)',
    'sympy.printing.rcode': 'extend package @symjs/codegen (planned)',
    'sympy.printing.rust': 'extend package @symjs/codegen (planned)',
    'sympy.printing.smtlib': 'extend package @symjs/codegen (planned)',
    'sympy.tensor.array.array_derivatives': 'ArrayDerivative; to be ported to ./tensor',
    'sympy.tensor.array.expressions.conv_array_to_indexed': 'array expressions to Indexed; to be ported to ./tensor',
    'sympy.tensor.array.expressions.from_array_to_indexed': 'array expressions to Indexed; to be ported to ./tensor',
    'sympy.tensor.array.expressions.utils': 'array expression helpers; to be ported to ./tensor',
    'sympy.tensor.toperators': '',
    'sympy.utilities.codegen': 'extend package @symjs/codegen (planned)',
}
# Packages whose modules are not implemented as a whole, with the plan; the
# most specific prefix wins and a module with a counterpart stays partial.
NOT_IMPLEMENTED_PACKAGES = {'sympy.physics.quantum': 'extend package @symjs/physics-quantum (not ported yet)',
 'sympy.physics': 'per-field extend package (planned)'}
# Notes on partially implemented modules (what is ported and what is not).
NOTES = {
    'sympy.polys.domains.mpelements': 'RealElement, ComplexElement and MPContext use numeric/ arbitrary precision, explicit context ownership and domain parents; mpmath _mpf/_mpc subclassing and Python context plumbing are excluded.',
    'sympy.functions.special.bsplines': 'Cox-de Boor B-spline bases and exact collocation interpolation on strictly increasing real coordinates.',
    'sympy.matrices.kind': 'Cached MatrixKind and propagation through matrix expressions and integrals; heterogeneous explicit matrix kinds remain partial.',
    'sympy.polys.fields': 'Sparse rational function fields, exact fraction arithmetic, differentiation, evaluation, substitution and generator inference; general domain integration and composition remain partial.',
    'sympy.polys.numberfields.utilities': 'Fundamental discriminant factorization and real algebraic root isolation with rational tolerances; other module utilities and complex isolation remain unported.',
    'sympy.polys.rootoftools': 'Evaluated indexed-root constructors, radical options, bound generators and real rational refinement; complex rational refinement and full root preprocessing remain incomplete.',
    'sympy.polys.appellseqs': 'Appell recurrence for Bernoulli, central Bernoulli, Genocchi, Euler and Andre polynomials, including Poly/PurePoly outputs; low-level dup_* exports remain unported.',
    'sympy.polys.dispersion': 'Univariate dispersion sets via factor pairs and exact shifts; inherits the supported coefficient domains of Poly.factorList.',
    'sympy.polys.solvers': 'sympyEqsToRing, eqsToMatrix and solveLinSys over field coefficient domains; solved generators and values are expressions, inconsistent systems return NoMatch.',
    'sympy.polys.puiseux': 'PuiseuxRing/PuiseuxPoly with exact rational exponents, arithmetic, conversion and differentiation; coefficient-domain restrictions remain',
    'sympy.polys.ring_series': 'truncated arithmetic, elementary functions, substitution/reversion and Newton sums; general multivariate leading-coefficient inverses are not implemented',
    'sympy.abc': 'symbols(); JavaScript has no module-level symbol namespace',
    'sympy.assumptions.cnf': 'CNF/EncodedCNF encoding used by satisfiable',
    'sympy.assumptions.sathandlers': 'allargs/anyarg/exactlyonearg; ClassFactRegistry of satask not ported',
    'sympy.assumptions.wrapper': 'is_infinite/is_extended_real/is_extended_nonnegative; AssumptionsWrapper not ported',
    'sympy.core.alphabets': 'Greek letter names used by the printers',
    'sympy.core.assumptions_generated': 'generated fact tables of the old assumptions',
    'sympy.core.facts': 'FactRules/FactKB deduction of the old assumptions',
    'sympy.core.operations': 'AssocOp.make_args as Expr.makeArgs; LatticeOp is Min/Max in functions/special/special.ts',
    'sympy.core.singleton': 'S registry',
    'sympy.crypto.crypto': 'lfsr_* take the GF(p) values and a modulus option; NonInvertibleCipherWarning (a Python warning) is not ported',
    'sympy.functions.elementary._trigonometric_special': 'migcdex, ipartfrac, fermat_coords; the cos_3..cos_257 tables are not ported',
    'sympy.logic.utilities.dimacs': 'load; load_file reads a file (no file system in the base module)',
    'sympy.physics.quantum.gate': 'extend package @symjs/physics-quantum',
    'sympy.series.acceleration': 'richardson/shanks of SymPy are symbolic: unassessed beyond the mpmath counterparts',
    'sympy.simplify._cse_diff': 'private CSE of Jacobians (forward differentiation)',
    'sympy.simplify.traversaltools': 'deprecated alias of use',
    'sympy.tensor.functions': 'shape, NoShapeError; TensorProduct not ported',
}


# Completeness is a conjunction of measured criteria, never a source-size score.
# Python protocol names are outside the contract: __repr__, __str__, __hash__,
# __slots__, construction, iteration, calls/subscripts, pickling and all other
# dunders, plus private names (including _sympystr/_latex-style printer hooks).
# Only the arithmetic/comparison dunders mapped by the harness below are kept.
OPERATOR_MEMBERS = {
    '__add__': ['add'], '__sub__': ['sub'], '__mul__': ['mul', 'compose'],
    '__truediv__': ['div', 'truediv', 'quotientModule', 'quotientRing'],
    '__pow__': ['pow'], '__floordiv__': ['floordiv'], '__mod__': ['mod'],
    '__matmul__': ['matmul', 'mul'], '__neg__': ['neg'],
    '__invert__': ['invert', 'inv', 'inverse'], '__and__': ['and', 'intersect', 'dot'],
    '__or__': ['or', 'union'], '__xor__': ['xor', 'cross', 'symmetricDifference'],
    '__rshift__': ['rshift'], '__lshift__': ['lshift'],
    '__eq__': ['equals', 'eq'], '__ne__': ['equals', 'ne'],
    '__lt__': ['lt'], '__le__': ['le'], '__gt__': ['gt'], '__ge__': ['ge'],
}
# Reflected arithmetic uses the same operation with the operands reversed.
for _operator in ('add', 'sub', 'mul', 'truediv', 'pow', 'floordiv', 'mod', 'matmul', 'and', 'or', 'xor', 'rshift', 'lshift'):
    OPERATOR_MEMBERS['__r' + _operator + '__'] = OPERATOR_MEMBERS['__' + _operator + '__']

# Exact allowlists: a new/unknown omission reason fails closed. Printing a
# mathematical expression is measurable, so printing-expression is NOT allowed.
DOCTEST_OMISSIONS = frozenset({
    'python-runtime-api', 'unstable-result-representation',  # Python object addresses
    'upstream-skip',  # explicit doctest +SKIP
    'illustrative-output',  # randomized output elided as Class(...)
    'random-output', 'sampling-output', 'python-object-printing',
})
DOCTEST_EXCLUSIONS = frozenset({
    'Python list method', 'Python class definition', 'Python threading', 'Python type object',
})
UNIT_OMISSIONS = frozenset({
    'duplicate', 'marked-xfail', 'test-utility', 'python-runtime-api', 'private-api', 'optional-dependency',
})

# Qualified names disambiguate exports with different meanings in different
# SymPy modules. These names and function-first forms are in docs/api-policy.md.
QUALIFIED_RENAMES = {
    'sympy.sets.setexpr.SetExpr': 'SetExpression',
    'sympy.ntheory.ecm.Point': 'ECMPoint',
    'sympy.vector.point.Point': 'VectorPoint',
    'sympy.vector.Point': 'VectorPoint',
    'sympy.stats.E': 'expectation', 'sympy.stats.rvinterface.E': 'expectation',
    'sympy.stats.Chi': 'ChiRV', 'sympy.stats.crv_types.Chi': 'ChiRV',
}
ATTRIBUTE_OWNERS = {
    'is_integer': {'Basic', 'Expr'}, 'is_Function': {'Basic', 'Expr'},
    'is_Number': {'Basic', 'Expr'}, 'canonical': {'Relational'},
}
FUNCTION_MEMBERS = {
    'Basic': {'free_symbols': 'freeSymbols', 'args': 'args', 'kind': 'kindOf'},
    'Function': {'nargs': 'nargs'}, 'Indexed': {'ranges': 'ranges'},
    'ExprWithLimits': {'variables': 'variables'},
    'AddWithLimits': {'has_finite_limits': 'hasFiniteLimits', 'has_reversed_limits': 'hasReversedLimits'},
    'BesselBase': {'order': 'order', 'argument': 'argument'},
}


@cache
def camel(name):
    return re.sub(r'_([a-zA-Z0-9])', lambda m: m[1].upper(), name)


def definitions(tree):
    """Module/class declarations, including conditional declarations, not locals."""
    for node in tree.body:
        yield node
        if isinstance(node, (ast.If, ast.Try)):
            for body in ([node.body, node.orelse] + ([node.finalbody] + [h.body for h in node.handlers] if isinstance(node, ast.Try) else [])):
                yield from definitions(ast.Module(body=body, type_ignores=[]))


def public_outline(tree, class_body=False):
    """Retain declaration structure, not the bodies of 825 modules' functions."""
    body = []
    for node in definitions(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            node.body = []
            body.append(node)
        elif isinstance(node, ast.ClassDef):
            public_outline(node, class_body=True)
            body.append(node)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            body.append(node)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            is_exports = any(isinstance(t, ast.Name) and t.id == '__all__' for t in targets)
            if class_body or is_exports:
                if not is_exports:
                    node.value = ast.Constant(value=None)
                body.append(node)
    tree.body = body
    return tree


class PublicContracts:
    """Resolve declared classes and their inherited members without importing backends."""
    def __init__(self, trees):
        self.trees = trees
        self.classes = {}
        self.imports = {}
        for module, tree in trees.items():
            imports = self.imports[module] = {}
            for node in definitions(tree):
                if isinstance(node, ast.ClassDef):
                    self.classes[module + '.' + node.name] = node
                elif isinstance(node, ast.ImportFrom) and node.module != '__future__':
                    # Package __init__ imports are resolved against the package itself.
                    package = module if getattr(tree, 'is_package', False) else module.rpartition('.')[0]
                    prefix = '.'.join(package.split('.')[:len(package.split('.')) - node.level + 1]) if node.level else ''
                    origin = '.'.join(p for p in (prefix, node.module) if p)
                    for alias in node.names:
                        imports[alias.asname or alias.name] = origin + '.' + alias.name
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        imports[alias.asname or alias.name.split('.')[0]] = alias.name if alias.asname else alias.name.split('.')[0]
        self.cache = {}

    def resolve(self, module, name, seen=frozenset()):
        full = module + '.' + name
        if full in seen:
            return full
        head, dot, tail = name.partition('.')
        target = self.imports.get(module, {}).get(head)
        if target:
            full = target + (dot + tail if dot else '')
        if full in self.classes:
            return full
        owner, _, local = full.rpartition('.')
        if owner in self.imports and local in self.imports[owner]:
            return self.resolve(owner, local, seen | {full})
        return full

    def members(self, full, seen=frozenset()):
        if full in self.cache:
            return self.cache[full]
        if full in seen or full not in self.classes:
            return set(), set(), set()
        node = self.classes[full]
        module = full.rpartition('.')[0]
        names, families, unresolved = set(), {node.name}, set()
        for item in definitions(node):
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not item.name.startswith('_') or item.name in OPERATOR_MEMBERS:
                    names.add(item.name)
            elif isinstance(item, (ast.Assign, ast.AnnAssign)):
                targets = item.targets if isinstance(item, ast.Assign) else [item.target]
                for target in targets:
                    if isinstance(target, ast.Name) and not target.id.startswith('_'):
                        names.add(target.id)
        for base in node.bases:
            name = ast.unparse(base)
            if name in {'object', 'Exception', 'BaseException', 'ValueError', 'TypeError', 'IndexError', 'KeyError', 'RuntimeError', 'ArithmeticError', 'ZeroDivisionError', 'NotImplementedError', 'tuple', 'dict', 'list', 'set', 'frozenset', 'int', 'str', 'type'}:
                continue
            parent = self.resolve(module, name)
            if parent not in self.classes:
                unresolved.add(parent)
                continue
            inherited, ancestors, unknown = self.members(parent, seen | {full})
            names.update(inherited)
            families.update(ancestors)
            unresolved.update(unknown)
        result = names, families, unresolved
        self.cache[full] = result
        return result

    def contract(self, module):
        names, classes, unresolved = set(), {}, set()
        for node in definitions(self.trees[module]):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and not node.name.startswith('_'):
                names.add(node.name)
                if isinstance(node, ast.ClassDef):
                    members, families, unknown = self.members(module + '.' + node.name)
                    classes[node.name] = {'members': sorted(members), 'families': sorted(families)}
                    unresolved.update(unknown)
            elif isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == '__all__' for t in node.targets):
                try:
                    exports = ast.literal_eval(node.value)
                except (ValueError, TypeError):
                    unresolved.add(module + '.__all__')
                    continue
                for name in exports:
                    names.add(name)
                    full = self.resolve(module, name)
                    if full in self.classes:
                        members, families, unknown = self.members(full)
                        classes[name] = {'members': sorted(members), 'families': sorted(families)}
                        unresolved.update(unknown)
        return {'names': sorted(names), 'classes': classes, 'unresolvedBases': sorted(unresolved)}


def export_exists(api, path):
    name, dot, member = path.partition('.')
    row = api['exports'].get(name)
    if row is None:
        return False
    if not dot:
        return True
    if member.startswith('prototype.'):
        return member[10:] in row['prototype']
    return member in row['static']


def api_criterion(module, contract, api):
    policy = api.get('policy', {})
    missing = []
    for name in contract['names']:
        qualified = QUALIFIED_RENAMES.get(module + '.' + name)
        if module == 'sympy.integrals.intpoly' and name != 'polytope_integrate':
            qualified = 'intpoly.' + camel(name)
        canonical = qualified or policy.get('renames', {}).get(name) or (name if name in contract['classes'] else camel(name))
        candidates = [canonical] if qualified else [canonical, policy.get('aliases', {}).get(name, canonical)]
        counterpart = next((path for path in candidates if export_exists(api, path)), None)
        if counterpart is None:
            missing.append(name)
        info = contract['classes'].get(name)
        if info is None:
            continue
        row = api['exports'].get((counterpart or canonical).split('.')[0], {})
        present = set(row.get('prototype', [])) | set(row.get('static', []))
        families = set(info['families'])
        if 'MatrixBase' in families:
            families.add('Matrix')
        free_members = {member for family in families for member in policy.get('memberFunctions', {}).get(family, [])}
        explicit_members = defaultdict(set)
        for family in families:
            for member, function in FUNCTION_MEMBERS.get(family, {}).items():
                explicit_members[member].add(function)
        for member in info['members']:
            spellings = OPERATOR_MEMBERS.get(member, [camel(member)])
            if present.intersection(spellings):
                continue
            functions = sorted(explicit_members[member])
            if camel(member) in free_members:
                functions.append(camel(member))
            if 'Matrix' in families:
                alias = policy.get('matrixMemberAliases', {}).get(camel(member))
                if alias:
                    functions.append(alias)
            if families.intersection(ATTRIBUTE_OWNERS.get(member, set())):
                functions.append(policy.get('attributeFunctions', {}).get(member, camel(member)))
            # Expression arithmetic is implemented by these public functions.
            if families.intersection({'Expr', 'Boolean'}):
                operator = {'__eq__': 'Eq', '__ne__': 'Ne', '__lt__': 'Lt', '__le__': 'Le', '__gt__': 'Gt', '__ge__': 'Ge', '__mod__': 'Mod', '__invert__': 'Not', '__and__': 'And', '__or__': 'Or', '__xor__': 'Xor'}
                if member in operator:
                    functions.append(operator[member])
                elif member in OPERATOR_MEMBERS and member not in {'__truediv__', '__floordiv__', '__matmul__'}:
                    functions.extend(OPERATOR_MEMBERS[member])
            if not any(export_exists(api, path) and api['exports'].get(path.split('.')[0], {}).get('kind') == 'function' for path in functions):
                missing.append(name + '.' + member)
    unresolved = contract.get('unresolvedBases', [])
    return {'pass': not missing and not unresolved, 'missingNames': sorted(missing), 'unresolvedBases': unresolved}


def disallowed_omissions(rows, allowed):
    counts = Counter()
    for row in rows:
        if row['reason'] not in allowed:
            counts[row['reason']] += row.get('count', 1)
    return dict(sorted(counts.items()))


def test_module_for(module):
    package, _, name = module.rpartition('.')
    return (package or module) + '.tests.test_' + name


def evaluate_completeness(module, contract, api, evidence, documented_examples=0, selected=True, note=None):
    """Pure criteria logic; unknown omissions and absent measurements fail closed."""
    docs = evidence['doctests'].get(module, [])
    omissions = evidence['doctestOmissions'].get(module, [])
    failures = sorted(gap for gap in evidence['doctestGaps'] if gap.startswith(module + ':'))
    excluded = {label: reason for label, reason in evidence['doctestExclusions'].items() if label.startswith(module + ':') and reason not in DOCTEST_EXCLUSIONS}
    bad_docs = disallowed_omissions(omissions, DOCTEST_OMISSIONS)
    missing_examples = max(0, documented_examples - len(docs) - sum(o.get('count', 1) for o in omissions))
    unmeasured = documented_examples > 0 and not selected
    test_module = test_module_for(module)
    unit = evidence['units'].get(test_module, {})
    gaps = sorted(set(unit.get('gaps', [])) | set(unit.get('timeouts', [])))
    bad_units = disallowed_omissions(unit.get('omitted', []), UNIT_OMISSIONS)
    statuses = Counter(t['status'] for t in unit.get('tests', []) if t['status'] != 'completed' and t['status'] not in UNIT_OMISSIONS)
    limits = [area for area in evidence['limitations'] if any(module == prefix or module.startswith(prefix + '.') for prefix in area['modules']) and area['remaining']]
    return {
        'publicApi': api_criterion(module, contract, api),
        'doctests': {'pass': not (failures or excluded or bad_docs or missing_examples or unmeasured),
                     'caseCount': len(docs), 'gapCount': len(failures), 'failingIds': failures,
                     'disallowedExclusions': excluded, 'disallowedOmissions': bad_docs,
                     'unaccountedExamples': missing_examples, 'notSelected': unmeasured},
        'unitTests': {'pass': bool(unit.get('exists') and unit.get('caseCount', 0)) and not (gaps or bad_units or statuses),
                      'testModule': test_module, 'testFile': test_module.replace('.', '/') + '.py',
                      'inCorpus': unit.get('exists', False), 'caseCount': unit.get('caseCount', 0),
                      'gapCount': len(gaps), 'timeoutCount': len(unit.get('timeouts', [])),
                      'disallowedOmissions': bad_units, 'incompleteTests': dict(sorted(statuses.items()))},
        'limitations': {'pass': note is None and not limits, 'hasNote': note is not None, 'note': note or '',
                       'capabilities': [{'area': a['area'], 'remaining': a['remaining']} for a in limits]},
    }


def load_evidence(root, corpus):
    compat = root / 'compat'
    read = lambda path: json.loads(path.read_text())
    def by_module(rows):
        result = defaultdict(list)
        for row in rows:
            result[row['module']].append(row)
        return result
    units = {}
    index = read(compat / 'tests-corpus/index.json')
    for category in index['categories'].values():
        audit = read(compat / 'tests-corpus' / category['auditFile'])
        omitted, tests = by_module(audit['omitted']), by_module(audit['tests'])
        counts = Counter()
        for shard in category['shards']:
            counts.update(c['module'] for c in read(compat / 'tests-corpus' / shard['file']))
        for module in category['modules']:
            units[module] = {'exists': True, 'caseCount': counts[module], 'omitted': omitted[module], 'tests': tests[module], 'gaps': [], 'timeouts': []}
    for kind, ids in read(compat / 'tests-known-gaps.json').items():
        for case_id in ids:
            module = case_id.split(':', 1)[0]
            if module in units:
                units[module]['timeouts' if kind == 'timeouts' else 'gaps'].append(case_id)
    return {'doctests': by_module(corpus['cases']), 'doctestOmissions': by_module(corpus['extraction']['omitted']),
            'doctestGaps': read(compat / 'known-gaps.json')['cases'],
            'doctestExclusions': read(compat / 'doctest-exclusions.json'),
            'units': units, 'limitations': read(compat / 'capabilities.json')['areas']}


def build_inventory(root):
    reference = Path(sympy.__file__).parent
    source = root / 'packages/symjs/src'
    corpus = json.loads((root / 'compat/corpus.json').read_text())
    measured = {c['module'] for c in corpus['cases']}
    selected_ast = ast.parse((root / 'compat/extract.py').read_text())
    selected = next(ast.literal_eval(n.value) for n in selected_ast.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'MODULES' for t in n.targets))
    api = json.loads((root / 'compat/api-members.json').read_text())
    evidence = load_evidence(root, corpus)
    trees = {}
    paths = {}
    source_info = {}
    parser = doctest.DocTestParser()
    for path in sorted(reference.rglob('*.py')):
        rel = path.relative_to(reference)
        if {'tests', 'benchmarks', '__pycache__'} & set(rel.parts) or path.name.startswith('test_'):
            continue
        module = 'sympy.' + '.'.join(rel.with_suffix('').parts)
        module = module.removesuffix('.__init__')
        text = path.read_text()
        tree = ast.parse(text)
        examples = 0
        for node in ast.walk(tree):
            if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                doc = ast.get_docstring(node)
                if doc:
                    examples += sum(bool(ex.want.strip()) for ex in parser.get_examples(doc))
        source_info[module] = (hashlib.sha256(text.encode()).hexdigest(), examples)
        public_outline(tree)
        tree.is_package = path.name == '__init__.py'
        trees[module] = tree
        paths[module] = path
    contracts = PublicContracts(trees)
    rows = []
    for module, path in paths.items():
        rel = path.relative_to(reference)
        source_hash, examples = source_info[module]
        contract = contracts.contract(module)
        names = list(contract['names'])
        for node in definitions(trees[module]):
            if isinstance(node, ast.ClassDef) and not node.name.startswith('_'):
                for member in definitions(node):
                    if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)) and (not member.name.startswith('_') or member.name in OPERATOR_MEMBERS):
                        names.append(node.name + '.' + member.name)
        names = sorted(set(names))
        counterpart = list(CORRESPONDENCES.get(module, []))
        candidate = '/'.join(p.replace('_', '') for p in rel.with_suffix('').parts) + '.ts'
        if (source / candidate).is_file():
            counterpart.append(candidate)
        counterpart = sorted({p for p in counterpart if (source / p).is_file()})
        reason = next((why for prefix, why in EXCLUSIONS.items() if module == prefix or module.startswith(prefix + '.')), None)
        package = next((p for p in sorted(NOT_IMPLEMENTED_PACKAGES, key=len, reverse=True) if module == p or module.startswith(p + '.')), None)
        status = 'excluded' if reason else 'partial' if counterpart else 'unimplemented' if module in NOT_IMPLEMENTED or package else 'unassessed'
        note = NOTES.get(module) or NOT_IMPLEMENTED.get(module) or (NOT_IMPLEMENTED_PACKAGES[package] if package and status == 'unimplemented' else '')
        completeness = evaluate_completeness(module, contract, api, evidence, examples, module in selected, NOTES.get(module)) if status == 'partial' else None
        if completeness and all(c['pass'] for c in completeness.values()):
            status = 'complete'
        rows.append({'module': module, 'sha256': source_hash, 'status': status,
                     **({'reason': reason} if reason else {}), **({'note': note} if note and not reason else {}), 'sources': counterpart,
                     **({'completeness': completeness} if completeness is not None else {}),
                     'selectedForExtraction': module in selected, 'hasCorpusCases': module in measured,
                     'documentedExamples': examples, 'declaredPublicNames': names})
    return {'schema': 2, 'reference': {'sympy': sympy.__version__},
            'definitions': {'complete': 'All public exports and class members are present; doctest and unit-test evidence passes strict omission/gap checks; no recorded limitation.',
                            'partial': 'A source counterpart exists, but at least one measured completeness criterion fails (see completeness).',
                            'unimplemented': 'Inspected mathematical module without an implementation.',
                            'unassessed': 'Not assessed; never treated as implemented or deliberately excluded.',
                            'excluded': 'An explicit runtime/infrastructure exclusion, with its reason.',
                            'note': 'For partial and unimplemented modules: what is ported, or where the module is planned (base module or an extend package).',
                            'declaredPublicNames': 'Public source definitions, explicit __all__ exports and declared class methods/properties. The API criterion also checks inherited members and class attributes. Python protocols are excluded except mapped arithmetic/comparison operators.'},
            'modules': rows}


if __name__ == '__main__':
    root = Path(__file__).resolve().parent.parent
    if sympy.__version__ != '1.14.0':
        raise SystemExit('The inventory is pinned to SymPy 1.14.0; review an upstream version change explicitly.')
    destination = Path(sys.argv[1]) if len(sys.argv) > 1 else root / 'compat/scope-inventory.json'
    destination.write_text(json.dumps(build_inventory(root), indent=1, ensure_ascii=False) + '\n')
