#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Execute instrumented SymPy 1.14 base-scope unit tests, independently of doctests.

PYTHONHASHSEED=0 python3 -B tools/sympy-reference/extract_tests.py tools/sympy-corpus/tests-corpus

The audit counts executed assertion instances, including duplicates, plus one
omission for each source site never reached. Test execution has a separate audit.
Timed-out tests are transactional: their partial, machine-dependent observations
are discarded. Nothing is inferred from an unexecuted right-hand side.
"""

import ast
import builtins
import contextlib
import copy
import functools
import hashlib
import inspect
import io
import itertools
import json
import math
import operator
import os
from pathlib import Path
import random
import re
import signal
import sys
import time
import types
import warnings
import weakref
from collections import Counter, defaultdict
from collections.abc import Iterator

import sympy
import extract


OPTIONAL = {"numpy", "scipy", "gmpy", "gmpy2", "flint", "matplotlib", "hypothesis",
            "numexpr", "cupy", "jax", "tensorflow", "torch", "sage"}
# Plotting computes its sample meshes with numpy; the reference values are plain numbers.
ALLOWED_OPTIONAL = {"plotting": {"numpy"}}
SKIP_MARKS = {"XFAIL", "xfail", "slow", "tooslow", "skip", "SKIP"}
OPS = {"__add__": operator.add, "__sub__": operator.sub, "__mul__": operator.mul,
       "__truediv__": operator.truediv, "__pow__": operator.pow,
       "__floordiv__": operator.floordiv, "__mod__": operator.mod,
       "__matmul__": operator.matmul, "__and__": operator.and_, "__or__": operator.or_,
       "__xor__": operator.xor, "__rshift__": operator.rshift, "__lshift__": operator.lshift,
       "__eq__": operator.eq, "__ne__": operator.ne, "__lt__": operator.lt,
       "__le__": operator.le, "__gt__": operator.gt, "__ge__": operator.ge,
       "__contains__": operator.contains, "__neg__": operator.neg,
       "__invert__": operator.invert, "__getitem__": operator.getitem,
       "__call__": lambda f, *args: f(*args)}


# Top-level package names, not the doctest report's combined calculus/special labels.
CATEGORIES = tuple("core polys assumptions sets logic concrete calculus series simplify solvers integrals functions matrices tensor ntheory combinatorics geometry vector stats discrete holonomic crypto liealgebras algebras categories strategies unify utilities printing parsing diffgeom plotting codegen".split())
EXCLUDED_AREAS = {
    "physics": "Physics belongs to extension packages, not the base symbolic engine.",
    "plotting/backends": "Rendering backends are provided by connector packages.",
    "plotting/pygletplot": "Interactive OpenGL rendering is provided by connector packages.",
    "codegen": "Source-code generation and compiler integration are outside this corpus.",
    "external": "Python bindings to optional external libraries are runtime-specific.",
    "interactive": "Python REPL/session integration is runtime-specific.",
    "testing": "Upstream test runners are infrastructure, not mathematical APIs.",
    "sandbox": "Experimental sandbox APIs are outside the base doctest scope.",
    "multipledispatch": "Python dispatch infrastructure is replaced by TypeScript expression dispatch; no public port.",
    "stats/sampling": "External sampling-library adapters require optional dependencies.",
    "utilities/_compilation": "Compiler and Python-extension build helpers are outside base scope.",
}
# File-level decisions for mixed areas. Every selected file has a technical reason;
# unmatched printing/parsing files are excluded by the defaults below.
FILE_SCOPE = {
    **{f"printing/tests/test_{name}.py": (False, "Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES.")
       for name in ("aesaracode", "c", "codeprinter", "cupy", "cxx", "fortran", "glsl", "gtk", "jax", "jscode",
                    "julia", "lambdarepr", "llvmjit", "maple", "mathematica", "numpy", "octave", "preview",
                    "pycode", "python", "rcode", "rust", "smtlib", "tensorflow", "theanocode", "torch")},
    **{f"parsing/tests/test_{name}.py": (False, "Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers).")
       for name in ("ast_parser", "autolev", "c_parser", "fortran_parser", "maxima", "sym_expr")},
    "parsing/tests/test_latex_deps.py": (False, "Checks the import failure without the ANTLR runtime; the port has no runtime dependency."),
    **{f"printing/tests/test_{name}.py": (True, "Base symbolic display printer or shared display support covered by extract.MODULES.")
       for name in ("str", "repr", "latex", "mathml", "tree", "dot", "tableform", "precedence", "conventions")},
    "printing/pretty/tests/test_pretty.py": (True, "Base ASCII/Unicode pretty printer covered by extract.MODULES."),
    **{f"parsing/tests/test_{name}.py": (True, "Public sympy_parser or Mathematica parser behavior.")
       for name in ("sympy_parser", "implicit_multiplication_application", "mathematica")},
    **{f"parsing/tests/test_{name}.py": (True, "LaTeX parser (ANTLR and Lark grammars) ported as the parsing subpath.")
       for name in ("latex", "latex_lark", "custom_latex")},
    "plotting/tests/test_experimental_lambdify.py": (False, "Python source generation is replaced by symjs numeric evaluation."),
    "codegen/tests/test_cfunctions.py": (True, "The C99 math functions of codegen.cfunctions are base symbolic functions; the rest of codegen generates source code."),
        **{f"utilities/tests/test_{name}.py": (False, reason) for name, reason in {
        "autowrap": "Compiles generated code with external toolchains.",
        "codegen": "Source-code generation is outside this corpus.",
        "codegen_julia": "Julia source-code generation is outside this corpus.",
        "codegen_octave": "Octave source-code generation is outside this corpus.",
        "codegen_rust": "Rust source-code generation is outside this corpus.",
        "matchpy_connector": "Requires the optional matchpy library.",
        "mathml": "XSLT conversion requires optional lxml; MathML printing is measured separately.",
        "xxe": "XML stylesheet processing requires optional lxml.",
        "pickling": "Python pickle persistence is runtime-specific.",
        "source": "Python import and source inspection are runtime-specific.",
        "timeutils": "Python benchmark/timing infrastructure is runtime-specific.",
        "exceptions": "Python warnings machinery has no JavaScript runtime counterpart.",
        "deprecated": "Deprecated Python module import shims are runtime-specific.",
    }.items()},
}
MIXED_DEFAULTS = {
    "printing": "Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES.",
    "parsing": "Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers).",
}


def file_scope(relative):
    name = relative.as_posix()
    if name in FILE_SCOPE:
        return FILE_SCOPE[name]
    for prefix, reason in EXCLUDED_AREAS.items():
        if name.startswith(prefix + "/"):
            return False, reason
    category = relative.parts[0]
    if category in MIXED_DEFAULTS:
        return False, MIXED_DEFAULTS[category]
    return (True, "Base package test directory.") if category in CATEGORIES else (False, "Area outside the base doctest scope.")


def discover(root):
    included = {category: [] for category in CATEGORIES}
    excluded = []
    for path in sorted(root.rglob("test_*.py")):
        relative = path.relative_to(root)
        if "tests" not in relative.parts:
            continue
        keep, reason = file_scope(relative)
        if keep:
            included[relative.parts[0]].append(path)
        else:
            excluded.append({"file": relative.as_posix(), "reason": reason})
    # Preserve the established core/polys top-level order before new subpackages.
    for category in ("core", "polys"):
        included[category].sort(key=lambda p: (p.parent != root / category / "tests", p.as_posix()))
    return included, excluded


class TestDeadline(BaseException):
    """An upstream `except Exception` must not swallow the test's deadline."""


def test_alarm(signum, frame):
    try:
        extract._alarm(signum, frame)
    except extract.Timeout:
        raise TestDeadline() from None


OPERATORS = {"==": operator.eq, "!=": operator.ne, "is": operator.is_, "is not": operator.is_not,
             "truthy": lambda a, b: bool(a), "falsy": lambda a, b: not a}


def call_hook(name, *args):
    return ast.Call(ast.Attribute(ast.Name("_compat_capture", ast.Load()), name, ast.Load()), list(args), [])


def asserted_names(test):
    """The names an assertion reads: G and H in `assert G == H`, `assert len(G) == 2` or `assert not G`."""
    return {n.id for n in ast.walk(test) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}


def raises_call(node):
    return isinstance(node, ast.Call) and (
        isinstance(node.func, ast.Name) and node.func.id == "raises"
        or isinstance(node.func, ast.Attribute) and node.func.attr == "raises")


# Python builtins applied to a measured value in an assertion (len(f(x)) == 2, str(f(x)) == '...'):
# the case measures the inner call and the replay applies the same projection to its result.
PROJECTIONS = {"len", "list", "tuple", "str", "repr"}


def comprehension_projection(node):
    """The iterated node of [str(r) for r in <node>], or None."""
    if not (isinstance(node, ast.ListComp) and len(node.generators) == 1):
        return None
    generator = node.generators[0]
    element = node.elt
    if (generator.ifs or generator.is_async or not isinstance(generator.target, ast.Name)
            or not (isinstance(element, ast.Call) and isinstance(element.func, ast.Name) and element.func.id == "str"
                    and len(element.args) == 1 and not element.keywords
                    and isinstance(element.args[0], ast.Name) and element.args[0].id == generator.target.id)):
        return None
    return generator.iter


def projection(node):
    """(builtin name, projected node) of an assertion side that applies a projection, or None."""
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in PROJECTIONS
            and len(node.args) == 1 and not node.keywords and not isinstance(node.args[0], ast.Starred)):
        return node.func.id, node.args[0]
    inner = comprehension_projection(node)
    return ("str-items", inner) if inner is not None else None


def assignment_targets(node):
    """Names bound by `name = <call>` or `a, b = <call>`, or None."""
    if len(node.targets) != 1:
        return None
    target = node.targets[0]
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, (ast.Tuple, ast.List)) and target.elts and all(isinstance(t, ast.Name) for t in target.elts):
        return tuple(t.id for t in target.elts)
    return None


def slice_call(node):
    """slice(lower, upper, step) for the ast.Slice of a subscript."""
    parts = [part if part is not None else ast.Constant(None) for part in (node.lower, node.upper, node.step)]
    return ast.Call(ast.Name("slice", ast.Load()), parts, [])


class Instrument(ast.NodeTransformer):
    """Wrap only the measured expression, leaving Python evaluation/control flow intact."""

    def __init__(self, source):
        self.source = source
        self.sites = []
        self.owner = "<module>"
        # Names that assertions of the current function read: only their assignments are bound.
        self.asserted = set()

    def site(self, node):
        index = len(self.sites)
        self.sites.append({"line": node.lineno, "src": ast.get_source_segment(self.source, node),
                           "owner": self.owner})
        return ast.Constant(index)

    def visit_FunctionDef(self, node):
        before, asserted = self.owner, self.asserted
        self.owner = node.name
        self.asserted = {name for child in ast.walk(node) if isinstance(child, ast.Assert)
                         for name in asserted_names(child.test)}
        self.generic_visit(node)
        self.owner, self.asserted = before, asserted
        return node

    def measured(self, node, site):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                prepared = call_hook("method", site, node.func.value, ast.Constant(node.func.attr))
            else:
                prepared = call_hook("function", site, node.func)
            return ast.copy_location(ast.Call(prepared, node.args, node.keywords), node)
        syn = self.synthetic(node)
        if syn is not None:
            name, receiver, args = syn
            return ast.copy_location(call_hook("synthetic", site, ast.Constant(name), receiver, *args), node)
        return None

    @staticmethod
    def synthetic(node):
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice):
            return "__getitem__", node.value, [slice_call(node.slice)]
        return extract.synthetic_call(node)

    def visit_Assign(self, node):
        names = None if raises_call(node.value) else assignment_targets(node)
        node = self.generic_visit(node)
        value = node.value
        if names is None or not self.asserted.intersection([names] if isinstance(names, str) else names):
            return node
        label = ast.Constant(names)
        if isinstance(value, ast.Call):
            if isinstance(value.func, ast.Attribute):
                prepared = call_hook("bind_method", label, value.func.value, ast.Constant(value.func.attr))
            else:
                prepared = call_hook("bind_function", label, value.func)
            node.value = ast.copy_location(ast.Call(prepared, value.args, value.keywords), value)
            return node
        syn = self.synthetic(value)
        if syn is not None:
            name, receiver, args = syn
            node.value = ast.copy_location(call_hook("bind_synthetic", label, ast.Constant(name), receiver, *args), value)
        return node

    def derived(self, lhs, site, op, rhs):
        """A check of a projected call or of a name bound to a measured call, or None."""
        projected = projection(lhs)
        builtin, inner = (None, lhs) if projected is None else projected
        builtin_node = ast.Constant(None) if builtin is None else ast.Name("str" if builtin == "str-items" else builtin, ast.Load())
        if isinstance(inner, ast.Name):
            return call_hook("check_bound", site, ast.Constant(op), ast.Constant(builtin), builtin_node,
                             ast.Constant(inner.id), inner, rhs)
        if builtin is None:
            return None
        measured = self.measured(inner, site)
        if measured is None:
            return None
        return call_hook("check_projection", site, ast.Constant(op), ast.Constant(builtin), builtin_node, measured, rhs)

    def split(self, node, tests):
        """Separate assertions, in order, for the given tests of one assert statement."""
        statements = []
        for test in tests:
            result = self.visit_Assert(ast.copy_location(ast.Assert(ast.copy_location(test, node.test), node.msg), node))
            statements.extend(result if isinstance(result, list) else [result])
        return statements

    def visit_Assert(self, node):
        test = node.test
        # assert a and b: separate assertions with Python's short-circuit order.
        if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
            return self.split(node, test.values)
        # assert a == b == c: one assertion per comparison of adjacent operands.
        if (isinstance(test, ast.Compare) and len(test.ops) > 1
                and all(isinstance(o, (ast.Eq, ast.NotEq)) for o in test.ops)):
            operands = [test.left, *test.comparators]
            return self.split(node, [ast.Compare(copy.deepcopy(operands[i]), [o], [copy.deepcopy(operands[i + 1])])
                                     for i, o in enumerate(test.ops)])
        site = self.site(node)
        lhs, rhs, op = node.test, ast.Constant(True), "truthy"
        if isinstance(lhs, ast.UnaryOp) and isinstance(lhs.op, ast.Not):
            lhs, rhs, op = lhs.operand, ast.Constant(False), "falsy"
        elif isinstance(lhs, ast.Compare):
            if len(lhs.ops) == 1 and isinstance(lhs.ops[0], (ast.Eq, ast.NotEq)):
                lhs, rhs, op = lhs.left, lhs.comparators[0], "==" if isinstance(lhs.ops[0], ast.Eq) else "!="
            elif len(lhs.ops) == 1 and isinstance(lhs.ops[0], ast.Is):
                # The right-hand side must evaluate to True, False, None or a class such as
                # sin in `x.func is sin` (checked when run); a class is compared like ==.
                lhs, rhs, op = lhs.left, lhs.comparators[0], "is"
            elif (len(lhs.ops) == 1 and isinstance(lhs.ops[0], ast.IsNot)
                  and isinstance(lhs.comparators[0], ast.Constant)
                  and any(lhs.comparators[0].value is v for v in (True, False, None))):
                lhs, rhs, op = lhs.left, lhs.comparators[0], "is not"
            elif len(lhs.ops) == 1 and isinstance(lhs.ops[0], (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                # an order comparison: the relation itself is measured and must be true
                rhs, op = ast.Constant(True), "truthy"
            elif len(lhs.ops) == 1 and isinstance(lhs.ops[0], ast.NotIn):
                # x not in items: the membership is measured and must be false
                lhs = ast.copy_location(ast.Compare(lhs.left, [ast.In()], lhs.comparators), lhs)
                rhs, op = ast.Constant(False), "falsy"
            else:
                return [ast.copy_location(ast.Expr(call_hook("omit", site, ast.Constant("unsupported-assertion"))), node), node]
        derived = self.derived(lhs, site, op, rhs)
        if derived is not None:
            node.test = ast.copy_location(derived, node.test)
            return node
        if projection(lhs) is not None:
            # str([...]), len(x.args[0]): the builtin applies to a value no measured call produced.
            return [ast.copy_location(ast.Expr(call_hook("omit", site, ast.Constant("non-call-expression"))), node), node]
        measured = self.measured(lhs, site)
        if measured is None:
            return [ast.copy_location(ast.Expr(call_hook("omit", site, ast.Constant("non-call-expression"))), node), node]
        node.test = ast.copy_location(call_hook("check", site, ast.Constant(op), measured, rhs), node.test)
        return node

    def visit_Call(self, node):
        if not raises_call(node):
            return self.generic_visit(node)
        site = self.site(node)
        if len(node.args) == 2 and isinstance(node.args[1], ast.Lambda):
            measured = self.measured(node.args[1].body, site)
            if measured is not None:
                callback = ast.Lambda(node.args[1].args, measured)
                return ast.copy_location(call_hook("raises_lambda", site, node.func, node.args[0], callback), node)
        # Preserve unsupported raises forms and count them when actually reached.
        return ast.copy_location(call_hook("unmeasured_raises", site, node.func, *node.args), node)

    def visit_With(self, node):
        if len(node.items) == 1 and raises_call(node.items[0].context_expr):
            context = node.items[0].context_expr
            site = self.site(node)
            # A single expression/assignment is unambiguous; do not guess which
            # call in an arbitrary multi-statement suite is supposed to raise.
            statement = node.body[0] if len(node.body) == 1 else None
            value = statement.value if isinstance(statement, (ast.Expr, ast.Assign, ast.AnnAssign)) else None
            measured = self.measured(value, site) if value is not None else None
            if len(context.args) == 1 and measured is not None:
                statement.value = measured
                node.items[0].context_expr = call_hook("raises_context", site, context.func, context.args[0])
                return node
            return [ast.copy_location(ast.Expr(call_hook("omit", site, ast.Constant("unsupported-raises"))), node), node]
        return self.generic_visit(node)


@functools.lru_cache(None)
def public_names(module):
    return extract.PUBLIC | extract.subpackage_public(module)


def sympy_object(value):
    """A SymPy object, including one that subclasses a Python container (Cycle is a dict)."""
    return extract.is_sympy_operand(value, []) or (
        not isinstance(value, type) and (type(value).__module__ or "").startswith("sympy."))


# Numerical test helpers of SymPy's own test suite, not mathematical API: they are not ported and
# their assertions are omitted with the reason "test-utility".
TEST_UTILITIES = {
    "all_close": "approximate structural comparison used by SymPy's tests (sympy.core.numbers.all_close)",
    "verify_numerically": "random numerical spot check used by SymPy's tests (sympy.core.random.verify_numerically)",
}


def contains_iterator(value):
    if isinstance(value, Iterator):
        return True
    if isinstance(value, (list, tuple, set, frozenset)):
        return any(contains_iterator(v) for v in value)
    if isinstance(value, dict):
        return any(contains_iterator(k) or contains_iterator(v) for k, v in value.items())
    return False


def deprecated_matrix_input(value):
    """A Matrix built with SymPy's deprecated forms: non-Expr entries (Poly) or a RawMatrix ``ring`` attribute."""
    from sympy.matrices import MatrixBase
    from sympy.polys.polytools import Poly
    if isinstance(value, MatrixBase):
        return getattr(value, "ring", None) is not None or any(isinstance(e, Poly) for e in value)
    if isinstance(value, (list, tuple)):
        return any(deprecated_matrix_input(v) for v in value)
    if isinstance(value, dict):
        return any(deprecated_matrix_input(v) for v in value.values())
    return False


def json_numbers(value):
    """Keep IEEE values JSON-safe and retain the captured arithmetic structure."""
    if isinstance(value, float) and not math.isfinite(value):
        return "NaN" if math.isnan(value) else "Infinity" if value > 0 else "-Infinity"
    if isinstance(value, list):
        return [json_numbers(v) for v in value]
    if isinstance(value, dict):
        result = {k: json_numbers(v) for k, v in value.items()}
        # Re-evaluating a serialized tree loses evaluate=False constructors,
        # duplicate arguments and power towers before the measured call runs.
        if result.get("t") in ("Add", "Mul", "Pow"):
            result["evaluate"] = False
        return result
    return value


# str(x) and repr(x) are replayed by printing the result (str of a SymPy object is sstr, and so is
# its repr, except for classes such as Permutation whose repr is their constructor call).
REPLAY_PROJECTIONS = {"len", "list", "tuple", "str-items", "str", "repr"}
# Builtin values whose str()/repr() the replay reproduces: containers print their items by repr.
PRINTABLE_BUILTINS = (type(None), bool, int, float, str, list, tuple, dict, set, frozenset)


def python_representation(value):
    """Whether str()/repr() of the value contains Python's own representation of an object that is
    neither a SymPy (or mpmath) value nor a builtin number, string or container."""
    if isinstance(value, (list, tuple, set, frozenset)):
        return any(python_representation(v) for v in value)
    if isinstance(value, dict):
        return any(python_representation(k) or python_representation(v) for k, v in value.items())
    if isinstance(value, PRINTABLE_BUILTINS + (sympy.Basic,)):
        # applied undefined functions are Basic instances of classes created at run time
        return False
    return not (type(value).__module__ or "").startswith(("sympy.", "mpmath."))


def bracket_kinds(value):
    """The kinds of the Python lists ("l") and tuples ("t") in the value, in preorder.

    JavaScript has one array type for both; the replay prints its arrays in this order with the
    brackets Python's str() uses for them.
    """
    kinds = []

    def walk(v):
        if isinstance(v, (list, tuple)):
            kinds.append("l" if isinstance(v, list) else "t")
            for item in v:
                walk(item)
        elif isinstance(v, dict):
            for key, item in v.items():
                walk(key)
                walk(item)
        elif isinstance(v, (set, frozenset)):
            for item in v:
                walk(item)
    walk(value)
    return "".join(kinds)


def tabulated(args):
    """Wrap each lambda argument that is not an expression of its parameters so that its calls are recorded.

    The wrapper is a plain function, like the lambda, and returns the lambda's values unchanged.
    """
    tables, wrapped = {}, list(args)
    for index, value in enumerate(args):
        if not (isinstance(value, types.FunctionType) and value.__name__ == "<lambda>"):
            continue
        try:
            extract.ser_lambda(value)
            continue
        except extract.Unsupported:
            pass
        calls = tables[index] = []

        def recorded(*xs, _f=value, _calls=calls):
            result = _f(*xs)
            _calls.append((xs, result))
            return result
        wrapped[index] = recorded
    return tuple(wrapped), tables


def fill_tables(record, tables):
    """The record with each tabulated lambda as the table of its recorded calls {"t": "JsTable", "entries": [[args, value], ...]}."""
    try:
        extract.DUMMY_IDS.clear()
        entries = {i: [[[extract.ser(x) for x in xs], extract.ser(v)] for xs, v in calls] for i, calls in tables.items()}
    except extract.Unsupported:
        return {"reason": "unserializable-input"}
    args = list(record["args"])
    for i, rows in entries.items():
        args[i] = {"t": "JsTable", "entries": json_numbers(rows)}
    return {**record, "args": args}


def project(projection, value):
    if projection is None:
        return value
    if projection == "str-items":
        return [str(item) for item in value]
    return getattr(builtins, projection)(value)


def held(value):
    """A callable returning the value: a weak reference when the value supports one."""
    try:
        return weakref.ref(value)
    except TypeError:
        return lambda: value


def fingerprint(value):
    """A fingerprint that detects in-place changes of a bound value.

    SymPy Basic objects are immutable; printing one can fill private caches that a test
    then asserts on (Permutation._cyclic_form), so they are identified by identity alone.
    """
    if isinstance(value, sympy.Basic):
        return "<immutable>"
    try:
        return str(value)
    except Exception:
        return None


def default_truth(value):
    """Python truthiness of an object without __bool__/__len__: always true, not a mathematical result."""
    return not hasattr(type(value), "__bool__") and not hasattr(type(value), "__len__")



def closure_vector(function):
    """The vector of the closure returned by Vector.dot(Del), with the call taking it as its last argument."""
    if getattr(function, "__qualname__", "") != "Vector.dot.<locals>.directional_derivative":
        return None, function
    vector = function.__closure__[function.__code__.co_freevars.index("self")].cell_contents
    return vector, functools.wraps(function)(lambda *args, **kwargs: function(*args[:-1], **kwargs))


class Capture:
    def __init__(self, module, category, sites):
        self.module, self.category, self.sites = module, category, sites
        self.test = "<module>"
        self.events = []
        self.pending = {}
        self.exceptions = {}
        self.bindings = {}

    def metadata(self, site):
        return {"module": self.module, "category": self.category, "test": self.test,
                "line": self.sites[site]["line"], "src": self.sites[site]["src"]}

    def omit(self, site, reason):
        self.events.append((site, {**self.metadata(site), "reason": reason}))

    def snapshot(self, site, name, receiver, args, kwargs, *, function=None, synthetic=False):
        try:
            if isinstance(function, type) and (reason := extract.custom_class_reason(function)):
                return {"reason": reason}
            # extract.ser materializes iterators. Before-call capture must never
            # consume the iterator the real test is about to pass to its API.
            if contains_iterator((receiver, args, kwargs)):
                return {"reason": "stateful-iterator-input"}
            if deprecated_matrix_input((receiver, args, kwargs)):
                return {"reason": "deprecated-api"}
            if name.startswith("."):
                if name[1:].startswith("_") and name not in extract.OPERATOR_FNS:
                    return {"reason": "private-api"}
                if not (extract.is_sympy_operand(receiver, args) or sympy_object(receiver)):
                    return {"reason": "python-runtime-api"}
            elif name in TEST_UTILITIES:
                return {"reason": "test-utility"}
            elif function is isinstance:
                # Python type introspection of a result, not a mathematical API.
                return {"reason": "python-runtime-api"}
            else:
                module = getattr(function, "__module__", "") or ""
                if (name.startswith("_") and module.startswith("sympy.") and ".tests." not in module
                        and not module.startswith("sympy.testing.")):
                    return {"reason": "private-api"}
                if (not module.startswith("sympy.") or ".tests." in module
                        or module.startswith("sympy.testing.") or name not in public_names(module)):
                    return {"reason": "not-exported-api"}
            extract.DUMMY_IDS.clear()
            record = {"fn": name, "args": [extract.ser(a) for a in args],
                      "kwargs": {k: extract.ser(v) for k, v in kwargs.items()}}
            owner = getattr(function, "__self__", None)
            if not name.startswith(".") and isinstance(owner, sympy.MatrixBase):
                record["boundMatrix"] = extract.ser(owner)
            if name == "classof":
                for arg, tree in zip(args, record["args"]):
                    if tree["t"] == "Matrix":
                        tree["matrixClass"] = type(arg).__name__
            if name.startswith("."):
                record["self"] = extract.ser(receiver)
            if self.category == "core" and name == ".diff" and isinstance(receiver, sympy.core.function.AppliedUndef):
                if callable(receiver.func._kwargs.get("fdiff")):
                    variables = [sympy.Dummy(f"arg{index}") for index in range(len(receiver.args))]
                    formal = receiver.func(*variables)
                    record["functionPartials"] = [extract.ser(sympy.Lambda(variables, formal.fdiff(index + 1)))
                                                  for index in range(len(variables))]
            if self.category == "core" and name == ".make_args":
                from sympy.core.operations import LatticeOp
                if isinstance(receiver, type) and issubclass(receiver, LatticeOp):
                    record["latticeOperation"] = [extract.ser(receiver.identity), extract.ser(receiver.zero)]
            if self.category == "core" and name == ".random":
                from sympy.core.random import rng
                _, state, gaussian = rng.getstate()
                record["randomState"] = {"words": state[:-1], "index": state[-1]}
                if gaussian is not None:
                    record["randomState"]["gaussian"] = gaussian
            if self.category == "core" and name == ".__getitem__" and isinstance(receiver, defaultdict) and receiver.default_factory is int:
                record["zeroDefault"] = True
            if self.category == "core" and name == ".__truediv__":
                from sympy.core.numbers import _errdict
                if _errdict["divide"]:
                    record["divideError"] = True
            if self.category == "polys":
                from sympy.polys.numberfields.modules import Submodule
                from sympy.printing.lambdarepr import IntervalPrinter
                if name in ("gf_irreducible_p", "gf_factor", "gf_factor_sqf", "groebner") and "method" not in kwargs:
                    from sympy.polys.polyconfig import query
                    setting = {"gf_irreducible_p": "GF_IRRED_METHOD", "groebner": "GROEBNER"}.get(name, "GF_FACTOR_METHOD")
                    record["polyReplay"] = {"method": query(setting)}
                elif name == ".args" and isinstance(receiver, sympy.AlgebraicNumber):
                    record["polyReplay"] = {"originalCoeffs": [extract.ser(c) for c in receiver.args[1]]}
                elif name == ".doprint" and isinstance(receiver, IntervalPrinter):
                    record["polyReplay"] = {"intervalPrinter": True}
                elif name == ".discard_before" and isinstance(receiver, Submodule):
                    record["polyReplay"] = {"computedTable": receiver._mult_tab is not None}
                elif name == ".mult_tab" and isinstance(receiver, Submodule):
                    for call, _, value, _ in self.bindings.values():
                        if value() is receiver and call.get("fn") == ".discard_before":
                            record["polyReplay"] = {"submoduleDiscard": {"original": call["self"],
                                "index": int(call["args"][0]["p"]), "computedTable": call["polyReplay"]["computedTable"]}}
                            break
            state = extract.tensor_state((receiver, args, kwargs))
            if state:
                record["tensorData"] = state
            def custom_reason(value):
                if isinstance(value, dict):
                    if "unsupportedClass" in value:
                        return value["unsupportedClass"]
                    return next((reason for item in value.values() if (reason := custom_reason(item))), None)
                if isinstance(value, list):
                    return next((reason for item in value if (reason := custom_reason(item))), None)
                return None
            reason = custom_reason(record)
            if reason:
                record["exclusion"] = reason
            from sympy.assumptions import global_assumptions
            if global_assumptions:
                record["assume"] = [extract.ser(a) for a in sorted(global_assumptions, key=str)]
            # Shared serializer constructors can include mutable Python lists.
            return {**json_numbers(copy.deepcopy(record)), '_dummyIds': extract.DUMMY_IDS.copy()}
        except (extract.Timeout, TestDeadline):
            raise
        except extract.PythonRuntime:
            return {"reason": "python-runtime-api"}
        except extract.Unsupported as error:
            return {"reason": str(error) if str(error).startswith("Python test class ") else "unserializable-input"}
        except Exception:
            return {"reason": "serialization-error"}

    def invoke(self, site, name, receiver, function, args, kwargs):
        args, tables = tabulated(args)
        record = self.snapshot(site, name, receiver, [None if i in tables else a for i, a in enumerate(args)], kwargs, function=function)
        self.pending[site] = record
        try:
            result = function(*args, **kwargs)
            if tables and "reason" not in record:
                self.pending[site] = fill_tables(record, tables)
            return result
        except (extract.Timeout, TestDeadline):
            raise
        except BaseException as error:
            expected = self.exceptions.get(site)
            if expected is not None and isinstance(error, expected):
                if isinstance(expected, tuple):
                    expected = type(error)
                self.finish(site, record, "is", None, raises=expected.__name__)
            else:
                self.omit(site, "reference-exception")
            self.pending.pop(site, None)
            raise

    def function(self, site, function):
        name = getattr(function, "__name__", "")
        if not name and sympy_object(function):
            return lambda *args, **kw: self.invoke(site, ".__call__", function, function, args, kw)
        vector, call = closure_vector(function)
        if vector is not None:
            return lambda *args, **kw: self.invoke(site, name, None, call, (*args, vector), kw)
        return lambda *args, **kw: self.invoke(site, name, None, function, args, kw)

    def method(self, site, receiver, name):
        function = getattr(receiver, name)
        if isinstance(receiver, types.ModuleType):
            return self.function(site, function)
        return lambda *args, **kw: self.invoke(site, "." + name, receiver, function, args, kw)

    def synthetic(self, site, name, receiver, *args):
        function = (lambda *a: OPS[name](receiver, *a)) if name in OPS else (lambda: getattr(receiver, name))
        return self.invoke(site, "." + name, receiver, function, args, {})

    def finish(self, site, record, op, expected, **extra):
        if "reason" in record:
            self.omit(site, record["reason"])
            return
        if (type(expected).__module__ or "").startswith(("_pytest.", "pytest")):
            # pytest.approx(...): an approximate comparison helper of the test runner
            self.omit(site, "test-utility")
            return
        text = str(expected)
        # Like extract.py: strings are compared as text, all other values by
        # their str form. Monomials in tuples need str instead of address repr.
        from sympy.polys.monomials import Monomial
        if isinstance(expected, tuple) and any(isinstance(x, Monomial) for x in expected):
            text = "(" + ", ".join(str(x) for x in expected) + ")"
        if re.search(r"<[^<>\n]*\bat 0x[0-9a-fA-F]+>", text):
            self.omit(site, "unstable-result-representation")
            return
        case = {**self.metadata(site), **{k: v for k, v in record.items() if k != "_dummyIds"}, "expected": text, "op": op, **extra}
        if op == "!=" and self.category == "tensor" and isinstance(expected, (sympy.Idx, sympy.Indexed, sympy.IndexedBase, sympy.tensor.tensor.TensorHead)):
            case["comparisonTree"] = extract.ser(expected)
        if op == "!=" and self.category == "polys":
            try:
                comparison = extract.ser(expected)
                if comparison["t"] == "AGCASubModule":
                    comparison["componentOrder"] = str(expected.order.args[1][0])
                case["comparisonTree"] = comparison
            except (extract.Unsupported, extract.PythonRuntime):
                pass
        # two random symbols of the same name print alike: the right-hand side is kept as a tree
        if op == "!=" and self.category == "stats" and isinstance(expected, sympy.stats.rv.RandomSymbol):
            case["comparisonTree"] = extract.ser(expected)
        if ported_function_case(case):
            case.pop("exclusion", None)
        if isinstance(expected, str):
            case["text"] = True
        if self.category == "core" and op == "!=" and case.get("post") is None and not contains_iterator(expected):
            # Preserve the compared value when two objects print alike.
            prior = extract.DUMMY_IDS.copy()
            extract.DUMMY_IDS.clear()
            extract.DUMMY_IDS.update(record.get("_dummyIds", {}))
            try:
                operand = extract.ser(expected)
            except extract.Unsupported:
                operand = None
            finally:
                extract.DUMMY_IDS.clear()
                extract.DUMMY_IDS.update(prior)
            if operand is not None and operand.get("t") == "UFnClass":
                operand["assume"] = {key: value for key, value in expected._kwargs.items() if isinstance(value, bool)}
            if operand is not None and operand.get("t") in ("Float", "Rational", "Symbol", "Dummy", "Subs", "Mul", "Add", "Pow", "Fn", "Lambda", "Str", "UFnClass"):
                case["expectedOperand"] = json_numbers(operand)
        self.events.append((site, case))

    def check(self, site, op, lhs, rhs):
        return self.compare(site, op, self.pending.pop(site), None, None, lhs, rhs)

    @contextlib.contextmanager
    def raises_context(self, site, raises, exception):
        self.exceptions[site] = exception
        try:
            with raises(exception) as context:
                yield context
        finally:
            self.exceptions.pop(site, None)
            if site in self.pending:
                self.pending.pop(site)
                self.omit(site, "reference-did-not-raise")

    def raises_lambda(self, site, raises, exception, callback):
        self.exceptions[site] = exception
        try:
            return raises(exception, callback)
        finally:
            self.exceptions.pop(site, None)
            if site in self.pending:
                self.pending.pop(site)
                self.omit(site, "reference-did-not-raise")

    def bind(self, names, record, value):
        """Remember which measured call produced the value of each assigned name.

        Values are held weakly where possible: a test may check that its value is collected.
        """
        if isinstance(names, str):
            self.bindings[names] = (record, None, held(value), fingerprint(value))
            return value
        items = tuple(value) if isinstance(value, Iterator) else value
        try:
            values = list(items)
        except TypeError:
            return items
        if len(values) == len(names):
            for index, (name, item) in enumerate(zip(names, values)):
                self.bindings[name] = (record, index, held(item), fingerprint(item))
        return items

    def bound_call(self, names, name, receiver, function, args, kwargs):
        record = self.snapshot(None, name, receiver, args, kwargs, function=function)
        return self.bind(names, record, function(*args, **kwargs))

    def bind_function(self, names, function):
        name = getattr(function, "__name__", "")
        if not name and sympy_object(function):
            return lambda *args, **kw: self.bound_call(names, ".__call__", function, function, args, kw)
        vector, call = closure_vector(function)
        if vector is not None:
            return lambda *args, **kw: self.bound_call(names, name, None, call, (*args, vector), kw)
        return lambda *args, **kw: self.bound_call(names, name, None, function, args, kw)

    def bind_method(self, names, receiver, name):
        function = getattr(receiver, name)
        if isinstance(receiver, types.ModuleType):
            return self.bind_function(names, function)
        return lambda *args, **kw: self.bound_call(names, "." + name, receiver, function, args, kw)

    def bind_synthetic(self, names, name, receiver, *args):
        function = (lambda *a: OPS[name](receiver, *a)) if name in OPS else (lambda: getattr(receiver, name))
        return self.bound_call(names, "." + name, receiver, function, args, {})

    def compare(self, site, op, record, builtin, projection, value, rhs):
        """Evaluate the (projected) assertion like Python and record it as a case of the measured call."""
        projected = project(projection, value)
        result = OPERATORS[op](projected, rhs)
        if builtin is not None and builtin is not getattr(builtins, "str" if projection == "str-items" else projection):
            self.omit(site, "non-call-expression")
        elif not result:
            self.omit(site, "reference-assertion-failed")
        elif "reason" in record:
            self.omit(site, record["reason"])
        elif op in ("truthy", "falsy") and not (projected is None or isinstance(projected, (bool, sympy.logic.boolalg.BooleanAtom))):
            self.omit(site, "python-runtime-api" if default_truth(projected) else "non-boolean-assertion")
        elif op == "is" and not (isinstance(rhs, type) or any(rhs is v for v in (True, False, None))):
            self.omit(site, "unsupported-assertion")
        elif projection in ("str", "repr") and python_representation(value):
            self.omit(site, "python-object-representation")
        elif projection in ("str", "repr"):
            brackets = bracket_kinds(value)
            self.finish(site, {**record, "post": projection, **({"brackets": brackets} if brackets else {})}, op, rhs)
        else:
            # an undecided query (None) asserted false is recorded as None
            self.finish(site, {**record, "post": projection} if projection in REPLAY_PROJECTIONS else record,
                        op, None if op == "falsy" and projected is None else rhs)
        return result

    def check_projection(self, site, op, projection, builtin, value, rhs):
        return self.compare(site, op, self.pending.pop(site), builtin, projection, value, rhs)

    def check_bound(self, site, op, projection, builtin, name, value, rhs):
        binding = self.bindings.get(name)
        if binding is None or binding[2]() is not value or binding[3] is None or fingerprint(value) != binding[3]:
            # Not produced by a measured call (or changed since): only Python evaluates it.
            result = OPERATORS[op](project(projection, value), rhs)
            self.omit(site, "non-call-expression")
            return result
        record, index, _, _ = binding
        if index is not None and "reason" not in record:
            record = {**record, "pick": index}
        return self.compare(site, op, record, builtin, projection, value, rhs)

    def unmeasured_raises(self, site, raises, *args):
        self.omit(site, "unsupported-raises")
        return raises(*args)


def mark_name(node):
    if isinstance(node, ast.Call):
        return mark_name(node.func)
    return node.id if isinstance(node, ast.Name) else node.attr if isinstance(node, ast.Attribute) else ""


def optional_aliases(tree, optional=OPTIONAL):
    aliases = set(optional)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for name in node.names:
                if ((getattr(node, "module", "") or "").split(".")[0] in optional
                        or name.name.split(".")[0] in optional):
                    aliases.add(name.asname or name.name.split(".")[0])
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            if mark_name(node.value.func) in ("import_module", "importorskip") and node.value.args:
                value = node.value.args[0]
                if isinstance(value, ast.Constant) and str(value.value).split(".")[0] in optional:
                    aliases.update(t.id for t in node.targets if isinstance(t, ast.Name))
    return aliases


def skip_reason(node, aliases, functions, visited=None, optional=OPTIONAL):
    visited = set() if visited is None else visited
    if node.name in visited:
        return None
    visited.add(node.name)
    for decorator in node.decorator_list:
        if mark_name(decorator) in SKIP_MARKS:
            return "marked-" + mark_name(decorator).lower()
    for child in ast.walk(node):
        if isinstance(child, ast.Import) and any(n.name.split(".")[0] in optional for n in child.names):
            return "optional-dependency"
        if isinstance(child, ast.ImportFrom) and (child.module or "").split(".")[0] in optional:
            return "optional-dependency"
        if isinstance(child, ast.Name) and child.id in aliases:
            return "optional-dependency"
        if isinstance(child, ast.Constant) and isinstance(child.value, str) and child.value in optional:
            return "optional-dependency"
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Name) and child.func.id in functions:
            reason = skip_reason(functions[child.func.id], aliases, functions, visited, optional)
            if reason == "optional-dependency":
                return reason
    return None


def disabled_test(node, tree):
    """A test renamed to _test_* so that pytest does not collect it: it takes no arguments and nothing calls it."""
    if not node.name.startswith("_test") or node.args.args or node.args.vararg or node.args.kwonlyargs or node.args.kwarg:
        return False
    return not any(isinstance(n, ast.Name) and n.id == node.name for n in ast.walk(tree))


def parameters(function):
    """Expand ordinary pytest parametrization without using pytest's runner."""
    rows = [{}]
    for mark in getattr(function, "pytestmark", []):
        if mark.name != "parametrize":
            continue
        names, values = mark.args[:2]
        names = [s.strip() for s in names.split(",")] if isinstance(names, str) else names
        additions = []
        for value in values:
            marks = getattr(value, "marks", ())
            reason = next(("marked-" + m.name for m in marks if m.name in SKIP_MARKS), None)
            value = value.values if hasattr(value, "values") else (value,) if len(names) == 1 else value
            additions.append({**dict(zip(names, value)), **({"_compat_skip": reason} if reason else {})})
        rows = [{**a, **b} for a, b in itertools.product(rows, additions)]
    return rows


def execute_source(source, module, category, filename, timeout=extract.ALARM_SECONDS):
    original = ast.parse(source, filename)
    functions = {n.name: n for n in original.body if isinstance(n, ast.FunctionDef)}
    optional = OPTIONAL - ALLOWED_OPTIONAL.get(category, set())
    aliases = optional_aliases(original, optional)
    skipped = {name: skip_reason(n, aliases, functions, optional=optional) for name, n in functions.items()
               if name.startswith("test") or disabled_test(n, original)}
    transform = Instrument(source)
    tree = ast.fix_missing_locations(transform.visit(copy.deepcopy(original)))
    capture = Capture(module, category, transform.sites)
    test_audit = []
    previous_handler = signal.signal(signal.SIGALRM, test_alarm)
    namespace = {"__name__": module, "__package__": module.rpartition(".")[0],
                 "__file__": filename, "_compat_capture": capture}
    from sympy.assumptions import global_assumptions
    from sympy.core.cache import clear_cache
    saved_assumptions = set(global_assumptions)
    saved_dummy_count = sympy.Dummy._count
    saved_dummy_base = sympy.Dummy._base_dummy_index
    original_import = builtins.__import__
    original_warn = warnings.warn
    original_random = random.Random

    class SeededRandom(original_random):
        """random.Random() without a seed draws one from the OS (randMatrix's default generator)."""

        def seed(self, a=None, version=2):
            super().seed(0 if a is None else a, version)

    def without_optional(name, *args, **kwargs):
        if name.split(".")[0] in optional:
            raise ImportError(f"Optional dependency excluded from the pilot: {name}")
        return original_import(name, *args, **kwargs)

    def warning_at_test(message, category=None, stacklevel=1, source=None, **kwargs):
        # The wrappers introduce frames. Keep upstream warning stacklevel tests
        # pointing to the original call site, with the original warning intact.
        frame = sys._getframe(1)
        level = stacklevel
        for _ in range(stacklevel - 1):
            if frame.f_back is not None:
                frame = frame.f_back
        while frame.f_code.co_filename == __file__ and frame.f_back is not None:
            frame = frame.f_back
            level += 1
        return original_warn(message, category, stacklevel=level + 1, source=source, **kwargs)

    try:
        # Dummy identity starts from a random process seed in SymPy. Allocate
        # disjoint deterministic ranges so timeouts cannot shift later names.
        sympy.Dummy._base_dummy_index = 10**15
        sympy.Dummy._count = int.from_bytes(hashlib.sha256(module.encode()).digest()[:6], "big")
        builtins.__import__ = without_optional
        warnings.warn = warning_at_test
        random.Random = SeededRandom
        random.seed(0)
        sympy.core.random.seed(0)
        signal.setitimer(signal.ITIMER_REAL, timeout)
        try:
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                exec(compile(tree, filename, "exec"), namespace)
        except BaseException as error:
            reason = "module-timeout" if isinstance(error, (extract.Timeout, TestDeadline)) else "optional-dependency" if isinstance(error, ImportError) else "module-exception"
            for name in skipped:
                skipped[name] = reason
            test_audit.append({"module": module, "test": "<module>", "status": reason, "error": type(error).__name__})
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
        for name, reason in skipped.items():
            if os.environ.get("EXTRACT_TESTS_PROGRESS"):
                print(f"  {module}:{name}", file=sys.stderr, flush=True)
            function = namespace.get(name)
            if reason or not callable(function):
                test_audit.append({"module": module, "test": name, "status": reason or "not-collected"})
                continue
            for index, kwargs in enumerate(parameters(function)):
                capture.test = name
                capture.bindings.clear()
                reason = kwargs.pop("_compat_skip", None)
                start = len(capture.events)
                sympy.Dummy._count = int.from_bytes(hashlib.sha256(f"{module}:{name}:{index}".encode()).digest()[:6], "big")
                random.seed(0)
                sympy.core.random.seed(0)
                clear_cache()
                global_assumptions.clear()
                global_assumptions.update(saved_assumptions)
                try:
                    if reason:
                        continue
                    inspect.signature(function).bind(**kwargs)
                    signal.setitimer(signal.ITIMER_REAL, timeout)
                    with warnings.catch_warnings(), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                        warnings.simplefilter("ignore")
                        function(**kwargs)
                    reason = "completed"
                except (extract.Timeout, TestDeadline):
                    reason = "test-timeout"
                    del capture.events[start:]
                except BaseException as error:
                    reason = ("optional-dependency" if isinstance(error, ImportError) else
                              "upstream-skip" if type(error).__name__ in ("Skipped", "SkippedException") else
                              "requires-fixture" if isinstance(error, TypeError) and not capture.events[start:] and inspect.signature(function).parameters else
                              "test-exception:" + type(error).__name__)
                finally:
                    signal.setitimer(signal.ITIMER_REAL, 0)
                    for site in capture.pending:
                        capture.omit(site, reason)
                    capture.pending.clear()
                    capture.exceptions.clear()
                    test_audit.append({"module": module, "test": name, "parameter": index, "status": reason})
                    if reason != "completed":
                        skipped[name] = reason
        seen = {site for site, _ in capture.events}
        for site, details in enumerate(transform.sites):
            if site not in seen:
                capture.test = details["owner"]
                capture.omit(site, skipped.get(details["owner"]) or "not-executed")
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
        global_assumptions.clear()
        global_assumptions.update(saved_assumptions)
        sympy.Dummy._count = saved_dummy_count
        sympy.Dummy._base_dummy_index = saved_dummy_base
        builtins.__import__ = original_import
        warnings.warn = original_warn
        random.Random = original_random
    return [event for _, event in capture.events], test_audit, len(transform.sites)


def corpus_from_events(events, tests, source_sites, categories=None):
    cases, omitted, seen = [], [], set()
    for event in events:
        if "reason" in event:
            omitted.append(event)
            continue
        key = json.dumps(event, sort_keys=True, ensure_ascii=False)
        if key in seen:
            omitted.append({k: event[k] for k in ("module", "category", "test", "line", "src")} | {"reason": "duplicate"})
        else:
            seen.add(key)
            cases.append(event)
    def audit(category=None):
        cs = [c for c in cases if category is None or c["category"] == category]
        os_ = [c for c in omitted if category is None or c["category"] == category]
        # Records retained from an audit file carry the multiplicity of identical omissions.
        reasons = Counter()
        for c in os_:
            reasons[c["reason"]] += c.get("count", 1)
        return {"examined": len(cs) + sum(reasons.values()), "cases": len(cs), "reasons": dict(sorted(reasons.items()))}
    return {"sympy": sympy.__version__, "cases": cases,
            "extraction": {**audit(), "sourceSites": source_sites,
                           "categories": {c: audit(c) for c in (categories if categories is not None else sorted({e["category"] for e in events}))},
                           "omitted": omitted, "tests": tests,
                           "testStatuses": dict(sorted(Counter(t["status"] for t in tests).items()))}}


MAX_SHARD_BYTES = 25_000_000


def json_line(value):
    return json.dumps(value, ensure_ascii=True, allow_nan=False, separators=(",", ":"))


def write_array(path, values):
    path.write_text("[\n" + ",\n".join(json_line(v) for v in values) + "\n]\n", encoding="utf-8")


def write_category(destination, category, corpus, max_bytes=MAX_SHARD_BYTES):
    """Bound shards by encoded bytes; never split a case or change its key order."""
    destination.mkdir(parents=True, exist_ok=True)
    chunks, chunk, size = [], [], 4
    for case in corpus["cases"]:
        length = len(json_line(case).encode("utf-8")) + 2
        if length + 4 > max_bytes:
            raise ValueError(f"Single {category} case exceeds shard size limit")
        if chunk and size + length > max_bytes:
            chunks.append(chunk)
            chunk, size = [], 4
        chunk.append(case)
        size += length
    chunks.append(chunk)
    shards = []
    for i, cases in enumerate(chunks):
        name = f"{category}.json" if len(chunks) == 1 else f"{category}-{i + 1:03}.json"
        path = destination / name
        write_array(path, cases)
        shards.append({"file": name, "cases": len(cases), "bytes": path.stat().st_size})
    audit = corpus["extraction"]
    audit_name = write_audit(destination, category, audit["omitted"], audit["tests"])

    return {**{k: v for k, v in audit.items() if k not in ("categories", "omitted", "tests")},
            "shards": shards, "auditFile": audit_name,
            "auditBytes": (destination / audit_name).stat().st_size,
            "modules": sorted({t["module"] for t in audit["tests"]})}



def write_audit(destination, category, omitted, tests):
    # Loop omissions often repeat the same source location hundreds of thousands
    # of times. Keep multiplicities without duplicating identical provenance.
    groups = {}
    for event in omitted:
        details = {k: v for k, v in event.items() if k != "count"}
        key = json_line(details)
        if key not in groups:
            groups[key] = {**details, "count": 0}
        groups[key]["count"] += event.get("count", 1)
    audit_name = f"{category}.audit.json"
    (destination / audit_name).write_text(
        '{"omitted":' + "[\n" + ",\n".join(json_line(v) for v in groups.values()) +
        '\n],"tests":[\n' + ",\n".join(json_line(v) for v in tests) + "\n]}\n", encoding="utf-8")
    return audit_name


def compact_audits(destination, only=()):
    """Repack existing provenance losslessly without re-running upstream tests."""
    destination = Path(destination)
    path = destination / "index.json"
    index = json.loads(path.read_text())
    selected = {c for item in only for c in item.split(",") if c} or set(index["categories"])
    if selected - set(index["categories"]):
        raise ValueError("Unknown categories in audit selection")
    for category in sorted(selected):
        summary = index["categories"][category]
        audit = json.loads((destination / summary["auditFile"]).read_text())
        name = write_audit(destination, category, audit["omitted"], audit["tests"])
        summary["auditBytes"] = (destination / name).stat().st_size
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(index, indent=2, ensure_ascii=True, allow_nan=False) + "\n")
    temporary.replace(path)

# the deadline of one upstream test; instrumented tests run several times slower than plain ones
TEST_SECONDS = 120


def extract_category(category, paths, timeout, baseline):
    from sympy.printing.pretty.pretty_symbology import pretty_use_unicode
    pretty_use_unicode(False)
    root = Path(sympy.__file__).parent
    start = time.monotonic()
    events, tests, source_sites = [], [], 0
    retained = set()
    if baseline:
        old = json.loads(Path(baseline).read_text())
        events.extend(c for c in old["cases"] if c["category"] == category)
        events.extend(c for c in old["extraction"]["omitted"] if c["category"] == category)
        tests.extend(t for t in old["extraction"]["tests"] if t["module"].split(".")[1] == category)
        retained = {t["module"] for t in tests}
    for path in paths:
        module = "sympy." + ".".join(path.relative_to(root).with_suffix("").parts)
        if module in retained:
            transform = Instrument(path.read_text())
            transform.visit(ast.parse(path.read_text()))
            source_sites += len(transform.sites)
            continue
        before = time.monotonic()
        es, ts, count = execute_source(path.read_text(), module, category, str(path), timeout)
        events.extend(es)
        tests.extend(ts)
        source_sites += count
        print(f"{module}: {len(es)} observations, {len(ts)} tests, {time.monotonic() - before:.2f}s", file=sys.stderr, flush=True)
    corpus = corpus_from_events(events, tests, source_sites, [category])
    corpus["extraction"].update(seconds=round(time.monotonic() - start, 3), retainedModules=len(retained))
    return corpus


def ported_function_case(case):
    """Function fixtures translated through the public JavaScript function API."""
    return (case.get("module"), case.get("test")) in {
        ("sympy.core.tests.test_function", "test_Function"),
        ("sympy.core.tests.test_function", "test_nargs_inheritance"),
        ("sympy.core.tests.test_function", "test_fdiff_argument_index_error"),
        ("sympy.functions.elementary.tests.test_interface", "test_function_series1"),
        ("sympy.functions.elementary.tests.test_interface", "test_function_series2"),
    }


def without_replay_state(value):
    """The original assertion identity, independent of replay-only state."""
    if isinstance(value, dict):
        return {k: without_replay_state(v) for k, v in value.items()
                if k not in ("tensorData", "exclusion", "unsupportedClass", "indexedAssumptions", "comparisonTree",
                             "matrixClass", "boundMatrix", "polyReplay", "expectedOperand", "zeroDefault", "divideError",
                             "functionPartials", "randomState", "latticeOperation")}
    if isinstance(value, list):
        return [without_replay_state(v) for v in value]
    return value


def refresh_replay_state(destination, timeout=TEST_SECONDS):
    """Re-execute stateful clusters while preserving every existing assertion and shard boundary."""
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise RuntimeError("Run with PYTHONHASHSEED=0 for deterministic reference output")
    destination = Path(destination)
    root = Path(sympy.__file__).parent
    modules = {
        "tensor": ["sympy.tensor.tests.test_tensor", "sympy.tensor.tests.test_indexed"],
        "core": ["sympy.core.tests.test_priority", "sympy.core.tests.test_function"],
        "functions": ["sympy.functions.elementary.tests.test_interface"],
    }
    exclusions = {}
    index_path = destination / "index.json"
    index = json.loads(index_path.read_text())
    for category, names in modules.items():
        observed, omitted = {}, {}
        for module in names:
            path = root.joinpath(*module.split(".")[1:]).with_suffix(".py")
            events, _, _ = execute_source(path.read_text(), module, category, str(path), timeout)
            for event in events:
                key = f"{module}:{event['test']}:{event['line']}: {event['src']}"
                if event.get("reason", "").startswith("Python test class "):
                    exclusions[key] = event["reason"]
                    omitted[key] = event["reason"]
                elif "reason" not in event:
                    observed[json_line(without_replay_state(event))] = event
                    if "exclusion" in event:
                        exclusions[key] = event["exclusion"]
            print(f"{module}: captured {len(events)} observations", file=sys.stderr, flush=True)
        changed = 0
        for shard in index["categories"][category]["shards"]:
            path = destination / shard["file"]
            original = path.read_text()
            cases = json.loads(original)
            for i, case in enumerate(cases):
                if case["module"] not in names:
                    continue
                if category == "tensor" and case["op"] != "!=" and case["module"].endswith("test_tensor") and not any(part in case["test"] for part in ("valued", "TensMul_data", "TensAdd_data", "noncommuting_components")):
                    continue
                replacement = observed.get(json_line(without_replay_state(case)))
                key = f"{case['module']}:{case['test']}:{case['line']}: {case['src']}"
                if replacement is None and key in omitted:
                    replacement = {**case, "exclusion": omitted[key]}
                if replacement is not None and replacement != case:
                    cases[i] = replacement
                    changed += 1
            encoded = "[\n" + ",\n".join(json_line(c) for c in cases) + "\n]\n"
            if encoded != original:
                path.write_text(encoded)
                shard["bytes"] = path.stat().st_size
        print(f"{category}: refreshed {changed} existing assertions", file=sys.stderr, flush=True)
    index_path.write_text(json.dumps(index, indent=2, ensure_ascii=True, allow_nan=False) + "\n")
    Path(__file__).with_name("unit-exclusions.json").write_text(json.dumps(dict(sorted(exclusions.items())), indent=2) + "\n")


def main(destination, only=(), timeout=TEST_SECONDS, jobs=1, baseline=None):
    if sympy.__version__ != "1.14.0":
        raise RuntimeError("The compatibility reference is pinned to SymPy 1.14.0")
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise RuntimeError("Run with PYTHONHASHSEED=0 for deterministic reference output")
    selected = {c for item in only for c in item.split(",") if c}
    unknown = selected - set(CATEGORIES)
    if unknown:
        raise ValueError(f"Unknown categories: {sorted(unknown)}")
    included, excluded = discover(Path(sympy.__file__).parent)
    destination = Path(destination)
    index_path = destination / "index.json"
    index = json.loads(index_path.read_text()) if index_path.exists() else {"sympy": sympy.__version__, "categories": {}}
    start = time.monotonic()
    from concurrent.futures import ProcessPoolExecutor, as_completed
    # Each area gets its own process: upstream module globals cannot leak across areas.
    with ProcessPoolExecutor(max_workers=jobs, max_tasks_per_child=1) as pool:
        pending = {pool.submit(extract_category, c, paths, timeout, baseline): c
                   for c, paths in included.items() if not selected or c in selected}
        for future in as_completed(pending):
            category = pending[future]
            corpus = future.result()
            previous = index["categories"].get(category, {})
            summary = write_category(destination, category, corpus)
            index["categories"][category] = summary
            for shard in previous.get("shards", []):
                if shard["file"] not in {s["file"] for s in summary["shards"]}:
                    (destination / shard["file"]).unlink(missing_ok=True)
            index["categories"] = dict(sorted(index["categories"].items()))
            index.update(excludedFiles=excluded, timeoutSeconds=timeout, jobs=jobs,
                         lastRunSeconds=round(time.monotonic() - start, 3))
            index_path.write_text(json.dumps(index, indent=2, ensure_ascii=True, allow_nan=False) + "\n")
            print(f"{category}: {summary['cases']} cases, {summary['seconds']}s", file=sys.stderr, flush=True)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", nargs="?", default="tools/sympy-corpus/tests-corpus")
    parser.add_argument("--only", action="append", default=[], help="Category names, comma-separated or repeatable; other shards are retained")
    parser.add_argument("--timeout", type=float, default=TEST_SECONDS)
    parser.add_argument("--jobs", type=int, default=4, help="Independent extraction processes")
    parser.add_argument("--baseline", help="Preserve all records/audits from already measured modules in a legacy corpus")
    parser.add_argument("--compact-audits", action="store_true", help="Losslessly combine repeated omission records without re-extraction")
    parser.add_argument("--refresh-state", action="store_true", help="Refresh tensor state and explicit custom-class exclusions in existing shards")
    args = parser.parse_args()
    if args.refresh_state:
        refresh_replay_state(args.destination, args.timeout)
    elif args.compact_audits:
        compact_audits(args.destination, args.only)
    else:
        main(args.destination, args.only, args.timeout, args.jobs, args.baseline)
