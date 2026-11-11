#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Execute instrumented SymPy 1.14 core/polys unit tests, independently of doctests.

PYTHONHASHSEED=0 python3 -B compat/extract_tests.py compat/tests-corpus.json

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
from collections import Counter
from collections.abc import Iterator

import sympy
import extract


OPTIONAL = {"numpy", "scipy", "gmpy", "gmpy2", "flint", "matplotlib", "hypothesis",
            "numexpr", "cupy", "jax", "tensorflow", "torch", "sage", "antlr4"}
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


class TestDeadline(BaseException):
    """An upstream `except Exception` must not swallow the test's deadline."""


def test_alarm(signum, frame):
    try:
        extract._alarm(signum, frame)
    except extract.Timeout:
        raise TestDeadline() from None


def call_hook(name, *args):
    return ast.Call(ast.Attribute(ast.Name("_compat_capture", ast.Load()), name, ast.Load()), list(args), [])


def raises_call(node):
    return isinstance(node, ast.Call) and (
        isinstance(node.func, ast.Name) and node.func.id == "raises"
        or isinstance(node.func, ast.Attribute) and node.func.attr == "raises")


class Instrument(ast.NodeTransformer):
    """Wrap only the measured expression, leaving Python evaluation/control flow intact."""

    def __init__(self, source):
        self.source = source
        self.sites = []
        self.owner = "<module>"

    def site(self, node):
        index = len(self.sites)
        self.sites.append({"line": node.lineno, "src": ast.get_source_segment(self.source, node),
                           "owner": self.owner})
        return ast.Constant(index)

    def visit_FunctionDef(self, node):
        before = self.owner
        self.owner = node.name
        self.generic_visit(node)
        self.owner = before
        return node

    def measured(self, node, site):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                prepared = call_hook("method", site, node.func.value, ast.Constant(node.func.attr))
            else:
                prepared = call_hook("function", site, node.func)
            return ast.copy_location(ast.Call(prepared, node.args, node.keywords), node)
        syn = extract.synthetic_call(node)
        if syn is not None:
            name, receiver, args = syn
            return ast.copy_location(call_hook("synthetic", site, ast.Constant(name), receiver, *args), node)
        return None

    def visit_Assert(self, node):
        site = self.site(node)
        lhs, rhs, op = node.test, ast.Constant(True), "truthy"
        if isinstance(lhs, ast.UnaryOp) and isinstance(lhs.op, ast.Not):
            lhs, rhs, op = lhs.operand, ast.Constant(False), "falsy"
        elif isinstance(lhs, ast.Compare):
            if len(lhs.ops) == 1 and isinstance(lhs.ops[0], (ast.Eq, ast.NotEq)):
                lhs, rhs, op = lhs.left, lhs.comparators[0], "==" if isinstance(lhs.ops[0], ast.Eq) else "!="
            elif (len(lhs.ops) == 1 and isinstance(lhs.ops[0], ast.Is)
                  and isinstance(lhs.comparators[0], ast.Constant)
                  and any(lhs.comparators[0].value is v for v in (True, False, None))):
                lhs, rhs, op = lhs.left, lhs.comparators[0], "is"
            else:
                return [ast.copy_location(ast.Expr(call_hook("omit", site, ast.Constant("unsupported-assertion"))), node), node]
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


def contains_iterator(value):
    if isinstance(value, Iterator):
        return True
    if isinstance(value, (list, tuple, set, frozenset)):
        return any(contains_iterator(v) for v in value)
    if isinstance(value, dict):
        return any(contains_iterator(k) or contains_iterator(v) for k, v in value.items())
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


class Capture:
    def __init__(self, module, category, sites):
        self.module, self.category, self.sites = module, category, sites
        self.test = "<module>"
        self.events = []
        self.pending = {}
        self.exceptions = {}

    def metadata(self, site):
        return {"module": self.module, "category": self.category, "test": self.test,
                "line": self.sites[site]["line"], "src": self.sites[site]["src"]}

    def omit(self, site, reason):
        self.events.append((site, {**self.metadata(site), "reason": reason}))

    def snapshot(self, site, name, receiver, args, kwargs, *, function=None, synthetic=False):
        try:
            # extract.ser materializes iterators. Before-call capture must never
            # consume the iterator the real test is about to pass to its API.
            if contains_iterator((receiver, args, kwargs)):
                return {"reason": "stateful-iterator-input"}
            if name.startswith("."):
                if name[1:].startswith("_") and name not in extract.OPERATOR_FNS:
                    return {"reason": "private-api"}
                if not extract.is_sympy_operand(receiver, args):
                    return {"reason": "python-runtime-api"}
            else:
                module = getattr(function, "__module__", "") or ""
                if (not module.startswith("sympy.") or ".tests." in module
                        or module.startswith("sympy.testing.") or name not in public_names(module)):
                    return {"reason": "not-exported-api"}
            extract.DUMMY_IDS.clear()
            record = {"fn": name, "args": [extract.ser(a) for a in args],
                      "kwargs": {k: extract.ser(v) for k, v in kwargs.items()}}
            if name.startswith("."):
                record["self"] = extract.ser(receiver)
            from sympy.assumptions import global_assumptions
            if global_assumptions:
                record["assume"] = [extract.ser(a) for a in sorted(global_assumptions, key=str)]
            # Shared serializer constructors can include mutable Python lists.
            return json_numbers(copy.deepcopy(record))
        except (extract.Timeout, TestDeadline):
            raise
        except extract.PythonRuntime:
            return {"reason": "python-runtime-api"}
        except extract.Unsupported:
            return {"reason": "unserializable-input"}
        except Exception:
            return {"reason": "serialization-error"}

    def invoke(self, site, name, receiver, function, args, kwargs):
        record = self.snapshot(site, name, receiver, args, kwargs, function=function)
        self.pending[site] = record
        try:
            return function(*args, **kwargs)
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
        if not name and extract.is_sympy_operand(function, []):
            return lambda *args, **kw: self.invoke(site, ".__call__", function, function, args, kw)
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
        text = str(expected)
        # Like extract.py: strings are compared as text, all other values by
        # their str form. Monomials in tuples need str instead of address repr.
        from sympy.polys.monomials import Monomial
        if isinstance(expected, tuple) and any(isinstance(x, Monomial) for x in expected):
            text = "(" + ", ".join(str(x) for x in expected) + ")"
        if re.search(r"<[^<>\n]*\bat 0x[0-9a-fA-F]+>", text):
            self.omit(site, "unstable-result-representation")
            return
        case = {**self.metadata(site), **record, "expected": text, "op": op, **extra}
        if isinstance(expected, str):
            case["text"] = True
        self.events.append((site, case))

    def check(self, site, op, lhs, rhs):
        record = self.pending.pop(site)
        result = {"==": operator.eq, "!=": operator.ne, "is": operator.is_,
                  "truthy": lambda a, b: bool(a), "falsy": lambda a, b: not a}[op](lhs, rhs)
        if op in ("truthy", "falsy") and not isinstance(lhs, (bool, sympy.logic.boolalg.BooleanAtom)):
            self.omit(site, "non-boolean-assertion")
        elif not result:
            self.omit(site, "reference-assertion-failed")
        else:
            self.finish(site, record, op, rhs)
        return result

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

    def unmeasured_raises(self, site, raises, *args):
        self.omit(site, "unsupported-raises")
        return raises(*args)


def mark_name(node):
    if isinstance(node, ast.Call):
        return mark_name(node.func)
    return node.id if isinstance(node, ast.Name) else node.attr if isinstance(node, ast.Attribute) else ""


def optional_aliases(tree):
    aliases = set(OPTIONAL)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for name in node.names:
                if ((getattr(node, "module", "") or "").split(".")[0] in OPTIONAL
                        or name.name.split(".")[0] in OPTIONAL):
                    aliases.add(name.asname or name.name.split(".")[0])
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            if mark_name(node.value.func) in ("import_module", "importorskip") and node.value.args:
                value = node.value.args[0]
                if isinstance(value, ast.Constant) and str(value.value).split(".")[0] in OPTIONAL:
                    aliases.update(t.id for t in node.targets if isinstance(t, ast.Name))
    return aliases


def skip_reason(node, aliases, functions, visited=None):
    visited = set() if visited is None else visited
    if node.name in visited:
        return None
    visited.add(node.name)
    for decorator in node.decorator_list:
        if mark_name(decorator) in SKIP_MARKS:
            return "marked-" + mark_name(decorator).lower()
    for child in ast.walk(node):
        if isinstance(child, ast.Import) and any(n.name.split(".")[0] in OPTIONAL for n in child.names):
            return "optional-dependency"
        if isinstance(child, ast.ImportFrom) and (child.module or "").split(".")[0] in OPTIONAL:
            return "optional-dependency"
        if isinstance(child, ast.Name) and child.id in aliases:
            return "optional-dependency"
        if isinstance(child, ast.Constant) and isinstance(child.value, str) and child.value in OPTIONAL:
            return "optional-dependency"
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Name) and child.func.id in functions:
            reason = skip_reason(functions[child.func.id], aliases, functions, visited)
            if reason == "optional-dependency":
                return reason
    return None


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
    aliases = optional_aliases(original)
    skipped = {name: skip_reason(n, aliases, functions) for name, n in functions.items() if name.startswith("test")}
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

    def without_optional(name, *args, **kwargs):
        if name.split(".")[0] in OPTIONAL:
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
    return [event for _, event in capture.events], test_audit, len(transform.sites)


def corpus_from_events(events, tests, source_sites):
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
        return {"examined": len(cs) + len(os_), "cases": len(cs), "reasons": dict(sorted(Counter(c["reason"] for c in os_).items()))}
    return {"sympy": sympy.__version__, "cases": cases,
            "extraction": {**audit(), "sourceSites": source_sites,
                           "categories": {c: audit(c) for c in ("core", "polys")},
                           "omitted": omitted, "tests": tests,
                           "testStatuses": dict(sorted(Counter(t["status"] for t in tests).items()))}}


def main(destination, only=(), timeout=extract.ALARM_SECONDS):
    if sympy.__version__ != "1.14.0":
        raise RuntimeError("The compatibility reference is pinned to SymPy 1.14.0")
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise RuntimeError("Run with PYTHONHASHSEED=0 for deterministic reference output")
    from sympy.printing.pretty.pretty_symbology import pretty_use_unicode
    pretty_use_unicode(False)
    root = Path(sympy.__file__).parent
    events, tests, source_sites = [], [], 0
    for category in ("core", "polys"):
        for path in sorted((root / category / "tests").glob("test_*.py")):
            module = "sympy." + ".".join(path.relative_to(root).with_suffix("").parts)
            if only and not any(module.startswith(prefix) for prefix in only):
                continue
            start = time.monotonic()
            es, ts, count = execute_source(path.read_text(), module, category, str(path), timeout)
            events.extend(es)
            tests.extend(ts)
            source_sites += count
            print(f"{module}: {len(es)} observations, {len(ts)} tests, {time.monotonic() - start:.2f}s", file=sys.stderr, flush=True)
    corpus = corpus_from_events(events, tests, source_sites)
    # SymPy's string tests intentionally contain lone UTF-16 surrogates.
    # JSON escapes preserve them without emitting invalid UTF-8.
    Path(destination).write_text(json.dumps(corpus, indent=1, ensure_ascii=True, allow_nan=False) + "\n")
    print(json.dumps({c: a for c, a in corpus["extraction"]["categories"].items()}, indent=2), file=sys.stderr)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination")
    parser.add_argument("--only", action="append", default=[], help="Test module prefix (repeatable)")
    parser.add_argument("--timeout", type=float, default=extract.ALARM_SECONDS)
    args = parser.parse_args()
    main(args.destination, args.only, args.timeout)
