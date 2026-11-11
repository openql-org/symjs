"""Extract the independent SymPy 1.14 differential-geometry reference corpus.

Run with PYTHONHASHSEED=0 python3 -B compat/extend/diffgeom/extract.py.
The shared extractors are imported; their base corpus files are never written.
"""
import importlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
extract = importlib.import_module("extract")
import extract_tests
import sympy
import sympy.diffgeom as dg
from sympy.diffgeom import diffgeom
from sympy.diffgeom import rn

base_ser = extract.ser
base_public_api_reason = extract.public_api_reason
base_serialize_call = extract.serialize_call


def public_api_reason(fn, globs, extra_public):
    value = globs.get(fn)
    if isinstance(value, sympy.Expr) and type(value).__module__ == diffgeom.__name__ and callable(value):
        return None
    return base_public_api_reason(fn, globs, extra_public)


def serialize_call(record, call, globs, assumed, pre_args=None, printed=False):
    name = record['fn']
    value = globs.get(name)
    if isinstance(value, sympy.Expr) and type(value).__module__ == diffgeom.__name__ and callable(value):
        record['fn'] = '.__call__'
        record['selfSrc'] = name
    return base_serialize_call(record, call, globs, assumed, pre_args, printed)


def serialize(value):
    """Preserve chart identity and relation data before serializing field args."""
    for name in rn.__all__:
        if value is getattr(rn, name):
            return {"t": "Extension", "ref": name}
    if isinstance(value, sympy.core.symbol.Str):
        return base_ser(str(value))
    if isinstance(value, dg.CoordinateSymbol):
        args = [value.coord_sys, value.index]
    elif isinstance(value, dg.CoordSystem):
        args = [str(value.name), value.patch, value.args[2], value.relations]
    elif isinstance(value, dg.Manifold):
        args = [str(value.name), int(value.dim)]
    elif isinstance(value, dg.Patch):
        args = [str(value.name), value.manifold]
    elif isinstance(value, sympy.Basic) and type(value).__module__ == diffgeom.__name__:
        args = value.args
    else:
        return base_ser(value)
    return {"t": "Extension", "cls": type(value).__name__, "args": [serialize(a) for a in args]}


def main():
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise RuntimeError("Use PYTHONHASHSEED=0 for deterministic reference output")
    extract.ser = serialize
    extract.public_api_reason = public_api_reason
    extract.serialize_call = serialize_call
    extract.MODULES = {"sympy.diffgeom.diffgeom": "diffgeom", "sympy.diffgeom.rn": "diffgeom"}
    extract.SUBPACKAGE_PUBLIC["sympy.diffgeom."] = ("sympy.diffgeom",)
    extract.api_inventory = lambda: [{"name": name, "category": "diffgeom"} for name in dg.__all__]
    destination = Path(__file__).resolve().parent
    extract.main(str(destination / "corpus.json"))
    corpus_path = destination / "corpus.json"
    doctests = json.loads(corpus_path.read_text())
    doctests['modules'] = list(extract.MODULES)
    corpus_path.write_text(json.dumps(doctests, indent=1, ensure_ascii=False) + '\n')
    extract.PUBLIC |= set(dg.__all__)
    events, tests, count = [], [], 0
    for path in sorted((Path(diffgeom.__file__).parent / "tests").glob("test_*.py")):
        module = "sympy.diffgeom.tests." + path.stem
        es, ts, n = extract_tests.execute_source(path.read_text(), module, "diffgeom", str(path))
        events.extend(es)
        tests.extend(ts)
        count += n
    corpus = extract_tests.corpus_from_events(events, tests, count)
    corpus["extraction"]["categories"] = {"diffgeom": {k: corpus["extraction"][k] for k in ("examined", "cases", "reasons")}}
    (destination / "tests-corpus.json").write_text(json.dumps(corpus, indent=1, ensure_ascii=True, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()
