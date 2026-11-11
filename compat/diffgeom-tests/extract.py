"""Extract SymPy differential-geometry unit assertions without writing base corpora.

Run with PYTHONHASHSEED=0 python3 -B compat/diffgeom-tests/extract.py.
"""
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import extract
import extract_tests
from sympy.diffgeom import diffgeom


def main():
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise RuntimeError("Use PYTHONHASHSEED=0 for deterministic reference output")
    destination = Path(__file__).resolve().parent
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
