# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import json
from pathlib import Path

MAX_SHARD_BYTES = 25_000_000


def json_line(value):
    return json.dumps(value, ensure_ascii=True, allow_nan=False, separators=(",", ":"))


def write_array(path, values):
    path.write_text("[\n" + ",\n".join(json_line(v) for v in values) + "\n]\n", encoding="utf-8")


def write_shards(destination, category, cases, max_bytes=MAX_SHARD_BYTES):
    """Bound shards by encoded bytes; never split a case or change its key order."""
    destination.mkdir(parents=True, exist_ok=True)
    chunks, chunk, size = [], [], 4
    for case in cases:
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
    return shards


def read_cases(directory, summary):
    return [case for shard in summary["shards"]
            for case in json.loads((directory / shard["file"]).read_text())]


def read_doctest_cases(directory, index, categories):
    """Restore extraction order where several categories contribute to one generated test file."""
    records = {name: iter(read_cases(directory, summary)) for name, summary in index["categories"].items()
               if name in categories}
    cases = []
    for name, count in index["caseOrder"]:
        if name in records:
            cases.extend(next(records[name]) for _ in range(count))
    if any(next(rows, None) is not None for rows in records.values()):
        raise ValueError("Doctest case order does not cover every record")
    return cases


def read_doctest(directory):
    directory = Path(directory)
    index = json.loads((directory / "index.json").read_text())
    extraction = index["extraction"]
    cases = read_doctest_cases(directory, index, index["categories"])
    for summary in index["categories"].values():
        for key, rows in json.loads((directory / summary["auditFile"]).read_text()).items():
            extraction.setdefault(key, []).extend(rows)
    return {"sympy": index["sympy"], "api": index["api"], "extraction": extraction, "cases": cases}
