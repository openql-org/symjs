#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Pin the entire SymPy module universe, including unmeasured modules.

This static scan never imports optional backends or executes doctests. A
module with a symjs source counterpart is only partially implemented until
its complete public contract has been assessed. Source size is not a measure
of behavioral compatibility.
"""
import ast
import doctest
import hashlib
import json
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
}

# Explicit correspondences for the different kernel layout and combined modules.
CORRESPONDENCES = {
    'sympy.core.basic': ['core/nodes.ts', 'core/basic.ts'],
    'sympy.core.expr': ['core/nodes.ts', 'core/methods.ts'],
    'sympy.core.add': ['core/ops.ts'], 'sympy.core.mul': ['core/ops.ts'],
    'sympy.core.power': ['core/ops.ts'], 'sympy.core.function': ['core/undef.ts', 'core/defun.ts'],
    'sympy.core.symbol': ['core/nodes.ts'], 'sympy.core.numbers': ['core/numbers.ts', 'core/num.ts'],
    'sympy.assumptions.ask': ['core/refine.ts'], 'sympy.assumptions.refine': ['core/refine.ts'],
    'sympy.core.relational': ['core/logic.ts'], 'sympy.core.traversal': ['core/traverse.ts'],
    'sympy.core.evalf': ['numeric/evalf.ts'],
    'sympy.polys.polytools': ['polys/sympoly.ts'], 'sympy.polys.polyroots': ['polys/poly.ts'],
    'sympy.polys.numberfields.minpoly': ['polys/numberfields.ts'],
    'sympy.integrals.integrals': ['integrals/integrate.ts'],
    'sympy.matrices.matrixbase': ['matrices/matrix.ts', 'matrices/more.ts'],
    'sympy.matrices.dense': ['matrices/matrix.ts'], 'sympy.matrices.eigen': ['matrices/linalg.ts'],
    'sympy.matrices.decompositions': ['matrices/linalg.ts'],
    'sympy.solvers.solvers': ['solvers/solve.ts'],
    'sympy.solvers.ode.ode': ['solvers/ode.ts', 'solvers/dsolve.ts'],
    'sympy.solvers.ode.systems': ['solvers/odesystem.ts'],
    'sympy.solvers.ode.lie_group': ['solvers/liegroup.ts'],
    'sympy.solvers.diophantine.diophantine': ['solvers/diophantine.ts'],
    'sympy.tensor.array.ndim_array': ['tensor/ndimarray.ts'],
    'sympy.tensor.array.arrayop': ['tensor/arrayop.ts'],
    'sympy.functions.elementary.trigonometric': ['functions/elementary/elementary.ts', 'functions/elementary/trigext.ts'],
    'sympy.functions.elementary.hyperbolic': ['functions/elementary/elementary.ts', 'functions/elementary/trigext.ts'],
    'sympy.functions.elementary.exponential': ['functions/elementary/elementary.ts'],
    'sympy.functions.special.gamma_functions': ['functions/special/special.ts'],
    'sympy.functions.special.error_functions': ['functions/special/special.ts'],
}
# These independently scoped mathematical modules were inspected and have no
# implementation yet. Everything else without a correspondence stays unassessed.
NOT_IMPLEMENTED = {
    'sympy.categories.diagram_drawing', 'sympy.diffgeom.diffgeom',
    'sympy.polys.numberfields.galoisgroups', 'sympy.functions.special.bsplines',
    'sympy.combinatorics.fp_groups', 'sympy.combinatorics.free_groups',
    'sympy.tensor.toperators', 'sympy.printing.jscode',
}


def build_inventory(root):
    reference = Path(sympy.__file__).parent
    source = root / 'packages/symjs/src'
    corpus = json.loads((root / 'compat/corpus.json').read_text())
    measured = {c['module'] for c in corpus['cases']}
    selected_ast = ast.parse((root / 'compat/extract.py').read_text())
    selected = next(ast.literal_eval(n.value) for n in selected_ast.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'MODULES' for t in n.targets))
    rows = []
    parser = doctest.DocTestParser()
    for path in sorted(reference.rglob('*.py')):
        rel = path.relative_to(reference)
        if {'tests', 'benchmarks', '__pycache__'} & set(rel.parts) or path.name.startswith('test_'):
            continue
        module = 'sympy.' + '.'.join(rel.with_suffix('').parts)
        if module.endswith('.__init__'):
            module = module[:-9]
        text = path.read_text()
        tree = ast.parse(text)
        names = []
        examples = 0
        for node in ast.walk(tree):
            if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                doc = ast.get_docstring(node)
                if doc:
                    examples += sum(bool(ex.want.strip()) for ex in parser.get_examples(doc))
        for node in tree.body:
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and not node.name.startswith('_'):
                names.append(node.name)
                if isinstance(node, ast.ClassDef):
                    names.extend(node.name + '.' + m.name for m in node.body if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)) and not m.name.startswith('_'))
        counterpart = list(CORRESPONDENCES.get(module, []))
        candidate = '/'.join(p.replace('_', '') for p in rel.with_suffix('').parts) + '.ts'
        if (source / candidate).is_file():
            counterpart.append(candidate)
        counterpart = sorted({p for p in counterpart if (source / p).is_file()})
        reason = next((why for prefix, why in EXCLUSIONS.items() if module == prefix or module.startswith(prefix + '.')), None)
        status = 'excluded' if reason else 'partial' if counterpart else 'unimplemented' if module in NOT_IMPLEMENTED else 'unassessed'
        rows.append({'module': module, 'sha256': hashlib.sha256(text.encode()).hexdigest(), 'status': status,
                     **({'reason': reason} if reason else {}), 'sources': counterpart,
                     'selectedForExtraction': module in selected, 'hasCorpusCases': module in measured,
                     'documentedExamples': examples, 'declaredPublicNames': names})
    return {'schema': 1, 'reference': {'sympy': sympy.__version__},
            'definitions': {'partial': 'A source counterpart exists; full behavioral compatibility is not established.',
                            'unimplemented': 'Inspected mathematical module without an implementation.',
                            'unassessed': 'Not assessed; never treated as implemented or deliberately excluded.',
                            'excluded': 'An explicit runtime/infrastructure exclusion, with its reason.',
                            'declaredPublicNames': 'Non-private definitions and class members in source; not an API-completeness denominator.'},
            'modules': rows}


if __name__ == '__main__':
    root = Path(__file__).resolve().parent.parent
    if sympy.__version__ != '1.14.0':
        raise SystemExit('The inventory is pinned to SymPy 1.14.0; review an upstream version change explicitly.')
    destination = Path(sys.argv[1]) if len(sys.argv) > 1 else root / 'compat/scope-inventory.json'
    destination.write_text(json.dumps(build_inventory(root), indent=1, ensure_ascii=False) + '\n')
