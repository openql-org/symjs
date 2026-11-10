"""Regenerate the references of free groups, finitely presented groups, coset
tables, rewriting systems, homomorphisms and polycyclic groups with SymPy 1.14.0.

Words are written as array forms [[symbol, exponent], ...] so that the tests
rebuild exactly the same inputs; results are compared by str().
"""
import json
from pathlib import Path

import sympy
from sympy.combinatorics import Permutation, PermutationGroup
from sympy.combinatorics.coset_table import coset_enumeration_c, coset_enumeration_r, modified_coset_enumeration_r
from sympy.combinatorics.fp_groups import FpGroup, FpSubgroup, low_index_subgroups, reidemeister_presentation, simplify_presentation
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.homomorphisms import group_isomorphism, homomorphism
from sympy.combinatorics.named_groups import AlternatingGroup, CyclicGroup, DihedralGroup, SymmetricGroup
from sympy.combinatorics.pc_groups import Collector

assert sympy.__version__ == '1.14.0'


def af(w):
    return [[str(s), int(e)] for s, e in w.array_form]


F, x, y = free_group('x, y')
FREE = {'x': x, 'y': y}
WORDS = [x**2*y**-1*x**3, (x*y)**3, x**-3*y**-1*x**5, x*y**2*x**-1, y**-2*x**4*y**-2, x**2*y**-2*x**-2 * y, y, x**-1]

words = []
for w in WORDS:
    words.append({
        'w': af(w), 'str': str(w), 'inverse': str(w.inverse()), 'len': len(w),
        'cyclic_reduction': str(w.cyclic_reduction()), 'removed': str(w.cyclic_reduction(removed=True)[1]),
        'identity_cyclic_reduction': str(w.identity_cyclic_reduction()), 'is_cyclically_reduced': w.is_cyclically_reduced(),
        'cyclic_conjugates': sorted(str(c) for c in w.cyclic_conjugates()),
        'exponent_sum_x': w.exponent_sum(x), 'exponent_sum_yi': w.exponent_sum(y**-1), 'generator_count_y': w.generator_count(y),
        'eliminate_x': str(w.eliminate_word(x, y**2, _all=True)), 'eliminate_xy': str(w.eliminate_words([x*y], _all=True)),
        'eliminate_noinv': str(w.eliminate_word(x**-1, y, inverse=False)),
        'subword_1_3': str(w.subword(1, min(3, len(w)))), 'cyclic_subword': str(w.cyclic_subword(1, len(w) + 3)),
        'power_of_x': w.power_of(x), 'power_of_xy': w.power_of(x * y), 'letters': [str(l) for l in w.letter_form],
        'lt': [w < v for v in WORDS], 'cyclic_conjugate': [w.is_cyclic_conjugate(v) for v in WORDS],
        'dependent': [w.is_dependent(v) for v in WORDS], 'ext_rep': [str(e) for e in w.ext_rep],
    })

PRESENTATIONS = {
    'S3': [x**2, y**3, (x*y)**2],
    'A4': [x**2, y**3, (x*y)**3],
    'S4': [x**2, y**3, (x*y)**4],
    'D3': [x**3, y**2, y*x*y*x],
    'D4': [x**4, y**2, (x*y)**2],
    'Q8': [x**4, x**2*y**-2, y**-1*x*y*x],
    'Z': [x, y**-1*x*y*x**-1],
    'free': [x**2],
}
groups = {}
for name, rels in PRESENTATIONS.items():
    G = FpGroup(F, rels)
    entry = {'rels': [af(r) for r in rels], 'str': str(G), 'order': str(G.order())}
    if G.order() is not sympy.S.Infinity:
        entry['table'] = G.coset_table([])
        for H in ([x], [y], [x * y]):
            C = coset_enumeration_r(G, H)
            C.compress()
            C.standardize()
            D = coset_enumeration_c(G, H)
            D.compress()
            D.standardize()
            entry.setdefault('cosets', []).append({'H': [af(h) for h in H], 'r': C.table, 'c': D.table, 'index': str(G.index(H)),
                                                   'reps': [str(C.coset_representative(i)) for i in range(len(C.table))]})
        g, r = reidemeister_presentation(G, [x])
        entry['reidemeister'] = [str(list(g)), str(list(r))]
        entry['low_index'] = [c.table for c in low_index_subgroups(G, 4)]
        entry['simplified'] = str(simplify_presentation(G).relators)
        entry['abelian'] = G.is_abelian
        entry['solvable'] = G.is_solvable
        entry['nilpotent'] = G.is_nilpotent
        entry['cyclic'] = G.is_cyclic
        entry['invariants'] = str(G.abelian_invariants())
        entry['elements'] = len(G.elements)
        entry['derived'] = [len(s) for s in G.derived_series()]
        entry['center'] = len(G.center())
        G.make_confluent()
        entry['reduce'] = [str(G.reduce(w)) for w in WORDS]
        entry['equals'] = [G.equals(w, x) for w in WORDS]
        entry['automaton'] = [str(G._rewriting_system.reduce_using_automaton(w)) for w in WORDS]
        entry['confluent'] = G._rewriting_system.is_confluent
    groups[name] = entry

fp = FpGroup(F, PRESENTATIONS['S4'])
K = FpSubgroup(fp, [x * y])
# The membership test of a subgroup of a free group (FpSubgroup with a FreeGroup parent) is not
# referenced: SymPy's implementation can raise IndexError or loop forever; symjs uses Stallings foldings.
subgroups = {'fp_contains': [K.__contains__(w) for w in WORDS], 'fp_order': str(K.order()), 'str': str(K)}
modified = modified_coset_enumeration_r(fp, [x * y])
modified.compress()
modified.standardize()
subgroups['modified'] = modified.table

# homomorphisms
D = DihedralGroup(4)
T = homomorphism(fp, SymmetricGroup(4), [x, y], [Permutation(3)(0, 1), Permutation(1, 2, 3)])
P, Tp = FpGroup(F, PRESENTATIONS['S3'])._to_perm_group()
homs = {
    'kernel': str(T.kernel().order()), 'image': str(T.image().order()), 'injective': T.is_injective(), 'surjective': T.is_surjective(),
    'apply': [str(T(w)) for w in WORDS], 'invert': [str(T(T.invert(T(w)))) for w in WORDS],
    'perm_order': str(P.order()),
    'iso_d3_s3': is_iso if (is_iso := group_isomorphism(DihedralGroup(3), SymmetricGroup(3), isomorphism=False)) is not None else None,
    'iso_c4_d2': group_isomorphism(CyclicGroup(4), DihedralGroup(2), isomorphism=False),
    'iso_fp': group_isomorphism(FpGroup(F, PRESENTATIONS['S3']), SymmetricGroup(3), isomorphism=False),
}

# presentations of permutation groups
pres = {}
for name, G in {'D4': D, 'S4': SymmetricGroup(4), 'A4': AlternatingGroup(4), 'C6': CyclicGroup(6), 'D6': DihedralGroup(6)}.items():
    p = G.presentation()
    s = G.strong_presentation()
    pres[name] = {'order': str(G.order()), 'presentation': str(p.order()), 'strong': str(s.order()), 'gens': len(p.generators)}

# collectors with fixed pc sequences
pc = {}
for name, G in {'S4': SymmetricGroup(4), 'D4': D, 'C6': CyclicGroup(6)}.items():
    PG = G.polycyclic_group()
    C = Collector(PG.pcgs, PG.pc_series, PG.relative_order)
    pc[name] = {
        'pcgs': [list(map(int, g.array_form)) for g in PG.pcgs],
        'series': [[list(map(int, g.array_form)) for g in s.generators] for s in PG.pc_series],
        'relative_order': [int(r) for r in PG.relative_order],
        'presentation': sorted(f'{k}: {v}' for k, v in C.pc_presentation.items()),
        'vectors': [C.exponent_vector(g) for g in sorted(G.elements, key=lambda p: p.array_form)],
        'depths': [C.depth(g) for g in sorted(G.elements, key=lambda p: p.array_form)],
        'induced': len(C.induced_pcgs([PG.pcgs[-1]])),
        'prime': PG.is_prime_order(),
    }

# coset tables: scans (SymPy test_coset_table), enumerations by both strategies, look-ahead, drafts and the
# modified methods, as [operation, arguments] replayed by the tests
from sympy.combinatorics.coset_table import CosetTable


def state(C, P=False):
    d = {'table': [list(row) for row in C.table], 'p': list(C.p)}
    if P:
        d['P'] = [[None if v is None else str(v) for v in row] for row in C.P]
    return d


scans = []
for rels, H, ops in [
    ([x**3, y**3, x**-1*y**-1*x*y], [x], [(0, x), (0, x**3), (0, y**3), (0, x**-1*y**-1*x*y), (1, x**3), (1, y**3), (1, x**-1*y**-1*x*y)]),
    ([x**2, y**3, (x*y)**3], [x*y], [(0, x*y), (0, x**2), (0, y**3), (0, (x*y)**3), (1, x**2), (1, y**3), (1, (x*y)**3), (2, x**2)]),
]:
    C = CosetTable(FpGroup(F, rels), H)
    steps = []
    for alpha, w in ops:
        C.scan_and_fill(alpha, w)
        steps.append({'alpha': alpha, 'w': af(w), **state(C)})
    scans.append({'rels': [af(r) for r in rels], 'H': [af(h) for h in H], 'steps': steps})

scans_c = []
for rels, H, ops in [
    ([x**3, y**3, x**-1*y**-1*x*y], [x], [(0, x), (0, x**3), (0, y**3), (0, x**-1*y**-1*x*y), (1, x**3), (1, y**3), (1, x**-1*y**-1*x*y), (2, y**3), (3, x**3)]),
    ([x**2, y**3, (x*y)**3], [x*y], [(0, x*y), (0, x**2), (0, y**3), (0, (x*y)**3), (1, x**2), (1, y**3), (1, (x*y)**3), (2, x**2)]),
]:
    C = CosetTable(FpGroup(F, rels), H)
    steps = []
    for alpha, w in ops:
        C.scan_and_fill_c(alpha, w)
        steps.append({'alpha': alpha, 'w': af(w), **state(C)})
    C.standardize()
    scans_c.append({'rels': [af(r) for r in rels], 'H': [af(h) for h in H], 'steps': steps, 'standardized': state(C)})

Fr, r, s_, t = free_group('r, s, t')
Fa, a, b = free_group('a, b')
Fc, a3, b3, c3 = free_group('a, b, c')
enumerations = []
for G, H in [
    (FpGroup(Fr, [t**-1*r*t*r**-2, r**-1*s_*r*s_**-2, s_**-1*t*s_*t**-2]), []),
    (FpGroup(Fa, [a**6, b**6, (a*b)**2, (a**2*b**2)**2, (a**3*b**3)**5]), [a]),
    (FpGroup(Fa, [a**4, b**4, (a*b)**4, (a**-1*b)**4, (a**2*b)**4, (a*b**2)**4, (a**2*b**2)**4, (a**-1*b*a*b)**4, (a*b**-1*a*b)**4]), [a]),
    (FpGroup(Fa, [b**-1*a**-1*b*a*b**-1*a*b*a**-2, a**-1*b**-1*a*b*a**-1*b*a*b**-2]), [a]),
    (FpGroup(F, [x**3, y**5, (x*y)**2]), [x*y, x**-1*y**-1*x*y*x]),
]:
    Cr = coset_enumeration_r(G, H)
    Cc = coset_enumeration_c(G, H)
    raw = {'r': len(Cr.p), 'c': len(Cc.p)}
    Cr.compress(); Cr.standardize(); Cc.compress(); Cc.standardize()
    enumerations.append({'free': [str(g) for g in G.free_group.symbols], 'rels': [af(q) for q in G.relators], 'H': [af(h) for h in H],
                         'r': Cr.table, 'c': Cc.table, 'raw': raw})
G = FpGroup(Fc, [a3**11, b3**5, c3**4, (a3*c3)**3, b3**2*c3**-1*b3**-1*c3, a3**4*b3**-1*a3**-1*b3])
CosetTable.max_stack_size = 10
La = coset_enumeration_c(G, [c3, b3, c3**2])
La.compress(); La.standardize()
CosetTable.max_stack_size = 100
look_ahead = {'free': ['a', 'b', 'c'], 'rels': [af(q) for q in G.relators], 'H': [af(h) for h in [c3, b3, c3**2]], 'table': La.table}

# drafts: an incomplete enumeration continued with more cosets
G = FpGroup(Fa, [a**6, b**6, (a*b)**2, (a**2*b**2)**2, (a**3*b**3)**5])
drafts = {}
for strategy in ('relator_based', 'coset_table_based'):
    d = G.coset_enumeration([a], strategy=strategy, max_cosets=40, incomplete=True)
    first = {'complete': d.is_complete(), 'n': len(d.table)}
    C = G.coset_enumeration([a], strategy=strategy, max_cosets=20000, draft=d)
    C.standardize()
    drafts[strategy] = {'first': first, 'table': C.table}

f = FpGroup(F, [x**3, y**5, (x*y)**2])
C = CosetTable(f, [x*y, x**-1*y**-1*x*y*x])
mod_steps = []
for op, args in [('define', (0, x)), ('define', (1, x)), ('scan', (0, x**3, 'identity', False)), ('scan', (0, x*y, 'a_0', False)),
                 ('define', (2, y**-1)), ('scan', (0, x**-1*y**-1*x*y*x, 'a_1', False)), ('scan', (0, y**5, 'identity', True)),
                 ('scan', (1, (x*y)**2, 'identity', True))]:
    if op == 'define':
        C.modified_define(*args)
        mod_steps.append({'op': op, 'alpha': args[0], 'w': af(args[1]), **state(C, True)})
    else:
        yy = C._grp.identity if args[2] == 'identity' else C._grp.generators[int(args[2][-1])]
        C.modified_scan(args[0], args[1], yy, fill=args[3])
        mod_steps.append({'op': op, 'alpha': args[0], 'w': af(args[1]), 'y': args[2], 'fill': args[3], **state(C, True)})
mod_enum = modified_coset_enumeration_r(FpGroup(F, [x**3, y**3, x**-1*y**-1*x*y]), [x]).table
Mc = modified_coset_enumeration_r(FpGroup(Fa, [a**6, b**6, (a*b)**2, (a**2*b**2)**2, (a**3*b**3)**5]), [a])
mod_cox = {'p': len(Mc.p), 'omega': len(Mc.omega)}
cosets = {'scans_c': scans_c, 'mod_cox': mod_cox, 'scans': scans, 'enumerations': enumerations, 'look_ahead': look_ahead, 'drafts': drafts, 'modified': mod_steps, 'modified_enumeration': mod_enum}

# low index subgroups (SymPy test_fp_groups.py)
f7 = FpGroup(F, [x**2, y**3, (x*y)**7])
low_index = {'N15': [c.table for c in low_index_subgroups(f7, 15)], 'N10x': [c.table for c in low_index_subgroups(f7, 10, [x])]}

# subgroups with their injections, orders by the various methods
f = FpGroup(F, [x**4, y**2, x*y*x**-1*y])
K, T = f.subgroup([x*y], homomorphism=True)
K2, T2 = f.subgroup([x**-1*y*x], homomorphism=True)
Fabc, a1, b1, c1 = free_group('a, b, c')
fp_extra = {
    'K': str(K), 'K_rels': str(K.relators), 'T_gens': str(T(list(K.generators))), 'T2_cube': str(T2(K2.generators[0]**3)),
    'order_d4': str(f.order()), 'order_inf': str(FpGroup(F, [x*y*x**-1*y**-1, y**2]).order()),
    'order_2000': str(FpGroup(Fabc, [a1**250, b1**2, c1*b1*c1**-1*b1, c1**4, c1**-1*a1**-1*c1*a1, a1**-1*b1**-1*a1*b1]).order()),
    'order_cyclic': str(FpGroup(free_group('z')[0], [free_group('z')[1]**6, free_group('z')[1]**4]).order()),
    'center_d8': str(FpGroup(F, [x**2, y**8, x*y*x**-1*y]).center()),
    'lcs_a4': [len(t) for t in FpGroup(F, [x**3, y**2, (x*y)**3]).lower_central_series()],
    'derived_a4': len(FpGroup(F, [x**3, y**2, (x*y)**3]).derived_subgroup()),
    'centralizer_d4': len(FpGroup(F, [x**2, y**4, x*y*x**-1*y]).centralizer(x)),
    'normal_closure_d4': len(FpGroup(F, [x**2, y**4, x*y*x**-1*y]).normal_closure([x])),
    'composition_a4': len(FpGroup(F, [x**3, y**2, (x*y)**3]).composition_series()),
    'simplify_change': [str(g) for g in simplify_presentation(FpGroup(F, [x**2, x**5, y**3]), change_gens=True).generators],
    'simplify_x': [str(r) for r in simplify_presentation(FpGroup(F, [x**2, x**5, y**3])).relators],
    'psl': [str(reidemeister_presentation(FpGroup(Fabc, [a1**11, b1**5, c1**4, (b1*c1**2)**2, (a1*b1*c1)**3, (a1**4*c1**2)**3, b1**2*c1**-1*b1**-1*c1, a1**4*b1**-1*a1**-1*b1]), [a1, b1, c1**2])[0])],
}

out = {'low_index': low_index, 'fp_extra': fp_extra, 'cosets': cosets, 'words': words, 'groups': groups, 'subgroups': subgroups, 'homomorphisms': homs, 'presentations': pres, 'pc': pc}
path = Path(__file__).resolve().parents[1] / 'packages/symjs/tests/combinatorics/fpgroups.references.json'
path.write_text(json.dumps(out, indent=1) + '\n')
