# SymPy unit-test compatibility (core and polys pilot)

Reference: SymPy 1.14.0. Independent of the doctest corpus and its ratchet.

Measured **12933** cases: **7851 exact**, **227 equivalent**, **4855 failing**. Agreement: **62.46%**.

Replay runtime: **200.45 s**. Known gaps: **4855**. Exception class mismatches accepted in the pilot: **160**.

Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the existing doctest matching and equivalence rules.

## Agreement by category

| Category | Cases | Exact | Equivalent | Fail | Unsupported | Error | Agreement |
|---|---:|---:|---:|---:|---:|---:|---:|
| core | 7858 | 5239 | 179 | 1245 | 918 | 277 | 68.95% |
| polys | 5075 | 2612 | 48 | 297 | 1679 | 439 | 52.41% |

## Agreement by test module

| Module | Cases | Exact | Equivalent | Fail | Unsupported | Error | Agreement |
|---|---:|---:|---:|---:|---:|---:|---:|
| sympy.core.tests.test_args | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_arit | 1235 | 712 | 27 | 255 | 235 | 6 | 59.84% |
| sympy.core.tests.test_assumptions | 699 | 344 | 0 | 171 | 181 | 3 | 49.21% |
| sympy.core.tests.test_basic | 198 | 164 | 0 | 10 | 11 | 13 | 82.83% |
| sympy.core.tests.test_cache | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_compatibility | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_complex | 74 | 45 | 12 | 17 | 0 | 0 | 77.03% |
| sympy.core.tests.test_constructor_postprocessor | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_containers | 57 | 19 | 0 | 1 | 31 | 6 | 33.33% |
| sympy.core.tests.test_count_ops | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_diff | 46 | 36 | 0 | 2 | 0 | 8 | 78.26% |
| sympy.core.tests.test_equal | 12 | 12 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.core.tests.test_eval | 33 | 33 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.core.tests.test_evalf | 133 | 61 | 18 | 23 | 30 | 1 | 59.40% |
| sympy.core.tests.test_expand | 145 | 110 | 2 | 17 | 16 | 0 | 77.24% |
| sympy.core.tests.test_expr | 846 | 666 | 14 | 94 | 30 | 42 | 80.38% |
| sympy.core.tests.test_exprtools | 183 | 129 | 6 | 12 | 9 | 27 | 73.77% |
| sympy.core.tests.test_facts | 1 | 0 | 0 | 0 | 1 | 0 | 0.00% |
| sympy.core.tests.test_function | 389 | 205 | 10 | 126 | 19 | 29 | 55.27% |
| sympy.core.tests.test_kind | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_logic | 61 | 47 | 0 | 1 | 0 | 13 | 77.05% |
| sympy.core.tests.test_match | 236 | 171 | 0 | 53 | 0 | 12 | 72.46% |
| sympy.core.tests.test_multidimensional | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_noncommutative | 44 | 31 | 1 | 11 | 1 | 0 | 72.73% |
| sympy.core.tests.test_numbers | 1616 | 1383 | 15 | 118 | 31 | 69 | 86.51% |
| sympy.core.tests.test_operations | 4 | 1 | 0 | 2 | 1 | 0 | 25.00% |
| sympy.core.tests.test_parameters | 47 | 22 | 25 | 0 | 0 | 0 | 100.00% |
| sympy.core.tests.test_power | 184 | 103 | 29 | 42 | 7 | 3 | 71.74% |
| sympy.core.tests.test_priority | 4 | 4 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.core.tests.test_random | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_relational | 1008 | 522 | 0 | 186 | 283 | 17 | 51.79% |
| sympy.core.tests.test_rules | 6 | 5 | 0 | 1 | 0 | 0 | 83.33% |
| sympy.core.tests.test_singleton | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_sorting | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.core.tests.test_subs | 353 | 262 | 9 | 72 | 1 | 9 | 76.77% |
| sympy.core.tests.test_symbol | 114 | 80 | 0 | 17 | 17 | 0 | 70.18% |
| sympy.core.tests.test_sympify | 120 | 66 | 10 | 14 | 14 | 16 | 63.33% |
| sympy.core.tests.test_traversal | 9 | 5 | 1 | 0 | 0 | 3 | 66.67% |
| sympy.core.tests.test_truediv | 1 | 1 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.core.tests.test_var | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.polys.tests.test_appellseqs | 61 | 56 | 0 | 5 | 0 | 0 | 91.80% |
| sympy.polys.tests.test_constructor | 55 | 25 | 6 | 13 | 6 | 5 | 56.36% |
| sympy.polys.tests.test_densearith | 312 | 1 | 0 | 3 | 308 | 0 | 0.32% |
| sympy.polys.tests.test_densebasic | 292 | 280 | 0 | 0 | 0 | 12 | 95.89% |
| sympy.polys.tests.test_densetools | 292 | 0 | 0 | 0 | 292 | 0 | 0.00% |
| sympy.polys.tests.test_dispersion | 9 | 8 | 0 | 0 | 0 | 1 | 88.89% |
| sympy.polys.tests.test_distributedmodules | 36 | 36 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.polys.tests.test_euclidtools | 123 | 96 | 0 | 0 | 2 | 25 | 78.05% |
| sympy.polys.tests.test_factortools | 186 | 66 | 2 | 1 | 85 | 32 | 36.56% |
| sympy.polys.tests.test_fields | 54 | 48 | 0 | 0 | 6 | 0 | 88.89% |
| sympy.polys.tests.test_galoistools | 323 | 321 | 0 | 2 | 0 | 0 | 99.38% |
| sympy.polys.tests.test_groebnertools | 73 | 10 | 0 | 0 | 0 | 63 | 13.70% |
| sympy.polys.tests.test_heuristicgcd | 9 | 0 | 0 | 0 | 9 | 0 | 0.00% |
| sympy.polys.tests.test_hypothesis | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.polys.tests.test_injections | 0 | 0 | 0 | 0 | 0 | 0 | - |
| sympy.polys.tests.test_modulargcd | 43 | 0 | 0 | 0 | 43 | 0 | 0.00% |
| sympy.polys.tests.test_monomials | 11 | 11 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.polys.tests.test_multivariate_resultants | 5 | 5 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.polys.tests.test_orderings | 18 | 7 | 0 | 0 | 11 | 0 | 38.89% |
| sympy.polys.tests.test_orthopolys | 90 | 19 | 0 | 0 | 0 | 71 | 21.11% |
| sympy.polys.tests.test_partfrac | 35 | 25 | 2 | 4 | 2 | 2 | 77.14% |
| sympy.polys.tests.test_polyclasses | 142 | 16 | 0 | 2 | 115 | 9 | 11.27% |
| sympy.polys.tests.test_polyfuncs | 46 | 39 | 0 | 4 | 0 | 3 | 84.78% |
| sympy.polys.tests.test_polymatrix | 15 | 0 | 0 | 0 | 15 | 0 | 0.00% |
| sympy.polys.tests.test_polyoptions | 9 | 3 | 0 | 0 | 6 | 0 | 33.33% |
| sympy.polys.tests.test_polyroots | 108 | 51 | 7 | 13 | 32 | 5 | 53.70% |
| sympy.polys.tests.test_polytools | 1584 | 911 | 26 | 212 | 302 | 133 | 59.15% |
| sympy.polys.tests.test_polyutils | 43 | 0 | 0 | 0 | 43 | 0 | 0.00% |
| sympy.polys.tests.test_puiseux | 69 | 50 | 0 | 3 | 9 | 7 | 72.46% |
| sympy.polys.tests.test_pythonrational | 78 | 68 | 0 | 0 | 8 | 2 | 87.18% |
| sympy.polys.tests.test_rationaltools | 30 | 30 | 0 | 0 | 0 | 0 | 100.00% |
| sympy.polys.tests.test_ring_series | 113 | 92 | 0 | 8 | 0 | 13 | 81.42% |
| sympy.polys.tests.test_rings | 166 | 147 | 1 | 9 | 6 | 3 | 89.16% |
| sympy.polys.tests.test_rootisolation | 306 | 2 | 0 | 0 | 303 | 1 | 0.65% |
| sympy.polys.tests.test_rootoftools | 131 | 86 | 0 | 10 | 8 | 27 | 65.65% |
| sympy.polys.tests.test_solvers | 9 | 5 | 4 | 0 | 0 | 0 | 100.00% |
| sympy.polys.tests.test_specialpolys | 36 | 16 | 0 | 3 | 0 | 17 | 44.44% |
| sympy.polys.tests.test_sqfreetools | 66 | 53 | 0 | 5 | 0 | 8 | 80.30% |
| sympy.polys.tests.test_subresultants_qq_zz | 97 | 29 | 0 | 0 | 68 | 0 | 29.90% |

## Extraction audit

16311 static assertion/exception sites; 32778 examined observations. Executed loop instances count individually. Duplicates count as omissions; never-reached sites count once. Partial observations from timed-out tests are discarded.

| Category | Examined | Cases | Omitted |
|---|---:|---:|---:|
| core | 25605 | 7858 | 17747 |
| polys | 7173 | 5075 | 2098 |

| Omission reason | core | polys | Total |
|---|---:|---:|---:|
| duplicate | 579 | 19 | 598 |
| marked-skip | 11 | 0 | 11 |
| marked-slow | 0 | 73 | 73 |
| marked-tooslow | 0 | 2 | 2 |
| marked-xfail | 47 | 10 | 57 |
| non-boolean-assertion | 22 | 4 | 26 |
| non-call-expression | 11791 | 392 | 12183 |
| not-executed | 27 | 18 | 45 |
| not-exported-api | 2176 | 399 | 2575 |
| optional-dependency | 82 | 6 | 88 |
| private-api | 50 | 18 | 68 |
| python-runtime-api | 260 | 266 | 526 |
| serialization-error | 17 | 0 | 17 |
| stateful-iterator-input | 76 | 125 | 201 |
| test-utility | 32 | 1 | 33 |
| unserializable-input | 867 | 359 | 1226 |
| unsupported-assertion | 1704 | 406 | 2110 |
| unsupported-raises | 6 | 0 | 6 |

| Test execution status | Count |
|---|---:|
| completed | 2853 |
| marked-skip | 71 |
| marked-slow | 5 |
| marked-tooslow | 2 |
| marked-xfail | 28 |
| optional-dependency | 15 |
| test-exception:Failed | 1 |

## Main failure groups

| API and result | Cases |
|---|---:|
| core: Relational (unsupported) | 148 |
| core: .is_nonpositive (unsupported) | 117 |
| polys: .dup_count_complex_roots (unsupported) | 105 |
| core: .subs (fail) | 87 |
| polys: .dup_isolate_real_roots_sqf (unsupported) | 76 |
| polys: .rep (unsupported) | 68 |
| core: .diff (fail) | 65 |
| core: .is_even (unsupported) | 59 |
| polys: groebner (error) | 56 |
| core: .is_odd (unsupported) | 55 |
| core: .reversedsign (unsupported) | 51 |
| core: .matches (fail) | 50 |
| core: .is_positive (fail) | 49 |
| core: .is_imaginary (unsupported) | 47 |
| core: .is_integer (fail) | 42 |
| core: .is_nonnegative (fail) | 42 |
| core: unchanged (unsupported) | 39 |
| core: .is_negative (fail) | 37 |
| core: .simplify (fail) | 37 |
| polys: dict_from_expr (unsupported) | 37 |
| core: .is_zero (fail) | 35 |
| core: .is_real (fail) | 35 |
| core: .is_comparable (unsupported) | 35 |
| polys: .dup_refine_real_root (unsupported) | 35 |
| polys: .dup_isolate_real_roots (unsupported) | 32 |
| core: Mod (fail) | 31 |
| core: .__lt__ (fail) | 31 |
| core: .is_finite (fail) | 28 |
| polys: .from_poly (unsupported) | 28 |
| core: .__ge__ (fail) | 26 |
| core: .is_rational (fail) | 25 |
| core: .is_composite (unsupported) | 25 |
| core: .__le__ (fail) | 25 |
| core: .__gt__ (fail) | 25 |
| core: .rewrite (fail) | 24 |
| polys: dmp_ground_content (unsupported) | 24 |
| polys: dup_sign_variations (unsupported) | 24 |
| core: .evalf (fail) | 22 |
| polys: intervals (unsupported) | 22 |
| core: .__rshift__ (fail) | 21 |

## Exception class mismatches

Any exception from an invoked adapter counts as agreement in this pilot. Missing adapters and deserialization failures do not. ValueError and ZeroDivisionError map to RangeError; TypeError, NotImplementedError and polynomial exception classes retain their names.

| Case | Python class | JS class |
|---|---|---|
| sympy.core.tests.test_assumptions:test_sanitize_assumptions:1043 #975e81bb6e5e9d0b3fd5 | ValueError | SyntaxError |
| sympy.core.tests.test_assumptions:test_sanitize_assumptions:1043 #1f9a7c6550525f71fe24 | ValueError | SyntaxError |
| sympy.core.tests.test_assumptions:test_sanitize_assumptions:1043 #8cb6ec9789d404150163 | ValueError | SyntaxError |
| sympy.core.tests.test_assumptions:test_issue_8075:1115 #1488a5b1b86786f5c97c | InconsistentAssumptions | SyntaxError |
| sympy.core.tests.test_assumptions:test_issue_8075:1116 #e5ad4be60544e7980d41 | InconsistentAssumptions | SyntaxError |
| sympy.core.tests.test_assumptions:test_issue_16579:1211 #1e1ddce5c866304d64e0 | InconsistentAssumptions | SyntaxError |
| sympy.core.tests.test_basic:test_subs:135 #5408e2b17838ab4cc2b7 | ValueError | SympifyError |
| sympy.core.tests.test_basic:test_subs:140 #6cf8ca1feb637ed1d3bd | TypeError | SympifyError |
| sympy.core.tests.test_containers:test_Tuple_concatenation:59 #eef7e1a0340099e725b1 | TypeError | SympifyError |
| sympy.core.tests.test_containers:test_Tuple_mul:129 #ac78bd6b788ed0595937 | TypeError | SympifyError |
| sympy.core.tests.test_containers:test_Dict:168 #2a7daa27219c4e5c8e8a | KeyError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:435 #a52c25d9a70f58b2bdc6 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:436 #8186f47faa74097d20c9 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:441 #0b224cdd80e17ca43388 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:442 #c0ba84b960bd29e3cc1f | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:435 #26b99d66f701eaf9bd0d | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:436 #1d6c86565f4e1e3dfa65 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:440 #a6149cb8e5bbdc558734 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:441 #887bbd75f16f638c98b6 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:442 #be40ebe6c4d0188f4a0a | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:435 #28e507e7284177fac734 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:436 #d784493df9851acf4a66 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:440 #735cd97326398f3911d6 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:441 #244ec6638e3139c67173 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:442 #0941031f839925d13075 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:435 #f383fb99b67a34a16fb4 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:436 #4e8a00a0931e3e177c0e | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:440 #60d6f17cdbd581abc17a | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:441 #4d28ddf02815680d98a7 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:442 #f54c9754e3aca5f80125 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:435 #ad25cfc15a9b5f41fbd3 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:436 #a98ca44a180a19506e9f | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:440 #50bafb10dadba6d04a10 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:441 #b091963b9dce934bd73f | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_basic_nostr:442 #bd5dd3d4062b864f3800 | TypeError | SympifyError |
| sympy.core.tests.test_expr:test_expr:2233 #ef0dc6c8d86ae98c2dd7 | TypeError | RangeError |
| sympy.core.tests.test_function:test_Lambda_arguments:317 #3560f254c8046f03c4ec | TypeError | SympifyError |
| sympy.core.tests.test_function:test_issue_5399:623 #c39e7bd2dba101e3918b | ValueError | TypeError |
| sympy.core.tests.test_function:test_Derivative__new__:1337 #abca8034fae3b8d94482 | TypeError | RangeError |
| sympy.core.tests.test_function:test_issue_15947:1390 #5367ed47c04b212099ad | TypeError | SympifyError |
| sympy.core.tests.test_function:test_issue_27163:1459 #a0138f1b2404cff805ca | TypeError | SympifyError |
| sympy.core.tests.test_numbers:test_igcd:236 #734b33c182c32e46252e | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #fbef4cc00d89a26289c8 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #82d5cf08fbb72169ccf4 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #6e83bce646c18d1a4613 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #768e0734e19f179eb04e | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #2c15d73e76ceebb1a8ea | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_igcd:241 #380c55df818f7d142610 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_ilcm:275 #aa424ca86a781e491ac9 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_ilcm:276 #18f80e829159e805aa3a | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Integer_new:321 #7a2c5aed3fad5bf75e54 | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Rational_new:355 #03bc1eac1ba91125513d | TypeError | SyntaxError |
| sympy.core.tests.test_numbers:test_Rational_new:356 #e7cab8c9c264051a14cd | TypeError | SyntaxError |
| sympy.core.tests.test_numbers:test_Number_new:400 #5a27deba34b9b470c91b | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Number_new:401 #f41a138e5f1cbc5bc14a | TypeError | SympifyError |
| sympy.core.tests.test_numbers:test_Float:517 #614811a8c5fa47908a80 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Float:561 #cec31480ff3f1c125198 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Float:577 #d886c6b3a7f7b368bc90 | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Float:578 #755521fab5e68656a380 | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Float:586 #a0dfb5da6903e97d6283 | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Float:587 #cebc45a3cb95ec934bae | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Float:588 #ed6dc1526be9598398c8 | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Float:589 #6cb52839a06afc67833a | ValueError | SyntaxError |
| sympy.core.tests.test_numbers:test_Float:631 #225e4088952ee57e0478 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_Float:632 #6cc4926b58fb26f48bf6 | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_integer_log:1077 #c45a928f064612246c0b | ValueError | TypeError |
| sympy.core.tests.test_numbers:test_comp1:2008 #163a45ea9eba88aec6ee | ValueError | SympifyError |
| sympy.core.tests.test_numbers:test_mod_inverse:2065 #9d9714355712220d1d28 | TypeError | RangeError |
| sympy.core.tests.test_symbol:test_Dummy_force_dummy_index:50 #316e1776eeb1f0d87450 | AssertionError | TypeError |
| sympy.core.tests.test_symbol:test_symbols:328 #1a8515b7b305a9c8eb6f | ValueError | SyntaxError |
| sympy.core.tests.test_symbol:test_symbols:329 #826c114cbd1efba38726 | ValueError | SyntaxError |
| sympy.core.tests.test_symbol:test_symbols:330 #61925f0ab75b88b3f01f | ValueError | SyntaxError |
| sympy.core.tests.test_symbol:test_symbols:331 #dacb8e52220efbad0f2d | ValueError | SyntaxError |
| sympy.core.tests.test_symbol:test_symbols:332 #cf1ef133c525497b6c2f | ValueError | SyntaxError |
| sympy.core.tests.test_symbol:test_symbols:333 #8f2e786d2c8a1eff6a37 | ValueError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_factorial:254 #c3a21b253dd403f30a7a | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_factorial:255 #557dedc3cc1120bffeb5 | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_factorial:256 #1526e5b802459a9857e9 | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_factorial:257 #3a61b6f126aedbded9f6 | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_factorial:258 #e5ce4f46d8689b85c28e | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_lambda_raises:275 #0960afe5f7c32940a4e4 | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_lambda_raises:276 #f8c4af005c9aa0c66f95 | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_lambda_raises:277 #fd2b7f5dfb35c74fc10c | SympifyError | SyntaxError |
| sympy.core.tests.test_sympify:test_sympify_raises:283 #2d221edfad70a717189a | SympifyError | SyntaxError |
| sympy.polys.tests.test_fields:test_FracElement___truediv__:275 #746d24248ab58efaad9e | ZeroDivisionError | SympifyError |
| sympy.polys.tests.test_polyroots:test_roots_strict:651 #370153f3c12af7961726 | UnsolvableFactorError | TypeError |
| sympy.polys.tests.test_polyroots:test_issue_19113:740 #61ff0d4f40f2718bdd1e | PolynomialError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly_from_list:179 #5083923ce56d26fdb5cd | MultivariatePolynomialError | PolynomialError |
| sympy.polys.tests.test_polytools:test_Poly__new__:373 #19eb6b65fafa33e8cefb | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:374 #cbeaf93d5e394e772c42 | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:376 #4dde3660eeafb313e1ac | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:377 #4b181194715993747234 | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:379 #3d30f27859786c31ce29 | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:380 #e50d29a0b6d03942a6af | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:382 #b8d677567c40af74fcd6 | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:383 #edee100496eadb8d96ac | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:385 #ea071b588befb105839b | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:388 #71c90c859e17142d2567 | OptionError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:391 #0713fac0facbea91333d | NotImplementedError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:392 #e2ba602af833e7e03e2f | NotImplementedError | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:394 #e034ff7c36f48ec61a40 | GeneratorsNeeded | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:395 #03f581266c8786ea936a | GeneratorsNeeded | TypeError |
| sympy.polys.tests.test_polytools:test_Poly__new__:396 #1debd1479841bb268186 | GeneratorsNeeded | TypeError |
| sympy.polys.tests.test_polytools:test_Poly_get_modulus:715 #2982c64c473eb056a2bc | PolynomialError | DomainError |
| sympy.polys.tests.test_polytools:test_Poly_set_modulus:726 #fb33fc5fcdec515699eb | CoercionFailed | DomainError |
| sympy.polys.tests.test_polytools:test_Poly_pow:829 #b722f120e7b3f0daaebb | TypeError | PolificationFailed |
| sympy.polys.tests.test_polytools:test_Poly_pow:830 #e443501555f857aaa191 | TypeError | PolificationFailed |
| sympy.polys.tests.test_polytools:test_Poly_replace:955 #41c7a2d2813e5fa79430 | PolynomialError | SympifyError |
| sympy.polys.tests.test_polytools:test_Poly_degree:1341 #72921a7239e2973282ab | PolynomialError | PolificationFailed |
| sympy.polys.tests.test_polytools:test_Poly_coeff:1451 #eb85ce0e06dd2b7897c6 | NotImplementedError | SympifyError |
| sympy.polys.tests.test_polytools:test_Poly_nth:1473 #d16692893b21dda368f8 | ValueError | InvariantError |
| sympy.polys.tests.test_polytools:test_Poly_eval:1658 #b5834de348273cda7b12 | PolynomialError | SympifyError |
| sympy.polys.tests.test_polytools:test_Poly_eval:1684 #6b9be7699ae0021e08f8 | ValueError | SympifyError |
| sympy.polys.tests.test_polytools:test_pdiv:1798 #e854171d8f65b6dda8e0 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_pdiv:1799 #1a02b2c361b160b958a5 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_pdiv:1800 #7cfeff780cfb63e32402 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_pdiv:1801 #a87509cc75b221a1b77f | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_div:1845 #34bcd1ddfd54bfc34784 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_div:1846 #c436ae48153a405fbdc0 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_div:1847 #b178137b40769a25340b | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_gcdex:1971 #0a3f533457ce3fe546cd | DomainError | PolynomialError |
| sympy.polys.tests.test_polytools:test_subresultants:1993 #5dbaff7c4caee92e41eb | ComputationFailed | InvariantError |
| sympy.polys.tests.test_polytools:test_resultant:2020 #23acbc51ff38127ed564 | ComputationFailed | TypeError |
| sympy.polys.tests.test_polytools:test_discriminant:2046 #0de18a8e942f1fe4c20e | ComputationFailed | TypeError |
| sympy.polys.tests.test_polytools:test_gcd:2184 #00919a2477809bb85919 | TypeError | SympifyError |
| sympy.polys.tests.test_polytools:test_gcd:2185 #10fda5b6d50827a46349 | TypeError | SympifyError |
| sympy.polys.tests.test_polytools:test_compose:2380 #bd4b1b85d7bcaa3eb490 | ComputationFailed | InvariantError |
| sympy.polys.tests.test_polytools:test_compose:2381 #26bab4f79cfd346ffeeb | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_sturm:2437 #57012653102ba08538e2 | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_sqf:2519 #56c89f477d6d2598217e | ComputationFailed | PolynomialError |
| sympy.polys.tests.test_polytools:test_refine_root:2970 #8e0519d89e7345288fb1 | PolynomialError | RangeError |
| sympy.polys.tests.test_polytools:test_Poly_root:3053 #bb58ef6297ff82e54a91 | IndexError | InvariantError |
| sympy.polys.tests.test_polytools:test_real_roots:3089 #34842c67d6694f095e2a | NotImplementedError | PolynomialError |
| sympy.polys.tests.test_polytools:test_all_roots:3121 #cbc4d77c4d6341e72d51 | NotImplementedError | PolynomialError |
| sympy.polys.tests.test_polytools:test_nroots:3181 #2c8eae33c3c10217551c | MultivariatePolynomialError | PolynomialError |
| sympy.polys.tests.test_polytools:test_nth_power_roots_poly:3237 #7ddf8288782ae9433099 | MultivariatePolynomialError | PolynomialError |
| sympy.polys.tests.test_polytools:test_cancel:3315 #ac97cb40bfafdcc1c94d | ValueError | SympifyError |
| sympy.polys.tests.test_polytools:test_make_monic_over_integers_by_scaling_roots:3522 #f878e51d11b677c396eb | ValueError | PolynomialError |
| sympy.polys.tests.test_polytools:test_make_monic_over_integers_by_scaling_roots:3525 #2d1f82512f7204fdc118 | ValueError | DomainError |
| sympy.polys.tests.test_puiseux:test_puiseux_poly_div:175 #4eef0dc54654681270dd | TypeError | SympifyError |
| sympy.polys.tests.test_puiseux:test_puiseux_poly_pow:191 #a5d9ad7671546f723cc0 | TypeError | SympifyError |
| sympy.polys.tests.test_puiseux:test_puiseux_poly_pow:193 #72217e6275cf76f6d0d2 | ValueError | SympifyError |
| sympy.polys.tests.test_puiseux:test_puiseux_poly_pow:194 #4fd324c9a13a8711f235 | ValueError | SympifyError |
| sympy.polys.tests.test_ring_series:test_inversion:121 #7f0a7d10d06d2055a5c0 | ValueError | CoercionFailed |
| sympy.polys.tests.test_rings:test_PolyElement_evaluate:1170 #a7d8c8a5de1201b3266a | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_evaluate:1187 #b9e32aff81291890c797 | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_evaluate:1188 #5a4794a6bbe28e4d5ba3 | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_evaluate:1189 #d811ecb2832eea00488b | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_subs:1198 #8e9fe2f050af065f57d6 | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_subs:1208 #f286bde30230a871667b | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_subs:1209 #829855f080f37fd812ee | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_subs:1210 #795f9bf2cf0efc5e0c40 | CoercionFailed | SympifyError |
| sympy.polys.tests.test_rings:test_PolyElement_compose:1261 #ab1df7f6a183c3593e91 | CoercionFailed | TypeError |
| sympy.polys.tests.test_rootoftools:test_CRootOf___new__:85 #78e8951ee30f55f98dd8 | GeneratorsNeeded | PolynomialError |
| sympy.polys.tests.test_rootoftools:test_CRootOf___new__:86 #0d1a018ecadd81702851 | GeneratorsNeeded | PolynomialError |
| sympy.polys.tests.test_rootoftools:test_CRootOf___new__:94 #e1a4432699e07110bd44 | NotImplementedError | PolynomialError |
| sympy.polys.tests.test_rootoftools:test_CRootOf___new__:111 #da5eb7838ff03bea84b5 | NotImplementedError | PolynomialError |
| sympy.polys.tests.test_rootoftools:test_CRootOf_attributes:124 #fd07f69d5504e1c8db92 | NotImplementedError | DomainError |
| sympy.polys.tests.test_rootoftools:test_RootSum___new__:445 #3d127b2f1fd8de2e7103 | MultivariatePolynomialError | TypeError |
| sympy.polys.tests.test_rootoftools:test_RootSum___new__:446 #97f353cf0f12224961cf | ValueError | TypeError |
