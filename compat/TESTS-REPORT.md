# SymPy unit-test compatibility

Reference: SymPy 1.14.0. Independent of the doctest corpus and its ratchet.

Measured **98726** cases: **83895 exact**, **2563 equivalent**, **12268 failing**. Agreement: **87.57%**.

Compatibility suite wall time: **624.24 s**. Sum of category replay times: **888.86 s** (projects run in parallel).

Extraction wall time: **0.51 s**, 4 processes, 30 s per upstream test. Retained modules reuse established observations; their time covers loading and auditing, not re-execution.

Synchronous replay has a 30 s deadline per core/polys case and 5 s elsewhere. Deadlines remain visible as failing/inconclusive observations and are never accepted as expected exceptions. Their IDs are stored separately in the ratchet: an unfinished assertion cannot establish or resolve a correctness regression.

Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the shared doctest deserializer, adapters and equivalence rules. Exception class mismatches are accepted and counted separately; missing adapters and deserialization errors never prove an expected exception.

## Agreement by category

| Category | Measured | Exact | Equivalent | Failing | Agreement | Replay s |
|---|---:|---:|---:|---:|---:|---:|
| algebras | 128 | 123 | 0 | 5 | 96.09% | 0.93 |
| assumptions | 2220 | 1753 | 5 | 462 | 79.19% | 5.23 |
| calculus | 518 | 417 | 1 | 100 | 80.69% | 5.28 |
| categories | 312 | 312 | 0 | 0 | 100.00% | 2.83 |
| codegen | 71 | 67 | 4 | 0 | 100.00% | 1.35 |
| combinatorics | 1671 | 1632 | 0 | 39 | 97.67% | 2.74 |
| concrete | 856 | 602 | 68 | 186 | 78.27% | 10.38 |
| core | 7858 | 5516 | 185 | 2157 | 72.55% | 147.75 |
| crypto | 155 | 153 | 0 | 2 | 98.71% | 0.56 |
| diffgeom | 177 | 171 | 6 | 0 | 100.00% | 1.12 |
| discrete | 185 | 184 | 1 | 0 | 100.00% | 1.47 |
| functions | 9853 | 5838 | 1849 | 2166 | 78.02% | 66.02 |
| geometry | 1046 | 1011 | 6 | 29 | 97.23% | 20.99 |
| holonomic | 102 | 100 | 0 | 2 | 98.04% | 1.50 |
| integrals | 1313 | 841 | 45 | 427 | 67.48% | 27.65 |
| liealgebras | 87 | 81 | 1 | 5 | 94.25% | 0.10 |
| logic | 662 | 486 | 1 | 175 | 73.56% | 1.36 |
| matrices | 3930 | 3184 | 37 | 709 | 81.96% | 66.91 |
| ntheory | 44169 | 44133 | 0 | 36 | 99.92% | 18.24 |
| parsing | 772 | 653 | 68 | 51 | 93.39% | 1.17 |
| plotting | 20 | 17 | 0 | 3 | 85.00% | 0.07 |
| polys | 9484 | 6706 | 74 | 2704 | 71.49% | 128.11 |
| printing | 1767 | 1246 | 0 | 521 | 70.51% | 1.63 |
| series | 1626 | 1157 | 29 | 440 | 72.94% | 22.43 |
| sets | 1494 | 873 | 12 | 609 | 59.24% | 3.07 |
| simplify | 1402 | 1221 | 39 | 142 | 89.87% | 12.42 |
| solvers | 2381 | 1496 | 77 | 808 | 66.06% | 75.40 |
| stats | 1865 | 1758 | 41 | 66 | 96.46% | 228.99 |
| strategies | 6 | 5 | 0 | 1 | 83.33% | 0.01 |
| tensor | 1593 | 1254 | 1 | 338 | 78.78% | 5.56 |
| unify | 8 | 1 | 0 | 7 | 12.50% | 0.01 |
| utilities | 375 | 311 | 9 | 55 | 85.33% | 21.45 |
| vector | 620 | 593 | 4 | 23 | 96.29% | 6.14 |

## Extraction audit

Executed loop instances count individually. Duplicates count as omissions; never-reached sites count once. Partial observations from timed-out upstream tests are discarded. Detailed source locations and test statuses are in each category audit file.

| Category | Source sites | Examined | Cases | Omitted | Wall s | Retained modules |
|---|---:|---:|---:|---:|---:|---:|
| algebras | 123 | 138 | 128 | 10 | 1.90 | 0 |
| assumptions | 2186 | 2636 | 2220 | 416 | 26.26 | 0 |
| calculus | 541 | 617 | 518 | 99 | 9.97 | 0 |
| categories | 372 | 372 | 312 | 60 | 4.69 | 0 |
| codegen | 71 | 71 | 71 | 0 | 0.20 | 0 |
| combinatorics | 1265 | 3530 | 1671 | 1859 | 1.86 | 21 |
| concrete | 1001 | 1095 | 856 | 239 | 29.71 | 0 |
| core | 9329 | 25605 | 7858 | 17747 | 6.50 | 40 |
| crypto | 185 | 5078 | 155 | 4923 | 1.98 | 0 |
| diffgeom | 205 | 205 | 177 | 28 | 11.22 | 0 |
| discrete | 198 | 198 | 185 | 13 | 2.82 | 0 |
| functions | 7116 | 23611 | 9853 | 13758 | 118.91 | 0 |
| geometry | 1410 | 1514 | 1046 | 468 | 51.94 | 0 |
| holonomic | 190 | 217 | 102 | 115 | 17.87 | 0 |
| integrals | 2261 | 2444 | 1313 | 1131 | 3.96 | 16 |
| liealgebras | 95 | 95 | 87 | 8 | 0.50 | 0 |
| logic | 944 | 8596 | 662 | 7934 | 8.50 | 0 |
| matrices | 4686 | 7002 | 3930 | 3072 | 76.67 | 0 |
| ntheory | 1039 | 601899 | 44169 | 557730 | 108.99 | 0 |
| parsing | 286 | 2072 | 772 | 1300 | 24.57 | 0 |
| plotting | 1033 | 1139 | 20 | 1119 | 5.97 | 0 |
| polys | 10731 | 29644 | 9484 | 20160 | 17.55 | 67 |
| printing | 4068 | 4706 | 1767 | 2939 | 44.06 | 0 |
| series | 1960 | 2027 | 1626 | 401 | 103.33 | 0 |
| sets | 1768 | 6442 | 1494 | 4948 | 6.41 | 0 |
| simplify | 1852 | 2254 | 1402 | 852 | 37.67 | 0 |
| solvers | 3696 | 8472 | 2381 | 6091 | 347.98 | 0 |
| stats | 1582 | 2363 | 1865 | 498 | 89.05 | 0 |
| strategies | 103 | 105 | 6 | 99 | 0.38 | 0 |
| tensor | 2070 | 2764 | 1593 | 1171 | 4.38 | 21 |
| unify | 63 | 63 | 8 | 55 | 0.40 | 0 |
| utilities | 1163 | 25623 | 375 | 25248 | 39.10 | 0 |
| vector | 768 | 776 | 620 | 156 | 31.10 | 0 |

| Category | Omission reason | Count |
|---|---|---:|
| algebras | marked-slow | 1 |
| algebras | non-call-expression | 5 |
| algebras | not-executed | 1 |
| algebras | private-api | 2 |
| algebras | unsupported-assertion | 1 |
| assumptions | duplicate | 316 |
| assumptions | marked-slow | 2 |
| assumptions | marked-xfail | 25 |
| assumptions | non-boolean-assertion | 22 |
| assumptions | non-call-expression | 4 |
| assumptions | not-executed | 3 |
| assumptions | not-exported-api | 31 |
| assumptions | unserializable-input | 6 |
| assumptions | unsupported-assertion | 7 |
| calculus | duplicate | 43 |
| calculus | marked-slow | 1 |
| calculus | marked-xfail | 5 |
| calculus | non-boolean-assertion | 1 |
| calculus | non-call-expression | 4 |
| calculus | not-executed | 2 |
| calculus | not-exported-api | 4 |
| calculus | stateful-iterator-input | 2 |
| calculus | unsupported-assertion | 37 |
| categories | non-call-expression | 14 |
| categories | not-exported-api | 11 |
| categories | unserializable-input | 32 |
| categories | unsupported-assertion | 3 |
| combinatorics | duplicate | 488 |
| combinatorics | marked-slow | 21 |
| combinatorics | marked-xfail | 6 |
| combinatorics | non-boolean-assertion | 10 |
| combinatorics | non-call-expression | 565 |
| combinatorics | not-executed | 1 |
| combinatorics | not-exported-api | 607 |
| combinatorics | private-api | 18 |
| combinatorics | python-runtime-api | 22 |
| combinatorics | stateful-iterator-input | 23 |
| combinatorics | test-timeout | 7 |
| combinatorics | unserializable-input | 14 |
| combinatorics | unstable-result-representation | 14 |
| combinatorics | unsupported-assertion | 63 |
| concrete | duplicate | 7 |
| concrete | marked-slow | 55 |
| concrete | marked-xfail | 4 |
| concrete | non-call-expression | 50 |
| concrete | not-exported-api | 71 |
| concrete | reference-exception | 2 |
| concrete | stateful-iterator-input | 1 |
| concrete | unserializable-input | 3 |
| concrete | unsupported-assertion | 46 |
| core | duplicate | 579 |
| core | marked-skip | 11 |
| core | marked-xfail | 47 |
| core | non-boolean-assertion | 22 |
| core | non-call-expression | 11791 |
| core | not-executed | 27 |
| core | not-exported-api | 2176 |
| core | optional-dependency | 82 |
| core | private-api | 50 |
| core | python-runtime-api | 260 |
| core | serialization-error | 17 |
| core | stateful-iterator-input | 76 |
| core | test-utility | 32 |
| core | unserializable-input | 867 |
| core | unsupported-assertion | 1704 |
| core | unsupported-raises | 6 |
| crypto | non-call-expression | 4919 |
| crypto | python-runtime-api | 1 |
| crypto | stateful-iterator-input | 1 |
| crypto | unsupported-assertion | 2 |
| diffgeom | non-call-expression | 13 |
| diffgeom | not-executed | 1 |
| diffgeom | not-exported-api | 4 |
| diffgeom | stateful-iterator-input | 2 |
| diffgeom | unsupported-assertion | 8 |
| discrete | non-boolean-assertion | 2 |
| discrete | stateful-iterator-input | 8 |
| discrete | unsupported-assertion | 3 |
| functions | duplicate | 7857 |
| functions | marked-slow | 104 |
| functions | marked-xfail | 18 |
| functions | non-boolean-assertion | 5 |
| functions | non-call-expression | 230 |
| functions | not-executed | 6 |
| functions | not-exported-api | 2768 |
| functions | optional-dependency | 1 |
| functions | private-api | 146 |
| functions | python-runtime-api | 1 |
| functions | stateful-iterator-input | 58 |
| functions | test-utility | 87 |
| functions | unserializable-input | 16 |
| functions | unsupported-assertion | 2461 |
| geometry | duplicate | 8 |
| geometry | marked-slow | 301 |
| geometry | non-boolean-assertion | 2 |
| geometry | non-call-expression | 53 |
| geometry | not-exported-api | 11 |
| geometry | private-api | 13 |
| geometry | python-runtime-api | 12 |
| geometry | stateful-iterator-input | 2 |
| geometry | test-utility | 1 |
| geometry | unsupported-assertion | 65 |
| holonomic | non-call-expression | 115 |
| integrals | duplicate | 63 |
| integrals | marked-slow | 607 |
| integrals | marked-tooslow | 1 |
| integrals | marked-xfail | 38 |
| integrals | non-boolean-assertion | 2 |
| integrals | non-call-expression | 86 |
| integrals | not-executed | 1 |
| integrals | not-exported-api | 70 |
| integrals | private-api | 1 |
| integrals | test-utility | 10 |
| integrals | unserializable-input | 188 |
| integrals | unsupported-assertion | 64 |
| liealgebras | non-call-expression | 8 |
| logic | duplicate | 40 |
| logic | marked-xfail | 18 |
| logic | non-boolean-assertion | 10 |
| logic | non-call-expression | 7347 |
| logic | not-executed | 6 |
| logic | not-exported-api | 53 |
| logic | python-runtime-api | 5 |
| logic | stateful-iterator-input | 19 |
| logic | unserializable-input | 26 |
| logic | unsupported-assertion | 394 |
| logic | unsupported-raises | 2 |
| logic | upstream-skip | 14 |
| matrices | duplicate | 368 |
| matrices | marked-slow | 52 |
| matrices | marked-xfail | 15 |
| matrices | non-boolean-assertion | 26 |
| matrices | non-call-expression | 1220 |
| matrices | not-executed | 32 |
| matrices | not-exported-api | 404 |
| matrices | optional-dependency | 40 |
| matrices | private-api | 21 |
| matrices | python-runtime-api | 3 |
| matrices | stateful-iterator-input | 73 |
| matrices | unserializable-input | 327 |
| matrices | unsupported-assertion | 487 |
| matrices | unsupported-raises | 4 |
| ntheory | duplicate | 10 |
| ntheory | marked-slow | 98 |
| ntheory | non-boolean-assertion | 3104 |
| ntheory | non-call-expression | 54281 |
| ntheory | not-exported-api | 463131 |
| ntheory | optional-dependency | 4 |
| ntheory | private-api | 6 |
| ntheory | python-runtime-api | 35499 |
| ntheory | serialization-error | 7 |
| ntheory | stateful-iterator-input | 67 |
| ntheory | test-timeout | 41 |
| ntheory | unserializable-input | 9 |
| ntheory | unsupported-assertion | 1471 |
| ntheory | unsupported-raises | 2 |
| parsing | duplicate | 10 |
| parsing | marked-xfail | 3 |
| parsing | non-call-expression | 1026 |
| parsing | not-executed | 1 |
| parsing | not-exported-api | 136 |
| parsing | private-api | 4 |
| parsing | python-runtime-api | 12 |
| parsing | test-exception:RecursionError | 1 |
| parsing | unserializable-input | 65 |
| parsing | unsupported-assertion | 40 |
| parsing | unsupported-raises | 2 |
| plotting | marked-xfail | 2 |
| plotting | non-boolean-assertion | 52 |
| plotting | non-call-expression | 103 |
| plotting | not-executed | 1 |
| plotting | not-exported-api | 220 |
| plotting | optional-dependency | 327 |
| plotting | stateful-iterator-input | 10 |
| plotting | unserializable-input | 366 |
| plotting | unsupported-assertion | 38 |
| polys | duplicate | 125 |
| polys | marked-slow | 74 |
| polys | marked-tooslow | 2 |
| polys | marked-xfail | 10 |
| polys | non-boolean-assertion | 52 |
| polys | non-call-expression | 15891 |
| polys | not-executed | 17 |
| polys | not-exported-api | 1105 |
| polys | optional-dependency | 291 |
| polys | private-api | 33 |
| polys | python-runtime-api | 692 |
| polys | serialization-error | 319 |
| polys | stateful-iterator-input | 137 |
| polys | test-exception:TypeError | 2 |
| polys | test-utility | 50 |
| polys | unserializable-input | 350 |
| polys | unsupported-assertion | 1009 |
| polys | unsupported-raises | 1 |
| printing | duplicate | 269 |
| printing | marked-xfail | 8 |
| printing | non-boolean-assertion | 1 |
| printing | non-call-expression | 27 |
| printing | not-executed | 9 |
| printing | not-exported-api | 1766 |
| printing | optional-dependency | 5 |
| printing | private-api | 3 |
| printing | python-runtime-api | 237 |
| printing | reference-exception | 1 |
| printing | serialization-error | 5 |
| printing | stateful-iterator-input | 9 |
| printing | test-timeout | 2 |
| printing | unserializable-input | 451 |
| printing | unsupported-assertion | 146 |
| series | duplicate | 4 |
| series | marked-slow | 71 |
| series | marked-xfail | 22 |
| series | non-call-expression | 47 |
| series | not-executed | 2 |
| series | not-exported-api | 68 |
| series | private-api | 11 |
| series | stateful-iterator-input | 31 |
| series | unserializable-input | 42 |
| series | unsupported-assertion | 99 |
| series | upstream-skip | 4 |
| sets | duplicate | 160 |
| sets | marked-xfail | 21 |
| sets | non-boolean-assertion | 6 |
| sets | non-call-expression | 3425 |
| sets | not-executed | 2 |
| sets | not-exported-api | 828 |
| sets | private-api | 10 |
| sets | python-runtime-api | 5 |
| sets | stateful-iterator-input | 38 |
| sets | unserializable-input | 18 |
| sets | unsupported-assertion | 414 |
| sets | unsupported-raises | 21 |
| simplify | duplicate | 61 |
| simplify | marked-slow | 103 |
| simplify | marked-tooslow | 1 |
| simplify | marked-xfail | 101 |
| simplify | non-boolean-assertion | 3 |
| simplify | non-call-expression | 218 |
| simplify | not-executed | 3 |
| simplify | not-exported-api | 155 |
| simplify | private-api | 8 |
| simplify | serialization-error | 1 |
| simplify | stateful-iterator-input | 82 |
| simplify | test-utility | 58 |
| simplify | unserializable-input | 14 |
| simplify | unsupported-assertion | 44 |
| solvers | duplicate | 67 |
| solvers | marked-skip | 2 |
| solvers | marked-slow | 421 |
| solvers | marked-tooslow | 5 |
| solvers | marked-xfail | 78 |
| solvers | non-boolean-assertion | 33 |
| solvers | non-call-expression | 253 |
| solvers | not-executed | 14 |
| solvers | not-exported-api | 2871 |
| solvers | private-api | 9 |
| solvers | python-runtime-api | 39 |
| solvers | stateful-iterator-input | 2136 |
| solvers | test-timeout | 11 |
| solvers | test-utility | 14 |
| solvers | unserializable-input | 7 |
| solvers | unsupported-assertion | 129 |
| solvers | upstream-skip | 2 |
| stats | marked-slow | 46 |
| stats | marked-xfail | 6 |
| stats | non-boolean-assertion | 10 |
| stats | non-call-expression | 89 |
| stats | not-executed | 4 |
| stats | not-exported-api | 122 |
| stats | optional-dependency | 48 |
| stats | stateful-iterator-input | 6 |
| stats | test-utility | 56 |
| stats | unserializable-input | 6 |
| stats | unsupported-assertion | 101 |
| stats | upstream-skip | 4 |
| strategies | non-call-expression | 3 |
| strategies | not-exported-api | 55 |
| strategies | stateful-iterator-input | 31 |
| strategies | unserializable-input | 3 |
| strategies | unstable-result-representation | 1 |
| strategies | unsupported-assertion | 6 |
| tensor | marked-xfail | 4 |
| tensor | non-boolean-assertion | 2 |
| tensor | non-call-expression | 411 |
| tensor | not-executed | 1 |
| tensor | not-exported-api | 370 |
| tensor | private-api | 79 |
| tensor | python-runtime-api | 2 |
| tensor | stateful-iterator-input | 22 |
| tensor | test-timeout | 97 |
| tensor | unserializable-input | 147 |
| tensor | unsupported-assertion | 36 |
| unify | non-boolean-assertion | 4 |
| unify | non-call-expression | 2 |
| unify | not-executed | 2 |
| unify | not-exported-api | 3 |
| unify | stateful-iterator-input | 36 |
| unify | unserializable-input | 6 |
| unify | unsupported-assertion | 2 |
| utilities | marked-skip | 3 |
| utilities | marked-slow | 5 |
| utilities | marked-xfail | 104 |
| utilities | non-call-expression | 224 |
| utilities | not-executed | 6 |
| utilities | not-exported-api | 24276 |
| utilities | optional-dependency | 125 |
| utilities | python-runtime-api | 6 |
| utilities | stateful-iterator-input | 158 |
| utilities | test-utility | 2 |
| utilities | unserializable-input | 24 |
| utilities | unsupported-assertion | 313 |
| utilities | unsupported-raises | 2 |
| vector | duplicate | 8 |
| vector | marked-xfail | 12 |
| vector | non-call-expression | 23 |
| vector | not-exported-api | 49 |
| vector | private-api | 13 |
| vector | unserializable-input | 1 |
| vector | unsupported-assertion | 50 |

| Category | Test execution status | Count |
|---|---|---:|
| algebras | completed | 18 |
| algebras | marked-slow | 2 |
| assumptions | completed | 146 |
| assumptions | marked-slow | 1 |
| assumptions | marked-xfail | 10 |
| calculus | completed | 42 |
| calculus | marked-slow | 1 |
| calculus | marked-xfail | 4 |
| categories | completed | 12 |
| codegen | completed | 10 |
| combinatorics | completed | 168 |
| combinatorics | marked-slow | 3 |
| combinatorics | marked-xfail | 3 |
| combinatorics | test-timeout | 1 |
| concrete | completed | 155 |
| concrete | marked-slow | 3 |
| concrete | marked-xfail | 2 |
| core | completed | 1960 |
| core | marked-skip | 71 |
| core | marked-xfail | 24 |
| core | optional-dependency | 10 |
| core | test-exception:Failed | 1 |
| crypto | completed | 51 |
| diffgeom | completed | 24 |
| discrete | completed | 14 |
| functions | completed | 542 |
| functions | marked-slow | 14 |
| functions | marked-xfail | 8 |
| functions | optional-dependency | 1 |
| geometry | completed | 113 |
| geometry | marked-slow | 4 |
| holonomic | completed | 32 |
| integrals | completed | 413 |
| integrals | marked-slow | 36 |
| integrals | marked-tooslow | 1 |
| integrals | marked-xfail | 36 |
| liealgebras | completed | 12 |
| logic | completed | 119 |
| logic | marked-slow | 1 |
| logic | marked-xfail | 4 |
| logic | upstream-skip | 3 |
| matrices | completed | 973 |
| matrices | marked-slow | 6 |
| matrices | marked-xfail | 9 |
| matrices | optional-dependency | 12 |
| ntheory | completed | 81 |
| ntheory | marked-slow | 4 |
| ntheory | optional-dependency | 3 |
| ntheory | test-timeout | 2 |
| parsing | completed | 60 |
| parsing | marked-xfail | 3 |
| parsing | test-exception:RecursionError | 2 |
| plotting | completed | 87 |
| plotting | marked-xfail | 3 |
| plotting | optional-dependency | 32 |
| polys | completed | 2208 |
| polys | marked-slow | 6 |
| polys | marked-tooslow | 2 |
| polys | marked-xfail | 4 |
| polys | optional-dependency | 22 |
| polys | test-exception:TypeError | 1 |
| polys | upstream-skip | 62 |
| printing | completed | 614 |
| printing | marked-xfail | 5 |
| printing | optional-dependency | 2 |
| printing | test-exception:NameError | 1 |
| printing | test-timeout | 1 |
| series | completed | 470 |
| series | marked-slow | 5 |
| series | marked-xfail | 12 |
| series | upstream-skip | 2 |
| sets | completed | 216 |
| sets | marked-xfail | 8 |
| simplify | completed | 303 |
| simplify | marked-slow | 14 |
| simplify | marked-tooslow | 1 |
| simplify | marked-xfail | 17 |
| solvers | completed | 542 |
| solvers | marked-skip | 2 |
| solvers | marked-slow | 53 |
| solvers | marked-tooslow | 6 |
| solvers | marked-xfail | 31 |
| solvers | test-timeout | 1 |
| solvers | upstream-skip | 1 |
| stats | completed | 203 |
| stats | marked-slow | 6 |
| stats | marked-xfail | 4 |
| stats | optional-dependency | 10 |
| stats | upstream-skip | 2 |
| strategies | completed | 50 |
| tensor | completed | 233 |
| tensor | marked-xfail | 1 |
| tensor | test-timeout | 5 |
| unify | completed | 33 |
| utilities | completed | 395 |
| utilities | marked-skip | 3 |
| utilities | marked-slow | 5 |
| utilities | marked-xfail | 147 |
| utilities | optional-dependency | 69 |
| vector | completed | 65 |
| vector | marked-xfail | 2 |

## Main failure groups

| Category | Kind | Count |
|---|---|---:|
| algebras | unexpected exception | 2 |
| algebras | wrong result | 3 |
| algebras | exception class mismatch (accepted) | 0 |
| assumptions | input conversion exception | 11 |
| assumptions | missing API/adapter | 40 |
| assumptions | unexpected exception | 3 |
| assumptions | unsupported value/input type | 10 |
| assumptions | wrong result | 398 |
| assumptions | exception class mismatch (accepted) | 1 |
| calculus | exception not raised | 14 |
| calculus | input conversion exception | 11 |
| calculus | missing API/adapter | 3 |
| calculus | unexpected exception | 16 |
| calculus | wrong result | 56 |
| calculus | exception class mismatch (accepted) | 15 |
| categories | exception class mismatch (accepted) | 5 |
| codegen | exception class mismatch (accepted) | 0 |
| combinatorics | exception not raised | 1 |
| combinatorics | missing API/adapter | 5 |
| combinatorics | result comparison exception | 1 |
| combinatorics | unexpected exception | 5 |
| combinatorics | unsupported value/input type | 4 |
| combinatorics | wrong result | 23 |
| combinatorics | exception class mismatch (accepted) | 8 |
| concrete | exception not raised | 12 |
| concrete | input conversion exception | 1 |
| concrete | missing API/adapter | 44 |
| concrete | replay timeout | 1 |
| concrete | result comparison exception | 3 |
| concrete | unexpected exception | 21 |
| concrete | wrong result | 104 |
| concrete | exception class mismatch (accepted) | 12 |
| core | exception not raised | 295 |
| core | input conversion exception | 24 |
| core | missing API/adapter | 560 |
| core | result comparison exception | 14 |
| core | unexpected exception | 256 |
| core | unsupported value/input type | 65 |
| core | wrong result | 943 |
| core | exception class mismatch (accepted) | 102 |
| crypto | wrong result | 2 |
| crypto | exception class mismatch (accepted) | 1 |
| diffgeom | exception class mismatch (accepted) | 0 |
| discrete | exception class mismatch (accepted) | 0 |
| functions | exception not raised | 75 |
| functions | input conversion exception | 2 |
| functions | missing API/adapter | 416 |
| functions | replay timeout | 4 |
| functions | unexpected exception | 284 |
| functions | unsupported value/input type | 50 |
| functions | wrong result | 1335 |
| functions | exception class mismatch (accepted) | 99 |
| geometry | exception not raised | 3 |
| geometry | input conversion exception | 3 |
| geometry | missing API/adapter | 3 |
| geometry | replay timeout | 1 |
| geometry | result comparison exception | 1 |
| geometry | unexpected exception | 4 |
| geometry | wrong result | 14 |
| geometry | exception class mismatch (accepted) | 6 |
| holonomic | wrong result | 2 |
| holonomic | exception class mismatch (accepted) | 0 |
| integrals | exception not raised | 14 |
| integrals | input conversion exception | 1 |
| integrals | missing API/adapter | 71 |
| integrals | replay timeout | 2 |
| integrals | result comparison exception | 1 |
| integrals | unexpected exception | 43 |
| integrals | unsupported value/input type | 5 |
| integrals | wrong result | 290 |
| integrals | exception class mismatch (accepted) | 6 |
| liealgebras | wrong result | 5 |
| liealgebras | exception class mismatch (accepted) | 0 |
| logic | exception not raised | 3 |
| logic | input conversion exception | 13 |
| logic | missing API/adapter | 61 |
| logic | unexpected exception | 14 |
| logic | wrong result | 84 |
| logic | exception class mismatch (accepted) | 35 |
| matrices | exception not raised | 105 |
| matrices | input conversion exception | 2 |
| matrices | missing API/adapter | 92 |
| matrices | replay timeout | 8 |
| matrices | result comparison exception | 16 |
| matrices | unexpected exception | 230 |
| matrices | unsupported value/input type | 30 |
| matrices | wrong result | 226 |
| matrices | exception class mismatch (accepted) | 118 |
| ntheory | exception not raised | 2 |
| ntheory | missing API/adapter | 10 |
| ntheory | replay timeout | 1 |
| ntheory | unexpected exception | 6 |
| ntheory | unsupported value/input type | 10 |
| ntheory | wrong result | 7 |
| ntheory | exception class mismatch (accepted) | 8 |
| parsing | exception not raised | 17 |
| parsing | unexpected exception | 18 |
| parsing | wrong result | 16 |
| parsing | exception class mismatch (accepted) | 16 |
| plotting | exception not raised | 2 |
| plotting | wrong result | 1 |
| plotting | exception class mismatch (accepted) | 8 |
| polys | exception not raised | 81 |
| polys | input conversion exception | 22 |
| polys | missing API/adapter | 901 |
| polys | replay timeout | 2 |
| polys | result comparison exception | 8 |
| polys | unexpected exception | 1113 |
| polys | unsupported value/input type | 283 |
| polys | wrong result | 294 |
| polys | exception class mismatch (accepted) | 128 |
| printing | exception not raised | 5 |
| printing | input conversion exception | 7 |
| printing | missing API/adapter | 65 |
| printing | unexpected exception | 117 |
| printing | unsupported value/input type | 26 |
| printing | wrong result | 301 |
| printing | exception class mismatch (accepted) | 2 |
| series | exception not raised | 25 |
| series | missing API/adapter | 85 |
| series | result comparison exception | 1 |
| series | unexpected exception | 133 |
| series | unsupported value/input type | 2 |
| series | wrong result | 194 |
| series | exception class mismatch (accepted) | 14 |
| sets | exception not raised | 33 |
| sets | input conversion exception | 1 |
| sets | missing API/adapter | 51 |
| sets | result comparison exception | 13 |
| sets | unexpected exception | 63 |
| sets | unsupported value/input type | 13 |
| sets | wrong result | 435 |
| sets | exception class mismatch (accepted) | 10 |
| simplify | exception not raised | 1 |
| simplify | missing API/adapter | 27 |
| simplify | unexpected exception | 20 |
| simplify | unsupported value/input type | 6 |
| simplify | wrong result | 88 |
| simplify | exception class mismatch (accepted) | 2 |
| solvers | exception not raised | 69 |
| solvers | input conversion exception | 19 |
| solvers | missing API/adapter | 124 |
| solvers | replay timeout | 4 |
| solvers | unexpected exception | 271 |
| solvers | unsupported value/input type | 4 |
| solvers | wrong result | 317 |
| solvers | exception class mismatch (accepted) | 53 |
| stats | exception not raised | 3 |
| stats | input conversion exception | 2 |
| stats | missing API/adapter | 4 |
| stats | replay timeout | 28 |
| stats | unexpected exception | 5 |
| stats | unsupported value/input type | 4 |
| stats | wrong result | 20 |
| stats | exception class mismatch (accepted) | 8 |
| strategies | missing API/adapter | 1 |
| strategies | exception class mismatch (accepted) | 0 |
| tensor | exception not raised | 3 |
| tensor | input conversion exception | 2 |
| tensor | missing API/adapter | 185 |
| tensor | unexpected exception | 22 |
| tensor | unsupported value/input type | 3 |
| tensor | wrong result | 123 |
| tensor | exception class mismatch (accepted) | 21 |
| unify | missing API/adapter | 7 |
| unify | exception class mismatch (accepted) | 0 |
| utilities | missing API/adapter | 13 |
| utilities | replay timeout | 2 |
| utilities | unexpected exception | 17 |
| utilities | wrong result | 23 |
| utilities | exception class mismatch (accepted) | 15 |
| vector | missing API/adapter | 8 |
| vector | unexpected exception | 4 |
| vector | wrong result | 11 |
| vector | exception class mismatch (accepted) | 4 |

## Most frequent failing APIs per category

| Category | API and outcome | Cases |
|---|---|---:|
| algebras | .__mul__ (fail) | 2 |
| algebras | .__add__ (fail) | 1 |
| algebras | .pow (error) | 1 |
| algebras | trigsimp (error) | 1 |
| assumptions | ask (fail) | 358 |
| assumptions | refine (fail) | 40 |
| assumptions | lra_satask (unsupported) | 39 |
| assumptions | ask (error) | 12 |
| assumptions | ask (unsupported) | 10 |
| assumptions | pretty (error) | 1 |
| assumptions | .handler (unsupported) | 1 |
| assumptions | .is_positive (error) | 1 |
| calculus | .__pow__ (fail) | 17 |
| calculus | .__truediv__ (fail) | 10 |
| calculus | periodicity (fail) | 9 |
| calculus | not_empty_in (error) | 7 |
| calculus | continuous_domain (fail) | 6 |
| calculus | .__sub__ (fail) | 5 |
| calculus | .__add__ (fail) | 3 |
| calculus | AccumulationBounds (unsupported) | 3 |
| calculus | .__mul__ (fail) | 3 |
| calculus | unchanged (error) | 3 |
| combinatorics | .P (fail) | 10 |
| combinatorics | srepr (fail) | 6 |
| combinatorics | sstr (fail) | 4 |
| combinatorics | unchanged (error) | 4 |
| combinatorics | .is_alt_sym (unsupported) | 2 |
| combinatorics | .from_inversion_vector (unsupported) | 2 |
| combinatorics | .__add__ (unsupported) | 1 |
| combinatorics | rubik (unsupported) | 1 |
| combinatorics | get_subset_from_bitstring (error) | 1 |
| combinatorics | .__gt__ (fail) | 1 |
| concrete | eval_sum_residue (unsupported) | 27 |
| concrete | .doit (fail) | 16 |
| concrete | summation (fail) | 12 |
| concrete | .is_nonpositive (unsupported) | 12 |
| concrete | .is_finite (fail) | 11 |
| concrete | .free_symbols (fail) | 8 |
| concrete | Sum (error) | 7 |
| concrete | Sum (fail) | 7 |
| concrete | .expand (fail) | 7 |
| concrete | Product (fail) | 6 |
| core | .is_nonpositive (unsupported) | 117 |
| core | .subs (fail) | 86 |
| core | .is_even (unsupported) | 59 |
| core | .diff (fail) | 59 |
| core | .is_odd (unsupported) | 55 |
| core | .reversedsign (unsupported) | 51 |
| core | .matches (fail) | 50 |
| core | .is_positive (fail) | 49 |
| core | .is_imaginary (unsupported) | 47 |
| core | .is_nonnegative (fail) | 42 |
| crypto | lfsr_sequence (fail) | 2 |
| functions | .rewrite (fail) | 234 |
| functions | .is_real (fail) | 159 |
| functions | .as_leading_term (error) | 128 |
| functions | .is_even (unsupported) | 116 |
| functions | .is_odd (unsupported) | 115 |
| functions | .is_rational (fail) | 104 |
| functions | .series (error) | 71 |
| functions | .is_algebraic (fail) | 58 |
| functions | .as_leading_term (fail) | 57 |
| functions | .expand (fail) | 47 |
| geometry | Intersection (fail) | 5 |
| geometry | Union (fail) | 3 |
| geometry | .__call__ (unsupported) | 2 |
| geometry | .subs (fail) | 2 |
| geometry | Intersection (error) | 2 |
| geometry | .is_nonzero (fail) | 2 |
| geometry | .__mul__ (fail) | 2 |
| geometry | .arbitrary_point (fail) | 1 |
| geometry | .is_tangent (error) | 1 |
| geometry | .__contains__ (error) | 1 |
| holonomic | .rewrite (fail) | 1 |
| holonomic | .expand (fail) | 1 |
| integrals | integrate (fail) | 147 |
| integrals | manualintegrate (fail) | 81 |
| integrals | integrate (error) | 20 |
| integrals | decompose (error) | 14 |
| integrals | heurisch (fail) | 12 |
| integrals | risch_integrate (unsupported) | 11 |
| integrals | order_at (unsupported) | 10 |
| integrals | .is_zero (fail) | 7 |
| integrals | best_origin (unsupported) | 7 |
| integrals | .as_sum (fail) | 5 |
| liealgebras | .basis (fail) | 3 |
| liealgebras | .cartan_type (fail) | 1 |
| liealgebras | .lie_algebra (fail) | 1 |
| logic | .simplify (fail) | 26 |
| logic | refine (fail) | 13 |
| logic | .__mod__ (unsupported) | 12 |
| logic | .binary_symbols (fail) | 9 |
| logic | simplify (fail) | 8 |
| logic | ITE (error) | 8 |
| logic | .is_Boolean (unsupported) | 6 |
| logic | .__add__ (unsupported) | 6 |
| logic | .__sub__ (unsupported) | 6 |
| logic | .__mul__ (unsupported) | 6 |
| matrices | .diff (fail) | 71 |
| matrices | simplify (error) | 60 |
| matrices | .__pow__ (error) | 38 |
| matrices | .__getitem__ (error) | 23 |
| matrices | MutableDenseMatrix (fail) | 18 |
| matrices | .from_index_summation (error) | 18 |
| matrices | .is_echelon (unsupported) | 18 |
| matrices | .is_Identity (unsupported) | 18 |
| matrices | .diff (error) | 17 |
| matrices | .kind (unsupported) | 14 |
| ntheory | smoothness_p (unsupported) | 10 |
| ntheory | is_extra_strong_lucas_prp (unsupported) | 6 |
| ntheory | factorint (fail) | 4 |
| ntheory | smoothness_p (error) | 4 |
| ntheory | primorial (fail) | 3 |
| ntheory | is_fermat_pseudoprime (unsupported) | 2 |
| ntheory | is_euler_jacobi_pseudoprime (unsupported) | 2 |
| ntheory | totient (fail) | 1 |
| ntheory | is_nthpow_residue (error) | 1 |
| ntheory | nthroot_mod (error) | 1 |
| parsing | parse_expr (fail) | 31 |
| parsing | parse_expr (error) | 18 |
| parsing | parse_latex_lark (fail) | 2 |
| plotting | intervalMembership (fail) | 1 |
| plotting | interval (fail) | 1 |
| plotting | .has (fail) | 1 |
| polys | .__mul__ (error) | 635 |
| polys | .dup_count_complex_roots (unsupported) | 105 |
| polys | .rep (unsupported) | 88 |
| polys | .dup_isolate_real_roots_sqf (unsupported) | 76 |
| polys | groebner (error) | 56 |
| polys | dict_from_expr (unsupported) | 37 |
| polys | .dup_refine_real_root (unsupported) | 35 |
| polys | .dup_isolate_real_roots (unsupported) | 32 |
| polys | .from_poly (unsupported) | 28 |
| polys | is_isomorphism_possible (unsupported) | 28 |
| printing | latex (fail) | 151 |
| printing | latex (error) | 108 |
| printing | mathml (fail) | 88 |
| printing | srepr (fail) | 39 |
| printing | precedence (unsupported) | 28 |
| printing | sstr (fail) | 23 |
| printing | latex (unsupported) | 22 |
| printing | requires_partial (unsupported) | 21 |
| printing | sstr (error) | 9 |
| printing | pretty (error) | 6 |
| series | .nseries (error) | 73 |
| series | gruntz (unsupported) | 41 |
| series | compare (fail) | 35 |
| series | .__add__ (fail) | 34 |
| series | limit (fail) | 32 |
| series | .series (error) | 31 |
| series | Order (fail) | 31 |
| series | .function (unsupported) | 16 |
| series | rational_algorithm (unsupported) | 15 |
| series | .subs (fail) | 15 |
| sets | .intersect (fail) | 172 |
| sets | .__pow__ (fail) | 31 |
| sets | .__truediv__ (fail) | 29 |
| sets | .is_finite_set (unsupported) | 25 |
| sets | .is_iterable (fail) | 23 |
| sets | .__mul__ (fail) | 21 |
| sets | Intersection (fail) | 20 |
| sets | .is_subset (fail) | 15 |
| sets | .__sub__ (fail) | 14 |
| sets | .contains (fail) | 12 |
| simplify | simplify (fail) | 25 |
| simplify | .simplify (fail) | 11 |
| simplify | simplify (error) | 10 |
| simplify | hyperexpand (fail) | 10 |
| simplify | collect (fail) | 9 |
| simplify | cancel (fail) | 8 |
| simplify | preprocess_for_cse (unsupported) | 5 |
| simplify | postprocess_for_cse (unsupported) | 5 |
| simplify | separatevars (fail) | 5 |
| simplify | besselsimp (fail) | 5 |
| solvers | solve (error) | 127 |
| solvers | solveset (fail) | 76 |
| solvers | solve (fail) | 57 |
| solvers | solveset_real (fail) | 46 |
| solvers | linodesolve (unsupported) | 37 |
| solvers | nonlinsolve (error) | 31 |
| solvers | dsolve (error) | 28 |
| solvers | classify_ode (fail) | 27 |
| solvers | solveset_complex (unsupported) | 24 |
| solvers | matrix_exp (fail) | 18 |
| stats | skewness (error) | 10 |
| stats | kurtosis (error) | 10 |
| stats | .dummy_eq (fail) | 8 |
| stats | variance (error) | 5 |
| stats | .__getitem__ (unsupported) | 4 |
| stats | median (fail) | 3 |
| stats | expectation (error) | 3 |
| stats | probability (fail) | 2 |
| stats | variance (fail) | 2 |
| stats | .__call__ (error) | 2 |
| strategies | treeapply (unsupported) | 1 |
| tensor | .__getitem__ (unsupported) | 106 |
| tensor | convert_array_to_matrix (fail) | 38 |
| tensor | .data (unsupported) | 29 |
| tensor | .func (unsupported) | 16 |
| tensor | .__call__ (unsupported) | 13 |
| tensor | .doit (fail) | 11 |
| tensor | .split_multiple_contractions (unsupported) | 10 |
| tensor | convert_matrix_to_array (fail) | 8 |
| tensor | .diff (fail) | 7 |
| tensor | .replace (error) | 7 |
| unify | deconstruct (unsupported) | 7 |
| utilities | ordinal (unsupported) | 11 |
| utilities | simplify (error) | 4 |
| utilities | integrate (fail) | 4 |
| utilities | solve (error) | 3 |
| utilities | .invert (error) | 2 |
| utilities | solveset (fail) | 2 |
| utilities | solveset_real (fail) | 2 |
| utilities | .series (error) | 2 |
| utilities | .__or__ (fail) | 1 |
| utilities | .__and__ (fail) | 1 |
| vector | .func (unsupported) | 4 |
| vector | BaseScalar (error) | 3 |
| vector | .equals (fail) | 3 |
| vector | srepr (fail) | 3 |
| vector | .__call__ (unsupported) | 3 |
| vector | .zero (fail) | 2 |
| vector | .__and__ (fail) | 2 |
| vector | directional_derivative (error) | 1 |
| vector | Integral (fail) | 1 |
| vector | .is_scalar (unsupported) | 1 |

## Corpus files

| Category | Cases bytes | Audit bytes | Shards |
|---|---:|---:|---:|
| algebras | 104409 | 4581 | 1 |
| assumptions | 1068001 | 85105 | 1 |
| calculus | 384185 | 24750 | 1 |
| categories | 1123226 | 12987 | 1 |
| codegen | 40819 | 1078 | 1 |
| combinatorics | 912051 | 123645 | 1 |
| concrete | 684557 | 71311 | 1 |
| core | 3534962 | 986914 | 1 |
| crypto | 60530 | 11364 | 1 |
| diffgeom | 216838 | 9347 | 1 |
| discrete | 158625 | 5412 | 1 |
| functions | 5504119 | 390805 | 1 |
| geometry | 779396 | 101709 | 1 |
| holonomic | 103903 | 19663 | 1 |
| integrals | 1160482 | 335101 | 1 |
| liealgebras | 59045 | 2842 | 1 |
| logic | 396810 | 94565 | 1 |
| matrices | 6935733 | 433701 | 1 |
| ntheory | 15835330 | 100766 | 1 |
| parsing | 235432 | 54771 | 1 |
| plotting | 14901 | 222147 | 1 |
| polys | 7928355 | 956239 | 1 |
| printing | 991535 | 673375 | 1 |
| series | 1212954 | 133937 | 1 |
| sets | 784089 | 135944 | 1 |
| simplify | 1111384 | 163075 | 1 |
| solvers | 2974966 | 446049 | 1 |
| stats | 1779902 | 91572 | 1 |
| strategies | 2779 | 24605 | 1 |
| tensor | 1873362 | 267912 | 1 |
| unify | 2822 | 15257 | 1 |
| utilities | 1355963 | 239872 | 1 |
| vector | 1652629 | 38287 | 1 |

Case shards contain one JSON case per line, with ASCII escapes and finite JSON numbers. Shards are at most 25 MB. tests-report.json contains summaries only; tests-results/*.jsonl contains one failure per line.

## Out-of-scope test files

| File (relative to sympy/) | Technical reason |
|---|---|
| codegen/tests/test_abstract_nodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_algorithms.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_applications.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_approximations.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_ast.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_cnodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_cxxnodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_fnodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_matrix_nodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_numpy_nodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_pynodes.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_pyutils.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_rewriting.py | Source-code generation and compiler integration are outside this corpus. |
| codegen/tests/test_scipy_nodes.py | Source-code generation and compiler integration are outside this corpus. |
| external/tests/test_autowrap.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_codegen.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_gmpy.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_importtools.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_ntheory.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_numpy.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_pythonmpq.py | Python bindings to optional external libraries are runtime-specific. |
| external/tests/test_scipy.py | Python bindings to optional external libraries are runtime-specific. |
| interactive/tests/test_interactive.py | Python REPL/session integration is runtime-specific. |
| interactive/tests/test_ipython.py | Python REPL/session integration is runtime-specific. |
| multipledispatch/tests/test_conflict.py | Python dispatch infrastructure is replaced by TypeScript expression dispatch; no public port. |
| multipledispatch/tests/test_core.py | Python dispatch infrastructure is replaced by TypeScript expression dispatch; no public port. |
| multipledispatch/tests/test_dispatcher.py | Python dispatch infrastructure is replaced by TypeScript expression dispatch; no public port. |
| parsing/tests/test_ast_parser.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| parsing/tests/test_autolev.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| parsing/tests/test_c_parser.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| parsing/tests/test_fortran_parser.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| parsing/tests/test_latex_deps.py | Checks the import failure without the ANTLR runtime; the port has no runtime dependency. |
| parsing/tests/test_maxima.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| parsing/tests/test_sym_expr.py | Parser other than sympy_parser or Mathematica (including LaTeX, Autolev and compiler parsers). |
| physics/biomechanics/tests/test_activation.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/biomechanics/tests/test_curve.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/biomechanics/tests/test_mixin.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/biomechanics/tests/test_musculotendon.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/continuum_mechanics/tests/test_arch.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/continuum_mechanics/tests/test_beam.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/continuum_mechanics/tests/test_cable.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/continuum_mechanics/tests/test_truss.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/control/tests/test_control_plots.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/control/tests/test_lti.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/hep/tests/test_gamma_matrices.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_actuator.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_body.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_functions.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_inertia.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_joint.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_jointsmethod.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_kane.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_kane2.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_kane3.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_kane4.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_kane5.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_lagrange.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_lagrange2.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_linearity_of_velocity_constraints.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_linearize.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_loads.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_method.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_models.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_particle.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_pathway.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_rigidbody.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_system.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_system_class.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/mechanics/tests/test_wrapping_geometry.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/optics/tests/test_gaussopt.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/optics/tests/test_medium.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/optics/tests/test_polarization.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/optics/tests/test_utils.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/optics/tests/test_waves.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_anticommutator.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_boson.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_cartesian.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_cg.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_circuitplot.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_circuitutils.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_commutator.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_constants.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_dagger.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_density.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_fermion.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_gate.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_grover.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_hilbert.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_identitysearch.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_innerproduct.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_kind.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_matrixutils.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_operator.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_operatorordering.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_operatorset.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_pauli.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_piab.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_printing.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_qapply.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_qasm.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_qexpr.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_qft.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_qubit.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_represent.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_sho1d.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_shor.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_spin.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_state.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_tensorproduct.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_trace.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/quantum/tests/test_transforms.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_clebsch_gordan.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_hydrogen.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_paulialgebra.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_physics_matrices.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_pring.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_qho_1d.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_secondquant.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/tests/test_sho.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_dimensions.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_dimensionsystem.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_prefixes.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_quantities.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_unit_system_cgs_gauss.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_unitsystem.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/units/tests/test_util.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_dyadic.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_fieldfunctions.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_frame.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_functions.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_output.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_point.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_printing.py | Physics belongs to extension packages, not the base symbolic engine. |
| physics/vector/tests/test_vector.py | Physics belongs to extension packages, not the base symbolic engine. |
| plotting/pygletplot/tests/test_plotting.py | Interactive OpenGL rendering is provided by connector packages. |
| plotting/tests/test_experimental_lambdify.py | Python source generation is replaced by symjs numeric evaluation. |
| printing/tests/test_aesaracode.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_c.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_codeprinter.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_cupy.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_cxx.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_fortran.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_glsl.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_gtk.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_jax.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_jscode.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_julia.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_lambdarepr.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_llvmjit.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_maple.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_mathematica.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_numpy.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_octave.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_preview.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_pycode.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_python.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_rcode.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_rust.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_smtlib.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_tensorflow.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_theanocode.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| printing/tests/test_torch.py | Code printer or external rendering backend; not a base symbolic display printer in extract.MODULES. |
| sandbox/tests/test_indexed_integrals.py | Experimental sandbox APIs are outside the base doctest scope. |
| stats/sampling/tests/test_sample_continuous_rv.py | External sampling-library adapters require optional dependencies. |
| stats/sampling/tests/test_sample_discrete_rv.py | External sampling-library adapters require optional dependencies. |
| stats/sampling/tests/test_sample_finite_rv.py | External sampling-library adapters require optional dependencies. |
| testing/tests/test_code_quality.py | Upstream test runners are infrastructure, not mathematical APIs. |
| testing/tests/test_deprecated.py | Upstream test runners are infrastructure, not mathematical APIs. |
| testing/tests/test_module_imports.py | Upstream test runners are infrastructure, not mathematical APIs. |
| testing/tests/test_pytest.py | Upstream test runners are infrastructure, not mathematical APIs. |
| testing/tests/test_runtests_pytest.py | Upstream test runners are infrastructure, not mathematical APIs. |
| utilities/_compilation/tests/test_compilation.py | Compiler and Python-extension build helpers are outside base scope. |
| utilities/tests/test_autowrap.py | Compiles generated code with external toolchains. |
| utilities/tests/test_codegen.py | Source-code generation is outside this corpus. |
| utilities/tests/test_codegen_julia.py | Julia source-code generation is outside this corpus. |
| utilities/tests/test_codegen_octave.py | Octave source-code generation is outside this corpus. |
| utilities/tests/test_codegen_rust.py | Rust source-code generation is outside this corpus. |
| utilities/tests/test_deprecated.py | Deprecated Python module import shims are runtime-specific. |
| utilities/tests/test_exceptions.py | Python warnings machinery has no JavaScript runtime counterpart. |
| utilities/tests/test_matchpy_connector.py | Requires the optional matchpy library. |
| utilities/tests/test_mathml.py | XSLT conversion requires optional lxml; MathML printing is measured separately. |
| utilities/tests/test_pickling.py | Python pickle persistence is runtime-specific. |
| utilities/tests/test_source.py | Python import and source inspection are runtime-specific. |
| utilities/tests/test_timeutils.py | Python benchmark/timing infrastructure is runtime-specific. |
| utilities/tests/test_xxe.py | XML stylesheet processing requires optional lxml. |

Accepted exception class mismatches: **697**. Their case IDs and classes are retained in tests-report.json.
