# SymPy unit-test compatibility

Reference: SymPy 1.14.0. Independent of the doctest corpus and its ratchet.

Measured **122717** cases: **112783 exact**, **2627 equivalent**, **7307 failing**. Agreement: **94.05%**.

Compatibility suite wall time: **352.41 s**. Sum of category replay times: **580.08 s** (projects run in parallel).

Extraction wall time: **66.07 s**, 4 processes, 120 s per upstream test. Retained modules reuse established observations; their time covers loading and auditing, not re-execution.

Synchronous replay has a 30 s deadline per core/polys case and 5 s elsewhere. Deadlines remain visible as failing/inconclusive observations and are never accepted as expected exceptions. Their IDs are stored separately in the ratchet: an unfinished assertion cannot establish or resolve a correctness regression.

Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the shared doctest deserializer, adapters and equivalence rules. Exception class mismatches are accepted and counted separately; missing adapters and deserialization errors never prove an expected exception.

## Agreement by category

| Category | Measured | Exact | Equivalent | Failing | Agreement | Replay s |
|---|---:|---:|---:|---:|---:|---:|
| algebras | 133 | 128 | 0 | 5 | 96.24% | 0.23 |
| assumptions | 2245 | 2089 | 11 | 145 | 93.54% | 0.66 |
| calculus | 525 | 429 | 1 | 95 | 81.90% | 1.27 |
| categories | 333 | 333 | 0 | 0 | 100.00% | 0.67 |
| codegen | 71 | 67 | 4 | 0 | 100.00% | 0.26 |
| combinatorics | 2196 | 2160 | 0 | 36 | 98.36% | 0.44 |
| concrete | 937 | 704 | 74 | 159 | 83.03% | 5.14 |
| core | 9337 | 8115 | 202 | 1020 | 89.08% | 43.07 |
| crypto | 5067 | 5065 | 0 | 2 | 99.96% | 0.40 |
| diffgeom | 210 | 204 | 6 | 0 | 100.00% | 0.50 |
| discrete | 192 | 191 | 1 | 0 | 100.00% | 0.33 |
| functions | 10649 | 7820 | 1852 | 977 | 90.83% | 33.89 |
| geometry | 1102 | 1063 | 6 | 33 | 97.01% | 9.50 |
| holonomic | 190 | 176 | 0 | 14 | 92.63% | 1.98 |
| integrals | 1424 | 1000 | 55 | 369 | 74.09% | 11.16 |
| liealgebras | 93 | 87 | 1 | 5 | 94.62% | 0.02 |
| logic | 7608 | 7501 | 1 | 106 | 98.61% | 1.01 |
| matrices | 5093 | 4573 | 42 | 478 | 90.61% | 76.83 |
| ntheory | 45168 | 45141 | 0 | 27 | 99.94% | 4.66 |
| parsing | 868 | 787 | 69 | 12 | 98.62% | 0.19 |
| plotting | 49 | 47 | 0 | 2 | 95.92% | 0.02 |
| polys | 12154 | 10564 | 86 | 1504 | 87.63% | 170.09 |
| printing | 2147 | 1941 | 1 | 205 | 90.45% | 4.55 |
| series | 1674 | 1319 | 32 | 323 | 80.70% | 5.35 |
| sets | 1858 | 1523 | 2 | 333 | 82.08% | 5.45 |
| simplify | 1525 | 1325 | 45 | 155 | 89.84% | 2.76 |
| solvers | 4618 | 3753 | 80 | 785 | 83.00% | 53.42 |
| stats | 2025 | 1931 | 42 | 52 | 97.43% | 132.58 |
| strategies | 7 | 5 | 0 | 2 | 71.43% | 0.00 |
| tensor | 1953 | 1572 | 1 | 380 | 80.54% | 2.64 |
| unify | 16 | 10 | 0 | 6 | 62.50% | 0.01 |
| utilities | 556 | 493 | 9 | 54 | 90.29% | 9.36 |
| vector | 694 | 667 | 4 | 23 | 96.69% | 1.62 |

## Extraction audit

Executed loop instances count individually. Duplicates count as omissions; never-reached sites count once. Partial observations from timed-out upstream tests are discarded. Detailed source locations and test statuses are in each category audit file.

| Category | Source sites | Examined | Cases | Omitted | Wall s | Retained modules |
|---|---:|---:|---:|---:|---:|---:|
| algebras | 123 | 138 | 133 | 5 | 1.46 | 0 |
| assumptions | 2186 | 2636 | 2245 | 391 | 29.01 | 0 |
| calculus | 543 | 619 | 525 | 94 | 13.02 | 0 |
| categories | 372 | 372 | 333 | 39 | 4.34 | 0 |
| codegen | 71 | 71 | 71 | 0 | 0.22 | 0 |
| combinatorics | 1274 | 403796 | 2196 | 401600 | 133.94 | 0 |
| concrete | 1026 | 1124 | 937 | 187 | 41.27 | 0 |
| core | 9529 | 26543 | 9337 | 17206 | 59.35 | 0 |
| crypto | 185 | 5078 | 5067 | 11 | 3.42 | 0 |
| diffgeom | 213 | 213 | 210 | 3 | 2.73 | 0 |
| discrete | 202 | 202 | 192 | 10 | 1.73 | 0 |
| functions | 7194 | 23768 | 10649 | 13119 | 119.34 | 0 |
| geometry | 1430 | 1534 | 1102 | 432 | 26.89 | 0 |
| holonomic | 190 | 217 | 190 | 27 | 15.14 | 0 |
| integrals | 2261 | 2477 | 1424 | 1053 | 179.24 | 0 |
| liealgebras | 95 | 95 | 93 | 2 | 0.21 | 0 |
| logic | 960 | 8612 | 7608 | 1004 | 35.60 | 0 |
| matrices | 4840 | 7206 | 5093 | 2113 | 65.39 | 0 |
| ntheory | 1050 | 601996 | 45168 | 556828 | 273.97 | 0 |
| parsing | 294 | 2112 | 868 | 1244 | 20.97 | 0 |
| plotting | 1128 | 1237 | 49 | 1188 | 4.67 | 0 |
| polys | 10731 | 37096 | 12154 | 24942 | 141.11 | 0 |
| printing | 4121 | 4759 | 2147 | 2612 | 132.47 | 0 |
| series | 1968 | 2035 | 1674 | 361 | 122.58 | 0 |
| sets | 1794 | 6469 | 1858 | 4611 | 7.15 | 0 |
| simplify | 1878 | 2292 | 1525 | 767 | 47.94 | 0 |
| solvers | 3740 | 8519 | 4618 | 3901 | 393.50 | 0 |
| stats | 1612 | 2401 | 2025 | 376 | 79.35 | 0 |
| strategies | 103 | 105 | 7 | 98 | 0.16 | 0 |
| tensor | 2070 | 2813 | 1953 | 860 | 612.12 | 0 |
| unify | 64 | 64 | 16 | 48 | 0.22 | 0 |
| utilities | 1176 | 25656 | 556 | 25100 | 39.87 | 0 |
| vector | 797 | 805 | 694 | 111 | 20.32 | 0 |

| Category | Omission reason | Count |
|---|---|---:|
| algebras | marked-slow | 1 |
| algebras | non-call-expression | 1 |
| algebras | not-executed | 1 |
| algebras | private-api | 2 |
| assumptions | duplicate | 316 |
| assumptions | marked-slow | 2 |
| assumptions | marked-xfail | 25 |
| assumptions | not-executed | 3 |
| assumptions | not-exported-api | 32 |
| assumptions | unserializable-input | 6 |
| assumptions | unsupported-assertion | 7 |
| calculus | duplicate | 43 |
| calculus | marked-slow | 1 |
| calculus | marked-xfail | 5 |
| calculus | not-executed | 2 |
| calculus | not-exported-api | 4 |
| calculus | python-runtime-api | 1 |
| calculus | stateful-iterator-input | 2 |
| calculus | unsupported-assertion | 36 |
| categories | non-call-expression | 2 |
| categories | not-exported-api | 1 |
| categories | python-runtime-api | 1 |
| categories | unserializable-input | 32 |
| categories | unsupported-assertion | 3 |
| combinatorics | duplicate | 489 |
| combinatorics | marked-slow | 21 |
| combinatorics | marked-xfail | 6 |
| combinatorics | non-boolean-assertion | 6 |
| combinatorics | non-call-expression | 138 |
| combinatorics | not-exported-api | 51 |
| combinatorics | private-api | 530 |
| combinatorics | python-runtime-api | 400274 |
| combinatorics | serialization-error | 2 |
| combinatorics | stateful-iterator-input | 17 |
| combinatorics | unserializable-input | 14 |
| combinatorics | unstable-result-representation | 14 |
| combinatorics | unsupported-assertion | 38 |
| concrete | duplicate | 9 |
| concrete | marked-slow | 55 |
| concrete | marked-xfail | 4 |
| concrete | non-call-expression | 4 |
| concrete | not-exported-api | 54 |
| concrete | private-api | 8 |
| concrete | python-runtime-api | 11 |
| concrete | reference-exception | 2 |
| concrete | stateful-iterator-input | 1 |
| concrete | unserializable-input | 3 |
| concrete | unsupported-assertion | 36 |
| core | duplicate | 320 |
| core | marked-skip | 11 |
| core | marked-xfail | 48 |
| core | non-boolean-assertion | 114 |
| core | non-call-expression | 10716 |
| core | not-executed | 30 |
| core | not-exported-api | 2641 |
| core | optional-dependency | 89 |
| core | private-api | 233 |
| core | python-runtime-api | 410 |
| core | serialization-error | 18 |
| core | stateful-iterator-input | 61 |
| core | test-utility | 41 |
| core | unserializable-input | 1539 |
| core | unsupported-assertion | 929 |
| core | unsupported-raises | 6 |
| crypto | non-call-expression | 6 |
| crypto | python-runtime-api | 4 |
| crypto | stateful-iterator-input | 1 |
| diffgeom | not-executed | 1 |
| diffgeom | stateful-iterator-input | 2 |
| discrete | python-runtime-api | 2 |
| discrete | stateful-iterator-input | 8 |
| functions | duplicate | 9464 |
| functions | marked-slow | 104 |
| functions | marked-xfail | 18 |
| functions | non-boolean-assertion | 2 |
| functions | non-call-expression | 24 |
| functions | not-executed | 6 |
| functions | not-exported-api | 312 |
| functions | optional-dependency | 1 |
| functions | private-api | 153 |
| functions | python-runtime-api | 64 |
| functions | stateful-iterator-input | 2448 |
| functions | test-utility | 87 |
| functions | unserializable-input | 16 |
| functions | unsupported-assertion | 420 |
| geometry | duplicate | 10 |
| geometry | marked-slow | 310 |
| geometry | non-boolean-assertion | 2 |
| geometry | non-call-expression | 23 |
| geometry | not-exported-api | 2 |
| geometry | private-api | 14 |
| geometry | python-runtime-api | 12 |
| geometry | stateful-iterator-input | 2 |
| geometry | test-utility | 3 |
| geometry | unsupported-assertion | 54 |
| holonomic | non-call-expression | 27 |
| integrals | duplicate | 63 |
| integrals | marked-slow | 607 |
| integrals | marked-tooslow | 1 |
| integrals | marked-xfail | 38 |
| integrals | non-boolean-assertion | 2 |
| integrals | non-call-expression | 33 |
| integrals | not-executed | 1 |
| integrals | not-exported-api | 26 |
| integrals | private-api | 11 |
| integrals | python-runtime-api | 26 |
| integrals | test-utility | 10 |
| integrals | unserializable-input | 205 |
| integrals | unsupported-assertion | 30 |
| liealgebras | non-call-expression | 2 |
| logic | duplicate | 462 |
| logic | marked-xfail | 18 |
| logic | non-call-expression | 19 |
| logic | not-executed | 6 |
| logic | not-exported-api | 24 |
| logic | private-api | 6 |
| logic | python-runtime-api | 17 |
| logic | stateful-iterator-input | 22 |
| logic | unserializable-input | 42 |
| logic | unsupported-assertion | 372 |
| logic | unsupported-raises | 2 |
| logic | upstream-skip | 14 |
| matrices | deprecated-api | 4 |
| matrices | duplicate | 637 |
| matrices | marked-slow | 52 |
| matrices | marked-xfail | 15 |
| matrices | non-boolean-assertion | 10 |
| matrices | non-call-expression | 191 |
| matrices | not-executed | 32 |
| matrices | not-exported-api | 150 |
| matrices | optional-dependency | 42 |
| matrices | private-api | 69 |
| matrices | python-runtime-api | 193 |
| matrices | stateful-iterator-input | 85 |
| matrices | unserializable-input | 383 |
| matrices | unsupported-assertion | 246 |
| matrices | unsupported-raises | 4 |
| ntheory | duplicate | 10 |
| ntheory | marked-slow | 98 |
| ntheory | non-call-expression | 1182 |
| ntheory | not-exported-api | 454042 |
| ntheory | optional-dependency | 4 |
| ntheory | private-api | 5637 |
| ntheory | python-runtime-api | 40914 |
| ntheory | serialization-error | 7 |
| ntheory | stateful-iterator-input | 53457 |
| ntheory | test-timeout | 41 |
| ntheory | unserializable-input | 11 |
| ntheory | unstable-result-representation | 21 |
| ntheory | unsupported-assertion | 1404 |
| parsing | duplicate | 10 |
| parsing | marked-xfail | 3 |
| parsing | non-call-expression | 37 |
| parsing | not-executed | 1 |
| parsing | not-exported-api | 132 |
| parsing | private-api | 4 |
| parsing | python-runtime-api | 12 |
| parsing | test-exception:RecursionError | 1 |
| parsing | unserializable-input | 1042 |
| parsing | unsupported-raises | 2 |
| plotting | marked-xfail | 2 |
| plotting | non-boolean-assertion | 1 |
| plotting | non-call-expression | 17 |
| plotting | not-executed | 1 |
| plotting | not-exported-api | 218 |
| plotting | optional-dependency | 330 |
| plotting | private-api | 10 |
| plotting | python-runtime-api | 119 |
| plotting | stateful-iterator-input | 8 |
| plotting | unserializable-input | 471 |
| plotting | unsupported-assertion | 11 |
| polys | duplicate | 6907 |
| polys | marked-slow | 74 |
| polys | marked-tooslow | 2 |
| polys | marked-xfail | 11 |
| polys | non-call-expression | 7309 |
| polys | not-executed | 17 |
| polys | not-exported-api | 1852 |
| polys | optional-dependency | 335 |
| polys | private-api | 223 |
| polys | python-runtime-api | 7098 |
| polys | serialization-error | 319 |
| polys | stateful-iterator-input | 172 |
| polys | test-exception:TypeError | 2 |
| polys | test-utility | 50 |
| polys | unserializable-input | 432 |
| polys | unsupported-assertion | 138 |
| polys | unsupported-raises | 1 |
| printing | duplicate | 269 |
| printing | marked-xfail | 8 |
| printing | non-call-expression | 33 |
| printing | not-executed | 9 |
| printing | not-exported-api | 1409 |
| printing | optional-dependency | 5 |
| printing | private-api | 3 |
| printing | python-runtime-api | 265 |
| printing | reference-exception | 1 |
| printing | serialization-error | 5 |
| printing | stateful-iterator-input | 9 |
| printing | test-timeout | 2 |
| printing | unserializable-input | 509 |
| printing | unsupported-assertion | 85 |
| series | duplicate | 6 |
| series | marked-slow | 71 |
| series | marked-xfail | 22 |
| series | non-call-expression | 23 |
| series | not-executed | 2 |
| series | not-exported-api | 36 |
| series | private-api | 11 |
| series | python-runtime-api | 25 |
| series | stateful-iterator-input | 27 |
| series | unserializable-input | 44 |
| series | unsupported-assertion | 90 |
| series | upstream-skip | 4 |
| sets | duplicate | 1457 |
| sets | marked-xfail | 21 |
| sets | non-boolean-assertion | 2 |
| sets | non-call-expression | 7 |
| sets | not-executed | 2 |
| sets | not-exported-api | 787 |
| sets | private-api | 14 |
| sets | python-runtime-api | 1975 |
| sets | stateful-iterator-input | 38 |
| sets | unserializable-input | 21 |
| sets | unsupported-assertion | 287 |
| simplify | duplicate | 76 |
| simplify | marked-slow | 103 |
| simplify | marked-tooslow | 1 |
| simplify | marked-xfail | 101 |
| simplify | non-boolean-assertion | 4 |
| simplify | non-call-expression | 60 |
| simplify | not-executed | 3 |
| simplify | not-exported-api | 154 |
| simplify | private-api | 58 |
| simplify | python-runtime-api | 36 |
| simplify | serialization-error | 1 |
| simplify | stateful-iterator-input | 83 |
| simplify | test-utility | 64 |
| simplify | unserializable-input | 1 |
| simplify | unsupported-assertion | 22 |
| solvers | duplicate | 68 |
| solvers | marked-skip | 5 |
| solvers | marked-slow | 427 |
| solvers | marked-tooslow | 5 |
| solvers | marked-xfail | 79 |
| solvers | non-boolean-assertion | 11 |
| solvers | non-call-expression | 157 |
| solvers | not-executed | 11 |
| solvers | not-exported-api | 359 |
| solvers | private-api | 390 |
| solvers | python-runtime-api | 137 |
| solvers | stateful-iterator-input | 2158 |
| solvers | test-utility | 14 |
| solvers | unserializable-input | 8 |
| solvers | unsupported-assertion | 70 |
| solvers | upstream-skip | 2 |
| stats | duplicate | 29 |
| stats | marked-slow | 46 |
| stats | marked-xfail | 7 |
| stats | non-call-expression | 26 |
| stats | not-executed | 4 |
| stats | not-exported-api | 63 |
| stats | optional-dependency | 48 |
| stats | python-runtime-api | 56 |
| stats | stateful-iterator-input | 18 |
| stats | test-utility | 56 |
| stats | unsupported-assertion | 19 |
| stats | upstream-skip | 4 |
| strategies | non-call-expression | 3 |
| strategies | not-exported-api | 65 |
| strategies | stateful-iterator-input | 21 |
| strategies | unserializable-input | 2 |
| strategies | unstable-result-representation | 1 |
| strategies | unsupported-assertion | 6 |
| tensor | duplicate | 18 |
| tensor | marked-xfail | 4 |
| tensor | non-boolean-assertion | 1 |
| tensor | non-call-expression | 136 |
| tensor | not-executed | 1 |
| tensor | not-exported-api | 81 |
| tensor | private-api | 257 |
| tensor | python-runtime-api | 84 |
| tensor | stateful-iterator-input | 1 |
| tensor | test-timeout | 97 |
| tensor | unserializable-input | 166 |
| tensor | unsupported-assertion | 14 |
| unify | non-boolean-assertion | 1 |
| unify | non-call-expression | 1 |
| unify | not-exported-api | 28 |
| unify | reference-assertion-failed | 2 |
| unify | stateful-iterator-input | 7 |
| unify | unserializable-input | 7 |
| unify | unsupported-assertion | 2 |
| utilities | duplicate | 6 |
| utilities | marked-skip | 3 |
| utilities | marked-slow | 5 |
| utilities | marked-xfail | 104 |
| utilities | non-call-expression | 189 |
| utilities | not-executed | 6 |
| utilities | not-exported-api | 21259 |
| utilities | optional-dependency | 134 |
| utilities | private-api | 3 |
| utilities | python-runtime-api | 3112 |
| utilities | stateful-iterator-input | 85 |
| utilities | test-utility | 2 |
| utilities | unserializable-input | 16 |
| utilities | unsupported-assertion | 174 |
| utilities | unsupported-raises | 2 |
| vector | duplicate | 8 |
| vector | marked-xfail | 12 |
| vector | non-call-expression | 11 |
| vector | not-exported-api | 20 |
| vector | private-api | 14 |
| vector | python-runtime-api | 20 |
| vector | unsupported-assertion | 26 |

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
| combinatorics | completed | 169 |
| combinatorics | marked-slow | 3 |
| combinatorics | marked-xfail | 3 |
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
| solvers | completed | 543 |
| solvers | marked-skip | 4 |
| solvers | marked-slow | 53 |
| solvers | marked-tooslow | 6 |
| solvers | marked-xfail | 31 |
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
| unify | test-exception:AssertionError | 2 |
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
| assumptions | missing API/adapter | 1 |
| assumptions | unexpected exception | 1 |
| assumptions | wrong result | 132 |
| assumptions | exception class mismatch (accepted) | 1 |
| calculus | exception not raised | 14 |
| calculus | input conversion exception | 11 |
| calculus | unexpected exception | 14 |
| calculus | wrong result | 56 |
| calculus | exception class mismatch (accepted) | 17 |
| categories | exception class mismatch (accepted) | 5 |
| codegen | exception class mismatch (accepted) | 0 |
| combinatorics | exception not raised | 1 |
| combinatorics | missing API/adapter | 11 |
| combinatorics | result comparison exception | 1 |
| combinatorics | unexpected exception | 1 |
| combinatorics | unsupported value/input type | 5 |
| combinatorics | wrong result | 17 |
| combinatorics | exception class mismatch (accepted) | 8 |
| concrete | exception not raised | 12 |
| concrete | input conversion exception | 2 |
| concrete | missing API/adapter | 2 |
| concrete | result comparison exception | 3 |
| concrete | unexpected exception | 21 |
| concrete | wrong result | 119 |
| concrete | exception class mismatch (accepted) | 12 |
| core | exception not raised | 142 |
| core | input conversion exception | 23 |
| core | missing API/adapter | 89 |
| core | result comparison exception | 2 |
| core | unexpected exception | 174 |
| core | unsupported value/input type | 19 |
| core | wrong result | 571 |
| core | exception class mismatch (accepted) | 104 |
| crypto | wrong result | 2 |
| crypto | exception class mismatch (accepted) | 1 |
| diffgeom | exception class mismatch (accepted) | 0 |
| discrete | exception class mismatch (accepted) | 0 |
| functions | exception not raised | 29 |
| functions | input conversion exception | 4 |
| functions | missing API/adapter | 5 |
| functions | replay timeout | 3 |
| functions | result comparison exception | 1 |
| functions | unexpected exception | 261 |
| functions | unsupported value/input type | 28 |
| functions | wrong result | 646 |
| functions | exception class mismatch (accepted) | 97 |
| geometry | exception not raised | 3 |
| geometry | input conversion exception | 3 |
| geometry | missing API/adapter | 1 |
| geometry | replay timeout | 1 |
| geometry | result comparison exception | 1 |
| geometry | unexpected exception | 8 |
| geometry | wrong result | 16 |
| geometry | exception class mismatch (accepted) | 6 |
| holonomic | result comparison exception | 2 |
| holonomic | unexpected exception | 3 |
| holonomic | wrong result | 9 |
| holonomic | exception class mismatch (accepted) | 0 |
| integrals | exception not raised | 14 |
| integrals | input conversion exception | 1 |
| integrals | missing API/adapter | 27 |
| integrals | replay timeout | 1 |
| integrals | result comparison exception | 1 |
| integrals | unexpected exception | 27 |
| integrals | unsupported value/input type | 5 |
| integrals | wrong result | 293 |
| integrals | exception class mismatch (accepted) | 6 |
| liealgebras | wrong result | 5 |
| liealgebras | exception class mismatch (accepted) | 0 |
| logic | exception not raised | 3 |
| logic | missing API/adapter | 11 |
| logic | unexpected exception | 14 |
| logic | wrong result | 78 |
| logic | exception class mismatch (accepted) | 5 |
| matrices | exception not raised | 50 |
| matrices | input conversion exception | 3 |
| matrices | missing API/adapter | 58 |
| matrices | replay timeout | 12 |
| matrices | unexpected exception | 79 |
| matrices | unsupported value/input type | 40 |
| matrices | wrong result | 236 |
| matrices | exception class mismatch (accepted) | 133 |
| ntheory | exception not raised | 1 |
| ntheory | unexpected exception | 9 |
| ntheory | unsupported value/input type | 10 |
| ntheory | wrong result | 7 |
| ntheory | exception class mismatch (accepted) | 10 |
| parsing | unexpected exception | 9 |
| parsing | wrong result | 3 |
| parsing | exception class mismatch (accepted) | 17 |
| plotting | exception not raised | 1 |
| plotting | wrong result | 1 |
| plotting | exception class mismatch (accepted) | 2 |
| polys | exception not raised | 72 |
| polys | input conversion exception | 41 |
| polys | missing API/adapter | 462 |
| polys | replay timeout | 4 |
| polys | result comparison exception | 8 |
| polys | unexpected exception | 414 |
| polys | unsupported value/input type | 176 |
| polys | wrong result | 327 |
| polys | exception class mismatch (accepted) | 209 |
| printing | exception not raised | 1 |
| printing | input conversion exception | 7 |
| printing | missing API/adapter | 9 |
| printing | unexpected exception | 40 |
| printing | unsupported value/input type | 22 |
| printing | wrong result | 126 |
| printing | exception class mismatch (accepted) | 2 |
| series | exception not raised | 25 |
| series | missing API/adapter | 27 |
| series | result comparison exception | 1 |
| series | unexpected exception | 60 |
| series | unsupported value/input type | 2 |
| series | wrong result | 208 |
| series | exception class mismatch (accepted) | 16 |
| sets | exception not raised | 23 |
| sets | input conversion exception | 7 |
| sets | missing API/adapter | 10 |
| sets | replay timeout | 1 |
| sets | result comparison exception | 11 |
| sets | unexpected exception | 49 |
| sets | unsupported value/input type | 15 |
| sets | wrong result | 217 |
| sets | exception class mismatch (accepted) | 29 |
| simplify | exception not raised | 1 |
| simplify | missing API/adapter | 29 |
| simplify | unexpected exception | 20 |
| simplify | unsupported value/input type | 7 |
| simplify | wrong result | 98 |
| simplify | exception class mismatch (accepted) | 2 |
| solvers | exception not raised | 67 |
| solvers | input conversion exception | 6 |
| solvers | missing API/adapter | 80 |
| solvers | replay timeout | 4 |
| solvers | unexpected exception | 273 |
| solvers | unsupported value/input type | 8 |
| solvers | wrong result | 347 |
| solvers | exception class mismatch (accepted) | 68 |
| stats | exception not raised | 3 |
| stats | input conversion exception | 2 |
| stats | missing API/adapter | 4 |
| stats | replay timeout | 9 |
| stats | unexpected exception | 6 |
| stats | unsupported value/input type | 6 |
| stats | wrong result | 22 |
| stats | exception class mismatch (accepted) | 8 |
| strategies | missing API/adapter | 2 |
| strategies | exception class mismatch (accepted) | 0 |
| tensor | exception not raised | 3 |
| tensor | input conversion exception | 8 |
| tensor | missing API/adapter | 168 |
| tensor | unexpected exception | 34 |
| tensor | unsupported value/input type | 3 |
| tensor | wrong result | 164 |
| tensor | exception class mismatch (accepted) | 22 |
| unify | unexpected exception | 2 |
| unify | wrong result | 4 |
| unify | exception class mismatch (accepted) | 0 |
| utilities | missing API/adapter | 2 |
| utilities | replay timeout | 1 |
| utilities | unexpected exception | 19 |
| utilities | unsupported value/input type | 3 |
| utilities | wrong result | 29 |
| utilities | exception class mismatch (accepted) | 16 |
| vector | missing API/adapter | 3 |
| vector | unexpected exception | 6 |
| vector | wrong result | 14 |
| vector | exception class mismatch (accepted) | 4 |

## Most frequent failing APIs per category

| Category | API and outcome | Cases |
|---|---|---:|
| algebras | .__mul__ (fail) | 2 |
| algebras | .__add__ (fail) | 1 |
| algebras | .pow (error) | 1 |
| algebras | trigsimp (error) | 1 |
| assumptions | ask (fail) | 132 |
| assumptions | ask (error) | 11 |
| assumptions | pretty (error) | 1 |
| assumptions | .handler (unsupported) | 1 |
| calculus | .__pow__ (fail) | 17 |
| calculus | .__truediv__ (fail) | 10 |
| calculus | periodicity (fail) | 9 |
| calculus | not_empty_in (error) | 7 |
| calculus | continuous_domain (fail) | 6 |
| calculus | .__sub__ (fail) | 5 |
| calculus | .__add__ (fail) | 3 |
| calculus | .__mul__ (fail) | 3 |
| calculus | .__pow__ (error) | 3 |
| calculus | stationary_points (fail) | 3 |
| combinatorics | .P (fail) | 10 |
| combinatorics | graph_certificate (unsupported) | 4 |
| combinatorics | .is_alt_sym (unsupported) | 2 |
| combinatorics | .from_inversion_vector (unsupported) | 2 |
| combinatorics | .__add__ (unsupported) | 1 |
| combinatorics | rubik (unsupported) | 1 |
| combinatorics | get_subset_from_bitstring (error) | 1 |
| combinatorics | .__gt__ (fail) | 1 |
| combinatorics | .__gt__ (unsupported) | 1 |
| combinatorics | .random_pr (unsupported) | 1 |
| concrete | .doit (fail) | 15 |
| concrete | summation (fail) | 12 |
| concrete | .is_finite (fail) | 11 |
| concrete | eval_sum_residue (fail) | 10 |
| concrete | .free_symbols (fail) | 8 |
| concrete | Sum (error) | 7 |
| concrete | .expand (fail) | 7 |
| concrete | Sum (fail) | 6 |
| concrete | .is_negative (fail) | 6 |
| concrete | Product (error) | 6 |
| core | .subs (fail) | 88 |
| core | .diff (fail) | 60 |
| core | .matches (fail) | 50 |
| core | .simplify (fail) | 38 |
| core | Mod (fail) | 31 |
| core | .__mod__ (fail) | 23 |
| core | .evalf (fail) | 23 |
| core | .has (fail) | 17 |
| core | .nargs (fail) | 16 |
| core | .expand (fail) | 14 |
| crypto | lfsr_sequence (fail) | 2 |
| functions | .rewrite (fail) | 120 |
| functions | .as_leading_term (error) | 95 |
| functions | .series (error) | 71 |
| functions | .expand (fail) | 47 |
| functions | .as_leading_term (fail) | 47 |
| functions | .is_real (fail) | 32 |
| functions | .is_integer (fail) | 30 |
| functions | .integrate (fail) | 28 |
| functions | integrate (fail) | 26 |
| functions | .simplify (fail) | 22 |
| geometry | Intersection (fail) | 5 |
| geometry | .equation (error) | 3 |
| geometry | Union (fail) | 3 |
| geometry | .subs (fail) | 2 |
| geometry | Intersection (error) | 2 |
| geometry | .is_nonzero (fail) | 2 |
| geometry | .__mul__ (fail) | 2 |
| geometry | .cut_section (fail) | 2 |
| geometry | .arbitrary_point (fail) | 1 |
| geometry | .is_tangent (error) | 1 |
| holonomic | .to_sequence (fail) | 5 |
| holonomic | expr_to_holonomic (error) | 3 |
| holonomic | DifferentialOperators (error) | 2 |
| holonomic | HolonomicFunction (fail) | 1 |
| holonomic | expr_to_holonomic (fail) | 1 |
| holonomic | .rewrite (fail) | 1 |
| holonomic | .expand (fail) | 1 |
| integrals | integrate (fail) | 151 |
| integrals | manualintegrate (fail) | 81 |
| integrals | integrate (error) | 19 |
| integrals | heurisch (fail) | 12 |
| integrals | .is_zero (fail) | 7 |
| integrals | .as_sum (fail) | 5 |
| integrals | .args (fail) | 5 |
| integrals | frac_in (unsupported) | 5 |
| integrals | DifferentialExtension (unsupported) | 5 |
| integrals | mellin_transform (fail) | 5 |
| liealgebras | .basis (fail) | 3 |
| liealgebras | .cartan_type (fail) | 1 |
| liealgebras | .lie_algebra (fail) | 1 |
| logic | .simplify (fail) | 26 |
| logic | .binary_symbols (fail) | 14 |
| logic | simplify (fail) | 8 |
| logic | pl_true (error) | 6 |
| logic | conjuncts (fail) | 5 |
| logic | disjuncts (fail) | 5 |
| logic | .rewrite (fail) | 4 |
| logic | Xor (fail) | 3 |
| logic | bool_map (fail) | 3 |
| logic | .as_set (error) | 3 |
| matrices | .diff (fail) | 71 |
| matrices | .from_index_summation (error) | 18 |
| matrices | .is_echelon (unsupported) | 18 |
| matrices | .rref (fail) | 13 |
| matrices | .charpoly (fail) | 12 |
| matrices | .doit (fail) | 11 |
| matrices | Mul (unsupported) | 9 |
| matrices | ask (fail) | 8 |
| matrices | MutableDenseMatrix (error) | 8 |
| matrices | diag (fail) | 8 |
| ntheory | smoothness_p (unsupported) | 10 |
| ntheory | factorint (fail) | 4 |
| ntheory | smoothness_p (error) | 4 |
| ntheory | .__getitem__ (error) | 3 |
| ntheory | divisors (fail) | 1 |
| ntheory | proper_divisors (fail) | 1 |
| ntheory | factorrat (fail) | 1 |
| ntheory | is_nthpow_residue (error) | 1 |
| ntheory | nthroot_mod (error) | 1 |
| ntheory | binomial_mod (fail) | 1 |
| parsing | parse_expr (error) | 9 |
| parsing | parse_latex_lark (fail) | 2 |
| parsing | parse_expr (fail) | 1 |
| plotting | intervalMembership (fail) | 1 |
| plotting | .has (fail) | 1 |
| polys | groebner (error) | 58 |
| polys | roots_binomial (unsupported) | 28 |
| polys | is_isomorphism_possible (unsupported) | 28 |
| polys | field_isomorphism_pslq (unsupported) | 27 |
| polys | .lll (unsupported) | 24 |
| polys | .lll_transform (unsupported) | 24 |
| polys | .rep (unsupported) | 20 |
| polys | .cancel_denom (fail) | 19 |
| polys | RootSum (error) | 18 |
| polys | .minpoly (fail) | 18 |
| printing | latex (fail) | 61 |
| printing | srepr (fail) | 29 |
| printing | latex (error) | 26 |
| printing | sstr (fail) | 17 |
| printing | latex (unsupported) | 13 |
| printing | sstr (error) | 9 |
| printing | pretty (error) | 4 |
| printing | .__mul__ (unsupported) | 4 |
| printing | Mul (fail) | 4 |
| printing | Add (fail) | 3 |
| series | .__add__ (fail) | 40 |
| series | compare (fail) | 35 |
| series | limit (fail) | 32 |
| series | Order (fail) | 31 |
| series | .series (error) | 16 |
| series | rational_algorithm (unsupported) | 15 |
| series | .subs (fail) | 15 |
| series | .nseries (fail) | 11 |
| series | .as_leading_term (error) | 9 |
| series | .nseries (error) | 8 |
| sets | .intersect (fail) | 31 |
| sets | .__pow__ (fail) | 31 |
| sets | .__truediv__ (fail) | 29 |
| sets | .__mul__ (fail) | 21 |
| sets | Intersection (fail) | 19 |
| sets | .__getitem__ (error) | 16 |
| sets | .__contains__ (error) | 13 |
| sets | imageset (fail) | 12 |
| sets | ConditionSet (fail) | 9 |
| sets | .contains (fail) | 9 |
| simplify | simplify (fail) | 25 |
| simplify | .simplify (fail) | 11 |
| simplify | hyperexpand (fail) | 10 |
| simplify | collect (fail) | 10 |
| simplify | separatevars (fail) | 8 |
| simplify | cancel (fail) | 8 |
| simplify | cse (error) | 6 |
| simplify | cse (fail) | 6 |
| simplify | preprocess_for_cse (unsupported) | 5 |
| simplify | postprocess_for_cse (unsupported) | 5 |
| solvers | solve (error) | 132 |
| solvers | solveset (fail) | 78 |
| solvers | solve (fail) | 63 |
| solvers | solveset_real (fail) | 46 |
| solvers | dsolve (error) | 31 |
| solvers | classify_ode (fail) | 29 |
| solvers | matrix_exp (fail) | 18 |
| solvers | solveset (error) | 17 |
| solvers | invert_real (fail) | 17 |
| solvers | nonlinsolve (error) | 17 |
| stats | .dummy_eq (fail) | 8 |
| stats | .__getitem__ (unsupported) | 4 |
| stats | skewness (error) | 4 |
| stats | kurtosis (error) | 4 |
| stats | median (fail) | 3 |
| stats | probability (fail) | 2 |
| stats | variance (fail) | 2 |
| stats | .doit (error) | 2 |
| stats | .__call__ (error) | 2 |
| stats | .foo (unsupported) | 2 |
| strategies | treeapply (unsupported) | 2 |
| tensor | .__getitem__ (unsupported) | 106 |
| tensor | convert_array_to_matrix (fail) | 42 |
| tensor | .data (unsupported) | 29 |
| tensor | .split_multiple_contractions (unsupported) | 10 |
| tensor | convert_matrix_to_array (fail) | 10 |
| tensor | .expand (fail) | 10 |
| tensor | .func (error) | 9 |
| tensor | .doit (fail) | 7 |
| tensor | .diff (fail) | 7 |
| tensor | .__le__ (fail) | 7 |
| unify | deconstruct (fail) | 4 |
| unify | unify (error) | 2 |
| utilities | partitions (fail) | 7 |
| utilities | integrate (fail) | 4 |
| utilities | capture (unsupported) | 3 |
| utilities | solve (error) | 3 |
| utilities | .series (error) | 3 |
| utilities | partitions (error) | 2 |
| utilities | .invert (error) | 2 |
| utilities | simplify (error) | 2 |
| utilities | solveset (fail) | 2 |
| utilities | solveset_real (fail) | 2 |
| vector | .__or__ (fail) | 6 |
| vector | BaseScalar (error) | 3 |
| vector | .equals (fail) | 3 |
| vector | .__call__ (unsupported) | 3 |
| vector | .func (error) | 2 |
| vector | .zero (fail) | 2 |
| vector | srepr (fail) | 2 |
| vector | directional_derivative (error) | 1 |
| vector | Integral (fail) | 1 |

## Corpus files

| Category | Cases bytes | Audit bytes | Shards |
|---|---:|---:|---:|
| algebras | 123013 | 3482 | 1 |
| assumptions | 1081762 | 79904 | 1 |
| calculus | 388159 | 23727 | 1 |
| categories | 1138161 | 8809 | 1 |
| codegen | 40819 | 1078 | 1 |
| combinatorics | 1355921 | 79520 | 1 |
| concrete | 771647 | 61690 | 1 |
| core | 4185811 | 910100 | 1 |
| crypto | 2082184 | 7777 | 1 |
| diffgeom | 238205 | 3565 | 1 |
| discrete | 165207 | 4372 | 1 |
| functions | 5823227 | 339863 | 1 |
| geometry | 823199 | 91168 | 1 |
| holonomic | 188368 | 4366 | 1 |
| integrals | 1273649 | 318200 | 1 |
| liealgebras | 61800 | 1736 | 1 |
| logic | 9048956 | 88539 | 1 |
| matrices | 9169026 | 331934 | 1 |
| ntheory | 17377555 | 88439 | 1 |
| parsing | 279569 | 50611 | 1 |
| plotting | 41322 | 217109 | 1 |
| polys | 12123959 | 697357 | 1 |
| printing | 1195320 | 602226 | 1 |
| series | 1249763 | 125631 | 1 |
| sets | 969247 | 101606 | 1 |
| simplify | 1207854 | 146351 | 1 |
| solvers | 3822046 | 399876 | 1 |
| stats | 1953182 | 72810 | 1 |
| strategies | 3283 | 24325 | 1 |
| tensor | 2375370 | 196707 | 1 |
| unify | 8055 | 13625 | 1 |
| utilities | 1465456 | 195453 | 1 |
| vector | 2099226 | 28350 | 1 |

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

Accepted exception class mismatches: **800**. Their case IDs and classes are retained in tests-report.json.
