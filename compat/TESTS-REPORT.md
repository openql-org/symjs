# SymPy unit-test compatibility

Reference: SymPy 1.14.0. Independent of the doctest corpus and its ratchet.

Measured **122717** cases: **108746 exact**, **2626 equivalent**, **11345 failing**. Agreement: **90.76%**.

Compatibility suite wall time: **1168.24 s**. Sum of category replay times: **1268.69 s** (projects run in parallel).

Extraction wall time: **66.07 s**, 4 processes, 120 s per upstream test. Retained modules reuse established observations; their time covers loading and auditing, not re-execution.

Synchronous replay has a 30 s deadline per core/polys case and 5 s elsewhere. Deadlines remain visible as failing/inconclusive observations and are never accepted as expected exceptions. Their IDs are stored separately in the ratchet: an unfinished assertion cannot establish or resolve a correctness regression.

The statistics row uses an isolated replay with a 30-second deadline per case; other rows retain the original full replay. Wall time includes that retry.

Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the shared doctest deserializer, adapters and equivalence rules. Exception class mismatches are accepted and counted separately; missing adapters and deserialization errors never prove an expected exception.

## Agreement by category

| Category | Measured | Exact | Equivalent | Failing | Agreement | Replay s |
|---|---:|---:|---:|---:|---:|---:|
| algebras | 133 | 128 | 0 | 5 | 96.24% | 0.52 |
| assumptions | 2245 | 1784 | 5 | 456 | 79.69% | 1.36 |
| calculus | 525 | 425 | 1 | 99 | 81.14% | 2.10 |
| categories | 333 | 327 | 0 | 6 | 98.20% | 1.35 |
| codegen | 71 | 67 | 4 | 0 | 100.00% | 0.57 |
| combinatorics | 2196 | 2153 | 0 | 43 | 98.04% | 1.02 |
| concrete | 937 | 682 | 71 | 184 | 80.36% | 14.83 |
| core | 9337 | 7742 | 202 | 1393 | 85.08% | 83.37 |
| crypto | 5067 | 5065 | 0 | 2 | 99.96% | 1.18 |
| diffgeom | 210 | 204 | 6 | 0 | 100.00% | 1.36 |
| discrete | 192 | 191 | 1 | 0 | 100.00% | 0.76 |
| functions | 10649 | 7491 | 1856 | 1302 | 87.77% | 43.16 |
| geometry | 1102 | 1061 | 6 | 35 | 96.82% | 11.96 |
| holonomic | 190 | 176 | 0 | 14 | 92.63% | 2.63 |
| integrals | 1424 | 936 | 49 | 439 | 69.17% | 17.85 |
| liealgebras | 93 | 87 | 1 | 5 | 94.62% | 0.05 |
| logic | 7608 | 7414 | 1 | 193 | 97.46% | 3.32 |
| matrices | 5093 | 4217 | 42 | 834 | 83.62% | 91.33 |
| ntheory | 45168 | 45140 | 0 | 28 | 99.94% | 9.26 |
| parsing | 868 | 736 | 69 | 63 | 92.74% | 0.44 |
| plotting | 49 | 23 | 0 | 26 | 46.94% | 0.05 |
| polys | 12154 | 8887 | 88 | 3179 | 73.84% | 236.82 |
| printing | 2147 | 1863 | 1 | 283 | 86.82% | 6.23 |
| series | 1674 | 1196 | 29 | 449 | 73.18% | 11.66 |
| sets | 1858 | 1137 | 11 | 710 | 61.79% | 1.50 |
| simplify | 1525 | 1314 | 44 | 167 | 89.05% | 7.18 |
| solvers | 4618 | 3654 | 82 | 882 | 80.90% | 79.21 |
| stats | 2025 | 1934 | 42 | 49 | 97.58% | 586.86 |
| strategies | 7 | 5 | 0 | 2 | 71.43% | 0.01 |
| tensor | 1953 | 1547 | 1 | 405 | 79.26% | 11.12 |
| unify | 16 | 10 | 0 | 6 | 62.50% | 0.04 |
| utilities | 556 | 485 | 10 | 61 | 89.03% | 28.61 |
| vector | 694 | 665 | 4 | 25 | 96.40% | 10.97 |

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
| assumptions | missing API/adapter | 40 |
| assumptions | unexpected exception | 3 |
| assumptions | unsupported value/input type | 10 |
| assumptions | wrong result | 392 |
| assumptions | exception class mismatch (accepted) | 1 |
| calculus | exception not raised | 14 |
| calculus | input conversion exception | 11 |
| calculus | missing API/adapter | 3 |
| calculus | unexpected exception | 15 |
| calculus | wrong result | 56 |
| calculus | exception class mismatch (accepted) | 15 |
| categories | missing API/adapter | 6 |
| categories | exception class mismatch (accepted) | 5 |
| codegen | exception class mismatch (accepted) | 0 |
| combinatorics | exception not raised | 1 |
| combinatorics | missing API/adapter | 14 |
| combinatorics | result comparison exception | 1 |
| combinatorics | unexpected exception | 5 |
| combinatorics | unsupported value/input type | 5 |
| combinatorics | wrong result | 17 |
| combinatorics | exception class mismatch (accepted) | 8 |
| concrete | exception not raised | 12 |
| concrete | input conversion exception | 2 |
| concrete | missing API/adapter | 30 |
| concrete | replay timeout | 1 |
| concrete | result comparison exception | 3 |
| concrete | unexpected exception | 22 |
| concrete | wrong result | 114 |
| concrete | exception class mismatch (accepted) | 12 |
| core | exception not raised | 281 |
| core | input conversion exception | 27 |
| core | missing API/adapter | 173 |
| core | result comparison exception | 2 |
| core | unexpected exception | 197 |
| core | unsupported value/input type | 98 |
| core | wrong result | 615 |
| core | exception class mismatch (accepted) | 106 |
| crypto | wrong result | 2 |
| crypto | exception class mismatch (accepted) | 1 |
| diffgeom | exception class mismatch (accepted) | 0 |
| discrete | exception class mismatch (accepted) | 0 |
| functions | exception not raised | 67 |
| functions | input conversion exception | 2 |
| functions | missing API/adapter | 78 |
| functions | replay timeout | 4 |
| functions | result comparison exception | 1 |
| functions | unexpected exception | 275 |
| functions | unsupported value/input type | 55 |
| functions | wrong result | 820 |
| functions | exception class mismatch (accepted) | 97 |
| geometry | exception not raised | 3 |
| geometry | input conversion exception | 3 |
| geometry | missing API/adapter | 3 |
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
| integrals | missing API/adapter | 78 |
| integrals | replay timeout | 1 |
| integrals | result comparison exception | 1 |
| integrals | unexpected exception | 39 |
| integrals | unsupported value/input type | 5 |
| integrals | wrong result | 300 |
| integrals | exception class mismatch (accepted) | 6 |
| liealgebras | wrong result | 5 |
| liealgebras | exception class mismatch (accepted) | 0 |
| logic | exception not raised | 3 |
| logic | input conversion exception | 13 |
| logic | missing API/adapter | 77 |
| logic | unexpected exception | 14 |
| logic | wrong result | 86 |
| logic | exception class mismatch (accepted) | 35 |
| matrices | exception not raised | 106 |
| matrices | input conversion exception | 41 |
| matrices | missing API/adapter | 94 |
| matrices | replay timeout | 13 |
| matrices | result comparison exception | 5 |
| matrices | unexpected exception | 244 |
| matrices | unsupported value/input type | 52 |
| matrices | wrong result | 279 |
| matrices | exception class mismatch (accepted) | 118 |
| ntheory | exception not raised | 2 |
| ntheory | unexpected exception | 9 |
| ntheory | unsupported value/input type | 10 |
| ntheory | wrong result | 7 |
| ntheory | exception class mismatch (accepted) | 10 |
| parsing | exception not raised | 8 |
| parsing | unexpected exception | 14 |
| parsing | wrong result | 41 |
| parsing | exception class mismatch (accepted) | 17 |
| plotting | exception not raised | 2 |
| plotting | input conversion exception | 2 |
| plotting | unexpected exception | 21 |
| plotting | wrong result | 1 |
| plotting | exception class mismatch (accepted) | 8 |
| polys | exception not raised | 92 |
| polys | input conversion exception | 44 |
| polys | missing API/adapter | 1027 |
| polys | replay timeout | 5 |
| polys | result comparison exception | 8 |
| polys | unexpected exception | 1253 |
| polys | unsupported value/input type | 342 |
| polys | wrong result | 408 |
| polys | exception class mismatch (accepted) | 187 |
| printing | exception not raised | 2 |
| printing | input conversion exception | 17 |
| printing | missing API/adapter | 11 |
| printing | replay timeout | 1 |
| printing | unexpected exception | 84 |
| printing | unsupported value/input type | 32 |
| printing | wrong result | 136 |
| printing | exception class mismatch (accepted) | 2 |
| series | exception not raised | 25 |
| series | missing API/adapter | 84 |
| series | result comparison exception | 1 |
| series | unexpected exception | 136 |
| series | unsupported value/input type | 2 |
| series | wrong result | 201 |
| series | exception class mismatch (accepted) | 14 |
| sets | exception not raised | 34 |
| sets | input conversion exception | 21 |
| sets | missing API/adapter | 49 |
| sets | result comparison exception | 13 |
| sets | unexpected exception | 123 |
| sets | unsupported value/input type | 15 |
| sets | wrong result | 455 |
| sets | exception class mismatch (accepted) | 29 |
| simplify | exception not raised | 1 |
| simplify | missing API/adapter | 30 |
| simplify | unexpected exception | 28 |
| simplify | unsupported value/input type | 7 |
| simplify | wrong result | 101 |
| simplify | exception class mismatch (accepted) | 2 |
| solvers | exception not raised | 69 |
| solvers | input conversion exception | 28 |
| solvers | missing API/adapter | 143 |
| solvers | replay timeout | 8 |
| solvers | unexpected exception | 293 |
| solvers | unsupported value/input type | 4 |
| solvers | wrong result | 337 |
| solvers | exception class mismatch (accepted) | 54 |
| stats | exception not raised | 3 |
| stats | input conversion exception | 5 |
| stats | missing API/adapter | 4 |
| stats | replay timeout | 5 |
| stats | unexpected exception | 6 |
| stats | unsupported value/input type | 4 |
| stats | wrong result | 22 |
| stats | exception class mismatch (accepted) | 8 |
| strategies | missing API/adapter | 2 |
| strategies | exception class mismatch (accepted) | 0 |
| tensor | exception not raised | 3 |
| tensor | input conversion exception | 6 |
| tensor | missing API/adapter | 182 |
| tensor | unexpected exception | 36 |
| tensor | unsupported value/input type | 3 |
| tensor | wrong result | 175 |
| tensor | exception class mismatch (accepted) | 21 |
| unify | unexpected exception | 2 |
| unify | wrong result | 4 |
| unify | exception class mismatch (accepted) | 0 |
| utilities | missing API/adapter | 2 |
| utilities | replay timeout | 2 |
| utilities | unexpected exception | 21 |
| utilities | unsupported value/input type | 3 |
| utilities | wrong result | 33 |
| utilities | exception class mismatch (accepted) | 16 |
| vector | missing API/adapter | 3 |
| vector | unexpected exception | 6 |
| vector | wrong result | 16 |
| vector | exception class mismatch (accepted) | 4 |

## Most frequent failing APIs per category

| Category | API and outcome | Cases |
|---|---|---:|
| algebras | .__mul__ (fail) | 2 |
| algebras | .__add__ (fail) | 1 |
| algebras | .pow (error) | 1 |
| algebras | trigsimp (error) | 1 |
| assumptions | ask (fail) | 352 |
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
| calculus | .__pow__ (error) | 3 |
| categories | ArrowStringDescription (unsupported) | 6 |
| combinatorics | .P (fail) | 10 |
| combinatorics | unchanged (error) | 4 |
| combinatorics | graph_certificate (unsupported) | 4 |
| combinatorics | .__getitem__ (unsupported) | 3 |
| combinatorics | .is_alt_sym (unsupported) | 2 |
| combinatorics | .from_inversion_vector (unsupported) | 2 |
| combinatorics | .__add__ (unsupported) | 1 |
| combinatorics | rubik (unsupported) | 1 |
| combinatorics | get_subset_from_bitstring (error) | 1 |
| combinatorics | .__gt__ (fail) | 1 |
| concrete | eval_sum_residue (unsupported) | 27 |
| concrete | .doit (fail) | 17 |
| concrete | summation (fail) | 12 |
| concrete | .is_finite (fail) | 11 |
| concrete | .free_symbols (fail) | 8 |
| concrete | Sum (error) | 7 |
| concrete | Sum (fail) | 7 |
| concrete | .expand (fail) | 7 |
| concrete | Product (fail) | 6 |
| concrete | .is_negative (fail) | 6 |
| core | .subs (fail) | 88 |
| core | .diff (fail) | 60 |
| core | .reversedsign (unsupported) | 51 |
| core | .matches (fail) | 50 |
| core | .simplify (fail) | 38 |
| core | Mod (fail) | 31 |
| core | .__lt__ (fail) | 29 |
| core | .__mul__ (fail) | 26 |
| core | .match (unsupported) | 26 |
| core | .__ge__ (fail) | 25 |
| crypto | lfsr_sequence (fail) | 2 |
| functions | .rewrite (fail) | 119 |
| functions | .as_leading_term (error) | 95 |
| functions | .__lt__ (fail) | 75 |
| functions | .series (error) | 71 |
| functions | primepi (fail) | 54 |
| functions | .expand (fail) | 47 |
| functions | .as_leading_term (fail) | 47 |
| functions | test_derivative_numerically (unsupported) | 38 |
| functions | .is_real (fail) | 32 |
| functions | .integrate (fail) | 30 |
| geometry | Intersection (fail) | 5 |
| geometry | .equation (error) | 3 |
| geometry | Union (fail) | 3 |
| geometry | .__call__ (unsupported) | 2 |
| geometry | .subs (fail) | 2 |
| geometry | Intersection (error) | 2 |
| geometry | .is_nonzero (fail) | 2 |
| geometry | .__mul__ (fail) | 2 |
| geometry | .cut_section (fail) | 2 |
| geometry | .arbitrary_point (fail) | 1 |
| holonomic | .to_sequence (fail) | 5 |
| holonomic | expr_to_holonomic (error) | 3 |
| holonomic | DifferentialOperators (error) | 2 |
| holonomic | HolonomicFunction (fail) | 1 |
| holonomic | expr_to_holonomic (fail) | 1 |
| holonomic | .rewrite (fail) | 1 |
| holonomic | .expand (fail) | 1 |
| integrals | integrate (fail) | 156 |
| integrals | manualintegrate (fail) | 81 |
| integrals | integrate (error) | 19 |
| integrals | decompose (error) | 14 |
| integrals | risch_integrate (unsupported) | 14 |
| integrals | heurisch (fail) | 12 |
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
| matrices | .__getitem__ (error) | 42 |
| matrices | .diff (error) | 23 |
| matrices | MutableDenseMatrix (fail) | 22 |
| matrices | .from_index_summation (error) | 18 |
| matrices | .is_echelon (unsupported) | 18 |
| matrices | .__pow__ (error) | 18 |
| matrices | .is_Identity (unsupported) | 18 |
| matrices | MutableDenseMatrix (error) | 17 |
| ntheory | smoothness_p (unsupported) | 10 |
| ntheory | factorint (fail) | 4 |
| ntheory | smoothness_p (error) | 4 |
| ntheory | .__getitem__ (error) | 3 |
| ntheory | divisors (fail) | 1 |
| ntheory | proper_divisors (fail) | 1 |
| ntheory | factorrat (fail) | 1 |
| ntheory | totient (fail) | 1 |
| ntheory | is_nthpow_residue (error) | 1 |
| ntheory | nthroot_mod (error) | 1 |
| parsing | parse_expr (fail) | 47 |
| parsing | parse_expr (error) | 14 |
| parsing | parse_latex_lark (fail) | 2 |
| plotting | LineOver1DRangeSeries (error) | 7 |
| plotting | Parametric2DLineSeries (error) | 3 |
| plotting | Parametric3DLineSeries (error) | 3 |
| plotting | SurfaceOver2DRangeSeries (error) | 3 |
| plotting | ContourSeries (error) | 2 |
| plotting | ParametricSurfaceSeries (error) | 2 |
| plotting | extract_solution (error) | 2 |
| plotting | intervalMembership (fail) | 1 |
| plotting | interval (fail) | 1 |
| plotting | ImplicitSeries (error) | 1 |
| polys | .__mul__ (error) | 653 |
| polys | .dup_count_complex_roots (unsupported) | 105 |
| polys | .rep (unsupported) | 88 |
| polys | .dup_isolate_real_roots_sqf (unsupported) | 76 |
| polys | groebner (error) | 58 |
| polys | .lll (unsupported) | 39 |
| polys | .lll_transform (unsupported) | 39 |
| polys | dict_from_expr (unsupported) | 37 |
| polys | .dup_refine_real_root (unsupported) | 35 |
| polys | .extract_slice (fail) | 34 |
| printing | latex (error) | 72 |
| printing | srepr (fail) | 35 |
| printing | latex (fail) | 34 |
| printing | mathml (fail) | 32 |
| printing | latex (unsupported) | 22 |
| printing | sstr (fail) | 17 |
| printing | .__getitem__ (error) | 10 |
| printing | sstr (error) | 9 |
| printing | pretty (error) | 4 |
| printing | .__mul__ (unsupported) | 4 |
| series | .nseries (error) | 73 |
| series | gruntz (unsupported) | 41 |
| series | .__add__ (fail) | 40 |
| series | compare (fail) | 35 |
| series | limit (fail) | 32 |
| series | .series (error) | 31 |
| series | Order (fail) | 31 |
| series | .function (unsupported) | 16 |
| series | rational_algorithm (unsupported) | 15 |
| series | .subs (fail) | 15 |
| sets | .intersect (fail) | 173 |
| sets | .__contains__ (error) | 50 |
| sets | .__pow__ (fail) | 31 |
| sets | .__truediv__ (fail) | 29 |
| sets | .is_finite_set (unsupported) | 25 |
| sets | .is_iterable (fail) | 23 |
| sets | Intersection (fail) | 21 |
| sets | .__mul__ (fail) | 21 |
| sets | .is_subset (fail) | 17 |
| sets | .__getitem__ (error) | 16 |
| simplify | simplify (fail) | 25 |
| simplify | .simplify (fail) | 11 |
| simplify | simplify (error) | 10 |
| simplify | hyperexpand (fail) | 10 |
| simplify | collect (fail) | 10 |
| simplify | separatevars (fail) | 8 |
| simplify | cancel (fail) | 8 |
| simplify | cse (error) | 6 |
| simplify | cse (fail) | 6 |
| simplify | preprocess_for_cse (unsupported) | 5 |
| solvers | solve (error) | 139 |
| solvers | solveset (fail) | 78 |
| solvers | solve (fail) | 61 |
| solvers | solveset_real (fail) | 46 |
| solvers | linodesolve (unsupported) | 37 |
| solvers | nonlinsolve (error) | 36 |
| solvers | dsolve (error) | 31 |
| solvers | classify_ode (fail) | 29 |
| solvers | solveset_complex (unsupported) | 24 |
| solvers | matrix_exp (fail) | 18 |
| stats | .dummy_eq (fail) | 8 |
| stats | .__getitem__ (unsupported) | 4 |
| stats | .doit (error) | 4 |
| stats | median (fail) | 3 |
| stats | probability (fail) | 2 |
| stats | variance (fail) | 2 |
| stats | skewness (error) | 2 |
| stats | kurtosis (error) | 2 |
| stats | .__call__ (error) | 2 |
| stats | .foo (unsupported) | 2 |
| strategies | treeapply (unsupported) | 2 |
| tensor | .__getitem__ (unsupported) | 106 |
| tensor | convert_array_to_matrix (fail) | 45 |
| tensor | .data (unsupported) | 29 |
| tensor | .__call__ (unsupported) | 17 |
| tensor | .doit (fail) | 11 |
| tensor | convert_matrix_to_array (fail) | 11 |
| tensor | .split_multiple_contractions (unsupported) | 10 |
| tensor | .expand (fail) | 10 |
| tensor | .func (error) | 9 |
| tensor | .diff (fail) | 7 |
| unify | deconstruct (fail) | 4 |
| unify | unify (error) | 2 |
| utilities | partitions (fail) | 7 |
| utilities | simplify (error) | 4 |
| utilities | integrate (fail) | 4 |
| utilities | capture (unsupported) | 3 |
| utilities | solve (error) | 3 |
| utilities | .series (error) | 3 |
| utilities | partitions (error) | 2 |
| utilities | .invert (error) | 2 |
| utilities | solveset (fail) | 2 |
| utilities | solveset_real (fail) | 2 |
| vector | .__or__ (fail) | 6 |
| vector | BaseScalar (error) | 3 |
| vector | .equals (fail) | 3 |
| vector | .__call__ (unsupported) | 3 |
| vector | .func (error) | 2 |
| vector | .zero (fail) | 2 |
| vector | .__and__ (fail) | 2 |
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

Accepted exception class mismatches: **782**. Their case IDs and classes are retained in tests-report.json.
