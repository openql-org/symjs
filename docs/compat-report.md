# SymPy agreement of generated corpus tests (`bun run corpus:report`)

Generated from the `*.corpus.test.ts` files; do not edit.
Rate = cases that give SymPy's result / all cases; Exact rate = cases printed as SymPy prints them / all cases.
Exact: the same `str()` output. Equivalent: a mathematically equal result in another form (listed in [compat-equivalent-cases.md](compat-equivalent-cases.md)).
Fails: translated, the result differs. Todo: not translated yet.

## Doctests

| Category | Rate | Exact rate | Exact | Equivalent | Fails | Todo | Stale |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| abc | 0.00% | 0.00% | 0 | 0 | 0 | 3 | 0 |
| algebras | 93.75% | 93.75% | 60 | 0 | 0 | 4 | 0 |
| assumptions | 87.73% | 87.73% | 193 | 0 | 0 | 27 | 0 |
| calculus | 91.45% | 91.45% | 107 | 0 | 0 | 10 | 0 |
| categories | 78.18% | 78.18% | 43 | 0 | 0 | 12 | 0 |
| codegen | 88.89% | 88.89% | 16 | 0 | 0 | 2 | 0 |
| combinatorics | 71.45% | 71.45% | 433 | 0 | 3 | 170 | 0 |
| concrete | 64.91% | 63.16% | 108 | 3 | 0 | 60 | 0 |
| core | 83.53% | 83.53% | 847 | 0 | 0 | 167 | 0 |
| crypto | 77.50% | 77.50% | 62 | 0 | 0 | 18 | 0 |
| diffgeom | 89.80% | 87.76% | 86 | 2 | 0 | 10 | 0 |
| discrete | 81.03% | 81.03% | 47 | 0 | 0 | 11 | 0 |
| functions | 96.83% | 96.34% | 974 | 5 | 0 | 32 | 0 |
| geometry | 85.12% | 84.93% | 451 | 1 | 0 | 79 | 0 |
| holonomic | 81.58% | 81.58% | 31 | 0 | 0 | 7 | 0 |
| integrals | 63.45% | 63.45% | 125 | 0 | 0 | 72 | 0 |
| liealgebras | 55.81% | 55.81% | 24 | 0 | 0 | 19 | 0 |
| logic | 85.71% | 85.71% | 180 | 0 | 0 | 30 | 0 |
| matrices | 89.85% | 89.85% | 983 | 0 | 0 | 111 | 0 |
| ntheory | 62.93% | 62.93% | 146 | 0 | 0 | 86 | 0 |
| parsing | 86.21% | 75.86% | 22 | 3 | 0 | 4 | 0 |
| plotting | 33.33% | 33.33% | 1 | 0 | 0 | 2 | 0 |
| polys | 79.34% | 79.27% | 1312 | 1 | 0 | 342 | 0 |
| printing | 72.00% | 72.00% | 54 | 0 | 0 | 21 | 0 |
| series | 76.11% | 76.11% | 86 | 0 | 0 | 27 | 0 |
| sets | 89.14% | 89.14% | 156 | 0 | 0 | 19 | 0 |
| simplify | 82.74% | 82.74% | 254 | 0 | 0 | 53 | 0 |
| solvers | 58.41% | 57.96% | 262 | 2 | 0 | 188 | 0 |
| stats | 94.43% | 92.43% | 415 | 9 | 1 | 24 | 0 |
| strategies | 25.00% | 25.00% | 2 | 0 | 0 | 6 | 0 |
| tensor | 81.49% | 81.49% | 229 | 0 | 0 | 52 | 0 |
| unify | 0.00% | 0.00% | 0 | 0 | 0 | 2 | 0 |
| utilities | 44.12% | 44.12% | 45 | 0 | 1 | 56 | 0 |
| vector | 41.57% | 41.57% | 69 | 0 | 0 | 97 | 0 |
| **all** | **81.11%** | **80.84%** | 7823 | 26 | 5 | 1823 | 0 |

## Unit tests

| Category | Rate | Exact rate | Exact | Equivalent | Fails | Todo | Stale |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| algebras | 93.98% | 93.98% | 125 | 0 | 0 | 8 | 0 |
| assumptions | 98.44% | 98.35% | 2208 | 2 | 6 | 29 | 0 |
| calculus | 91.05% | 90.86% | 477 | 1 | 3 | 44 | 0 |
| categories | 64.56% | 64.56% | 215 | 0 | 0 | 118 | 0 |
| codegen | 85.92% | 80.28% | 57 | 4 | 0 | 10 | 0 |
| combinatorics | 80.10% | 80.10% | 1759 | 0 | 1 | 436 | 0 |
| concrete | 77.48% | 71.72% | 672 | 54 | 3 | 208 | 0 |
| core | 88.00% | 86.53% | 8079 | 138 | 34 | 1086 | 0 |
| crypto | 99.29% | 99.29% | 5031 | 0 | 1 | 35 | 0 |
| diffgeom | 89.52% | 86.67% | 182 | 6 | 0 | 22 | 0 |
| discrete | 80.21% | 79.69% | 153 | 1 | 0 | 38 | 0 |
| functions | 95.54% | 79.47% | 8463 | 1711 | 20 | 455 | 0 |
| geometry | 85.57% | 85.30% | 940 | 3 | 3 | 156 | 0 |
| holonomic | 86.84% | 86.84% | 165 | 0 | 0 | 25 | 0 |
| integrals | 73.31% | 68.82% | 980 | 64 | 1 | 379 | 0 |
| liealgebras | 68.82% | 67.74% | 63 | 1 | 0 | 29 | 0 |
| logic | 97.80% | 97.78% | 7439 | 2 | 0 | 167 | 0 |
| matrices | 84.53% | 84.06% | 4281 | 24 | 27 | 761 | 0 |
| ntheory | 99.47% | 99.47% | 44928 | 0 | 8 | 232 | 0 |
| parsing | 90.67% | 83.41% | 724 | 63 | 12 | 69 | 0 |
| plotting | 71.43% | 71.43% | 35 | 0 | 0 | 14 | 0 |
| polys | 59.53% | 59.12% | 7185 | 50 | 167 | 4752 | 0 |
| printing | 87.70% | 87.66% | 1882 | 1 | 1 | 263 | 0 |
| series | 86.08% | 84.71% | 1418 | 23 | 5 | 228 | 0 |
| sets | 86.01% | 85.90% | 1596 | 2 | 13 | 247 | 0 |
| simplify | 87.28% | 84.92% | 1295 | 36 | 0 | 194 | 0 |
| solvers | 32.07% | 31.23% | 1442 | 39 | 29 | 3108 | 0 |
| stats | 97.23% | 95.90% | 1942 | 27 | 1 | 55 | 0 |
| strategies | 100.00% | 100.00% | 7 | 0 | 0 | 0 | 0 |
| tensor | 75.27% | 75.27% | 1470 | 0 | 13 | 470 | 0 |
| unify | 62.50% | 62.50% | 10 | 0 | 4 | 2 | 0 |
| utilities | 59.71% | 58.99% | 328 | 4 | 9 | 215 | 0 |
| vector | 26.51% | 26.51% | 184 | 0 | 2 | 508 | 0 |
| **all** | **88.00%** | **86.16%** | 105735 | 2256 | 363 | 14363 | 0 |
