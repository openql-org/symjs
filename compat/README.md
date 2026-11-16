# Compatibility ratchets

The doctest and unit-test ratchets replay the corpora of
[`tools/sympy-corpus`](../tools/sympy-corpus/README.md) through its harness and
compare the results with the recorded gaps. The two corpora have independent
denominators and ratchets. Neither report measures unexecuted assertions as
successes.

| Measurement | Replay | Ratchet | Report |
|---|---|---|---|
| Doctests | `compat.test.ts` | `known-gaps.json` | `REPORT.md`, `report.json` |
| Unit tests | `tests-compat.test.ts` | `tools/sympy-corpus/tests-known-gaps.json` | `TESTS-REPORT.md`, `tests-report.json` |

Run all compatibility checks with:

```sh
npx vitest run --config compat/vitest.config.ts
npx vitest run --config compat/vitest.config.ts --project unit-geometry
```
