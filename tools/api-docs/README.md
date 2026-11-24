# API documentation tools

Checks of the documentation comments of `packages/symjs/src` against the rules of
[docs/api-policy.md](../../docs/api-policy.md#documentation-comments).

| Script | Purpose | Run with |
|---|---|---|
| `coverage.ts` | Emits the declarations with `tsc`, follows every entry point of `package.json` `exports` to the declaration of each export, and reports per source area which exports and public class members have a comment, `@param`/`@returns` for every signature, `@see SymPy` and `@example`. `--json <file>` writes one record per export (source file, members, missing parameters) | `bun run docs:coverage` (writes `docs/api-docs-coverage.md`) |
| `examples.ts` | Extracts the fenced `ts` blocks of `@example`, type-checks them with `tsc` against the sources and runs them with `bun`; a statement followed by `// => result` must give `result` (a string as it is, a number by `String()`, any other value through `sstr`, which prints like SymPy's `str()`). Path arguments restrict the check to files or directories; `--no-run` only type-checks | `bun run docs:examples [paths...]` |

## Writing a comment

1. Find the export in `bun tools/api-docs/coverage.ts --json <file>` (fields
   `missingParams`, `missingReturns`, `sympy`, `example`, and `members` of classes).
2. Take the SymPy docstring of the counterpart
   (`python3 -c "import sympy; help(sympy.factor)"`) for the description and the
   examples; translate the examples to the public API with `ex` and options objects.
3. Write the summary, `@param`, `@returns`, `@throws`, ``@see SymPy `sympy....` ``
   and `@example` (see `factor` in `packages/symjs/src/polys/sympoly.ts`).
4. Run `bun run docs:examples <file>`. Where symjs's result differs from SymPy's,
   the example shows symjs's result and `@remarks` gives SymPy's.
