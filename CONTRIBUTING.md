# Contributing

## Per-unit cadence

For every bounded unit of work:

1. Search mathlib for existing API.
2. Identify whether the unit is new or adapted.
3. Review or rewrite the target statement.
4. Add adversarial examples (empty supports, diagonal tuples, degenerate partitions,
   zero denominators).
5. Implement it under the `RegularityLemmata` namespace.
6. Run:
   - `lake build`
   - `bash scripts/check.sh`
   - `git diff --check`
7. Inspect `git status --short`.
8. Commit only the intended files.
9. Push immediately.

## Commit messages

Conventional prefixes: `feat(area):`, `docs:`, `chore:`, `ci:`. One green semantic unit
per commit. Never rewrite pushed history.

## Gates

`scripts/check.sh` enforces: successful build; no `sorry`/`admit`/`axiom` in source; no
sorry warnings in the build log; and an axiom audit of every
declaration in the library namespace (standard axioms only). CI runs the same script.
