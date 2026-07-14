# Contributing

Contributions are welcome via pull requests from forks. The library is pre-1.0: the
API may change between releases, and large contributions are best discussed in an
issue first so the statement-freeze discipline below can be applied before code is
written.

## Licensing of contributions

By submitting a contribution, you agree that it is licensed under the Apache License
2.0 (the license of this repository) and that you have the right to submit it under
that license. Add the standard SPDX header to new files.

## Workflow

1. Fork the repository and create a topic branch from `main`.
2. Make your changes following the per-unit cadence below.
3. Open a pull request. CI runs `bash scripts/check.sh`; it must pass.
4. Maintainers review; once approved, the PR is merged without history rewriting.

## Per-unit cadence

For every bounded unit of work:

1. Search mathlib for existing API.
2. Identify whether the unit is new or adapted, and record public antecedents in
   docstrings (and `PROVENANCE.md` where they materially inform a proof).
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

## Commit messages

Conventional prefixes: `feat(area):`, `docs:`, `chore:`, `ci:`. One green semantic unit
per commit. Never rewrite pushed history.

## Gates

`scripts/check.sh` enforces: successful build; no `sorry`/`admit`/`axiom` in source; no
sorry warnings in the build log; and an axiom audit of every declaration in the library
namespace (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`). CI runs
the same script.

## Conventions

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the frozen design conventions (type and
denominator policies, injectivity policy, partition conventions, statement discipline,
and code organization). Changes to frozen conventions require an explicit owner
decision recorded there.
