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
4. Maintainers review; once approved, the PR is squash-merged onto `main`. Published history on `main` is never rewritten; the squash is the one commit the branch becomes.

## Building and checking the repository

This is the workflow for working on the library itself; to *use* the library in a project, see
the quick start in the README.

```bash
lake exe cache get      # mathlib's compiled cache, once per pin
lake build              # the library, the gates umbrella, and the examples
bash scripts/check.sh   # build, sorry scan, axiom audit, roots gate; what CI runs
```

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and the mathlib revision in
[`lake-manifest.json`](lake-manifest.json); both change only in dedicated PRs.

**Release verification.** Every release is checked from outside: the external consumer fixture
under [`consumer/`](consumer/README.md), a separate Lake package depending on this repository by
Git at a full commit, is rebuilt against the release candidate and again against the merge
commit before the tag is created, and its resolved manifest must name that commit. The recipe
is in its README.

## Public API impact

Every pull request must contain a nonempty `## Public API impact` section. Use one or more
of the following forms:

- `Added: ...`
- `Changed: ...`
- `Deprecated/removed: ...`
- `None`

Use `None` explicitly when the change has no public API impact. CI checks that the section
is present, nonblank after removing template comments, and contains one of these forms.
Reviewers remain responsible for checking that the inventory is complete and that items
classified as `None` are genuinely internal or documentary.

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
sorry warnings in the build log; an axiom audit of every declaration in the library
namespace (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`); and the
self-tests for the pull-request-body validator. On pull requests, CI additionally validates
the actual `Public API impact` section before building.

## Documentation

Four surfaces, four triggers. Keeping them separate is what stops any of them from staling:

- **`README.md`** — update only when the **user-facing capability boundary** changes: a new
  public capability, or a change to what the library does not yet claim. Not for individual
  theorems, and never a development chronology.
- **`ARCHITECTURE.md`** — update when a **design invariant** changes: a policy, a frozen
  constant, a module dependency direction, or the supported theorem boundary.
- **`PROVENANCE.md`** — update when an **intellectual dependency or adaptation claim**
  changes: a new antecedent, or a change in what is borrowed versus what is not.

- **`docs/design/*.md`** — one document per design target, each opening with a status banner
  (implemented, with links to the declarations; approved but not implemented; or deferred): goal,
  fixed normalizations, proved inputs, current construction, permanent obstruction gates, open
  certificates, non-goals. An implemented record keeps the historical design as frozen; factual
  corrections and status updates (the banner, links to what merged) are made in place, and a
  changed contract gets a new record rather than a rewritten one. A rejected route is recorded there once, by its mathematical
  obstruction. Do not transfer chronology into it; Git history and issues already preserve
  the order of discovery.

Per-module detail belongs in module docstrings, which are the record for their own module.

## Conventions

See [`ARCHITECTURE.md`](ARCHITECTURE.md) for the frozen design conventions (type and
denominator policies, injectivity policy, partition conventions, statement discipline,
and code organization). Changes to frozen conventions require an explicit owner
decision recorded there.
