# Architecture and conventions

These conventions are frozen. Changes require an explicit owner decision recorded here.

## Type policy

- **Raw counts live in `ℕ`.** Cardinalities, edit distances, and tuple counts are natural
  numbers.
- **Normalized densities and errors live in `ℝ`.** There is no pervasive `ℚ → ℝ` cast
  layer. Where mathlib's API is `ℚ`-valued (e.g. `SimpleGraph.edgeDensity`,
  `Finpartition.energy`), a bridge states exactly one `Rat.cast` equation at the boundary.

## Denominator policy

- Densities are **zero on an empty denominator**, via real division's `x / 0 = 0`.
  Definitions carry no `if`-guards for emptiness.
- Substantive theorems require denominator positivity or support nonemptiness as
  **explicit hypotheses**. Complement identities such as `d(p) + d(¬p) = 1` are false on
  empty supports and are only stated with a `Nonempty` hypothesis.

## Injectivity policy

- All copy-counting intended for removal arguments uses **injective source tuples**.
  Diagonal-sensitive variants must be separate, clearly named, and require exact diagonal
  control. Collision (non-injective) mass is bounded explicitly and loses one ambient
  power of the host size.

## Partition conventions

- Partitions are mathlib `Finpartition`s; the library never introduces a private
  partition type.
- **`P ≤ Q` means `P` is finer than `Q`** (mathlib's order).
- **Energy is mass-weighted.** The partition energy is
  `Σ_{A,B} (|A||B| / |s|²) · d(A,B)²`, **including diagonal blocks**. This is the
  refinement-monotone quantity; the uniform block-mean of `d²` is *not*
  refinement-monotone and is never used as the primary notion. Mathlib's
  `Finpartition.energy` (uniform, `ℚ`-valued, off-diagonal) is bridged only where both
  sides speak `SimpleGraph`.

## Statement discipline

- **No `sorry`, `admit`, or custom `axiom` on committed branches.** All declarations use
  only the standard axioms `propext`, `Classical.choice`, `Quot.sound`
  (enforced by `scripts/check.sh`, which audits every declaration in the library
  namespace).
- **No contentless `Prop` placeholders.** An unproved major result is never represented
  by defining a large `Prop` and treating it as available.
- Major statements pass, in order: a mathematical statement review; small finite
  counterexample tests; a dependency audit; and only then an API freeze.
- Search mathlib before introducing every foundational definition; wrap rather than
  reprove.

## Code organization

- Files stay focused, generally below 600 lines.
- Each file ends with a `/-! ### Tests and adversarial examples -/` section exercising
  its API on small finite types (kernel `decide` preferred; `native_decide` only in
  anonymous `example`s).
- Every green semantic unit becomes a commit and is pushed immediately. Pushed history
  is never rewritten.

## Deferred summit statements

Intended results whose proofs are not yet complete are recorded here as prose — never as
Lean `Prop` placeholders.

- **Almost-refining regular equipartition** (graph ladder): an honestly stated theorem
  producing an equitable regular partition almost-refining a given partition, consuming
  the quantitative `AlmostRefines` bridge.
- **Strong graph regularity with counting**, **finite Frieze–Kannan weak regularity**,
  **triadic regular approximation**, and **colored arity-three counting/removal**:
  planned for later releases; statements will be frozen only after their falsification
  gates.
