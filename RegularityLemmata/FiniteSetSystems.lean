/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import RegularityLemmata.Finite.RelationFiber
import RegularityLemmata.Finite.VCTrace

/-!
# Facade: finite set systems

One import for the library's stability-free finite set-system substrate. A **facade** imports
a curated stack and defines nothing; each listed module remains directly importable.

* `Finite.RelationFiber` — fibers of heterogeneous relations on supplied finite supports,
  finite fiber families, restriction/monotonicity laws, and honest empty-support endpoints.
* `Finite.VCTrace` — restriction of finite set families, Mathlib's VC dimension under tracing,
  and support-sensitive Sauer–Shelah and powerset bounds.

Mathlib owns the underlying shattering and VC-dimension definitions. This facade introduces no
stability, ladder, goodness, model, probability, or regularity vocabulary.
-/
