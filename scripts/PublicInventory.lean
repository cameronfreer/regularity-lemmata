/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import RegularityLemmata

/-!
# Public inventory (environment-based)

Prints one line per public constant of the environment obtained by importing the public root
`RegularityLemmata`: every constant declared in a module under the `RegularityLemmata` prefix
that is neither private nor an internal detail (`Name.isInternalDetail`: auxiliary
`match_`/`proof_`/`_eq_`-style names and underscore-prefixed components). Generated public
names (structure projections, constructors, recursors, `noConfusion`, `injEq`, …) and
instances are included, since a reader can refer to them; instances are tagged `[instance]`.

    lake exe public_inventory > inventory.txt

Diffing the output at two commits is the mechanical public-API delta of a change. The axiom
audit's total counts private and internal constants as well and is not a public-API count.
Fails closed: an empty inventory exits nonzero.
-/

open Lean

def inventoryRoot : Name := `RegularityLemmata

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def main : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := inventoryRoot }] {} (trustLevel := 1024)
    -- Instances, read from the persisted per-module entries of the instance extension (the
    -- extension's live state is not populated by a bare `importModules`).
    let mut instNames : Std.HashSet Name := {}
    for idx in [0:env.header.moduleNames.size] do
      for e in Meta.instanceExtension.ext.getModuleEntries env idx do
        if let .global ie := e then
          if let some n := ie.globalName? then instNames := instNames.insert n
    let mut lines : Array String := #[]
    let mut modules : Std.HashSet Name := {}
    for (n, ci) in env.constants.map₁.toList do
      if isPrivateName n || n.isInternalDetail then continue
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless inventoryRoot.isPrefixOf mod do continue
      modules := modules.insert mod
      let inst := if instNames.contains n then " [instance]" else ""
      lines := lines.push s!"{mod}: {kindOf ci} {n}{inst}"
    let sorted := lines.qsort (· < ·)
    for l in sorted do IO.println l
    IO.eprintln s!"public_inventory: {sorted.size} public constants in {modules.size} modules under {inventoryRoot}"
    if sorted.isEmpty then
      IO.eprintln "public_inventory: FAIL — empty inventory"
      return 1
    return 0
  catch e =>
    IO.eprintln s!"public_inventory: FAIL — {e}"
    return 1
