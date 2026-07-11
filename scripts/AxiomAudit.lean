import Lean

/-!
# Axiom audit

Walks every constant under the `RegularityLemmata` namespace and verifies that its
axioms are a subset of `{propext, Classical.choice, Quot.sound}`.

Fails closed: any enumeration or collection error exits nonzero, and auditing zero
declarations is itself a failure (the library root always defines
`RegularityLemmata.version`, so an empty audit means the walk went wrong).
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def auditRoot : Name := `RegularityLemmata

def main : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := auditRoot }] {} (trustLevel := 1024)
    -- Normalize private names (`_private.RegularityLemmata.….0.RegularityLemmata.foo`)
    -- back to their user names so private project declarations are audited too.
    let targets := env.constants.fold (init := #[]) fun acc n _ =>
      if auditRoot.isPrefixOf (privateToUserName n) then acc.push n else acc
    let coreCtx : Core.Context := { fileName := "<axiom_audit>", fileMap := default }
    let mut audited := 0
    let mut offenders : Array (Name × Name) := #[]
    for n in targets do
      let (axs, _) ← (collectAxioms n : CoreM (Array Name)).toIO coreCtx { env := env }
      audited := audited + 1
      for a in axs do
        unless allowedAxioms.contains a do
          offenders := offenders.push (n, a)
    IO.println s!"axiom_audit: audited {audited} declaration(s) under {auditRoot}"
    if audited == 0 then
      IO.eprintln "axiom_audit: FAIL — zero declarations audited"
      return 1
    unless offenders.isEmpty do
      for (n, a) in offenders do
        IO.eprintln s!"axiom_audit: FAIL — {n} uses non-standard axiom {a}"
      return 1
    IO.println "axiom_audit: OK — standard axioms only"
    return 0
  catch e =>
    IO.eprintln s!"axiom_audit: FAIL — error during audit: {e}"
    return 1
