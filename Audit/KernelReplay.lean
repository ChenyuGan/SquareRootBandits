/-
Copyright (c) 2026 Bandits Lean preparation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Lean.CoreM
import Lean.Replay
import Lean.Util.FoldConsts

/-!
Inspection-only driver. Run after lake build, as documented in README.md.
The loading/replay sequence follows the pinned toolchain's LeanChecker.lean
`replayFromImports`, including private proof bodies. No mathematical fallback.
The metaprogramming exception is confined to this checker, outside Bandits.
-/

public section
open Lean

private def allowedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

/-- Walk actual bodies, rather than trusting serialized axiom summaries. -/
private def audit (env : Environment) (own mathematical : Std.HashMap Name ConstantInfo) : IO Nat := do
  let mut todo := mathematical.toList.map Prod.fst
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := (own[n]?).orElse (fun _ => env.find? n) |
      throw <| IO.userError s!"AXIOM_FAIL: missing dependency {n}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"LOGICAL_SAFETY_FAIL: proof dependency {n} is unsafe/partial"
    if let .axiomInfo _ := ci then
      unless allowedAxiom n do
        throw <| IO.userError s!"AXIOM_FAIL: forbidden axiom {n}"
      axioms := axioms.insert n
    for dep in ci.getUsedConstantsAsSet do
      todo := dep :: todo
  IO.println s!"AXIOMS_OK: {axioms.toArray.qsort Name.lt} ({seen.size} dependencies)"
  return seen.size

/-- Replay exactly one compiled module, never a module-name prefix. -/
private unsafe def checkModule (modName : Name) (expected : List String) : IO Unit := do
  let path ← findOLean modName
  let server := OLeanLevel.server.adjustFileName path
  let priv := OLeanLevel.private.adjustFileName path
  -- Modular pilot code must have all three parts; absence fails closed.
  for p in #[path, server, priv] do
    unless ← p.pathExists do
      throw <| IO.userError s!"REPLAY_FAIL: missing module part {p}"
  let parts ← readModuleDataParts #[path, server, priv]
  let some (pub, _) := parts[0]? |
    throw <| IO.userError "REPLAY_FAIL: no exported module data"
  let some (full, _) := parts.back? |
    throw <| IO.userError "REPLAY_FAIL: no private module data"
  unless pub.isModule && full.isModule do
    throw <| IO.userError "INTERFACE_FAIL: compiled file is not a module"
  unless full.constNames.size == full.constants.size do
    throw <| IO.userError "REPLAY_FAIL: malformed constant arrays"
  let (_, state) ← importModulesCore full.imports |>.run
  let env ← finalizeImport state full.imports {} 0 false false (isModule := true)
  let mut own : Std.HashMap Name ConstantInfo := {}
  for n in full.constNames, ci in full.constants do
    own := own.insert n ci
  let mut mathematical : Std.HashMap Name ConstantInfo := {}
  let mut compilerAuxiliaries := 0
  for (n, ci) in own.toList do
    if let .axiomInfo _ := ci then
      throw <| IO.userError s!"AXIOM_FAIL: project declares axiom {n}"
    if ci.isUnsafe || ci.isPartial then
      -- Lean emits an implementation-only recursive function for safe recursion.
      -- Permit only that narrow shape, with a safe parent in this same module.
      let .str parent "_unsafe_rec" := n |
        throw <| IO.userError s!"REPLAY_FAIL: unsafe/partial constant {n}"
      let some (.defnInfo parentInfo) := own[parent]? |
        throw <| IO.userError s!"REPLAY_FAIL: compiler auxiliary {n} has no definition parent"
      unless parentInfo.safety == .safe do
        throw <| IO.userError s!"REPLAY_FAIL: compiler auxiliary {n} has unsafe parent"
      compilerAuxiliaries := compilerAuxiliaries + 1
      IO.println s!"COMPILER_AUXILIARY: {n} (excluded from logical roots; dependency exclusion checked)"
    else
      mathematical := mathematical.insert n ci
      IO.println s!"CONSTANT: {n}"
  for s in expected do
    let n := s.toName
    unless pub.constNames.contains n && mathematical.contains n do
      throw <| IO.userError s!"INTERFACE_FAIL: expected public declaration missing: {n}"
  -- Print the actual transitive closure for the Python isolation check.
  for imp in env.header.modules do
    IO.println s!"IMPORT: {imp.module}"
    IO.println s!"IMPORT_PATH: {imp.module}\t{← findOLean imp.module}"
  for imp in full.imports do
    IO.println s!"DIRECT_IMPORT: {imp.module}"
  discard <| audit env own mathematical
  discard <| env.toKernelEnv.replay mathematical
  IO.println s!"KERNEL_REPLAY_OK: {modName} constants={mathematical.size} exports={expected.length} compiler_auxiliaries={compilerAuxiliaries}"
  env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  try
    let mod :: expected := args |
      throw <| IO.userError "usage: KernelReplay.lean MODULE [EXPECTED_PUBLIC_NAME ...]"
    let sysroot ← findSysroot
    initSearchPath sysroot
    IO.println s!"SYSROOT: {sysroot}"
    checkModule mod.toName expected
    return 0
  catch e =>
    (← IO.getStdout).flush
    IO.eprintln s!"KERNEL_REPLAY_FAIL: {e}"
    return 1

end
