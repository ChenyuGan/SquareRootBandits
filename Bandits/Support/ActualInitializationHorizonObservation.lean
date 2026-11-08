/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationHorizonMeasurability

/-!
# Agreement of the actual initialization observation with its run

The observer below assembles only the existing observational coordinates. Its
branches use the actual prelaunch slice and its actual initialized successor.
The mathematical evidence is `07_public_setup.tex:55-114,144-164`,
`appendix_b_communication.tex:94-131,160-165`, and
`06_interruptions.tex:235-297`, under `sources/zip4/manuscript/`.
This is internal deterministic mathematics, with fixed whole grid rewards.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationBlockFoldMeasurability
open Bandits.Support.ActualInitializationBlockFoldExact
open Bandits.Support.ActualInitializationBlockHandoffMeasurability
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability
open Bandits.Support.ActualInitializationStepMeasurability

namespace Bandits.Support.ActualInitializationHorizonObservation

open ActualInitializationHorizonMeasurability
open ActualInitializationHorizon
open ActualInitializationRun

variable {p : ActualInitializationHorizon.Parameters} {rate : ActualInitializationHorizonMeasurability.RateInput p}
  {C_star C_h : ℝ} {rewards : ActualInitializationHorizonMeasurability.GridRewardTable p}

/-- Finite coordinate assembly, using the original remaining-block measure. -/
def observeAux : (fuel : ℕ) → (block : Fin (n_boot p)) →
    n_boot p - block.val = fuel → BlockInput p rate block C_star C_h →
      RunTailObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
  | 0, block, hmeasure, _ => by
      have h := block.isLt
      omega
  | fuel + 1, block, hmeasure, input => by
      classical
      by_cases hnext : block.val + 1 < n_boot p
      · have hm : n_boot p - (ActualInitializationRun.successorBlock p block hnext).val = fuel := by
          simp only [ActualInitializationRun.successorBlock]
          omega
        by_cases hpre : input ∈ actualBlockPrelaunchSet
            (p := p) (rate := rate) (block := block)
            (C_star := C_star) (C_h := C_h) rewards
        · exact continuedRunTailObservation block
            (continuedBlockTraceOfPrelaunch block hnext rewards ⟨input, hpre⟩)
            (observeAux fuel (ActualInitializationRun.successorBlock p block hnext) hm
              (actualSuccessorBlockInput block hnext rewards ⟨input, hpre⟩))
        · exact terminalRunTailObservation block
            (terminalBlockTraceOfInput (rewards := rewards) block input)
      · exact terminalRunTailObservation block
          (terminalBlockTraceOfInput (rewards := rewards) block input)

/-- The same original source and fixed-constant incoming carry are retained. -/
def runFromObservation (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    RunFromObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block :=
  ⟨input.1, input.2, observeAux (rewards := rewards)
    (n_boot p - block.val) block rfl input⟩

/-- The successor is H's actual branch, on the original source and carry. -/
theorem successor_branch {block : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) :
    (ActualInitializationRun.combinedBoundaryHandoff p rate block input.1.1 rewards
      input.1.2.1.C_star input.1.2.1.C_h
      (ActualInitializationRun.foldBlock p rate block input.1.1 rewards input.1.2.1)).disposition =
        .continueNext (ActualInitializationRun.successorBlock p block hnext)
          (actualSuccessorBlockInput block hnext rewards input).2.1 := by
  obtain ⟨next, carry, hd, hn, hc, _, _⟩ :=
    actualPrelaunchInput_handoff_continueNext hnext input
  subst next
  have hc' := eq_of_heq hc
  rw [hc'] at hd
  rw [actualBlockHandoffOfInput_eq_runFromInput input.1] at hd
  exact hd

/-- This literal projection retains every dependent terminal data field. -/
def terminalData {source : BootstrapPrivateRoundStreams.SourceInput p} {block : Fin (n_boot p)}
    {carry : ActualInitializationRun.BlockCarry p rate block}
    (run : ActualInitializationHorizon.RunSuffix p rate source rewards block carry) :
    Σ terminal : Fin (n_boot p), Σ star : ℝ, Σ ch : ℝ,
      ActualInitializationRun.BlockFoldOutput p rate terminal source rewards star ch 0 ×
        ActualInitializationRun.CombinedBoundaryHandoff p rate terminal source ×
          ActualInitializationRun.BoundaryDisposition p rate terminal :=
  ⟨run.terminalBlock, run.terminalC_star, run.terminalC_h,
    run.terminalFold, run.terminalHandoff, run.terminalDisposition⟩

/-- Literal projections, used to avoid discarding dependent terminal fields. -/
def runData {source : BootstrapPrivateRoundStreams.SourceInput p} {block : Fin (n_boot p)}
    {carry : ActualInitializationRun.BlockCarry p rate block}
    (run : ActualInitializationHorizon.RunSuffix p rate source rewards block carry) :=
  (terminalData run, run.records, run.continuedBlocks)

private theorem transport_eq_apply {ι : Sort*} {α : Sort*} {a b c : ι}
    (h : a = b) (f : c = a → α) (g : c = b) :
    (Eq.ndrec (motive := fun x => c = x → α) f h) g =
      f (g.trans h.symm) := by
  cases h
  rfl

private theorem disposition_cases_continue {block : Fin (n_boot p)} {α : Sort*}
    (d : ActualInitializationRun.BoundaryDisposition p rate block)
    (hc : ∀ next carry, d = .continueNext next carry → α)
    (hl : ∀ launch seed, d = .launched launch seed → α)
    (he : ∀ live, d = .exhausted live → α)
    (next : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate next)
    (hd : d = .continueNext next carry) :
    (ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun x => d = x → α) d hc hl he rfl) = hc next carry hd := by
  cases hd
  rfl

private theorem disposition_cases_launched {block : Fin (n_boot p)} {α : Sort*}
    (d : ActualInitializationRun.BoundaryDisposition p rate block)
    (hc : ∀ next carry, d = .continueNext next carry → α)
    (hl : ∀ launch seed, d = .launched launch seed → α)
    (he : ∀ live, d = .exhausted live → α)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hd : d = .launched launch seed) :
    (ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun x => d = x → α) d hc hl he rfl) = hl launch seed hd := by
  cases hd
  rfl

private theorem disposition_cases_exhausted {block : Fin (n_boot p)} {α : Sort*}
    (d : ActualInitializationRun.BoundaryDisposition p rate block)
    (hc : ∀ next carry, d = .continueNext next carry → α)
    (hl : ∀ launch seed, d = .launched launch seed → α)
    (he : ∀ live, d = .exhausted live → α)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hd : d = .exhausted live) :
    (ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun x => d = x → α) d hc hl he rfl) = he live hd := by
  cases hd
  rfl

theorem runData_continue {source : BootstrapPrivateRoundStreams.SourceInput p} {block : Fin (n_boot p)}
    (carry : ActualInitializationRun.BlockCarry p rate block) (next : Fin (n_boot p))
    (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (hd : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      carry.C_star carry.C_h (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition =
        .continueNext next nextCarry) :
    runData (ActualInitializationHorizon.runFrom p rate source rewards block carry) =
      (terminalData (ActualInitializationHorizon.runFrom p rate source rewards next nextCarry),
        (ActualInitializationRun.foldBlock p rate block source rewards carry).records ++
          (ActualInitializationHorizon.runFrom p rate source rewards next nextCarry).records,
        ({
          block := block
          carry := carry
          next := next
          nextCarry := nextCarry
          branch_eq := hd } : ActualInitializationHorizon.ContinuedBlockExecution p rate source rewards) ::
            (ActualInitializationHorizon.runFrom p rate source rewards next nextCarry).continuedBlocks) := by
  rw [ActualInitializationHorizon.runFrom]
  rw [disposition_cases_continue _ _ _ _ next nextCarry hd]
  rw [transport_eq_apply]
  rfl

theorem runData_stop {source : BootstrapPrivateRoundStreams.SourceInput p} {block : Fin (n_boot p)}
    (carry : ActualInitializationRun.BlockCarry p rate block)
    (hs : ∀ next nextCarry,
      (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        carry.C_star carry.C_h (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition ≠
          .continueNext next nextCarry) :
    runData (ActualInitializationHorizon.runFrom p rate source rewards block carry) =
      (⟨block, carry.C_star, carry.C_h,
        ActualInitializationRun.foldBlock p rate block source rewards carry,
        ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards carry.C_star carry.C_h
          (ActualInitializationRun.foldBlock p rate block source rewards carry),
        (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards carry.C_star carry.C_h
          (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition⟩,
        (ActualInitializationRun.foldBlock p rate block source rewards carry).records, []) := by
  cases hd : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      carry.C_star carry.C_h
      (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition with
  | continueNext next nextCarry => exact (hs next nextCarry hd).elim
  | launched launch seed =>
      rw [ActualInitializationHorizon.runFrom]
      rw [disposition_cases_launched _ _ _ _ launch seed hd]
      rw [transport_eq_apply]
      simp only [runData, terminalData]
  | exhausted live =>
      rw [ActualInitializationHorizon.runFrom]
      rw [disposition_cases_exhausted _ _ _ _ live hd]
      rw [transport_eq_apply]
      simp only [runData, terminalData]

theorem stopped_of_not_prelaunch {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h)
    (hs : ¬(block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
      (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards)) :
    ∀ next nextCarry,
      (ActualInitializationRun.combinedBoundaryHandoff p rate block input.1 rewards
        input.2.1.C_star input.2.1.C_h
        (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1)).disposition ≠
          .continueNext next nextCarry := by
  intro next nextCarry hd
  have hf := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
    (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1) next nextCarry hd
  have hn : block.val + 1 < n_boot p := by
    have h := next.isLt
    omega
  apply hs
  refine ⟨hn, (actualBlockPrelaunchSet_iff_handoff_continueNext hn input).mpr ?_⟩
  rw [← actualBlockHandoffOfInput_eq_runFromInput input] at hd
  exact ⟨next, nextCarry, hd⟩

/-- On a real successor/prelaunch slice, the observer prepends exactly that block. -/
theorem observeAux_continue {fuel : ℕ} {block : Fin (n_boot p)}
    (hm : n_boot p - block.val = fuel + 1)
    (hnext : block.val + 1 < n_boot p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards) :
    observeAux (rewards := rewards) (fuel + 1) block hm input.1 =
      continuedRunTailObservation block
        (continuedBlockTraceOfPrelaunch block hnext rewards input)
        (observeAux (rewards := rewards) fuel (successorBlock p block hnext) (by
          simp only [successorBlock]
          omega) (actualSuccessorBlockInput block hnext rewards input)) := by
  classical
  simp only [observeAux, dite_eq_left hnext, dite_eq_left input.2]

/-- Both actual stopping dispositions retain the complete terminal trace. -/
theorem observeAux_stop {fuel : ℕ} {block : Fin (n_boot p)}
    (hm : n_boot p - block.val = fuel + 1)
    (input : BlockInput p rate block C_star C_h)
    (hs : ¬(block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
      (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards)) :
    observeAux (rewards := rewards) (fuel + 1) block hm input =
      terminalRunTailObservation block
        (terminalBlockTraceOfInput (rewards := rewards) block input) := by
  classical
  by_cases hn : block.val + 1 < n_boot p
  · have hp : input ∉ actualBlockPrelaunchSet (p := p) (rate := rate)
        (block := block) (C_star := C_star) (C_h := C_h) rewards :=
      fun hp => hs ⟨hn, hp⟩
    simp only [observeAux, dite_eq_left hn, dite_eq_right hp]
  · simp only [observeAux, dite_eq_right hn]

/-- The last NEXT carry, or the original carry for an empty continuation list.
This is a literal projection of H's entries, not another protocol recursion. -/
def finalCarriedInput {source : BootstrapPrivateRoundStreams.SourceInput p}
    (initial : Σ b : Fin (n_boot p), BlockCarry p rate b)
    (executions : List (ContinuedBlockExecution p rate source rewards)) :=
  executions.foldl (fun _ execution => ⟨execution.next, execution.nextCarry⟩) initial

/-- Terminal identity retains a genuinely reached carry on the original source.
The equality of dependent tuples identifies the full fold and full handoff,
including disposition, rather than only their terminal indices. -/
theorem observeAux_terminal (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h),
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      (observeAux (rewards := rewards) fuel block hm input).terminalBlock = terminal ∧
      (observeAux (rewards := rewards) fuel block hm input).terminalEntries =
        (terminalRunTailObservation terminal
          (terminalBlockTraceOfInput (rewards := rewards) terminal (input.1, carry))).terminalEntries ∧
      terminalData (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1) =
        ⟨terminal, carry.1.C_star, carry.1.C_h,
          foldBlock p rate terminal input.1 rewards carry.1,
          combinedBoundaryHandoff p rate terminal input.1 rewards carry.1.C_star carry.1.C_h
            (foldBlock p rate terminal input.1 rewards carry.1),
          (combinedBoundaryHandoff p rate terminal input.1 rewards carry.1.C_star carry.1.C_h
            (foldBlock p rate terminal input.1 rewards carry.1)).disposition⟩ ∧
      finalCarriedInput ⟨block, input.2.1⟩
        (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks =
          ⟨terminal, carry.1⟩ := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        obtain ⟨terminal, carry, hb, ht, hd, hcarry⟩ :=
          ih (successorBlock p block hs.1) hm'
            (actualSuccessorBlockInput block hs.1 rewards pre)
        have hr := congrArg Prod.fst
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        rw [observeAux_continue hm hs.1 pre]
        refine ⟨terminal, carry, hb, ht, hr.trans hd, ?_⟩
        have hc := congrArg (fun data => data.2.2)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks = _ at hc
        rw [hc]
        exact hcarry
      · rw [observeAux_stop hm input hs]
        have hr := runData_stop input.2.1 (stopped_of_not_prelaunch input hs)
        refine ⟨block, input.2, rfl, rfl, congrArg Prod.fst hr, ?_⟩
        have hc := congrArg (fun data => data.2.2) hr
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks = [] at hc
        rw [hc]
        rfl

/-- Full SAME-block code, with the original block fibre included. -/
def fullRecordCode {source : BootstrapPrivateRoundStreams.SourceInput p}
    (record : PhysicalRoundRecord p rate source rewards) :
    FullPhysicalRoundCode (p := p) (rate := rate) :=
  ⟨record.block, physicalRoundCode C_star C_h record⟩

/-- Reading the stored per-block lists is a literal observation projection. -/
def blockRoundCodes
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (block : Fin (n_boot p)) :
    List (FullPhysicalRoundCode (p := p) (rate := rate)) :=
  match observation.continuedEntries block with
  | .inr ⟨tag, trace⟩ => trace.blockCode.1.rounds.map (Sigma.mk tag)
  | .inl _ => match observation.terminalEntries block with
    | .inr ⟨tag, trace⟩ => trace.blockCode.1.rounds.map (Sigma.mk tag)
    | .inl _ => []

private theorem tagged_physicalRoundCodes
    {source : BootstrapPrivateRoundStreams.SourceInput p} {block : Fin (n_boot p)}
    (records : List (PhysicalRoundRecord p rate source rewards))
    (hb : ∀ record ∈ records, record.block = block) :
    (physicalRoundCodes C_star C_h records hb).map (Sigma.mk block) =
      records.map (fullRecordCode (C_star := C_star) (C_h := C_h)) := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      have hr := hb record (by simp only [List.mem_cons, true_or])
      subst block
      simp only [physicalRoundCodes, List.pmap_cons, List.map_cons]
      congr 1
      exact ih (fun r h => hb r (List.mem_cons_of_mem _ h))

/-- The accepted block reconstruction supplies the entire tagged record list. -/
theorem terminalTrace_roundCodes {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    (terminalBlockTraceOfInput (rewards := rewards) block input).blockCode.1.rounds.map
        (Sigma.mk block) =
      (foldBlock p rate block input.1 rewards input.2.1).records.map
        (fullRecordCode (C_star := C_star) (C_h := C_h)) := by
  rw [← terminalBlockChronologicalRoundCodes,
    terminalBlockChronologicalRoundCodes_eq_physicalRecords _ rewards input rfl]
  exact tagged_physicalRoundCodes _ _

/-- Full carried data in one stored continuation entry; only certificates are omitted. -/
def continuedTracePayload {block : Fin (n_boot p)}
    (trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :
    Σ b : Fin (n_boot p), BlockCarry p rate b ×
      (Fin (n_boot p) × (Σ next : Fin (n_boot p), BlockCarry p rate next)) :=
  ⟨block, trace.carry.1, trace.nextBlock, trace.nextCarry.1, trace.nextCarry.2.1⟩

/-- The corresponding literal projection of H's actual execution, including NEXT carry. -/
def executionPayload {source : BootstrapPrivateRoundStreams.SourceInput p}
    (execution : ContinuedBlockExecution p rate source rewards) :
    Σ b : Fin (n_boot p), BlockCarry p rate b ×
      (Fin (n_boot p) × (Σ next : Fin (n_boot p), BlockCarry p rate next)) :=
  ⟨execution.block, execution.carry, execution.next, execution.next, execution.nextCarry⟩

def continuedEntryPayload
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (block : Fin (n_boot p)) :
    Unit ⊕ (Σ b : Fin (n_boot p), BlockCarry p rate b ×
      (Fin (n_boot p) × (Σ next : Fin (n_boot p), BlockCarry p rate next))) :=
  match observation.continuedEntries block with
  | .inl _ => .inl ()
  | .inr ⟨_, trace⟩ => .inr (continuedTracePayload trace)

/-- Literal lookup in the original ordered execution list. -/
def executionEntryPayload {source : BootstrapPrivateRoundStreams.SourceInput p}
    (executions : List (ContinuedBlockExecution p rate source rewards))
    (other : Fin (n_boot p)) :
    Unit ⊕ (Σ b : Fin (n_boot p), BlockCarry p rate b ×
      (Fin (n_boot p) × (Σ next : Fin (n_boot p), BlockCarry p rate next))) :=
  match executions.find? (fun execution => execution.block == other) with
  | none => .inl ()
  | some execution => .inr (executionPayload execution)

private theorem executionEntryPayload_cons_ne
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (execution : ContinuedBlockExecution p rate source rewards)
    (executions : List (ContinuedBlockExecution p rate source rewards))
    (other : Fin (n_boot p)) (ho : execution.block ≠ other) :
    executionEntryPayload (execution :: executions) other =
      executionEntryPayload executions other := by
  simp only [executionEntryPayload, List.find?_cons,
    beq_eq_false_iff_ne.mpr ho]

/-- Every continued slot is precisely the matching actual list entry, or absent.
The matched execution retains H's original `branch_eq` certificate. -/
theorem observeAux_continued (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)),
    continuedEntryPayload (observeAux (rewards := rewards) fuel block hm input) other =
      executionEntryPayload
        (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks
        other := by
  classical
  induction fuel with
  | zero =>
      intro block hm input other
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input other
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        have hc := congrArg (fun data => data.2.2)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks = _ at hc
        rw [observeAux_continue hm hs.1 pre, hc]
        by_cases ho : other = block
        · subst other
          simp only [continuedEntryPayload, continuedRunTailObservation,
            executionEntryPayload, List.find?_cons, beq_self_eq_true]
          rfl
        · rw [executionEntryPayload_cons_ne _ _ other (Ne.symm ho)]
          change continuedEntryPayload _ other = _
          simpa only [continuedEntryPayload, continuedRunTailObservation,
            dite_eq_right ho, actualSuccessorBlockInput, pre] using
            ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre) other
      · have hc := congrArg (fun data => data.2.2)
          (runData_stop input.2.1 (stopped_of_not_prelaunch input hs))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks = [] at hc
        rw [observeAux_stop hm input hs, hc]
        rfl

/-- Every physical record belongs to the current or a later actual block. -/
theorem runFrom_records_blocks_ge (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (_hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h),
    ∀ record ∈ (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records, block.val ≤ record.block.val := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input record hr
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        have hrecords := congrArg (fun data => data.2.1)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hrecords
        rw [hrecords, List.mem_append] at hr
        rcases hr with hr | hr
        · rw [foldBlock_records_block input.1 rewards input.2.1 record hr]
        · have h := ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre) record hr
          change block.val + 1 ≤ record.block.val at h
          omega
      · have hrecords := congrArg (fun data => data.2.1)
          (runData_stop input.2.1 (stopped_of_not_prelaunch input hs))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hrecords
        rw [hrecords] at hr
        rw [foldBlock_records_block input.1 rewards input.2.1 record hr]

private theorem blockRoundCodes_terminal {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) (other : Fin (n_boot p)) :
    blockRoundCodes (terminalRunTailObservation block trace) other =
      if other = block then trace.blockCode.1.rounds.map (Sigma.mk block) else [] := by
  classical
  by_cases ho : other = block
  · simp [blockRoundCodes, terminalRunTailObservation, ho]
  · simp only [blockRoundCodes, terminalRunTailObservation, dite_eq_right ho, ite_eq_right ho]

private theorem blockRoundCodes_continue {block : Fin (n_boot p)}
    (trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)
    (tail : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (other : Fin (n_boot p)) :
    blockRoundCodes (continuedRunTailObservation block trace tail) other =
      if other = block then trace.blockCode.1.rounds.map (Sigma.mk block)
      else blockRoundCodes tail other := by
  classical
  by_cases ho : other = block
  · simp [blockRoundCodes, continuedRunTailObservation, ho]
  · simp only [blockRoundCodes, continuedRunTailObservation, dite_eq_right ho, ite_eq_right ho]

private theorem fold_records_filter {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)) :
    (foldBlock p rate block input.1 rewards input.2.1).records.filter
        (fun record => record.block == other) =
      if other = block then (foldBlock p rate block input.1 rewards input.2.1).records
      else [] := by
  classical
  by_cases ho : other = block
  · subst other
    rw [ite_eq_left rfl]
    apply List.filter_eq_self.mpr
    intro record hr
    simp only [foldBlock_records_block input.1 rewards input.2.1 record hr, beq_self_eq_true]
  · rw [ite_eq_right ho]
    apply List.filter_eq_nil_iff.mpr
    intro record hr
    simpa only [foldBlock_records_block input.1 rewards input.2.1 record hr, beq_iff_eq]
      using Ne.symm ho

/-- Complete per-block code agreement, with every nonoccurring block filtered
out of H's actual physical records. No round or continuous payload is discarded. -/
theorem observeAux_blockRoundCodes (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)),
    blockRoundCodes (observeAux (rewards := rewards) fuel block hm input) other =
      ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.filter
        (fun record => record.block == other)).map
          (fullRecordCode (C_star := C_star) (C_h := C_h)) := by
  classical
  induction fuel with
  | zero =>
      intro block hm input other
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input other
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        have hr := congrArg (fun data => data.2.1)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [observeAux_continue hm hs.1 pre, blockRoundCodes_continue, hr,
          List.filter_append, List.map_append, fold_records_filter input other]
        dsimp only [pre, actualSuccessorBlockInput] at *
        by_cases ho : other = block
        · subst other
          have ht : ((ActualInitializationHorizon.runFrom p rate input.1 rewards
              (successorBlock p block hs.1)
              (actualSuccessorBlockInput block hs.1 rewards pre).2.1).records.filter
                (fun record => record.block == block)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro record hrecord
            have hb := runFrom_records_blocks_ge fuel _ hm'
              (actualSuccessorBlockInput block hs.1 rewards pre) record hrecord
            change block.val + 1 ≤ record.block.val at hb
            simp only [beq_iff_eq]
            intro he
            have hv := congrArg Fin.val he
            omega
          simp only [ite_true]
          have ht' := ht
          simp only [actualSuccessorBlockInput] at ht'
          dsimp only [pre, actualSuccessorBlockInput] at *
          rw [ht']
          simp only [List.map_nil, List.append_nil]
          exact terminalTrace_roundCodes (rewards := rewards) input
        · simp only [ite_eq_right ho, List.map_nil, List.nil_append]
          exact ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre) other
      · have hr := congrArg (fun data => data.2.1)
          (runData_stop input.2.1 (stopped_of_not_prelaunch input hs))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [observeAux_stop hm input hs, blockRoundCodes_terminal, hr,
          fold_records_filter input other]
        by_cases ho : other = block
        · simp only [ite_eq_left ho]
          exact terminalTrace_roundCodes input
        · simp only [ite_eq_right ho, List.map_nil]

private theorem blockPhysicalRoundCodeAt_eq_coordinates {block : Fin (n_boot p)}
    (code : BlockFoldCode p rate block C_star C_h) (cursor : ℕ) :
    blockPhysicalRoundCodeAt block code cursor =
      (roundCodeListCoordinates (code.rounds.map (Sigma.mk block))).2 cursor := by
  unfold blockPhysicalRoundCodeAt roundCodeListCoordinates
  simp only [List.getElem?_map]
  cases h : code.rounds[cursor]? <;> rfl

/-- The whole indexed round stream is exactly the coordinate stream of the
same full stored per-block list, including absent positions. -/
theorem observeAux_round_stream (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)) (cursor : ℕ),
    (observeAux (rewards := rewards) fuel block hm input).physicalRoundCodes other cursor =
      (roundCodeListCoordinates
        (blockRoundCodes (observeAux (rewards := rewards) fuel block hm input) other)).2 cursor := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input other cursor
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        rw [observeAux_continue hm hs.1 pre, blockRoundCodes_continue]
        by_cases ho : other = block
        · subst other
          simp only [continuedRunTailObservation, ite_true]
          exact blockPhysicalRoundCodeAt_eq_coordinates _ cursor
        · simp only [continuedRunTailObservation, ite_eq_right ho]
          exact ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre) other cursor
      · rw [observeAux_stop hm input hs, blockRoundCodes_terminal]
        by_cases ho : other = block
        · subst other
          simp only [terminalRunTailObservation, ite_true]
          exact blockPhysicalRoundCodeAt_eq_coordinates _ cursor
        · simp only [terminalRunTailObservation, ite_eq_right ho, roundCodeListCoordinates,
            List.getElem?_nil]

/-- Calendar lookup of a stored block list. Out-of-calendar indices have no
slot; this creates no physical round at the exclusive horizon endpoint. -/
def roundCodesAtNat
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (index : ℕ) :
    List (FullPhysicalRoundCode (p := p) (rate := rate)) :=
  if h : index < n_boot p then blockRoundCodes observation ⟨index, h⟩ else []

/-- Chronological concatenation is a literal scan in the original block order. -/
def chronologicalRoundCodes (block : Fin (n_boot p))
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) :=
  (consecutiveNat block.val (n_boot p - block.val)).flatMap (roundCodesAtNat observation)

private theorem roundCodesAtNat_continue_ne {block : Fin (n_boot p)}
    (trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)
    (tail : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (index : ℕ) (hn : index ≠ block.val) :
    roundCodesAtNat (continuedRunTailObservation block trace tail) index =
      roundCodesAtNat tail index := by
  classical
  by_cases hi : index < n_boot p
  · have he : (⟨index, hi⟩ : Fin (n_boot p)) ≠ block :=
      fun h => hn (congrArg Fin.val h)
    simp only [roundCodesAtNat, dite_eq_left hi, blockRoundCodes_continue, ite_eq_right he]
  · simp only [roundCodesAtNat, dite_eq_right hi]

private theorem roundCodesAtNat_terminal_ne {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)
    (index : ℕ) (hn : index ≠ block.val) :
    roundCodesAtNat (terminalRunTailObservation block trace) index = [] := by
  classical
  by_cases hi : index < n_boot p
  · have he : (⟨index, hi⟩ : Fin (n_boot p)) ≠ block :=
      fun h => hn (congrArg Fin.val h)
    simp only [roundCodesAtNat, dite_eq_left hi, blockRoundCodes_terminal, ite_eq_right he]
  · simp only [roundCodesAtNat, dite_eq_right hi]

/-- Concatenation uses H's actual append equation and the strictly later
successor index. There is no supplied valid-code or nonoverlap assumption. -/
theorem observeAux_chronological (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h),
    (consecutiveNat block.val fuel).flatMap
        (roundCodesAtNat (observeAux (rewards := rewards) fuel block hm input)) =
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
        (fullRecordCode (C_star := C_star) (C_h := C_h)) := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        have hr := congrArg (fun data => data.2.1)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [observeAux_continue hm hs.1 pre, consecutiveNat, List.flatMap_cons, hr,
          List.map_append]
        have hrest : (consecutiveNat (block.val + 1) fuel).flatMap
            (roundCodesAtNat (continuedRunTailObservation block
              (continuedBlockTraceOfPrelaunch block hs.1 rewards pre)
              (observeAux (rewards := rewards) fuel (successorBlock p block hs.1) hm'
                (actualSuccessorBlockInput block hs.1 rewards pre)))) =
            (consecutiveNat (block.val + 1) fuel).flatMap
              (roundCodesAtNat (observeAux (rewards := rewards) fuel
                (successorBlock p block hs.1) hm'
                (actualSuccessorBlockInput block hs.1 rewards pre))) := by
          apply List.flatMap_congr
          intro index hi
          have hn := (consecutiveNat_mem_iff _ _ _).mp hi
          exact roundCodesAtNat_continue_ne _ _ index (by omega)
        rw [hrest]
        simp only [roundCodesAtNat, dite_eq_left block.isLt, blockRoundCodes_continue]
        rw [show (continuedBlockTraceOfPrelaunch block hs.1 rewards pre).blockCode.1.rounds.map
            (Sigma.mk block) = (foldBlock p rate block input.1 rewards input.2.1).records.map
              (fullRecordCode (C_star := C_star) (C_h := C_h)) from
            terminalTrace_roundCodes (rewards := rewards) input]
        congr 1
        exact ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre)
      · have hr := congrArg (fun data => data.2.1)
          (runData_stop input.2.1 (stopped_of_not_prelaunch input hs))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [observeAux_stop hm input hs, consecutiveNat, List.flatMap_cons, hr]
        have hrest : (consecutiveNat (block.val + 1) fuel).flatMap
            (roundCodesAtNat (terminalRunTailObservation block
              (terminalBlockTraceOfInput (rewards := rewards) block input))) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro index hi
          have hn := (consecutiveNat_mem_iff _ _ _).mp hi
          exact roundCodesAtNat_terminal_ne _ index (by omega)
        rw [hrest, List.append_nil]
        simp only [roundCodesAtNat, dite_eq_left block.isLt, blockRoundCodes_terminal]
        exact terminalTrace_roundCodes (rewards := rewards) input

/-- Full simultaneous action projection, retaining the physical error tag. -/
def fullActionEntry (code : FullPhysicalRoundCode (p := p) (rate := rate)) :
    Unit ⊕ FiniteBanditModel.ActionProfile p.m p.K :=
  Sum.elim (fun _ => .inl ()) (fun successful => .inr successful.2.1.1) code.2

/-- Full denominator-D feedback projection, with the same physical error tag. -/
def fullFeedbackEntry (code : FullPhysicalRoundCode (p := p) (rate := rate)) :
    Unit ⊕ (Fin p.m → Fin (D p + 1)) :=
  Sum.elim (fun _ => .inl ()) (fun successful => .inr successful.2.1.2) code.2

def fullOwnEntry (player : Fin p.m)
    (code : FullPhysicalRoundCode (p := p) (rate := rate)) :=
  physicalOwnEntryFromActualRoundOutput rate code.1 code.2 player

/-- Both chronological histories project the same full physical codes. -/
def chronologicalActionFeedbackHistory (block : Fin (n_boot p))
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) :=
  ((chronologicalRoundCodes block observation).map fullActionEntry,
    (chronologicalRoundCodes block observation).map fullFeedbackEntry)

def chronologicalOwnHistory (block : Fin (n_boot p))
    (observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) (player : Fin p.m) :=
  (chronologicalRoundCodes block observation).map (fullOwnEntry player)

/-- A conditional internal list lemma. Its only mathematical input is the
explicit SAME-block projection identity `hfold`; each use below supplies A's
proved identity. It assumes no whole-run law or measurable run. -/
private theorem runFrom_map_codes {α : Type*}
    (f : FullPhysicalRoundCode (p := p) (rate := rate) → α)
    (g : {source : BootstrapPrivateRoundStreams.SourceInput p} →
      PhysicalRoundRecord p rate source rewards → α)
    (hfold : ∀ (block : Fin (n_boot p)) (input : BlockInput p rate block C_star C_h),
      ((foldBlock p rate block input.1 rewards input.2.1).records.map
        (fullRecordCode (C_star := C_star) (C_h := C_h))).map f =
        (foldBlock p rate block input.1 rewards input.2.1).records.map g)
    (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (_hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h),
    ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
      (fullRecordCode (C_star := C_star) (C_h := C_h))).map f =
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map g := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        have hr := congrArg (fun data => data.2.1)
          (runData_continue input.2.1 _ _ (successor_branch hs.1 pre))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [hr, List.map_append, List.map_append, List.map_append, hfold block input]
        congr 1
        exact ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre)
      · have hr := congrArg (fun data => data.2.1)
          (runData_stop input.2.1 (stopped_of_not_prelaunch input hs))
        change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records = _ at hr
        rw [hr]
        exact hfold block input

/-- The full chronological list equals the physical encodings of H's original
records. This consumes the actual observer/run agreement, not another code run. -/
theorem runFrom_chronologicalRoundCodes (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    chronologicalRoundCodes block
        (runFromObservation (rewards := rewards) block input).suffix =
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
        (fullRecordCode (C_star := C_star) (C_h := C_h)) :=
  observeAux_chronological (n_boot p - block.val) block rfl input

/-- Full simultaneous actions and grid feedback in H's original physical order. -/
theorem runFrom_actionFeedbackHistory (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    chronologicalActionFeedbackHistory block
        (runFromObservation (rewards := rewards) block input).suffix =
      (((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
          (fun record => Sum.inr record.result.actions)),
        ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
          (fun record => Sum.inr record.result.feedback))) := by
  unfold chronologicalActionFeedbackHistory
  rw [runFrom_chronologicalRoundCodes]
  apply Prod.ext
  · apply runFrom_map_codes fullActionEntry (fun record => Sum.inr record.result.actions)
      ?_ (n_boot p - block.val) block rfl input
    intro b x
    rw [← terminalTrace_roundCodes (rewards := rewards) x]
    simpa only [terminalBlockActionFeedbackHistory, BlockFoldCode.actions,
      List.map_map, Function.comp_def, fullActionEntry, PhysicalRoundRecord.actions] using
      congrArg Prod.fst (terminalBlockActionFeedbackHistory_eq_physicalRecords rewards x)
  · apply runFrom_map_codes fullFeedbackEntry (fun record => Sum.inr record.result.feedback)
      ?_ (n_boot p - block.val) block rfl input
    intro b x
    rw [← terminalTrace_roundCodes (rewards := rewards) x]
    simpa only [terminalBlockActionFeedbackHistory, BlockFoldCode.feedback,
      List.map_map, Function.comp_def, fullFeedbackEntry, PhysicalRoundRecord.feedback] using
      congrArg Prod.snd (terminalBlockActionFeedbackHistory_eq_physicalRecords rewards x)

/-- Each player's own history is projected from the same chronological codes. -/
theorem runFrom_ownHistory (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) (player : Fin p.m) :
    chronologicalOwnHistory block
        (runFromObservation (rewards := rewards) block input).suffix player =
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.map
        (fun record => Sum.inr (record.result.actions player, record.result.feedback player)) := by
  unfold chronologicalOwnHistory
  rw [runFrom_chronologicalRoundCodes]
  apply runFrom_map_codes (fullOwnEntry player)
    (fun record => Sum.inr (record.result.actions player, record.result.feedback player))
    ?_ (n_boot p - block.val) block rfl input
  intro b x
  rw [← terminalTrace_roundCodes (rewards := rewards) x]
  simpa only [terminalBlockOwnHistory, List.map_map, Function.comp_def, fullOwnEntry] using
    terminalBlockOwnHistory_eq_physicalRecords rewards x player

/-- Complete terminal reconstruction at the actual reached input. The fold
identity uses A's stored-code decoder and the handoff identity uses A's stored
combined observation. BOTH constants and consumed count are retained. -/
theorem runFrom_terminal_reconstruction (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    let observation := runFromObservation (rewards := rewards) block input
    let run := ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      let trace := terminalBlockTraceOfInput (rewards := rewards) terminal (input.1, carry)
      observation.suffix.terminalBlock = terminal ∧
      observation.suffix.terminalEntries =
        (terminalRunTailObservation terminal trace).terminalEntries ∧
      finalCarriedInput ⟨block, input.2.1⟩ run.continuedBlocks = ⟨terminal, carry.1⟩ ∧
      trace.carry = carry ∧ trace.terminalC_star = run.terminalC_star ∧
      trace.terminalC_h = run.terminalC_h ∧
      trace.consumed = (foldBlock p rate terminal input.1 rewards carry.1).consumed ∧
      decodeBlockFoldCodeOfInput rewards (input.1, carry) trace.blockCode.1 =
        some (foldBlock p rate terminal input.1 rewards carry.1) ∧
      terminalData run =
        ⟨terminal, carry.1.C_star, carry.1.C_h,
          foldBlock p rate terminal input.1 rewards carry.1,
          combinedBoundaryHandoffOfObservation trace.blockCode.2,
          (combinedBoundaryHandoffOfObservation trace.blockCode.2).disposition⟩ := by
  dsimp only
  obtain ⟨terminal, carry, hb, ht, hd, hc⟩ :=
    observeAux_terminal (rewards := rewards) (n_boot p - block.val) block rfl input
  have hstar := (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalC_star_eq.trans input.2.2.1
  have hch := (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalC_h_eq.trans input.2.2.2
  have hcoords := terminalBlockTraceOfInput_input_coordinates rewards (input.1, carry)
  refine ⟨terminal, carry, hb, ht, hc, hcoords.1,
    hcoords.2.1.trans hstar.symm, hcoords.2.2.trans hch.symm,
    terminalBlockTraceOfInput_consumed_eq_fold rewards (input.1, carry),
    terminalBlockTraceOfInput_reconstructs_fold rewards terminal (input.1, carry), ?_⟩
  have hh := terminalBlockTraceOfInput_reconstructs_handoff rewards terminal (input.1, carry)
  rw [actualBlockHandoffOfInput_eq_runFromInput (input.1, carry)] at hh
  rw [hh]
  exact hd

/-- Full indexed code agreement, including the outer absent-position tag. -/
theorem runFrom_round_stream (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)) (cursor : ℕ) :
    (runFromObservation (rewards := rewards) block input).suffix.physicalRoundCodes other cursor =
      (roundCodeListCoordinates
        (((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.filter
          (fun record => record.block == other)).map
            (fullRecordCode (C_star := C_star) (C_h := C_h)))).2 cursor := by
  rw [show (runFromObservation (rewards := rewards) block input).suffix =
      observeAux (rewards := rewards) (n_boot p - block.val) block rfl input from rfl,
    observeAux_round_stream, observeAux_blockRoundCodes]

private theorem consecutiveNat_nodup (start count : ℕ) :
    (consecutiveNat start count).Nodup := by
  induction count generalizing start with
  | zero => exact List.nodup_nil
  | succ count ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih (start + 1)⟩
      intro hm
      have h := (consecutiveNat_mem_iff _ _ _).mp hm
      omega

/-- H's original increasing indices ensure that a block occurs at most once. -/
theorem runFrom_continued_indices (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    let run := ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1
    run.continuedBlocks.map (fun execution => execution.block.val) =
      consecutiveNat block.val run.continuedBlocks.length ∧
    (run.continuedBlocks.map (fun execution => execution.block.val)).Nodup := by
  dsimp only
  refine ⟨(ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlockIndex, ?_⟩
  rw [(ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlockIndex]
  exact consecutiveNat_nodup _ _

/-- The observed continuation payloads appear in exactly H's original order.
The carried data determine the actual execution, whose `branch_eq` is retained
in H's list. Numerical and saved-real fields are never identified by proof irrelevance. -/
theorem runFrom_continued_order (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    let observation := runFromObservation (rewards := rewards) block input
    let run := ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1
    run.continuedBlocks.map (fun execution =>
      continuedEntryPayload observation.suffix execution.block) =
        run.continuedBlocks.map (fun execution => Sum.inr (executionPayload execution)) := by
  dsimp only
  apply List.map_congr_left
  intro execution he
  rw [show (runFromObservation (rewards := rewards) block input).suffix =
      observeAux (rewards := rewards) (n_boot p - block.val) block rfl input from rfl,
    observeAux_continued]
  have hn := (runFrom_continued_indices (rewards := rewards) block input).2
  have hf : ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks.find? (fun entry => entry.block == execution.block)) = some execution := by
    cases hfind : ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks.find? (fun entry => entry.block == execution.block)) with
    | none =>
        have hnone := List.find?_eq_none.mp hfind execution he
        simp only [beq_self_eq_true, not_true_eq_false] at hnone
    | some found =>
        have hm := List.mem_of_find?_eq_some hfind
        have hb := List.find?_some hfind
        have heq : found = execution := List.inj_on_of_nodup_map hn hm he
          (congrArg Fin.val (beq_iff_eq.mp hb))
        exact congrArg some heq
  simp only [executionEntryPayload, hf]

/-- An absent continuation slot is exactly a block absent from H's actual list. -/
theorem runFrom_continued_absent (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)) :
    (runFromObservation (rewards := rewards) block input).suffix.continuedEntries other = .inl () ↔
      ∀ execution ∈ (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks, execution.block ≠ other := by
  have heq := observeAux_continued (rewards := rewards)
    (n_boot p - block.val) block rfl input other
  change continuedEntryPayload
      (runFromObservation (rewards := rewards) block input).suffix other = _ at heq
  have habsent : (runFromObservation (rewards := rewards) block input).suffix.continuedEntries
      other = .inl () ↔ continuedEntryPayload
        (runFromObservation (rewards := rewards) block input).suffix other = .inl () := by
    unfold continuedEntryPayload
    cases (runFromObservation (rewards := rewards) block input).suffix.continuedEntries other with
    | inl u =>
        cases u
        simp
    | inr trace => simp only [Sum.inr_ne_inl]
  rw [habsent, heq]
  have hlookup : executionEntryPayload
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks
      other = .inl () ↔
      ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks.find? (fun entry => entry.block == other)) = none := by
    unfold executionEntryPayload
    cases ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks.find? (fun entry => entry.block == other)) <;> simp
  rw [hlookup, List.find?_eq_none]
  simp only [beq_iff_eq]

/-- The literal execution payload determines the entire execution, including
its branch certificate. Only the final proof field uses proof irrelevance. -/
theorem executionPayload_injective {source : BootstrapPrivateRoundStreams.SourceInput p} :
    Function.Injective (executionPayload (p := p) (rate := rate)
      (source := source) (rewards := rewards)) := by
  rintro ⟨b, c, n, nc, hd⟩ ⟨b', c', n', nc', hd'⟩ h
  obtain ⟨hb, hp⟩ := Sigma.mk.inj_iff.mp h
  cases hb
  have hp' := eq_of_heq hp
  obtain ⟨hc, hn⟩ := Prod.mk.inj hp'
  cases hc
  obtain ⟨hn, hnc⟩ := Prod.mk.inj hn
  cases hn
  have hnc' := eq_of_heq (Sigma.mk.inj_iff.mp hnc).2
  cases hnc'
  rfl

private theorem observeAux_continued_code (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel)
      (input : BlockInput p rate block C_star C_h) (other tag : Fin (n_boot p))
      (trace : ContinuedBlockTrace (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) tag),
      (observeAux (rewards := rewards) fuel block hm input).continuedEntries other =
        .inr ⟨tag, trace⟩ →
      trace.blockCode = (terminalBlockTraceOfInput (rewards := rewards)
        tag (input.1, trace.carry)).blockCode := by
  classical
  induction fuel with
  | zero =>
      intro block hm input
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm input other tag trace hentry
      by_cases hs : block.val + 1 < n_boot p ∧ input ∈ actualBlockPrelaunchSet
          (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards
      · let pre : ActualBlockPrelaunchInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hs.2⟩
        have hm' : n_boot p - (successorBlock p block hs.1).val = fuel := by
          simp only [successorBlock]
          omega
        rw [observeAux_continue hm hs.1 pre] at hentry
        by_cases ho : other = block
        · simp only [continuedRunTailObservation, dite_eq_left ho] at hentry
          obtain ⟨hb, ht⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hentry)
          cases hb
          have ht' := eq_of_heq ht
          cases ht'
          rfl
        · simp only [continuedRunTailObservation, dite_eq_right ho] at hentry
          exact ih _ hm' (actualSuccessorBlockInput block hs.1 rewards pre)
            other tag trace hentry
      · rw [observeAux_stop hm input hs] at hentry
        cases hentry

/-- Every actual continued execution is stored, with its actual input and
NEXT carry, and carries its original `branch_eq`; no trace is supplied. -/
theorem runFrom_continued_reconstruction (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    let observation := runFromObservation (rewards := rewards) block input
    let run := ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1
    ∀ execution ∈ run.continuedBlocks,
      ∃ (tag : Fin (n_boot p))
        (trace : ContinuedBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) tag),
        observation.suffix.continuedEntries execution.block = .inr ⟨tag, trace⟩ ∧
        continuedTracePayload trace = executionPayload execution ∧
        trace.blockCode = (terminalBlockTraceOfInput (rewards := rewards)
          tag (input.1, trace.carry)).blockCode ∧
        decodeBlockFoldCodeOfInput rewards (input.1, trace.carry) trace.blockCode.1 =
          some (foldBlock p rate tag input.1 rewards trace.carry.1) ∧
        HEq (combinedBoundaryHandoffOfObservation trace.blockCode.2)
          (combinedBoundaryHandoff p rate tag input.1 rewards
            trace.carry.1.C_star trace.carry.1.C_h
            (foldBlock p rate tag input.1 rewards trace.carry.1)) ∧
        (combinedBoundaryHandoff p rate execution.block input.1 rewards
          execution.carry.C_star execution.carry.C_h
          (foldBlock p rate execution.block input.1 rewards execution.carry)).disposition =
            .continueNext execution.next execution.nextCarry := by
  dsimp only
  intro execution he
  have hp := List.map_inj_left.mp (runFrom_continued_order (rewards := rewards) block input)
    execution he
  unfold continuedEntryPayload at hp
  cases ht : (runFromObservation (rewards := rewards) block input).suffix.continuedEntries
      execution.block with
  | inl u => simp only [ht, Sum.inl_ne_inr] at hp
  | inr data =>
      rcases data with ⟨tag, trace⟩
      simp only [ht, Sum.inr.injEq] at hp
      have hcode := observeAux_continued_code (rewards := rewards)
        (n_boot p - block.val) block rfl input execution.block tag trace ht
      refine ⟨tag, trace, rfl, hp, hcode, ?_, ?_, execution.branch_eq⟩
      · rw [hcode]
        exact terminalBlockTraceOfInput_reconstructs_fold rewards tag (input.1, trace.carry)
      · rw [hcode]
        have hh := terminalBlockTraceOfInput_reconstructs_handoff rewards tag (input.1, trace.carry)
        rw [actualBlockHandoffOfInput_eq_runFromInput (input.1, trace.carry)] at hh
        exact heq_of_eq hh

/-- Equality of terminal indices is a consequence of the full terminal
reconstruction, not its substitute. -/
theorem runFrom_terminalBlock_eq (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    (runFromObservation (rewards := rewards) block input).suffix.terminalBlock =
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalBlock := by
  obtain ⟨terminal, carry, hb, _, hd, _⟩ :=
    observeAux_terminal (rewards := rewards) (n_boot p - block.val) block rfl input
  exact hb.trans (congrArg Sigma.fst hd).symm

/-- Exact original input coordinates, with no inferred matching-carry premise. -/
theorem runFrom_original_input_coordinates (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    (runFromObservation (rewards := rewards) block input).originalSource = input.1 ∧
    (runFromObservation (rewards := rewards) block input).initialCarry = input.2 :=
  ⟨rfl, rfl⟩

private theorem measurable_observeAux (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hm : n_boot p - block.val = fuel),
      Measurable (observeAux (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) fuel block hm) := by
  classical
  induction fuel with
  | zero =>
      intro block hm
      have hb := block.isLt
      omega
  | succ fuel ih =>
      intro block hm
      by_cases hn : block.val + 1 < n_boot p
      · have hm' : n_boot p - (successorBlock p block hn).val = fuel := by
          simp only [successorBlock]
          omega
        have hset := measurableSet_actualBlockPrelaunchSet (p := p) (rate := rate)
          (block := block) (C_star := C_star) (C_h := C_h) rewards
        have htrace := measurable_continuedBlockTraceOfPrelaunch (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) block hn
        have hnext := measurable_actualSuccessorBlockInput (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) block hn
        have htail := (ih (successorBlock p block hn) hm').comp hnext
        have hcontinue := (measurable_continuedRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block).comp (htrace.prodMk htail)
        have hstop := (measurable_terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block).comp
          ((measurable_terminalBlockTraceOfInput (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) block).comp
              (measurable_subtype_coe (p := fun x : BlockInput p rate block C_star C_h =>
                x ∉ actualBlockPrelaunchSet (p := p) (rate := rate) (block := block)
                  (C_star := C_star) (C_h := C_h) rewards)))
        simp only [observeAux, dite_eq_left hn]
        exact Measurable.dite hcontinue hstop hset
      · simp only [observeAux, dite_eq_right hn]
        exact (measurable_terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block).comp
            (measurable_terminalBlockTraceOfInput (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) (rewards := rewards) block)

/-- Joint measurability on the whole original source AND varying full carry.
The terminal, continuation, and chronological reconstruction theorems above
identify this observation with H's actual dependent data. -/
theorem measurable_runFromObservation (block : Fin (n_boot p)) :
    Measurable (runFromObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun input : BlockInput p rate block C_star C_h =>
    (input.1, (input.2, observeAux (rewards := rewards)
      (n_boot p - block.val) block rfl input)))
  exact measurable_fst.prodMk (measurable_snd.prodMk
    (measurable_observeAux (rewards := rewards) (n_boot p - block.val) block rfl))

/-- Actual H terminal-index measurability explicitly consumes the full
observer/run identity. No space is pulled back through H.runFrom. -/
theorem measurable_actual_terminalBlock (block : Fin (n_boot p)) :
    Measurable (fun input : BlockInput p rate block C_star C_h =>
      (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalBlock) := by
  have htail := measurable_observeAux (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (n_boot p - block.val) block rfl
  have h : Measurable (fun input : BlockInput p rate block C_star C_h =>
      (observeAux (rewards := rewards) (n_boot p - block.val) block rfl input).terminalBlock) :=
    (measurable_runTail_terminalBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)).comp htail
  convert h using 1
  funext input
  exact (runFrom_terminalBlock_eq (rewards := rewards) block input).symm

/-- Borel coordinates of H's ACTUAL full physical records, via the proved
SAME-run stream identity. Rewards remain a fixed whole denominator-D table. -/
theorem measurable_actual_round_stream (block other : Fin (n_boot p)) (cursor : ℕ) :
    Measurable (fun input : BlockInput p rate block C_star C_h =>
      (roundCodeListCoordinates
        (((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.filter
          (fun record => record.block == other)).map
            (fullRecordCode (C_star := C_star) (C_h := C_h)))).2 cursor) := by
  have htail := measurable_observeAux (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (n_boot p - block.val) block rfl
  have h : Measurable (fun input : BlockInput p rate block C_star C_h =>
      (observeAux (rewards := rewards) (n_boot p - block.val) block rfl input).physicalRoundCodes other cursor) :=
    (measurable_pi_apply cursor).comp ((measurable_pi_apply other).comp
      ((measurable_runTail_physicalRoundCodes (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h)).comp htail))
  convert h using 1
  funext input
  exact (runFrom_round_stream (rewards := rewards) block input other cursor).symm

/-- All slots before the actual starting block are absent. The proof uses
H's increasing execution indices and the produced record-block lower bound. -/
theorem runFrom_earlier_slots (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p))
    (hearly : other.val < block.val) :
    let observation := runFromObservation (rewards := rewards) block input
    observation.suffix.terminalEntries other = .inl () ∧
      observation.suffix.continuedEntries other = .inl () ∧
      ∀ cursor, observation.suffix.physicalRoundCodes other cursor = .inl () := by
  dsimp only
  obtain ⟨terminal, carry, _, ht, hd, _⟩ :=
    observeAux_terminal (rewards := rewards) (n_boot p - block.val) block rfl input
  have hterminal := congrArg Sigma.fst hd
  change (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalBlock = terminal at hterminal
  have hindex := (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).terminalBlock_index
  have hne : other ≠ terminal := by
    intro he
    have hv := congrArg Fin.val he
    rw [hterminal] at hindex
    omega
  refine ⟨?_, ?_, ?_⟩
  · change (observeAux (rewards := rewards) (n_boot p - block.val) block rfl input).terminalEntries other = _
    rw [ht]
    simp only [terminalRunTailObservation, dite_eq_right hne]
  · apply (runFrom_continued_absent (rewards := rewards) block input other).mpr
    intro execution he hblock
    have hm : execution.block.val ∈
        (ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).continuedBlocks.map (fun execution => execution.block.val) :=
      List.mem_map.mpr ⟨execution, he, rfl⟩
    rw [(runFrom_continued_indices (rewards := rewards) block input).1] at hm
    have hg := (consecutiveNat_mem_iff _ _ _).mp hm
    have hv := congrArg Fin.val hblock
    omega
  · intro cursor
    rw [runFrom_round_stream]
    have hfilter : ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.filter (fun record => record.block == other)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro record hr
      have hg := runFrom_records_blocks_ge (rewards := rewards)
        (n_boot p - block.val) block rfl input record hr
      simp only [beq_iff_eq]
      intro he
      have hv := congrArg Fin.val he
      omega
    simp only [hfilter, List.map_nil, roundCodeListCoordinates, List.getElem?_nil]

private theorem roundCoordinates_absent_iff {α : Type*} (codes : List α) (cursor : ℕ) :
    (roundCodeListCoordinates codes).2 cursor = .inl () ↔ codes.length ≤ cursor := by
  unfold roundCodeListCoordinates
  cases hg : codes[cursor]? with
  | none =>
      simp only [hg]
      constructor
      · intro _
        exact List.getElem?_eq_none_iff.mp hg
      · intro _
        exact True.intro
  | some code =>
      simp only [hg]
      constructor
      · intro h
        cases h
      · intro h
        have hn := List.getElem?_eq_none_iff.mpr h
        rw [hg] at hn
        cases hn

/-- Exact absence of a per-block round position, as distinguished from the
inner physical error tag. All nonoccurring blocks therefore have no positions. -/
theorem runFrom_round_slot_absent_iff (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) (other : Fin (n_boot p)) (cursor : ℕ) :
    (runFromObservation (rewards := rewards) block input).suffix.physicalRoundCodes other cursor =
        .inl () ↔
      ((ActualInitializationHorizon.runFrom p rate input.1 rewards block input.2.1).records.filter
        (fun record => record.block == other)).length ≤ cursor := by
  rw [runFrom_round_stream, roundCoordinates_absent_iff, List.length_map]

end Bandits.Support.ActualInitializationHorizonObservation
