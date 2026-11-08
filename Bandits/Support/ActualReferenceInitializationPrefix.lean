/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationHorizon
public import Bandits.Support.ActualReferenceInitializationBoundary

import Lean.Elab.Tactic.Omega

/-!
# Actual/reference initialization prefix induction

The actual horizon recursion carries the incoming actual block state and the
physical records already produced. Under the literal current-block event
complements, its accepted block continuation yields the next incoming
reference boundary. The same induction recovers the actual incoming carry at
the terminal fold.

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,63-140` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.InitializationFailureProvenance
open Bandits.Support.BootstrapAllCandidateController

namespace Bandits.Support.ActualReferenceInitializationPrefix

abbrev Parameters := ConstructorDimensions.Parameters

private theorem take_append_after_prefix {α : Type} (left right : List α)
    (n : ℕ) (hlen : left.length ≤ n) :
    (left ++ right).take n = left ++ right.take (n - left.length) := by
  rw [List.take_append, List.take_of_length_le hlen]

private abbrev TerminalFoldData (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :=
  Σ C_star : ℝ, Σ C_h : ℝ, Σ block : Fin (n_boot p),
    ActualInitializationRun.BlockFoldOutput p rate block source rewards C_star C_h 0

private def terminalFoldData (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    {startBlock : Fin (n_boot p)}
    {startCarry : ActualInitializationRun.BlockCarry p rate startBlock}
    (result : ActualInitializationHorizon.RunSuffix p rate source rewards startBlock startCarry) :
    TerminalFoldData p rate source rewards :=
  ⟨result.terminalC_star, result.terminalC_h, result.terminalBlock, result.terminalFold⟩

private theorem terminalFoldData_eq_fields (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (left right : TerminalFoldData p rate source rewards) (h : left = right) :
    left.1 = right.1 ∧ left.2.1 = right.2.1 ∧ left.2.2.1 = right.2.2.1 ∧
      HEq left.2.2.2 right.2.2.2 := by
  cases h
  exact ⟨rfl, rfl, rfl, HEq.rfl⟩

private theorem blockFoldOutput_records_eq_of_heq {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star₁ C_h₁ C_star₂ C_h₂ : ℝ}
    {block₁ block₂ : Fin (n_boot p)}
    (fold₁ : ActualInitializationRun.BlockFoldOutput p rate block₁ source rewards C_star₁ C_h₁ 0)
    (fold₂ : ActualInitializationRun.BlockFoldOutput p rate block₂ source rewards C_star₂ C_h₂ 0)
    (hblock : block₁ = block₂) (hstar : C_star₁ = C_star₂) (hch : C_h₁ = C_h₂)
    (hfold : HEq fold₁ fold₂) : fold₁.records = fold₂.records := by
  cases hblock
  cases hstar
  cases hch
  exact congrArg (fun output : ActualInitializationRun.BlockFoldOutput p rate block₁ source rewards
      C_star₁ C_h₁ 0 => output.records) (eq_of_heq hfold)

private theorem apply_ndrec_eq {ι α : Type} {d a b : ι}
    (f : d = a → α) (h : a = b) (e : d = b) :
    (Eq.ndrec (motive := fun t => d = t → α) f h) e = f (e.trans h.symm) := by
  cases h
  rfl

-- Evaluate the dependent eliminator before taking any `RunSuffix` projection.
-- The motive retains the handoff equation, whose only data are the computed branch.
private theorem disposition_cases_continueNext
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)} {α : Type}
    {d : ActualInitializationRun.BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {next : Fin (n_boot p)} {nextCarry : ActualInitializationRun.BlockCarry p rate next}
    (h : d = .continueNext next nextCarry) :
    ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun t => d = t → α) d onContinue onLaunch onExhaust rfl =
        onContinue next nextCarry h := by
  cases h
  rfl

private theorem disposition_cases_launched
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)} {α : Type}
    {d : ActualInitializationRun.BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {launch : BootstrapCoordinatorLocalRound.LaunchedBlock p}
    {seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p}
    (h : d = .launched launch seed) :
    ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun t => d = t → α) d onContinue onLaunch onExhaust rfl =
        onLaunch launch seed h := by
  cases h
  rfl

private theorem disposition_cases_exhausted
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)} {α : Type}
    {d : ActualInitializationRun.BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {live : BootstrapCoordinatorLocalRound.PrelaunchBlock p}
    (h : d = .exhausted live) :
    ActualInitializationRun.BoundaryDisposition.casesOn
      (motive := fun t => d = t → α) d onContinue onLaunch onExhaust rfl =
        onExhaust live h := by
  cases h
  rfl

/-- Induction over the actual `runFrom` recursion. `past` is the actual
chronological record accumulator before `block`; the base caller supplies the
empty accumulator and every recursive caller appends the actual computed fold.
The only event inputs are the literal generated-DOWN and selected-row
all-candidate complements along the existing reference run. -/
private theorem runFrom_incoming_prefix
    (p : Parameters) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (block : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate block)
    (b : ReferenceInitializationRun.Boundary p)
    (hb : b = ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      block.val)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h
      rate block carry b past) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p),
      ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown x
        (ReferenceInitializationRun.run x r) hcompleted i) →
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p)
      (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T) →
    (∀ (execution : ActualInitializationHorizon.ContinuedBlockExecution p rate source rewards),
      execution ∈ (ActualInitializationHorizon.runFrom p rate source rewards block carry).continuedBlocks →
      (ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        execution.block execution.carry
        (ReferenceInitializationRun.run x execution.block.val)
        (past ++ (ActualInitializationHorizon.runFrom p rate source rewards block carry).records.take
          (BootstrapObservedFollower.blockStart p execution.block -
            BootstrapObservedFollower.blockStart p block)) ∧
       ∃ h : (ReferenceInitializationRun.run x execution.block.val).completed < n_boot p,
        execution.next.val = execution.block.val + 1 ∧
        ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
          execution.next execution.nextCarry
          (ReferenceInitializationRun.finishBlock x
            (ReferenceInitializationRun.run x execution.block.val) h)
          (past ++ (ActualInitializationHorizon.runFrom p rate source rewards block carry).records.take
            (BootstrapObservedFollower.blockStart p execution.next -
              BootstrapObservedFollower.blockStart p block)))) ∧
    ∃ terminalCarry : ActualInitializationRun.BlockCarry p rate
        (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock,
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock
        terminalCarry
        (ReferenceInitializationRun.run x
          (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock.val)
        (past ++ (ActualInitializationHorizon.runFrom p rate source rewards block carry).records.take
          (BootstrapObservedFollower.blockStart p
            (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock -
            BootstrapObservedFollower.blockStart p block)) ∧
      terminalCarry.C_star =
        (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalC_star ∧
      terminalCarry.C_h =
        (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalC_h ∧
      HEq (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalFold
        (ActualInitializationRun.foldBlock p rate
          (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock
          source rewards terminalCarry) ∧
      (ActualInitializationHorizon.runFrom p rate source rewards block carry).records =
        (ActualInitializationHorizon.runFrom p rate source rewards block carry).records.take
          (BootstrapObservedFollower.blockStart p
            (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalBlock -
            BootstrapObservedFollower.blockStart p block) ++
          (ActualInitializationHorizon.runFrom p rate source rewards block carry).terminalFold.records := by
  dsimp only
  intro hdown hclean
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  have hrelatedCurrent := hr
  rcases hr with ⟨hindex, hcross, hforced, hcounter, hstar, hch, hpast, hfollowers⟩
  have hcompleted : b.completed < n_boot p := by
    rw [hindex]
    exact block.isLt
  have hcrossRun : (ReferenceInitializationRun.run x block.val).crossing = none := by
    rw [← hb]
    exact hcross
  have hcompletedRun : (ReferenceInitializationRun.run x block.val).completed < n_boot p := by
    rw [← hb, hindex]
    exact block.isLt
  have hdownCurrent := hdown block.val block.isLt hcrossRun hcompletedRun
  have hcleanCurrent := hclean block.val block.isLt hcrossRun hcompletedRun
  have hdownBoundary : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown x b
      hcompleted i := by
    intro i hbad
    have hbadRun : InitializationFailureProvenance.generatedBlockDown x
        (ReferenceInitializationRun.run x block.val) hcompletedRun i := by
      cases hb
      exact hbad
    exact hdownCurrent i hbadRun
  have hcleanBoundary : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical x b hcompleted).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical x b hcompleted)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T := by
    intro i hi
    have hiRun : refFollower i ∈
        (ReferenceInitializationRun.physical x
          (ReferenceInitializationRun.run x block.val) hcompletedRun).uninformed := by
      cases hb
      exact hi
    have hcleanResult := hcleanCurrent i hiRun
    have hcleanBoundaryResult :
        BootstrapAllCandidateController.cleanPrefix
          (ReferenceInitializationRun.physical x b hcompleted)
          source.1.2 ⟨refFollower i, hi⟩
          (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T := by
      cases hb
      exact hcleanResult
    exact hcleanBoundaryResult
  have hbIndex : b = ReferenceInitializationRun.run x b.completed := by
    calc
      b = ReferenceInitializationRun.run x block.val := hb
      _ = ReferenceInitializationRun.run x b.completed := by rw [← hindex]
  have hblock : ReferenceInitializationRun.nextBlock b hcompleted = block := by
    apply Fin.ext
    exact hindex
  subst block
  let block := ReferenceInitializationRun.nextBlock b hcompleted
  have hbState : b = ReferenceInitializationRun.run x block.val := by
    calc
      b = ReferenceInitializationRun.run x b.completed := hbIndex
      _ = ReferenceInitializationRun.run x block.val := by rw [← hindex]
  have hrelatedCurrentAtBlock :
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        block carry b past := hrelatedCurrent
  have hrelatedCurrentAtRun := hrelatedCurrentAtBlock
  rw [hbState] at hrelatedCurrentAtRun
  let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    carry.C_star carry.C_h folded
  let suffix := ActualInitializationHorizon.runFrom p rate source rewards block carry
  cases hdisposition : handoff.disposition with
  | continueNext next nextCarry =>
      have hcontinue :
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h folded).disposition =
            .continueNext next nextCarry := by
        simpa [handoff, folded] using hdisposition
      have hcontinueBoundary :
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h folded).disposition = .continueNext next nextCarry := hcontinue
      have hfoldRecords :
          (ActualInitializationRun.foldBlock p rate block source rewards carry).records =
            folded.records := rfl
      have hfacts := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
        folded next nextCarry hcontinue
      have hfactNext := hfacts.1
      have hnotLast : block.val + 1 ≠ n_boot p := by
        have hnextLt := next.isLt
        omega
      have hrelatedNext :=
        ActualReferenceInitializationBoundary.combinedBoundaryHandoff_continueNext_related
          source rewards rate C_star C_h b hcompleted carry past hrelatedCurrent
          hdownBoundary hcleanBoundary next nextCarry hcontinueBoundary
      obtain ⟨hnextVal, hrelatedNext⟩ := hrelatedNext
      have hnextValBlock : next.val = block.val + 1 := by
        calc
          next.val = b.completed + 1 := hnextVal
          _ = block.val + 1 := by rw [hindex]
      have hrelatedNextAtRun :
          ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
            next nextCarry
            (ReferenceInitializationRun.finishBlock x b hcompleted)
            (past ++ folded.records) := by
        simpa [block, folded, hfoldRecords] using hrelatedNext
      have hfinish : ReferenceInitializationRun.run x next.val =
          ReferenceInitializationRun.finishBlock x b hcompleted := by
        calc
          ReferenceInitializationRun.run x next.val =
              ReferenceInitializationRun.run x (b.completed + 1) := by rw [hnextVal]
          _ = ReferenceInitializationRun.advance x
              (ReferenceInitializationRun.run x b.completed) :=
                ReferenceInitializationRun.run_succ x b.completed
          _ = ReferenceInitializationRun.advance x b := by rw [← hbIndex]
          _ = ReferenceInitializationRun.finishBlock x b hcompleted :=
                ReferenceInitializationRun.advance_of_no_crossing x b hcross hcompleted
      have hfinishBoundary :
          ReferenceInitializationRun.finishBlock x b hcompleted =
            ReferenceInitializationRun.finishBlock x
              (ReferenceInitializationRun.run x block.val) hcompletedRun := by
        have hfinishAtRun :
            ReferenceInitializationRun.finishBlock x
              (ReferenceInitializationRun.run x block.val) hcompletedRun =
              ReferenceInitializationRun.run x next.val := by
          calc
            ReferenceInitializationRun.finishBlock x
                (ReferenceInitializationRun.run x block.val) hcompletedRun =
                ReferenceInitializationRun.advance x
                  (ReferenceInitializationRun.run x block.val) :=
                    (ReferenceInitializationRun.advance_of_no_crossing x
                      (ReferenceInitializationRun.run x block.val) hcrossRun hcompletedRun).symm
            _ = ReferenceInitializationRun.run x (block.val + 1) :=
                  (ReferenceInitializationRun.run_succ x block.val).symm
            _ = ReferenceInitializationRun.run x next.val := by rw [hnextValBlock]
        calc
          ReferenceInitializationRun.finishBlock x b hcompleted =
              ReferenceInitializationRun.run x next.val := hfinish.symm
          _ = ReferenceInitializationRun.finishBlock x
                (ReferenceInitializationRun.run x block.val) hcompletedRun := hfinishAtRun.symm
      have hrelatedNextRun :
          ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
            next nextCarry
            (ReferenceInitializationRun.finishBlock x
              (ReferenceInitializationRun.run x block.val) hcompletedRun)
            (past ++ folded.records) := by
        rw [← hfinishBoundary]
        exact hrelatedNextAtRun
      have htail := runFrom_incoming_prefix p source rewards rate C_star C_h next nextCarry
        (ReferenceInitializationRun.finishBlock x b hcompleted) hfinish.symm
        (past ++ folded.records) hrelatedNextAtRun
      have htail := htail hdown hclean
      let tail := ActualInitializationHorizon.runFrom p rate source rewards next nextCarry
      let execution : ActualInitializationHorizon.ContinuedBlockExecution p rate source rewards :=
        ⟨block, carry, next, nextCarry, hcontinue⟩
      have hrunFields :
          suffix.records = folded.records ++ tail.records ∧
          suffix.continuedBlocks = execution :: tail.continuedBlocks := by
        dsimp only [suffix, tail]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_continueNext hcontinue]
        rw [apply_ndrec_eq]
        exact ⟨rfl, rfl⟩
      rcases hrunFields with ⟨hrecords, hcontinued⟩
      have hterminalData : terminalFoldData p rate source rewards suffix =
          terminalFoldData p rate source rewards tail := by
        dsimp only [terminalFoldData, suffix, tail]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_continueNext hcontinue]
        rw [apply_ndrec_eq]
      have hterminalFields := terminalFoldData_eq_fields p rate source rewards _ _ hterminalData
      dsimp only [terminalFoldData] at hterminalFields
      rcases hterminalFields with ⟨hterminalCStar, hterminalCH, hterminalBlock, hterminalFold⟩
      have hterminalFoldRecords : suffix.terminalFold.records = tail.terminalFold.records := by
        exact blockFoldOutput_records_eq_of_heq suffix.terminalFold tail.terminalFold
          hterminalBlock hterminalCStar hterminalCH hterminalFold
      have hfoldCount : folded.records.length = BootstrapObservedFollower.blockLength p block := by
        have hcount := folded.record_count
        rw [folded.consumed_eq_blockLength] at hcount
        omega
      have hnextStart : BootstrapObservedFollower.blockStart p next =
          BootstrapObservedFollower.blockStop p block := by
        have hactivation := ActualInitializationHorizon.nextActivationRound_eq_successor_start
          block next hnextValBlock
        change BootstrapObservedFollower.blockStop p block + 1 =
          BootstrapObservedFollower.blockStart p next + 1 at hactivation
        omega
      have hblockGap : BootstrapObservedFollower.blockStart p next =
          BootstrapObservedFollower.blockStart p block + folded.records.length := by
        calc
          BootstrapObservedFollower.blockStart p next =
              BootstrapObservedFollower.blockStop p block := hnextStart
          _ = BootstrapObservedFollower.blockStart p block +
              BootstrapObservedFollower.blockLength p block :=
                (ActualInitializationRun.blockStart_add_length_eq_stop p block).symm
          _ = BootstrapObservedFollower.blockStart p block + folded.records.length := by
                rw [hfoldCount]
      have htakeNext :
          suffix.records.take
            (BootstrapObservedFollower.blockStart p next -
              BootstrapObservedFollower.blockStart p block) = folded.records := by
        rw [hrecords]
        have hoffset : BootstrapObservedFollower.blockStart p next -
            BootstrapObservedFollower.blockStart p block = folded.records.length := by
          rw [hblockGap]
          omega
        rw [hoffset]
        rw [List.take_append_of_le_length (by rfl : folded.records.length ≤ folded.records.length)]
        exact List.take_of_length_le le_rfl
      have htailIndexLower (e : ActualInitializationHorizon.ContinuedBlockExecution
          p rate source rewards) (he : e ∈ tail.continuedBlocks) : next.val ≤ e.block.val := by
        have hmem : e.block.val ∈ (tail.continuedBlocks.map fun execution => execution.block.val) :=
          List.mem_map.mpr ⟨e, he, rfl⟩
        rw [tail.continuedBlockIndex] at hmem
        exact (ActualInitializationHorizon.consecutiveNat_mem_iff next.val
          tail.continuedBlocks.length e.block.val).mp hmem |>.1
      have hblockStartLower (e : Fin (n_boot p)) (hle : next.val ≤ e.val) :
          BootstrapObservedFollower.blockStart p next ≤ BootstrapObservedFollower.blockStart p e := by
        simpa [BootstrapObservedFollower.blockStart] using
          Nat.mul_le_mul_right (B_boot p) hle
      have htakeAt (eBlock : Fin (n_boot p)) (hle : next.val ≤ eBlock.val) :
          suffix.records.take
            (BootstrapObservedFollower.blockStart p eBlock -
              BootstrapObservedFollower.blockStart p block) =
          folded.records ++ tail.records.take
            (BootstrapObservedFollower.blockStart p eBlock -
              BootstrapObservedFollower.blockStart p next) := by
        have hstartle := hblockStartLower eBlock hle
        have hoffset : BootstrapObservedFollower.blockStart p eBlock -
            BootstrapObservedFollower.blockStart p block = folded.records.length +
              (BootstrapObservedFollower.blockStart p eBlock -
                BootstrapObservedFollower.blockStart p next) := by
          omega
        rw [hrecords, hoffset]
        calc
          (folded.records ++ tail.records).take
              (folded.records.length +
                (BootstrapObservedFollower.blockStart p eBlock -
                  BootstrapObservedFollower.blockStart p next)) =
              folded.records ++ tail.records.take
                (folded.records.length +
                  (BootstrapObservedFollower.blockStart p eBlock -
                    BootstrapObservedFollower.blockStart p next) - folded.records.length) :=
                take_append_after_prefix folded.records tail.records _ (by omega)
          _ = folded.records ++ tail.records.take
                (BootstrapObservedFollower.blockStart p eBlock -
                  BootstrapObservedFollower.blockStart p next) := by
                congr 2; omega
      refine ⟨?_, ?_⟩
      · intro execution' hmembership
        rw [hcontinued] at hmembership
        rcases List.mem_cons.mp hmembership with hhead | htailMem
        · cases hhead
          have hincoming :
              ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
                execution.block execution.carry (ReferenceInitializationRun.run x execution.block.val)
                (past ++ suffix.records.take
                  (BootstrapObservedFollower.blockStart p execution.block -
                    BootstrapObservedFollower.blockStart p block)) := by
            change ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              block carry (ReferenceInitializationRun.run x block.val)
              (past ++ suffix.records.take
                (BootstrapObservedFollower.blockStart p block -
                  BootstrapObservedFollower.blockStart p block))
            have hcurrentRelatedRun :
                ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
                  block carry (ReferenceInitializationRun.run x block.val) past := by
              exact hrelatedCurrentAtRun
            simpa only [Nat.sub_self, List.take_zero, List.append_nil] using hcurrentRelatedRun
          refine ⟨hincoming, ?_⟩
          have hcompletedAtRun :
              (ReferenceInitializationRun.run x execution.block.val).completed < n_boot p := by
            change (ReferenceInitializationRun.run x block.val).completed < n_boot p
            exact hcompletedRun
          refine ⟨hcompletedAtRun, ?_, ?_⟩
          · change next.val = block.val + 1
            calc
              next.val = b.completed + 1 := hnextVal
              _ = block.val + 1 := by rw [hindex]
          · change ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              execution.next execution.nextCarry
              (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x block.val)
                hcompletedAtRun) (past ++ suffix.records.take
                  (BootstrapObservedFollower.blockStart p execution.next -
                    BootstrapObservedFollower.blockStart p block))
            simpa only [execution, htakeNext] using hrelatedNextRun
        · have horder := htailIndexLower execution' htailMem
          have hprefix := htakeAt execution'.block horder
          have htailProperty := htail.1 execution' htailMem
          rcases htailProperty with ⟨hincomingTail, hsuccessorTail⟩
          have hincoming :
              ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
                execution'.block execution'.carry (ReferenceInitializationRun.run x execution'.block.val)
                (past ++ suffix.records.take
                  (BootstrapObservedFollower.blockStart p execution'.block -
                    BootstrapObservedFollower.blockStart p block)) := by
            simpa [hprefix, List.append_assoc] using hincomingTail
          rcases hsuccessorTail with ⟨hcur, hnext, hnextRelatedTail⟩
          have hnextOrder : next.val ≤ execution'.next.val := by omega
          have hnextPrefix := htakeAt execution'.next hnextOrder
          have hnextRelated :
              ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
                execution'.next execution'.nextCarry
                (ReferenceInitializationRun.finishBlock x
                  (ReferenceInitializationRun.run x execution'.block.val) hcur)
                (past ++ suffix.records.take
                  (BootstrapObservedFollower.blockStart p execution'.next -
                    BootstrapObservedFollower.blockStart p block)) := by
            simpa [hnextPrefix, List.append_assoc] using hnextRelatedTail
          exact ⟨hincoming, ⟨hcur, hnext, hnextRelated⟩⟩
      · rcases htail.2 with ⟨tailCarry, htailRelated, htailStar, htailCH,
          htailFold, htailRecords⟩
        have hterminalIndexLower : next.val ≤ tail.terminalBlock.val := by
          rw [tail.terminalBlock_index]
          omega
        have hterminalPrefix := htakeAt tail.terminalBlock hterminalIndexLower
        have hterminalRelatedTail :
            ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              tail.terminalBlock tailCarry
              (ReferenceInitializationRun.run x tail.terminalBlock.val)
              (past ++ suffix.records.take
                (BootstrapObservedFollower.blockStart p tail.terminalBlock -
                  BootstrapObservedFollower.blockStart p block)) := by
          simpa only [hterminalPrefix, List.append_assoc] using htailRelated
        have hterminalStarTail : tailCarry.C_star = suffix.terminalC_star :=
          htailStar.trans hterminalCStar.symm
        have hterminalCHTail : tailCarry.C_h = suffix.terminalC_h :=
          htailCH.trans hterminalCH.symm
        have hterminalFoldTail :
            HEq suffix.terminalFold
              (ActualInitializationRun.foldBlock p rate tail.terminalBlock source rewards tailCarry) :=
          hterminalFold.trans htailFold
        have hterminalRecordsTail : suffix.records =
            suffix.records.take
              (BootstrapObservedFollower.blockStart p tail.terminalBlock -
                BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
          calc
            suffix.records = folded.records ++ tail.records := hrecords
            _ = folded.records ++
                (tail.records.take
                  (BootstrapObservedFollower.blockStart p tail.terminalBlock -
                    BootstrapObservedFollower.blockStart p next) ++ tail.terminalFold.records) := by
                  exact congrArg (fun records => folded.records ++ records) htailRecords
            _ = (folded.records ++ tail.records.take
                  (BootstrapObservedFollower.blockStart p tail.terminalBlock -
                    BootstrapObservedFollower.blockStart p next)) ++ tail.terminalFold.records := by
                  rw [← List.append_assoc]
            _ = suffix.records.take
                  (BootstrapObservedFollower.blockStart p tail.terminalBlock -
                    BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
                  rw [← hterminalPrefix, hterminalFoldRecords]
        let terminalIncoming := fun (terminal : Fin (n_boot p)) =>
          ∃ terminalCarry : ActualInitializationRun.BlockCarry p rate terminal,
            ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              terminal terminalCarry (ReferenceInitializationRun.run x terminal.val)
              (past ++ suffix.records.take
                (BootstrapObservedFollower.blockStart p terminal -
                  BootstrapObservedFollower.blockStart p block)) ∧
            terminalCarry.C_star = suffix.terminalC_star ∧
            terminalCarry.C_h = suffix.terminalC_h ∧
            HEq suffix.terminalFold
              (ActualInitializationRun.foldBlock p rate terminal source rewards terminalCarry) ∧
            suffix.records = suffix.records.take
              (BootstrapObservedFollower.blockStart p terminal -
                BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records
        have hterminalForTail : terminalIncoming tail.terminalBlock :=
          ⟨tailCarry, hterminalRelatedTail, hterminalStarTail, hterminalCHTail,
            hterminalFoldTail, hterminalRecordsTail⟩
        have hterminalForSuffix : terminalIncoming suffix.terminalBlock := by
          exact Eq.mp (congrArg terminalIncoming hterminalBlock.symm) hterminalForTail
        rcases hterminalForSuffix with ⟨terminalCarry, hterminalRelated,
          hterminalStar, hterminalCH', hterminalFold', hterminalRecords⟩
        exact ⟨terminalCarry, hterminalRelated, hterminalStar,
          hterminalCH', hterminalFold', hterminalRecords⟩
  | launched launch learnerSeed =>
      have hbranch :
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h folded).disposition = .launched launch learnerSeed := by
        simpa [handoff, folded] using hdisposition
      have hrunFields :
          suffix.records = folded.records ∧ suffix.continuedBlocks = [] := by
        dsimp only [suffix]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_launched hbranch]
        rw [apply_ndrec_eq]
        exact ⟨rfl, rfl⟩
      rcases hrunFields with ⟨hrecords, hcontinued⟩
      have hterminalData : terminalFoldData p rate source rewards suffix =
          (⟨carry.C_star, carry.C_h, block, folded⟩ : TerminalFoldData p rate source rewards) := by
        dsimp only [terminalFoldData, suffix]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_launched hbranch]
        rw [apply_ndrec_eq]
      have hterminalFields := terminalFoldData_eq_fields p rate source rewards _ _ hterminalData
      dsimp only [terminalFoldData] at hterminalFields
      rcases hterminalFields with ⟨hterminalCStar, hterminalCH, hterminalBlock, hterminalFold⟩
      refine ⟨?_, ?_⟩
      · intro execution hmembership
        change execution ∈ suffix.continuedBlocks at hmembership
        rw [hcontinued] at hmembership
        exact (List.not_mem_nil hmembership).elim
      · have hprefix :
            past ++ suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block) = past := by
          simp only [hterminalBlock, Nat.sub_self, List.take_zero, List.append_nil]
        let terminalIncoming := fun (terminal : Fin (n_boot p)) =>
          ∃ terminalCarry : ActualInitializationRun.BlockCarry p rate terminal,
            ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              terminal terminalCarry (ReferenceInitializationRun.run x terminal.val) past ∧
            HEq suffix.terminalFold
              (ActualInitializationRun.foldBlock p rate terminal source rewards terminalCarry)
        have hterminalIncomingAtBlock : terminalIncoming block := by
          refine ⟨carry, hrelatedCurrentAtRun, ?_⟩
          simpa [folded] using hterminalFold
        have hterminalIncoming : terminalIncoming suffix.terminalBlock :=
          Eq.mp (congrArg terminalIncoming hterminalBlock.symm) hterminalIncomingAtBlock
        rcases hterminalIncoming with ⟨terminalCarry, hterminalRelated, hterminalFoldActual⟩
        have hterminalFoldRecords : suffix.terminalFold.records = folded.records := by
          exact blockFoldOutput_records_eq_of_heq suffix.terminalFold folded
            hterminalBlock hterminalCStar hterminalCH hterminalFold
        have hrecordsTerminal : suffix.records =
            suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
          calc
            suffix.records = folded.records := hrecords
            _ = suffix.records.take
                  (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                    BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
                  rw [hterminalFoldRecords]
                  simp only [hterminalBlock, Nat.sub_self, List.take_zero, List.nil_append]
        have hterminalStarInitial : terminalCarry.C_star = C_star :=
          hterminalRelated.2.2.2.2.1
        have hterminalCHInitial : terminalCarry.C_h = C_h :=
          hterminalRelated.2.2.2.2.2.1
        have hterminalStarSuffix : terminalCarry.C_star = suffix.terminalC_star :=
          (hterminalStarInitial.trans hstar.symm).trans hterminalCStar.symm
        have hterminalCHSuffix : terminalCarry.C_h = suffix.terminalC_h :=
          (hterminalCHInitial.trans hch.symm).trans hterminalCH.symm
        refine ⟨terminalCarry, ?_, ?_, ?_, ?_, hrecordsTerminal⟩
        · change ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
            suffix.terminalBlock terminalCarry
            (ReferenceInitializationRun.run x suffix.terminalBlock.val)
            (past ++ suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block))
          rw [hprefix]
          exact hterminalRelated
        · exact hterminalStarSuffix
        · exact hterminalCHSuffix
        · exact hterminalFoldActual
  | exhausted live =>
      have hbranch :
          (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
            carry.C_star carry.C_h folded).disposition = .exhausted live := by
        simpa [handoff, folded] using hdisposition
      have hrunFields :
          suffix.records = folded.records ∧ suffix.continuedBlocks = [] := by
        dsimp only [suffix]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_exhausted hbranch]
        rw [apply_ndrec_eq]
        exact ⟨rfl, rfl⟩
      rcases hrunFields with ⟨hrecords, hcontinued⟩
      have hterminalData : terminalFoldData p rate source rewards suffix =
          (⟨carry.C_star, carry.C_h, block, folded⟩ : TerminalFoldData p rate source rewards) := by
        dsimp only [terminalFoldData, suffix]
        rw [ActualInitializationHorizon.runFrom.eq_1]
        rw [disposition_cases_exhausted hbranch]
        rw [apply_ndrec_eq]
      have hterminalFields := terminalFoldData_eq_fields p rate source rewards _ _ hterminalData
      dsimp only [terminalFoldData] at hterminalFields
      rcases hterminalFields with ⟨hterminalCStar, hterminalCH, hterminalBlock, hterminalFold⟩
      refine ⟨?_, ?_⟩
      · intro execution hmembership
        change execution ∈ suffix.continuedBlocks at hmembership
        rw [hcontinued] at hmembership
        exact (List.not_mem_nil hmembership).elim
      · have hprefix :
            past ++ suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block) = past := by
          simp only [hterminalBlock, Nat.sub_self, List.take_zero, List.append_nil]
        let terminalIncoming := fun (terminal : Fin (n_boot p)) =>
          ∃ terminalCarry : ActualInitializationRun.BlockCarry p rate terminal,
            ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
              terminal terminalCarry (ReferenceInitializationRun.run x terminal.val) past ∧
            HEq suffix.terminalFold
              (ActualInitializationRun.foldBlock p rate terminal source rewards terminalCarry)
        have hterminalIncomingAtBlock : terminalIncoming block := by
          refine ⟨carry, hrelatedCurrentAtRun, ?_⟩
          simpa [folded] using hterminalFold
        have hterminalIncoming : terminalIncoming suffix.terminalBlock :=
          Eq.mp (congrArg terminalIncoming hterminalBlock.symm) hterminalIncomingAtBlock
        rcases hterminalIncoming with ⟨terminalCarry, hterminalRelated, hterminalFoldActual⟩
        have hterminalFoldRecords : suffix.terminalFold.records = folded.records := by
          exact blockFoldOutput_records_eq_of_heq suffix.terminalFold folded
            hterminalBlock hterminalCStar hterminalCH hterminalFold
        have hrecordsTerminal : suffix.records =
            suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
          calc
            suffix.records = folded.records := hrecords
            _ = suffix.records.take
                  (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                    BootstrapObservedFollower.blockStart p block) ++ suffix.terminalFold.records := by
                  rw [hterminalFoldRecords]
                  simp only [hterminalBlock, Nat.sub_self, List.take_zero, List.nil_append]
        have hterminalStarInitial : terminalCarry.C_star = C_star :=
          hterminalRelated.2.2.2.2.1
        have hterminalCHInitial : terminalCarry.C_h = C_h :=
          hterminalRelated.2.2.2.2.2.1
        have hterminalStarSuffix : terminalCarry.C_star = suffix.terminalC_star :=
          (hterminalStarInitial.trans hstar.symm).trans hterminalCStar.symm
        have hterminalCHSuffix : terminalCarry.C_h = suffix.terminalC_h :=
          (hterminalCHInitial.trans hch.symm).trans hterminalCH.symm
        refine ⟨terminalCarry, ?_, ?_, ?_, ?_, hrecordsTerminal⟩
        · change ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
            suffix.terminalBlock terminalCarry
            (ReferenceInitializationRun.run x suffix.terminalBlock.val)
            (past ++ suffix.records.take
              (BootstrapObservedFollower.blockStart p suffix.terminalBlock -
                BootstrapObservedFollower.blockStart p block))
          rw [hprefix]
          exact hterminalRelated
        · exact hterminalStarSuffix
        · exact hterminalCHSuffix
        · exact hterminalFoldActual
termination_by n_boot p - block.val
decreasing_by omega

/-- Every actual continued block begins with the reference boundary generated
by the prior accepted handoff. Its actual record prefix is recovered by
`runFrom` concatenation and `take`, and its actual successor carry is related
to the boundary produced by `finishBlock`. -/
theorem sourceInitializedRun_continued_prefix_related
    (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p),
      ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown x
        (ReferenceInitializationRun.run x r) hcompleted i) →
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p)
      (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T) →
    ∀ (execution : ActualInitializationHorizon.ContinuedBlockExecution p rate source rewards),
      execution ∈ result.continuedBlocks →
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        execution.block execution.carry (ReferenceInitializationRun.run x execution.block.val)
        (result.records.take (BootstrapObservedFollower.blockStart p execution.block)) ∧
      ∃ h : (ReferenceInitializationRun.run x execution.block.val).completed < n_boot p,
        execution.next.val = execution.block.val + 1 ∧
        ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
          execution.next execution.nextCarry
          (ReferenceInitializationRun.finishBlock x
            (ReferenceInitializationRun.run x execution.block.val) h)
          (result.records.take (BootstrapObservedFollower.blockStart p execution.next)) := by
  dsimp only
  intro hdown hclean execution hmembership
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hinitial := ActualReferenceInitializationBlock.initial_related
    source rewards C_star C_h rate
  have hinitialRun :
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        (ActualInitializationRun.firstBlock p)
        (ActualInitializationRun.initialCarry p rate C_star C_h)
        (ReferenceInitializationRun.run x (ActualInitializationRun.firstBlock p).val) [] := by
    simpa [ActualInitializationRun.firstBlock, ReferenceInitializationRun.run_zero] using hinitial
  have hinitialBoundary :
      ReferenceInitializationRun.initial p =
        ReferenceInitializationRun.run x (ActualInitializationRun.firstBlock p).val := by
    simp [ActualInitializationRun.firstBlock, ReferenceInitializationRun.run_zero]
  have hrun := runFrom_incoming_prefix p source rewards rate C_star C_h
    (ActualInitializationRun.firstBlock p)
    (ActualInitializationRun.initialCarry p rate C_star C_h)
    (ReferenceInitializationRun.initial p) hinitialBoundary [] hinitialRun hdown hclean
  have hproperty := hrun.1 execution (by simpa [result,
    ActualInitializationHorizon.sourceInitializedRun] using hmembership)
  simpa [result, ActualInitializationHorizon.sourceInitializedRun,
    ActualInitializationRun.firstBlock, BootstrapObservedFollower.blockStart] using hproperty

/-- The same actual recursion has a terminal incoming carry. The terminal
fold is that carry's actual fold (heterogeneously across the already-derived
shared constants), and the complete actual records split at its physical
block start. -/
theorem sourceInitializedRun_terminal_incoming_prefix
    (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p),
      ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown x
        (ReferenceInitializationRun.run x r) hcompleted i) →
    (∀ (r : ℕ) (_hrange : r < n_boot p) (_hcross : (ReferenceInitializationRun.run x r).crossing = none)
      (hcompleted : (ReferenceInitializationRun.run x r).completed < n_boot p)
      (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x r)
          hcompleted)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T) →
    ∃ terminalCarry : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        result.terminalBlock terminalCarry
        (ReferenceInitializationRun.run x result.terminalBlock.val)
        (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
      terminalCarry.C_star = C_star ∧ terminalCarry.C_h = C_h ∧
      terminalCarry.C_star = result.terminalC_star ∧
      terminalCarry.C_h = result.terminalC_h ∧
      HEq result.terminalFold
        (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards
          terminalCarry) ∧
      result.records = result.records.take
        (BootstrapObservedFollower.blockStart p result.terminalBlock) ++ result.terminalFold.records := by
  dsimp only
  intro hdown hclean
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hinitial := ActualReferenceInitializationBlock.initial_related
    source rewards C_star C_h rate
  have hinitialRun :
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        (ActualInitializationRun.firstBlock p)
        (ActualInitializationRun.initialCarry p rate C_star C_h)
        (ReferenceInitializationRun.run x (ActualInitializationRun.firstBlock p).val) [] := by
    simpa [ActualInitializationRun.firstBlock, ReferenceInitializationRun.run_zero] using hinitial
  have hinitialBoundary :
      ReferenceInitializationRun.initial p =
        ReferenceInitializationRun.run x (ActualInitializationRun.firstBlock p).val := by
    simp [ActualInitializationRun.firstBlock, ReferenceInitializationRun.run_zero]
  have hrun := runFrom_incoming_prefix p source rewards rate C_star C_h
    (ActualInitializationRun.firstBlock p)
    (ActualInitializationRun.initialCarry p rate C_star C_h)
    (ReferenceInitializationRun.initial p) hinitialBoundary [] hinitialRun hdown hclean
  rcases hrun.2 with ⟨terminalCarry, hterminalRelated, hterminalStar, hterminalCH,
    hterminalFold, hterminalRecords⟩
  have hterminalStarInitial : terminalCarry.C_star = C_star := hterminalRelated.2.2.2.2.1
  have hterminalCHInitial : terminalCarry.C_h = C_h := hterminalRelated.2.2.2.2.2.1
  have hfirstStart : BootstrapObservedFollower.blockStart p
      (ActualInitializationRun.firstBlock p) = 0 := by
    simp [ActualInitializationRun.firstBlock, BootstrapObservedFollower.blockStart]
  have hfirstStartDiff : BootstrapObservedFollower.blockStart p result.terminalBlock -
      BootstrapObservedFollower.blockStart p (ActualInitializationRun.firstBlock p) =
        BootstrapObservedFollower.blockStart p result.terminalBlock := by
    rw [hfirstStart]
    omega
  have hterminalRelatedAtResult :
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        result.terminalBlock terminalCarry
        (ReferenceInitializationRun.run x result.terminalBlock.val)
        (result.records.take
          (BootstrapObservedFollower.blockStart p result.terminalBlock -
            BootstrapObservedFollower.blockStart p (ActualInitializationRun.firstBlock p))) := by
    simpa only [result, ActualInitializationHorizon.sourceInitializedRun, List.nil_append]
      using hterminalRelated
  have hterminalRecordsAtResult : result.records =
      result.records.take
        (BootstrapObservedFollower.blockStart p result.terminalBlock -
          BootstrapObservedFollower.blockStart p (ActualInitializationRun.firstBlock p)) ++
        result.terminalFold.records := by
    simpa only [result, ActualInitializationHorizon.sourceInitializedRun] using hterminalRecords
  rw [hfirstStartDiff] at hterminalRelatedAtResult hterminalRecordsAtResult
  have hterminalStarAtResult : terminalCarry.C_star = result.terminalC_star := by
    simpa only [result, ActualInitializationHorizon.sourceInitializedRun] using hterminalStar
  have hterminalCHAtResult : terminalCarry.C_h = result.terminalC_h := by
    simpa only [result, ActualInitializationHorizon.sourceInitializedRun] using hterminalCH
  have hterminalFoldAtResult : HEq result.terminalFold
      (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards terminalCarry) := by
    simpa only [result, ActualInitializationHorizon.sourceInitializedRun] using hterminalFold
  exact ⟨terminalCarry, hterminalRelatedAtResult, hterminalStarInitial,
    hterminalCHInitial, hterminalStarAtResult, hterminalCHAtResult,
    hterminalFoldAtResult, hterminalRecordsAtResult⟩

end Bandits.Support.ActualReferenceInitializationPrefix

end
