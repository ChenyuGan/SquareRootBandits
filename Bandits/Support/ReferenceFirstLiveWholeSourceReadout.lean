/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout
public import Bandits.Support.ReferenceFirstLiveBranchIntegralTransport

import Lean.Elab.Tactic.Omega

/-!
# Whole-source first-live numerical readouts

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

These deterministic identities join the whole-source first-live list to the
existing source-stratum queue readouts. The preservation result concerns only
the literal readout path outside a retained incoming cell.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstLiveWholeSourceReadout

variable {p : ReferenceFirstLiveCalendarPrefixReadout.Parameters}
variable (rate : ReferenceFirstLiveCalendarPrefixReadout.RateInput p)
  (rewards : ReferenceFirstLiveCalendarPrefixReadout.RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val)

local notation "n" => t.val - s
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards
  C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

private theorem source_start_eq_stratum (z : Z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := by
  have hfacts := (ReferenceFirstLiveBranchIntegralTransport.sourceStratum_mem_iff rate rewards C_star C_h q t s hs z.val).mp
    z.property
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
    hfacts.2.2
  simpa [ReferenceCompletePhysicalHistory.physicalStart, ReferenceCompletePhysicalHistory.generatedBoundary, ReferenceCompletePhysicalHistory.generatedInput] using helapsed

/-- The original whole-source suffix agrees with the source-stratum list
through the inclusive current cell on every source stratum. -/
theorem wholeFirstLiveCells_take_stratum (z : Z) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take (n + 1) =
      ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z := by
  have hfacts := (ReferenceFirstLiveBranchIntegralTransport.sourceStratum_mem_iff rate rewards C_star C_h q t s hs z.val).mp
    z.property
  have hcross := hfacts.2.1
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
    hfacts.2.2
  let sFin : Fin (p.T + 1) := ⟨s, by omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s := ⟨z.val, ⟨hcross, helapsed⟩⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber rate rewards C_star C_h sFin x
  have hfullSpan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
        (p.T - s) ≤ p.T := by
    rw [helapsed]
    simpa only [sFin] using ReferenceFirstLiveOverflowReadout.maximal_span sFin
  have hwholeCells : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross (p.T - s) hfullSpan := by
    simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells, ReferenceFirstLiveOverflowReadout.launch_crossing, ReferenceFirstLiveOverflowReadout.launch_span, sFin] using hwhole.2
  have hprefix := ReferenceFirstLiveCalendarPrefixReadout.actualLiveSourceCells_take_of_le rate z.val rewards C_star C_h hcross
    (n + 1) (p.T - s) (by omega) hfullSpan
  have hspanCurrent : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by
    rw [helapsed]
    omega
  have hBcells : ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross (n + 1) hspanCurrent := by
    unfold ReferenceFirstLiveBranchIntegralTransport.actualSourceCells
    congr 1
  calc
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take (n + 1) =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross (p.T - s) hfullSpan).take
          (n + 1) := by rw [hwholeCells]
    _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hcross (n + 1) hspanCurrent := hprefix
    _ = ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z := hBcells.symm

/-- Every shorter prefix agrees, including the strict-past prefix. -/
theorem wholeFirstLiveCells_take_stratum_prefix (z : Z) (k : ℕ) (hk : k ≤ n + 1) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take k =
      (ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take k := by
  calc
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take k =
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take (n + 1)).take k := by
          rw [List.take_take, Nat.min_eq_left hk]
    _ = (ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take k := by
      rw [wholeFirstLiveCells_take_stratum rate rewards C_star C_h q t s hs z]

/-- The branch transport's incoming overflow test is the literal run on the
strict-past prefix of the whole-source first-live list. -/
theorem actualOverflowFalseSet_iff (z : Z) :
    z ∈ ReferenceFirstLiveBranchIntegralTransport.actualOverflowFalseSet rate rewards C_star C_h q t s hs ↔
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h))).overflow = false := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z n
    (by omega)
  rw [hstart]
  change (RecordedQueueRun.run Q
      ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take n)).overflow = false ↔ _
  rw [← hprefix]

/-- The whole-source potential before the current source-stratum cell. -/
theorem firstWindowPotentialAt_stratum_before (z : Z) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h t.val z.val =
      ReferenceFirstLiveBranchIntegralTransport.actualPotentialBefore rate rewards C_star C_h q t s hs z := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z n
    (by omega)
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt, hstart]
  change RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take n)) =
    RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take n))
  rw [hprefix]

/-- The whole-source potential after the current source-stratum cell. -/
theorem firstWindowPotentialAt_stratum_after (z : Z) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h (t.val + 1) z.val =
      ReferenceFirstLiveBranchIntegralTransport.actualPotentialAfter rate rewards C_star C_h q t s hs z := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hnext : t.val + 1 - s = n + 1 := by omega
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z
    (n + 1) (by omega)
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt, hstart, hnext]
  change RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take (n + 1))) =
    RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take (n + 1)))
  rw [hprefix]

/-- The whole-source weighted backlog before the current cell. -/
theorem firstWindowWeightedBacklogAt_stratum_before (z : Z) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt rate rewards C_star C_h t.val z.val =
      ReferenceFirstLiveBranchIntegralTransport.actualWeightedBacklogBefore rate rewards C_star C_h q t s hs z := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z n
    (by omega)
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt, hstart]
  change RecordedWeightedDrift.weightedBacklog p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take n)) =
    RecordedWeightedDrift.weightedBacklog p.m Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take n))
  rw [hprefix]

/-- The whole-source normalized backlog before the current cell. -/
theorem firstWindowBacklogAt_stratum_before (z : Z) (j : Fin p.K) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j t.val z.val =
      ReferenceFirstLiveBranchIntegralTransport.actualNormalizedBacklogBefore rate rewards C_star C_h q t s hs j z := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z n
    (by omega)
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt, hstart]
  change StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take n)) j =
    StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take n)) j
  rw [hprefix]

/-- The whole-source normalized backlog after the current cell, retaining its
first-overflow update. -/
theorem firstWindowBacklogAt_stratum_after (z : Z) (j : Fin p.K) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) z.val =
      ReferenceFirstLiveBranchIntegralTransport.actualNormalizedBacklogAfter rate rewards C_star C_h q t s hs j z := by
  have hstart := source_start_eq_stratum rate rewards C_star C_h q t s hs z
  have hnext : t.val + 1 - s = n + 1 := by omega
  have hprefix := wholeFirstLiveCells_take_stratum_prefix rate rewards C_star C_h q t s hs z
    (n + 1) (by omega)
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt, hstart, hnext]
  change StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take (n + 1))) j =
    StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z).take (n + 1))) j
  rw [hprefix]

/-- The beta-exponential readout before the current cell is the same original
source readout as in the branch transport. -/
theorem firstWindowExpBacklogAt_stratum_before (z : Z) (j : Fin p.K) :
    Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j t.val z.val) =
      ReferenceFirstLiveBranchIntegralTransport.actualExpBacklogBefore rate rewards C_star C_h q t s hs j z := by
  rw [ReferenceFirstLiveBranchIntegralTransport.actualExpBacklogBefore, firstWindowBacklogAt_stratum_before rate rewards C_star C_h q t s hs z j]

/-- The beta-exponential readout after the current cell is the same original
source readout as in the branch transport. -/
theorem firstWindowExpBacklogAt_stratum_after (z : Z) (j : Fin p.K) :
    Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) z.val) =
      ReferenceFirstLiveBranchIntegralTransport.actualExpBacklogAfter rate rewards C_star C_h q t s hs j z := by
  rw [ReferenceFirstLiveBranchIntegralTransport.actualExpBacklogAfter, firstWindowBacklogAt_stratum_after rate rewards C_star C_h q t s hs z j]

private theorem weightedSquarePotential_eq_of_registers_eq
    {K : ℕ} (m : ℕ) (queue : RecordedQueueRun.Parameters)
    (left right : RecordedQueueRun.RunState K)
    (hregisters : left.registers = right.registers) :
    RecordedWeightedDrift.weightedSquarePotential m queue left =
      RecordedWeightedDrift.weightedSquarePotential m queue right := by
  have hscore : RecordedQueueRun.scoreWeight queue left =
      RecordedQueueRun.scoreWeight queue right := by
    funext i
    unfold RecordedQueueRun.scoreWeight
    rw [hregisters]
  unfold RecordedWeightedDrift.weightedSquarePotential
  rw [hscore]
  apply Finset.sum_congr rfl
  intro i hi
  unfold StoppedQueueBound.normalizedBacklog
  rw [congrFun hregisters i]

private theorem weightedBacklog_eq_of_registers_eq
    {K : ℕ} (m : ℕ) (queue : RecordedQueueRun.Parameters)
    (left right : RecordedQueueRun.RunState K)
    (hregisters : left.registers = right.registers) :
    RecordedWeightedDrift.weightedBacklog m queue left =
      RecordedWeightedDrift.weightedBacklog m queue right := by
  have hscore : RecordedQueueRun.scoreWeight queue left =
      RecordedQueueRun.scoreWeight queue right := by
    funext i
    unfold RecordedQueueRun.scoreWeight
    rw [hregisters]
  unfold RecordedWeightedDrift.weightedBacklog
  rw [hscore]
  apply Finset.sum_congr rfl
  intro i hi
  unfold StoppedQueueBound.normalizedBacklog
  rw [congrFun hregisters i]

private theorem normalizedBacklog_eq_of_registers_eq
    {K : ℕ} (queue : RecordedQueueRun.Parameters)
    (left right : RecordedQueueRun.RunState K) (j : Fin K)
    (hregisters : left.registers = right.registers) :
    StoppedQueueBound.normalizedBacklog queue left j =
      StoppedQueueBound.normalizedBacklog queue right j := by
  unfold StoppedQueueBound.normalizedBacklog
  rw [hregisters]

/-- Outside a retained live cell, the actual register vector is unchanged by
the calendar successor readout. The sole premise is the literal path test. -/
theorem firstWindow_registers_eq_of_not_retained_cell
    (t : Fin p.T) (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (hnot : ¬ (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ∧
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).overflow = false)) :
    (RecordedQueueRun.run Q
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).registers =
    (RecordedQueueRun.run Q
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).registers := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  let L := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega
  let k := t.val - start
  change ¬ (start ≤ t.val ∧ k < L.length ∧
    (RecordedQueueRun.run Q (L.take k)).overflow = false) at hnot
  have hregisters :
      (RecordedQueueRun.run Q (L.take (t.val + 1 - start))).registers =
        (RecordedQueueRun.run Q (L.take (t.val - start))).registers := by
    by_cases hstarted : start ≤ t.val
    · by_cases hsaturated : L.length ≤ k
      · have hcountAfter : t.val + 1 - start = k + 1 := by omega
        have hcountBefore : t.val - start = k := rfl
        have htake : L.take (k + 1) = L.take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le hsaturated]
        rw [hcountAfter, hcountBefore, htake]
      · have hcell : k < L.length := Nat.lt_of_not_ge hsaturated
        have hincoming : (RecordedQueueRun.run Q (L.take k)).overflow = true := by
          cases hflag : (RecordedQueueRun.run Q (L.take k)).overflow with
          | false => exact False.elim (hnot ⟨hstarted, hcell, hflag⟩)
          | true => rfl
        have hrun := RecordedPotentialStep.run_take_succ_eq_step Q L k hcell
        have hcountAfter : t.val + 1 - start = k + 1 := by omega
        have hcountBefore : t.val - start = k := rfl
        rw [hcountAfter, hcountBefore, hrun]
        funext i
        exact (RecordedQueueRun.step_after_overflow_preserves Q
          (RecordedQueueRun.run Q (L.take k)) L[k] hincoming i).1
    · have hcountAfter : t.val + 1 - start = 0 := by omega
      have hcountBefore : t.val - start = 0 := by omega
      rw [hcountAfter, hcountBefore]
  simpa only [start, L] using hregisters

/-- Potential readout is unchanged outside retained cells. -/
theorem firstWindowPotentialAt_eq_of_not_retained_cell
    (t : Fin p.T) (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (hnot : ¬ (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ∧
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).overflow = false)) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h (t.val + 1) omega =
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h t.val omega := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  let L := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega
  have hregisters := firstWindow_registers_eq_of_not_retained_cell rate rewards C_star C_h
    t omega hnot
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
  change RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q (L.take (t.val + 1 - start))) =
    RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q (L.take (t.val - start)))
  exact weightedSquarePotential_eq_of_registers_eq p.m Q
    (RecordedQueueRun.run Q (L.take (t.val + 1 - start)))
    (RecordedQueueRun.run Q (L.take (t.val - start))) hregisters

/-- Weighted backlog readout is unchanged outside retained cells. -/
theorem firstWindowWeightedBacklogAt_eq_of_not_retained_cell
    (t : Fin p.T) (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (hnot : ¬ (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ∧
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).overflow = false)) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt rate rewards C_star C_h (t.val + 1) omega =
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt rate rewards C_star C_h t.val omega := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  let L := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega
  have hregisters := firstWindow_registers_eq_of_not_retained_cell rate rewards C_star C_h
    t omega hnot
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt
  change RecordedWeightedDrift.weightedBacklog p.m Q
      (RecordedQueueRun.run Q (L.take (t.val + 1 - start))) =
    RecordedWeightedDrift.weightedBacklog p.m Q
      (RecordedQueueRun.run Q (L.take (t.val - start)))
  exact weightedBacklog_eq_of_registers_eq p.m Q
    (RecordedQueueRun.run Q (L.take (t.val + 1 - start)))
    (RecordedQueueRun.run Q (L.take (t.val - start))) hregisters

/-- Each normalized backlog readout is unchanged outside retained cells. -/
theorem firstWindowBacklogAt_eq_of_not_retained_cell
    (t : Fin p.T) (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin p.K)
    (hnot : ¬ (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ∧
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).overflow = false)) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) omega =
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j t.val omega := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  let L := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega
  have hregisters := firstWindow_registers_eq_of_not_retained_cell rate rewards C_star C_h
    t omega hnot
  unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
  change StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q (L.take (t.val + 1 - start))) j =
    StoppedQueueBound.normalizedBacklog Q
      (RecordedQueueRun.run Q (L.take (t.val - start))) j
  exact normalizedBacklog_eq_of_registers_eq Q
    (RecordedQueueRun.run Q (L.take (t.val + 1 - start)))
    (RecordedQueueRun.run Q (L.take (t.val - start))) j hregisters

/-- The beta-exponential backlog readout is unchanged outside retained cells. -/
theorem firstWindowExpBacklogAt_eq_of_not_retained_cell
    (t : Fin p.T) (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin p.K)
    (hnot : ¬ (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length ∧
      (RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h))).overflow = false)) :
    Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j (t.val + 1) omega) =
    Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j t.val omega) := by
  rw [firstWindowBacklogAt_eq_of_not_retained_cell rate rewards C_star C_h t omega j hnot]

end Bandits.Support.ReferenceFirstLiveWholeSourceReadout

end
