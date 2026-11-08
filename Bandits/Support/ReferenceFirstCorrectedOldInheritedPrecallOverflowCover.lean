/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCoordinatorQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedFollowerRegisterOverflowCover

import Mathlib.Tactic

/-!
# First-corrected old inherited backlog overflow reaches the precall event

The first corrected old inherited follower backlog event is transferred from
the original whole first-live numerical source list to the actual strict-past
list used by the terminal precall readout. The first crossing update is
preserved when that list is extended by the actual cutoff collection suffix.

Sources: ZIP4 `appendix_a_local_protocol.tex:8-64`,
`06_interruptions.tex:192-233,246-299,391-408,425-426`, and
`04_slow_fast_learner.tex:157-187,256-290`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (correctedCell)

namespace Bandits.Support.ReferenceFirstCorrectedOldInheritedPrecallOverflowCover

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- A whole-source first-live crossing in a corrected cell is still a
crossing in the exact strict-past list read by the terminal precall event. -/
theorem correctedCell_inter_firstWindowOverflow_subset_precallOverflow
    (u t : Fin p.T) :
    {z : SourceInput p |
      z ∈ correctedCell rate rewards C_star C_h u t ∧
        z ∈ ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h} ⊆
      ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
        rate rewards C_star C_h := by
  classical
  intro z hz
  rcases hz with ⟨hzCell, hzWindow⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  obtain ⟨hc, hs, _, _, _, _, D, L, _, _, _, _, _, _, _, _, _, _, hjoin,
      hpast, _, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hzCell.1
  let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hs
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hRecords : R =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hc count hs).records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
  have hLength : L0.length =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
        rate rewards C_star C_h z := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    change L0.length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    rw [hRecords]
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hs
  have hwholeCross :
      (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true := by
    simpa only [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hc
  have hWholeCells :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z = L0 := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    rw [dite_eq_left hwholeCross]
  have hWholePrefixEq :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
        rate rewards C_star C_h z =
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0 := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
    rw [hWholeCells]
  change ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
    rate rewards C_star C_h z ≠ none at hzWindow
  have hWholeBound :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
          rate rewards C_star C_h z ≤
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
          rate rewards C_star C_h z := by
    by_contra hnot
    have hnone : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
        rate rewards C_star C_h z = none := by
      unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rw [ite_eq_right hnot]
    exact hzWindow hnone
  have hCrossBound :
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0 ≤ L0.length := by
    rw [hWholePrefixEq, ← hLength] at hWholeBound
    exact hWholeBound
  have hfirstCross :=
    UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first Q L0
      hCrossBound
  have hLtake (n : ℕ) (hn : n ≤ L0.length) :
      L.take n = L0.take n := by
    rw [hjoin]
    exact List.take_append_of_le_length hn
  have hReplay (a : Fin p.K)
      (n : ℕ) (hn : n ≤ L0.length) :
      UnstoppedRecordedQueueComparison.unstoppedReplay Q L n a =
        UnstoppedRecordedQueueComparison.unstoppedReplay Q L0 n a := by
    unfold UnstoppedRecordedQueueComparison.unstoppedReplay
    rw [hLtake n hn]
  have hCrossInL :
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q L
        (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0) := by
    change ∃ a, 32 *
      (UnstoppedRecordedQueueComparison.unstoppedReplay Q L
        (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0) a).2 > Q.D
    rcases hfirstCross with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [hReplay a _ hCrossBound]
    exact ha
  have hLlength : L.length = L0.length + D.length := by
    rw [hjoin, List.length_append]
  have hL0leL : L0.length ≤ L.length := by
    omega
  have hCrossPos :
      0 < UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0 :=
    UnstoppedRecordedQueueComparison.first_overflow_prefix_pos Q L0
  have hCrossInLBound :
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0 ≤ L.length :=
    hCrossBound.trans hL0leL
  have hsomeCross : ∃ n, 1 ≤ n ∧ n ≤ L.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q L n :=
    ⟨UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0,
      hCrossPos, hCrossInLBound, hCrossInL⟩
  have hfirstLBound :
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L ≤
        UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L0 := by
    unfold UnstoppedRecordedQueueComparison.firstOverflowPrefix
    rw [dite_eq_left hsomeCross]
    exact Nat.find_min' hsomeCross
      ⟨hCrossPos, hCrossInLBound, hCrossInL⟩
  have hfirstL :
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L ≤ L.length :=
    hfirstLBound.trans hCrossInLBound
  have hrunPrefix :=
    (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q L L.length le_rfl).2 hfirstL
  have hrun : (RecordedQueueRun.run Q L).overflow = true := by
    simpa only [List.take_length] using hrunPrefix
  have hterminal :
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h p.T z = some L := by
    rw [ReferenceFirstCollectionPrecallOverflowBound.precallCells_terminal_eq_pastCells_on_firstCell
      rate rewards C_star C_h u t z hzCell.1, hpast]
  exact ⟨p.T, le_rfl, L, hterminal, hrun⟩

/-- The per-cell literal old inherited follower overflow remains inside the
same actual precall event. -/
theorem literalOldInheritedFollowerStoredBacklogOverflowAt_subset_precallOverflow
    (u t : Fin p.T) :
    {z : SourceInput p |
      ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflowAt
        rate rewards C_star C_h u t z} ⊆
      ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
        rate rewards C_star C_h := by
  intro z hz
  have hzCell : z ∈ correctedCell rate rewards C_star C_h u t := hz.1
  have hWindow : z ∈
      ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
        rate rewards C_star C_h :=
    ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflow_subset_firstWindowOverflow
      rate rewards C_star C_h ⟨u, t, hz⟩
  exact correctedCell_inter_firstWindowOverflow_subset_precallOverflow
    rate rewards C_star C_h u t ⟨hzCell, hWindow⟩

/-- The union of all literal old inherited follower overflow cells is inside
the same original-source precall event. -/
theorem literalOldInheritedFollowerStoredBacklogOverflow_subset_precallOverflow :
    ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflow
        rate rewards C_star C_h ⊆
      ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
        rate rewards C_star C_h := by
  rintro z ⟨u, t, hz⟩
  exact literalOldInheritedFollowerStoredBacklogOverflowAt_subset_precallOverflow
    rate rewards C_star C_h u t hz

end Bandits.Support.ReferenceFirstCorrectedOldInheritedPrecallOverflowCover

end
