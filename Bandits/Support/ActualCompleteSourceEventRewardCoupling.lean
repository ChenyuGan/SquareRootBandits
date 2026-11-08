/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteRewardPrefixComparison
public import Bandits.Support.ReferenceCompleteInclusivePhysicalDecoderErrors

/-!
# Actual source events applied to complete reward comparison

Sources: `sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:240-299`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:16-85`.

The original source's stopped wrong-completion exclusion discharges the
canonical comparison's saved-record condition at actual calendar dates. The
inclusive detector prefix is compared on that same source and physical run;
when there is no physical overflow, the full actual and reference rewards
agree. No probability or learning estimate is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ActualCompleteSourceEventRewardCoupling

private theorem actualRecord_eq_completeSuffixRecord_get
    (p : ConstructorDimensions.Parameters)
    (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (t : Fin p.T)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hdate : t.val = ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h ≤ t.val := by
    rw [hdate]
    exact Nat.le_add_right _ _
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = k.val := by
    omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex, List.getElem?_eq_getElem k.isLt]

private theorem no_wrong_unique_accepted_on_suffix_take
    (p : ConstructorDimensions.Parameters)
    (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (q : Fin p.T)
    (count : ℕ)
    (hcount : count ≤ q.val + 1 -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (hthrough : ∀ t : Fin p.T, t.val ≤ q.val →
      ∀ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
          some r → ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r) :
    ∀ r ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).take count,
      ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r := by
  intro r hr
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
  have hjcount : j < count := lt_of_lt_of_le hj (List.length_take_le _ _)
  have hjdate : start + j ≤ q.val := by
    dsimp only [start] at hcount ⊢
    omega
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  have hjSuffix : j < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length := by
    rw [hlen]
    omega
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).length := ⟨j, hjSuffix⟩
  let t : Fin p.T := ⟨start + j, by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h
    dsimp only [start]
    omega⟩
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] :=
    actualRecord_eq_completeSuffixRecord_get p rate source rewards C_star C_h t k (by
      dsimp only [t, k, start])
  have hsafe := hthrough t (by dsimp only [t]; exact hjdate)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val] hactual
  have hgetTake :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j]'hjSuffix =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).take count)[j]'hj := by
    exact List.getElem_take' (hj := hjcount) hjSuffix
  have hgetSuffix : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val] = r := by
    calc
      _ = (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j]'hjSuffix := rfl
      _ = ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).take count)[j]'hj := hgetTake
      _ = r := hget
  rw [← hgetSuffix]
  exact hsafe

private theorem no_wrong_unique_accepted_on_all_suffix_records
    (p : ConstructorDimensions.Parameters)
    (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hdate : ∀ t : Fin p.T,
      ∀ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
          some r → ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r) :
    ∀ r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h,
      ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r := by
  intro r hr
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).length := ⟨j, hj⟩
  let t : Fin p.T := ⟨start + j, by
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h
    dsimp only [start]
    omega⟩
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] :=
    actualRecord_eq_completeSuffixRecord_get p rate source rewards C_star C_h t k (by
      dsimp only [t, k, start])
  have hsafe := hdate t (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val] hactual
  have hgetSuffix : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val] = r := by
    simpa only [k] using hget
  rw [← hgetSuffix]
  exact hsafe

/-- The actual source's stopped wrong-completion exclusion supplies the
canonical saved-record hypothesis through and including the first physical
overflow detector. On the complement of physical overflow it supplies that
hypothesis over the entire original suffix, yielding full reward equality.

The prefix count is `q.val + 1 - s`: the record at detector date `q` is
included. Only that prefix is compared; the actual history itself retains all
physical rounds through `T`. -/
theorem actualSourceExceptionalEvent_reward_prefix_and_noOverflow_total
    (p : ConstructorDimensions.Parameters)
    (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (hwrong : source ∉ ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
      rate rewards C_star C_h) :
    (source ∈ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h →
      ∃ q : Fin p.T,
        source ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
          rate rewards C_star C_h q ∧
        let suffix := ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h
        let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
        let count := q.val + 1 - s
        let projected := (ActualCompletePhysicalHistory.postlaunchRecords
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
            p rate source rewards C_star C_h)).map
          ActualCompleteHistoryOrdinarySuffixIdentification.mixedPhysicalProjection
        projected.take count =
            (suffix.map ReferenceActiveStoppedPrefixCoupling.referencePhysical).take count ∧
          ActualInitializationPhysicalRewards.sourceInitializationReward
              (p := p) (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) source +
            ((projected.take count).map
              ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum =
          ReferenceInitializationPhysicalRewards.boundaryReward p
              (ReferenceCompletePhysicalHistory.generatedBoundary
                rate source rewards C_star C_h) +
            ((suffix.take count).map
              ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum) ∧
    (source ∉ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h →
      ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
          (p := p) (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) source =
        ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h) := by
  constructor
  · intro hphysical
    obtain ⟨q, hdetector, hthrough⟩ :=
      ReferenceCompleteInclusivePhysicalDecoderErrors.no_wrong_unique_accepted_through_actual_first_detector
        rate rewards C_star C_h source hwrong hphysical
    let u := ActualInitializationHorizon.sourceInitializedRun
      p rate source rewards C_star C_h
    cases hdisposition : u.terminalDisposition with
    | continueNext next carry =>
        have hstopped := u.terminal_stopped
        rw! [hdisposition] at hstopped
        exact hstopped.elim
    | launched launch seed =>
        obtain ⟨_active, _hspan, _hmode, _hhandoff, _hcorrected, hstart,
          _hinitReward, _hrecords, hprefix, _hfull⟩ :=
          ActualCompleteRewardPrefixComparison.sourceInitializedRun_launched_canonical_comparison
            p rate source rewards C_star C_h hinit hfalse launch seed hdisposition
        let suffix := ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h
        let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
        let count := q.val + 1 - s
        let projected := (ActualCompletePhysicalHistory.postlaunchRecords
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
            p rate source rewards C_star C_h)).map
          ActualCompleteHistoryOrdinarySuffixIdentification.mixedPhysicalProjection
        have hcount : count ≤ p.T - launch.monitor.launchPosition := by
          dsimp only [count, s]
          rw [← hstart]
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h
          omega
        have hgood : ∀ record ∈ suffix.take count,
            ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
          exact no_wrong_unique_accepted_on_suffix_take p rate source rewards C_star C_h
            q count (by dsimp only [count, s]; omega) hthrough
        have hprefixResult := hprefix count hcount hgood
        refine ⟨q, hdetector, ?_⟩
        simpa only [suffix, s, count, projected] using hprefixResult
    | exhausted live =>
        have hexhausted :=
          ActualCompleteHistoryOrdinarySuffixIdentification.sourceInitializedRun_exhausted_no_postlaunch
            p rate source rewards C_star C_h hinit hfalse live hdisposition
        have hnone := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
          rate source rewards C_star C_h).2 hexhausted.1
        have hcharacterization :=
          ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
            rate rewards C_star C_h source
        rw [hnone] at hcharacterization
        rcases hcharacterization with ⟨_, _, _, hnoOverflow, _⟩
        exact (hnoOverflow hphysical).elim
  · intro hnoPhysical
    have hdate :=
      ReferenceCompleteInclusivePhysicalDecoderErrors.no_wrong_unique_accepted_all_suffix_dates_of_no_physical_overflow
        rate rewards C_star C_h source hwrong hnoPhysical
    have hgood := no_wrong_unique_accepted_on_all_suffix_records
      p rate source rewards C_star C_h hdate
    exact ActualCompleteRewardPrefixComparison.sourceInitializedActualCompleteTotalReward_eq_completeReward
      p rate source rewards C_star C_h hinit hfalse hgood

end Bandits.Support.ActualCompleteSourceEventRewardCoupling

end
