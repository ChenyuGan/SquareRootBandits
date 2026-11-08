/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCalendarPendingTotal

import Lean.Elab.Tactic.Omega

/-!
# Raw first-collection numerical coverage

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-278`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,425-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.

The original collection-window dates produce their actual boundary and unique
full-coordinate numerical cells. The current cell is retained at a first
overflow crossing. A separate strict-past decoder condition identifies dates
in the existing awaited support.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRawCalendarNumericalCoverage

abbrev Cell (p : ConstructorDimensions.Parameters) :=
  RecordedQueueRun.RoundInput p.K

abbrev Observation (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceCompleteFirstPhaseObservationRecovery.OBS rate

private theorem collectionWindow_prefix_drop {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) :
    ReferenceCollectionPhaseHistory.collectionWindow records w <+: records.drop w := by
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  have htail :
      (records.drop (w + 1)).takeWhile
        (fun record : ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.laterChosen record.input) <+:
        records.drop (w + 1) := List.takeWhile_prefix _
  obtain ⟨suffix, hsuffix⟩ := htail
  have hhead : (records.drop w).take 1 ++ records.drop (w + 1) = records.drop w := by
    simp
  refine ⟨suffix, ?_⟩
  calc
    ((records.drop w).take 1 ++
        (records.drop (w + 1)).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)) ++ suffix =
      (records.drop w).take 1 ++
        ((records.drop (w + 1)).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ++ suffix) := by
            simp [List.append_assoc]
    _ = (records.drop w).take 1 ++ records.drop (w + 1) := by rw [hsuffix]
    _ = records.drop w := hhead

private theorem completeSuffix_record_time
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    {i : ℕ}
    (hi : i < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen : R.length = p.T - b := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  have hi' : i < p.T - b := by rw [← hlen]; exact hi
  have hic : i < (ReferenceActivePhysicalHorizon.calendar b (p.T - b)).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hi'
  have hmap := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hlookup := congrArg (fun xs : List ℕ => xs[i]?) hmap
  have hleft :
      (R.map (fun record => record.input.time.val))[i]? =
        some (R[i].input.time.val) := by
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp
  have hright :
      (ReferenceActivePhysicalHorizon.calendar b (p.T - b))[i]? = some (b + i) := by
    rw [List.getElem?_eq_getElem hic]
    simp [ReferenceActivePhysicalHorizon.calendar]
  rw [hleft, hright] at hlookup
  exact Option.some.inj hlookup

private theorem raw_calendar_date
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length).length) :
    ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length)[k.val]'k.isLt).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length +
        k.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  have hprefix : B <+: R.drop w := collectionWindow_prefix_drop R w
  rcases hprefix with ⟨tail, hprefix⟩
  have hkB : k.val < B.length := k.isLt
  have hprefixLength : B.length + tail.length = (R.drop w).length := by
    simpa only [List.length_append] using congrArg List.length hprefix
  have hdropIndex : k.val < (R.drop w).length := by
    rw [← hprefixLength]
    omega
  have hget : B[k.val]'hkB = (R.drop w)[k.val]'hdropIndex := by
    have happ : k.val < (B ++ tail).length := by
      simp only [List.length_append]
      omega
    calc
      B[k.val] = (B ++ tail)[k.val] :=
        (List.getElem_append_left (as := B) (bs := tail)
          (i := k.val) hkB).symm
      _ = (R.drop w)[k.val] := List.getElem_of_eq hprefix happ
  have hindex : w + k.val < R.length := by
    have hdropIndex' : k.val < R.length - w := by
      simpa only [List.length_drop] using hdropIndex
    omega
  have hrecordTime := completeSuffix_record_time rate rewards C_star C_h z hindex
  calc
    B[k.val].input.time.val = (R.drop w)[k.val].input.time.val :=
      congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate) => record.input.time.val) hget
    _ = R[w + k.val].input.time.val := by simp
    _ = b + (w + k.val) := hrecordTime
    _ = b + w + k.val := by omega

private theorem coherence_of_local_matches
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {b u : ℕ} (t0 t1 : Fin p.T) (hbu : b ≤ u) (hut : u ≤ t0.val)
    (hdate : t0.val ≤ t1.val) (omega : Observation p rate)
    (N0 N1 : List (Cell p)) (c0 c1 : Cell p)
    (hm0 : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
      rate b u t0 omega N0 c0)
    (hm1 : ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
      rate b u t1 omega N1 c1) :
    N0 ++ [c0] = (N1 ++ [c1]).take (N0.length + 1) :=
  ReferenceFirstCollectionQueuePrefixChronology.whole_matches_prefix
    rate t0 t1 hbu hut hdate omega N0 N1 c0 c1 hm0 hm1

variable {p : ConstructorDimensions.Parameters}

/-- Every actual raw collection date has its original physical boundary and
the unique full numerical pair, whose `Matches` body includes the strict-past
length and every `numericalLookup` coordinate through the current cell. -/
public theorem original_raw_calendar_numerical_coverage
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    ∀ k : Fin B.length,
      b ≤ b + w ∧ b + w ≤ B[k.val].input.time.val ∧ w < R.length ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
          rate rewards C_star C_h b (b + w) B[k.val].input.time ∧
        ∃! pair : List (Cell p) × Cell p,
          ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
            rate b (b + w) B[k.val].input.time omega pair.1 pair.2 := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z
  intro k
  have hQ := ReferenceFirstCollectionCalendarPendingTotal.original_raw_calendar_pending_nonempty
    rate rewards C_star C_h z k
  have hPraw : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h B[k.val].input.time.val z).Nonempty := by
    rw [ReferenceFirstCollectionPendingObservation.Praw_at]
    exact hQ
  obtain ⟨pair, hboundary⟩ :=
    (ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      B[k.val].input.time z hPraw).exists
  rcases pair with ⟨s, u⟩
  rcases hboundary with ⟨hsu, hut, hC, hs, hu, hw⟩
  have hs' : s = b := by simpa [b] using hs
  have hu' : u = b + w := by simpa [b, w] using hu
  subst s
  subst u
  have hw' : w < R.length := by simpa [R, w] using hw
  have hmatch :=
    ReferenceFirstCollectionActiveBoundaryQueueQuery.existsUnique_matching
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      b (b + w) B[k.val].input.time (by omega) hut z hC
  exact ⟨by omega, hut, hw', hC, hmatch⟩

/-- The unique pairs produced at two actual raw dates agree on the first
date's whole prefix, including its current cell. The source-record calendar
proves that list order agrees with date order. -/
public theorem original_raw_calendar_prefix_coherence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    ∀ k0 k1 : Fin B.length, k0 ≤ k1 →
      let t0 := B[k0.val].input.time
      let t1 := B[k1.val].input.time
      ∃! pair0 : List (Cell p) × Cell p,
        ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
          rate b (b + w) t0 omega pair0.1 pair0.2 ∧
        ∃! pair1 : List (Cell p) × Cell p,
          ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
            rate b (b + w) t1 omega pair1.1 pair1.2 ∧
          pair0.1 ++ [pair0.2] =
            (pair1.1 ++ [pair1.2]).take (pair0.1.length + 1) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z
  intro k0 k1 hk
  have hdate0 := raw_calendar_date rate rewards C_star C_h z k0
  have hdate1 := raw_calendar_date rate rewards C_star C_h z k1
  have hdate : B[k0.val].input.time.val ≤ B[k1.val].input.time.val := by
    rw [hdate0, hdate1]
    omega
  have hcoverage0 := original_raw_calendar_numerical_coverage
    rate rewards C_star C_h z k0
  have hcoverage1 := original_raw_calendar_numerical_coverage
    rate rewards C_star C_h z k1
  rcases hcoverage0 with ⟨hbu0, hut0, hw0, hC0, hunique0⟩
  rcases hcoverage1 with ⟨hbu1, hut1, hw1, hC1, hunique1⟩
  rcases hunique0 with ⟨pair0, hm0, hu0⟩
  rcases hunique1 with ⟨pair1, hm1, hu1⟩
  have hprefix := coherence_of_local_matches rate
    (B[k0.val].input.time) (B[k1.val].input.time) hbu0 hut0 hdate omega
    pair0.1 pair1.1 pair0.2 pair1.2 hm0 hm1
  refine ⟨pair0, ⟨hm0, ?_⟩, ?_⟩
  · refine ⟨pair1, ⟨hm1, hprefix⟩, ?_⟩
    intro q hq
    exact hu1 q hq.1
  · intro q hq
    exact hu0 q hq.1

/-- At each produced pair, queue admissibility is precisely strict-past
first-overflow comparison. The current cell is retained, so a crossing in
that cell does not remove its date from coverage. -/
public theorem original_raw_calendar_queue_event_current_overflow
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    ∀ k : Fin B.length,
      let t := B[k.val].input.time
      ∃ N : List (Cell p), ∃ c : Cell p,
        (∃! pair : List (Cell p) × Cell p,
          ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
            rate b (b + w) t omega pair.1 pair.2) ∧
        ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
          rate b (b + w) t omega N c ∧
        (z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          b (b + w) t ↔
          N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) (N ++ [c])) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z
  intro k
  have hcoverage := original_raw_calendar_numerical_coverage
    rate rewards C_star C_h z k
  rcases hcoverage with ⟨hbu, hut, _hw, hC, hunique⟩
  rcases hunique with ⟨pair, hm, huniq⟩
  rcases pair with ⟨N, c⟩
  have hUnique : ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
        rate b (b + w) B[k.val].input.time omega pair.1 pair.2 :=
    ⟨(N, c), hm, huniq⟩
  have hEvent :=
    ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_iff_before_current_firstOverflow
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      b (b + w) B[k.val].input.time hbu hut z hC N c hm
  exact ⟨N, c, hUnique, hm, hEvent⟩

/-- Conditional on the literal strict-past failure flag being false, a raw
collection date belongs to the existing awaited phase support. This is a
support inclusion, with no stopped-charge assertion. -/
public theorem original_raw_calendar_awaited_support_of_no_past_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    ∀ k : Fin B.length,
      ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h B[k.val].input.time.val z = false →
      B[k.val].input.time.val ∈
        ReferenceFirstCollectionAwaitedPhaseSupport.supportIndices
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  intro k hfailure
  have hQ := ReferenceFirstCollectionCalendarPendingTotal.original_raw_calendar_pending_nonempty
    rate rewards C_star C_h z k
  have hraw : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h B[k.val].input.time.val z).Nonempty := by
    rw [ReferenceFirstCollectionPendingObservation.Praw_at]
    exact hQ
  obtain ⟨i, hi⟩ := hraw
  have hawait : i ∈ ReferenceFirstCollectionAwaitedTaskSupport.Pawait
      rate rewards C_star C_h B[k.val].input.time.val z :=
    (ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
      rate rewards C_star C_h B[k.val].input.time.val z i).2 ⟨hfailure, hi⟩
  exact (ReferenceFirstCollectionAwaitedPhaseSupport.mem_supportIndices_iff
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z
    B[k.val].input.time.val).2 ⟨B[k.val].input.time.isLt, ⟨i, hawait⟩⟩

end Bandits.Support.ReferenceFirstCollectionRawCalendarNumericalCoverage
