/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureRetainedMoments

import Mathlib.Tactic

/-!
# Inclusive endpoint of the actual first-replacement slice

The endpoint is read from the original renewal source records. It includes a
first cutoff record after its update and stops before any other noncontinuing
record. No search over successful numerical cells is used.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureSliceEndpoint

open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalNextPhysicalPrefix
open ReferenceFirstReplacementLiveFollowerPrefix

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t

/-- The original complete physical suffix retained by the admitted renewal
source. -/
def sourceRecords (z : Z) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
    rate rewards C_star C_h u t z

/-- The original launch index in that suffix. -/
def sourceStart (z : Z) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
    rate rewards C_star C_h u t z

/-- The actual continuing records after the renewal call, with the literal
constructor test and original calendar order. -/
def continuingRecords (z : Z) :=
  ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
    rate rewards C_star C_h u t z

/-- First calendar date after the inherited whole prefix. -/
def beginning : ℕ := t.val + 1

/-- Number of actual continuing records in the first-replacement slice. -/
def continuingLength (z : Z) := (continuingRecords rate rewards C_star C_h u t z).length

/-- The calendar index of the first record excluded by the continuing prefix. -/
def continuingEnd (z : Z) := beginning t + continuingLength rate rewards C_star C_h u t z

/-- The original record immediately after the continuing prefix, if it exists.
Its list index is the original suffix offset `v + 1 + ell`. -/
def firstNoncontinuingRecord (z : Z) :
    Option (ReferenceFirstCollectionSamplerCall.RoundRecord p rate) :=
  (sourceRecords rate rewards C_star C_h u t z)[
    (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z]?

/-- Include one extra calendar position exactly when the actual excluded
record is the first detecting cutoff update. -/
def cutoffEndpointDelta (z : Z) : ℕ :=
  match firstNoncontinuingRecord rate rewards C_star C_h u t z with
  | some r =>
      match r.output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen ..) => 1
      | _ => 0
  | none => 0

/-- Inclusive endpoint of this actual slice. -/
def endpointIndex (z : Z) : ℕ :=
  continuingEnd rate rewards C_star C_h u t z +
    cutoffEndpointDelta rate rewards C_star C_h u t z

/-- The ordinary source-prefix readout at the inclusive endpoint. -/
def endpointReadout (z : Z) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rate rewards C_star C_h u t (endpointIndex rate rewards C_star C_h u t z) z

/-- Literal retained support: the actual future parameter projection is
present and the actual inherited optional queue readout is present. -/
def supportTest (q : Fin p.T) (hfuture : t.val + 1 < q.val) (z : Z) : Prop :=
  (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture).isSome = true ∧
    (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
      rate rewards C_star C_h u t q z).isSome = true

private theorem suffix_length (z : Z) :
    (sourceRecords rate rewards C_star C_h u t z).length =
      p.T - sourceStart rate rewards C_star C_h u t z := by
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards
      C_star C_h).length =
    p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  rw [← ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z]
  exact ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
    rate rewards C_star C_h u t z

private theorem continuing_length_le (z : Z) :
    continuingLength rate rewards C_star C_h u t z ≤
      p.T - (t.val + 1) := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have htail :
      ((sourceRecords rate rewards C_star C_h u t z).drop
        (t.val - sourceStart rate rewards C_star C_h u t z + 1)).takeWhile
          isContinuingChosen <+:
        (sourceRecords rate rewards C_star C_h u t z).drop
          (t.val - sourceStart rate rewards C_star C_h u t z + 1) :=
    List.takeWhile_prefix _
  have hlen := suffix_length rate rewards C_star C_h u t z
  unfold continuingLength
  change (((sourceRecords rate rewards C_star C_h u t z).drop
      (t.val - sourceStart rate rewards C_star C_h u t z + 1)).takeWhile
        isContinuingChosen).length ≤ p.T - (t.val + 1)
  calc
    _ ≤ ((sourceRecords rate rewards C_star C_h u t z).drop
        (t.val - sourceStart rate rewards C_star C_h u t z + 1)).length := htail.length_le
    _ = (sourceRecords rate rewards C_star C_h u t z).length -
          (t.val - sourceStart rate rewards C_star C_h u t z + 1) := by
          simp only [List.length_drop]
    _ = p.T - sourceStart rate rewards C_star C_h u t z -
          (t.val - sourceStart rate rewards C_star C_h u t z + 1) := by rw [hlen]
    _ ≤ p.T - (t.val + 1) := by
          have hs' : sourceStart rate rewards C_star C_h u t z ≤ t.val := by
            simpa only [sourceStart] using hs
          omega

private theorem firstNoncontinuing_index (z : Z) :
    (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z =
        continuingEnd rate rewards C_star C_h u t z -
          sourceStart rate rewards C_star C_h u t z := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have hs' : sourceStart rate rewards C_star C_h u t z ≤ t.val := by
    simpa only [sourceStart] using hs
  simp only [continuingEnd, beginning, sourceStart]
  omega

private theorem cutoffEndpoint_lt_horizon (z : Z)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1) :
    continuingEnd rate rewards C_star C_h u t z < p.T := by
  have hsome : (firstNoncontinuingRecord rate rewards C_star C_h u t z).isSome = true := by
    unfold cutoffEndpointDelta at hdelta
    cases hr : firstNoncontinuingRecord rate rewards C_star C_h u t z with
    | none => simp [hr] at hdelta
    | some r => simp
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hidx, _⟩ := List.getElem?_eq_some_iff.mp hr
  have hlen := suffix_length rate rewards C_star C_h u t z
  rw [firstNoncontinuing_index rate rewards C_star C_h u t z] at hidx
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have hs' : sourceStart rate rewards C_star C_h u t z ≤ t.val := by
    simpa only [sourceStart] using hs
  have hend : sourceStart rate rewards C_star C_h u t z ≤
      continuingEnd rate rewards C_star C_h u t z := by
    simp only [continuingEnd, beginning, sourceStart]
    omega
  dsimp only [sourceStart] at hidx hlen ⊢
  omega

/-- The inclusive slice endpoints are ordered and stay within the original
finite horizon. -/
theorem endpoint_bounds (z : Z) :
    beginning t ≤ continuingEnd rate rewards C_star C_h u t z ∧
    continuingEnd rate rewards C_star C_h u t z ≤ endpointIndex rate rewards C_star C_h u t z ∧
    endpointIndex rate rewards C_star C_h u t z ≤ p.T := by
  have hlen := continuing_length_le rate rewards C_star C_h u t z
  have hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z ≤ 1 := by
    unfold cutoffEndpointDelta
    cases firstNoncontinuingRecord rate rewards C_star C_h u t z with
    | none => simp
    | some r =>
        cases hcoord : r.output.preparation.coordinator with
        | live registers owned base outcome =>
            cases outcome <;> simp [hcoord]
        | first outcome => simp [hcoord]
        | collection payload ledger clock cutoff outcome => simp [hcoord]
        | invalidCollectionCutoff => simp [hcoord]
        | dagger => simp [hcoord]
  have hs : sourceStart rate rewards C_star C_h u t z ≤ t.val :=
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
  have hcalendar : t.val + 1 + continuingLength rate rewards C_star C_h u t z ≤ p.T := by
    omega
  constructor
  · exact Nat.le_add_right _ _
  constructor
  · exact Nat.le_add_right _ _
  · by_cases hd : cutoffEndpointDelta rate rewards C_star C_h u t z = 1
    · have he := cutoffEndpoint_lt_horizon rate rewards C_star C_h u t z hd
      have hstep : continuingEnd rate rewards C_star C_h u t z + 1 ≤ p.T :=
        Nat.succ_le_iff.mpr he
      simpa only [endpointIndex, hd] using hstep
    · have hd0 : cutoffEndpointDelta rate rewards C_star C_h u t z = 0 := by omega
      simp only [endpointIndex, hd0, continuingEnd, beginning]
      exact hcalendar

/-- At the terminal prefix there is no record at the would-be endpoint, so
the inclusive selector remains the physical horizon and does not name a
fictitious `Fin T` action. -/
theorem terminal_endpoint (z : Z)
    (hend : continuingEnd rate rewards C_star C_h u t z = p.T) :
    firstNoncontinuingRecord rate rewards C_star C_h u t z = none ∧
    cutoffEndpointDelta rate rewards C_star C_h u t z = 0 ∧
    endpointIndex rate rewards C_star C_h u t z = p.T := by
  have hidx := firstNoncontinuing_index rate rewards C_star C_h u t z
  have hlen := suffix_length rate rewards C_star C_h u t z
  have hi : (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z =
      (sourceRecords rate rewards C_star C_h u t z).length := by
    rw [hidx, hend, hlen]
  have hnone : firstNoncontinuingRecord rate rewards C_star C_h u t z = none := by
    unfold firstNoncontinuingRecord
    rw [hi]
    exact List.getElem?_eq_none (Nat.le_refl _)
  refine ⟨hnone, ?_, ?_⟩
  · simp [cutoffEndpointDelta, hnone]
  · simpa [endpointIndex, cutoffEndpointDelta, hnone] using hend

/-- The actual inherited optional readout at the immediate successor boundary
is present, with all whole-prefix registers and histories. -/
theorem readout_at_beginning (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (beginning t) z =
      some (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z) := by
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
        C_star C_h u t (t.val + 1) z) = _
  exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_readout
    rate rewards C_star C_h u t z

private theorem sourceRecords_eq_nextSourceRecords (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z := rfl

private theorem sourceStart_eq_nextStart (z : Z) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z := by
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = _
  exact (ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z).symm

/-- The immediate next record is the same original record used by the next
physical-prefix API. -/
private theorem futureRecord_eq_nextRecord (z : Z) (hq : t.val + 1 < p.T) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord rate rewards
        C_star C_h u t ⟨t.val + 1, hq⟩ z =
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards
        C_star C_h u t z hq := by
  have hrecords := sourceRecords_eq_nextSourceRecords rate rewards C_star C_h u t z
  have hstart := sourceStart_eq_nextStart rate rewards C_star C_h u t z
  have hsourcele := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have hnextle : ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z ≤ t.val := by
    rw [← hstart]
    exact hsourcele
  have hindex :
      t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z =
        t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
          rate rewards C_star C_h u t z + 1 := by
    rw [hstart]
    omega
  cases hrecords
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord
    ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
    ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextIndex
  congr 1
  apply Fin.ext
  simpa only [Fin.val_mk] using hindex

/-- At the immediate next date, both public next-date APIs produce the
baseline readout for every successful live-continuing or cutoff constructor. -/
private theorem immediate_futureCell_present (z : Z) (hq : t.val + 1 < p.T)
    (hgood : match (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).output.preparation.coordinator with
      | .live _ _ _ (.continuingChosen ..) => True
      | .live _ _ _ (.cutoffChosen ..) => True
      | _ => False) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell rate rewards
      C_star C_h u t ⟨t.val + 1, hq⟩ z).isSome = true := by
  have hdate := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts
    rate rewards C_star C_h u t z hq
  have hbaseline := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_baseline_readouts
    rate rewards C_star C_h u t z hq
  cases hcoord : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen =>
          simp only [hcoord] at hdate hgood
          obtain ⟨c, hnext, _hread, _hnone, _hnone0⟩ := hdate
          have hread := hbaseline.1.trans hnext
          rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell,
            ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell,
            futureRecord_eq_nextRecord rate rewards C_star C_h u t z hq]
          simp [hread]
      | cutoffChosen =>
          simp only [hcoord] at hdate hgood
          obtain ⟨c, hnext, _hread, _hnone, _hnone0⟩ := hdate
          have hread := hbaseline.2.trans hnext
          rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell,
            ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell,
            futureRecord_eq_nextRecord rate rewards C_star C_h u t z hq]
          simp [hread]
      | clockFailure => simp [hcoord] at hgood
      | initializerFailure => simp [hcoord] at hgood
      | localFailure => simp [hcoord] at hgood
  | first outcome => simp [hcoord] at hgood
  | collection payload ledger clock cutoff outcome => simp [hcoord] at hgood
  | invalidCollectionCutoff => simp [hcoord] at hgood
  | dagger => simp [hcoord] at hgood

private theorem nextRecord_is_continuing_of_nonempty (z : Z)
    (hq : t.val + 1 < p.T)
    (hnonempty : 0 < continuingLength rate rewards C_star C_h u t z) :
    match (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) => True
    | _ => False := by
  have hlen : 0 <
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := by
    simpa only [continuingLength, continuingRecords] using hnonempty
  let i : Fin (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).length := ⟨0, hlen⟩
  have hchosen := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
      rate rewards C_star C_h u t z)
    (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z)
    ((ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).get i)
    (List.get_mem _ _)
  have htail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
      rate rewards C_star C_h u t z)
    (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z) i
  simp only [i, Nat.add_zero] at htail
  have hnext := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_lookup
    rate rewards C_star C_h u t z hq
  have hrecord : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq =
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).get i :=
    Option.some.inj (hnext.symm.trans htail)
  rw [← hrecord] at hchosen
  cases hcoord : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome <;> simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hchosen ⊢
  | first outcome => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
      hcoord] at hchosen ⊢
  | collection payload ledger clock cutoff outcome =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hchosen ⊢
  | invalidCollectionCutoff =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hchosen ⊢
  | dagger =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hchosen ⊢

/-- The public next-date producer supplies the immediate numerical cell when
the actual continuing slice is nonempty. -/
theorem immediate_futureCell_present_of_continuing_nonempty (z : Z)
    (hq : t.val + 1 < p.T)
    (hnonempty : 0 < continuingLength rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell rate rewards
      C_star C_h u t ⟨t.val + 1, hq⟩ z).isSome = true := by
  have hgood : match (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) => True
    | .live _ _ _ (.cutoffChosen ..) => True
    | _ => False := by
    have hc := nextRecord_is_continuing_of_nonempty rate rewards C_star C_h u t z hq hnonempty
    cases hcoord : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | live registers owned base outcome => cases outcome <;> simp [hcoord] at hc ⊢
    | first outcome => simp [hcoord] at hc ⊢
    | collection payload ledger clock cutoff outcome => simp [hcoord] at hc ⊢
    | invalidCollectionCutoff => simp [hcoord] at hc ⊢
    | dagger => simp [hcoord] at hc ⊢
  exact immediate_futureCell_present rate rewards C_star C_h u t z hq hgood

private theorem calendarCells_immediate_succ (z : Z) (hq : t.val + 1 < p.T) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
        C_star C_h u t (t.val + 2) z =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
        C_star C_h u t (t.val + 1) z ++
          [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell rate rewards
            C_star C_h u t ⟨t.val + 1, hq⟩ z] := by
  have hlen := suffix_length rate rewards C_star C_h u t z
  change (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z).length =
    p.T - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z at hlen
  have hindex : t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z <
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).length := by
    rw [hlen]
    have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z ≤ t.val at hs
    omega
  have hget := List.getElem?_eq_getElem hindex
  have hsub : t.val + 2 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
      (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z) + 1 := by
    have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z ≤ t.val at hs
    omega
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
  rw [hsub, List.take_add_one, hget, List.map_append]
  rfl

/-- The first appended prefix readout is present when the actual continuing
slice has a next record. The whole inherited prefix is retained by `mapM`. -/
theorem immediate_futurePrefixReadout_present_of_continuing_nonempty (z : Z)
    (hq : t.val + 1 < p.T)
    (hnonempty : 0 < continuingLength rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout rate rewards
      C_star C_h u t (t.val + 2) z).isSome = true := by
  have hcell := immediate_futureCell_present_of_continuing_nonempty
    rate rewards C_star C_h u t z hq hnonempty
  obtain ⟨c, hc⟩ : ∃ c, ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
      rate rewards C_star C_h u t ⟨t.val + 1, hq⟩ z = some c := by
    cases h : ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell rate rewards
        C_star C_h u t ⟨t.val + 1, hq⟩ z with
    | none => simp [h] at hcell
    | some c => exact ⟨c, rfl⟩
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
  rw [calendarCells_immediate_succ rate rewards C_star C_h u t z hq, hc]
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout_append
    rate (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
      C_star C_h u t (t.val + 1) z) (some c)]
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
    rate rewards C_star C_h u t z]
  rfl

/-- Every actual member of the continuing slice has its live physical cell
present at its original future date. -/
theorem continuing_futureCell_present (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hk : q.val - (t.val + 1) < continuingLength rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture).isSome = true := by
  have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_live_readout
    rate rewards C_star C_h u t z q hfuture hk
  obtain ⟨cell, _, hzero, _, _, _, _, _, _⟩ := hread
  have hrecord := ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_eq_continuing
    rate rewards C_star C_h u t z q hfuture hk
  have hcontinuing := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem
    (sourceRecords rate rewards C_star C_h u t z)
    (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z)
    ((ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).get ⟨q.val - (t.val + 1), by
        simpa only [continuingLength, continuingRecords] using hk⟩)
    (List.get_mem _ _)
  rw [← hrecord] at hcontinuing
  have hbranch : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture = some false := by
    have hle : q.val - (t.val + 1) ≤
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
          rate rewards C_star C_h u t z).length := by
      simpa only [continuingLength, continuingRecords] using Nat.le_of_lt hk
    unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
    rw [ite_eq_left hle]
    rw [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag_eq]
    cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
    | live registers owned base outcome =>
        cases outcome <;> simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
          hcoord, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
          ReferenceLiveDispatchOutputMeasurability.outcomeData] at hcontinuing ⊢
    | first outcome => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
    | collection payload ledger clock cutoff outcome => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
    | invalidCollectionCutoff => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
    | dagger => simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
        hcoord] at hcontinuing
  unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
  rw [hbranch]
  simp [hzero]

/-- A present inherited prefix stays present after appending a present actual
numerical cell through the public optional-readout recursion. -/
private theorem futurePrefixReadout_succ_present (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hprefix : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t q.val z).isSome = true)
    (hcell : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
      rate rewards C_star C_h u t q z).isSome = true) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z).isSome = true := by
  cases hp : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
        C_star C_h u t q.val z) with
  | none =>
      have hnone : ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t q.val z = none := by
        unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout
        simp only [hp]
        rfl
      rw [hnone] at hprefix
      cases hprefix
  | some inputs =>
      cases hc : ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
          rate rewards C_star C_h u t q z with
      | none => simp [hc] at hcell
      | some c =>
          rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout_succ
            rate rewards C_star C_h u t q z hfuture]
          simp [hp, hc]

private theorem futurePrefixReadout_present_between_beginning_and_end
    (z : Z) (n : ℕ)
    (hbegin : beginning t + 1 ≤ n)
    (hend : n ≤ continuingEnd rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t n z).isSome = true := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n = beginning t + 1
      · subst n
        have hlen : 0 < continuingLength rate rewards C_star C_h u t z := by
          unfold continuingEnd beginning at hend
          omega
        have heT : t.val + 1 < p.T := by
          have hb := endpoint_bounds rate rewards C_star C_h u t z
          have hT : continuingEnd rate rewards C_star C_h u t z ≤ p.T :=
            hb.2.1.trans hb.2.2
          unfold beginning at hend
          omega
        exact immediate_futurePrefixReadout_present_of_continuing_nonempty
          rate rewards C_star C_h u t z heT hlen
      · have hprev : beginning t + 1 ≤ n - 1 := by omega
        have hprevEnd : n - 1 ≤ continuingEnd rate rewards C_star C_h u t z := by omega
        have hprior := ih (n - 1) (by omega) hprev hprevEnd
        have hqLt : n - 1 < p.T := by
          have hb := endpoint_bounds rate rewards C_star C_h u t z
          have hT : continuingEnd rate rewards C_star C_h u t z ≤ p.T :=
            hb.2.1.trans hb.2.2
          omega
        let q : Fin p.T := ⟨n - 1, hqLt⟩
        have hfuture : t.val + 1 < q.val := by
          dsimp [q, beginning] at hbase hbegin ⊢
          omega
        have hcellV :
            (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
              rate rewards C_star C_h u t z q hfuture).isSome = true := by
          apply continuing_futureCell_present rate rewards C_star C_h u t z q hfuture
          have hlen : n - 1 - (t.val + 1) <
              continuingLength rate rewards C_star C_h u t z := by
            unfold continuingEnd beginning at hend
            dsimp [beginning] at hbegin hbase
            omega
          simpa [q] using hlen
        obtain ⟨c, hcV⟩ := Option.isSome_iff_exists.mp hcellV
        have hcN := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureSliceCell_eq_unmasked
          rate rewards C_star C_h u t q hfuture z c hcV
        have hcellN :
            (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
              rate rewards C_star C_h u t q z).isSome = true := by
          rw [hcN]
          rfl
        have hnext := futurePrefixReadout_succ_present rate rewards C_star C_h u t z q
          hfuture hprior hcellN
        have hqeq : q.val + 1 = n := by
          dsimp [q]
          omega
        rw [hqeq] at hnext
        exact hnext

/-- Every prefix ending at or before the first excluded record is present.
This uses the actual immediate producer and each continuing live readout. -/
theorem futurePrefixReadout_present_through_continuingEnd (z : Z) (n : ℕ)
    (hbegin : beginning t ≤ n)
    (hend : n ≤ continuingEnd rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t n z).isSome = true := by
  by_cases hbase : n = beginning t
  · subst n
    rw [readout_at_beginning rate rewards C_star C_h u t z]
    rfl
  · have hsucc : beginning t + 1 ≤ n := by omega
    exact futurePrefixReadout_present_between_beginning_and_end rate rewards C_star C_h u t z n
      hsucc hend

/-- If the source has no first cutoff update, the inclusive endpoint readout
is the already-proved prefix through the continuing end. -/
theorem endpointReadout_present_of_no_cutoff (z : Z)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 0) :
    (endpointReadout rate rewards C_star C_h u t z).isSome = true := by
  have hb := endpoint_bounds rate rewards C_star C_h u t z
  simpa [endpointReadout, endpointIndex, hdelta] using
    (futurePrefixReadout_present_through_continuingEnd rate rewards C_star C_h u t z
      (continuingEnd rate rewards C_star C_h u t z) hb.1 (Nat.le_refl _))

/-- A true branch tag is the actual selected cutoff constructor at the first
excluded record, so the inclusive endpoint advances by exactly one. -/
theorem cutoffDelta_trueBranch (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture = some true) :
    cutoffEndpointDelta rate rewards C_star C_h u t z = 1 := by
  have hle : q.val - (t.val + 1) ≤
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := by
    unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch at hb
    split_ifs at hb with hle
    · exact hle
  have htag := hb
  unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch at htag
  rw [ite_eq_left hle] at htag
  rw [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag_eq] at htag
  have hcut : match
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen ..) => True
      | _ => False := by
    cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
        <;> simp only [hcoord] at htag ⊢ <;> try contradiction
    rename_i registers owned base outcome
    cases outcome <;> simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
      ReferenceLiveDispatchOutputMeasurability.outcomeData] at htag ⊢ <;> try contradiction
  have hoff := (ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
    rate rewards C_star C_h u t z q hfuture true hb).2 rfl
  have hcalendar : q.val = continuingEnd rate rewards C_star C_h u t z := by
    have hbase : t.val + 1 ≤ q.val := by omega
    calc
      q.val = (q.val - (t.val + 1)) + (t.val + 1) := by omega
      _ = (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
          rate rewards C_star C_h u t z).length + (t.val + 1) := by rw [hoff]
      _ = t.val + 1 +
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
            rate rewards C_star C_h u t z).length := by omega
      _ = continuingEnd rate rewards C_star C_h u t z := rfl
  have hstart : sourceStart rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z :=
    sourceStart_eq_nextStart rate rewards C_star C_h u t z
  have hindex : (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z =
      q.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z := by
    rw [firstNoncontinuing_index rate rewards C_star C_h u t z]
    rw [← hcalendar, ← hstart]
  have hrecord : firstNoncontinuingRecord rate rewards C_star C_h u t z =
      some (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture) := by
    unfold firstNoncontinuingRecord
    rw [hindex]
    exact ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_lookup
      rate rewards C_star C_h u t z q hfuture
  unfold cutoffEndpointDelta
  rw [hrecord]
  cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
      rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> simp_all
  | first outcome => simp_all
  | collection payload ledger clock cutoff outcome => simp_all
  | invalidCollectionCutoff => simp_all
  | dagger => simp_all

/-- At the first noncontinuing calendar offset, the source selector is exactly
the corresponding original future record. -/
theorem firstNoncontinuing_eq_futureRecord (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hpos : q.val - (t.val + 1) = continuingLength rate rewards C_star C_h u t z) :
    firstNoncontinuingRecord rate rewards C_star C_h u t z =
      some (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture) := by
  have hcalendar : q.val = continuingEnd rate rewards C_star C_h u t z := by
    have hoff : q.val - (t.val + 1) =
        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
          rate rewards C_star C_h u t z).length := by
      simpa only [continuingLength, continuingRecords] using hpos
    have hbase : t.val + 1 ≤ q.val := by omega
    calc
      q.val = (q.val - (t.val + 1)) + (t.val + 1) := by omega
      _ = (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
          rate rewards C_star C_h u t z).length + (t.val + 1) := by rw [hoff]
      _ = t.val + 1 +
          (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
            rate rewards C_star C_h u t z).length := by omega
      _ = continuingEnd rate rewards C_star C_h u t z := rfl
  have hstart : sourceStart rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z :=
    sourceStart_eq_nextStart rate rewards C_star C_h u t z
  have hindex : (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z =
      q.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z := by
    rw [firstNoncontinuing_index rate rewards C_star C_h u t z]
    rw [← hcalendar, ← hstart]
  unfold firstNoncontinuingRecord
  rw [hindex]
  exact ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord_lookup
    rate rewards C_star C_h u t z q hfuture

/-- Presence of both literal support projections forces the date to lie before
the inclusive endpoint. Later unmasked renewal readouts are not excluded. -/
theorem supportTest_before_endpoint (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hs : supportTest rate rewards C_star C_h u t q hfuture z) :
    q.val < endpointIndex rate rewards C_star C_h u t z := by
  have hp := hs.1
  have hview : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture).isSome = true := by
    cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q hfuture with
    | none => simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv] at hp
    | some data => simp
  have hbranch : ∃ b, ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture = some b := by
    cases hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture with
    | none =>
        have := hview
        simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
          hb] at this
    | some b => exact ⟨b, rfl⟩
  obtain ⟨b, hb⟩ := hbranch
  have hg := ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
    rate rewards C_star C_h u t z q hfuture b hb
  cases b with
  | false =>
      have hlt := hg.1 rfl
      have hend := endpoint_bounds rate rewards C_star C_h u t z
      have hqend : q.val < continuingEnd rate rewards C_star C_h u t z := by
        unfold continuingEnd beginning continuingLength continuingRecords
        omega
      exact hqend.trans_le hend.2.1
  | true =>
      have hend := hg.2 rfl
      have hdelta := cutoffDelta_trueBranch rate rewards C_star C_h u t z q hfuture hb
      have hqend : q.val = continuingEnd rate rewards C_star C_h u t z := by
        unfold continuingEnd beginning continuingLength continuingRecords
        omega
      rw [endpointIndex, hdelta]
      exact Nat.lt_succ_of_le (le_of_eq hqend)

private theorem futureParameters_present_of_futureCell (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      rw [hv] at hr
      simp only at hr
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hc.symm.trans hr.2
      cases hbad
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hr
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hr
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      have hparameters' : parameters = some (c.enabled, c.rate) := by
        rw [← hcell_eq]
        exact hparameters
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters, hv,
        hparameters']

/-- In the no-cutoff arm, the literal two-part support test is exactly the
continuing slice. Both directions use the actual cell and inherited readout. -/
theorem supportTest_iff_before_continuingEnd_of_no_cutoff (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 0) :
    supportTest rate rewards C_star C_h u t q hfuture z ↔
      q.val < continuingEnd rate rewards C_star C_h u t z := by
  constructor
  · intro hs
    have hlt := supportTest_before_endpoint rate rewards C_star C_h u t z q hfuture hs
    rw [endpointIndex, hdelta] at hlt
    exact hlt
  · intro hq
    have hpos : q.val - (t.val + 1) < continuingLength rate rewards C_star C_h u t z := by
      unfold continuingEnd beginning at hq
      omega
    have hcellV := continuing_futureCell_present rate rewards C_star C_h u t z q hfuture hpos
    obtain ⟨c, hcV⟩ := Option.isSome_iff_exists.mp hcellV
    have hparams := futureParameters_present_of_futureCell rate rewards C_star C_h u t z
      q hfuture c hcV
    have hread := futurePrefixReadout_present_through_continuingEnd rate rewards C_star C_h u t z
      q.val (by unfold beginning; omega) (le_of_lt hq)
    change (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture).isSome = true ∧
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z).isSome = true
    rw [hparams]
    refine ⟨rfl, ?_⟩
    simpa [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hread

/-- If the continuing slice is empty and the immediate actual next record is
its first cutoff update, the inclusive endpoint readout is present after that
update. The cell is produced by the public immediate-date APIs. -/
theorem endpointReadout_present_of_immediate_cutoff (z : Z)
    (hq : t.val + 1 < p.T)
    (hempty : continuingLength rate rewards C_star C_h u t z = 0)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1) :
    (endpointReadout rate rewards C_star C_h u t z).isSome = true := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  have hindex : (t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
      continuingLength rate rewards C_star C_h u t z =
        t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
          rate rewards C_star C_h u t z + 1 := by
    have hindex' := firstNoncontinuing_index rate rewards C_star C_h u t z
    unfold sourceStart at hindex' ⊢
    simp only [hempty] at hindex'
    unfold continuingEnd beginning at hindex'
    have hstart := sourceStart_eq_nextStart rate rewards C_star C_h u t z
    have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    have hs' : ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z ≤ t.val := by rw [← hstart]; exact hs
    rw [hstart]
    omega
  have hrecord : firstNoncontinuingRecord rate rewards C_star C_h u t z =
      some (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq) := by
    unfold firstNoncontinuingRecord
    change (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z)[(t.val - sourceStart rate rewards C_star C_h u t z) + 1 +
        continuingLength rate rewards C_star C_h u t z]? = _
    rw [hindex, sourceRecords_eq_nextSourceRecords rate rewards C_star C_h u t z]
    exact ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_lookup
      rate rewards C_star C_h u t z hq
  have hgood : match (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator with
      | .live _ _ _ (.continuingChosen ..) => True
      | .live _ _ _ (.cutoffChosen ..) => True
      | _ => False := by
    unfold cutoffEndpointDelta at hdelta
    rw [hrecord] at hdelta
    cases hcoord : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq).output.preparation.coordinator with
    | live registers owned base outcome =>
        cases outcome <;> simp [hcoord] at hdelta ⊢
    | first outcome => simp [hcoord] at hdelta ⊢
    | collection payload ledger clock cutoff outcome => simp [hcoord] at hdelta ⊢
    | invalidCollectionCutoff => simp [hcoord] at hdelta ⊢
    | dagger => simp [hcoord] at hdelta ⊢
  have hcell := immediate_futureCell_present rate rewards C_star C_h u t z hq hgood
  obtain ⟨c, hc⟩ : ∃ c, ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
      rate rewards C_star C_h u t q z = some c := by
    cases h : ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
        rate rewards C_star C_h u t q z with
    | none => simp [q, h] at hcell
    | some c => exact ⟨c, rfl⟩
  have hprefix : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (t.val + 2) z).isSome = true := by
    unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rw [calendarCells_immediate_succ rate rewards C_star C_h u t z hq, hc]
    rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout_append
      rate (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards
        C_star C_h u t (t.val + 1) z) (some c)]
    rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
      rate rewards C_star C_h u t z]
    rfl
  simpa [endpointReadout, endpointIndex, continuingEnd, beginning, hdelta, hempty] using hprefix

/-- The first excluded record has a present actual slice cell when its literal
constructor selects cutoff. The public cutoff readout produces the preparation
and numerical cell, including a disabled cutoff update. -/
theorem cutoff_futureCell_present (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val)
    (hpos : q.val - (t.val + 1) = continuingLength rate rewards C_star C_h u t z)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1) :
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture).isSome = true := by
  have hrecord := firstNoncontinuing_eq_futureRecord rate rewards C_star C_h u t z
    q hfuture hpos
  have hoff : q.val - (t.val + 1) =
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := hpos
  have hread := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_cutoff_readout
    rate rewards C_star C_h u t z q hfuture hoff
  unfold cutoffEndpointDelta at hdelta
  rw [hrecord] at hdelta
  cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
      rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen =>
          simp only [hcoord] at hread
          obtain ⟨c, _, hzero, _⟩ := hread
          have hbranch : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
              rate rewards C_star C_h u t z q hfuture = some true := by
            simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch,
              ite_eq_left (Nat.le_of_eq hoff),
              ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag_eq,
              hcoord, ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
              ReferenceLiveDispatchOutputMeasurability.outcomeData]
          unfold ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
          rw [hbranch]
          simp only [Option.isSome_some, ite_true]
          cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
              (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
                rate rewards C_star C_h u t z q hfuture) with
          | none => simp [hzero]
          | some d => rfl
      | continuingChosen => simp [hcoord] at hdelta
      | clockFailure => simp [hcoord] at hdelta
      | initializerFailure => simp [hcoord] at hdelta
      | localFailure => simp [hcoord] at hdelta
  | first outcome => simp [hcoord] at hdelta
  | collection payload ledger clock cutoff outcome => simp [hcoord] at hdelta
  | invalidCollectionCutoff => simp [hcoord] at hdelta
  | dagger => simp [hcoord] at hdelta

/-- A later actual cutoff is included after its detecting update. Its present
cell is appended to the whole inherited and continuing prefix. -/
theorem endpointReadout_present_of_later_cutoff (z : Z)
    (hnonempty : 0 < continuingLength rate rewards C_star C_h u t z)
    (hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1) :
    (endpointReadout rate rewards C_star C_h u t z).isSome = true := by
  have hqT := cutoffEndpoint_lt_horizon rate rewards C_star C_h u t z hdelta
  let q : Fin p.T := ⟨continuingEnd rate rewards C_star C_h u t z, hqT⟩
  have hfuture : t.val + 1 < q.val := by
    dsimp only [q, continuingEnd, beginning]
    omega
  have hpos : q.val - (t.val + 1) = continuingLength rate rewards C_star C_h u t z := by
    dsimp only [q, continuingEnd, beginning]
    omega
  have hcellV := cutoff_futureCell_present rate rewards C_star C_h u t z q hfuture hpos hdelta
  obtain ⟨c, hcV⟩ := Option.isSome_iff_exists.mp hcellV
  have hcN := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureSliceCell_eq_unmasked
    rate rewards C_star C_h u t q hfuture z c hcV
  have hcellN : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureCell
      rate rewards C_star C_h u t q z).isSome = true := by
    rw [hcN]
    rfl
  have hb := endpoint_bounds rate rewards C_star C_h u t z
  have hprefix := futurePrefixReadout_present_through_continuingEnd
    rate rewards C_star C_h u t z q.val hb.1 (Nat.le_refl _)
  have hnext := futurePrefixReadout_succ_present rate rewards C_star C_h u t z q
    hfuture hprefix hcellN
  simpa only [endpointReadout, endpointIndex, hdelta, q] using hnext

/-- The literal inclusive endpoint readout is always present on the original
source. No numerical-presence or successful-preparation premise is supplied. -/
theorem endpointReadout_present (z : Z) :
    (endpointReadout rate rewards C_star C_h u t z).isSome = true := by
  by_cases hd : cutoffEndpointDelta rate rewards C_star C_h u t z = 0
  · exact endpointReadout_present_of_no_cutoff rate rewards C_star C_h u t z hd
  · have hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1 := by
      unfold cutoffEndpointDelta at hd ⊢
      cases hr : firstNoncontinuingRecord rate rewards C_star C_h u t z with
      | none => simp [hr] at hd
      | some r =>
          cases hc : r.output.preparation.coordinator with
          | live registers owned base outcome => cases outcome <;> simp [hr, hc] at hd ⊢
          | first outcome => simp [hr, hc] at hd
          | collection payload ledger clock cutoff outcome => simp [hr, hc] at hd
          | invalidCollectionCutoff => simp [hr, hc] at hd
          | dagger => simp [hr, hc] at hd
    by_cases hempty : continuingLength rate rewards C_star C_h u t z = 0
    · have hqT : t.val + 1 < p.T := by
        have hlt := cutoffEndpoint_lt_horizon rate rewards C_star C_h u t z hdelta
        simpa only [continuingEnd, beginning, hempty, Nat.add_zero] using hlt
      exact endpointReadout_present_of_immediate_cutoff rate rewards C_star C_h u t z
        hqT hempty hdelta
    · exact endpointReadout_present_of_later_cutoff rate rewards C_star C_h u t z
        (Nat.pos_of_ne_zero hempty) hdelta

/-- Every calendar prefix from the inherited boundary through the inclusive
endpoint is present, including the entire first detecting cutoff update. -/
theorem futurePrefixReadout_present_through_endpoint (z : Z) (n : ℕ)
    (hbegin : beginning t ≤ n)
    (hend : n ≤ endpointIndex rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t n z).isSome = true := by
  by_cases he : n ≤ continuingEnd rate rewards C_star C_h u t z
  · exact futurePrefixReadout_present_through_continuingEnd
      rate rewards C_star C_h u t z n hbegin he
  · have hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z ≤ 1 := by
      unfold cutoffEndpointDelta
      cases firstNoncontinuingRecord rate rewards C_star C_h u t z with
      | none => simp
      | some r =>
          cases hc : r.output.preparation.coordinator with
          | live registers owned base outcome => cases outcome <;> simp [hc]
          | first outcome => simp [hc]
          | collection payload ledger clock cutoff outcome => simp [hc]
          | invalidCollectionCutoff => simp [hc]
          | dagger => simp [hc]
    have hlast : n = endpointIndex rate rewards C_star C_h u t z := by
      unfold endpointIndex at hend ⊢
      omega
    rw [hlast]
    exact endpointReadout_present rate rewards C_star C_h u t z

/-- Exact support of every genuine future date: both literal projections are
present exactly before the inclusive endpoint. This does not exclude later
unmasked numerical readouts after another collection or renewal. -/
theorem supportTest_iff_before_endpoint (z : Z) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    supportTest rate rewards C_star C_h u t q hfuture z ↔
      q.val < endpointIndex rate rewards C_star C_h u t z := by
  constructor
  · exact supportTest_before_endpoint rate rewards C_star C_h u t z q hfuture
  · intro hq
    have hcellV : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture).isSome = true := by
      by_cases he : q.val < continuingEnd rate rewards C_star C_h u t z
      · apply continuing_futureCell_present rate rewards C_star C_h u t z q hfuture
        unfold continuingEnd beginning at he
        omega
      · have hdelta : cutoffEndpointDelta rate rewards C_star C_h u t z = 1 := by
          by_contra hd
          have hd0 : cutoffEndpointDelta rate rewards C_star C_h u t z = 0 := by
            unfold cutoffEndpointDelta at hd ⊢
            cases hr : firstNoncontinuingRecord rate rewards C_star C_h u t z with
            | none => simp
            | some r =>
                cases hc : r.output.preparation.coordinator with
                | live registers owned base outcome => cases outcome <;> simp [hr, hc] at hd ⊢
                | first outcome => simp [hc]
                | collection payload ledger clock cutoff outcome => simp [hc]
                | invalidCollectionCutoff => simp [hc]
                | dagger => simp [hc]
          simp only [endpointIndex, hd0, Nat.add_zero] at hq
          exact he hq
        have hpos : q.val - (t.val + 1) = continuingLength rate rewards C_star C_h u t z := by
          simp only [endpointIndex, hdelta] at hq
          unfold continuingEnd beginning at he hq
          omega
        exact cutoff_futureCell_present rate rewards C_star C_h u t z q hfuture hpos hdelta
    obtain ⟨c, hcV⟩ := Option.isSome_iff_exists.mp hcellV
    have hparams := futureParameters_present_of_futureCell rate rewards C_star C_h u t z
      q hfuture c hcV
    have hread := futurePrefixReadout_present_through_endpoint rate rewards C_star C_h u t z
      q.val (by unfold beginning; omega) (Nat.le_of_lt hq)
    unfold supportTest
    rw [hparams]
    refine ⟨rfl, ?_⟩
    simpa only [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hread

end Bandits.Support.ReferenceFirstCollectionRenewalFutureSliceEndpoint
