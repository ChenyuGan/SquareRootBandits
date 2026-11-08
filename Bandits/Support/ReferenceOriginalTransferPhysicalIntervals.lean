/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts
public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Tactic

/-!
# Original transfer collection and later LIVE intervals

The outer stopped window uses the accepted ranked starts and inclusive bad
date. Every actual live cutoff produces its maximal collection segment on
the original complete suffix. Its literal next installation supplies the new
payload and missing-DOWN interval through the next cutoff or horizon.
Dates use the original one-based calendar and the sentinel `T + 1`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support
open scoped Classical

namespace Bandits.Support.ReferenceOriginalTransferPhysicalIntervals

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}

/-- The next accepted stopped physical start after zero-based rank `k`.
The sentinel is the same `T + 1` used by the accepted ranked-start list. -/
def nextStoppedTransferStartDate
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList
    rate rewards C_star C_h z).getD (k.val + 1) (p.T + 1)

/-- The right-open endpoint of the actual stopped transfer beginning at
rank `k`: the next accepted start or one date after the inclusive stop,
whichever comes first. -/
def stoppedTransferWindowEndDate
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  min (nextStoppedTransferStartDate rate rewards C_star C_h k z)
    (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z) p.T + 1)

private theorem stoppedTransferWindowEndDate_le_sentinel
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedTransferWindowEndDate rate rewards C_star C_h k z ≤ p.T + 1 := by
  unfold stoppedTransferWindowEndDate
  exact (Nat.min_le_right _ _).trans (Nat.succ_le_succ (Nat.min_le_right _ _))

private theorem present_start_precedes_bad_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤
      min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T + 1 := by
  have hmem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h k z).mp hk
  obtain ⟨q, hq, hdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z ∧
      q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z at hq
  have hcalendar : q.val + 1 ≤ p.T := by rw [hdate]; exact hk
  have hmin : q.val + 1 ≤ min
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T :=
    Nat.le_min.mpr ⟨hq.2, hcalendar⟩
  rw [← hdate]
  omega

private theorem next_start_ge_present_start
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤
      nextStoppedTransferStartDate rate rewards C_star C_h k z := by
  have hrank := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_present_exactly
    rate rewards C_star C_h k z).mp hk
  have hcount := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_card_le_horizon
    rate rewards C_star C_h z
  have hklt : k.val < p.T := Nat.lt_of_lt_of_le hrank hcount
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hknext : k ≤ next := Fin.le_iff_val_le_val.mpr (by simp [next])
  change ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z
  exact ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_monotone
    rate rewards C_star C_h k next z hknext

private theorem next_start_gt_present_start
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z <
      nextStoppedTransferStartDate rate rewards C_star C_h k z := by
  have hrank := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_present_exactly
    rate rewards C_star C_h k z).mp hk
  have hcount := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_card_le_horizon
    rate rewards C_star C_h z
  have hklt : k.val < p.T := Nat.lt_of_lt_of_le hrank hcount
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hknext : k ≤ next := Fin.le_iff_val_le_val.mpr (by simp [next])
  have hge := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_monotone
    rate rewards C_star C_h k next z hknext
  have hnextDate : nextStoppedTransferStartDate rate rewards C_star C_h k z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h next z := rfl
  have hbound := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_sentinel
    rate rewards C_star C_h next z
  by_cases hp : nextStoppedTransferStartDate rate rewards C_star C_h k z ≤ p.T
  · have hnotEq : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≠
      nextStoppedTransferStartDate rate rewards C_star C_h k z := by
      intro heq
      have hdateEq :
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z =
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h next z := by simpa only [hnextDate] using heq
      have hindices := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_injective_present
        rate rewards C_star C_h k next z hk hp hdateEq
      have hne : k ≠ next := by
        intro he
        have := congrArg Fin.val he
        dsimp only [next] at this
        omega
      exact hne hindices
    omega
  · rw [← hnextDate] at hbound
    omega

private theorem present_start_strictly_before_bad_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z <
      min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T + 1 := by
  have hmem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h k z).mp hk
  obtain ⟨q, hq, hdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z ∧
      q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z at hq
  have hcalendar : q.val + 1 ≤ p.T := by rw [hdate]; exact hk
  have hmin : q.val + 1 ≤ min
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T :=
    Nat.le_min.mpr ⟨hq.2, hcalendar⟩
  rw [← hdate]
  omega

/-- A present rank has a nonempty outer window, ending no later than the
one-past-horizon sentinel. -/
public theorem stoppedTransferWindowEndDate_bounds
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z <
      stoppedTransferWindowEndDate rate rewards C_star C_h k z ∧
    stoppedTransferWindowEndDate rate rewards C_star C_h k z ≤ p.T + 1 := by
  constructor
  · exact Nat.lt_min.mpr ⟨
      next_start_gt_present_start rate rewards C_star C_h k z hk,
      present_start_strictly_before_bad_boundary rate rewards C_star C_h k z hk⟩
  · exact stoppedTransferWindowEndDate_le_sentinel rate rewards C_star C_h k z

/-- An absent rank has an empty date interval. -/
public theorem absent_stoppedTransferWindow_empty
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ∀ d : ℕ,
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ d →
      d < stoppedTransferWindowEndDate rate rewards C_star C_h k z → False := by
  have hsent := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_sentinel
    rate rewards C_star C_h k z
  have hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z = p.T + 1 := by omega
  have hend := stoppedTransferWindowEndDate_le_sentinel rate rewards C_star C_h k z
  intro d hleft hright
  omega

/-- If rank `k + 1` is present, the current window ends exactly at that
accepted start. Thus the bad-date truncation cannot cut before a later
accepted start. -/
public theorem stoppedTransferWindowEndDate_eq_next_of_present
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hn : nextStoppedTransferStartDate rate rewards C_star C_h k z ≤ p.T) :
    stoppedTransferWindowEndDate rate rewards C_star C_h k z =
      nextStoppedTransferStartDate rate rewards C_star C_h k z := by
  have hcount := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_card_le_horizon
    rate rewards C_star C_h z
  have hrank := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_present_exactly
    rate rewards C_star C_h k z).mp hk
  have hklt : k.val < p.T := Nat.lt_of_lt_of_le hrank hcount
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hnextDate : nextStoppedTransferStartDate rate rewards C_star C_h k z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h next z := rfl
  have hnextPresent : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z ≤ p.T := by
    simpa only [hnextDate] using hn
  have hnextBad := present_start_precedes_bad_boundary rate rewards C_star C_h next z
    hnextPresent
  calc
    stoppedTransferWindowEndDate rate rewards C_star C_h k z =
        min (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h next z)
          (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z) p.T + 1) := by
              rw [stoppedTransferWindowEndDate, hnextDate]
    _ = ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h next z := Nat.min_eq_left hnextBad
    _ = nextStoppedTransferStartDate rate rewards C_star C_h k z := hnextDate.symm

/-- When the following rank is absent, the window ends at the inclusive
first-bad/horizon boundary. -/
public theorem stoppedTransferWindowEndDate_eq_bad_boundary_of_no_next
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hn : nextStoppedTransferStartDate rate rewards C_star C_h k z = p.T + 1) :
    stoppedTransferWindowEndDate rate rewards C_star C_h k z =
      min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T + 1 := by
  rw [stoppedTransferWindowEndDate, hn]
  have hbound : min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z) p.T + 1 ≤ p.T + 1 :=
    Nat.succ_le_succ (Nat.min_le_right _ _)
  exact Nat.min_eq_right hbound

/-- Ranked outer windows cannot overlap a later ranked start, including the
sentinel ranks. -/
public theorem stoppedTransferWindowEndDate_le_later_rank
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k l : Fin (p.T + 1)) (z : SourceInput p) (hkl : k < l) :
    stoppedTransferWindowEndDate rate rewards C_star C_h k z ≤
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h l z := by
  have hklt : k.val < p.T := by have := l.isLt; omega
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hnextle : next ≤ l := Fin.le_iff_val_le_val.mpr (by simp [next]; omega)
  calc
    stoppedTransferWindowEndDate rate rewards C_star C_h k z ≤
        nextStoppedTransferStartDate rate rewards C_star C_h k z :=
      Nat.min_le_left _ _
    _ = ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h next z := rfl
    _ ≤ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h l z :=
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_monotone
        rate rewards C_star C_h next l z hnextle

/-- Every present ranked stopped start is an actual original FIRST launch
or the actual live `StartRound.initializeAt` command. The record witness and
date are read from the original source API. -/
public theorem present_start_actual_first_or_live_initializeAt
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ∃ q : Fin p.T,
      q.val + 1 = ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ∧
      ((∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
            rate rewards C_star C_h q z = some record ∧
          record.input.state.coordinator = .first) ∨
        ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ)
          (started : CoordinatorPhaseClock.StartRoundResult p),
          ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
            rate rewards C_star C_h q z = some record ∧
          record.input.state.coordinator = .live registers owned base ∧
          CoordinatorPhaseClock.startRound p rate.eta.val q registers.priorClock
            registers.clockPending = .ok started ∧
          started.ledgerCommand = some (.initializeAt q)) := by
  have hmem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h k z).mp hk
  obtain ⟨q, hstart, hdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z ∧ _ at hstart
  refine ⟨q, hdate, ?_⟩
  rcases hstart with hfirst | hlive
  · left
    exact (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
      rate rewards C_star C_h q z).mp hfirst
  · right
    obtain ⟨record, registers, owned, base, started, hrecord, hstate, hcall, hcommand⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
        rate rewards C_star C_h q z).mp hlive
    exact ⟨record, registers, owned, base, started,
      hrecord, hstate, hcall, hcommand⟩

/-- A genuine later-choice installation finishes an existing transfer. Its
actual collection-state record is not another ranked transfer start. -/
public theorem actual_laterChosen_installation_is_not_transfer_start
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin p.T) (z : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h q z = some record)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true) :
    ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z := by
  obtain ⟨payload, ledger, saved, hstate, _hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty record.input hlater
  exact ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt_false_of_collection
    rate rewards C_star C_h q z record hrecord payload ledger saved hstate

/-- The complete suffix retains the exact original one-based source date at
each finite index. -/
public theorem completeSuffixRecord_source_date
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.time.val + 1 =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          i.val + 1 := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hindex : i.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h]
    exact i.isLt
  have hget := congrArg
    (fun dates : List ℕ => dates[i.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hindex,
    Nat.one_mul] at hget
  have htime := Option.some.inj hget
  omega

/-- An actual source-record lookup at or after launch is the same indexed
record in the accepted complete physical suffix. This provides the date
transport used to place actual start commands inside their ranked windows. -/
public theorem actualRecordAt_suffix_index
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin p.T) (z : SourceInput p)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ q.val)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h q z = some record) :
    ∃ i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i.val =
        q.val ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val] = record := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlookup : R[q.val - s]? = some record := by
    change (if s ≤ q.val then R[q.val - s]? else none) = some record at hrecord
    rw [ite_eq_left hstart] at hrecord
    exact hrecord
  cases hopt : R[q.val - s]? with
  | none => rw [hopt] at hlookup; cases hlookup
  | some actual =>
      have hbound := (List.getElem?_eq_some_iff.mp hopt).1
      have hget := (List.getElem?_eq_some_iff.mp hopt).2
      have hactual : actual = record := Option.some.inj (hopt.symm.trans hlookup)
      let i : Fin R.length := ⟨q.val - s, hbound⟩
      refine ⟨i, ?_, ?_⟩
      · dsimp only [i, s]
        omega
      · change R[q.val - s]'hbound = record
        exact hget.trans hactual

/-- Each present ranked start is located at its exact index in the same
complete suffix. The returned record is the actual original FIRST record or
the actual live record carrying its `StartRound.initializeAt` command. -/
public theorem present_start_actual_suffix_record
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ∃ (q : Fin p.T)
      (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      q.val + 1 = ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i.val =
        q.val ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val] = record ∧
      (record.input.state.coordinator = .first ∨
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ)
          (started : CoordinatorPhaseClock.StartRoundResult p),
          record.input.state.coordinator = .live registers owned base ∧
          CoordinatorPhaseClock.startRound p rate.eta.val q registers.priorClock
            registers.clockPending = .ok started ∧
          started.ledgerCommand = some (.initializeAt q)) := by
  obtain ⟨q, hdate, hbranch⟩ := present_start_actual_first_or_live_initializeAt
    rate rewards C_star C_h k z hk
  rcases hbranch with hfirst | hlive
  · obtain ⟨record, hrecord, hstate⟩ := hfirst
    have hmarker :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h q z).mpr ⟨record, hrecord, hstate⟩
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val := by
      unfold ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt at hmarker
      omega
    obtain ⟨i, hindex, hsame⟩ := actualRecordAt_suffix_index
      rate rewards C_star C_h q z hstart record hrecord
    exact ⟨q, i, record, hdate, hindex, hsame, Or.inl hstate⟩
  · obtain ⟨record, registers, owned, base, started, hrecord, hstate, hcall, hcommand⟩ := hlive
    have hliveStart :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
        rate rewards C_star C_h q z).mpr
        ⟨record, registers, owned, base, started, hrecord, hstate, hcall, hcommand⟩
    have hstart := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_after_physicalStart
      rate rewards C_star C_h q z hliveStart
    obtain ⟨i, hindex, hsame⟩ := actualRecordAt_suffix_index
      rate rewards C_star C_h q z hstart record hrecord
    exact ⟨q, i, record, hdate, hindex, hsame,
      Or.inr ⟨registers, owned, base, started, hstate, hcall, hcommand⟩⟩

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

private theorem collectionPostChoice_success_frame
    {rate : RateInput p} {x : RoundInput p rate}
    (prepared : PreparedRound x) (c : Choice rate)
    (hfailure : (collectionPostChoice prepared c.payload c.preLedger
      c.started c.weights).failure = none) :
    ∃ ledger saved, (collectionPostChoice prepared c.payload c.preLedger
      c.started c.weights).configuration = .collection c.payload ledger saved := by
  unfold collectionPostChoice at hfailure ⊢
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared c.payload c.started c.weights) with
  | none => simp only [hrecord, coordinatorFailure, reduceCtorEq] at hfailure
  | some recording =>
      simp only [hrecord] at hfailure ⊢
      cases hstart : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hstart, coordinatorFailure, reduceCtorEq] at hfailure
      | rejected bad => simp only [hstart, coordinatorFailure, reduceCtorEq] at hfailure
      | success started =>
          simp only [hstart] at hfailure ⊢
          unfold collectionFinish at hfailure ⊢
          cases hreceive : (receiveUp prepared started).result with
          | invalid => simp only [hreceive, coordinatorFailure, reduceCtorEq] at hfailure
          | success pair | rejected pair =>
              obtain ⟨decoded, bank⟩ := pair
              simp only [hreceive] at hfailure ⊢
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp only [hfinish, coordinatorFailure, reduceCtorEq] at hfailure
              | rejected bad => simp only [hfinish, coordinatorFailure, reduceCtorEq] at hfailure
              | success finished =>
                  simp only [hfinish] at hfailure ⊢
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason =>
                      simp only [hclock, coordinatorFailure, reduceCtorEq] at hfailure
                  | ok clockFinished => exact ⟨_, _, rfl⟩

/-- Every collection choice on the original complete run executes its actual
recorder, receiver and FINISH, retaining the old payload even when the last
UP reply is accepted. FINISH itself never installs the next assignment. -/
public theorem actual_collection_choice_completed
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (c : Choice rate)
    (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input = some c) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val]
    (∃ ledger saved, r.output.next.coordinator = .collection c.payload ledger saved) ∧
      (extractRound r).isSome = true := by
  intro r
  have hfailure := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z i).1
  have htail : r.output.coordinator = collectionPostChoice (prepare r.input)
      c.payload c.preLedger c.started c.weights := by
    rw [r.output_eq]
    exact choice_tail r.input c hc
  rw [htail] at hfailure
  obtain ⟨ledger, saved, hconfiguration⟩ :=
    collectionPostChoice_success_frame (prepare r.input) c hfailure
  have hnext : r.output.next.coordinator = .collection c.payload ledger saved := by
    have hout : r.output.next.coordinator = r.output.coordinator.configuration := by
      rw [r.output_eq]
      rfl
    rw [hout, htail]
    exact hconfiguration
  obtain ⟨done, hdone⟩ := actual_collection_round_complete r c c.payload ledger saved hc hnext
  exact ⟨⟨ledger, saved, hnext⟩, by rw [hdone]; rfl⟩

private theorem actual_live_initializeAt_cutoff
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.state.coordinator =
        .live registers owned base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time
      registers.priorClock registers.clockPending = .ok started)
    (hcommand : started.ledgerCommand = some (.initializeAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time)) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val]
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
      ∃ c : Choice rate, choice r.input = some c ∧ c.payload = registers.payload ∧
        c.initializer = some (cutoffInitializer
          (liveRegistersAt registers r.input.time)
          (liveOwnedAt registers owned r.input.time) base r.input.time) := by
  intro r
  obtain ⟨hprepared, hbranch⟩ :=
    ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
      rate rewards C_star C_h z i registers owned base hstate
  change (prepare r.input).coordinator = _ at hprepared
  cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) with
  | continuingChosen dispatched hs continuation selection =>
      rw [hd] at hbranch
      have hsame : dispatched.startResult = started :=
        Except.ok.inj (hs.symm.trans hstart)
      have hshape := CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
        (liveRegistersAt registers r.input.time) started hstart hcommand
      have hu := hbranch.2.1
      rw [hsame, hshape.1] at hu
      cases hu
  | cutoffChosen dispatched hs ledger hinit hledger hdomain hclock hpending hnone selected =>
      rw [hd] at hprepared
      refine ⟨by simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hprepared], ?_⟩
      let c : Choice rate := ⟨registers.payload, sharedLedger ledger,
        dispatched.startResult, (liveRegistersAt registers r.input.time).complementWeights,
        some (cutoffInitializer (liveRegistersAt registers r.input.time)
          (liveOwnedAt registers owned r.input.time) base r.input.time)⟩
      refine ⟨c, ?_, rfl, rfl⟩
      simp only [choice, hprepared, DispatchCut.selection, selectionAt, dite_true,
        reduceCtorEq, ite_false, choiceOfCut]
      rfl
  | clockFailure => rw [hd] at hbranch; exact False.elim hbranch
  | initializerFailure => rw [hd] at hbranch; exact False.elim hbranch
  | localFailure => rw [hd] at hbranch; exact False.elim hbranch

/-- A genuine original live transfer start extracts a nonempty segment at
that same physical index. Its initializer and complete old payload are the
actual cutoff's, and every retained round has a successful collection choice.
The remaining suffix retains the actual first excluded record. -/
public theorem actual_initializeAt_collection_segment
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.state.coordinator =
        .live registers owned base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time
      registers.priorClock registers.clockPending = .ok started)
    (hcommand : started.ledgerCommand = some (.initializeAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[i.val].input.time)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ seg : Segment rate,
      segmentAt R i.val = some seg ∧ seg.entry = R[i.val] ∧ seg.records ≠ [] ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.context.payload = registers.payload ∧
      seg.context.initializer = some (cutoffInitializer
        (liveRegistersAt registers R[i.val].input.time)
        (liveOwnedAt registers owned R[i.val].input.time) base R[i.val].input.time) ∧
      seg.records ++ seg.remaining = R.drop i.val ∧
      (∀ r ∈ seg.records, (extractRound r).isSome = true) := by
  intro R
  obtain ⟨hcut, c, hc, hpayload, hinitializer⟩ := actual_live_initializeAt_cutoff
    rate rewards C_star C_h z i registers owned base started hstate hstart hcommand
  have hdone := (actual_collection_choice_completed
    rate rewards C_star C_h z i c hc).2
  let seg : Segment rate := ⟨R[i.val], c,
    R[i.val] :: (R.drop (i.val + 1)).takeWhile continuing,
    (R.drop (i.val + 1)).dropWhile continuing⟩
  have hsegment : ReferenceCollectionSegmentExtraction.segment (R.drop i.val) = some seg := by
    rw [List.drop_eq_getElem_cons i.isLt]
    simp only [ReferenceCollectionSegmentExtraction.segment, hc, Option.map_some, hdone, ite_true]
    rfl
  have hat : segmentAt R i.val = some seg := by
    simp only [segmentAt, hsegment, Option.bind_some, seg, hinitializer,
      Option.isSome_some, or_true, ite_true]
  exact ⟨seg, hat, rfl, List.cons_ne_nil _ _, hcut, hpayload, hinitializer,
    segmentAt_partition R i.val seg hat, segment_all_completed _ seg hsegment⟩

private theorem actual_collection_input_choice_or_installation
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.state.coordinator =
        .collection payload ledger saved) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val]
    (∃ c : Choice rate, choice r.input = some c) ∨
      ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
  intro r
  change r.input.state.coordinator = .collection payload ledger saved at hstate
  have hfailure := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z i).1
  have hf : (prepare r.input).observeCoordinator.failure = none := by
    rw [r.output_eq] at hfailure
    exact hfailure
  have hd : (prepare r.input).coordinator = dispatch r.input := rfl
  simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch] at hd
  split at hd
  next hvalid =>
    cases ho : CoordinatorRoundDispatch.dispatchCollection
        (collectionInput r.input payload ledger
          (collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
          ⟨ledger.cutoff - 1, by omega⟩) with
    | continuing core snapshot boundary scores =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        left
        simp only [choice, hd, DispatchCut.selection, reduceCtorEq, ite_false, choiceOfCut]
        exact ⟨_, rfl⟩
    | laterChosen core consistent started hstart instruction hi output hlocal clockData installed selected =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        right
        simp only [ReferenceCollectionPhaseHistory.laterChosen, hd]
    | clockFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | localFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | coreFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | laterReconstructionFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | laterPrefixFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | laterOrientationFailure =>
        rw [ho] at hd
        change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          dite_true, coordinatorFailure, reduceCtorEq] at hf
    | laterChoiceFailure =>
      rw [ho] at hd
      change (prepare r.input).coordinator = .collection payload ledger _ _ _ at hd
      simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
        dite_true, coordinatorFailure, reduceCtorEq] at hf
  next hvalid =>
    simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
      dite_true, coordinatorFailure, reduceCtorEq] at hf



private theorem segment_remaining_not_continuing
    {rate : RateInput p} (R : List (RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hat : segmentAt R e = some seg)
    (hne : seg.records ≠ []) (r : RoundRecord (p := p) (rate := rate))
    (hr : seg.remaining.head? = some r) : continuing r = false := by
  have hsegment := (segmentAt_branch R e seg hat).1
  cases hdrop : R.drop e with
  | nil => simp only [hdrop, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hsegment
  | cons entry rest =>
      simp only [hdrop, ReferenceCollectionSegmentExtraction.segment] at hsegment
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at hsegment
      | some c =>
          simp only [hc, Option.map_some] at hsegment
          split at hsegment
          next hgood =>
            cases Option.some.inj hsegment
            change (rest.dropWhile continuing).head? = some r at hr
            have hlength : 0 < (rest.dropWhile continuing).length := by
              exact List.length_pos_iff.mpr (by intro hnil; simp only [hnil, List.head?_nil,
                reduceCtorEq] at hr)
            have hnot := List.dropWhile_get_zero_not continuing rest hlength
            have hhead : (rest.dropWhile continuing)[0]'hlength = r := by
              exact (List.getElem?_eq_some_iff.mp
                (by simpa only [List.head?_eq_getElem?] using hr)).2
            rw [List.get_eq_getElem, hhead] at hnot
            exact Bool.eq_false_iff.mpr hnot
          next hbad =>
            cases Option.some.inj hsegment
            exact False.elim (hne rfl)

/-- An actual cutoff segment can end only at the physical horizon or at
the next actual later-choice installation. This rules out a spurious end at
a grid boundary, at the last UP acceptance, or at a collection FINISH. The
terminal alternative requires no future installation witness. -/
public theorem actual_collection_segment_horizon_or_installation
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let v := e + seg.records.length
    v ≤ R.length ∧
      (v = R.length ∨ ∃ hv : v < R.length,
        R.drop v = seg.remaining ∧
        ReferenceCollectionPhaseHistory.laterChosen R[v].input = true ∧
        seg.exit = .laterChosen R[v] ∧
        R[v].input.state = endpointState seg.entry.input.state seg.records ∧
        ∃ saved, R[v].input.state.coordinator =
          .collection seg.context.payload seg.final saved ∧ seg.final.pending = ∅) := by
  intro R v
  obtain ⟨hle, _hfields, _hpayload, saved, hend, _hcursor, during, _hrecords,
    _hprefix, _hnotlater, _hduring, _hpending, _hnodup, _hwitnesses, hboundary⟩ :=
    ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
      rate rewards C_star C_h z e seg hat hne hcut
  refine ⟨hle, ?_⟩
  rcases hboundary with hhorizon | ⟨hv, hstate, hcoord, _htime, hdrop, hbranch⟩
  · exact Or.inl hhorizon
  · right
    have hlater : ReferenceCollectionPhaseHistory.laterChosen R[v].input = true := by
      rcases actual_collection_input_choice_or_installation
          rate rewards C_star C_h z ⟨v, hv⟩ seg.context.payload seg.final saved hcoord with
        ⟨c, hc⟩ | hlater
      · have hdone := (actual_collection_choice_completed
          rate rewards C_star C_h z ⟨v, hv⟩ c hc).2
        obtain ⟨done, hextract⟩ := Option.isSome_iff_exists.mp hdone
        change extractRound R[v] = some done at hextract
        have hchoice := (actual_collection_round_checked R[v] done hextract).1
        have hinitializer := (choice_collection_pre R[v].input
          seg.context.payload seg.final saved done.context hcoord hchoice).2
        have hcontinue : continuing R[v] = true := by
          simp only [continuing, hextract, hinitializer, Option.isNone_none]
        have hhead : seg.remaining.head? = some R[v] := by
          rw [← hdrop, List.drop_eq_getElem_cons hv]
          rfl
        have hfalse := segment_remaining_not_continuing R e seg hat hne R[v] hhead
        rw [hcontinue] at hfalse
        cases hfalse
      · exact hlater
    have hempty : seg.final.pending = ∅ := by
      rcases hbranch with hfalse | ⟨_hlater, hempty, _hup⟩
      · rw [hlater] at hfalse
        cases hfalse
      · exact hempty
    refine ⟨hv, hdrop, hlater, ?_, hstate, saved, hcoord, hempty⟩
    change exitOf seg.remaining = _
    rw [← hdrop, List.drop_eq_getElem_cons hv]
    simp only [exitOf]
    unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
    cases hd : (prepare R[v].input).coordinator with
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, Bool.false_eq_true] at hlater
        rfl
    | first outcome => simp only [hd, Bool.false_eq_true] at hlater
    | live registers owned base outcome => simp only [hd, Bool.false_eq_true] at hlater
    | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hlater
    | dagger => simp only [hd, Bool.false_eq_true] at hlater

private theorem actual_first_record_index_zero
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (i : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hfirst : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[i.val].input.state.coordinator = .first) :
    i.val = 0 := by
  by_contra hnonzero
  have hprev : i.val - 1 + 1 = i.val := by omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (i.val - 1) (by rw [hprev]; exact i.isLt)
  have hphase := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨i.val - 1, by omega⟩
  have hnotfirst := hphase.2.2.2.1
  apply hnotfirst
  have hcoord := congrArg State.coordinator hadj
  simpa only [hprev, hfirst] using hcoord.symm

/-- Every date of an actual extracted cutoff segment is a collection choice
with the same old payload. These are consecutive original physical dates,
including frozen rounds, and the actual end is the horizon or an installation. -/
public theorem actual_collection_segment_calendar
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∀ j : Fin seg.records.length,
      R[e + j.val]? = some seg.records[j.val] ∧
      seg.records[j.val].input.time.val + 1 = s + e + j.val + 1 ∧
      ∃ c : Choice rate, choice seg.records[j.val].input = some c ∧
        c.payload = seg.context.payload := by
  intro R s j
  obtain ⟨_hle, _hfields, hpayload, _rest⟩ :=
    ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
      rate rewards C_star C_h z e seg hat hne hcut
  have hslot := ReferenceCompleteLaterCollectionCalendarWord.actual_later_segment_slot_record
    rate rewards C_star C_h z e seg hat j
  obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hslot
  have hdate := completeSuffixRecord_source_date
    rate rewards C_star C_h z ⟨e + j.val, hbound⟩
  change R[e + j.val].input.time.val + 1 = s + (e + j.val) + 1 at hdate
  rw [hget] at hdate
  obtain ⟨done, hdone⟩ := Option.isSome_iff_exists.mp
    (segment_all_completed _ seg (segmentAt_branch R e seg hat).1
      seg.records[j.val] (List.getElem_mem j.isLt))
  have hc := (actual_collection_round_checked seg.records[j.val] done hdone).1
  exact ⟨hslot, by omega, done.context, hc,
    hpayload _ (List.getElem_mem j.isLt) done.context hc⟩

private theorem birth_continuing_index
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    ∀ j : Fin V.length, ∃ hj : b.val + j.val < R.length,
      V[j.val] = R[b.val + j.val] := by
  intro R W V j
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact ⟨by simpa only [Nat.add_zero] using b.isLt, rfl⟩
  | succ j =>
      have hjW : j < W.length := by
        simp only [V, List.length_cons] at hj
        omega
      have hp : W <+: R.drop (b.val + 1) := List.takeWhile_prefix _
      have hbound := hp.length_le
      simp only [List.length_drop] at hbound
      have hindex : b.val + (j + 1) < R.length := by omega
      refine ⟨hindex, ?_⟩
      have hget := hp.getElem hjW
      rw [List.getElem_drop] at hget
      simpa only [V, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hget

private theorem missing_test_rank_iff
    {rate : RateInput p} (V : List (RoundRecord (p := p) (rate := rate)))
    (hfalse : ∀ r ∈ V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false)
    (j : Fin V.length) :
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice V[j.val] = true ↔
      j.val < (V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length := by
  let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  have hpartition : H ++ Rel = V := List.takeWhile_append_dropWhile
  by_cases hj : j.val < H.length
  · have hprefix : H <+: V := List.takeWhile_prefix _
    have hmember : V[j.val] ∈ H := by
      rw [← hprefix.getElem hj]
      exact List.getElem_mem hj
    exact ⟨fun _ => hj, fun _ => List.mem_takeWhile_imp hmember⟩
  · have hbound : j.val - H.length < Rel.length := by
      have hlength := congrArg List.length hpartition
      simp only [List.length_append] at hlength
      omega
    have hget : V[j.val] = Rel[j.val - H.length] := by
      have h := List.getElem_append_right' H (i := j.val - H.length) hbound
      have hsum : j.val - H.length + H.length = j.val := by omega
      simpa only [hpartition, hsum] using h.symm
    have hf := hfalse V[j.val] (hget ▸ List.getElem_mem hbound)
    rw [hf]
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (hj h)⟩

/-- On the actual installation and its same-source continuing LIVE prefix,
the missing-DOWN field has a genuine calendar interval. The endpoint is the
finite first-empty search justified by the accepted no-resurrection theorem.
No follower release-status or pending-UP set is substituted for this field. -/
public theorem actual_later_installation_missing_date_iff
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let h := (V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
    ∃ payload : Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      (∀ j : Fin V.length,
        R[b.val + j.val]? = some V[j.val] ∧
        V[j.val].input.time.val + 1 = s + b.val + j.val + 1 ∧
        ∃ selected : Selection V[j.val].input,
          V[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (selected.view.pendingAtChoice.Nonempty ↔
            V[j.val].input.time.val + 1 < s + b.val + h + 1) ∧
          (selected.view.pendingAtChoice = ∅ ↔
            s + b.val + h + 1 ≤ V[j.val].input.time.val + 1)) ∧
      (∀ j : Fin V.length,
        ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] →
        V[j.val].input.time.val + 1 + 1 = s + b.val + h + 1) := by
  intro R s W V h
  have hhistory := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hhistory
  obtain ⟨rb, qb, beta, birthSelected, _hnext, hbirth, _hlater,
    hbirthSelection, hbirthPayload, _hbirthPending, _hrbPending, _hnoEvent,
    _hfollowers, _htail, _hnoRelease, hframes⟩ := hhistory
  have hfalse := ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_suffix_test_false
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hfalse
  change ∀ r ∈ V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false at hfalse
  have hboundary := ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_boundary
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hboundary
  have hcalendar : ∀ j : Fin V.length,
      R[b.val + j.val]? = some V[j.val] ∧
      V[j.val].input.time.val + 1 = s + b.val + j.val + 1 := by
    intro j
    obtain ⟨hj, hget⟩ := birth_continuing_index rate rewards C_star C_h z b j
    have htime := completeSuffixRecord_source_date
      rate rewards C_star C_h z ⟨b.val + j.val, hj⟩
    change R[b.val + j.val].input.time.val + 1 = s + (b.val + j.val) + 1 at htime
    rw [← hget] at htime
    change V[j.val].input.time.val + 1 = s + (b.val + j.val) + 1 at htime
    exact ⟨by rw [List.getElem?_eq_getElem hj, ← hget], by omega⟩
  have hselection : ∀ j : Fin V.length, ∃ selected : Selection V[j.val].input,
      V[j.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = rb.payload := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact ⟨birthSelected, hbirthSelection, hbirthPayload⟩
    | succ j =>
        have hjW : j < W.length := by
          simp only [V, List.length_cons] at hj
          omega
        obtain ⟨r, q, selected, next, owned, states, memories, _hin, _hp, hs,
          hselectedPayload, _hrest⟩ := hframes ⟨j, hjW⟩
        exact ⟨selected, hs, hselectedPayload⟩
  refine ⟨rb.payload, hbirth, ?_, ?_⟩
  · intro j
    obtain ⟨selected, hs, hp⟩ := hselection j
    have hm := missing_test_rank_iff V hfalse j
    simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hs,
      decide_eq_true_eq] at hm
    have htime := (hcalendar j).2
    refine ⟨(hcalendar j).1, htime, selected, hs, hp, ?_, ?_⟩
    · constructor
      · intro hn
        have := hm.mp hn
        omega
      · intro hd
        exact hm.mpr (by omega)
    · rw [← Finset.not_nonempty_iff_eq_empty, hm]
      omega
  · intro j hclear
    have hindex := hboundary.1 j hclear
    change j.val + 1 = h at hindex
    have htime := (hcalendar j).2
    omega

private theorem actual_missing_eq_selected
    {rate : RateInput p} (r : RoundRecord (p := p) (rate := rate))
    (selected : Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r =
      selected.view.pendingAtChoice := by
  simp only [ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection, hs]
  rfl

/-- Missing DOWN confirmations are nested on the actual later installation
and its continuing prefix. The proof uses the original adjacent physical
states and the actual confirmation erasure equations, rather than a search
or an assumed phase partition. -/
public theorem actual_later_installation_missing_nested
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    ∀ j k : Fin V.length, j.val ≤ k.val →
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[k.val] ⊆
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[j.val] := by
  intro R W V
  have hhistory := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hhistory
  obtain ⟨rb, qb, beta, birthSelected, _hnext, _hbirth, _hlater,
    hbirthSelection, _hbirthPayload, hbirthPending, _hrbPending, _hnoEvent,
    _hfollowers, _htail, _hnoRelease, hframes⟩ := hhistory
  have hstep : ∀ n (hn : n + 1 < V.length),
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (V[n + 1]'hn) ⊆
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate (V[n]'(by omega)) := by
    intro n hn
    cases n with
    | zero =>
        have hmissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[0] =
            Finset.univ :=
          (actual_missing_eq_selected R[b.val] birthSelected hbirthSelection).trans hbirthPending
        rw [hmissing]
        exact Finset.subset_univ _
    | succ n =>
        have hnV : n + 1 + 1 < V.length := hn
        have hnW : n < W.length := by simp only [V, List.length_cons] at hn; omega
        have hnW' : n + 1 < W.length := by simp only [V, List.length_cons] at hn; omega
        obtain ⟨r, q, selected, next, owned, states, memories, _hin, _hp, hs, _hsp,
          hm, hout, _hop, hu, _hrest⟩ := hframes ⟨n, hnW⟩
        obtain ⟨r', q', selected', next', owned', states', memories', hin', _hp', hs',
          _hsp', hm', _hrest'⟩ := hframes ⟨n + 1, hnW'⟩
        obtain ⟨hindex, hget⟩ := birth_continuing_index rate rewards C_star C_h z b
          ⟨n + 1, by change n + 1 < V.length; omega⟩
        obtain ⟨hindex', hget'⟩ := birth_continuing_index rate rewards C_star C_h z b
          ⟨n + 1 + 1, hn⟩
        have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z (b.val + (n + 1)) (by omega)
        have hstate : (W[n + 1]'hnW').input.state = (W[n]'hnW).output.next := by
          change V[n + 1 + 1].input.state = V[n + 1].output.next
          rw [hget, hget']
          simpa only [Nat.add_assoc] using hadj
        have hcoord := congrArg State.coordinator hstate
        rw [hin', hout] at hcoord
        have hr : r' = next := (CoordinatorConfiguration.live.inj hcoord).1
        have hcur := actual_missing_eq_selected W[n] selected hs
        have hnext := actual_missing_eq_selected W[n + 1] selected' hs'
        change ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate W[n + 1] ⊆
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate W[n]
        rw [hcur, hnext, hm', hr, hu]
        split
        · exact Finset.erase_subset _ _
        · exact Finset.Subset.refl _
  intro j k hjk
  have hiterate : ∀ d (hd : j.val + d < V.length),
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[j.val + d] ⊆
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[j.val] := by
    intro d
    induction d with
    | zero => intro hd; exact Finset.Subset.refl _
    | succ d ih =>
        intro hd
        have hprevious : j.val + d < V.length := by omega
        exact (hstep (j.val + d) (by omega)).trans (ih hprevious)
  have hsum : j.val + (k.val - j.val) = k.val := by omega
  simpa only [hsum] using hiterate (k.val - j.val) (by omega)

/-- The same later installation's LIVE prefix ends exactly at the horizon
or at an actual next cutoff. Installation itself stays in this prefix; it
does not enumerate another transfer start. -/
public theorem actual_later_installation_live_end
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let v := b.val + 1 + W.length
    v = R.length ∨ ∃ e : Fin R.length, e.val = v ∧
      ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true := by
  intro R W v
  have hhistory := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hhistory
  obtain ⟨rb, qb, beta, _birthSelected, _hnext, _hbirth, hlater,
    _hbirthSelection, _hbirthPayload, _hbirthPending, _hrbPending, _hnoEvent,
    _hfollowers, htail, _hnoRelease, _hframes⟩ := hhistory
  rcases htail with hterminal | ⟨k, hk, hin, _hframes⟩
  · left
    have hW : W = [] := by
      simp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
        hterminal, List.drop_length, List.takeWhile_nil]
    simp only [v, hW, List.length_nil, Nat.add_zero, hterminal]
    rfl
  · have hmax := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_maximal
      rewards C_star C_h z k rb qb beta hin hlater
    have hlength : (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val).length = W.length := by rw [hk]
    rcases hmax with hend | ⟨he, r, q, _hpayload, _hstate, chosen, hprepared, htag⟩
    · left
      change k.val + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z k.val).length = R.length at hend
      dsimp only [v]
      omega
    · right
      let e : Fin R.length := ⟨k.val +
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z k.val).length, he⟩
      refine ⟨e, by dsimp only [e, v]; omega, ?_⟩
      have hactual : R[e.val].output.preparation = prepare R[e.val].input := by
        rw [R[e.val].output_eq]
        rfl
      change R[e.val].output.preparation.coordinator = .live r q beta chosen at hprepared
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [← hactual, hprepared]
      cases chosen <;> cases htag
      rfl

private theorem complete_record_actual_lookup
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h R[j.val].input.time z = some R[j.val] := by
  intro R
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have ht := completeSuffixRecord_source_date rate rewards C_star C_h z j
  change R[j.val].input.time.val + 1 = s + j.val + 1 at ht
  have htime : R[j.val].input.time.val = s + j.val := by omega
  change (if s ≤ R[j.val].input.time.val then R[R[j.val].input.time.val - s]?
    else none) = some R[j.val]
  rw [htime, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem j.isLt

/-- The actual later installation is already a live-assignment choice,
so it is excluded from the collection portion ending immediately before it. -/
public theorem actual_laterChosen_not_collection_choice
    {rate : RateInput p} (r : RoundRecord (p := p) (rate := rate))
    (hb : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    choice r.input = none := by
  unfold choice
  split
  · rfl
  · unfold ReferenceCollectionPhaseHistory.laterChosen at hb
    cases hd : (prepare r.input).coordinator with
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, Bool.false_eq_true] at hb
        simp only [choiceOfCut]
    | first outcome => simp only [hd, Bool.false_eq_true] at hb
    | live registers owned base outcome => simp only [hd, Bool.false_eq_true] at hb
    | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hb
    | dagger => simp only [hd, Bool.false_eq_true] at hb

/-- On the original collection interval through its first excluded date,
actual collection choice is equivalent to being strictly before the physical
installation/horizon endpoint. In particular the installation date is not C. -/
public theorem actual_collection_segment_choice_iff
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ j : Fin R.length, e ≤ j.val → j.val ≤ e + seg.records.length →
      ((choice R[j.val].input).isSome = true ↔ j.val < e + seg.records.length) := by
  intro R j hleft hright
  by_cases hj : j.val < e + seg.records.length
  · have hlocal : j.val - e < seg.records.length := by omega
    obtain ⟨hslot, _hdate, c, hc, _hp⟩ := actual_collection_segment_calendar
      rate rewards C_star C_h z e seg hat hne hcut ⟨j.val - e, hlocal⟩
    have hindex : e + (j.val - e) = j.val := by omega
    have hget := (List.getElem?_eq_some_iff.mp hslot).2
    have hrecord : R[j.val] = seg.records[j.val - e] := by
      simpa only [hindex] using hget
    rw [hrecord, hc]
    exact ⟨fun _ => hj, fun _ => rfl⟩
  · have hindex : j.val = e + seg.records.length := by omega
    obtain ⟨_hle, hboundary⟩ := actual_collection_segment_horizon_or_installation
      rate rewards C_star C_h z e seg hat hne hcut
    rcases hboundary with hterminal | ⟨hv, _hdrop, hlater, _hexit, _hstate, _hrest⟩
    · change e + seg.records.length = R.length at hterminal
      have := j.isLt
      omega
    · have hlater' : ReferenceCollectionPhaseHistory.laterChosen R[j.val].input = true := by
        simpa only [hindex] using hlater
      rw [actual_laterChosen_not_collection_choice R[j.val] hlater']
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (hj h)⟩

/-- No date after entry inside this actual collection segment is another
transfer start. This includes any grid boundary and the final accepted UP
round: the adjacent predecessor's FINISH still leaves a collection state. -/
public theorem actual_collection_segment_no_internal_transfer_start
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (j : Fin seg.records.length) (hj : 0 < j.val) :
    ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h seg.records[j.val].input.time z := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let prev : Fin seg.records.length := ⟨j.val - 1, by omega⟩
  have hslot := ReferenceCompleteLaterCollectionCalendarWord.actual_later_segment_slot_record
    rate rewards C_star C_h z e seg hat j
  have hslotPrev := ReferenceCompleteLaterCollectionCalendarWord.actual_later_segment_slot_record
    rate rewards C_star C_h z e seg hat prev
  obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hslot
  obtain ⟨hboundPrev, hgetPrev⟩ := List.getElem?_eq_some_iff.mp hslotPrev
  have hgood := segment_all_completed _ seg (segmentAt_branch R e seg hat).1
    seg.records[prev.val] (List.getElem_mem prev.isLt)
  obtain ⟨done, hdone⟩ := Option.isSome_iff_exists.mp hgood
  obtain ⟨_hc, _hr, _hchecked, payload, saved, hout⟩ :=
    actual_collection_round_checked seg.records[prev.val] done hdone
  have hsum : e + prev.val + 1 = e + j.val := by dsimp only [prev]; omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (e + prev.val) (by omega)
  have hstate : seg.records[j.val].input.state = seg.records[prev.val].output.next := by
    have hcur : R[e + prev.val + 1] = seg.records[j.val] := by
      simpa only [hsum] using hget
    change R[e + prev.val + 1].input.state = R[e + prev.val].output.next at hadj
    rw [hcur, hgetPrev] at hadj
    exact hadj
  have hcoord : seg.records[j.val].input.state.coordinator =
      .collection payload done.final saved :=
    (congrArg State.coordinator hstate).trans hout
  have hlookup := complete_record_actual_lookup rate rewards C_star C_h z ⟨e + j.val, hbound⟩
  change ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
    rate rewards C_star C_h R[e + j.val].input.time z = some R[e + j.val] at hlookup
  rw [hget] at hlookup
  exact ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt_false_of_collection
    rate rewards C_star C_h seg.records[j.val].input.time z seg.records[j.val]
    hlookup payload done.final saved hcoord

private theorem continuing_live_not_collection_choice
    {rate : RateInput p} (r : RoundRecord (p := p) (rate := rate))
    (ht : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true) :
    choice r.input = none := by
  have hprepare : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at ht
  cases hd : r.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome <;> simp only [hd, Bool.false_eq_true] at ht
      unfold choice
      rw [← hprepare, hd]
      simp only [choiceOfCut, ite_self]
  | first outcome => simp only [hd, Bool.false_eq_true] at ht
  | collection payload ledger clock cutoff outcome => simp only [hd, Bool.false_eq_true] at ht
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at ht
  | dagger => simp only [hd, Bool.false_eq_true] at ht

/-- The installation date and every continuing LIVE choice after it are
outside C, on exactly the original records used by the missing-DOWN interval. -/
public theorem actual_later_installation_no_collection_choice
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    ∀ j : Fin (R[b.val] :: W).length, choice (R[b.val] :: W)[j.val].input = none := by
  intro R W j
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact actual_laterChosen_not_collection_choice R[b.val] hb
  | succ j =>
      have hjW : j < W.length := by simp only [List.length_cons] at hj; omega
      exact continuing_live_not_collection_choice W[j]
        (List.mem_takeWhile_imp (List.getElem_mem hjW))

/-- Each present original ranked start either is the genuine initial FIRST
installation, with no collection choice, or generates its actual maximal
collection segment on this same complete suffix. Its boundary is constructed
internally and can be terminal; no later-installation premise is supplied.
When installation occurs, the SAME boundary supplies the new-payload LIVE
interval, its next-cutoff/horizon endpoint, and its actual missing-DOWN fields. -/
public theorem present_start_original_collection_interval
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ i : Fin R.length,
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = s + i.val + 1 ∧
      ((i.val = 0 ∧ R[i.val].input.state.coordinator = .first ∧
          choice R[i.val].input = none) ∨
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ) (seg : Segment rate),
          R[i.val].input.state.coordinator = .live registers owned base ∧
          segmentAt R i.val = some seg ∧ seg.entry = R[i.val] ∧ seg.records ≠ [] ∧
          ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
          seg.context.payload = registers.payload ∧
          seg.context.initializer = some (cutoffInitializer
            (liveRegistersAt registers R[i.val].input.time)
            (liveOwnedAt registers owned R[i.val].input.time) base R[i.val].input.time) ∧
          seg.records ++ seg.remaining = R.drop i.val ∧
          (∀ j : Fin R.length, i.val ≤ j.val → j.val ≤ i.val + seg.records.length →
            ((choice R[j.val].input).isSome = true ↔ j.val < i.val + seg.records.length)) ∧
          (∀ j : Fin seg.records.length, 0 < j.val →
            ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
              rate rewards C_star C_h seg.records[j.val].input.time z) ∧
          (∀ j : Fin seg.records.length,
            R[i.val + j.val]? = some seg.records[j.val] ∧
            seg.records[j.val].input.time.val + 1 = s + i.val + j.val + 1 ∧
            ∃ c : Choice rate, choice seg.records[j.val].input = some c ∧
              c.payload = registers.payload) ∧
          (i.val + seg.records.length = R.length ∨
            ∃ b : Fin R.length, b.val = i.val + seg.records.length ∧
              ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
              seg.exit = .laterChosen R[b.val] ∧
              R.drop b.val = seg.remaining ∧
              ∃ saved, R[b.val].input.state.coordinator =
                .collection registers.payload seg.final saved ∧ seg.final.pending = ∅ ∧
              let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z (b.val + 1)
              let V := R[b.val] :: W
              let h := (V.takeWhile
                ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
              (b.val + V.length = R.length ∨ ∃ e : Fin R.length,
                e.val = b.val + V.length ∧
                ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true) ∧
              (∀ j : Fin V.length, choice V[j.val].input = none) ∧
              ∃ newPayload : Payload rate,
                ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] newPayload ∧
                (∀ j : Fin V.length,
                  R[b.val + j.val]? = some V[j.val] ∧
                  V[j.val].input.time.val + 1 = s + b.val + j.val + 1 ∧
                  ∃ selected : Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.payload = newPayload ∧
                    (selected.view.pendingAtChoice.Nonempty ↔
                      V[j.val].input.time.val + 1 < s + b.val + h + 1) ∧
                    (selected.view.pendingAtChoice = ∅ ↔
                      s + b.val + h + 1 ≤ V[j.val].input.time.val + 1)) ∧
                (∀ j : Fin V.length,
                  ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] →
                  V[j.val].input.time.val + 1 + 1 = s + b.val + h + 1) ∧
                (∀ j l : Fin V.length, j.val ≤ l.val →
                  ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[l.val] ⊆
                    ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate V[j.val]))) := by
  intro R s
  obtain ⟨q, i, record, hdate, hindex, hsame, hbranch⟩ :=
    present_start_actual_suffix_record rate rewards C_star C_h k z hk
  have htime := completeSuffixRecord_source_date rate rewards C_star C_h z i
  have hdate' : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z = s + i.val + 1 := by omega
  have hq : R[i.val].input.time = q := by
    apply Fin.ext
    change (R[i.val]).input.time.val + 1 = s + i.val + 1 at htime
    omega
  change R[i.val] = record at hsame
  subst record
  refine ⟨i, hdate', ?_⟩
  rcases hbranch with hfirst | ⟨registers, owned, base, started, hstate, hstart, hcommand⟩
  · exact Or.inl ⟨actual_first_record_index_zero rate rewards C_star C_h z i hfirst,
      hfirst, choice_first_none R[i.val].input hfirst⟩
  · right
    rw [← hq] at hstart hcommand
    obtain ⟨seg, hat, hentry, hne, hcut, hpayload, hinitializer, hpartition, _hgood⟩ :=
      actual_initializeAt_collection_segment rate rewards C_star C_h z i registers
        owned base started hstate hstart hcommand
    have hcalendar := actual_collection_segment_calendar
      rate rewards C_star C_h z i.val seg hat hne hcut
    obtain ⟨_hle, hboundary⟩ := actual_collection_segment_horizon_or_installation
      rate rewards C_star C_h z i.val seg hat hne hcut
    refine ⟨registers, owned, base, seg, hstate, hat, hentry, hne, hcut, hpayload,
      hinitializer, hpartition,
      actual_collection_segment_choice_iff rate rewards C_star C_h z i.val seg hat hne hcut,
      actual_collection_segment_no_internal_transfer_start
        rate rewards C_star C_h z i.val seg hat, ?_, ?_⟩
    · simpa only [hpayload] using hcalendar
    · rcases hboundary with hterminal | ⟨hb, hdrop, hlater, hexit, _hstate, saved, hcoord, hempty⟩
      · exact Or.inl hterminal
      · let b : Fin R.length := ⟨i.val + seg.records.length, hb⟩
        have hmissing := actual_later_installation_missing_date_iff
          rate rewards C_star C_h z b hlater
        have hnested := actual_later_installation_missing_nested
          rate rewards C_star C_h z b hlater
        have hend := actual_later_installation_live_end
          rate rewards C_star C_h z b hlater
        obtain ⟨newPayload, hbirth, hfields, hclear⟩ := hmissing
        refine Or.inr ⟨b, rfl, hlater, hexit, hdrop, saved,
          by simpa only [hpayload] using hcoord, hempty, ?_,
          actual_later_installation_no_collection_choice rate rewards C_star C_h z b hlater,
          newPayload, hbirth, hfields, hclear, hnested⟩
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend

end Bandits.Support.ReferenceOriginalTransferPhysicalIntervals

end
