/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarPhysicalTransferCount
public import Bandits.Support.ReferenceOriginalFirstBadStrictPrefix

import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Inclusive stopped physical transfer starts

For each original round, retain the actual physical transfer start exactly
when it is no later than the inclusive first decoder-failure or overflow
date. The ranked dates use one-based manuscript dates; Lean position `k.val`
is zero-based, and the absent value is the sentinel `T + 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
  (sourcePrefix sourcePrefixFiltration actualRecord)
open Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw
  (actualRecordAt actualObserver)
open Bandits.Support.ReferenceOriginalCalendarPhysicalTransferCount
  (actualPhysicalTransferStartAt actualPhysicalTransferInitialMarkerAt
    actualPhysicalTransferLiveStartAt physicalStartObservationFlags
    actualPhysicalTransferInitialMarkerAt_iff_record_first
    actualPhysicalTransferLiveStartAt_iff)
open Bandits.Support.ReferenceOriginalFirstBadStrictPrefix
  (noBadEventStrictlyBefore)
open Bandits.Support.PhaseServiceWaiting (IsPreRoundStoppingTime)
open scoped Classical

namespace Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- A start date is included through the detecting update itself. -/
def stoppedPhysicalTransferStartAt (q : Fin p.T) (z : SourceInput p) : Prop :=
  actualPhysicalTransferStartAt rate rewards C_star C_h q z ∧
    q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z

/-- The original round indices whose literal actual starts survive the
inclusive first-bad-date cutoff. -/
def stoppedPhysicalTransferStartRounds (z : SourceInput p) : Finset (Fin p.T) :=
  Finset.univ.filter (fun q => stoppedPhysicalTransferStartAt rate rewards C_star C_h q z)

/-- Original one-based dates of all included physical starts. -/
def stoppedPhysicalTransferStartDates (z : SourceInput p) : Finset ℕ :=
  (stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).image
    (fun q : Fin p.T => q.val + 1)

/-- The chronological finite list of included one-based start dates. -/
def stoppedPhysicalTransferStartList (z : SourceInput p) : List ℕ :=
  (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).sort (· ≤ ·)

/-- The `k`-th included physical start, with zero-based Lean position and
sentinel `T + 1` when fewer than `k + 1` starts are present. -/
def stoppedPhysicalTransferStartDate (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  (stoppedPhysicalTransferStartList rate rewards C_star C_h z).getD k.val (p.T + 1)

private theorem actualRecordAt_state_correspondence
    (q : Fin p.T) (z z' : SourceInput p)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z')
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecordAt rate rewards C_star C_h q z = some record) :
    ∃ record' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      actualRecordAt rate rewards C_star C_h q z' = some record' ∧
        record.input.state = record'.input.state := by
  cases hr' : actualRecordAt rate rewards C_star C_h q z' with
  | none =>
      have hr0 : actualRecord rate rewards C_star C_h q z = some record := hr
      have hr'0 : actualRecord rate rewards C_star C_h q z' = none := hr'
      have hnone := hin
      change (actualRecord rate rewards C_star C_h q z).map
          (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
        (actualRecord rate rewards C_star C_h q z').map
          (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
        at hnone
      rw [hr0, hr'0] at hnone
      cases hnone
  | some record' =>
      have hr0 : actualRecord rate rewards C_star C_h q z = some record := hr
      have hr'0 : actualRecord rate rewards C_star C_h q z' = some record' := hr'
      have hcode :
          ReferenceActivePhysicalStepMeasurability.encodeState record.input.state =
            ReferenceActivePhysicalStepMeasurability.encodeState record'.input.state := by
        have hcodes := hin
        change (actualRecord rate rewards C_star C_h q z).map
            (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
          (actualRecord rate rewards C_star C_h q z').map
            (fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
          at hcodes
        rw [hr0, hr'0] at hcodes
        exact Option.some.inj hcodes
      exact ⟨record', rfl,
        ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode⟩

private theorem actualPhysicalTransferInitialMarkerAt_prefix_factor
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p) :
    actualPhysicalTransferInitialMarkerAt rate rewards C_star C_h q z ↔
      actualPhysicalTransferInitialMarkerAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z) := by
  rw [actualPhysicalTransferInitialMarkerAt_iff_record_first,
    actualPhysicalTransferInitialMarkerAt_iff_record_first]
  constructor
  · rintro ⟨record, hr, hfirst⟩
    obtain ⟨record', hr', hstate⟩ := actualRecordAt_state_correspondence
      rate rewards C_star C_h q z (sourcePrefix control0 q.val z)
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 q z) record hr
    exact ⟨record', hr', by rw [← hstate]; exact hfirst⟩
  · rintro ⟨record, hr, hfirst⟩
    obtain ⟨record', hr', hstate⟩ := actualRecordAt_state_correspondence
      rate rewards C_star C_h q (sourcePrefix control0 q.val z) z
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 q z).symm record hr
    exact ⟨record', hr', by rw [← hstate]; exact hfirst⟩

private theorem actualPhysicalTransferLiveStartAt_prefix_factor
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p) :
    actualPhysicalTransferLiveStartAt rate rewards C_star C_h q z ↔
      actualPhysicalTransferLiveStartAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z) := by
  rw [actualPhysicalTransferLiveStartAt_iff, actualPhysicalTransferLiveStartAt_iff]
  constructor
  · rintro ⟨record, regs, owned, base, started, hr, hcoord, hstart, hcommand⟩
    obtain ⟨record', hr', hstate⟩ := actualRecordAt_state_correspondence
      rate rewards C_star C_h q z (sourcePrefix control0 q.val z)
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 q z) record hr
    refine ⟨record', regs, owned, base, started, hr', ?_, hstart, hcommand⟩
    rw [← hstate]
    exact hcoord
  · rintro ⟨record, regs, owned, base, started, hr, hcoord, hstart, hcommand⟩
    obtain ⟨record', hr', hstate⟩ := actualRecordAt_state_correspondence
      rate rewards C_star C_h q (sourcePrefix control0 q.val z) z
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 q z).symm record hr
    refine ⟨record', regs, owned, base, started, hr', ?_, hstart, hcommand⟩
    rw [← hstate]
    exact hcoord

/-- The actual start marker is determined by incoming state and the literal
pre-round live clock call. Row-bearing current records need not be identical. -/
theorem actualPhysicalTransferStartAt_prefix_factor
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p) :
    actualPhysicalTransferStartAt rate rewards C_star C_h q z ↔
      actualPhysicalTransferStartAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z) := by
  change (actualPhysicalTransferInitialMarkerAt rate rewards C_star C_h q z ∨
      actualPhysicalTransferLiveStartAt rate rewards C_star C_h q z) ↔
    (actualPhysicalTransferInitialMarkerAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z) ∨
      actualPhysicalTransferLiveStartAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z))
  rw [actualPhysicalTransferInitialMarkerAt_prefix_factor,
    actualPhysicalTransferLiveStartAt_prefix_factor]

/-- The first-bad-date test includes a start on the detecting update and
factors through the original strict prefix. -/
theorem stoppedPhysicalTransferStartAt_prefix_factor
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p) :
    stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ↔
      stoppedPhysicalTransferStartAt rate rewards C_star C_h q
        (sourcePrefix control0 q.val z) := by
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨(actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z).mp hs, ?_⟩
    exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
      rate rewards C_star C_h control0 q z).mp hb
  · rintro ⟨hs, hb⟩
    refine ⟨(actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z).mpr hs, ?_⟩
    exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
      rate rewards C_star C_h control0 q z).mpr hb

/-- Replacing the current selected control leaves both the actual pre-round
start command and the inclusive first-bad-date decision unchanged. -/
theorem stoppedPhysicalTransferStartAt_replaceSourceControl
    (control0 : TimeControl p) (q : Fin p.T) (z : SourceInput p)
    (control : TimeControl p) :
    stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ↔
      stoppedPhysicalTransferStartAt rate rewards C_star C_h q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z control) := by
  constructor
  · rintro ⟨hs, hb⟩
    have hprefix := (actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z).mp hs
    rw [← ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
      control0 q z control] at hprefix
    have hreplace := (actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z control)).mpr hprefix
    exact ⟨hreplace,
      (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_replaceSourceControl
        rate rewards C_star C_h control0 q z control).mp hb⟩
  · rintro ⟨hs, hb⟩
    have hprefix := (actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z control)).mp hs
    rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
      control0 q z control] at hprefix
    have horiginal := (actualPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z).mpr hprefix
    exact ⟨horiginal,
      (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_replaceSourceControl
        rate rewards C_star C_h control0 q z control).mpr hb⟩

/-- The actual encoded incoming state is measurable at the source's
pre-choice field. This is the state input used by both literal start flags. -/
theorem actualIncomingState_preRound_measurable
    (control0 : TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q) :=
  ReferenceSourcePrefixHistoryFiltration.incoming_measurable
    rate rewards C_star C_h control0 q

/-- Predictability of the actual physical start at its one-based source round. -/
theorem actualPhysicalTransferStartAt_preRound_measurable
    (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p | actualPhysicalTransferStartAt rate rewards C_star C_h q z} := by
  have hbase : Measurable (fun z : SourceInput p =>
      decide (actualPhysicalTransferStartAt rate rewards C_star C_h q z)) := by
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      (ReferenceOriginalCalendarPhysicalTransferCount.measurableSet_actualPhysicalTransferStartAt
        rate rewards C_star C_h q)
  have hstart : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p |
      actualPhysicalTransferStartAt rate rewards C_star C_h q z} := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
    have hcomap := hbase.comp (comap_measurable (sourcePrefix control0 q.val))
    have hset : {z : SourceInput p | actualPhysicalTransferStartAt rate rewards C_star C_h q z} =
        {z : SourceInput p | decide (actualPhysicalTransferStartAt rate rewards C_star C_h q
          (sourcePrefix control0 q.val z)) = true} := by
      ext z
      simp only [decide_eq_true_eq]
      exact (actualPhysicalTransferStartAt_prefix_factor
        rate rewards C_star C_h control0 q z)
    rw [hset]
    exact hcomap (measurableSet_singleton true)
  exact hstart

/-- Predictability of the actual stopped start at its one-based source round. -/
theorem stoppedPhysicalTransferStartAt_preRound_measurable
    (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p | stoppedPhysicalTransferStartAt rate rewards C_star C_h q z} := by
  have hstart := actualPhysicalTransferStartAt_preRound_measurable
    rate rewards C_star C_h control0 q
  have hstop : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      {z : SourceInput p |
      q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z} := by
    have hset : {z : SourceInput p |
        q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z} =
        {z | noBadEventStrictlyBefore rate rewards C_star C_h z q} := by
      ext x
      exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff
        rate rewards C_star C_h x q)
    rw [hset]
    exact ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_strictPrefix_measurable
      rate rewards C_star C_h control0 q
  exact hstart.inter hstop

/-- The count of included starts at or before original one-based date `n`. -/
def stoppedPhysicalTransferStartCountThrough (n : ℕ) (z : SourceInput p) : ℕ :=
  ((stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).filter
    (fun q => q.val + 1 ≤ n)).card

theorem stoppedPhysicalTransferStartRounds_card_eq_count (z : SourceInput p) :
    (stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).card =
      ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z := by
  classical
  unfold stoppedPhysicalTransferStartRounds stoppedPhysicalTransferStartAt
  rw [ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount]
  simp [Finset.sum_boole]

theorem stoppedPhysicalTransferStartDates_card_eq_rounds_card (z : SourceInput p) :
    (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).card =
      (stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).card := by
  apply Finset.card_image_of_injOn
  intro q hq r hr heq
  apply Fin.ext
  exact Nat.add_right_cancel heq

theorem stoppedPhysicalTransferStartDates_card_le_horizon (z : SourceInput p) :
    (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).card ≤ p.T := by
  rw [stoppedPhysicalTransferStartDates_card_eq_rounds_card]
  calc
    (stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).card ≤
        (Finset.univ : Finset (Fin p.T)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = p.T := by simp

theorem stoppedPhysicalTransferStartList_length (z : SourceInput p) :
    (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length =
      (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).card := by
  simp [stoppedPhysicalTransferStartList, Finset.length_sort]

theorem stoppedPhysicalTransferStartList_sortedLE (z : SourceInput p) :
    (stoppedPhysicalTransferStartList rate rewards C_star C_h z).SortedLE := by
  exact (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).sortedLT_sort.sortedLE

theorem stoppedPhysicalTransferStartList_nodup (z : SourceInput p) :
    (stoppedPhysicalTransferStartList rate rewards C_star C_h z).Nodup := by
  exact (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).sort_nodup (· ≤ ·)

theorem mem_stoppedPhysicalTransferStartDates_iff (d : ℕ) (z : SourceInput p) :
    d ∈ stoppedPhysicalTransferStartDates rate rewards C_star C_h z ↔
      ∃ q : Fin p.T, stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
        q.val + 1 = d := by
  classical
  simp [stoppedPhysicalTransferStartDates, stoppedPhysicalTransferStartRounds,
    stoppedPhysicalTransferStartAt, eq_comm]

theorem stoppedPhysicalTransferStartDate_le_horizon_iff
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T ↔
      k.val < (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length := by
  let l := stoppedPhysicalTransferStartList rate rewards C_star C_h z
  by_cases hk : k.val < l.length
  · have hmem : l[k.val] ∈ l := List.getElem_mem ..
    have hdates := (Finset.mem_sort (α := ℕ) (· ≤ ·)).1 hmem
    obtain ⟨q, hq, hdate⟩ := (mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hdates
    have hdateBound : l[k.val] ≤ p.T := by rw [← hdate]; omega
    change l.getD k.val (p.T + 1) ≤ p.T ↔ k.val < l.length
    rw [List.getD_eq_getElem (l := l) (d := p.T + 1) hk]
    exact ⟨fun _ => hk, fun _ => hdateBound⟩
  · have hdefault := List.getD_eq_default (l := l) (d := p.T + 1)
      (Nat.le_of_not_gt hk)
    change l.getD k.val (p.T + 1) ≤ p.T ↔ k.val < l.length
    rw [hdefault]
    constructor
    · intro h
      exact False.elim (by omega)
    · intro h
      exact False.elim (hk h)

theorem stoppedPhysicalTransferStartDate_eq_iff
    (k : Fin (p.T + 1)) (d : ℕ) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z = d ↔
      (stoppedPhysicalTransferStartList rate rewards C_star C_h z)[k.val]? = some d ∨
      ((stoppedPhysicalTransferStartList rate rewards C_star C_h z).length ≤ k.val ∧
        p.T + 1 = d) := by
  let l := stoppedPhysicalTransferStartList rate rewards C_star C_h z
  change l.getD k.val (p.T + 1) = d ↔ _
  rw [List.getD_eq_getElem?_getD]
  cases hget : l[k.val]? with
  | none =>
      have hlen : l.length ≤ k.val := (List.getElem?_eq_none_iff).mp hget
      simp [hlen, l]
  | some value =>
      have hpos : k.val < l.length := (List.getElem?_eq_some_iff.mp hget).1
      simp [hpos, l]

theorem stoppedPhysicalTransferStartDate_present_exactly
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T ↔
      k.val < (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).card := by
  rw [stoppedPhysicalTransferStartDate_le_horizon_iff,
    stoppedPhysicalTransferStartList_length]

theorem stoppedPhysicalTransferStartDate_eq_sentinel_iff
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z = p.T + 1 ↔
      (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).card ≤ k.val := by
  constructor
  · intro hdate
    by_contra hnot
    have hpos : k.val < (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length := by
      rw [stoppedPhysicalTransferStartList_length]
      omega
    have hle := (stoppedPhysicalTransferStartDate_le_horizon_iff
      rate rewards C_star C_h k z).2 hpos
    omega
  · intro hk
    unfold stoppedPhysicalTransferStartDate
    have hkList : (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length ≤ k.val := by
      rw [stoppedPhysicalTransferStartList_length]
      exact hk
    rw [List.getD_eq_default
      (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
      (d := p.T + 1) hkList]

theorem stoppedPhysicalTransferStartDate_mem_iff
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T ↔
      stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ∈
        stoppedPhysicalTransferStartDates rate rewards C_star C_h z := by
  constructor
  · intro hk
    have hpos := (stoppedPhysicalTransferStartDate_le_horizon_iff
      rate rewards C_star C_h k z).mp hk
    have hmem :
        (stoppedPhysicalTransferStartList rate rewards C_star C_h z)[k.val] ∈
          stoppedPhysicalTransferStartList rate rewards C_star C_h z :=
      List.getElem_mem hpos
    have hget := List.getD_eq_getElem
      (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
      (d := p.T + 1) hpos
    rw [stoppedPhysicalTransferStartDate, hget]
    exact (Finset.mem_sort (α := ℕ) (· ≤ ·)).mp
      hmem
  · intro hmem
    obtain ⟨q, hq, hdate⟩ := (mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
    rw [← hdate]
    omega

theorem stoppedPhysicalTransferStartDate_injective_present
    (k l : Fin (p.T + 1)) (z : SourceInput p)
    (hk : stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T)
    (hl : stoppedPhysicalTransferStartDate rate rewards C_star C_h l z ≤ p.T)
    (heq : stoppedPhysicalTransferStartDate rate rewards C_star C_h k z =
      stoppedPhysicalTransferStartDate rate rewards C_star C_h l z) :
    k = l := by
  have hkl := (stoppedPhysicalTransferStartDate_present_exactly
    rate rewards C_star C_h k z).mp hk
  have hll := (stoppedPhysicalTransferStartDate_present_exactly
    rate rewards C_star C_h l z).mp hl
  have hklList : k.val < (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length := by
    rw [stoppedPhysicalTransferStartList_length]
    exact hkl
  have hllList : l.val < (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length := by
    rw [stoppedPhysicalTransferStartList_length]
    exact hll
  have hget : (stoppedPhysicalTransferStartList rate rewards C_star C_h z)[k.val] =
      (stoppedPhysicalTransferStartList rate rewards C_star C_h z)[l.val] := by
    simpa only [stoppedPhysicalTransferStartDate,
      List.getD_eq_getElem
        (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
        (d := p.T + 1) hklList,
      List.getD_eq_getElem
        (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
        (d := p.T + 1) hllList] using heq
  apply Fin.ext
  exact (stoppedPhysicalTransferStartList_nodup rate rewards C_star C_h z).getElem_inj_iff.mp hget

theorem every_stoppedPhysicalTransferStartDate_occurs_once
    (d : ℕ) (z : SourceInput p)
    (hd : d ∈ stoppedPhysicalTransferStartDates rate rewards C_star C_h z) :
    ∃! k : Fin (p.T + 1), stoppedPhysicalTransferStartDate rate rewards C_star C_h k z = d := by
  have hdBound : d ≤ p.T := by
    obtain ⟨q, hq, rfl⟩ :=
      (mem_stoppedPhysicalTransferStartDates_iff rate rewards C_star C_h d z).mp hd
    omega
  have hlistMem : d ∈ stoppedPhysicalTransferStartList rate rewards C_star C_h z :=
    (Finset.mem_sort (α := ℕ) (· ≤ ·)).2 hd
  obtain ⟨i, hi, hget⟩ :=
    List.mem_iff_getElem.mp hlistMem
  have hiBound : i < p.T := by
    have hlen : (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length ≤ p.T := by
      rw [stoppedPhysicalTransferStartList_length]
      exact stoppedPhysicalTransferStartDates_card_le_horizon rate rewards C_star C_h z
    omega
  let k : Fin (p.T + 1) := ⟨i, by omega⟩
  have hdate : stoppedPhysicalTransferStartDate rate rewards C_star C_h k z = d := by
    rw [stoppedPhysicalTransferStartDate,
      List.getD_eq_getElem
        (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
        (d := p.T + 1) hi]
    exact hget
  refine ⟨k, hdate, ?_⟩
  intro l hld
  apply stoppedPhysicalTransferStartDate_injective_present
    rate rewards C_star C_h l k z ?_ ?_ (hld.trans hdate.symm)
  · simpa only [hld] using hdBound
  · simpa only [hdate] using hdBound

theorem stoppedPhysicalTransferStartDate_monotone
    (k l : Fin (p.T + 1)) (z : SourceInput p) (hkl : k ≤ l) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤
      stoppedPhysicalTransferStartDate rate rewards C_star C_h l z := by
  let dates := stoppedPhysicalTransferStartList rate rewards C_star C_h z
  by_cases hk : k.val < dates.length
  · by_cases hl : l.val < dates.length
    · have hmono := (stoppedPhysicalTransferStartList_sortedLE rate rewards C_star C_h z)
        |>.monotone_get (show (⟨k.val, hk⟩ : Fin dates.length) ≤ ⟨l.val, hl⟩ by
          exact Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hkl))
      change dates.getD k.val (p.T + 1) ≤ dates.getD l.val (p.T + 1)
      rw [List.getD_eq_getElem (l := dates) (d := p.T + 1) hk,
        List.getD_eq_getElem (l := dates) (d := p.T + 1) hl]
      exact hmono
    · have hleft : stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T :=
        (stoppedPhysicalTransferStartDate_le_horizon_iff rate rewards C_star C_h k z).2 hk
      have hright : stoppedPhysicalTransferStartDate rate rewards C_star C_h l z = p.T + 1 :=
        List.getD_eq_default (l := dates) (d := p.T + 1) (Nat.le_of_not_gt hl)
      rw [hright]
      omega
  · have hl : ¬ l.val < dates.length := by
      intro hl
      exact hk (lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hkl) hl)
    unfold stoppedPhysicalTransferStartDate
    rw [
      List.getD_eq_default (l := dates) (d := p.T + 1) (Nat.le_of_not_gt hk),
      List.getD_eq_default (l := dates) (d := p.T + 1) (Nat.le_of_not_gt hl)]

private theorem sorted_getD_le_iff_filter_length_gt
    (l : List ℕ) (hsorted : l.SortedLE) (k n sentinel : ℕ)
    (hsentinel : n < sentinel) :
    l.getD k sentinel ≤ n ↔ k < (l.filter (fun d => d ≤ n)).length := by
  induction l generalizing k with
  | nil => simp [List.getD, hsentinel]
  | cons a l ih =>
      have hp := hsorted.pairwise
      have htailSorted : l.SortedLE := hp.tail.sortedLE
      by_cases ha : a ≤ n
      · cases k with
        | zero => simp [List.getD, ha]
        | succ k =>
            have hget : l.getD k sentinel ≤ n ↔ k < (l.filter (fun d => d ≤ n)).length :=
              ih htailSorted k
            have hcon : (a :: l).getD (k + 1) sentinel = l.getD k sentinel := by
              calc
                (a :: l).getD (k + 1) sentinel = ((a :: l)[k + 1]?).getD sentinel :=
                  List.getD_eq_getElem?_getD
                _ = l[k]?.getD sentinel := by simp
                _ = l.getD k sentinel :=
                  (List.getD_eq_getElem?_getD (l := l)).symm
            rw [hcon]
            simp only [List.filter_cons, decide_eq_true_eq, ha, ite_eq_left, List.length_cons,
              Nat.succ_lt_succ_iff]
            exact hget
      · have htail : ∀ b ∈ l, n < b := by
          intro b hb
          have hab := hp.rel_head_tail hb
          exact lt_of_lt_of_le (lt_of_not_ge ha) hab
        have hfilter : (a :: l).filter (fun d => d ≤ n) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · simpa only [decide_eq_true_eq] using ha
          · simpa only [decide_eq_true_eq] using not_le_of_gt (htail b hb)
        cases k with
        | zero => simp [List.getD, hfilter, ha]
        | succ k =>
            have hget : n < l.getD k sentinel := by
              by_cases hk : k < l.length
              · have hmem : l.getD k sentinel ∈ l := by
                  rw [List.getD_eq_getElem (l := l) (d := sentinel) hk]
                  exact List.getElem_mem ..
                exact htail _ hmem
              · rw [List.getD_eq_default (l := l) (d := sentinel)
                  (Nat.le_of_not_gt hk)]
                exact hsentinel
            have hget' : n < l[k]?.getD sentinel := by
              rw [← List.getD_eq_getElem?_getD]
              exact hget
            change (l[k]?.getD sentinel ≤ n) ↔ _
            rw [hfilter]
            simp [hget']

private theorem stoppedPhysicalTransferStartDates_filter_eq_image
    (n : ℕ) (z : SourceInput p) :
    (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).filter
        (fun d => d ≤ n) =
      ((stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).filter
        (fun q : Fin p.T => q.val + 1 ≤ n)).image (fun q : Fin p.T => q.val + 1) := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hd, hdn⟩
    obtain ⟨q, hq, rfl⟩ := (mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h d z).mp hd
    exact ⟨q, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, hdn⟩, rfl⟩
  · rintro ⟨q, ⟨hq, hqn⟩, rfl⟩
    exact ⟨(mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h (q.val + 1) z).mpr
        ⟨q, (Finset.mem_filter.mp hq).2, rfl⟩, hqn⟩

theorem stoppedPhysicalTransferStartDates_filter_card_eq_count
    (n : ℕ) (z : SourceInput p) :
    ((stoppedPhysicalTransferStartDates rate rewards C_star C_h z).filter
      (fun d => d ≤ n)).card = stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n z := by
  rw [stoppedPhysicalTransferStartDates_filter_eq_image rate rewards C_star C_h n z]
  calc
    (((stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).filter
      (fun q : Fin p.T => q.val + 1 ≤ n)).image (fun q : Fin p.T => q.val + 1)).card =
      ((stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).filter
        (fun q : Fin p.T => q.val + 1 ≤ n)).card := by
          apply Finset.card_image_of_injOn
          intro q hq r hr heq
          apply Fin.ext
          exact Nat.add_right_cancel heq
    _ = stoppedPhysicalTransferStartCountThrough rate rewards C_star C_h n z := rfl

theorem stoppedPhysicalTransferStartList_filter_length_eq_count
    (n : ℕ) (z : SourceInput p) :
    ((stoppedPhysicalTransferStartList rate rewards C_star C_h z).filter
      (fun d => d ≤ n)).length = stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n z := by
  rw [← List.toFinset_card_of_nodup
    ((stoppedPhysicalTransferStartList_nodup rate rewards C_star C_h z).filter _)]
  have hset : ((stoppedPhysicalTransferStartList rate rewards C_star C_h z).filter
      (fun d => d ≤ n)).toFinset =
      (stoppedPhysicalTransferStartDates rate rewards C_star C_h z).filter
        (fun d => d ≤ n) := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdn⟩
      exact ⟨(Finset.mem_sort (α := ℕ) (· ≤ ·)).1 hd, of_decide_eq_true hdn⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨(Finset.mem_sort (α := ℕ) (· ≤ ·)).2 hd, by simpa using hdn⟩
  rw [hset, stoppedPhysicalTransferStartDates_filter_card_eq_count]

theorem stoppedPhysicalTransferStartDate_le_iff_count_gt
    (k : Fin (p.T + 1)) (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ n ↔
      k.val < stoppedPhysicalTransferStartCountThrough rate rewards C_star C_h n z := by
  rw [stoppedPhysicalTransferStartDate,
    sorted_getD_le_iff_filter_length_gt
      (stoppedPhysicalTransferStartList rate rewards C_star C_h z)
      (stoppedPhysicalTransferStartList_sortedLE rate rewards C_star C_h z)
      k.val n (p.T + 1) (by omega),
    stoppedPhysicalTransferStartList_filter_length_eq_count]

/-- Membership and exact chronological position in the sorted finite set. -/
theorem stoppedPhysicalTransferStartCountThrough_gt_iff_subset
    (n k : ℕ) (z : SourceInput p) :
    k < stoppedPhysicalTransferStartCountThrough rate rewards C_star C_h n z ↔
      ∃ s : Finset (Fin p.T), s.card = k + 1 ∧
        ∀ q ∈ s, stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
          q.val + 1 ≤ n := by
  rw [stoppedPhysicalTransferStartCountThrough, Nat.lt_iff_add_one_le]
  constructor
  · intro hcard
    obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hcard
    refine ⟨s, hscard, ?_⟩
    intro q hq
    have hq' := Finset.mem_filter.mp (hs hq)
    exact ⟨(Finset.mem_filter.mp hq'.1).2, hq'.2⟩
  · rintro ⟨s, hscard, hproperty⟩
    have hs : s ⊆ (stoppedPhysicalTransferStartRounds rate rewards C_star C_h z).filter
        (fun q => q.val + 1 ≤ n) := by
      intro q hq
      have ⟨hstop, hdate⟩ := hproperty q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstop⟩, hdate⟩
    have := Finset.card_le_card hs
    omega

private theorem stoppedPhysicalTransferStartAt_measurable_through
    (control0 : TimeControl p) (q : Fin p.T) (n : ℕ) :
    MeasurableSet[sourcePrefixFiltration control0 n]
      {z : SourceInput p | stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
        q.val + 1 ≤ n} := by
  by_cases hqn : q.val + 1 ≤ n
  · have hq := stoppedPhysicalTransferStartAt_preRound_measurable
      rate rewards C_star C_h control0 q
    have hmono := (sourcePrefixFiltration control0).mono hqn _ hq
    simpa only [hqn, and_true] using hmono
  · have hset : {z : SourceInput p |
        stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧ q.val + 1 ≤ n} = ∅ := by
      ext z
      simp [hqn]
    rw [hset]
    exact @MeasurableSet.empty (SourceInput p) (sourcePrefixFiltration control0 n)

private theorem stoppedPhysicalTransferStartSubset_measurable
    (control0 : TimeControl p) (n k : ℕ) (s : Finset (Fin p.T)) :
    MeasurableSet[sourcePrefixFiltration control0 n]
      {z : SourceInput p | s.card = k + 1 ∧
        ∀ q ∈ s, stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
          q.val + 1 ≤ n} := by
  by_cases hcard : s.card = k + 1
  · simp only [hcard, true_and, Set.ofPred_forall]
    exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
      stoppedPhysicalTransferStartAt_measurable_through
        rate rewards C_star C_h control0 q n
  · simp [hcard]

/-- Every ordered start has the same one-based date as its finite-set slot;
its absence is exactly the horizon sentinel. -/
theorem stoppedPhysicalTransferStartDate_le_sentinel
    (k : Fin (p.T + 1)) (z : SourceInput p) :
    stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T + 1 := by
  by_cases hk : k.val < (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length
  · have hpresent := (stoppedPhysicalTransferStartDate_le_horizon_iff
      rate rewards C_star C_h k z).2 hk
    omega
  · rw [stoppedPhysicalTransferStartDate,
      List.getD_eq_default
        (l := stoppedPhysicalTransferStartList rate rewards C_star C_h z)
        (d := p.T + 1) (Nat.le_of_not_gt hk)]

/-- The `k`-th date is a stopping time for the analytical original-source
pre-round filtration, including zero, interior dates and the sentinel. -/
theorem stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
    (control0 : TimeControl p) (k : Fin (p.T + 1)) :
    IsPreRoundStoppingTime (sourcePrefixFiltration control0)
      (stoppedPhysicalTransferStartDate rate rewards C_star C_h k) := by
  intro n
  by_cases hn : p.T < n
  · have hset : {z : SourceInput p |
        stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (stoppedPhysicalTransferStartDate_le_sentinel
        rate rewards C_star C_h k z).trans (Nat.succ_le_of_lt hn)
    rw [hset]
    exact MeasurableSet.univ
  · have hnT : n ≤ p.T := Nat.le_of_not_gt hn
    have hevent : {z : SourceInput p |
        stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ n} =
      {z | ∃ s : Finset (Fin p.T), s.card = k.val + 1 ∧
        ∀ q ∈ s, stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
          q.val + 1 ≤ n} := by
      ext z
      simpa only [Set.mem_ofPred_eq] using
        (stoppedPhysicalTransferStartDate_le_iff_count_gt
          rate rewards C_star C_h k n hnT z).trans
          (stoppedPhysicalTransferStartCountThrough_gt_iff_subset
            rate rewards C_star C_h n k z)
    rw [hevent]
    have hunion : {z : SourceInput p | ∃ s : Finset (Fin p.T),
        s.card = k.val + 1 ∧ ∀ q ∈ s,
          stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧ q.val + 1 ≤ n} =
        ⋃ s : Finset (Fin p.T), {z : SourceInput p | s.card = k.val + 1 ∧
          ∀ q ∈ s, stoppedPhysicalTransferStartAt rate rewards C_star C_h q z ∧
            q.val + 1 ≤ n} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hunion]
    exact MeasurableSet.iUnion fun s =>
      stoppedPhysicalTransferStartSubset_measurable
        rate rewards C_star C_h control0 n k.val s

/-- The finite chronological list contains exactly the literal stopped
starts counted by the accepted full-calendar root. -/
theorem stoppedPhysicalTransferStartList_length_eq_actualCount (z : SourceInput p) :
    (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length =
      ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z := by
  rw [stoppedPhysicalTransferStartList_length,
    stoppedPhysicalTransferStartDates_card_eq_rounds_card,
    stoppedPhysicalTransferStartRounds_card_eq_count]

private theorem sum_present_sigma_eq_list_length (z : SourceInput p) :
    (∑ k : Fin (p.T + 1),
      if stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T then 1 else 0) =
      (stoppedPhysicalTransferStartList rate rewards C_star C_h z).length := by
  let dates := stoppedPhysicalTransferStartList rate rewards C_star C_h z
  have hlen : dates.length ≤ p.T := by
    dsimp only [dates]
    rw [stoppedPhysicalTransferStartList_length]
    exact stoppedPhysicalTransferStartDates_card_le_horizon rate rewards C_star C_h z
  have hfilter : (Finset.univ.filter (fun k : Fin (p.T + 1) => k.val < dates.length)).card =
      dates.length := by
    let embed : Fin dates.length → Fin (p.T + 1) := fun i =>
      ⟨i.val, Nat.lt_succ_of_le (le_trans i.isLt.le hlen)⟩
    have hset : Finset.univ.filter (fun k : Fin (p.T + 1) => k.val < dates.length) =
        Finset.image embed Finset.univ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · intro hk
        exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
      · rintro ⟨i, rfl⟩
        exact i.isLt
    have hinj : Function.Injective embed := by
      intro i j hij
      apply Fin.ext
      simpa only [embed] using congrArg Fin.val hij
    calc
      (Finset.univ.filter (fun k : Fin (p.T + 1) => k.val < dates.length)).card =
          (Finset.image embed Finset.univ).card := congrArg Finset.card hset
      _ = (Finset.univ : Finset (Fin dates.length)).card :=
        Finset.card_image_of_injective Finset.univ hinj
      _ = dates.length := by simp
  calc
    (∑ k : Fin (p.T + 1),
        if stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T then 1 else 0) =
      ∑ k ∈ (Finset.univ : Finset (Fin (p.T + 1))),
        if k.val < dates.length then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hiff := stoppedPhysicalTransferStartDate_le_horizon_iff
            rate rewards C_star C_h k z
          by_cases hp : stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T
          · have hq := hiff.mp hp
            simp [hp, hq, dates]
          · have hq : ¬ k.val < dates.length := by
              intro hq
              exact hp (hiff.mpr (by simpa only [dates] using hq))
            simp [hp, hq]
    _ = (Finset.univ.filter (fun k : Fin (p.T + 1) => k.val < dates.length)).card := by
      exact Finset.sum_boole _ _
    _ = dates.length := hfilter

/-- The sum of present ranked starts is exactly the actual inclusive stopped
physical-transfer count; all actual branches and the first detecting date are
inherited from that count's defining predicate. -/
theorem sum_indicator_stoppedPhysicalTransferStartDate_eq_actualCount
    (z : SourceInput p) :
    (∑ k : Fin (p.T + 1),
      if stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T then 1 else 0) =
      ReferenceOriginalCalendarPhysicalTransferCount.actualStoppedPhysicalTransferCount
        rate rewards C_star C_h z := by
  rw [sum_present_sigma_eq_list_length, stoppedPhysicalTransferStartList_length_eq_actualCount]

end Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts

end
