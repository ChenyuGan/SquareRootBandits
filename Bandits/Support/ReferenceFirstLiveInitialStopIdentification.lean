/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInitialDecoderStopIdentification
public import Bandits.Support.ReferenceFirstLiveOriginalNumericalPrefix
public import Bandits.Support.ReferenceFirstLiveInitialTransferCost

/-!
# Original first-bad-date identification for the initial stopped transfer

The actual initial first-live window's local stop, handover support, release
support, and signed charge are identified with the original source's inclusive
first-bad-date prefix. The physical run and its reward and private inputs are
the same throughout.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveInitialStopIdentification

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Source" => SourceInput p
local notation "W" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h
local notation "missing" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
local notation "SH" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h
local notation "SR" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
    rate rewards C_star C_h
local notation "badDate" =>
  ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h

/-- The exact handover dates in the raw first-live window, clipped at the
original inclusive first-bad date. -/
public def originalFirstBadHandoverFilter (z : Source) : Finset ℕ := by
  classical
  exact ((W z).toFinset.filter fun r =>
    (missing r).Nonempty ∧ r.input.time.val + 1 ≤ badDate z).image
      (fun r => r.input.time.val + 1)

/-- The exact empty-missing dates in the raw first-live window, clipped at the
original inclusive first-bad date. -/
public def originalFirstBadReleaseFilter (z : Source) : Finset ℕ := by
  classical
  exact ((W z).toFinset.filter fun r =>
    missing r = ∅ ∧ r.input.time.val + 1 ≤ badDate z).image
      (fun r => r.input.time.val + 1)

/-- The actual first-live record date is retained exactly through the
inclusive original first-bad date. -/
public theorem first_window_stop_iff_firstBadDate
    (z : Source) (k : Fin (W z).length) :
    ((W z).get k).input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z ↔
      ((W z).get k).input.time.val + 1 ≤ badDate z := by
  let t := ((W z).get k).input.time
  have hdecoder :=
    ReferenceFirstLiveInitialDecoderStopIdentification.first_window_decoder_stop_iff
      rate rewards C_star C_h z k
  dsimp only at hdecoder
  have hoverflow :=
    ReferenceFirstLiveOriginalNumericalPrefix.overflowCutoff_iff_not_numericalOverflowBy
      rate rewards C_star C_h z k
  have hoverflow' :
      ((W z).get k).input.time.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
            rate rewards C_star C_h z ↔
        ¬ ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy
          rate rewards C_star C_h ((W z).get k).input.time z := by
    simpa only [List.get_eq_getElem] using hoverflow
  have hobservers :=
    ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_iff_observers
      rate rewards C_star C_h t z
  have hprefix :=
    ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff
      rate rewards C_star C_h z t
  have htests :
      ((W z).get k).input.time.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
            rate rewards C_star C_h z ∧
        ((W z).get k).input.time.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
            rate rewards C_star C_h z ↔
        ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore
          rate rewards C_star C_h z t := by
    rw [hdecoder, hoverflow', hobservers]
    constructor
    · rintro ⟨⟨hpre, hflag⟩, hnoOverflow⟩
      exact ⟨hnoOverflow, hpre, hflag⟩
    · rintro ⟨hnoOverflow, hpre, hflag⟩
      exact ⟨⟨hpre, hflag⟩, hnoOverflow⟩
  calc
    ((W z).get k).input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z ↔
      (((W z).get k).input.time.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
            rate rewards C_star C_h z ∧
        ((W z).get k).input.time.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
            rate rewards C_star C_h z) := by
      simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded,
        lt_min_iff]
    _ ↔ ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore
        rate rewards C_star C_h z t := htests
    _ ↔ ((W z).get k).input.time.val + 1 ≤ badDate z := hprefix.symm

/-- Membership in the clipped handover dates retains an actual raw-window
record and its original missing-confirmation state. -/
public theorem originalFirstBadHandoverFilter_mem_iff
    (z : Source) (d : ℕ) :
    d ∈ originalFirstBadHandoverFilter rate rewards C_star C_h z ↔
      ∃ k : Fin (W z).length,
        (W z)[k.val].input.time.val + 1 = d ∧
        (missing (W z)[k.val]).Nonempty ∧ d ≤ badDate z := by
  classical
  rw [originalFirstBadHandoverFilter, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, hdate⟩
    rcases Finset.mem_filter.mp hr with ⟨hr, hm, hbound⟩
    obtain ⟨n, hn, heq⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    refine ⟨⟨n, hn⟩, ?_, ?_, ?_⟩
    · exact (congrArg (fun q : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate) => q.input.time.val + 1) heq).trans hdate
    · simpa only [heq] using hm
    · simpa only [← hdate] using hbound
  · rintro ⟨k, hdate, hm, hbound⟩
    refine ⟨(W z)[k.val], ?_, hdate⟩
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), ?_⟩
    exact ⟨hm, by simpa only [hdate] using hbound⟩

/-- Membership in the clipped release dates retains an actual raw-window
record with empty missing-confirmation state. -/
public theorem originalFirstBadReleaseFilter_mem_iff
    (z : Source) (d : ℕ) :
    d ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z ↔
      ∃ k : Fin (W z).length,
        (W z)[k.val].input.time.val + 1 = d ∧
        missing (W z)[k.val] = ∅ ∧ d ≤ badDate z := by
  classical
  rw [originalFirstBadReleaseFilter, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, hdate⟩
    rcases Finset.mem_filter.mp hr with ⟨hr, hm, hbound⟩
    obtain ⟨n, hn, heq⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    refine ⟨⟨n, hn⟩, ?_, ?_, ?_⟩
    · exact (congrArg (fun q : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate) => q.input.time.val + 1) heq).trans hdate
    · simpa only [heq] using hm
    · simpa only [← hdate] using hbound
  · rintro ⟨k, hdate, hm, hbound⟩
    refine ⟨(W z)[k.val], ?_, hdate⟩
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), ?_⟩
    exact ⟨hm, by simpa only [hdate] using hbound⟩

private theorem rawReleaseSupport_mem_iff (z : Source) (d : ℕ) :
    d ∈ SR z ↔
      ∃ k : Fin (W z).length,
        (W z)[k.val].input.time.val + 1 = d ∧
        missing (W z)[k.val] = ∅ ∧
        d < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z := by
  rw [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport,
    ReferenceFirstLiveInitialTransferChronology.raw_release_calendar
      rate rewards C_star C_h z]
  constructor
  · intro hd
    obtain ⟨hgate, hstop⟩ := Finset.mem_filter.mp hd
    obtain ⟨r, hr, hdate⟩ := Finset.mem_image.mp hgate
    obtain ⟨hr, hempty⟩ := Finset.mem_filter.mp hr
    obtain ⟨n, hn, heq⟩ :=
      List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    refine ⟨⟨n, hn⟩, ?_, ?_, ?_⟩
    · exact (congrArg (fun q : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate) => q.input.time.val + 1) heq).trans hdate
    · simpa only [heq] using hempty
    · simpa only [hdate] using hstop
  · rintro ⟨k, hdate, hempty, hstop⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ?_, hstop⟩
    refine ⟨(W z)[k.val], ?_, hdate⟩
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), hempty⟩

/-- Each date in the stopped handover support is exactly a nonempty-missing
window date no later than the original first bad event. -/
public theorem handoverSupport_eq_originalFirstBadFilter (z : Source) :
    SH z = originalFirstBadHandoverFilter rate rewards C_star C_h z := by
  ext d
  rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
      rate rewards C_star C_h z d,
    originalFirstBadHandoverFilter_mem_iff rate rewards C_star C_h z d]
  constructor
  · rintro ⟨k, hdate, hmissing, hstop⟩
    have hlocal : (W z)[k.val].input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z := by
      rw [hdate]
      exact hstop
    have hbound := (first_window_stop_iff_firstBadDate
      rate rewards C_star C_h z k).mp
        (by simpa only [List.get_eq_getElem] using hlocal)
    have hdate' : ((W z).get k).input.time.val + 1 = d := by
      simpa only [List.get_eq_getElem] using hdate
    exact ⟨k, hdate, hmissing, by rw [hdate'] at hbound; exact hbound⟩
  · rintro ⟨k, hdate, hmissing, hbound⟩
    have hbound' : (W z)[k.val].input.time.val + 1 ≤ badDate z := by
      rw [hdate]
      exact hbound
    have hlocal := (first_window_stop_iff_firstBadDate
      rate rewards C_star C_h z k).mpr
        (by simpa only [List.get_eq_getElem] using hbound')
    exact ⟨k, hdate, hmissing, by rw [← hdate]; exact hlocal⟩

/-- The actual stopped release support is exactly the empty-missing window
dates no later than the original first bad event. -/
public theorem releaseSupport_eq_originalFirstBadFilter (z : Source) :
    SR z = originalFirstBadReleaseFilter rate rewards C_star C_h z := by
  ext d
  rw [rawReleaseSupport_mem_iff rate rewards C_star C_h z d,
    originalFirstBadReleaseFilter_mem_iff rate rewards C_star C_h z d]
  constructor
  · rintro ⟨k, hdate, hempty, hstop⟩
    have hlocal : (W z)[k.val].input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z := by
      rw [hdate]
      exact hstop
    have hbound := (first_window_stop_iff_firstBadDate
      rate rewards C_star C_h z k).mp
        (by simpa only [List.get_eq_getElem] using hlocal)
    have hdate' : ((W z).get k).input.time.val + 1 = d := by
      simpa only [List.get_eq_getElem] using hdate
    exact ⟨k, hdate, hempty, by rw [hdate'] at hbound; exact hbound⟩
  · rintro ⟨k, hdate, hempty, hbound⟩
    have hbound' : (W z)[k.val].input.time.val + 1 ≤ badDate z := by
      rw [hdate]
      exact hbound
    have hlocal := (first_window_stop_iff_firstBadDate
      rate rewards C_star C_h z k).mpr
        (by simpa only [List.get_eq_getElem] using hbound')
    exact ⟨k, hdate, hempty, by rw [← hdate]; exact hlocal⟩

/-- The two exact original first-bad-date filters partition the already
accepted stopped initial calendar, including empty-window and no-release
branches. -/
public theorem stoppedInitialDates_eq_originalFirstBadFilters_union
    (z : Source) :
    ReferenceFirstLiveInitialTransferChronology.stoppedInitialDates
        rate rewards C_star C_h z =
      originalFirstBadHandoverFilter rate rewards C_star C_h z ∪
        originalFirstBadReleaseFilter rate rewards C_star C_h z := by
  have hcalendar :=
    ReferenceFirstLiveInitialTransferChronology.stopped_initial_calendar
      rate rewards C_star C_h z
  calc
    ReferenceFirstLiveInitialTransferChronology.stoppedInitialDates
        rate rewards C_star C_h z = SH z ∪ SR z := hcalendar.2.1.symm
    _ = originalFirstBadHandoverFilter rate rewards C_star C_h z ∪
          originalFirstBadReleaseFilter rate rewards C_star C_h z := by
      rw [handoverSupport_eq_originalFirstBadFilter,
        releaseSupport_eq_originalFirstBadFilter]

local notation "gH" =>
  ReferenceFirstLiveStoppedHandoverAdaptation.g_H rate rewards C_star C_h
local notation "signedStep" =>
  ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
    rate rewards C_star C_h

/-- The literal release deficit branch on the original actual-record and
stored-payload options, before its stopped-support mask is applied. -/
public def originalSignedReleaseBranch (t : Fin p.T) (z : Source) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => 0
  | some r =>
    match ReferenceAssignmentPayloadPersistence.storedPayload
        r.input.state.coordinator with
    | none => 0
    | some M =>
      ReleaseRoundKernel.slowReward
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        M.slowSet
        + (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
            (r.actions (ActiveRoundActions.coordinator p.two_le_m))
        - ∑ player : Fin p.m, ((r.ownEntries player).2).val.val

/-- The original signed release step keeps its actual-record and stored-
payload branches, with only its exact stopped-support mask transported to the
first-bad-date release filter. -/
public theorem signedStep_eq_originalFirstBadReleaseFilter
    (z : Source) (t : Fin p.T) :
    signedStep t z =
      if t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z then
        originalSignedReleaseBranch rate rewards C_star C_h t z
      else 0 := by
  change (if t.val + 1 ∈ SR z then
      originalSignedReleaseBranch rate rewards C_star C_h t z
      else 0) = _
  rw [releaseSupport_eq_originalFirstBadFilter rate rewards C_star C_h z]

/-- The exact initial charge is the capped handover sum and the same signed
release deficit, each filtered on raw first-live dates through the original
inclusive first-bad date. -/
public theorem initialCharge_eq_originalFirstBadFilteredCharge
    (control0 : ContinuousLearningRows.TimeControl p) (z : Source) :
    ReferenceFirstLiveInitialTransferCost.initialCharge
        rate rewards C_star C_h control0 z =
      (∑ t ∈ Finset.range p.T,
        if t + 1 ∈ originalFirstBadHandoverFilter rate rewards C_star C_h z then
          min (p.m : ℝ)
            (gH control0 t z)
        else 0) +
      (∑ t : Fin p.T,
        if t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z then
          signedStep t z else 0) := by
  have hhandover := handoverSupport_eq_originalFirstBadFilter
    rate rewards C_star C_h z
  have hcalendar :=
    ReferenceFirstLiveInitialTransferCost.initialCharge_calendar_characterization
      rate rewards C_star C_h control0 z
  have hcharge := hcalendar.2.2.2.2
  rw [hhandover] at hcharge
  have hsigned (t : Fin p.T) :
      signedStep t z =
        if t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z then
          signedStep t z else 0 := by
    by_cases h : t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z
    · simp [h]
    · rw [signedStep_eq_originalFirstBadReleaseFilter
        rate rewards C_star C_h z t]
      simp [h]
  have hsum :
      (∑ t : Fin p.T, signedStep t z) =
        ∑ t : Fin p.T,
          if t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z then
            signedStep t z else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hsigned t
  calc
    ReferenceFirstLiveInitialTransferCost.initialCharge
        rate rewards C_star C_h control0 z =
      (∑ t ∈ Finset.range p.T,
        if t + 1 ∈ originalFirstBadHandoverFilter rate rewards C_star C_h z then
          min (p.m : ℝ) (gH control0 t z) else 0) +
        (∑ t : Fin p.T, signedStep t z) := hcharge
    _ =
      (∑ t ∈ Finset.range p.T,
        if t + 1 ∈ originalFirstBadHandoverFilter rate rewards C_star C_h z then
          min (p.m : ℝ) (gH control0 t z) else 0) +
        (∑ t : Fin p.T,
          if t.val + 1 ∈ originalFirstBadReleaseFilter rate rewards C_star C_h z then
            signedStep t z else 0) := by rw [hsum]

end Bandits.Support.ReferenceFirstLiveInitialStopIdentification

end
