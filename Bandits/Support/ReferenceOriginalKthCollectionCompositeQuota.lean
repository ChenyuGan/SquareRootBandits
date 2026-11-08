/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment
public import Bandits.Support.ReferenceOriginalCollectionOldDownCanonicalQuota
public import Bandits.Support.ReferenceOriginalCollectionFormedUpCanonicalQuota

import Mathlib.Tactic

/-!
# Composite quota for the actual original kth C service readout

The OLD and FORMED-UP readouts are transported on the same original cutoff
run. Their accepted canonical quotas give the inclusive composite bound and
the strict incoming-prefix bound at every actual pending kth-C choice.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceOriginalKthCollectionCutoffAlignment
open ReferenceOriginalCollectionOldDownPendingPrefix
open ReferenceOriginalCollectionFormedUpCanonicalQuota
open ReferenceOriginalKthCollectionSourceSections
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthCollectionCompositeQuota

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Record {p : Parameters} (rate : RateInput p) :=
  ReferenceCompletePhysicalHistory.RoundRecord (p := p) (rate := rate)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

private theorem consecutive_dates_nodup (K : List (Record rate)) (start : ℕ)
    (hd : ∀ a : Fin K.length, K[a.val].input.time.val = start + a.val) :
    (K.map fun r => r.input.time).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro a b hab
  have ha : a.val < K.length := by simpa only [List.length_map] using a.isLt
  have hb : b.val < K.length := by simpa only [List.length_map] using b.isLt
  simp only [List.getElem_map] at hab
  have hv := congrArg Fin.val hab
  have hda := hd ⟨a.val, ha⟩
  have hdb := hd ⟨b.val, hb⟩
  change K[a.val].input.time.val = start + a.val at hda
  change K[b.val].input.time.val = start + b.val at hdb
  apply Fin.ext
  omega

private theorem calendar_prefix_sum_eq_take
    (K : List (Record rate)) (start : ℕ) (f : Fin p.T → ℝ)
    (hd : ∀ a : Fin K.length, K[a.val].input.time.val = start + a.val)
    (hzero : ∀ t, (¬ ∃ r ∈ K, r.input.time = t) → f t = 0)
    (v : ℕ) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v), f t) =
      ((K.take (v - start)).map fun r => f r.input.time).sum := by
  let L := (K.take (v - start)).map fun r => r.input.time
  have hnodup : L.Nodup := by
    apply consecutive_dates_nodup rate (K.take (v - start)) start
    intro a
    have ha : a.val < K.length := by
      have := a.isLt
      simp only [List.length_take] at this
      omega
    simpa only [List.getElem_take] using hd ⟨a.val, ha⟩
  have hsub : L.toFinset ⊆ Finset.univ.filter (fun t : Fin p.T => t.val < v) := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    obtain ⟨a, ha, har⟩ := List.mem_take_iff_getElem.mp hr
    have haK : a < K.length := (lt_min_iff.mp ha).2
    have hday := hd ⟨a, haK⟩
    change K[a].input.time.val = start + a at hday
    rw [har, hrt] at hday
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [show (K.take (v - start)).map (fun r => f r.input.time) = L.map f by
    simp only [L, List.map_map, Function.comp_def]]
  rw [← List.sum_toFinset f hnodup]
  symm
  apply Finset.sum_subset hsub
  intro t ht hnot
  apply hzero t
  rintro ⟨r, hr, hrt⟩
  obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
  have hday := hd ⟨a, ha⟩
  change K[a].input.time.val = start + a at hday
  rw [har, hrt] at hday
  have htv := (Finset.mem_filter.mp ht).2
  have hatake : a < min (v - start) K.length := by omega
  apply hnot
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨r, List.mem_take_iff_getElem.mpr ⟨a, hatake, har⟩, hrt⟩

private theorem complete_suffix_actual_launch_le_record
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
        rate rewards C_star C_h z ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time.val + 1 := by
  have ht := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
    rate rewards C_star C_h z j
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hj := j.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl] at hj
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by rw [hl]; rfl)
      have hc' : (ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome =
          true := hc
      change ReferenceInitializationRun.launchRound
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) ≤ _
      unfold ReferenceInitializationRun.launchRound
      rw [hc']
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 ≤ _
      omega

private theorem prechoice_some_actual_choice
    (t : Fin p.T) (data : KthCPrechoiceData rate)
    (hd : kthCPrechoiceData rate rewards C_star C_h t z = some data) :
    ∃ (r : Record rate) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceCollectionSegmentExtraction.choice r.input = some c := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp only [kthCPrechoiceData, ReferenceSourcePrefixHistoryFiltration.incoming,
        hr, Option.map_none, Option.bind_none] at hd
      cases hd
  | some r =>
      have hcode := kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr
      have hsome : ReferenceCollectionSegmentExtraction.choice r.input ≠ none := by
        intro hn
        cases hs : r.input.state.coordinator with
        | first =>
            rw [hcode] at hd
            simp [kthCPrechoiceDataFromCoordinatorCode,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs] at hd
        | dagger =>
            rw [hcode] at hd
            simp [kthCPrechoiceDataFromCoordinatorCode,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs] at hd
        | live registers owned base =>
            have hnone := kthCPrechoiceData_liveNoCollectionChoice
              rate rewards C_star C_h t z r hr registers owned base hs hn
            rw [hnone] at hd
            cases hd
        | collection payload ledger saved =>
            by_cases hp : ledger.pending.Nonempty
            · obtain ⟨c, hc, _⟩ := kthCPrechoiceData_actualCollectionChoice_nonempty
                rate rewards C_star C_h t z r hr payload ledger saved hs hp
              rw [hn] at hc
              cases hc
            · rw [hcode] at hd
              simp [kthCPrechoiceDataFromCoordinatorCode,
                ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs, hp] at hd
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hsome
      exact ⟨r, c, rfl, hc⟩

private theorem formed_mask_supported
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (hformed : z ∈ kthCFORMEDSet rate rewards C_star C_h k t i) :
    t ∈ kthCDates rate rewards C_star C_h z k := by
  obtain ⟨hs, pending, _hi, hstage⟩ := hformed
  obtain ⟨data, hdata, _hvalue⟩ := Option.map_eq_some_iff.mp hstage
  obtain ⟨r, c, hr, hc⟩ := prechoice_some_actual_choice
    rate rewards C_star C_h z t data hdata
  have hlookup := hr
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hlookup
  split at hlookup
  next hstart =>
    obtain ⟨hj, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
    let j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length :=
      ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, hj⟩
    have hday := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
      rate rewards C_star C_h z j
    have htime : r.input.time = t := by
      rw [hrecord] at hday
      apply Fin.ext
      dsimp only [j] at hday
      omega
    apply (mem_kthCDates_iff rate rewards C_star C_h z k t).mpr
    refine ⟨(kthCStratum_iff_mem_window rate rewards C_star C_h z k t).mp hs,
      j, ?_, ?_⟩
    · apply (mem_collectionPhaseIndices_iff rate rewards C_star C_h z j).mpr
      constructor
      · change ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
            rate rewards C_star C_h z ≤ _ ∧ _ ≤ min _ p.T
        refine ⟨complete_suffix_actual_launch_le_record rate rewards C_star C_h z j, ?_⟩
        change (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time.val + 1 ≤ _
        rw [hrecord, htime]
        exact Nat.le_min.mpr ⟨hs.2.2, by omega⟩
      · have hchoiceRecord :
            ReferenceCollectionSegmentExtraction.choice
              (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[j.val].input = some c := by
          cases hrecord
          exact hc
        change ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
          ReferenceCollectionSegmentExtraction.choice
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[j.val].input = some c
        exact ⟨c, hchoiceRecord⟩
    · change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time = t
      rw [hrecord]
      exact htime
  · cases hlookup

private theorem kthCFORMEDReadout_eq_zero_of_not_mem
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (ht : t ∉ kthCDates rate rewards C_star C_h z k) :
    kthCFORMEDReadout rate rewards C_star C_h k t i z = 0 := by
  unfold kthCFORMEDReadout
  apply Set.indicator_of_notMem
  intro hformed
  exact ht (formed_mask_supported rate rewards C_star C_h z k t i hformed)

private theorem kthCFORMEDReadout_at_supported_date
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (ht : t ∈ kthCDates rate rewards C_star C_h z k) :
    kthCFORMEDReadout rate rewards C_star C_h k t i z =
      (if ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .formed)
       then (1 : ℝ) else 0) *
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t z := by
  have hs := (kthCStratum_iff_mem_window rate rewards C_star C_h z k t).mpr
    (Finset.mem_inter.mp ht).1
  by_cases hm : ∃ pending, i ∈ pending ∧
      kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .formed)
  · have hz : z ∈ kthCFORMEDSet rate rewards C_star C_h k t i := ⟨hs, hm⟩
    rw [kthCFORMEDReadout, Set.indicator_of_mem hz]
    simp only [hm, ite_true, one_mul]
  · have hz : z ∉ kthCFORMEDSet rate rewards C_star C_h k t i := fun h => hm h.2
    rw [kthCFORMEDReadout, Set.indicator_of_notMem hz]
    simp only [hm, ite_false, zero_mul]

private theorem formed_readout_on_projected_record
    (k : Fin (p.T + 1)) (K : List (Record rate))
    (hprojection : kthCDates rate rewards C_star C_h z k =
      actualCutoffChoiceDates rate K
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z))
    (r : Record rate) (hr : r ∈ K)
    (hc : (ReferenceCollectionSegmentExtraction.choice r.input).isSome = true)
    (i : Fin (p.m - 1)) :
    kthCFORMEDReadout rate rewards C_star C_h k r.input.time i z =
      (if r.input.time.val + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
        then (1 : ℝ) else 0) *
      (if ∃ pending, i ∈ pending ∧
          kthCPrechoiceStage rate rewards C_star C_h r.input.time i z = some (pending, .formed)
        then (1 : ℝ) else 0) *
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i r.input.time z := by
  by_cases hb : r.input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  · have ht : r.input.time ∈ kthCDates rate rewards C_star C_h z k := by
      rw [hprojection]
      exact (mem_actualCutoffChoiceDates_iff rate K _ _).mpr ⟨r, hr, hc, hb, rfl⟩
    rw [kthCFORMEDReadout_at_supported_date rate rewards C_star C_h z k r.input.time i ht]
    simp only [hb, ite_true, one_mul]
  · have ht : r.input.time ∉ kthCDates rate rewards C_star C_h z k := by
      rw [hprojection]
      intro ht
      obtain ⟨r', _hr', _hc', hb', ht'⟩ :=
        (mem_actualCutoffChoiceDates_iff rate K _ _).mp ht
      rw [ht'] at hb'
      exact hb hb'
    rw [kthCFORMEDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k
      r.input.time i ht]
    simp only [hb, ite_false, zero_mul]

private theorem actual_cutoff_formed_up_prefix_transport_of_segment
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hat : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (v : ℕ) (i : Fin (p.m - 1)) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCFORMEDReadout rate rewards C_star C_h k t i z) =
      actualFormedUpPrefixReadoutSum rate rewards C_star C_h z seg.records
        (v - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val))
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) i := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hcalendar := ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
    rate rewards C_star C_h z e.val seg hat hne hcut
  have hprojection := kthCDates_eq_actual_segment_dates
    rate rewards C_star C_h z k hk e seg hdate hat
  have hd : ∀ a : Fin seg.records.length,
      seg.records[a.val].input.time.val =
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val) + a.val := by
    intro a
    have hday := (hcalendar a).2.1
    omega
  have hc : ∀ r ∈ seg.records,
      (ReferenceCollectionSegmentExtraction.choice r.input).isSome = true := by
    intro r hr
    obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨_hslot, _hday, c, hchoice, _hpayload⟩ := hcalendar ⟨a, ha⟩
    have hchoice' : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
      rw [← har]
      exact hchoice
    rw [hchoice']
    rfl
  let f : Fin p.T → ℝ := fun t =>
    kthCFORMEDReadout rate rewards C_star C_h k t i z
  have hzero : ∀ t, (¬ ∃ r ∈ seg.records, r.input.time = t) → f t = 0 := by
    intro t hnone
    apply kthCFORMEDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k t i
    rw [hprojection]
    intro ht
    obtain ⟨r, hr, _hc, _hb, hrt⟩ :=
      (mem_actualCutoffChoiceDates_iff rate seg.records _ _).mp ht
    exact hnone ⟨r, hr, hrt⟩
  rw [calendar_prefix_sum_eq_take rate seg.records
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val)
    f hd hzero v]
  unfold f actualFormedUpPrefixReadoutSum
  rw [← List.take_eq_take_min]
  congr 1
  apply List.map_congr_left
  intro r hr
  have hrK : r ∈ seg.records := List.mem_of_mem_take hr
  exact formed_readout_on_projected_record rate rewards C_star C_h z k seg.records
    hprojection r hrK (hc r hrK) i

/-- The literal FORMED-UP source readout on a calendar prefix equals the
date-gated readout on the same untruncated actual cutoff run. -/
public theorem actual_cutoff_formed_up_prefix_transport
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hat : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (v : ℕ) (i : Fin (p.m - 1)) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCFORMEDReadout rate rewards C_star C_h k t i z) =
      actualFormedUpPrefixReadoutSum rate rewards C_star C_h z
        (actualCutoffRun rate
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e)
        (v - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val))
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) i := by
  rw [actualCutoffRun_eq_actual_segment rate rewards C_star C_h z e seg hat hne hcut]
  exact actual_cutoff_formed_up_prefix_transport_of_segment rate rewards C_star C_h z
    k hk e seg hdate hat hne hcut v i

private theorem kthCSourceReadout_nonneg
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) :
    0 ≤ kthCSourceReadout rate rewards C_star C_h k t i z := by
  have hdown : 0 ≤ kthCOLDReadout rate rewards C_star C_h k t i z := by
    unfold kthCOLDReadout
    by_cases hm : z ∈ kthCOLDSet rate rewards C_star C_h k t i
    · rw [Set.indicator_of_mem hm]
      exact (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout_bounds
        (rate := rate) rewards C_star C_h i t z).1
    · rw [Set.indicator_of_notMem hm]
  have hup : 0 ≤ kthCFORMEDReadout rate rewards C_star C_h k t i z := by
    unfold kthCFORMEDReadout
    by_cases hm : z ∈ kthCFORMEDSet rate rewards C_star C_h k t i
    · rw [Set.indicator_of_mem hm]
      exact (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout_bounds
        (rate := rate) rewards C_star C_h i t z).1
    · rw [Set.indicator_of_notMem hm]
  unfold kthCSourceReadout
  exact add_nonneg hdown hup

private theorem kthCSourceReadout_prefix_nonneg
    (k : Fin (p.T + 1)) (v : ℕ) (i : Fin (p.m - 1)) :
    0 ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCSourceReadout rate rewards C_star C_h k t i z := by
  apply Finset.sum_nonneg
  intro t ht
  exact kthCSourceReadout_nonneg rate rewards C_star C_h z k t i

private theorem kthCFORMEDReadout_zero_of_empty
    (k : Fin (p.T + 1))
    (hempty : kthCDates rate rewards C_star C_h z k = ∅)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    kthCFORMEDReadout rate rewards C_star C_h k t i z = 0 := by
  apply kthCFORMEDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k t i
  rw [hempty]
  exact Finset.notMem_empty t

private theorem actual_cutoff_run_record_date
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hat : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (hrun : actualCutoffRun rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e =
        seg.records)
    (a : Fin (actualCutoffRun rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e).length) :
    ((actualCutoffRun rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e).get a).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + a.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let K := actualCutoffRun rate R e
  have hrun' : K = seg.records := hrun
  let a' : Fin seg.records.length := ⟨a.val, hrun' ▸ a.isLt⟩
  have hrecord : K.get a = seg.records.get a' := by
    simpa only [a'] using List.get_of_eq hrun' a
  have hcalendar := ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
    rate rewards C_star C_h z e.val seg hat hne hcut
  have hday := (hcalendar a').2.1
  have hrecordElem : K.get a = seg.records[a'.val]'a'.isLt := by
    simpa only [List.get_eq_getElem] using hrecord
  rw [← hrecordElem] at hday
  change (K.get a).input.time.val + 1 = _ at hday
  have haVal : a'.val = a.val := rfl
  rw [haVal] at hday
  change (K.get a).input.time.val + 1 =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + a.val + 1 at hday
  exact Nat.add_right_cancel hday

/-- Every original-source calendar prefix has nonnegative actual kth-C
readout and total mass at most the composite quota `4Q`. -/
public theorem kthCSourceReadout_prefix_bounds
    (k : Fin (p.T + 1)) (v : ℕ) (i : Fin (p.m - 1)) :
    0 ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCSourceReadout rate rewards C_star C_h k t i z ∧
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCSourceReadout rate rewards C_star C_h k t i z) ≤
        4 * (AffineBatchDecoder.quota p : ℝ) := by
  have hnonneg := kthCSourceReadout_prefix_nonneg rate rewards C_star C_h z k v i
  obtain ⟨hemptyDates, _hzeroOld⟩ | ⟨e, registers, owned, base, outcome, seg, hdate, _hstate,
      houtput, hcutout, hat, hentry, _hpayload, hrun, _hprojection,
      _hnodup, _hnot, _hboundary, _hframes, htransportOld⟩ :=
    ReferenceOriginalKthCollectionCutoffAlignment.kthCDates_empty_or_actual_cutoff_alignment
      rate rewards C_star C_h z k
  · refine ⟨hnonneg, ?_⟩
    have hzero : ∀ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
        kthCSourceReadout rate rewards C_star C_h k t i z = 0 := by
      intro t _ht
      unfold kthCSourceReadout
      rw [ReferenceOriginalKthCollectionCutoffAlignment.kthCOLDReadout_zero_of_empty
        rate rewards C_star C_h z k hemptyDates t i,
        kthCFORMEDReadout_zero_of_empty rate rewards C_star C_h z k hemptyDates t i]
      simp
    rw [Finset.sum_eq_zero hzero]
    positivity
  · let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
      rw [hentry]
      have hp : (ReferenceActivePhysicalStep.prepare (R[e.val]'e.isLt).input).coordinator =
          .live registers owned base outcome := by
        have hstep := congrArg
          (fun o : ReferenceActivePhysicalStep.RoundOutput (R[e.val]'e.isLt).input =>
            o.preparation.coordinator) (R[e.val]'e.isLt).output_eq
        exact hstep.symm.trans houtput
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [hp]
      cases outcome <;> simp_all
    have hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T := by
      rw [hdate]
      have hsource := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z e
      have ht := (R[e.val]'e.isLt).input.time.isLt
      change (R[e.val]'e.isLt).input.time.val + 1 =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1 at hsource
      omega
    have hne : seg.records ≠ [] := by
      have hK : actualCutoffRun rate R e ≠ [] := by simp [actualCutoffRun]
      intro hnil
      exact hK (hrun.trans hnil)
    let K := actualCutoffRun rate R e
    let j := v - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val)
    let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
    have hreadForm := actual_cutoff_formed_up_prefix_transport
      rate rewards C_star C_h z k hk e seg hdate hat hne hcut v i
    have htransportOld' := htransportOld
    have hreadOld :
        (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
          kthCOLDReadout rate rewards C_star C_h k t i z) =
        actualOldDownPrefixReadoutSum rate rewards C_star C_h z K j beta i := by
      simpa only [K, j, beta, R] using htransportOld' v i
    have hsum :
        (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
          kthCSourceReadout rate rewards C_star C_h k t i z) =
        actualOldDownPrefixReadoutSum rate rewards C_star C_h z K j beta i +
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K j beta i := by
      unfold kthCSourceReadout
      rw [Finset.sum_add_distrib, hreadOld, hreadForm]
    refine ⟨hnonneg, ?_⟩
    cases outcome with
    | continuingChosen dispatched hstart continuation selected => simp at hcutout
    | clockFailure failure hfailure => simp at hcutout
    | initializerFailure dispatched hstart checked hfailure => simp at hcutout
    | localFailure dispatched hstart failure => simp at hcutout
    | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selected =>
      have hquotaOld := ReferenceOriginalCollectionOldDownCanonicalQuota.actual_old_down_canonical_quota
        rate rewards C_star C_h z e i
      have hquotaForm := actual_cutoff_formed_up_canonical_quota
        rate rewards C_star C_h z e i
      dsimp only [R] at hquotaOld hquotaForm
      simp only [List.getElem?_eq_getElem e.isLt] at hquotaOld hquotaForm
      rw [houtput] at hquotaOld hquotaForm
      dsimp only at hquotaOld hquotaForm
      rcases hquotaOld with ⟨hOldAll, _⟩
      rcases hquotaForm with ⟨hFormAll, _⟩
      have hOldBound :
          actualOldDownPrefixReadoutSum rate rewards C_star C_h z K j beta i ≤
            2 * (AffineBatchDecoder.quota p : ℝ) := by
        simpa only [K, j, beta, R, actualCutoffRun] using (hOldAll j).2
      have hFormBound :
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K j beta i ≤
            2 * (AffineBatchDecoder.quota p : ℝ) := by
        have h := (hFormAll j).2.2
        have h' : actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K j beta i ≤
            (2 * AffineBatchDecoder.quota p : ℕ) := by
          simpa only [K, j, beta, R, actualCutoffRun] using h
        exact_mod_cast h'
      rw [hsum]
      linarith

/-- At every actual kth-C date, the source readout on the strict incoming
calendar past is strictly below `4Q`, using that same actual prechoice's
pending membership. -/
public theorem kthCSourceReadout_prechoice_prefix_lt
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (ht : t ∈ kthCDates rate rewards C_star C_h z k)
    (d : KthCPrechoiceData rate)
    (hd : kthCPrechoiceData rate rewards C_star C_h t z = some d)
    (hip : i ∈ d.2.1) :
    (∑ s ∈ Finset.univ.filter (fun s : Fin p.T => s.val < t.val),
      kthCSourceReadout rate rewards C_star C_h k s i z) <
        4 * (AffineBatchDecoder.quota p : ℝ) := by
  obtain ⟨hemptyDates, _hzeroOld⟩ | ⟨e, registers, owned, base, outcome, seg, hdate,
      _hstate, houtput, hcutout, hat, hentry, _hpayload, hrun, hprojection,
      _hnodup, _hnot, _hboundary, hframes, htransportOld⟩ :=
    ReferenceOriginalKthCollectionCutoffAlignment.kthCDates_empty_or_actual_cutoff_alignment
      rate rewards C_star C_h z k
  · rw [hemptyDates] at ht
    exact False.elim (Finset.notMem_empty t ht)
  · let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let K := actualCutoffRun rate R e
    let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
    have hdateMember : t ∈ actualCutoffChoiceDates rate K beta := by
      rw [← hprojection]
      exact ht
    obtain ⟨r, hrK, _hcBool, hgate, htime⟩ :=
      (mem_actualCutoffChoiceDates_iff rate K beta t).mp hdateMember
    obtain ⟨an, han, har⟩ := List.mem_iff_getElem.mp hrK
    let a : Fin K.length := ⟨an, han⟩
    have hKa : K.get a = r := by
      change K[an] = r
      exact har
    obtain ⟨j, c, selected, data, _hlo, _hhi, _hrecord, _hsourceDate,
      hlookup, hchoice, _hpayload, _hselected, _hselectedPayload, _hselectedPending,
      hpreFrame, _hdataPayload, hdataPending, _hdataCutoff, _hframe⟩ := hframes r hrK
    have hpreFrameAtT : kthCPrechoiceData rate rewards C_star C_h t z = some data := by
      simpa only [htime] using hpreFrame
    have hdataEq : data = d := Option.some.inj (hpreFrameAtT.symm.trans hd)
    have hpendingEq : d.2.1 = c.preLedger.pending := by
      rw [← hdataEq]
      exact hdataPending
    have hipC : i ∈ c.preLedger.pending := by
      rw [hpendingEq] at hip
      exact hip
    have hchoiceA :
        ReferenceCollectionSegmentExtraction.choice (K.get a).input = some c := by
      calc
        ReferenceCollectionSegmentExtraction.choice (K.get a).input =
            ReferenceCollectionSegmentExtraction.choice r.input := by rw [hKa]
        _ = some c := hchoice
    have hdateA : (K.get a).input.time.val + 1 ≤ beta := by
      have htimeVal : r.input.time.val = t.val := congrArg Fin.val htime
      rw [hKa]
      omega
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
      rw [hentry]
      have hp : (ReferenceActivePhysicalStep.prepare (R[e.val]'e.isLt).input).coordinator =
          .live registers owned base outcome := by
        have hstep := congrArg
          (fun o : ReferenceActivePhysicalStep.RoundOutput (R[e.val]'e.isLt).input =>
            o.preparation.coordinator) (R[e.val]'e.isLt).output_eq
        exact hstep.symm.trans houtput
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [hp]
      cases outcome <;> simp_all
    have hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T := by
      rw [hdate]
      have hsource := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z e
      have htFin := (R[e.val]'e.isLt).input.time.isLt
      change (R[e.val]'e.isLt).input.time.val + 1 =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1 at hsource
      omega
    have hne : seg.records ≠ [] := by
      have hK : actualCutoffRun rate R e ≠ [] := by simp [actualCutoffRun]
      intro hnil
      exact hK (hrun.trans hnil)
    have hreadForm := actual_cutoff_formed_up_prefix_transport
      rate rewards C_star C_h z k hk e seg hdate hat hne hcut t.val i
    have hOldPast := htransportOld t.val i
    have hlocal : t.val -
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val) =
        a.val := by
      have htimeA' := actual_cutoff_run_record_date rate rewards C_star C_h z
        e seg hat hne hcut hrun a
      have htimeA : (K.get a).input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + a.val := by
        simpa only [K, R] using htimeA'
      have htimeVal : r.input.time.val = t.val := congrArg Fin.val htime
      have htimeEq : (K.get a).input.time.val = t.val := by
        rw [hKa]
        exact htimeVal
      omega
    rw [hlocal] at hOldPast hreadForm
    have hsourcePast :
        (∑ s ∈ Finset.univ.filter (fun s : Fin p.T => s.val < t.val),
          kthCSourceReadout rate rewards C_star C_h k s i z) =
        actualOldDownPrefixReadoutSum rate rewards C_star C_h z K a.val beta i +
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K a.val beta i := by
      unfold kthCSourceReadout
      rw [Finset.sum_add_distrib, hOldPast, hreadForm]
    cases outcome with
    | continuingChosen dispatched hstart continuation selected => simp at hcutout
    | clockFailure failure hfailure => simp at hcutout
    | initializerFailure dispatched hstart checked hfailure => simp at hcutout
    | localFailure dispatched hstart failure => simp at hcutout
    | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection =>
      have hcounts := actual_cutoff_pending_pre_count_lt
        rate rewards C_star C_h z e.val i
      have hreads := actual_cutoff_formed_up_readout_eq_count
        rate rewards C_star C_h z e.val a.val i
      have hquotaOld := ReferenceOriginalCollectionOldDownCanonicalQuota.actual_old_down_canonical_quota
        rate rewards C_star C_h z e.val i
      dsimp only [R] at hcounts hreads hquotaOld
      simp only [List.getElem?_eq_getElem e.isLt] at hcounts hreads hquotaOld
      rw [houtput] at hcounts hreads hquotaOld
      dsimp only at hcounts hreads hquotaOld
      have hcount := hcounts a c hchoiceA hipC hdateA
      have htimeAt : ∀ b : Fin K.length,
          (K.get b).input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + b.val := by
        intro b
        exact actual_cutoff_run_record_date rate rewards C_star C_h z
          e seg hat hne hcut hrun b
      have htakeAll : ∀ r ∈ K.take a.val,
          (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
        intro r hr
        obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
        have hbK : b < K.length := (lt_min_iff.mp hb).2
        have hba : b < a.val := (lt_min_iff.mp hb).1
        have htimeB := htimeAt ⟨b, hbK⟩
        have htimeA := htimeAt a
        have hbr' : K.get ⟨b, hbK⟩ = r := by
          change K[b] = r at hbr
          simpa only [List.get_eq_getElem] using hbr
        have htimeR : r.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + b := by
          calc
            r.input.time.val = (K.get ⟨b, hbK⟩).input.time.val := by rw [hbr']
            _ = _ := htimeB
        apply decide_eq_true
        rw [htimeR]
        omega
      have hL : actualOldDownPrefixLength rate K a.val beta = a.val := by
        unfold actualOldDownPrefixLength
        rw [(List.takeWhile_eq_self_iff).mpr htakeAll]
        exact List.length_take_of_le (Nat.le_of_lt a.isLt)
      have hformedRead := hreads
      change actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K a.val beta i =
        ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
          (K.take (actualOldDownPrefixLength rate K a.val beta)) i
          (registers.payload.downRecord i)).length : ℝ) at hformedRead
      rw [hL] at hformedRead
      have hformedStrict :
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h z K a.val beta i <
            2 * (AffineBatchDecoder.quota p : ℝ) := by
        rw [hformedRead]
        exact_mod_cast hcount
      rcases hquotaOld with ⟨hOldAll, _⟩
      have hOldBound :
          actualOldDownPrefixReadoutSum rate rewards C_star C_h z K a.val beta i ≤
            2 * (AffineBatchDecoder.quota p : ℝ) := by
        simpa only [K, beta, R, actualCutoffRun] using (hOldAll a.val).2
      rw [hsourcePast]
      linarith

end Bandits.Support.ReferenceOriginalKthCollectionCompositeQuota

end
