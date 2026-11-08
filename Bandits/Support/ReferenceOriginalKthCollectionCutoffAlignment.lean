/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCollectionOldDownPendingPrefix
public import Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals
public import Bandits.Support.ReferenceOriginalStoppedTransferSignedReindex

import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-!
# Original kth C dates and cutoff alignment

This module intersects the original ranked transfer window with the actual
stopped collection-choice dates.  Cutoff runs below are projections of the
complete physical suffix, retaining the actual source records and payload.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover
open Bandits.Support.ReferenceOriginalStoppedTransferSignedReindex
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

/-- Original calendar dates in the kth actual stopped C interval. -/
public def kthCDates (k : Fin (p.T + 1)) : Finset (Fin p.T) :=
  ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k ∩
    ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
      rate rewards C_star C_h z

/-- The untruncated actual cutoff run in the complete original suffix. -/
public def actualCutoffRun
    (R : List (Record rate)) (e : Fin R.length) : List (Record rate) :=
  R[e.val] :: (R.drop (e.val + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)

/-- Canonical finite date projection of actual collection-choice records in
an entire cutoff run, gated by the inclusive first-bad date. -/
public def actualCutoffChoiceDates
    (K : List (Record rate)) (beta : ℕ) : Finset (Fin p.T) :=
  (((K.filter fun r =>
      (ReferenceCollectionSegmentExtraction.choice r.input).isSome = true ∧
        r.input.time.val + 1 ≤ beta).map fun r => r.input.time).toFinset)

/-- The actual cutoff run is exactly the no-later-choice prefix of the
complete suffix beginning at its original record index. -/
public theorem actualCutoffRun_eq_suffix_prefix
    (R : List (Record rate)) (e : Fin R.length)
    (hcut : ReferenceCollectionPhaseHistory.laterChosen
      (R[e.val]'e.isLt).input = false) :
    actualCutoffRun rate R e =
      (R.drop e.val).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
  unfold actualCutoffRun
  rw [List.drop_eq_getElem_cons e.isLt, List.takeWhile_cons]
  simp only [hcut, Bool.not_false, ↓reduceIte]

/-- Membership in the canonical date projection is witnessed by an actual
choice record in the unchanged cutoff run, with its inclusive bad-date gate. -/
public theorem mem_actualCutoffChoiceDates_iff
    (K : List (Record rate)) (beta : ℕ) (t : Fin p.T) :
    t ∈ actualCutoffChoiceDates rate K beta ↔
      ∃ r : Record rate, r ∈ K ∧
        (ReferenceCollectionSegmentExtraction.choice r.input).isSome = true ∧
        r.input.time.val + 1 ≤ beta ∧ r.input.time = t := by
  classical
  simp only [actualCutoffChoiceDates, List.mem_toFinset,
    List.mem_map, List.mem_filter, decide_eq_true_eq, and_assoc]

/-- Membership keeps the source ranked window and the exact source record
index used by the actual collection-date image. -/
public theorem mem_kthCDates_iff (k : Fin (p.T + 1)) (t : Fin p.T) :
    t ∈ kthCDates rate rewards C_star C_h z k ↔
      t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
          rate rewards C_star C_h z k ∧
        ∃ j : Fin (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
            rate rewards C_star C_h z).length,
          j ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseIndices
              rate rewards C_star C_h z ∧
            (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
              rate rewards C_star C_h z)[j.val].input.time = t := by
  classical
  simp only [kthCDates, Finset.mem_inter,
    ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates]
  rw [Finset.mem_image]

/-- The image source is the actual original record index with the inclusive
first-bad gate and actual collection-choice predicate. -/
public theorem mem_collectionPhaseIndices_iff
    (j : Fin (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
      rate rewards C_star C_h z).length) :
    j ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseIndices
        rate rewards C_star C_h z ↔
      ReferenceOriginalCalendarTransferPhaseCover.retainedByFirstBadDate
          rate rewards C_star C_h z j ∧
        ReferenceOriginalCalendarTransferPhaseCover.actualCollectionChoice rate
          ((ReferenceOriginalCalendarTransferPhaseCover.actualRecords
            rate rewards C_star C_h z)[j.val]) := by
  simp only [ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- An absent original ranked start has no dates in the intersected kth C
set. -/
public theorem kthCDates_empty_of_absent (k : Fin (p.T + 1))
    (hk : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    kthCDates rate rewards C_star C_h z k = ∅ := by
  have hwindow := ReferenceOriginalStoppedTransferSignedReindex.absent_ranked_window_empty
    rate rewards C_star C_h z k hk
  ext t
  simp [kthCDates, hwindow]

/-- The genuine launch rank has no actual C choice, as witnessed by the raw
initial transfer window on the same complete physical suffix. -/
public theorem kthCDates_empty_at_initial_rank (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1) :
    kthCDates rate rewards C_star C_h z k = ∅ := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
    rate rewards C_star C_h z
  let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rate rewards C_star C_h k z
  obtain ⟨_hWpos, _hE, hclip, hglobal,
      ⟨_newPayload, _hpayload, hfields, hCempty, _hH, _hR, _hboundary, _hrelease⟩⟩ :=
    ReferenceOriginalStoppedTransferPhaseIntervals.initial_rank_stopped_transfer_phase_intervals
      rate rewards C_star C_h k z hk hstart
  ext t
  constructor
  · intro ht
    obtain ⟨hwindow, ⟨j, ⟨hphase, htime⟩⟩⟩ :=
      (mem_kthCDates_iff rate rewards C_star C_h z k t).mp ht
    obtain ⟨_, ⟨_hstartDate, hstopDate⟩⟩ := Finset.mem_filter.mp hwindow
    obtain ⟨⟨_hlaunch, hbad⟩, hchoice⟩ :=
      (mem_collectionPhaseIndices_iff rate rewards C_star C_h z j).mp hphase
    rcases hchoice with ⟨c, hc⟩
    have hjR : j.val < R.length := by
      simpa [R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using j.isLt
    let jR : Fin R.length := ⟨j.val, hjR⟩
    have htimeR : R[jR.val].input.time = t := by
      simpa [R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using htime
    have hrecordBefore : R[jR.val].input.time.val + 1 < E := by
      rw [htimeR]
      exact hstopDate
    have hbefore : j.val < W.length := by
      have h := (hglobal jR).mp hrecordBefore
      exact h.1
    let wj : Fin W.length := ⟨j.val, hbefore⟩
    have hrecord : R[jR.val] = W[wj.val] := by
      have hs : R[jR.val]? = some W[wj.val] := by
        simpa [R, W, jR, wj,
          ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using (hfields wj).1
      rw [List.getElem?_eq_getElem jR.isLt] at hs
      exact Option.some.inj hs
    have hdate : W[wj.val].input.time.val + 1 = t.val + 1 := by
      rw [← hrecord, htimeR]
    have hchoiceW : ReferenceCollectionSegmentExtraction.choice W[wj.val].input = some c := by
      rw [← hrecord]
      simpa [R, ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using hc
    exact (hCempty (t.val + 1) ⟨wj, c, hchoiceW, hdate, hstopDate⟩).elim
  · intro hfalse
    simp at hfalse

private theorem laterChosen_false_of_cutoff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ReferenceCollectionPhaseHistory.laterChosen x = false := by
  cases hprep : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      cases outcome <;>
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceCollectionPhaseHistory.laterChosen, hprep] at hcut ⊢
  | first outcome =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        hprep] at hcut
  | collection payload ledger clock cutoff outcome =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        hprep] at hcut
  | invalidCollectionCutoff =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        hprep] at hcut
  | dagger =>
      simp [ReferenceCollectionPhaseHistory.cutoffChosen,
        hprep] at hcut

private theorem actualCutoffRun_eq_segment_records
    (R : List (Record rate)) (e : Fin R.length)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hentry : seg.entry = R[e.val])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (hpartition : seg.records ++ seg.remaining = R.drop e.val)
    (hcalendar : ∀ j : Fin seg.records.length,
      ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice seg.records[j.val].input = some c)
    (hboundary : e.val + seg.records.length = R.length ∨
      ∃ b : Fin R.length,
        b.val = e.val + seg.records.length ∧
        ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
        R.drop b.val = seg.remaining) :
    actualCutoffRun rate R e = seg.records := by
  have hcutR : ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true := by
    simpa only [hentry] using hcut
  have hnotR := laterChosen_false_of_cutoff rate R[e.val].input hcutR
  have hprefix : ∀ r ∈ seg.records,
      (!ReferenceCollectionPhaseHistory.laterChosen r.input) = true := by
    intro r hr
    obtain ⟨n, hn, hrecord⟩ := List.mem_iff_getElem.mp hr
    let j : Fin seg.records.length := ⟨n, hn⟩
    obtain ⟨c, hc⟩ := hcalendar j
    have hc' : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
      rw [← hrecord]
      exact hc
    have hnot : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
      cases hlater : ReferenceCollectionPhaseHistory.laterChosen r.input with
      | false => rfl
      | true =>
          have hnone := ReferenceOriginalTransferPhysicalIntervals.actual_laterChosen_not_collection_choice
            r hlater
          rw [hc'] at hnone
          cases hnone
    simp [hnot]
  rw [actualCutoffRun_eq_suffix_prefix rate R e hnotR]
  rw [← hpartition]
  rcases hboundary with hterminal | ⟨b, hb, hlater, hdrop⟩
  · have hlen : seg.records.length + seg.remaining.length = R.length - e.val := by
      have h := congrArg List.length hpartition
      simpa only [List.length_append, List.length_drop] using h
    have hrem : seg.remaining = [] := by
      cases hxs : seg.remaining with
      | nil => rfl
      | cons head tail =>
          simp only [hxs, List.length_cons] at hlen
          omega
    simpa [hrem] using (List.takeWhile_eq_self_iff.mpr hprefix)
  · rw [← hdrop, List.takeWhile_append_of_pos hprefix]
    have htail : (R.drop b.val).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) = [] := by
      rw [List.drop_eq_getElem_cons b.isLt, List.takeWhile_cons, hlater]
      rfl
    simp only [htail, List.append_nil]

private theorem segment_records_not_laterChosen
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hcalendar : ∀ j : Fin seg.records.length,
      ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice seg.records[j.val].input = some c) :
    ∀ r ∈ seg.records,
      ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
  intro r hr
  obtain ⟨n, hn, hrecord⟩ := List.mem_iff_getElem.mp hr
  let j : Fin seg.records.length := ⟨n, hn⟩
  obtain ⟨c, hc⟩ := hcalendar j
  have hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
    rw [← hrecord]
    exact hc
  cases hlater : ReferenceCollectionPhaseHistory.laterChosen r.input with
  | false => rfl
  | true =>
      have hnone := ReferenceOriginalTransferPhysicalIntervals.actual_laterChosen_not_collection_choice
        r hlater
      rw [hchoice] at hnone
      cases hnone

private theorem actual_launch_le_record
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

private theorem segment_date_projection
    (k : Fin (p.T + 1))
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (seg : Segment rate) (rawEnd : ℕ)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hcalendar : ∀ j : Fin seg.records.length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[e.val + j.val]? = some seg.records[j.val] ∧
      seg.records[j.val].input.time.val + 1 =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + j.val + 1 ∧
      ∃ c : Choice rate, choice seg.records[j.val].input = some c)
    (hend : e.val + seg.records.length ≤ rawEnd)
    (hE : ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
        rate rewards C_star C_h k z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        min rawEnd (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) + 1)
    (hno : ∀ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      e.val + seg.records.length ≤ j.val → j.val < rawEnd →
        choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input = none) :
    kthCDates rate rewards C_star C_h z k = actualCutoffChoiceDates rate seg.records
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rate rewards C_star C_h k z
  have hE' : E = s + min rawEnd (min beta p.T - s) + 1 := hE
  ext t
  constructor
  · intro ht
    obtain ⟨hw, j, hj, htime⟩ := (mem_kthCDates_iff rate rewards C_star C_h z k t).mp ht
    obtain ⟨_, hleft, hright⟩ := Finset.mem_filter.mp hw
    obtain ⟨hret, c, hc⟩ := (mem_collectionPhaseIndices_iff rate rewards C_star C_h z j).mp hj
    have hjR : j.val < R.length := j.isLt
    let jR : Fin R.length := ⟨j.val, hjR⟩
    have htimeR : R[jR.val].input.time = t := htime
    have hsource := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
      rate rewards C_star C_h z jR
    change R[jR.val].input.time.val + 1 = s + j.val + 1 at hsource
    rw [htimeR] at hsource
    have hleft' : e.val ≤ j.val := by change _ ≤ _ at hleft; rw [hdate] at hleft; omega
    have hright' : j.val < rawEnd := by change t.val + 1 < E at hright; omega
    have hlocal : j.val < e.val + seg.records.length := by
      by_contra hn
      have hnone := hno jR (by change e.val + seg.records.length ≤ j.val; omega) hright'
      have hc' : choice R[jR.val].input = some c := hc
      rw [hnone] at hc'
      cases hc'
    let a : Fin seg.records.length := ⟨j.val - e.val, by omega⟩
    obtain ⟨hslot, _hday, ca, hca⟩ := hcalendar a
    have hidx : e.val + a.val = j.val := by dsimp only [a]; omega
    rw [hidx, List.getElem?_eq_getElem jR.isLt] at hslot
    have hr : R[jR.val] = seg.records[a.val] := Option.some.inj hslot
    apply (mem_actualCutoffChoiceDates_iff rate seg.records beta t).mpr
    refine ⟨seg.records[a.val], List.getElem_mem a.isLt, ?_, ?_, ?_⟩
    · rw [hca]; rfl
    · have hb := hret.2
      change R[jR.val].input.time.val + 1 ≤ min beta p.T at hb
      rw [hr] at hb
      omega
    · rw [← hr]; exact htimeR
  · intro ht
    obtain ⟨r, hr, _hc, hb, htime⟩ :=
      (mem_actualCutoffChoiceDates_iff rate seg.records beta t).mp ht
    obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
    let aF : Fin seg.records.length := ⟨a, ha⟩
    obtain ⟨hslot, hday, c, hc⟩ := hcalendar aF
    have hslot' := List.getElem?_eq_some_iff.mp hslot
    let j : Fin R.length := ⟨e.val + a, hslot'.1⟩
    have hrecord : R[j.val] = r := hslot'.2.trans har
    have hday' : t.val + 1 = s + e.val + a + 1 := by
      simpa only [aF, har, htime] using hday
    have htT := t.isLt
    have hstop : t.val + 1 < E := by omega
    apply (mem_kthCDates_iff rate rewards C_star C_h z k t).mpr
    refine ⟨?_, j, ?_, ?_⟩
    · simp only [kthStoppedTransferWindowDates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨by rw [hdate]; change s + e.val + 1 ≤ t.val + 1; omega, hstop⟩
    · apply (mem_collectionPhaseIndices_iff rate rewards C_star C_h z j).mpr
      constructor
      · change ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
            rate rewards C_star C_h z ≤ R[j.val].input.time.val + 1 ∧
          R[j.val].input.time.val + 1 ≤ min beta p.T
        refine ⟨actual_launch_le_record rate rewards C_star C_h z j, ?_⟩
        rw [hrecord, htime]
        omega
      · refine ⟨c, ?_⟩
        change choice R[j.val].input = some c
        rw [hrecord, ← har]
        exact hc
    · change R[j.val].input.time = t
      rw [hrecord, htime]

/-- The C projection uses the same original segment and inclusive cutoff;
physical play after the analytic gate remains in the segment. -/
public theorem kthCDates_eq_actual_segment_dates
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (seg : Segment rate)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e.val = some seg) :
    kthCDates rate rewards C_star C_h z k = actualCutoffChoiceDates rate seg.records
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨e', hd', hbranch⟩ :=
    ReferenceOriginalStoppedTransferPhaseIntervals.present_stopped_transfer_collection_intervals
      rate rewards C_star C_h k z hk
  have heq : e' = e := by apply Fin.ext; omega
  subst e'
  rcases hbranch with hfirst | ⟨registers, owned, base, seg', _hstate, hat',
    _hentry, _hpayload, _hne, hcalendar, _hactual, _hCiff, hboundary⟩
  · have hseg := (ReferenceCollectionSegmentExtraction.segmentAt_branch R e.val seg hat).1
    rw [List.drop_eq_getElem_cons e.isLt] at hseg
    simp only [ReferenceCollectionSegmentExtraction.segment, hfirst.2.2,
      Option.map_none] at hseg
    cases hseg
  · have hseg : seg' = seg := Option.some.inj (hat'.symm.trans hat)
    subst seg'
    have hcal : ∀ j : Fin seg.records.length,
        R[e.val + j.val]? = some seg.records[j.val] ∧
        seg.records[j.val].input.time.val + 1 =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
            e.val + j.val + 1 ∧ ∃ c : Choice rate, choice seg.records[j.val].input = some c := by
      intro j
      obtain ⟨hr, hd, c, hc, _⟩ := hcalendar j
      exact ⟨hr, hd, c, hc⟩
    rcases hboundary with hterminal | ⟨b, hb, _hlater, _hexit, _hstate,
      _hempty, hlen, hE, _hclip, _hglobal, newPayload, _hbirth, hfields, _rest⟩
    · exact segment_date_projection rate rewards C_star C_h z k e seg R.length hdate
        hcal (by
          have ht : e.val + seg.records.length = R.length := hterminal.1
          exact ht.le)
        hterminal.2.1 (by
          intro j hj
          have ht : e.val + seg.records.length = R.length := hterminal.1
          have := j.isLt
          change _ ≤ j.val at hj
          omega)
    · let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      apply segment_date_projection rate rewards C_star C_h z k e seg (b.val + V.length)
        hdate hcal (by omega) hE
      intro j hj hjend
      let a : Fin V.length := ⟨j.val - b.val, by omega⟩
      obtain ⟨hr, _hd, hc, _⟩ := hfields a
      have hidx : b.val + a.val = j.val := by dsimp only [a]; omega
      rw [hidx, List.getElem?_eq_getElem j.isLt] at hr
      rw [Option.some.inj hr]
      exact hc

/-- Every original rank is geometrically empty or starts at its actual
cutoff record.  The cutoff branch carries the same payload, physical source
indices, and the actual terminal or later-installation boundary. -/
public theorem kthCDates_empty_or_actual_cutoff_segment (k : Fin (p.T + 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    kthCDates rate rewards C_star C_h z k = ∅ ∨
      ∃ e : Fin R.length,
        ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
            ∃ base : Fin (p.m - 1) → ℕ,
              ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
                ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
                    rate rewards C_star C_h k z =
                  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1 ∧
                R[e.val].input.state.coordinator = .live registers owned base ∧
                ReferenceCollectionSegmentExtraction.segmentAt R e.val = some seg ∧
                seg.entry = R[e.val] ∧ seg.records ≠ [] ∧
                ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
                seg.context.payload = registers.payload ∧
                (∀ j : Fin seg.records.length,
                  R[e.val + j.val]? = some seg.records[j.val] ∧
                  seg.records[j.val].input.time.val + 1 =
                    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
                      e.val + j.val + 1 ∧
                  ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
                    ReferenceCollectionSegmentExtraction.choice seg.records[j.val].input = some c ∧
                      c.payload = registers.payload) ∧
                kthCDates rate rewards C_star C_h z k =
                  actualCutoffChoiceDates rate (actualCutoffRun rate R e)
                    (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
                      rate rewards C_star C_h z) ∧
                actualCutoffRun rate R e = seg.records ∧
                (∀ r ∈ actualCutoffRun rate R e,
                  ReferenceCollectionPhaseHistory.laterChosen r.input = false) ∧
                (e.val + seg.records.length = R.length ∨
                  ∃ b : Fin R.length,
                    b.val = e.val + seg.records.length ∧
                    ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
                    seg.exit = .laterChosen R[b.val] ∧
                    R.drop b.val = seg.remaining) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  by_cases hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T
  · obtain ⟨i, hdate, hbranch⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.present_start_original_collection_interval
        rate rewards C_star C_h k z hk
    rcases hbranch with hfirst | ⟨registers, owned, base, seg, hstate,
      hsegment, hentry, hne, hcut, hpayload, _hinitializer, _hpartition,
      _hchoiceiff, _hnostart, hcalendar, hboundary⟩
    · obtain ⟨hi, _hstate, _hchoice⟩ := hfirst
      have hinitial :
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
        rw [hdate, hi]
      exact Or.inl (kthCDates_empty_at_initial_rank rate rewards C_star C_h z k hk hinitial)
    · right
      have hchoices : ∀ j : Fin seg.records.length,
          ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
            ReferenceCollectionSegmentExtraction.choice seg.records[j.val].input = some c := by
        intro j
        obtain ⟨_, _, c, hc, _⟩ := hcalendar j
        exact ⟨c, hc⟩
      rcases hboundary with hterminal | ⟨b, hb, hlater, _hexit, _hdrop, _hstate,
        _saved, _hempty, _W, _hchoices, _newPayload, _hbirth, _hfields, _hclear, _hnested⟩
      · have hcalendar' : ∀ j : Fin seg.records.length,
            ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
              ReferenceCollectionSegmentExtraction.choice seg.records[j.val].input = some c := hchoices
        have hrun := actualCutoffRun_eq_segment_records rate R i seg hentry hcut
          _hpartition hcalendar' (Or.inl hterminal)
        have hnotRun : ∀ r ∈ actualCutoffRun rate R i,
            ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
          intro r hr
          rw [hrun] at hr
          exact segment_records_not_laterChosen rate seg hchoices r hr
        exact ⟨i, registers, owned, base, seg, hdate, hstate, hsegment,
          hentry, hne, hcut, hpayload, hcalendar,
          (by
            rw [hrun]
            exact kthCDates_eq_actual_segment_dates
              rate rewards C_star C_h z k hk i seg hdate hsegment),
          hrun, hnotRun, Or.inl hterminal⟩
      · exact ⟨i, registers, owned, base, seg, hdate, hstate, hsegment,
          hentry, hne, hcut, hpayload, hcalendar,
          (by
            rw [actualCutoffRun_eq_segment_records rate R i seg hentry hcut _hpartition
              hchoices (Or.inr ⟨b, hb, hlater, _hdrop⟩)]
            exact kthCDates_eq_actual_segment_dates
              rate rewards C_star C_h z k hk i seg hdate hsegment),
          actualCutoffRun_eq_segment_records rate R i seg hentry hcut _hpartition
            hchoices
            (Or.inr ⟨b, hb, hlater, _hdrop⟩),
          (by
            intro r hr
            rw [actualCutoffRun_eq_segment_records rate R i seg hentry hcut
              _hpartition hchoices (Or.inr ⟨b, hb, hlater, _hdrop⟩)] at hr
            exact segment_records_not_laterChosen rate seg hchoices r hr),
          Or.inr ⟨b, hb, hlater, _hexit, _hdrop⟩⟩
  · exact Or.inl (kthCDates_empty_of_absent rate rewards C_star C_h z k hk)

open ReferenceOriginalKthCollectionSourceSections

/-- The original stratum and the signed-window endpoint use the same next
rank and inclusive first-bad date. -/
public theorem kthCStratum_iff_mem_window (k : Fin (p.T + 1)) (t : Fin p.T) :
    kthCStratum rate rewards C_star C_h k t z ↔
      t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k := by
  have hnext : kthNextStoppedStartDate rate rewards C_star C_h k z =
      ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
        rate rewards C_star C_h k z := by
    unfold kthNextStoppedStartDate
    split
    · rfl
    next hn =>
      have hlen : (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList
          rate rewards C_star C_h z).length ≤ p.T := by
        rw [ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_length]
        exact ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_card_le_horizon
          rate rewards C_star C_h z
      symm
      apply List.getD_eq_default
      omega
  simp only [kthCStratum, hnext, kthStoppedTransferWindowDates,
    ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate,
    Finset.mem_filter, Finset.mem_univ, true_and, lt_min_iff]
  have ht := t.isLt
  omega

private theorem prechoice_some_actual_choice
    (t : Fin p.T) (data : KthCPrechoiceData rate)
    (hd : kthCPrechoiceData rate rewards C_star C_h t z = some data) :
    ∃ (r : Record rate) (c : Choice rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧ choice r.input = some c := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp only [kthCPrechoiceData, ReferenceSourcePrefixHistoryFiltration.incoming,
        hr, Option.map_none, Option.bind_none] at hd
      cases hd
  | some r =>
      have hcode := kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr
      have hsome : choice r.input ≠ none := by
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

private theorem old_mask_supported
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (hold : z ∈ kthCOLDSet rate rewards C_star C_h k t i) :
    t ∈ kthCDates rate rewards C_star C_h z k := by
  obtain ⟨hs, pending, _hi, hstage⟩ := hold
  obtain ⟨data, hdata, _hvalue⟩ := Option.map_eq_some_iff.mp hstage
  obtain ⟨r, c, hr, hc⟩ := prechoice_some_actual_choice
    rate rewards C_star C_h z t data hdata
  have hlookup := hr
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hlookup
  split at hlookup
  next hstart =>
    obtain ⟨hj, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
    let j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := ⟨t.val -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, hj⟩
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
        refine ⟨actual_launch_le_record rate rewards C_star C_h z j, ?_⟩
        change (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time.val + 1 ≤ _
        rw [hrecord, htime]
        exact Nat.le_min.mpr ⟨hs.2.2, by omega⟩
      · refine ⟨c, ?_⟩
        change choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input = some c
        rw [hrecord]
        exact hc
    · change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time = t
      rw [hrecord]
      exact htime
  · cases hlookup

/-- The literal OLD readout vanishes at every date outside the actual kth C
set, including all empty-rank branches. -/
public theorem kthCOLDReadout_eq_zero_of_not_mem
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (ht : t ∉ kthCDates rate rewards C_star C_h z k) :
    kthCOLDReadout rate rewards C_star C_h k t i z = 0 := by
  apply Set.indicator_of_notMem
  intro hold
  exact ht (old_mask_supported rate rewards C_star C_h z k t i hold)

/-- On a supported date the ranked mask keeps exactly the existing incoming
pending/OLD selector; the original reward readout is unchanged. -/
public theorem kthCOLDReadout_at_supported_date
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1))
    (ht : t ∈ kthCDates rate rewards C_star C_h z k) :
    kthCOLDReadout rate rewards C_star C_h k t i z =
      (if ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .old)
       then (1 : ℝ) else 0) *
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t z := by
  have hs := (kthCStratum_iff_mem_window rate rewards C_star C_h z k t).mpr
    (Finset.mem_inter.mp ht).1
  by_cases hm : ∃ pending, i ∈ pending ∧
      kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .old)
  · have hz : z ∈ kthCOLDSet rate rewards C_star C_h k t i := ⟨hs, hm⟩
    rw [kthCOLDReadout, Set.indicator_of_mem hz]
    simp only [hm, ite_true, one_mul]
  · have hz : z ∉ kthCOLDSet rate rewards C_star C_h k t i := fun h => hm h.2
    rw [kthCOLDReadout, Set.indicator_of_notMem hz]
    simp only [hm, ite_false, zero_mul]

/-- A geometrically empty C interval has identically zero OLD readouts. -/
public theorem kthCOLDReadout_zero_of_empty (k : Fin (p.T + 1))
    (hempty : kthCDates rate rewards C_star C_h z k = ∅)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    kthCOLDReadout rate rewards C_star C_h k t i z = 0 := by
  apply kthCOLDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k t i
  rw [hempty]
  exact Finset.notMem_empty t

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

private theorem old_readout_on_projected_record
    (k : Fin (p.T + 1)) (K : List (Record rate))
    (hprojection : kthCDates rate rewards C_star C_h z k =
      actualCutoffChoiceDates rate K
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z))
    (r : Record rate) (hr : r ∈ K)
    (hc : (choice r.input).isSome = true) (i : Fin (p.m - 1)) :
    kthCOLDReadout rate rewards C_star C_h k r.input.time i z =
      (if r.input.time.val + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
        then (1 : ℝ) else 0) *
      (if ∃ pending, i ∈ pending ∧
          kthCPrechoiceStage rate rewards C_star C_h r.input.time i z = some (pending, .old)
        then (1 : ℝ) else 0) *
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i r.input.time z := by
  by_cases hb : r.input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  · have ht : r.input.time ∈ kthCDates rate rewards C_star C_h z k := by
      rw [hprojection]
      exact (mem_actualCutoffChoiceDates_iff rate K _ _).mpr ⟨r, hr, hc, hb, rfl⟩
    rw [kthCOLDReadout_at_supported_date rate rewards C_star C_h z k r.input.time i ht]
    simp only [hb, ite_true, one_mul]
  · have ht : r.input.time ∉ kthCDates rate rewards C_star C_h z k := by
      rw [hprojection]
      intro ht
      obtain ⟨r', _hr', _hc', hb', ht'⟩ :=
        (mem_actualCutoffChoiceDates_iff rate K _ _).mp ht
      rw [ht'] at hb'
      exact hb hb'
    rw [kthCOLDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k r.input.time i ht]
    simp only [hb, ite_false, zero_mul]

private theorem old_prefix_transport
    (k : Fin (p.T + 1)) (K : List (Record rate)) (start : ℕ)
    (hd : ∀ a : Fin K.length, K[a.val].input.time.val = start + a.val)
    (hc : ∀ r ∈ K, (choice r.input).isSome = true)
    (hprojection : kthCDates rate rewards C_star C_h z k =
      actualCutoffChoiceDates rate K
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z))
    (v : ℕ) (i : Fin (p.m - 1)) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCOLDReadout rate rewards C_star C_h k t i z) =
      ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
        rate rewards C_star C_h z K (v - start)
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) i := by
  rw [calendar_prefix_sum_eq_take rate K start
    (fun t => kthCOLDReadout rate rewards C_star C_h k t i z) hd (by
      intro t hnone
      apply kthCOLDReadout_eq_zero_of_not_mem rate rewards C_star C_h z k t i
      rw [hprojection]
      intro ht
      obtain ⟨r, hr, _hc, _hb, hrt⟩ := (mem_actualCutoffChoiceDates_iff rate K _ _).mp ht
      exact hnone ⟨r, hr, hrt⟩) v]
  unfold ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
  rw [← List.take_eq_take_min]
  congr 1
  apply List.map_congr_left
  intro r hr
  have hrK : r ∈ K := List.mem_of_mem_take hr
  exact old_readout_on_projected_record rate rewards C_star C_h z k K hprojection
    r hrK (hc r hrK) i

private theorem choice_selected_pending
    (r : Record rate) (c : Choice rate) (hc : choice r.input = some c) :
    ∃ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = c.payload ∧
      selected.view.pendingAtChoice = c.preLedger.pending := by
  have hp : (prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]
    rfl
  unfold choice at hc
  split at hc
  · contradiction
  next hsome =>
    rw [hp] at hc hsome
    cases ho : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [ho, choiceOfCut] at hc
    | invalidCollectionCutoff => simp [ho, choiceOfCut] at hc
    | dagger => simp [ho, choiceOfCut] at hc
    | live registers owned base outcome =>
        cases outcome <;> simp only [ho, choiceOfCut] at hc
        all_goals try contradiction
        next dispatched _hstart ledger _hinit hledger _hdomains _hclock hpending _hno selected =>
          cases Option.some.inj hc
          simp only [DispatchCut.selection, selectionAt, dite_true]
          refine ⟨_, rfl, rfl, ?_⟩
          change dispatched.startResult.pending = (sharedLedger ledger).pending
          rw [hpending, hledger]
          rfl
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [ho, choiceOfCut] at hc
        all_goals try contradiction
        next core snapshot _hboundary _hscores =>
          cases Option.some.inj hc
          exact ⟨_, rfl, rfl, snapshot.clockStarted_frame.2.1⟩

/-- At an actual collection choice, both the physical selection and the
prechoice code carry the same payload and pending set. The two alternatives
retain the entire incoming ledger or the actual checked cutoff initializer. -/
public theorem actual_choice_pending_frame
    (t : Fin p.T) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (c : Choice rate) (hc : choice r.input = some c) :
    ∃ (selected : Selection r.input) (data : KthCPrechoiceData rate),
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = c.payload ∧
      selected.view.pendingAtChoice = c.preLedger.pending ∧
      kthCPrechoiceData rate rewards C_star C_h t z = some data ∧
      data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
      data.2.2.1 = c.preLedger.cutoff ∧
      ((∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ) (initializer : Initializer p),
          r.input.state.coordinator = .live registers owned base ∧
          c.initializer = some initializer ∧
          initializer.checkedStart rate = .success c.preLedger ∧
          c.preLedger.pending = Finset.univ) ∨
        ∃ (payload : Payload rate) (ledger : Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.input.state.coordinator = .collection payload ledger saved ∧
          c.preLedger = ledger ∧ c.initializer = none) := by
  obtain ⟨selected, hselected, hP, hpend⟩ := choice_selected_pending rate r c hc
  cases hs : r.input.state.coordinator with
  | first =>
      have hn := choice_first_none r.input hs
      rw [hn] at hc
      cases hc
  | dagger =>
      simp [choice, prepare, dispatch, hs, DispatchCut.selection] at hc
  | live registers owned base =>
      obtain ⟨data, hd, hdP, hdp, hdc, initializer, hi⟩ :=
        kthCPrechoiceData_actualLiveCollectionChoice
          rate rewards C_star C_h t z r hr registers owned base hs c hc
      have hreset : c.preLedger.pending = Finset.univ := by
        have hp := kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr
        rw [hp] at hd
        simp only [kthCPrechoiceDataFromCoordinatorCode,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs] at hd
        split at hd
        · have heq := Option.some.inj hd
          have heqp := congrArg (fun d : KthCPrechoiceData rate => d.2.1) heq
          exact hdp.symm.trans heqp.symm
        · cases hd
      exact ⟨selected, data, hselected, hP, hpend, hd, hdP, hdp, hdc,
        Or.inl ⟨registers, owned, base, initializer, rfl, hi,
          choice_initializer r.input c initializer hc hi, hreset⟩⟩
  | collection payload ledger saved =>
      have hnonempty : ledger.pending.Nonempty := by
        by_contra hn
        have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
        have hnone := (kthCPrechoiceData_emptyCollection_laterChosen
          rate rewards C_star C_h t z r hr payload ledger saved hs hempty).2.1
        rw [hnone] at hc
        cases hc
      obtain ⟨c', hc', _hP', _hp', _hcut', _hi', data, hd, hdP, hdp, hdc⟩ :=
        kthCPrechoiceData_actualCollectionChoice_nonempty
          rate rewards C_star C_h t z r hr payload ledger saved hs hnonempty
      have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst c'
      obtain ⟨hledger, hi⟩ := choice_collection_pre r.input payload ledger saved c hs hc
      exact ⟨selected, data, hselected, hP, hpend, hd, hdP, hdp, hdc,
        Or.inr ⟨payload, ledger, saved, rfl, hledger, hi⟩⟩

/-- The cutoff is the actual successful LIVE cutoff outcome, with the same
incoming registers and all of its original dependent dispatch witnesses. -/
public theorem cutoff_live_dispatch
    (r : Record rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hs : r.input.state.coordinator = .live registers owned base)
    (hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    ∃ outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput r.input registers owned base),
      r.output.preparation.coordinator = .live registers owned base outcome ∧
      (match outcome with
        | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => True
        | _ => False) := by
  have hp : (prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]
    rfl
  have hd : (prepare r.input).coordinator =
      .live registers owned base (CoordinatorRoundDispatch.dispatchLive
        (liveInput r.input registers owned base)) := by
    simp only [prepare, dispatch, hs, CoordinatorRoundDispatch.dispatch]
    rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hc
  rw [hd] at hc
  cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) <;>
    simp only [ho] at hc hd
  all_goals try contradiction
  exact ⟨_, hp.symm.trans hd, trivial⟩

/-- Every original segment coordinate supplies its actual selection and
prechoice frame. The full incoming ledger is preserved in the continuing
branch; only a genuine LIVE cutoff uses a checked initializer. -/
public theorem actual_segment_choice_frame
    (e : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (a : Fin seg.records.length) :
    ∃ (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (c : Choice rate) (selected : Selection seg.records[a.val].input)
      (data : KthCPrechoiceData rate),
      j.val = e + a.val ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val] = seg.records[a.val] ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        seg.records[a.val].input.time z = some seg.records[a.val] ∧
      choice seg.records[a.val].input = some c ∧ c.payload = seg.context.payload ∧
      seg.records[a.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = c.payload ∧
      selected.view.pendingAtChoice = c.preLedger.pending ∧
      kthCPrechoiceData rate rewards C_star C_h seg.records[a.val].input.time z = some data ∧
      data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
      data.2.2.1 = c.preLedger.cutoff ∧
      ((∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ) (initializer : Initializer p),
          seg.records[a.val].input.state.coordinator = .live registers owned base ∧
          c.initializer = some initializer ∧
          initializer.checkedStart rate = .success c.preLedger ∧
          c.preLedger.pending = Finset.univ) ∨
        ∃ (payload : Payload rate) (ledger : Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          seg.records[a.val].input.state.coordinator = .collection payload ledger saved ∧
          c.preLedger = ledger ∧ c.initializer = none) := by
  obtain ⟨hslot, _hday, c, hc, hP⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
      rate rewards C_star C_h z e seg hat hne hcut a
  obtain ⟨hj, hr⟩ := List.getElem?_eq_some_iff.mp hslot
  let j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).length := ⟨e + a.val, hj⟩
  have hrecord : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val] = seg.records[a.val] := hr
  have hlookup := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
    rate rewards C_star C_h z j.val j.isLt
  rw [hrecord] at hlookup
  obtain ⟨selected, data, hs, hsP, hsp, hd, hdP, hdp, hdc, hframe⟩ :=
    actual_choice_pending_frame rate rewards C_star C_h z _ _ hlookup c hc
  exact ⟨j, c, selected, data, rfl, hrecord, hlookup, hc, hP,
    hs, hsP, hsp, hd, hdP, hdp, hdc, hframe⟩

/-- The raw cutoff run is the actual original segment, before analytic
stopping. No inherited follower decoder bank is reset by this identity. -/
public theorem actualCutoffRun_eq_actual_segment
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    actualCutoffRun rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e =
        seg.records := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hs := (segmentAt_branch R e.val seg hat).1
  have hpartition := segment_partition (R.drop e.val) seg hs
  have hentry : seg.entry = R[e.val] := by
    rw [List.drop_eq_getElem_cons e.isLt] at hs
    unfold ReferenceCollectionSegmentExtraction.segment at hs
    cases hc : choice R[e.val].input with
    | none =>
        dsimp only [R] at hc
        simp only [hc, Option.map_none] at hs
        cases hs
    | some c =>
        dsimp only [R] at hc
        simp only [hc, Option.map_some] at hs
        split at hs
        · exact (congrArg Segment.entry (Option.some.inj hs)).symm
        · exact (congrArg Segment.entry (Option.some.inj hs)).symm
  have hcalendar := ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
    rate rewards C_star C_h z e.val seg hat hne hcut
  have hchoices : ∀ a : Fin seg.records.length, ∃ c : Choice rate,
      choice seg.records[a.val].input = some c := by
    intro a
    obtain ⟨_hr, _hd, c, hc, _hp⟩ := hcalendar a
    exact ⟨c, hc⟩
  obtain ⟨_hlen, hboundary⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_horizon_or_installation
      rate rewards C_star C_h z e.val seg hat hne hcut
  apply actualCutoffRun_eq_segment_records rate R e seg hentry hcut hpartition hchoices
  rcases hboundary with hterminal | ⟨hb, hdrop, hlater, _hrest⟩
  · exact Or.inl hterminal
  · exact Or.inr ⟨⟨e.val + seg.records.length, hb⟩, rfl, hlater, hdrop⟩

/-- On the actual raw cutoff run, supported and excluded dates keep the
literal inclusive bad-date gate and the existing incoming OLD selector. -/
public theorem actual_cutoff_old_readout_pointwise
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (seg : Segment rate)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let K := actualCutoffRun rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e
    ∀ r ∈ K, ∀ i : Fin (p.m - 1),
      kthCOLDReadout rate rewards C_star C_h k r.input.time i z =
        (if r.input.time.val + 1 ≤
            ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
          then (1 : ℝ) else 0) *
        (if ∃ pending, i ∈ pending ∧ kthCPrechoiceStage
            rate rewards C_star C_h r.input.time i z = some (pending, .old)
          then (1 : ℝ) else 0) *
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i r.input.time z := by
  dsimp only
  rw [actualCutoffRun_eq_actual_segment rate rewards C_star C_h z e seg hat hne hcut]
  intro r hr i
  have hprojection := kthCDates_eq_actual_segment_dates
    rate rewards C_star C_h z k hk e seg hdate hat
  obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_hr, _hd, c, hc, _hP⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
      rate rewards C_star C_h z e.val seg hat hne hcut ⟨a, ha⟩
  change choice seg.records[a].input = some c at hc
  rw [har] at hc
  exact old_readout_on_projected_record rate rewards C_star C_h z k seg.records
    hprojection r hr (by rw [hc]; rfl) i

/-- Every calendar prefix transports to the literal local OLD readout on
the same entire cutoff run. `List.take` clamps the natural subtraction at
both the calendar start and the end of the actual run. -/
public theorem actual_cutoff_old_prefix_transport
    (k : Fin (p.T + 1))
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (e : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (seg : Segment rate)
    (hdate : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e.val = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (v : ℕ) (i : Fin (p.m - 1)) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      kthCOLDReadout rate rewards C_star C_h k t i z) =
      ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
        rate rewards C_star C_h z
        (actualCutoffRun rate (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h) e)
        (v - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val))
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) i := by
  rw [actualCutoffRun_eq_actual_segment rate rewards C_star C_h z e seg hat hne hcut]
  have hcalendar := ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_calendar
    rate rewards C_star C_h z e.val seg hat hne hcut
  apply old_prefix_transport rate rewards C_star C_h z k seg.records
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val)
  · intro a
    have hd := (hcalendar a).2.1
    omega
  · intro r hr
    obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨_hr, _hd, c, hc, _hp⟩ := hcalendar ⟨a, ha⟩
    change choice seg.records[a].input = some c at hc
    rw [har] at hc
    rw [hc]
    rfl
  · exact kthCDates_eq_actual_segment_dates rate rewards C_star C_h z k hk e seg hdate hat

/-- Different ranks cannot share a supported C date. -/
public theorem kthCDates_disjoint (k l : Fin (p.T + 1)) (hkl : k ≠ l) :
    Disjoint (kthCDates rate rewards C_star C_h z k)
      (kthCDates rate rewards C_star C_h z l) := by
  apply Finset.disjoint_left.mpr
  intro t ht hk
  exact (Finset.disjoint_left.mp
    (kthStoppedTransferWindowDates_disjoint rate rewards C_star C_h z k l hkl))
    (Finset.mem_inter.mp ht).1 (Finset.mem_inter.mp hk).1

/-- All-source alignment and its literal OLD-prefix application. Every
nonempty branch uses the actual original LIVE cutoff and unchanged complete
cutoff run. No quota, bank acceptance, waiting bound or law is asserted. -/
public theorem kthCDates_empty_or_actual_cutoff_alignment (k : Fin (p.T + 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    (kthCDates rate rewards C_star C_h z k = ∅ ∧
      ∀ (t : Fin p.T) (i : Fin (p.m - 1)),
        kthCOLDReadout rate rewards C_star C_h k t i z = 0) ∨
    ∃ (e : Fin R.length)
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (outcome : CoordinatorRoundDispatch.LiveOutcome (p := p)
        (liveInput (p := p) (rate := rate) (R[e.val]'e.isLt).input registers owned base))
      (seg : Segment rate),
      let K := actualCutoffRun rate R e
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val + 1 ∧
      R[e.val].input.state.coordinator = .live registers owned base ∧
      R[e.val].output.preparation.coordinator = .live registers owned base outcome ∧
      (match outcome with | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => True | _ => False) ∧
      segmentAt R e.val = some seg ∧ seg.entry = R[e.val] ∧
      seg.context.payload = registers.payload ∧ K = seg.records ∧
      kthCDates rate rewards C_star C_h z k = actualCutoffChoiceDates rate K
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) ∧
      (K.map fun r => r.input.time).Nodup ∧
      (∀ r ∈ K, ReferenceCollectionPhaseHistory.laterChosen r.input = false) ∧
      (e.val + K.length = R.length ∨ ∃ b : Fin R.length,
        b.val = e.val + K.length ∧
        ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
        seg.exit = .laterChosen R[b.val] ∧ R.drop b.val = seg.remaining) ∧
      (∀ r ∈ K, ∃ (j : Fin R.length) (c : Choice rate)
          (selected : Selection r.input) (data : KthCPrechoiceData rate),
        e.val ≤ j.val ∧ j.val < e.val + K.length ∧
        R[j.val] = r ∧
        r.input.time.val + 1 =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val + 1 ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h r.input.time z = some r ∧
        choice r.input = some c ∧ c.payload = registers.payload ∧
        r.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = c.payload ∧
        selected.view.pendingAtChoice = c.preLedger.pending ∧
        kthCPrechoiceData rate rewards C_star C_h r.input.time z = some data ∧
        data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
        data.2.2.1 = c.preLedger.cutoff ∧
        ((∃ (live : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (liveOwned : CoordinatorLiveServiceFinish.OwnedRegisters live)
            (liveBase : Fin (p.m - 1) → ℕ) (initializer : Initializer p),
            r.input.state.coordinator = .live live liveOwned liveBase ∧
            c.initializer = some initializer ∧
            initializer.checkedStart rate = .success c.preLedger ∧
            c.preLedger.pending = Finset.univ) ∨
          ∃ (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
            r.input.state.coordinator = .collection payload ledger saved ∧
            c.preLedger = ledger ∧ c.initializer = none)) ∧
      (∀ (v : ℕ) (i : Fin (p.m - 1)),
        (∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
          kthCOLDReadout rate rewards C_star C_h k t i z) =
        ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
          rate rewards C_star C_h z K
          (v - (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val))
          (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) i) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain hempty | ⟨e, registers, owned, base, seg, hdate, hstate, hat, hentry,
      hne, hcut, hpayload, hcalendar, hprojection, hrun, hnot, hboundary⟩ :=
    kthCDates_empty_or_actual_cutoff_segment rate rewards C_star C_h z k
  · exact Or.inl ⟨hempty, fun t i =>
      kthCOLDReadout_zero_of_empty rate rewards C_star C_h z k hempty t i⟩
  · have hc : ReferenceCollectionPhaseHistory.cutoffChosen R[e.val].input = true := by
      rw [← hentry]
      exact hcut
    obtain ⟨outcome, houtcome, hsuccessful⟩ := cutoff_live_dispatch rate R[e.val]
      registers owned base hstate hc
    have hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ p.T := by
      rw [hdate]
      have hsource := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z e
      have ht := R[e.val].input.time.isLt
      change R[e.val].input.time.val + 1 = _ at hsource
      omega
    refine Or.inr ⟨e, registers, owned, base, outcome, seg, hdate, hstate, houtcome,
      (by cases outcome <;> exact hsuccessful),
      hat, hentry, hpayload, hrun, hprojection, ?_, hnot, ?_, ?_, ?_⟩
    · rw [hrun]
      apply consecutive_dates_nodup rate seg.records
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e.val)
      intro a
      have hd := (hcalendar a).2.1
      omega
    · simpa only [hrun] using hboundary
    · intro r hr
      rw [hrun] at hr
      obtain ⟨a, ha, har⟩ := List.mem_iff_getElem.mp hr
      subst r
      obtain ⟨j, c, selected, data, hidx, hrecord, hlookup, hchoice, hP,
          hselected, hsP, hsp, hd, hdP, hdp, hdc, hframe⟩ :=
        actual_segment_choice_frame rate rewards C_star C_h z e.val seg hat hne hcut ⟨a, ha⟩
      have hday := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z j
      rw [hrecord] at hday
      refine ⟨j, c, selected, data, ?_, ?_, hrecord, hday, hlookup, hchoice,
        hP.trans hpayload, hselected, hsP, hsp, hd, hdP, hdp, hdc, hframe⟩
      · change j.val = e.val + a at hidx
        omega
      · rw [hrun]
        change j.val = e.val + a at hidx
        omega
    · intro v i
      exact actual_cutoff_old_prefix_transport rate rewards C_star C_h z
        k hk e seg hdate hat hne hcut v i

end Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment

end
