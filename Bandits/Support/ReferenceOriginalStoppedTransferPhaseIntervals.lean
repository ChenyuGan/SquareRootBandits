/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalTransferPhysicalIntervals
public import Bandits.Support.ReferenceOriginalInstalledLiveStartExclusion
public import Bandits.Support.ReferenceOriginalInitialTransferWindowGeometry

import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-!
# Stopped phase intervals on the original physical calendar

This module composes the accepted raw collection, later-installation, and
initial-transfer geometry with the inclusive first-bad-date truncation.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCollectionSegmentExtraction
open scoped Classical

namespace Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem sorted_next_eq_of_minimal_mem {L : List ℕ} (k : ℕ)
    (hsorted : L.SortedLE) (hnodup : L.Nodup)
    (hk : k < L.length) (a : ℕ) (ha : L[k] = a)
    (b : ℕ) (hbmem : b ∈ L) (hab : a < b)
    (hgap : ∀ d ∈ L, a < d → d < b → False) :
    L[k + 1]? = some b := by
  obtain ⟨j, hj, hbj⟩ := List.mem_iff_getElem.mp hbmem
  have hpos : k < j := by
    by_contra hnot
    have hjk : j ≤ k := Nat.le_of_not_gt hnot
    have hle := hsorted.getElem_le_getElem_of_le (hi := hj)
      (hj := hk) hjk
    rw [hbj, ha] at hle
    omega
  have hsucc : j = k + 1 := by
    by_contra hne
    have hlt : k + 1 < j := by omega
    have hbound : k + 1 < L.length := by omega
    have hnext : a ≤ L[k + 1] := by
      have := hsorted.getElem_le_getElem_of_le (hi := hk)
        (hj := hbound) (by omega)
      simpa only [ha] using this
    have hnextle : L[k + 1] ≤ b := by
      have := hsorted.getElem_le_getElem_of_le (hi := hbound)
        (hj := hj) (by omega)
      simpa only [hbj] using this
    have hnextne : L[k + 1] ≠ a := by
      intro heq
      have hvalue : L[k + 1] = L[k] := heq.trans ha.symm
      have hinj := hnodup.getElem_inj_iff.mp hvalue
      omega
    have hstrict : a < L[k + 1] := by omega
    have hnextneB : L[k + 1] ≠ b := by
      intro heq
      have hvalue : L[k + 1] = L[j] := heq.trans hbj.symm
      have hinj := hnodup.getElem_inj_iff.mp hvalue
      omega
    have hstrictB : L[k + 1] < b := by omega
    exact (hgap L[k + 1] (List.getElem_mem _) hstrict hstrictB).elim
  subst j
  rw [List.getElem?_eq_getElem (by omega), hbj]

private theorem sorted_next_default_of_no_later_mem {L : List ℕ} (k : ℕ)
    (hsorted : L.SortedLE) (hnodup : L.Nodup)
    (hk : k < L.length) (a : ℕ) (ha : L[k] = a)
    (hno : ∀ d ∈ L, a < d → False) :
    L[k + 1]? = none := by
  have hlen : L.length ≤ k + 1 := by
    by_contra h
    have hbound : k + 1 < L.length := by omega
    have hmem : L[k + 1] ∈ L := List.getElem_mem hbound
    have hge : a ≤ L[k + 1] := by
      have := hsorted.getElem_le_getElem_of_le (hi := hk)
        (hj := hbound) (by omega)
      simpa only [ha] using this
    have hne : L[k + 1] ≠ a := by
      intro heq
      have hvalue : L[k + 1] = L[k] := heq.trans ha.symm
      have hinj := hnodup.getElem_inj_iff.mp hvalue
      omega
    exact (hno L[k + 1] hmem (by omega)).elim
  exact List.getElem?_eq_none_iff.mpr (by omega)

private theorem suffix_record_actual_lookup
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val] := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have ht := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
    rate rewards C_star C_h z j
  change R[j.val].input.time.val + 1 = s + j.val + 1 at ht
  have htime : R[j.val].input.time.val = s + j.val := by omega
  change (if s ≤ R[j.val].input.time.val then R[R[j.val].input.time.val - s]?
    else none) = some R[j.val]
  rw [htime, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem j.isLt

private theorem slot_record_actual_lookup
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (j : ℕ) (r : Record rate)
    (hslot : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j]? = some r) :
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h r.input.time z = some r := by
  obtain ⟨hj, hsame⟩ := List.getElem?_eq_some_iff.mp hslot
  have hactual := suffix_record_actual_lookup rate rewards C_star C_h z ⟨j, hj⟩
  rw [hsame] at hactual
  exact hactual

private theorem actual_start_suffix_index
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (q : Fin p.T)
    (hstart : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z) :
    ∃ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length,
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val = q.val ∧
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time z := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  rcases hstart with hfirst | hlive
  · obtain ⟨record, hrecord, hstate⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h q z).mp hfirst
    obtain ⟨j, hindex, hsame⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actualRecordAt_suffix_index
        rate rewards C_star C_h q z (by
          rcases hfirst with ⟨_, htime, _⟩
          omega) record hrecord
    subst record
    refine ⟨j, hindex, ?_⟩
    have htime : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time = q := by
      have hcalendar := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z j
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        j.val = q.val at hindex
      apply Fin.ext
      omega
    rw [htime]
    exact Or.inl hfirst
  · obtain ⟨record, regs, owned, base, started, hrecord, hstate, hcall, hcommand⟩ :=
      (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_iff
        rate rewards C_star C_h q z).mp hlive
    obtain ⟨j, hindex, hsame⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actualRecordAt_suffix_index
        rate rewards C_star C_h q z (by
          exact ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_after_physicalStart
            rate rewards C_star C_h q z hlive) record hrecord
    subst record
    refine ⟨j, hindex, ?_⟩
    have htime : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time = q := by
      have hcalendar := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z j
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        j.val = q.val at hindex
      apply Fin.ext
      omega
    rw [htime]
    exact Or.inr hlive

private theorem stopped_list_successor_raw_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (i n : ℕ)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hi : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i + 1)
    (hin : i < n)
    (hnR : n ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hgap : ∀ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length,
      i < j.val → j.val < n →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time z)
    (hboundary : ∀ (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length),
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[n]'hn).input.time z) :
    (if n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
      then ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1
      else p.T + 1) =
    ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
      rate rewards C_star C_h k z := by
  let D := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates
    rate rewards C_star C_h z
  let L := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList
    rate rewards C_star C_h z
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hkPresent :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_present_exactly
      rate rewards C_star C_h k z).mp hk
  have hkL : k.val < L.length := by
    rw [ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_length]
    exact hkPresent
  have hcurGet : L[k.val] = s + i + 1 := by
    have h := hi
    change L.getD k.val (p.T + 1) = s + i + 1 at h
    rw [List.getD_eq_getElem (l := L) (d := p.T + 1) hkL] at h
    exact h
  have hnoLaterBefore : ∀ d ∈ L, s + i + 1 < d →
      d < s + n + 1 → False := by
    intro d hd hcurd hdn
    obtain ⟨q, hq, hdate⟩ :=
      (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
        rate rewards C_star C_h d z).mp
        ((Finset.mem_sort (α := ℕ) (· ≤ ·)).1 hd)
    change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h q z ∧
      q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z at hq
    obtain ⟨j, hindex, hactual⟩ := actual_start_suffix_index
      rate rewards C_star C_h z q hq.1
    change s + j.val = q.val at hindex
    have hgapj : i < j.val ∧ j.val < n := by
      rw [← hdate] at hcurd hdn
      omega
    exact hgap j hgapj.1 hgapj.2 hactual
  by_cases hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length
  · let bdate := s + n + 1
    have hbactual := hboundary hn
    let q := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[n].input.time
    have hqdate : q.val + 1 = bdate := by
      have hdate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z ⟨n, hn⟩
      dsimp only [q, bdate, s] at hdate ⊢
      exact hdate
    by_cases hstop : bdate ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z
    · have hbdmem : bdate ∈ D := by
        apply (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
          rate rewards C_star C_h bdate z).2
        refine ⟨q, ?_, hqdate⟩
        change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
            rate rewards C_star C_h q z ∧
          q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z
        exact ⟨hbactual, by rw [hqdate]; exact hstop⟩
      have hbdSorted : bdate ∈ L :=
        (Finset.mem_sort (α := ℕ) (· ≤ ·)).2 hbdmem
      have hgreater : s + i + 1 < bdate := by
        dsimp only [bdate]
        omega
      have hnextSome := sorted_next_eq_of_minimal_mem (L := L) k.val
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_sortedLE
          rate rewards C_star C_h z)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_nodup
          rate rewards C_star C_h z)
        hkL (s + i + 1) hcurGet bdate hbdSorted hgreater hnoLaterBefore
      have hnext : ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
          rate rewards C_star C_h k z = bdate := by
        change L.getD (k.val + 1) (p.T + 1) = bdate
        rw [List.getD_eq_getElem?_getD, hnextSome]
        rfl
      have hcond : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length ∧
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ≤
            ReferenceCompleteSignedFirstBadCalendar.firstBadDate
              rate rewards C_star C_h z := by
        exact ⟨hn, by simpa only [bdate, s] using hstop⟩
      rw [ite_eq_left hcond]
      exact hnext.symm
    · have hnoStop : ∀ d ∈ L, s + i + 1 < d → False := by
        intro d hd hcurd
        by_cases hdb : d < bdate
        · exact hnoLaterBefore d hd hcurd hdb
        · have hmem := (Finset.mem_sort (α := ℕ) (· ≤ ·)).1 hd
          obtain ⟨q', hq', hdq'⟩ :=
            (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
              rate rewards C_star C_h d z).mp hmem
          change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
              rate rewards C_star C_h q' z ∧
            q'.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
              rate rewards C_star C_h z at hq'
          have hdl : d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
              rate rewards C_star C_h z := by omega
          have hbdate : bdate ≤ d := by omega
          exact hstop (by omega)
      have hnextNone := sorted_next_default_of_no_later_mem (L := L) k.val
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_sortedLE
          rate rewards C_star C_h z)
        (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_nodup
          rate rewards C_star C_h z)
        hkL (s + i + 1) hcurGet hnoStop
      have hnextEq : ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
          rate rewards C_star C_h k z = p.T + 1 := by
        change L.getD (k.val + 1) (p.T + 1) = p.T + 1
        rw [List.getD_eq_getElem?_getD, hnextNone]
        rfl
      have hcond : ¬(n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length ∧
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ≤
            ReferenceCompleteSignedFirstBadCalendar.firstBadDate
              rate rewards C_star C_h z) := by
        intro h
        exact hstop (by simpa only [bdate, s] using h.2)
      rw [ite_eq_right hcond]
      exact hnextEq.symm
  · have hnoStop : ∀ d ∈ L, s + i + 1 < d → False := by
      intro d hd hcurd
      have hmem := (Finset.mem_sort (α := ℕ) (· ≤ ·)).1 hd
      obtain ⟨q, hq, hdate⟩ :=
        (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
          rate rewards C_star C_h d z).mp hmem
      change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
          rate rewards C_star C_h q z ∧
        q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z at hq
      have : d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z := by omega
      have hdlt : d < s + n + 1 := by
        have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
        rw [← hdate] at hcurd
        omega
      exact hnoLaterBefore d hd hcurd hdlt
    have hnextNone := sorted_next_default_of_no_later_mem (L := L) k.val
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_sortedLE
        rate rewards C_star C_h z)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList_nodup
        rate rewards C_star C_h z)
      hkL (s + i + 1) hcurGet hnoStop
    have hnextEq : ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
        rate rewards C_star C_h k z = p.T + 1 := by
      change L.getD (k.val + 1) (p.T + 1) = p.T + 1
      rw [List.getD_eq_getElem?_getD, hnextNone]
      rfl
    have hcond : ¬(n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) := by
      intro h
      exact hn h.1
    rw [ite_eq_right hcond]
    exact hnextEq.symm

private theorem stopped_end_eq_clipped_raw_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (i n : ℕ)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hi : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i + 1)
    (hin : i < n)
    (hnR : n ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hgap : ∀ j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length,
      i < j.val → j.val < n →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[j.val].input.time z)
    (hboundary : ∀ (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length),
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[n]'hn).input.time z) :
    ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
        rate rewards C_star C_h k z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        min n (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) + 1 := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hrawNext := stopped_list_successor_raw_boundary
    rate rewards C_star C_h k z i n hk hi hin hnR hgap hboundary
  have hcurMem :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
      rate rewards C_star C_h k z).mp hk
  obtain ⟨q, hq, hqdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hcurMem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z ∧
    q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z at hq
  have hs : s ≤ min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z) p.T := by
    have hdate : q.val + 1 = s + i + 1 := by rw [← hi]; exact hqdate
    have hT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hbad : s ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z := by omega
    exact Nat.le_min.mpr ⟨hbad, hT⟩
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hRlen : R.length = p.T - s := by simpa only [R, s] using hlen
  unfold ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
  rw [← hrawNext]
  by_cases hraw : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
  · simp only [ite_eq_left hraw]
    have hrawBound : s + n + 1 ≤ min
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T + 1 := by
      have hsn : s + n + 1 ≤ p.T := by rw [hRlen] at hnR; omega
      omega
    have hmin : min n (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T - s) = n := by
      have hsub : n ≤ min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T - s := by omega
      exact Nat.min_eq_left hsub
    rw [Nat.min_eq_left hrawBound, hmin]
  · simp only [ite_eq_right hraw]
    have hclipEq : min n (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T - s) =
        min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z)
          p.T - s := by
      by_cases hnlt : n < R.length
      · have hdateT : s + n + 1 ≤ p.T := by rw [hRlen] at hnR; omega
        have hbadLt : ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z < s + n + 1 := by
          by_contra hnot
          exact hraw ⟨hnlt, by omega⟩
        have hminBad : min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z) p.T =
            ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
          exact Nat.min_eq_left (by omega)
        rw [hminBad]
        exact Nat.min_eq_right (by omega)
      · have hnEq : n = R.length := by omega
        rw [hnEq, hRlen]
        exact Nat.min_eq_right (by omega)
    rw [hclipEq, Nat.min_eq_right (Nat.succ_le_succ (Nat.min_le_right _ _))]
    omega

private theorem clipped_date_membership_iff
    (s n d firstBad T : ℕ)
    (hs : s ≤ min firstBad T) (hn : n ≤ T - s) :
    d < s + min n (min firstBad T - s) + 1 ↔
      d < s + n + 1 ∧ d ≤ firstBad := by
  have hstop : s + min n (min firstBad T - s) + 1 =
      min (s + n + 1) (min firstBad T + 1) := by
    by_cases h : n ≤ min firstBad T - s
    · rw [Nat.min_eq_left h]
      have hleft : s + n + 1 ≤ min firstBad T + 1 := by omega
      rw [Nat.min_eq_left hleft]
    · rw [Nat.min_eq_right (by omega)]
      have hright : min firstBad T + 1 ≤ s + n + 1 := by omega
      rw [Nat.min_eq_right hright]
      omega
  rw [hstop, Nat.lt_min]
  constructor
  · rintro ⟨hdRaw, hdStop⟩
    have hdBadMin : d ≤ min firstBad T := by omega
    exact ⟨hdRaw, (Nat.le_min.mp hdBadMin).1⟩
  · rintro ⟨hdRaw, hdBad⟩
    have hdT : d ≤ T := by omega
    have hdBadMin : d ≤ min firstBad T := Nat.le_min.mpr ⟨hdBad, hdT⟩
    exact ⟨hdRaw, by omega⟩

private theorem present_start_before_bad_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (i : ℕ)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hi : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i + 1) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hmem :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
      rate rewards C_star C_h k z).mp hk
  obtain ⟨q, hq, hqdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      rate rewards C_star C_h q z ∧
    q.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z at hq
  have hdate : q.val + 1 = s + i + 1 := by rw [← hi]; exact hqdate
  have hbad : s ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z := by omega
  have hT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  exact Nat.le_min.mpr ⟨hbad, hT⟩

private theorem installed_raw_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    b.val + V.length ≤ R.length ∧
    (∀ j : Fin R.length, b.val ≤ j.val → j.val < b.val + V.length →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h R[j.val].input.time z) ∧
    (∀ hn : b.val + V.length < R.length,
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h (R[b.val + V.length]'hn).input.time z) := by
  intro R V
  obtain ⟨hrows, hend⟩ :=
    ReferenceOriginalInstalledLiveStartExclusion.actual_later_installation_live_start_exclusion
      rate rewards C_star C_h z b hb
  change b.val + V.length = R.length ∨ _ at hend
  have hle : b.val + V.length ≤ R.length := by
    rcases hend with heq | ⟨e, he, _⟩
    · exact heq.le
    · change e.val = b.val + V.length at he
      have : e.val < R.length := e.isLt
      omega
  refine ⟨hle, ?_, ?_⟩
  · intro j hj hjn
    let v : Fin V.length := ⟨j.val - b.val, by omega⟩
    obtain ⟨hslot, _, _, _, _, _, _, _, _, _, hno⟩ := hrows v
    have hindex : b.val + v.val = j.val := by dsimp only [v]; omega
    rw [hindex, List.getElem?_eq_getElem j.isLt] at hslot
    have hsame := Option.some.inj hslot
    simpa only [hsame] using hno
  · intro hn
    rcases hend with heq | ⟨e, he, _, _, _, _, _, _, _, _, _, _,
      registers, owned, base, _, _, _, hlive⟩
    · omega
    · change e.val = b.val + V.length at he
      have hrec : R[b.val + V.length] = R[e.val] :=
        congrArg (fun x : Fin R.length => R[x.val])
          (show (⟨b.val + V.length, hn⟩ : Fin R.length) = e from Fin.ext he.symm)
      rw [hrec]
      exact Or.inr hlive

private theorem collection_installed_raw_gap
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (i : ℕ) (seg : Segment rate)
    (hat : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) i = some seg)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hbi : b.val = i + seg.records.length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    ∀ j : Fin R.length, i < j.val → j.val < b.val + V.length →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h R[j.val].input.time z := by
  intro R V j hij hjn
  by_cases hjb : j.val < b.val
  · let c : Fin seg.records.length := ⟨j.val - i, by omega⟩
    have hslot := ReferenceCompleteLaterCollectionCalendarWord.actual_later_segment_slot_record
      rate rewards C_star C_h z i seg hat c
    have hindex : i + c.val = j.val := by dsimp only [c]; omega
    rw [hindex, List.getElem?_eq_getElem j.isLt] at hslot
    have hsame := Option.some.inj hslot
    rw [hsame]
    exact ReferenceOriginalTransferPhysicalIntervals.actual_collection_segment_no_internal_transfer_start
      rate rewards C_star C_h z i seg hat c (by dsimp only [c]; omega)
  · exact (installed_raw_boundary rate rewards C_star C_h z b hb).2.1 j
      (by omega) hjn

private theorem indexed_phase_dates_iff
    {rate : RateInput p} (L : List (Record rate)) (a lo hi stop : ℕ)
    (hhi : hi ≤ L.length)
    (hdates : ∀ j : Fin L.length, L[j.val].input.time.val + 1 = a + j.val + 1)
    (d : ℕ) :
    (∃ j : Fin L.length, lo ≤ j.val ∧ j.val < hi ∧
      L[j.val].input.time.val + 1 = d ∧ d < stop) ↔
      a + lo + 1 ≤ d ∧ d < min (a + hi + 1) stop := by
  constructor
  · rintro ⟨j, hjlo, hjhi, hjdate, hjstop⟩
    have := hdates j
    omega
  · rintro ⟨hdlo, hdhi⟩
    obtain ⟨hdhi, hstop⟩ := Nat.lt_min.mp hdhi
    let j : Fin L.length := ⟨d - (a + 1), by omega⟩
    have hdate := hdates j
    refine ⟨j, ?_, ?_, ?_, ?_⟩
    · dsimp only [j]
      omega
    · dsimp only [j]
      omega
    · exact hdate.trans (by dsimp only [j]; omega)
    · exact hstop

private theorem indexed_pending_fields
    {rate : RateInput p} (V : List (Record rate)) (a h : ℕ) (payload : Payload rate)
    (hdates : ∀ j : Fin V.length, V[j.val].input.time.val + 1 = a + j.val + 1)
    (hfields : ∀ j : Fin V.length, ∃ selected : Selection V[j.val].input,
      V[j.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧
      (selected.view.pendingAtChoice.Nonempty ↔ V[j.val].input.time.val + 1 < a + h + 1) ∧
      (selected.view.pendingAtChoice = ∅ ↔ a + h + 1 ≤ V[j.val].input.time.val + 1)) :
    ∀ j : Fin V.length, ∃ selected : Selection V[j.val].input,
      V[j.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧
      (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
      (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val) := by
  intro j
  obtain ⟨selected, hs, hp, hm, he⟩ := hfields j
  rw [hdates j] at hm he
  exact ⟨selected, hs, hp,
    by simpa only [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_left] using hm,
    by simpa only [Nat.add_le_add_iff_right, Nat.add_le_add_iff_left] using he⟩

private theorem selected_phase_dates_iff
    {rate : RateInput p} (V : List (Record rate)) (a h stop : ℕ)
    (hh : h ≤ V.length)
    (hdates : ∀ j : Fin V.length, V[j.val].input.time.val + 1 = a + j.val + 1)
    (hfields : ∀ j : Fin V.length, ∃ selected : Selection V[j.val].input,
      V[j.val].output.preparation.coordinator.selection = some selected ∧
      (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
      (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val)) :
    (∀ d : ℕ,
      (∃ j : Fin V.length, ∃ selected : Selection V[j.val].input,
        V[j.val].output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice.Nonempty ∧
        V[j.val].input.time.val + 1 = d ∧ d < stop) ↔
        a + 1 ≤ d ∧ d < min (a + h + 1) stop) ∧
    (∀ d : ℕ,
      (∃ j : Fin V.length, ∃ selected : Selection V[j.val].input,
        V[j.val].output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice = ∅ ∧
        V[j.val].input.time.val + 1 = d ∧ d < stop) ↔
        a + h + 1 ≤ d ∧ d < min (a + V.length + 1) stop) := by
  constructor
  · intro d
    rw [← indexed_phase_dates_iff V a 0 h stop hh hdates d]
    constructor
    · rintro ⟨j, selected, hs, hp, hd, hstop⟩
      obtain ⟨actual, ha, hm, _⟩ := hfields j
      have heq : selected = actual := Option.some.inj (hs.symm.trans ha)
      subst selected
      exact ⟨j, Nat.zero_le _, hm.mp hp, hd, hstop⟩
    · rintro ⟨j, _, hj, hd, hstop⟩
      obtain ⟨selected, hs, hm, _⟩ := hfields j
      exact ⟨j, selected, hs, hm.mpr hj, hd, hstop⟩
  · intro d
    rw [← indexed_phase_dates_iff V a h V.length stop le_rfl hdates d]
    constructor
    · rintro ⟨j, selected, hs, hp, hd, hstop⟩
      obtain ⟨actual, ha, _, hm⟩ := hfields j
      have heq : selected = actual := Option.some.inj (hs.symm.trans ha)
      subst selected
      exact ⟨j, hm.mp hp, j.isLt, hd, hstop⟩
    · rintro ⟨j, hj, _, hd, hstop⟩
      obtain ⟨selected, hs, _, hm⟩ := hfields j
      exact ⟨j, selected, hs, hm.mpr hj, hd, hstop⟩

private theorem initial_raw_boundary
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    W.length ≤ R.length ∧
    (∀ j : Fin R.length, 0 < j.val → j.val < W.length →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h R[j.val].input.time z) ∧
    (∀ hn : W.length < R.length,
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h (R[W.length]'hn).input.time z) := by
  intro R W
  have hprefix : W <+: R := by
    dsimp only [W, R]
    rw [ReferenceOriginalInitialTransferWindowGeometry.raw_window_eq_complete_suffix_takeWhile]
    exact List.takeWhile_prefix _
  refine ⟨hprefix.length_le, ?_, ?_⟩
  · intro j hj hjW
    have heq : W[j.val] = R[j.val] := hprefix.getElem hjW
    rw [← heq]
    exact ReferenceOriginalInitialTransferWindowGeometry.raw_window_no_positive_transfer_start
      rate rewards C_star C_h z ⟨j.val, hjW⟩ hj
  · intro hn
    obtain ⟨r, hr, hstart⟩ :=
      ReferenceOriginalInitialTransferWindowGeometry.raw_first_excluded_live_transfer_start
        rate rewards C_star C_h z hn
    change R[W.length] = r at hr
    rw [hr]
    exact Or.inr hstart

private theorem original_record_clipping_iff
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (n E : ℕ)
    (hclip : ∀ d : ℕ, d < E ↔
      d < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n + 1 ∧
      d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input.time.val + 1 < E ↔
      j.val < n ∧ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[j.val].input.time.val + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
  have hdate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
    rate rewards C_star C_h z j
  rw [hclip, hdate]
  omega

private theorem choice_none_of_first_or_live_no_cutoff
    {rate : RateInput p} (r : Record rate)
    (hstate : r.input.state.coordinator = .first ∨
      ∃ registers owned base, r.input.state.coordinator = .live registers owned base)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false) :
    choice r.input = none := by
  rcases hstate with hfirst | ⟨registers, owned, base, hcoord⟩
  · exact choice_first_none r.input hfirst
  · have hd : dispatch r.input = .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base)) := by
      simp only [dispatch, hcoord, CoordinatorRoundDispatch.dispatch]
      rfl
    unfold choice
    split
    · rfl
    · change choiceOfCut (dispatch r.input) = none
      rw [hd]
      cases ho : CoordinatorRoundDispatch.dispatchLive
          (liveInput r.input registers owned base) <;>
        simp_all only [ReferenceCollectionPhaseHistory.cutoffChosen, prepare,
          choiceOfCut, Bool.true_eq_false]

private theorem later_release_after_clipping
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) (E : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let h := (V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
    E ≤ s + b.val + V.length + 1 → s + b.val + h + 1 < E →
      ∃ (j : Fin V.length) (hn : j.val + 1 < V.length),
        j.val + 1 = h ∧ V[j.val].input.time.val + 1 < E ∧
        ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] ∧
        ∃ selected : Selection V[j.val].input,
          V[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice =
            {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (V[j.val].input.row.2 V[j.val].input.time).1} ∧
          R[b.val + j.val]? = some V[j.val] ∧
          R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
          (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
          (V[j.val + 1]'hn).input.time.val + 1 < E ∧
          ∃ nextSelected : Selection (V[j.val + 1]'hn).input,
            (V[j.val + 1]'hn).output.preparation.coordinator.selection = some nextSelected ∧
            nextSelected.view.pendingAtChoice = ∅ := by
  intro R V s h hEraw hsurvives
  have hhV : h < V.length := by omega
  let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  have hRel : Rel ≠ [] := by
    intro hnil
    have hsplit : h + Rel.length = V.length := by
      have hlen := congrArg List.length (List.takeWhile_append_dropWhile
        (p := ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice) (l := V))
      simpa only [List.length_append] using hlen
    rw [hnil, List.length_nil] at hsplit
    omega
  have hrelease :=
    ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_boundary
      rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hrelease
  obtain ⟨_, _, _, _, hboundaryRelease⟩ := hrelease
  obtain ⟨j, hn, hj, htwo, hclear, selected, hs, hsingle,
    hslot, hslotNext, _hhead, hdate, _hfollowers⟩ := hboundaryRelease hRel
  change j.val = h - 1 at hj
  change 2 ≤ h at htwo
  have hjh : j.val + 1 = h := by omega
  obtain ⟨_payload, _hbirth, hfields, _hclear⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.actual_later_installation_missing_date_iff
      rate rewards C_star C_h z b hb
  have hprevDate : V[j.val].input.time.val + 1 = s + b.val + j.val + 1 :=
    (hfields j).2.1
  obtain ⟨_hslot, hnextDate, nextSelected, hnextSelection, _hpayload, _hmissing, hempty⟩ :=
    hfields ⟨j.val + 1, hn⟩
  change (V[j.val + 1]'hn).input.time.val + 1 = s + b.val + (j.val + 1) + 1 at hnextDate
  have hnextPending : nextSelected.view.pendingAtChoice = ∅ := by
    apply hempty.mpr
    change s + b.val + h + 1 ≤ (V[j.val + 1]'hn).input.time.val + 1
    rw [hnextDate, hjh]
  refine ⟨j, hn, hjh, ?_, hclear, selected, hs, hsingle, hslot,
    hslotNext, hdate, ?_, nextSelected, hnextSelection, hnextPending⟩
  · change V[j.val].input.time.val + 1 < E
    omega
  · change (V[j.val + 1]'hn).input.time.val + 1 < E
    omega

private theorem initial_release_after_clipping
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (E : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let h := ReferenceOriginalInitialTransferWindowGeometry.rawMissingPrefixLength
      rate rewards C_star C_h z
    E ≤ s + W.length + 1 → s + h + 1 < E →
      ∃ (j : Fin W.length) (hn : j.val + 1 < W.length),
        j.val + 1 = h ∧ W[j.val].input.time.val + 1 < E ∧
        ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[j.val] selected ∧
          selected.view.pendingAtChoice =
            {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (W[j.val].input.row.2 W[j.val].input.time).1} ∧
          R[j.val]? = some W[j.val] ∧ R[j.val + 1]? = some (W[j.val + 1]'hn) ∧
          (W[j.val + 1]'hn).input.time.val = W[j.val].input.time.val + 1 ∧
          (W[j.val + 1]'hn).input.time.val + 1 < E ∧
          ∃ nextSelected : Selection (W[j.val + 1]'hn).input,
            (W[j.val + 1]'hn).output.preparation.coordinator.selection = some nextSelected ∧
            nextSelected.view.pendingAtChoice = ∅ := by
  intro R W s h hEraw hsurvives
  have hhW : h < W.length := by omega
  have hWpos : 0 < W.length := by omega
  have hfirstMissing :=
    (ReferenceOriginalInitialTransferWindowGeometry.raw_window_first_is_initial_marker
      rate rewards C_star C_h z hWpos).2
  have hnonempty : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate W[0]).Nonempty := by
    rw [hfirstMissing]
    exact ⟨⟨0, by have := p.two_le_m; omega⟩, Finset.mem_univ _⟩
  have hhpos : 0 < h :=
    (ReferenceOriginalInitialTransferWindowGeometry.raw_missing_prefix_iff
      rate rewards C_star C_h z ⟨0, hWpos⟩).mp hnonempty
  obtain ⟨⟨selected, hselection, hconfirmation, hsingle⟩, _hfalse, _hdate⟩ :=
    ReferenceOriginalInitialTransferWindowGeometry.raw_first_release_after_clearing
      rate rewards C_star C_h z hhW
  let j : Fin W.length := ⟨h - 1, by omega⟩
  have hjh : j.val + 1 = h := by dsimp only [j]; omega
  have hn : j.val + 1 < W.length := by omega
  have hsel : W[j.val].output.preparation.coordinator.selection = some selected := hselection
  have hmissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate W[j.val] =
      selected.view.pendingAtChoice := by
    unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
    rw [hsel]
    rfl
  have hsingle' : selected.view.pendingAtChoice =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[j.val].input.row.2 W[j.val].input.time).1} := hmissing.symm.trans hsingle
  have hprovenance :=
    ReferenceOriginalInitialTransferWindowGeometry.raw_initial_transfer_window_provenance
      rate rewards C_star C_h z
  rcases hprovenance with hzero | ⟨_hW, _installed, _selected0, _hs0,
    _hinstalled, _hp0, _hm0, _hpayload0, hrows⟩
  · change W.length = 0 at hzero
    omega
  · obtain ⟨nextSelected, hnextSelection, _hp, _hphase, _hnext⟩ := hrows ⟨j.val + 1, hn⟩
    change (W[j.val + 1]'hn).output.preparation.coordinator.selection = some nextSelected
      at hnextSelection
    have hnextMissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
        (W[j.val + 1]'hn) = nextSelected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hnextSelection]
      rfl
    have hm := ReferenceOriginalInitialTransferWindowGeometry.raw_missing_prefix_iff
      rate rewards C_star C_h z ⟨j.val + 1, hn⟩
    rw [hnextMissing] at hm
    change nextSelected.view.pendingAtChoice.Nonempty ↔ j.val + 1 < h at hm
    have hempty : nextSelected.view.pendingAtChoice = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rw [hm, hjh]
      exact Nat.lt_irrefl _
    have hprefix : W <+: R := by
      dsimp only [W, R]
      rw [ReferenceOriginalInitialTransferWindowGeometry.raw_window_eq_complete_suffix_takeWhile]
      exact List.takeWhile_prefix _
    have hslot (v : Fin W.length) : R[v.val]? = some W[v.val] := by
      rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le v.isLt hprefix.length_le)]
      exact congrArg some (hprefix.getElem v.isLt).symm
    have hprevTime : W[j.val].input.time.val = s + j.val :=
      (ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z j).1
    have hnextTime : (W[j.val + 1]'hn).input.time.val = s + (j.val + 1) :=
      (ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z ⟨j.val + 1, hn⟩).1
    refine ⟨j, hn, hjh, ?_, selected, hsel, hconfirmation, hsingle',
      hslot j, hslot ⟨j.val + 1, hn⟩, ?_, ?_, nextSelected, hnextSelection, hempty⟩
    · omega
    · omega
    · omega

private theorem initial_raw_indexed_fields
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let h := ReferenceOriginalInitialTransferWindowGeometry.rawMissingPrefixLength
      rate rewards C_star C_h z
    W.length = 0 ∨ ∃ newPayload : Payload rate,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
        rate rewards C_star C_h z = some newPayload ∧
      (∀ j : Fin W.length,
        R[j.val]? = some W[j.val] ∧ W[j.val].input.time.val + 1 = s + j.val + 1 ∧
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h W[j.val].input.time z = some W[j.val] ∧
        choice W[j.val].input = none ∧
        ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = newPayload ∧
          (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
          (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val)) := by
  intro R W s h
  have hprefix : W <+: R := by
    dsimp only [W, R]
    rw [ReferenceOriginalInitialTransferWindowGeometry.raw_window_eq_complete_suffix_takeWhile]
    exact List.takeWhile_prefix _
  have hnR : W.length ≤ R.length := hprefix.length_le
  have hprovenance :=
    ReferenceOriginalInitialTransferWindowGeometry.raw_initial_transfer_window_provenance
      rate rewards C_star C_h z
  rcases hprovenance with hzero | ⟨_hW, installed, _selected0, _hs0,
    _hinstalled, _hp0, _hm0, hpayload0, hrows⟩
  · change W.length = 0 at hzero
    exact Or.inl hzero
  · have hfields : ∀ j : Fin W.length,
        R[j.val]? = some W[j.val] ∧ W[j.val].input.time.val + 1 = s + j.val + 1 ∧
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h W[j.val].input.time z = some W[j.val] ∧
        choice W[j.val].input = none ∧
        ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = installed.registers.payload ∧
          (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
          (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val) := by
      intro j
      obtain ⟨selected, hselected, hpayload, hphase, _hnext⟩ := hrows j
      change W[j.val].output.preparation.coordinator.selection = some selected at hselected
      change (match W[j.val].input.state.coordinator with
        | .first => selected.view.pendingAtChoice = Finset.univ
        | .live incoming _ _ => selected.view.payload = incoming.payload ∧
            selected.view.pendingAtChoice = incoming.pendingAtChoice
        | _ => False) at hphase
      have hcoord : W[j.val].input.state.coordinator = .first ∨
          ∃ registers owned base, W[j.val].input.state.coordinator = .live registers owned base := by
        cases hc : W[j.val].input.state.coordinator with
        | first => exact Or.inl rfl
        | live registers owned base => exact Or.inr ⟨registers, owned, base, rfl⟩
        | collection payload ledger saved => simp only [hc] at hphase
        | dagger => simp only [hc] at hphase
      have hchoice := choice_none_of_first_or_live_no_cutoff W[j.val] hcoord
        (ReferenceOriginalInitialTransferWindowGeometry.raw_window_no_collection_choice
          rate rewards C_star C_h z j)
      have hmissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate W[j.val] =
          selected.view.pendingAtChoice := by
        unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
        rw [hselected]
        rfl
      have hm := ReferenceOriginalInitialTransferWindowGeometry.raw_missing_prefix_iff
        rate rewards C_star C_h z j
      rw [hmissing] at hm
      change selected.view.pendingAtChoice.Nonempty ↔ j.val < h at hm
      have he : selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val := by
        rw [← Finset.not_nonempty_iff_eq_empty, hm]
        omega
      have hcalendar := ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z j
      have hdate : W[j.val].input.time.val + 1 = s + j.val + 1 := by
        have ht : W[j.val].input.time.val = s + j.val := hcalendar.1
        omega
      have hslot : R[j.val]? = some W[j.val] := by
        rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le j.isLt hnR)]
        exact congrArg some (hprefix.getElem j.isLt).symm
      exact ⟨hslot, hdate, hcalendar.2, hchoice, selected, hselected, hpayload, hm, he⟩
    exact Or.inr ⟨installed.registers.payload, hpayload0, hfields⟩

/-- An actual later ranked transfer consists of the old-payload maximal C
segment, followed, if installation occurs, by the new-payload LIVE interval.
The initial branch is identified literally and is handled separately below.
Every phase date characterization is bidirectional and uses the same stopped
right endpoint, including the first bad update. -/
public theorem present_stopped_transfer_collection_intervals
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
      rate rewards C_star C_h k z
    let B := min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z) p.T - s
    ∃ i : Fin R.length,
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = s + i.val + 1 ∧
      ((i.val = 0 ∧ R[i.val].input.state.coordinator = .first ∧
          choice R[i.val].input = none) ∨
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ) (seg : Segment rate),
          R[i.val].input.state.coordinator = .live registers owned base ∧
          segmentAt R i.val = some seg ∧ seg.entry = R[i.val] ∧
          seg.context.payload = registers.payload ∧ seg.records ≠ [] ∧
          (∀ j : Fin seg.records.length,
            R[i.val + j.val]? = some seg.records[j.val] ∧
            seg.records[j.val].input.time.val + 1 = s + i.val + j.val + 1 ∧
            ∃ c : Choice rate, choice seg.records[j.val].input = some c ∧
              c.payload = registers.payload) ∧
          (∀ j : Fin seg.records.length,
            ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
              rate rewards C_star C_h seg.records[j.val].input.time z = some seg.records[j.val]) ∧
          (∀ d : ℕ,
            (∃ j : Fin seg.records.length, ∃ c : Choice rate,
              choice seg.records[j.val].input = some c ∧ c.payload = registers.payload ∧
              seg.records[j.val].input.time.val + 1 = d ∧ d < E) ↔
              s + i.val + 1 ≤ d ∧
                d < min (s + i.val + seg.records.length + 1) E) ∧
          ((i.val + seg.records.length = R.length ∧
              E = s + min R.length B + 1 ∧
              (∀ j : Fin R.length, i.val ≤ j.val →
                (choice R[j.val].input).isSome = true) ∧
              ¬ (∃ b : Fin R.length, b.val = i.val + seg.records.length)) ∨
            ∃ b : Fin R.length, b.val = i.val + seg.records.length ∧
              ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
              seg.exit = .laterChosen R[b.val] ∧
              (∃ saved, R[b.val].input.state.coordinator =
                .collection registers.payload seg.final saved) ∧
              seg.final.pending = ∅ ∧
              let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z (b.val + 1)
              let h := (V.takeWhile
                ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
              b.val + V.length ≤ R.length ∧
              E = s + min (b.val + V.length) B + 1 ∧
              (∀ d : ℕ, d < E ↔ d < s + b.val + V.length + 1 ∧
                d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
                  rate rewards C_star C_h z) ∧
              (∀ j : Fin R.length,
                (i.val ≤ j.val ∧ R[j.val].input.time.val + 1 < E) ↔
                  i.val ≤ j.val ∧ j.val < b.val + V.length ∧
                    R[j.val].input.time.val + 1 ≤
                      ReferenceCompleteSignedFirstBadCalendar.firstBadDate
                        rate rewards C_star C_h z) ∧
              ∃ newPayload : Payload rate,
                ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] newPayload ∧
                (∀ j : Fin V.length,
                  R[b.val + j.val]? = some V[j.val] ∧
                  V[j.val].input.time.val + 1 = s + b.val + j.val + 1 ∧
                  choice V[j.val].input = none ∧
                  ∃ selected : Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.payload = newPayload ∧
                    (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
                    (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val)) ∧
                (∀ j : Fin V.length,
                  ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
                    rate rewards C_star C_h V[j.val].input.time z = some V[j.val]) ∧
                (∀ d : ℕ,
                  (∃ j : Fin V.length, ∃ selected : Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice.Nonempty ∧
                    V[j.val].input.time.val + 1 = d ∧ d < E) ↔
                    s + b.val + 1 ≤ d ∧ d < min (s + b.val + h + 1) E) ∧
                (∀ d : ℕ,
                  (∃ j : Fin V.length, ∃ selected : Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice = ∅ ∧
                    V[j.val].input.time.val + 1 = d ∧ d < E) ↔
                    s + b.val + h + 1 ≤ d ∧
                      d < min (s + b.val + V.length + 1) E) ∧
                (E ≤ s + b.val + h + 1 → ∀ d : ℕ,
                  ¬ (∃ j : Fin V.length, ∃ selected : Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice = ∅ ∧
                    V[j.val].input.time.val + 1 = d ∧ d < E)) ∧
                (s + b.val + h + 1 < E →
                  ∃ (j : Fin V.length) (hn : j.val + 1 < V.length),
                    j.val + 1 = h ∧ V[j.val].input.time.val + 1 < E ∧
                    ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] ∧
                    ∃ selected : Selection V[j.val].input,
                      V[j.val].output.preparation.coordinator.selection = some selected ∧
                      selected.view.pendingAtChoice =
                        {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                          (V[j.val].input.row.2 V[j.val].input.time).1} ∧
                      R[b.val + j.val]? = some V[j.val] ∧
                      R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
                      (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
                      (V[j.val + 1]'hn).input.time.val + 1 < E ∧
                      ∃ nextSelected : Selection (V[j.val + 1]'hn).input,
                        (V[j.val + 1]'hn).output.preparation.coordinator.selection = some nextSelected ∧
                        nextSelected.view.pendingAtChoice = ∅))) := by
  intro R s E B
  obtain ⟨i, hi, hbranch⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.present_start_original_collection_interval
      rate rewards C_star C_h k z hk
  refine ⟨i, hi, ?_⟩
  rcases hbranch with hfirst | ⟨registers, owned, base, seg, hstate, hat, hentry,
    hne, _hcut, hpayload, _hinit, _hpartition, _hchoice, hno, hcalendar, hend⟩
  · exact Or.inl hfirst
  · right
    have hCdates : ∀ j : Fin seg.records.length,
        seg.records[j.val].input.time.val + 1 = (s + i.val) + j.val + 1 :=
      fun j => (hcalendar j).2.1
    have hCiff : ∀ d : ℕ,
        (∃ j : Fin seg.records.length, ∃ c : Choice rate,
          choice seg.records[j.val].input = some c ∧ c.payload = registers.payload ∧
          seg.records[j.val].input.time.val + 1 = d ∧ d < E) ↔
          s + i.val + 1 ≤ d ∧ d < min (s + i.val + seg.records.length + 1) E := by
      intro d
      rw [← indexed_phase_dates_iff seg.records (s + i.val) 0 seg.records.length E
        le_rfl hCdates d]
      constructor
      · rintro ⟨j, c, _hc, _hp, hd, hstop⟩
        exact ⟨j, Nat.zero_le _, j.isLt, hd, hstop⟩
      · rintro ⟨j, _, _, hd, hstop⟩
        obtain ⟨c, hc, hp⟩ := (hcalendar j).2.2
        exact ⟨j, c, hc, hp, hd, hstop⟩
    refine ⟨registers, owned, base, seg, hstate, hat, hentry, hpayload, hne,
      hcalendar, (fun j => slot_record_actual_lookup rate rewards C_star C_h z
        (i.val + j.val) seg.records[j.val] (hcalendar j).1), hCiff, ?_⟩
    have hsegpos : 0 < seg.records.length := List.length_pos_iff.mpr hne
    rcases hend with hterminal | ⟨b, hbi, hb, hexit, _hdrop, saved,
      hbstate, hempty, _hrawEnd, hnoC, newPayload, hbirth, hfields, _hclear, _hnested⟩
    · left
      change i.val + seg.records.length = R.length at hterminal
      refine ⟨hterminal, ?_, ?_, ?_⟩
      · have hgap : ∀ j : Fin R.length, i.val < j.val → j.val < R.length →
            ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
              rate rewards C_star C_h R[j.val].input.time z := by
          intro j hij _hjR
          let c : Fin seg.records.length := ⟨j.val - i.val, by omega⟩
          have hslot := (hcalendar c).1
          have hindex : i.val + c.val = j.val := by dsimp only [c]; omega
          rw [hindex, List.getElem?_eq_getElem j.isLt] at hslot
          rw [Option.some.inj hslot]
          exact hno c (by dsimp only [c]; omega)
        exact stopped_end_eq_clipped_raw_boundary rate rewards C_star C_h k z
          i.val R.length hk hi i.isLt le_rfl hgap (by
            intro hn
            change R.length < R.length at hn
            exact (Nat.lt_irrefl _ hn).elim)
      · intro j hji
        have hjR : j.val < R.length := j.isLt
        exact (_hchoice j hji (by omega)).mpr (by omega)
      · rintro ⟨b, hb⟩
        have hbR : b.val < R.length := b.isLt
        omega
    · right
      let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      let h := (V.takeWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length
      obtain ⟨hnR, _hVgap, hboundary⟩ := installed_raw_boundary
        rate rewards C_star C_h z b hb
      change b.val + V.length ≤ R.length at hnR
      have hgap := collection_installed_raw_gap rate rewards C_star C_h z
        i.val seg hat b hbi hb
      have hVpos : 0 < V.length := by simp only [V, List.length_cons]; omega
      have hE : E = s + min (b.val + V.length) B + 1 :=
        stopped_end_eq_clipped_raw_boundary rate rewards C_star C_h k z
          i.val (b.val + V.length) hk hi (by omega) hnR hgap hboundary
      have hs := present_start_before_bad_boundary rate rewards C_star C_h k z i.val hk hi
      have hlength : R.length = p.T - s :=
        ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
      have hclip : ∀ d : ℕ, d < E ↔ d < s + b.val + V.length + 1 ∧
          d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
        intro d
        rw [hE]
        simpa only [B, Nat.add_assoc] using clipped_date_membership_iff s
          (b.val + V.length) d
          (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z)
          p.T hs (by rw [← hlength]; exact hnR)
      have hglobal (j : Fin R.length) :
          (i.val ≤ j.val ∧ R[j.val].input.time.val + 1 < E) ↔
            i.val ≤ j.val ∧ j.val < b.val + V.length ∧
              R[j.val].input.time.val + 1 ≤
                ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z :=
        and_congr_right (fun _ => original_record_clipping_iff rate rewards C_star C_h z
          (b.val + V.length) E (by simpa only [Nat.add_assoc] using hclip) j)
      have hdates : ∀ j : Fin V.length,
          V[j.val].input.time.val + 1 = (s + b.val) + j.val + 1 :=
        fun j => (hfields j).2.1
      have hpending := indexed_pending_fields V (s + b.val) h newPayload hdates
        (fun j => (hfields j).2.2)
      have hselected (j : Fin V.length) : ∃ selected : Selection V[j.val].input,
          V[j.val].output.preparation.coordinator.selection = some selected ∧
          (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
          (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val) := by
        obtain ⟨selected, hs, _hp, hm, he⟩ := hpending j
        exact ⟨selected, hs, hm, he⟩
      have hh : h ≤ V.length := (List.takeWhile_prefix _).length_le
      obtain ⟨hHiff, hRiff⟩ := selected_phase_dates_iff V (s + b.val) h E hh
        hdates hselected
      refine ⟨b, hbi, hb, hexit, ⟨saved, hbstate⟩, hempty,
        hnR, hE, hclip, hglobal, newPayload, hbirth, ?_,
        (fun j => slot_record_actual_lookup rate rewards C_star C_h z
          (b.val + j.val) V[j.val] (hfields j).1), hHiff, hRiff, ?_, ?_⟩
      · intro j
        exact ⟨(hfields j).1, (hfields j).2.1, hnoC j, hpending j⟩
      · intro hclipped d hrelease
        have hd := (hRiff d).mp hrelease
        change E ≤ s + b.val + h + 1 at hclipped
        omega
      · apply later_release_after_clipping rate rewards C_star C_h z b hb E
        change E ≤ s + b.val + V.length + 1
        rw [hE]
        have := Nat.min_le_left (b.val + V.length) B
        omega

/-- The rank at the genuine launch has empty C. Its actual raw initial
window supplies the new-payload H/R fields; analytic clipping is applied only
after identifying its actual next cutoff or horizon. The branch localizer is
only equality of the ranked start with the original launch date. -/
public theorem initial_rank_stopped_transfer_phase_intervals
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T)
    (hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
      rate rewards C_star C_h k z
    let h := ReferenceOriginalInitialTransferWindowGeometry.rawMissingPrefixLength
      rate rewards C_star C_h z
    0 < W.length ∧
    E = s + min W.length
      (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T - s) + 1 ∧
    (∀ d : ℕ, d < E ↔ d < s + W.length + 1 ∧
      d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) ∧
    (∀ j : Fin R.length,
      R[j.val].input.time.val + 1 < E ↔ j.val < W.length ∧
        R[j.val].input.time.val + 1 ≤
          ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) ∧
    ∃ newPayload : Payload rate,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
        rate rewards C_star C_h z = some newPayload ∧
      (∀ j : Fin W.length,
        R[j.val]? = some W[j.val] ∧ W[j.val].input.time.val + 1 = s + j.val + 1 ∧
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h W[j.val].input.time z = some W[j.val] ∧
        choice W[j.val].input = none ∧
        ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = newPayload ∧
          (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
          (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val)) ∧
      (∀ d : ℕ, ¬ (∃ j : Fin W.length, ∃ c : Choice rate,
        choice W[j.val].input = some c ∧ W[j.val].input.time.val + 1 = d ∧ d < E)) ∧
      (∀ d : ℕ,
        (∃ j : Fin W.length, ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice.Nonempty ∧
          W[j.val].input.time.val + 1 = d ∧ d < E) ↔
          s + 1 ≤ d ∧ d < min (s + h + 1) E) ∧
      (∀ d : ℕ,
        (∃ j : Fin W.length, ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          W[j.val].input.time.val + 1 = d ∧ d < E) ↔
          s + h + 1 ≤ d ∧ d < min (s + W.length + 1) E) ∧
      (E ≤ s + h + 1 → ∀ d : ℕ,
        ¬ (∃ j : Fin W.length, ∃ selected : Selection W[j.val].input,
          W[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          W[j.val].input.time.val + 1 = d ∧ d < E)) ∧
      (s + h + 1 < E →
        ∃ (j : Fin W.length) (hn : j.val + 1 < W.length),
          j.val + 1 = h ∧ W[j.val].input.time.val + 1 < E ∧
          ∃ selected : Selection W[j.val].input,
            W[j.val].output.preparation.coordinator.selection = some selected ∧
            ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent W[j.val] selected ∧
            selected.view.pendingAtChoice =
              {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (W[j.val].input.row.2 W[j.val].input.time).1} ∧
            R[j.val]? = some W[j.val] ∧
            R[j.val + 1]? = some (W[j.val + 1]'hn) ∧
            (W[j.val + 1]'hn).input.time.val = W[j.val].input.time.val + 1 ∧
            (W[j.val + 1]'hn).input.time.val + 1 < E ∧
            ∃ nextSelected : Selection (W[j.val + 1]'hn).input,
              (W[j.val + 1]'hn).output.preparation.coordinator.selection = some nextSelected ∧
              nextSelected.view.pendingAtChoice = ∅) := by
  intro R W s E h
  obtain ⟨q, i, _record, hq, hi, _hr, _hbranch⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.present_start_actual_suffix_record
      rate rewards C_star C_h k z hk
  have hRpos : 0 < R.length := by
    have hiR : i.val < R.length := i.isLt
    omega
  let zero : Fin R.length := ⟨0, hRpos⟩
  have htime : R[0].input.time.val = s := by
    have hdate := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
      rate rewards C_star C_h z zero
    change R[0].input.time.val + 1 = s + 0 + 1 at hdate
    omega
  have hmarker :=
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_of_launch
      rate rewards C_star C_h R[0].input.time z htime
  obtain ⟨first, hlookup, hfirst⟩ :=
    (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
      rate rewards C_star C_h R[0].input.time z).mp hmarker
  have hactual := suffix_record_actual_lookup rate rewards C_star C_h z zero
  have hsame : first = R[0] := Option.some.inj (hlookup.symm.trans hactual)
  have hfirst0 : R[0].input.state.coordinator = .first := hsame ▸ hfirst
  have hWpos : 0 < W.length := by
    by_contra hnot
    have hzero : W.length = 0 := by omega
    obtain ⟨r, hr, _hd, hc, _hl⟩ :=
      ReferenceOriginalInitialTransferWindowGeometry.raw_first_excluded_record
        rate rewards C_star C_h z (show W.length < R.length by omega)
    change R[W.length] = r at hr
    have hr0 : R[0] = r := by simpa only [hzero] using hr
    have hcut0 : ReferenceCollectionPhaseHistory.cutoffChosen R[0].input = false := by
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, prepare,
        dispatch_first R[0].input hfirst0]
    rw [← hr0, hcut0] at hc
    cases hc
  obtain ⟨hnR, hgap, hboundary⟩ := initial_raw_boundary rate rewards C_star C_h z
  change W.length ≤ R.length at hnR
  have hE : E = s + min W.length
      (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h z) p.T - s) + 1 := by
    simpa only [Nat.add_zero] using stopped_end_eq_clipped_raw_boundary
      rate rewards C_star C_h k z 0 W.length hk (by simpa only [Nat.add_zero] using hstart)
      hWpos hnR hgap hboundary
  have hs := present_start_before_bad_boundary rate rewards C_star C_h k z 0 hk
    (by simpa only [Nat.add_zero] using hstart)
  have hlength : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hclip : ∀ d : ℕ, d < E ↔ d < s + W.length + 1 ∧
      d ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
    intro d
    rw [hE]
    exact clipped_date_membership_iff s W.length d
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T
      hs (by rw [← hlength]; exact hnR)
  have hglobal := original_record_clipping_iff rate rewards C_star C_h z W.length E hclip
  obtain hzero | ⟨newPayload, hpayload0, hfields⟩ :=
    initial_raw_indexed_fields rate rewards C_star C_h z
  · change W.length = 0 at hzero
    omega
  ·
    have hdates : ∀ j : Fin W.length, W[j.val].input.time.val + 1 = s + j.val + 1 :=
      fun j => (hfields j).2.1
    have hselected : ∀ j : Fin W.length, ∃ selected : Selection W[j.val].input,
        W[j.val].output.preparation.coordinator.selection = some selected ∧
        (selected.view.pendingAtChoice.Nonempty ↔ j.val < h) ∧
        (selected.view.pendingAtChoice = ∅ ↔ h ≤ j.val) := by
      intro j
      obtain ⟨selected, hs, _hp, hm, he⟩ := (hfields j).2.2.2.2
      exact ⟨selected, hs, hm, he⟩
    have hh : h ≤ W.length := (List.takeWhile_prefix _).length_le
    obtain ⟨hHiff, hRiff⟩ := selected_phase_dates_iff W s h E hh hdates hselected
    have hCempty (d : ℕ) : ¬ (∃ j : Fin W.length, ∃ c : Choice rate,
        choice W[j.val].input = some c ∧ W[j.val].input.time.val + 1 = d ∧ d < E) := by
      rintro ⟨j, c, hc, _hd, _hstop⟩
      rw [(hfields j).2.2.2.1] at hc
      cases hc
    refine ⟨hWpos, hE, hclip, hglobal, newPayload, hpayload0,
      hfields, hCempty, hHiff, hRiff, ?_, ?_⟩
    · intro hclipped d hrelease
      have hd := (hRiff d).mp hrelease
      change E ≤ s + h + 1 at hclipped
      omega
    · apply initial_release_after_clipping rate rewards C_star C_h z E
      change E ≤ s + W.length + 1
      rw [hE]
      have := Nat.min_le_left W.length
        (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T - s)
      omega

/-- A present stopped rank has an exact original suffix record witness, and
its right endpoint is the accepted next rank or the inclusive first-bad/horizon
boundary. The raw C/H/R field assembly is developed from the same source in
the private boundary lemmas above. -/
public theorem present_stopped_transfer_rank_endpoint
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let startDate := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z
    let nextDate := ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
      rate rewards C_star C_h k z
    let stopDate := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
      rate rewards C_star C_h k z
    ∃ (q : Fin p.T) (i : Fin R.length)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      q.val + 1 = startDate ∧ s + i.val = q.val ∧ R[i.val] = record ∧
      (record.input.state.coordinator = .first ∨
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ)
          (started : CoordinatorPhaseClock.StartRoundResult p),
          record.input.state.coordinator = .live registers owned base ∧
          CoordinatorPhaseClock.startRound p rate.eta.val q registers.priorClock
            registers.clockPending = .ok started ∧
          started.ledgerCommand = some (.initializeAt q)) ∧
      (nextDate ≤ p.T → stopDate = nextDate) ∧
      (nextDate = p.T + 1 → stopDate =
        min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T + 1) := by
  intro R s startDate nextDate stopDate
  obtain ⟨q, i, record, hdate, hindex, hrecord, hbranch⟩ :=
    ReferenceOriginalTransferPhysicalIntervals.present_start_actual_suffix_record
      rate rewards C_star C_h k z hk
  refine ⟨q, i, record, hdate, hindex, hrecord, hbranch, ?_, ?_⟩
  · intro hnext
    exact ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate_eq_next_of_present
      rate rewards C_star C_h k z hk hnext
  · intro hnext
    exact ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate_eq_bad_boundary_of_no_next
      rate rewards C_star C_h k z hnext

/-- An absent rank has no stopped phase date at all. This includes no-launch,
terminal-crossing, and ranks beyond a prior inclusive stop. -/
public theorem absent_stopped_transfer_phase_dates_empty
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (z : SourceInput p)
    (hk : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T) :
    ∀ d : ℕ,
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ d →
      d < ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
        rate rewards C_star C_h k z → False :=
  ReferenceOriginalTransferPhysicalIntervals.absent_stoppedTransferWindow_empty
    rate rewards C_star C_h k z hk

end Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals

end
