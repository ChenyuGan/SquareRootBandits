/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRawCalendarNumericalCoverage

import Lean.Elab.Tactic.Omega

/-!
# The raw first-collection queue stopping calendar

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-278`,
`sources/zip4/manuscript/06_interruptions.tex:355-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64`.

The whole numerical prefix at a later original raw date determines queue
retention at every earlier original raw date. On a nonempty raw collection
window its actual last cell supplies one common endpoint. The literal finite
calendar intersects the original dates with their actual strict-past queue
event. No decoder stop, queue probability, or complete stopped charge is claimed.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRawQueueStoppingCalendar


abbrev Cell (p : ConstructorDimensions.Parameters) := RecordedQueueRun.RoundInput p.K

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

theorem original_raw_calendar_date
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
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length)[k.val]'k.isLt).input.time.val =
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

variable {p : ConstructorDimensions.Parameters}

/-- At an in-list date, the endpoint tests precisely whether its strict past
precedes the first crossing. In the no-crossing branch both tests hold. -/
private theorem before_endpoint_iff
    (rate : ReferenceActivePhysicalStep.RateInput p) (s n : ℕ)
    (L : List (Cell p)) (hn : n < L.length) (ht : s + n < p.T) :
    s + n + 1 < ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate s L ↔
      n < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L := by
  unfold ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
  dsimp only
  split_ifs with hk
  · rw [Nat.lt_min]
    omega
  · omega

/-- Restriction of the entire numerical list preserves the strict-past test,
even when a future first crossing replaces the earlier sentinel endpoint. -/
private theorem kept_date_comparison
    (rate : ReferenceActivePhysicalStep.RateInput p) (s : ℕ)
    (N : List (Cell p)) (c : Cell p) (L : List (Cell p))
    (hprefix : N ++ [c] = L.take (N.length + 1))
    (hn : N.length < L.length) (ht : s + N.length < p.T) :
    s + N.length + 1 < ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate s (N ++ [c]) ↔
      s + N.length + 1 < ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate s L := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hpast : N = L.take N.length := by
    have hh := congrArg (List.take N.length) hprefix
    simpa [List.take_take] using hh
  have hlocal := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    q (N ++ [c]) N.length (by simp)
  have hlater := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    q L N.length (Nat.le_of_lt hn)
  have htake : (N ++ [c]).take N.length = N := by simp
  rw [htake] at hlocal
  rw [← hpast] at hlater
  have hcross : N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix q (N ++ [c]) ↔
      N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix q L := by
    have hh := not_congr (hlocal.symm.trans hlater)
    simpa only [not_le] using hh
  exact (before_endpoint_iff rate s N.length (N ++ [c]) (by simp) ht).trans
    (hcross.trans (before_endpoint_iff rate s N.length L hn ht).symm)

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "b" =>
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "w" => List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R)
local notation "B" => ReferenceCollectionPhaseHistory.collectionWindow R w
local notation "omega" =>
  ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The original raw dates are strictly chronological. -/
theorem original_raw_calendar_strictMono :
    StrictMono (fun k : Fin (B).length => B[k.val].input.time) := by
  intro k0 k1 hk
  change B[k0.val].input.time.val < B[k1.val].input.time.val
  rw [original_raw_calendar_date rate rewards C_star C_h z k0,
    original_raw_calendar_date rate rewards C_star C_h z k1]
  exact Nat.add_lt_add_left hk _

/-- In particular distinct original raw cells cannot count the same date. -/
theorem original_raw_calendar_injective :
    Function.Injective (fun k : Fin (B).length => B[k.val].input.time) :=
  (original_raw_calendar_strictMono rate rewards C_star C_h z).injective

/-- One later full pair supplies the common first-overflow endpoint for every
earlier original raw date. Both pairs are uniquely characterized by all their
numerical fields, and the earlier whole list is the later whole prefix. -/
theorem original_raw_calendar_common_prefix_endpoint :
    ∀ k1 : Fin (B).length,
      ∃! pair1 : List (Cell p) × Cell p,
        ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
          rate b (b + w) B[k1.val].input.time omega pair1.1 pair1.2 ∧
        ∀ k0 : Fin (B).length, k0 ≤ k1 →
          ∃! pair0 : List (Cell p) × Cell p,
            ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
              rate b (b + w) B[k0.val].input.time omega pair0.1 pair0.2 ∧
            pair0.1 ++ [pair0.2] =
              (pair1.1 ++ [pair1.2]).take (pair0.1.length + 1) ∧
            (z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) b (b + w) B[k0.val].input.time ↔
              B[k0.val].input.time.val + 1 <
                ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
                  rate b (pair1.1 ++ [pair1.2])) := by
  intro k1
  obtain ⟨hbu1, hut1, _hw1, _hC1, pair1, hm1, hu1⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
      rate rewards C_star C_h z k1
  refine ⟨pair1, ⟨hm1, ?_⟩, fun pair hp => hu1 pair hp.1⟩
  intro k0 hk
  obtain ⟨hbu0, hut0, _hw0, hC0, _unique0⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
      rate rewards C_star C_h z k0
  obtain ⟨pair0, ⟨hm0, later, ⟨hmlater, hwhole⟩, _⟩, hu0⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_prefix_coherence
      rate rewards C_star C_h z k0 k1 hk
  have heq : later = pair1 := hu1 later hmlater
  subst later
  refine ⟨pair0, ⟨hm0, hwhole, ?_⟩, ?_⟩
  · have hlocal := ReferenceFirstCollectionQueuePrefixChronology.actual_local_overflow_date
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      z hbu0 hut0 hC0 pair0.1 pair0.2 hm0
    have hdate : B[k0.val].input.time.val ≤ B[k1.val].input.time.val :=
      (original_raw_calendar_strictMono rate rewards C_star C_h z).monotone hk
    have htime0 : B[k0.val].input.time.val = b + pair0.1.length := by
      have hlen := hm0.1
      omega
    have hlen : pair0.1.length < (pair1.1 ++ [pair1.2]).length := by
      have hlen1 := hm1.1
      simp only [List.length_append, List.length_singleton]
      omega
    have hcompare := kept_date_comparison rate b pair0.1 pair0.2
      (pair1.1 ++ [pair1.2]) hwhole hlen (by rw [← htime0]; exact Fin.isLt _)
    rw [← htime0] at hcompare
    exact hlocal.trans hcompare
  · intro pair hp
    exact hu0 pair ⟨hp.1, ⟨pair1, ⟨hm1, hp.2.1⟩, fun q hq => hu1 q hq.1⟩⟩

/-- Every finite-prefix endpoint is between the first potentially excluded
one-based date and the horizon sentinel. -/
private theorem endpoint_bounds (s : ℕ) (L : List (Cell p)) :
    2 ≤ ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate s L ∧
      ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate s L ≤ p.T + 1 := by
  have hpos := UnstoppedRecordedQueueComparison.first_overflow_prefix_pos qp L
  have hT := p.one_le_T
  unfold ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
  dsimp only
  split_ifs
  · constructor
    · exact Nat.le_min.mpr ⟨by omega, by omega⟩
    · exact Nat.min_le_left _ _
  · omega

/-- A nonempty original window has one uniquely matched actual last pair.
That pair fixes the common endpoint; uniqueness is of the pair, not an
unsupported assertion that retained-date comparisons determine an endpoint. -/
theorem original_raw_calendar_last_endpoint (hB : B ≠ []) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
        rate b (b + w) (List.getLast B hB).input.time omega pair.1 pair.2 ∧
      2 ≤ ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate b (pair.1 ++ [pair.2]) ∧
      ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate b (pair.1 ++ [pair.2]) ≤ p.T + 1 ∧
      ∀ k : Fin (B).length,
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) b (b + w) B[k.val].input.time ↔
        B[k.val].input.time.val + 1 <
          ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded rate b (pair.1 ++ [pair.2]) := by
  have hpos : 0 < (B).length := List.length_pos_iff.mpr hB
  let last : Fin (B).length := ⟨(B).length - 1, by omega⟩
  have hlast : B[last.val] = List.getLast B hB := by
    simp only [List.getLast_eq_getElem, last]
  obtain ⟨pair, ⟨hm, hall⟩, hu⟩ :=
    original_raw_calendar_common_prefix_endpoint rate rewards C_star C_h z last
  have hbds := endpoint_bounds rate b (pair.1 ++ [pair.2])
  refine ⟨pair, ⟨by simpa only [hlast] using hm, hbds.1, hbds.2, ?_⟩, ?_⟩
  · intro k
    obtain ⟨_pair0, ⟨_hm0, _hwhole, hevent⟩, _⟩ := hall k (by change k.val ≤ (B).length - 1; omega)
    exact hevent
  · intro other ho
    exact ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      b (b + w) (List.getLast B hB).input.time omega ho.1 (by simpa only [hlast] using hm)

/-- Literal original raw dates intersected with the actual queue event at
exactly the physical first start and first cutoff. -/
noncomputable def rawQueueCalendar : Finset (Fin p.T) :=
  (Finset.univ.image (fun k : Fin (B).length => B[k.val].input.time)).filter
    (fun t => z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) b (b + w) t)

/-- Exact literal membership, including the original raw-date requirement. -/
theorem mem_rawQueueCalendar_iff (t : Fin p.T) :
    t ∈ rawQueueCalendar rate rewards C_star C_h z ↔
      (∃ k : Fin (B).length, B[k.val].input.time = t) ∧
      z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) b (b + w) t := by
  simp only [rawQueueCalendar, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]

/-- Empty original windows have empty raw queue calendars, without a default
prefix or a fictitious last cell. -/
theorem rawQueueCalendar_eq_empty_of_window_empty (hB : B = []) :
    rawQueueCalendar rate rewards C_star C_h z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨⟨k, _⟩, _⟩ := (mem_rawQueueCalendar_iff rate rewards C_star C_h z t).mp ht
  have hk := k.isLt
  have hlen : (B).length = 0 := by rw [hB]; rfl
  omega

/-- Original raw dates are exactly the contiguous calendar interval of the
actual collection window. This also covers the empty-window case. -/
theorem original_raw_dates_iff (t : Fin p.T) :
    (∃ k : Fin (B).length, B[k.val].input.time = t) ↔
      b + w ≤ t.val ∧ t.val < b + w + (B).length := by
  constructor
  · rintro ⟨k, hk⟩
    have hdate := original_raw_calendar_date rate rewards C_star C_h z k
    have ht := congrArg Fin.val hk
    have hlen := k.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    let k : Fin (B).length := ⟨t.val - (b + w), by omega⟩
    refine ⟨k, Fin.ext ?_⟩
    rw [original_raw_calendar_date rate rewards C_star C_h z k]
    change b + w + (t.val - (b + w)) = t.val
    omega

/-- The actual last full pair gives the exact finite calendar prefix and its
count. The image is injective, so no raw date is counted twice. -/
theorem original_raw_queue_calendar_characterization (hB : B ≠ []) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
        rate b (b + w) (List.getLast B hB).input.time omega pair.1 pair.2 ∧
      let e := ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
        rate b (pair.1 ++ [pair.2])
      let indices := (Finset.univ : Finset (Fin (B).length)).filter
        (fun k => B[k.val].input.time.val + 1 < e)
      2 ≤ e ∧ e ≤ p.T + 1 ∧
      (∀ t : Fin p.T,
        t ∈ rawQueueCalendar rate rewards C_star C_h z ↔
          b + w ≤ t.val ∧ t.val < b + w + (B).length ∧ t.val + 1 < e) ∧
      rawQueueCalendar rate rewards C_star C_h z =
        indices.image (fun k => B[k.val].input.time) ∧
      (rawQueueCalendar rate rewards C_star C_h z).card = indices.card := by
  obtain ⟨pair, ⟨hm, hlo, hhi, hall⟩, _hu⟩ :=
    original_raw_calendar_last_endpoint rate rewards C_star C_h z hB
  let e := ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
    rate b (pair.1 ++ [pair.2])
  let indices := (Finset.univ : Finset (Fin (B).length)).filter
    (fun k => B[k.val].input.time.val + 1 < e)
  have hmem (t : Fin p.T) :
      t ∈ rawQueueCalendar rate rewards C_star C_h z ↔
        b + w ≤ t.val ∧ t.val < b + w + (B).length ∧ t.val + 1 < e := by
    rw [mem_rawQueueCalendar_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, hq⟩
      have hbounds := (original_raw_dates_iff rate rewards C_star C_h z t).mp ⟨k, hk⟩
      have hevent : B[k.val].input.time.val + 1 < e := (hall k).mp (by simpa only [hk] using hq)
      exact ⟨hbounds.1, hbounds.2, by simpa only [hk] using hevent⟩
    · rintro ⟨hlo', hhi', he⟩
      obtain ⟨k, hk⟩ := (original_raw_dates_iff rate rewards C_star C_h z t).mpr ⟨hlo', hhi'⟩
      refine ⟨⟨k, hk⟩, ?_⟩
      have hq := (hall k).mpr (by simpa only [hk] using he)
      simpa only [hk] using hq
  have himage : rawQueueCalendar rate rewards C_star C_h z =
      indices.image (fun k => B[k.val].input.time) := by
    ext t
    rw [mem_rawQueueCalendar_iff]
    simp only [Finset.mem_image, indices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, hk⟩, hq⟩
      exact ⟨k, (hall k).mp (by simpa only [hk] using hq), hk⟩
    · rintro ⟨k, he, hk⟩
      exact ⟨⟨k, hk⟩, by simpa only [hk] using (hall k).mpr he⟩
  refine ⟨pair, ⟨hm, hlo, hhi, hmem, himage, ?_⟩, ?_⟩
  · rw [himage]
    exact Finset.card_image_of_injective indices
      (original_raw_calendar_injective rate rewards C_star C_h z)
  · intro other ho
    exact ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      b (b + w) (List.getLast B hB).input.time omega ho.1 hm

/-- At an actual detecting raw cell its unique pair determines the crossing's
actual date. That cell is retained and every later original raw date is
excluded, with no no-overflow premise on the full detecting prefix. -/
theorem original_raw_calendar_first_detecting_cell :
    ∀ k0 : Fin (B).length,
      ∃! pair : List (Cell p) × Cell p,
        ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
          rate b (b + w) B[k0.val].input.time omega pair.1 pair.2 ∧
        (UnstoppedRecordedQueueComparison.firstOverflowPrefix qp (pair.1 ++ [pair.2]) =
            pair.1.length + 1 →
          B[k0.val].input.time.val =
            b + UnstoppedRecordedQueueComparison.firstOverflowPrefix
              qp (pair.1 ++ [pair.2]) - 1 ∧
          B[k0.val].input.time ∈ rawQueueCalendar rate rewards C_star C_h z ∧
          (∀ k1 : Fin (B).length, k0 < k1 →
            B[k1.val].input.time ∉ rawQueueCalendar rate rewards C_star C_h z) ∧
          (∀ k1 : Fin (B).length, k0 ≤ k1 →
            ∃! later : List (Cell p) × Cell p,
              ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches
                rate b (b + w) B[k1.val].input.time omega later.1 later.2 ∧
              UnstoppedRecordedQueueComparison.firstOverflowPrefix
                qp (later.1 ++ [later.2]) = pair.1.length + 1 ∧
              ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
                rate b (later.1 ++ [later.2]) =
                  min (p.T + 1) (B[k0.val].input.time.val + 2))) := by
  intro k0
  obtain ⟨hbu, hut, _hw, hC, pair, hm, hu⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
      rate rewards C_star C_h z k0
  refine ⟨pair, ⟨hm, ?_⟩, fun other ho => hu other ho.1⟩
  intro hcross
  have htime : B[k0.val].input.time.val = b + pair.1.length := by
    have hlen := hm.1
    omega
  have hq0 : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      b (b + w) B[k0.val].input.time := by
    apply (ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_iff_before_current_firstOverflow
      b (b + w) B[k0.val].input.time hbu hut z hC pair.1 pair.2 hm).mpr
    rw [hcross]
    omega
  refine ⟨by rw [hcross]; omega, ?_, ?_, ?_⟩
  · exact (mem_rawQueueCalendar_iff rate rewards C_star C_h z _).mpr ⟨⟨k0, rfl⟩, hq0⟩
  · intro k1 hk hmem
    have hq1 := ((mem_rawQueueCalendar_iff rate rewards C_star C_h z _).mp hmem).2
    obtain ⟨_hbu1, _hut1, _hw1, hC1, _pair1⟩ :=
      ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
        rate rewards C_star C_h z k1
    have hdates := original_raw_calendar_strictMono rate rewards C_star C_h z hk
    exact (ReferenceFirstCollectionQueuePrefixChronology.actual_current_first_crossing
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      hbu hut hdates hC1 pair.1 pair.2 hm hcross).2 hq1
  · intro k1 hk
    obtain ⟨_hbu1, _hut1, _hw1, _hC1, later, hmlater, hulater⟩ :=
      ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
        rate rewards C_star C_h z k1
    have hdates := (original_raw_calendar_strictMono rate rewards C_star C_h z).monotone hk
    have hwhole := ReferenceFirstCollectionQueuePrefixChronology.whole_matches_prefix
      rate B[k0.val].input.time B[k1.val].input.time hbu hut hdates omega
      pair.1 later.1 pair.2 later.2 hm hmlater
    have hstable := ReferenceFirstCollectionQueuePrefixChronology.first_crossing_date_stable
      rate b (pair.1 ++ [pair.2]) (later.1 ++ [later.2])
      (by simpa only [List.length_append, List.length_singleton] using hwhole)
      (by rw [hcross]; simp)
    have hendpoint : ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
        rate b (pair.1 ++ [pair.2]) = min (p.T + 1) (B[k0.val].input.time.val + 2) := by
      unfold ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
      dsimp only
      rw [hcross]
      simp only [List.length_append, List.length_singleton, le_refl, ite_true]
      congr 1
      omega
    exact ⟨later, ⟨hmlater, hstable.1.trans hcross, hstable.2.trans hendpoint⟩,
      fun other ho => hulater other ho.1⟩

end Actual

end Bandits.Support.ReferenceFirstCollectionRawQueueStoppingCalendar
