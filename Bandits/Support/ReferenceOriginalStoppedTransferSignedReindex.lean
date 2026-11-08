/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalTransferPhysicalIntervals
public import Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover

import Mathlib.Tactic

/-!
# Signed charge over actual ranked stopped transfer windows

The actual ranked starts partition the original retained calendar suffix.
Each window keeps the actual date charge, including its unrestricted signed
release diagnostic, and their finite sum is the original stopped calendar
charge.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceOriginalStoppedTransferSignedReindex

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

/-- The actual source dates assigned to ranked stopped transfer `k`. -/
public def kthStoppedTransferWindowDates (k : Fin (p.T + 1)) : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ t.val + 1 ∧
      t.val + 1 < ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate rate rewards C_star C_h k z

/-- The actual signed calendar charge in ranked stopped transfer window `k`. -/
public def kthWindowSignedCharge (k : Fin (p.T + 1)) : ℝ :=
  ∑ t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k,
    ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge rate rewards C_star C_h z t

private theorem actualLaunchRound_eq_physicalStart_succ :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hround := ReferenceCompletePhysicalHistory.no_launch_sentinel_round
        rate z rewards C_star C_h hlaunch
      have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hlaunch
      change ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) = _
      rw [hround, hstart]
  | some active =>
      have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h).isSome = true := by
        rw [hlaunch]
        rfl
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp hsome
      have hcross' : (ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome = true := by
        simpa [ReferenceCompletePhysicalHistory.generatedInput] using hcross
      change ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
        ReferenceInitializationRun.elapsed p
          (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).completed + 1
      unfold ReferenceInitializationRun.launchRound
      rw [hcross']
      rfl

private theorem actualStart_date_ge_launch (q : Fin p.T)
    (hstart : ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q z) :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤ q.val + 1 := by
  rw [actualLaunchRound_eq_physicalStart_succ rate rewards C_star C_h z]
  rcases hstart with hmarker | hlive
  · rcases hmarker with ⟨_, htime, _⟩
    omega
  · have hafter := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_after_physicalStart
      rate rewards C_star C_h q z hlive
    omega

private theorem kth_window_mem_retained (k : Fin (p.T + 1))
    (t : Fin p.T)
    (ht : t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z := by
  have hwindow := (Finset.mem_filter.mp ht).2
  have hdate : t.val + 1 ≤ p.T := by omega
  have hpresent : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T :=
    le_trans hwindow.1 hdate
  have hmem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h k z).mp hpresent
  obtain ⟨q, hq, hqdate⟩ := (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
    rate rewards C_star C_h _ z).mp hmem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q z ∧ _ at hq
  have hlaunch := actualStart_date_ge_launch rate rewards C_star C_h z q hq.1
  have hend := hwindow.2
  have hboundary : t.val + 1 ≤
      min (ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z) p.T := by
    have hend' : t.val + 1 < min
        (ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
          rate rewards C_star C_h k z)
        (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z) p.T + 1) := by
      simpa [ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate] using hend
    have hlt := (Nat.lt_min.mp hend').2
    change t.val + 1 ≤ min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z) p.T
    exact Nat.le_of_lt_succ hlt
  have hlaunch' : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
      rate rewards C_star C_h z ≤
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z := by
    rw [hqdate] at hlaunch
    exact hlaunch
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact ⟨le_trans hlaunch' hwindow.1, hboundary⟩

/-- When the actual launch survives the inclusive stop, the earliest accepted
rank is the genuine initial transfer marker at that launch. -/
public theorem first_stopped_transfer_start_eq_launch
    (hretained : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤
      min (ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z) p.T) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h
      ⟨0, Nat.zero_lt_succ _⟩ z = ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z := by
  have hlaunch := actualLaunchRound_eq_physicalStart_succ rate rewards C_star C_h z
  have hphysical_lt : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < p.T := by
    omega
  let q : Fin p.T := ⟨ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
    hphysical_lt⟩
  have hmarker := ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_of_launch
    rate rewards C_star C_h q z rfl
  have hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt rate rewards C_star C_h q z := by
    change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q z ∧ _
    exact ⟨Or.inl hmarker, by rw [← hlaunch]; exact (Nat.le_min.mp hretained).1⟩
  have hdateMem : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ∈
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates rate rewards C_star C_h z := by
    exact (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).2 ⟨q, hstart, by rw [← hlaunch]⟩
  obtain ⟨j, hj, _hunique⟩ := ReferenceOriginalStoppedPhysicalTransferStarts.every_stoppedPhysicalTransferStartDate_occurs_once
    rate rewards C_star C_h (ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z) z hdateMem
  let zero : Fin (p.T + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hzeroj : zero ≤ j := Fin.zero_le j
  have hzero_le := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_monotone
    rate rewards C_star C_h zero j z hzeroj
  have hzero_upper : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h zero z ≤ p.T := by
    exact (hzero_le.trans (by simpa only [hj] using (Nat.le_min.mp hretained).2))
  have hzero_mem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h zero z).mp hzero_upper
  obtain ⟨q0, hq0, hq0date⟩ := (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
    rate rewards C_star C_h _ z).mp hzero_mem
  change ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q0 z ∧ _ at hq0
  have hzero_lower := actualStart_date_ge_launch rate rewards C_star C_h z q0 hq0.1
  rw [hq0date] at hzero_lower
  have hzero_le_launch : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h zero z ≤
        ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z := by
    rw [hj] at hzero_le
    exact hzero_le
  have hlaunch_le_zero : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
      rate rewards C_star C_h z ≤
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h zero z := by
    exact hzero_lower
  change ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h zero z =
        ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z
  exact Nat.le_antisymm hzero_le_launch hlaunch_le_zero

private theorem retained_start_count_pos (d : ℕ)
    (hd : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤ d)
    (hdT : d ≤ p.T)
    (hstop : d ≤ ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z) :
    0 < ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough rate rewards C_star C_h d z := by
  have hretained : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤
      min (ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z) p.T :=
    Nat.le_min.mpr ⟨hd.trans hstop, hd.trans hdT⟩
  have hfirst := first_stopped_transfer_start_eq_launch rate rewards C_star C_h z hretained
  have hfirst_le : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h
      ⟨0, Nat.zero_lt_succ _⟩ z ≤ d := by rw [hfirst]; exact hd
  exact (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
    rate rewards C_star C_h ⟨0, Nat.zero_lt_succ _⟩ d hdT z).mp hfirst_le

private theorem retained_date_has_ranked_window (t : Fin p.T)
    (ht : t ∈ ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z) :
    ∃ k : Fin (p.T + 1),
      t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k := by
  have hretained := (Finset.mem_filter.mp ht).2
  let d := t.val + 1
  have hdT : d ≤ p.T := (Nat.le_min.mp hretained.2).2
  have hstop : d ≤ ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z :=
    (Nat.le_min.mp hretained.2).1
  let n := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough rate rewards C_star C_h d z
  have hnpos : 0 < n := by
    exact retained_start_count_pos rate rewards C_star C_h z d hretained.1 hdT hstop
  have hnle : n ≤ p.T := by
    dsimp [n, ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough]
    calc
      _ ≤ (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds
          rate rewards C_star C_h z).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Finset.univ : Finset (Fin p.T)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = p.T := by simp
  let k : Fin (p.T + 1) := ⟨n - 1, by omega⟩
  have hklt : k.val < n := by dsimp [k]; omega
  have hstart_le := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
    rate rewards C_star C_h k d hdT z).2 (by simpa [n] using hklt)
  let next : Fin (p.T + 1) := ⟨n, by omega⟩
  have hnext_not : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h next z ≤ d := by
    intro hle
    have hcount := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h next d hdT z).mp hle
    simp [next, n] at hcount
  have hdate_lt_next : d < ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z := Nat.lt_of_not_ge hnext_not
  have hk_succ : k.val + 1 = n := by dsimp [k]; omega
  have hnext_eq : ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
      rate rewards C_star C_h k z =
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h next z := by
    change (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList
        rate rewards C_star C_h z).getD (k.val + 1) (p.T + 1) =
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartList
        rate rewards C_star C_h z).getD next.val (p.T + 1)
    rw [hk_succ]
  have hend : d < ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate rate rewards C_star C_h k z := by
    unfold ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rw [hnext_eq]
    apply Nat.lt_min.mpr
    constructor
    · exact hdate_lt_next
    · change d < min (ReferenceOriginalCalendarTransferPhaseCover.firstBadDate
        rate rewards C_star C_h z) p.T + 1
      exact Nat.lt_succ_of_le hretained.2
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact ⟨hstart_le, hend⟩

/-- Every retained source date belongs to precisely one actual ranked window. -/
public theorem kthStoppedTransferWindowDates_disjoint (k l : Fin (p.T + 1)) (hkl : k ≠ l) :
    Disjoint (kthStoppedTransferWindowDates rate rewards C_star C_h z k)
      (kthStoppedTransferWindowDates rate rewards C_star C_h z l) := by
  apply Finset.disjoint_left.mpr
  intro t htk htl
  have htk' := (Finset.mem_filter.mp htk).2
  have htl' := (Finset.mem_filter.mp htl).2
  rcases lt_or_gt_of_ne hkl with hkl' | hlk'
  · have hbound := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate_le_later_rank
      rate rewards C_star C_h k l z hkl'
    omega
  · have hbound := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate_le_later_rank
      rate rewards C_star C_h l k z hlk'
    omega

/-- Every retained source date belongs to precisely one actual ranked window. -/
public theorem retained_date_iff_exactly_one_ranked_window (t : Fin p.T) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z ↔
      ∃! k : Fin (p.T + 1),
        t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k := by
  constructor
  · intro ht
    obtain ⟨k, hk⟩ := retained_date_has_ranked_window rate rewards C_star C_h z t ht
    refine ⟨k, hk, ?_⟩
    intro l hl
    by_contra hne
    have hkl := kthStoppedTransferWindowDates_disjoint
      rate rewards C_star C_h z k l (Ne.symm hne)
    exact (Finset.disjoint_left.mp hkl) hk hl
  · rintro ⟨k, hk, _⟩
    exact kth_window_mem_retained rate rewards C_star C_h z k t hk

/-- The union of the actual ranked windows is the original retained suffix. -/
public theorem ranked_windows_biUnion_eq_retained_suffix :
    (Finset.univ : Finset (Fin (p.T + 1))).biUnion
        (kthStoppedTransferWindowDates rate rewards C_star C_h z) =
      ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z := by
  ext t
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact kth_window_mem_retained rate rewards C_star C_h z k t hk
  · intro ht
    exact retained_date_has_ranked_window rate rewards C_star C_h z t ht

/-- The sentinel and every absent ranked start have an empty actual window. -/
public theorem absent_ranked_window_empty (k : Fin (p.T + 1))
    (hk : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h k z ≤ p.T) :
    kthStoppedTransferWindowDates rate rewards C_star C_h z k = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro t ht
  have hwindow := (Finset.mem_filter.mp ht).2
  have hempty := ReferenceOriginalTransferPhysicalIntervals.absent_stoppedTransferWindow_empty
    rate rewards C_star C_h k z hk (t.val + 1) hwindow.1 hwindow.2
  exact hempty.elim

private theorem retained_suffix_empty_of_launch_after_first_bad
    (hbad : ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z <
      ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z) :
    ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro t ht
  have hmem := (Finset.mem_filter.mp ht).2
  omega

private theorem retained_suffix_empty_of_launch_beyond_horizon
    (hlaunch : p.T < ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
      rate rewards C_star C_h z) :
    ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro t ht
  have hmem := (Finset.mem_filter.mp ht).2
  omega

/-- With no generated launch, the source suffix and every ranked window are empty. -/
public theorem no_launch_suffix_empty
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z = ∅ := by
  have hround := ReferenceCompletePhysicalHistory.no_launch_sentinel_round
    rate z rewards C_star C_h hno
  have hlaunch : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z = p.T + 1 := by
    change ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) = p.T + 1
    exact hround
  apply retained_suffix_empty_of_launch_beyond_horizon rate rewards C_star C_h z
  rw [hlaunch]
  omega

/-- A terminal crossing has the launch sentinel and no retained source dates. -/
public theorem terminal_launch_suffix_empty (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z = ∅ := by
  have hround := (ReferenceCompletePhysicalHistory.terminal_crossing_sentinel_round
    rate z rewards C_star C_h active hlaunch hterminal).2
  have hlaunch' : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z = p.T + 1 := by
    change ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) = p.T + 1
    exact hround
  apply retained_suffix_empty_of_launch_beyond_horizon rate rewards C_star C_h z
  rw [hlaunch']
  omega

/-- If the inclusive bad date precedes launch, the retained suffix is empty. -/
public theorem suffix_empty_when_bad_date_precedes_launch
    (hbad : ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z <
      ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z) :
    ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z = ∅ :=
  retained_suffix_empty_of_launch_after_first_bad rate rewards C_star C_h z hbad

/-- Each window's charge is its capped collection/handover sum plus its
unrestricted signed release diagnostic sum. -/
public theorem kthWindowSignedCharge_eq_signed_phase_sums (k : Fin (p.T + 1)) :
    kthWindowSignedCharge rate rewards C_star C_h z k =
      (∑ t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k ∩
          (ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates rate rewards C_star C_h z ∪
            ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates rate rewards C_star C_h z),
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
      ∑ t ∈ kthStoppedTransferWindowDates rate rewards C_star C_h z k ∩
          ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates rate rewards C_star C_h z,
        ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t := by
  classical
  let window := kthStoppedTransferWindowDates rate rewards C_star C_h z k
  let ch := ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates rate rewards C_star C_h z ∪
    ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates rate rewards C_star C_h z
  let release := ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates rate rewards C_star C_h z
  have hpartition : window = (window ∩ ch) ∪ (window ∩ release) := by
    ext t
    constructor
    · intro ht
      have hret := kth_window_mem_retained rate rewards C_star C_h z k t ht
      have hphase := (ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_cover rate rewards C_star C_h z).symm ▸ hret
      rcases Finset.mem_union.mp hphase with hch | hrelease
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨ht, hch⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨ht, hrelease⟩))
    · intro ht
      rcases Finset.mem_union.mp ht with hch | hrelease
      · exact (Finset.mem_inter.mp hch).1
      · exact (Finset.mem_inter.mp hrelease).1
  have hdisjoint : Disjoint (window ∩ ch) (window ∩ release) := by
    apply Finset.disjoint_left.mpr
    intro t ht1 ht2
    have h1 := (Finset.mem_inter.mp ht1).2
    have h2 := (Finset.mem_inter.mp ht2).2
    have hpair := (ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_pairwise_disjoint
      rate rewards C_star C_h z).2.2
    have hchr : Disjoint ch release := by
      exact Finset.disjoint_union_left.mpr ⟨
        (ReferenceOriginalCalendarTransferPhaseCover.stopped_phase_dates_pairwise_disjoint rate rewards C_star C_h z).2.1,
        hpair⟩
    exact (Finset.disjoint_left.mp hchr) h1 h2
  have hchcharge (t : Fin p.T) (ht : t ∈ window ∩ ch) :
      ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge rate rewards C_star C_h z t =
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t := by
    have hret := kth_window_mem_retained rate rewards C_star C_h z k t
      (Finset.mem_inter.mp ht).1
    have hnone := (ReferenceOriginalCalendarTransferPhaseCover.retained_actual_observation_phase_characterization
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
      t hret).1.2 (Finset.mem_inter.mp ht).2
    simp [ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge, hnone]
  have hreleasecharge (t : Fin p.T) (ht : t ∈ window ∩ release) :
      ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge rate rewards C_star C_h z t =
        ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t := by
    have hret := kth_window_mem_retained rate rewards C_star C_h z k t
      (Finset.mem_inter.mp ht).1
    obtain ⟨e, y, delta, hobs⟩ :=
      (ReferenceOriginalCalendarTransferPhaseCover.retained_actual_observation_phase_characterization
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (z := z)
        t hret).2.2 (Finset.mem_inter.mp ht).2
    simp [ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge, ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta, hobs]
  calc
    kthWindowSignedCharge rate rewards C_star C_h z k =
        ∑ t ∈ window, ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge
          rate rewards C_star C_h z t := rfl
    _ = ∑ t ∈ (window ∩ ch) ∪ (window ∩ release),
        ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge
          rate rewards C_star C_h z t := by rw [← hpartition]
    _ = (∑ t ∈ window ∩ ch,
          ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge
            rate rewards C_star C_h z t) +
        ∑ t ∈ window ∩ release,
          ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge
            rate rewards C_star C_h z t := Finset.sum_union hdisjoint
    _ = (∑ t ∈ window ∩ ch,
          ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
        ∑ t ∈ window ∩ release,
          ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t := by
      congr 1
      · exact Finset.sum_congr rfl hchcharge
      · exact Finset.sum_congr rfl hreleasecharge
    _ = _ := rfl

/-- Summing actual ranked window charges reindexes to the original retained
calendar charge. -/
public theorem sum_kthWindowSignedCharge_eq_retained_calendar_charge :
    (∑ k : Fin (p.T + 1), kthWindowSignedCharge rate rewards C_star C_h z k) =
      ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.retainedSuffixDates rate rewards C_star C_h z,
        ReferenceOriginalCalendarTransferPhaseCover.actualDateCalendarCharge rate rewards C_star C_h z t := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (p.T + 1))))
      (kthStoppedTransferWindowDates rate rewards C_star C_h z) := by
    intro k hk l hl hne
    exact kthStoppedTransferWindowDates_disjoint rate rewards C_star C_h z k l hne
  unfold kthWindowSignedCharge
  rw [← Finset.sum_biUnion hdisjoint,
    ranked_windows_biUnion_eq_retained_suffix rate rewards C_star C_h z]

/-- The finite ranked-window sum is the same global capped C/H plus signed R
phase charge obtained from the accepted original calendar projection. -/
public theorem sum_kthWindowSignedCharge_eq_global_signed_phase_sum :
    (∑ k : Fin (p.T + 1), kthWindowSignedCharge rate rewards C_star C_h z k) =
      (∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates rate rewards C_star C_h z ∪
          ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates rate rewards C_star C_h z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
      ∑ t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates rate rewards C_star C_h z,
        ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t := by
  rw [sum_kthWindowSignedCharge_eq_retained_calendar_charge rate rewards C_star C_h z,
    ReferenceOriginalCalendarTransferPhaseCover.retained_suffix_dates_eq_calendar_projection rate rewards C_star C_h z]
  exact ReferenceOriginalCalendarTransferPhaseCover.actual_calendar_projection_signed_sum_eq_phase_sum
    rate rewards C_star C_h z

end Bandits.Support.ReferenceOriginalStoppedTransferSignedReindex

end
