/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport
public import Bandits.Support.ReferenceFirstCollectionQueuePrefixChronology
public import Bandits.Support.PhaseStartInclusiveCountWaiting

import Lean.Elab.Tactic.Omega

/-!
# Interval and inclusive-count support for awaited first collection

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240`,
`sources/zip4/manuscript/06_interruptions.tex:425-431,459-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.

The physical awaited support stays unchanged. These endpoints describe its
nonempty dates; queue chronology and the strict-past failure scan prove the
interval and nesting facts used by the phase waiting estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAwaitedPhaseSupport

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}

abbrev Awaited (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstCollectionAwaitedTaskSupport.Pawait rate rewards C_star C_h n z

private abbrev FailFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
    rate rewards C_star C_h n z

private abbrev RawPending (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h n z

/-- The exact finite calendar of nonempty dates of the existing awaited set. -/
def supportIndices (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset ℕ :=
  (Finset.range p.T).filter fun n =>
    (Awaited (rate := rate) (rewards := rewards) C_star C_h n z).Nonempty

/-- First included round, with the source horizon sentinel for empty support. -/
noncomputable def sigma (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).min' h + 1
  else p.T + 1

/-- First excluded round, with the same horizon sentinel for empty support. -/
noncomputable def theta (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).max' h + 2
  else p.T + 1

theorem mem_supportIndices_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) :
    n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z ↔
      n < p.T ∧
        (Awaited (rate := rate) (rewards := rewards) C_star C_h n z).Nonempty := by
  simp [supportIndices]

private theorem awaited_support_backward
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    {s n t : ℕ} (hsn : s ≤ n) (hnt : n ≤ t) (ht : t < p.T)
    (hstart : (Awaited (rate := rate) (rewards := rewards)
      C_star C_h s z).Nonempty)
    (hlater : (Awaited (rate := rate) (rewards := rewards)
      C_star C_h t z).Nonempty) :
    ∀ i : Fin (p.m - 1),
      i ∈ Awaited (rate := rate) (rewards := rewards) C_star C_h t z →
      i ∈ Awaited (rate := rate) (rewards := rewards) C_star C_h n z := by
  classical
  intro i hi
  have hsT : s < p.T := lt_of_le_of_lt (le_trans hsn hnt) ht
  have hnT : n < p.T := lt_of_le_of_lt hnt ht
  have hrawS : (RawPending (rate := rate) (rewards := rewards)
      C_star C_h s z).Nonempty := by
    rcases hstart with ⟨j, hj⟩
    exact ⟨j, (ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
      (rate := rate) (rewards := rewards) C_star C_h s z j).1 hj |>.2⟩
  have hrawT : (RawPending (rate := rate) (rewards := rewards)
      C_star C_h t z).Nonempty := by
    rcases hlater with ⟨j, hj⟩
    rcases (ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
      (rate := rate) (rewards := rewards) C_star C_h t z j).1 hj with ⟨_, hraw⟩
    exact ⟨j, hraw⟩
  obtain ⟨pairS, hpairS⟩ :=
    (ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      ⟨s, hsT⟩ z hrawS).exists
  obtain ⟨pairT, hpairT⟩ :=
    (ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      ⟨t, ht⟩ z hrawT).exists
  dsimp only at hpairS hpairT
  rcases pairS with ⟨s0, u0⟩
  rcases pairT with ⟨s1, u1⟩
  rcases hpairS with ⟨hsu0, huS, hCS, hs0, hu0, _⟩
  rcases hpairT with ⟨hsu1, huT, hCT, hs1, hu1, _⟩
  change s0 ≤ u0 at hsu0
  change u0 ≤ s at huS
  change s0 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at hs0
  change u0 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length at hu0
  change s1 ≤ u1 at hsu1
  change u1 ≤ t at huT
  change s1 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at hs1
  change u1 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length at hu1
  have hs01 : s0 = s1 := hs0.trans hs1.symm
  have hu01 : u0 = u1 := by
    calc
      u0 = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length := hu0
      _ = u1 := hu1.symm
  have huN : u1 ≤ n := by
    calc
      u1 = u0 := hu01.symm
      _ ≤ s := huS
      _ ≤ n := hsn
  have hback := ReferenceFirstCollectionQueuePrefixChronology.active_boundary_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (z := z) (s := s1) (u := u1) (t0 := ⟨n, hnT⟩) (t1 := ⟨t, ht⟩)
    hsu1 huN hnt hCT
  have hrawBack : i ∈ RawPending (rate := rate) (rewards := rewards)
      C_star C_h n z := hback.2 ((_root_.Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
        (rate := rate) (rewards := rewards) C_star C_h t z i).1 hi).2
  have hflagT := (_root_.Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
    (rate := rate) (rewards := rewards) C_star C_h t z i).1 hi |>.1
  have hflagN : FailFlag (rate := rate) (rewards := rewards)
      C_star C_h n z = false := by
    by_contra hne
    have htrue : FailFlag (rate := rate) (rewards := rewards)
        C_star C_h n z = true := Bool.eq_true_of_not_eq_false hne
    have hmono := _root_.Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_mono
      (rate := rate) (rewards := rewards) C_star C_h z n t hnt htrue
    rw [hflagT] at hmono
    cases hmono
  exact (_root_.Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
    (rate := rate) (rewards := rewards) C_star C_h n z i).2 ⟨hflagN, hrawBack⟩

/-- Nonempty awaited dates are convex. The witnesses come from the same
actual physical start and cutoff, identified by the public boundary producer. -/
theorem supportIndices_convex
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s t n : ℕ}
    (hs : s ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z)
    (ht : t ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z)
    (hsn : s ≤ n) (hnt : n ≤ t) :
    n ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z := by
  rcases (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z s).1 hs with ⟨hsT, hsNonempty⟩
  rcases (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z t).1 ht with ⟨htT, htNonempty⟩
  have hnT : n < p.T := lt_of_le_of_lt hnt htT
  have hsnested := awaited_support_backward (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z hsn hnt htT hsNonempty htNonempty
  have hmem : (Awaited (rate := rate) (rewards := rewards)
      C_star C_h n z).Nonempty := by
    rcases htNonempty with ⟨i, hi⟩
    exact ⟨i, hsnested i hi⟩
  exact (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z n).2 ⟨hnT, hmem⟩

/-- The support calendar is exactly the closed span between its first and
last supported dates, expressed using round-number endpoints. -/
theorem supportIndices_eq_Ico
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z =
      Finset.Ico (sigma (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z - 1)
        (theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z - 1) := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem _ hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem _ hS
    have hminlemax : S.min' hS ≤ S.max' hS :=
      Finset.min'_le _ _ hmax
    have hmaxT : S.max' hS < p.T :=
      (mem_supportIndices_iff (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z _).1 hmax |>.1
    have hspan : ∀ n, n ∈ S ↔ S.min' hS ≤ n ∧ n ≤ S.max' hS := by
      intro n
      constructor
      · intro hn
        exact ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
      · rintro ⟨hlo, hhi⟩
        have hnmem := supportIndices_convex (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z hmin hmax hlo hhi
        exact hnmem
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    ext n
    change n ∈ S ↔ n ∈ Finset.Ico
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1)
    rw [hspan]
    rw [hsig, htheta]
    simp only [Finset.mem_Ico]
    omega
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [theta, S, hS]
    change S = Finset.Ico
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1)
    rw [hSempty, hsig, htheta]
    simp

theorem endpoint_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z ∧
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z ∧
      theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ p.T + 1 := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hmaxT := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z _).1 hmax |>.1
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega
  · have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    exact ⟨by omega, le_rfl, le_rfl⟩

theorem support_nonempty_iff_phase
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (Awaited (rate := rate) (rewards := rewards) C_star C_h n z).Nonempty ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ n + 1 ∧
        n + 1 < theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z := by
  by_cases hn : n < p.T
  · have hmember : n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z ↔
          (Awaited (rate := rate) (rewards := rewards) C_star C_h n z).Nonempty := by
      rw [mem_supportIndices_iff]
      exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
    rw [← hmember, supportIndices_eq_Ico]
    simp only [Finset.mem_Ico]
    omega
  · have hnT : p.T ≤ n := by omega
    have hempty := ReferenceFirstCollectionAwaitedTaskSupport.Pawait_of_horizon_le
      rate rewards C_star C_h n hnT z
    change (ReferenceFirstCollectionAwaitedTaskSupport.Pawait
      rate rewards C_star C_h n z).Nonempty ↔ _
    rw [hempty]
    constructor
    · intro h
      simp at h
    · intro hphase
      have hbounds := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
      omega

/-- The awaited task set shrinks between the two analytical endpoints. -/
theorem Pawait_shrinking
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s t : ℕ}
    (hst : s ≤ t) (hs : sigma (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤ s + 1)
    (ht : t + 1 < theta (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z) :
    Awaited (rate := rate) (rewards := rewards) C_star C_h t z ⊆
      Awaited (rate := rate) (rewards := rewards) C_star C_h s z := by
  classical
  intro i hit
  have htsupport : (Awaited (rate := rate) (rewards := rewards)
      C_star C_h t z).Nonempty := ⟨i, hit⟩
  have htT : t < p.T := by
    have hbounds := endpoint_bounds (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z
    omega
  have hsT : s < p.T := lt_of_le_of_lt (by omega : s ≤ t) htT
  have hphaseS : sigma (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ≤ s + 1 ∧
      s + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
    exact ⟨hs, by omega⟩
  have hsNonempty := (support_nonempty_iff_phase (rate := rate)
    (rewards := rewards) (C_star := C_star) (C_h := C_h) z s).mpr hphaseS
  exact awaited_support_backward (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z (n := s) (t := t) le_rfl hst htT
    hsNonempty htsupport i hit

private theorem support_nonempty_measurable_at
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (Awaited (rate := rate) (rewards := rewards) C_star C_h t.val z).Nonempty} := by
  classical
  have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      (Awaited (rate := rate) (rewards := rewards) C_star C_h t.val z).Nonempty} =
      ⋃ i : Fin (p.m - 1),
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          i ∈ Awaited (rate := rate) (rewards := rewards) C_star C_h t.val z} := by
    ext z
    simp [Finset.Nonempty]
  rw [hEq]
  exact MeasurableSet.iUnion fun i =>
    ReferenceFirstCollectionAwaitedTaskSupport.Pawait_mem_measurable
      control0 rate rewards C_star C_h i t

theorem sigma_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hnT : p.T + 1 ≤ n
  ·
    have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hb := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
      exact hb.2.1.trans (hb.2.2.trans hnT)
    rw [hwhole]
    exact MeasurableSet.univ
  · have hnle : n ≤ p.T := by omega
    have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ n} =
        ⋃ k : Fin p.T,
          {z | k.val + 1 ≤ n ∧
            (Awaited (rate := rate) (rewards := rewards)
              C_star C_h k.val z).Nonempty} := by
      ext z
      by_cases hS : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).Nonempty
      · have hmin := Finset.min'_mem
          (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z) hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_left hS]
        constructor
        · intro h
          refine ⟨⟨_, (mem_supportIndices_iff (rate := rate)
            (rewards := rewards) (C_star := C_star) (C_h := C_h) z _).1 hmin |>.1⟩,
            ?_, ?_⟩
          · omega
          · exact (mem_supportIndices_iff (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z _).1 hmin |>.2
        · rintro ⟨k, hk, hnonempty⟩
          have hmem := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z k.val).2 ⟨k.isLt, hnonempty⟩
          have hminle := Finset.min'_le
            (supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z) k.val hmem
          omega
      · have hEmpty : supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_right hS]
        constructor
        · intro h
          omega
        · rintro ⟨k, _, hnonempty⟩
          have hmem := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z k.val).2 ⟨k.isLt, hnonempty⟩
          rw [hEmpty] at hmem
          simp at hmem
    rw [hEq]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k.val + 1 ≤ n
    · have hdet := support_nonempty_measurable_at
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        control0 k
      have hdet' := (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0).mono (by omega : k.val + 1 ≤ n) _ hdet
      simpa [hk] using hdet'
    · simp [hk]

private theorem theta_le_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) {n : ℕ}
    (hn0 : 0 < n) (hnT : n ≤ p.T) :
    theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z < n ∧
        ¬ (Awaited (rate := rate) (rewards := rewards)
          C_star C_h (n - 1) z).Nonempty := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have hnsub : n - 1 < p.T := by omega
  have hidx : (Awaited (rate := rate) (rewards := rewards)
      C_star C_h (n - 1) z).Nonempty ↔ n - 1 ∈ S := by
    change (Awaited (rate := rate) (rewards := rewards)
        C_star C_h (n - 1) z).Nonempty ↔
      n - 1 ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
    rw [mem_supportIndices_iff]
    exact ⟨fun h => ⟨hnsub, h⟩, fun h => h.2⟩
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    have hAt : (Awaited (rate := rate) (rewards := rewards)
        C_star C_h (n - 1) z).Nonempty ↔
        S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
      have hspan : n - 1 ∈ S ↔
          S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
        constructor
        · intro h
          exact ⟨Finset.min'_le S _ h, Finset.le_max' S _ h⟩
        · rintro ⟨hlo, hhi⟩
          exact supportIndices_convex (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z hmin hmax hlo hhi
      exact hidx.trans hspan
    rw [hsig, htheta, hAt]
    omega
  ·
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega

theorem theta_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hempty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hrange := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
      omega
    rw [hempty]
    exact (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 0).measurableSet_empty
  · by_cases hnT : p.T + 1 ≤ n
    · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (endpoint_bounds (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).2.2.trans hnT
      rw [hwhole]
      exact MeasurableSet.univ
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnle : n ≤ p.T := by omega
      have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} =
          {z | sigma (rate := rate) (rewards := rewards)
                (C_star := C_star) (C_h := C_h) z < n} ∩
            {z | ¬ (Awaited (rate := rate) (rewards := rewards)
              C_star C_h (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact theta_le_iff (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z hnpos hnle
      rw [hEq]
      apply (MeasurableSet.inter ?_ ?_)
      · have hsig := sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 (n - 1)
        have hsig' := (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0).mono (by omega : n - 1 ≤ n) _ hsig
        apply hsig'.congr
        ext z
        simp only [Set.mem_ofPred_eq]
        omega
      · have hdet := support_nonempty_measurable_at
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 ⟨n - 1, by omega⟩
        have hnsub : (n - 1) + 1 = n := by omega
        rw [hnsub] at hdet
        exact hdet.compl

/-- The exact calendar identity for every natural prefix length. -/
theorem N_eq_filtered_servicePositiveDates
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (v : ℕ) :
    PhaseServiceWaiting.N
        (fun n z' => Awaited (rate := rate) (rewards := rewards)
          C_star C_h n z')
        (ReferenceFirstCollectionRoundEndObservation.x (rate := rate)
          rewards C_star C_h) i v z =
      ((ReferenceFirstCollectionAwaitedTaskSupport.servicePositiveDates
        (rate := rate) (rewards := rewards) C_star C_h i z).filter
        (fun t => t.val < v)).card := by
  classical
  let P := fun n z' => Awaited (rate := rate) (rewards := rewards)
    C_star C_h n z'
  let X := ReferenceFirstCollectionRoundEndObservation.x (rate := rate)
    rewards C_star C_h
  let D := (Finset.range v).filter fun n => i ∈ P n z ∧ X i n z = true
  have hN (v : ℕ) :
      PhaseServiceWaiting.N P X i v z =
        ((Finset.range v).filter fun n => i ∈ P n z ∧ X i n z = true).card := by
    induction v with
    | zero => simp [PhaseServiceWaiting.N]
    | succ v ih =>
      rw [PhaseServiceWaiting.N_succ, ih]
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : i ∈ P v z ∧ X i v z = true
      · simp [h]
      · simp [h]
  have hcard : D.card =
      ((ReferenceFirstCollectionAwaitedTaskSupport.servicePositiveDates
        (rate := rate) (rewards := rewards) C_star C_h i z).filter
        (fun t => t.val < v)).card := by
    refine Finset.card_bij (s := D)
      (t := (ReferenceFirstCollectionAwaitedTaskSupport.servicePositiveDates
        (rate := rate) (rewards := rewards) C_star C_h i z).filter
        (fun t => t.val < v))
      (fun n hn => ⟨n, ?_⟩) ?_ ?_ ?_
    · rcases Finset.mem_filter.mp hn with ⟨hnv, hpositive⟩
      have hnT : n < p.T := by
        by_contra hnot
        have hT : p.T ≤ n := by omega
        have hEmpty := ReferenceFirstCollectionAwaitedTaskSupport.Pawait_of_horizon_le
          (rate := rate) (rewards := rewards) C_star C_h n hT z
        have hPempty : P n z = ∅ := by
          simpa only [P, Awaited] using hEmpty
        rw [hPempty] at hpositive
        simp at hpositive
      exact hnT
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnv, hpositive⟩
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpositive⟩,
        Finset.mem_range.mp hnv⟩
    · intro n hn m hm hij
      exact congrArg Fin.val hij
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htservice, htv⟩
      rcases Finset.mem_filter.mp htservice with ⟨_, hpositive⟩
      refine ⟨t.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htv, ?_⟩, ?_⟩
      · exact hpositive
      · apply Fin.ext
        rfl
  change PhaseServiceWaiting.N P X i v z = _
  rw [hN v, hcard]

/-- Every prefix count is at most the accepted inclusive `4Q` service quota. -/
theorem N_le_fourQ
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (v : ℕ) :
    PhaseServiceWaiting.N
        (fun n z' => Awaited (rate := rate) (rewards := rewards)
          C_star C_h n z')
        (ReferenceFirstCollectionRoundEndObservation.x (rate := rate)
          rewards C_star C_h) i v z ≤ 4 * AffineBatchDecoder.quota p := by
  rw [N_eq_filtered_servicePositiveDates (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z i v]
  exact (Finset.card_filter_le _ _).trans
    (_root_.Bandits.Support.ReferenceFirstCollectionAwaitedTaskSupport.actual_first_collection_service_positive_dates_quota
      (rate := rate) (rewards := rewards) C_star C_h control0 z i)

end Bandits.Support.ReferenceFirstCollectionAwaitedPhaseSupport

end
