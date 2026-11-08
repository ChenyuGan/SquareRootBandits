/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionCalendarServiceLaw

import Lean.Elab.Tactic.Omega

/-!
# Support phase of the actual first replacement collection

Sources: pinned ZIP4 `06_interruptions.tex:431-437,459-487` and
`appendix_a_local_protocol.tex:28-85,92-157`.

The endpoints are literal finite support coordinates of the existing `P_repl`.
The calendar constructor supplies one matched physical segment for both onset
localization and subsequent nesting. No physical cutoff identity is asserted.
The strict-past common stop in `P_repl` retains the detecting round.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionPhaseSupport

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}
variable {control0 : ContinuousLearningRows.TimeControl p}

/-- The existing replacement pending support on the original source. -/
abbrev Pending (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstReplacementCollectionPendingFoundation.P_repl
    rate rewards C_star C_h control0 n z

/-- The exact finite calendar of nonempty dates of the existing replacement pending set. -/
def supportIndices (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset ℕ :=
  (Finset.range p.T).filter fun n =>
    (Pending rate rewards C_star C_h control0 n z).Nonempty

/-- First included round, with the source horizon sentinel for empty support. -/
noncomputable def sigma (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z).min' h + 1
  else p.T + 1

/-- First excluded round, with the same horizon sentinel for empty support. -/
noncomputable def theta (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z).max' h + 2
  else p.T + 1

theorem mem_supportIndices_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) :
    n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z ↔
      n < p.T ∧
        (Pending rate rewards C_star C_h control0 n z).Nonempty := by
  simp [supportIndices]

/-- Once replacement support has begun, the actual pending set shrinks.
Both the onset coordinate and nesting come from the SAME calendar witness. -/
theorem pending_shrinking_after_supported
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s n t : ℕ}
    (hsn : s ≤ n) (hnt : n ≤ t)
    (hstart : (Pending rate rewards C_star C_h control0 s z).Nonempty) :
    Pending rate rewards C_star C_h control0 t z ⊆
      Pending rate rewards C_star C_h control0 n z := by
  have h := ReferenceFirstReplacementCollectionActualCalendarTasks.complete_first_replacement_actual_calendar_tasks
    rate rewards C_star C_h control0 z
  dsimp only at h
  split at h
  · rw [show Pending rate rewards C_star C_h control0 t z = ∅ from h t]
    exact Finset.empty_subset _
  · split at h
    · split at h
      · rw [show Pending rate rewards C_star C_h control0 t z = ∅ from h t]
        exact Finset.empty_subset _
      · split at h
        · obtain ⟨hloc, _, _, hmono, _⟩ := h
          obtain ⟨a, ha, _, _⟩ := hloc s hstart
          exact hmono n t (by omega) hnt
        · rw [show Pending rate rewards C_star C_h control0 t z = ∅ from h t]
          exact Finset.empty_subset _
    · rw [show Pending rate rewards C_star C_h control0 t z = ∅ from h t]
      exact Finset.empty_subset _

/-- Emptiness cannot be followed by a new task after this support has begun.
There is no global nesting assertion before the replacement onset. -/
theorem no_return_after_empty
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s n t : ℕ}
    (hsn : s ≤ n) (hnt : n ≤ t)
    (hstart : (Pending rate rewards C_star C_h control0 s z).Nonempty)
    (hempty : Pending rate rewards C_star C_h control0 n z = ∅) :
    Pending rate rewards C_star C_h control0 t z = ∅ := by
  have hsub := pending_shrinking_after_supported z hsn hnt hstart
  rw [hempty] at hsub
  exact Finset.subset_empty.mp hsub

/-- Nonempty replacement dates are convex. The witnesses come from the same
actual physical start and cutoff, identified by the public boundary producer. -/
theorem supportIndices_convex
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s t n : ℕ}
    (hs : s ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z)
    (ht : t ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z)
    (hsn : s ≤ n) (hnt : n ≤ t) :
    n ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z := by
  rcases (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z s).1 hs with ⟨hsT, hsNonempty⟩
  rcases (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z t).1 ht with ⟨htT, htNonempty⟩
  have hnT : n < p.T := lt_of_le_of_lt hnt htT
  have hsnested := pending_shrinking_after_supported z hsn hnt hsNonempty
  have hmem : (Pending rate rewards C_star C_h control0 n z).Nonempty := by
    rcases htNonempty with ⟨i, hi⟩
    exact ⟨i, hsnested hi⟩
  exact (mem_supportIndices_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z n).2 ⟨hnT, hmem⟩

/-- The support calendar is exactly the closed span between its first and
last supported dates, expressed using round-number endpoints. -/
theorem supportIndices_eq_Ico
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z =
      Finset.Ico (sigma (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z - 1)
        (theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z - 1) := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem _ hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem _ hS
    have hminlemax : S.min' hS ≤ S.max' hS :=
      Finset.min'_le _ _ hmax
    have hmaxT : S.max' hS < p.T :=
      (mem_supportIndices_iff (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z _).1 hmax |>.1
    have hspan : ∀ n, n ∈ S ↔ S.min' hS ≤ n ∧ n ≤ S.max' hS := by
      intro n
      constructor
      · intro hn
        exact ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
      · rintro ⟨hlo, hhi⟩
        have hnmem := supportIndices_convex (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z hmin hmax hlo hhi
        exact hnmem
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    ext n
    change n ∈ S ↔ n ∈ Finset.Ico
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) z - 1)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) z - 1)
    rw [hspan]
    rw [hsig, htheta]
    simp only [Finset.mem_Ico]
    omega
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [theta, S, hS]
    change S = Finset.Ico
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) z - 1)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) z - 1)
    rw [hSempty, hsig, htheta]
    simp

theorem endpoint_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z ∧
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z ∧
      theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ p.T + 1 := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hmaxT := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z _).1 hmax |>.1
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega
  · have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    exact ⟨by omega, le_rfl, le_rfl⟩

theorem support_nonempty_iff_phase
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (Pending rate rewards C_star C_h control0 n z).Nonempty ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ n + 1 ∧
        n + 1 < theta (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z := by
  by_cases hn : n < p.T
  · have hmember : n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z ↔
          (Pending rate rewards C_star C_h control0 n z).Nonempty := by
      rw [mem_supportIndices_iff]
      exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
    rw [← hmember, supportIndices_eq_Ico]
    simp only [Finset.mem_Ico]
    omega
  · have hnT : p.T ≤ n := by omega
    have hempty := ReferenceFirstReplacementCollectionPendingFoundation.P_repl_of_horizon_le
      rate rewards C_star C_h control0 n hnT z
    change (ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z).Nonempty ↔ _
    rw [hempty]
    constructor
    · intro h
      simp at h
    · intro hphase
      have hbounds := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z
      omega

/-- The replacement task set shrinks between the two analytical endpoints. -/
theorem P_repl_shrinking
    (z : BootstrapPrivateRoundStreams.SourceInput p) {s t : ℕ}
    (hst : s ≤ t) (hs : sigma (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z ≤ s + 1)
    (ht : t + 1 < theta (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z) :
    Pending rate rewards C_star C_h control0 t z ⊆
      Pending rate rewards C_star C_h control0 s z := by
  have hphaseS : sigma (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) z ≤ s + 1 ∧
      s + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z :=
    ⟨hs, by omega⟩
  have hsNonempty := (support_nonempty_iff_phase (rate := rate)
    (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) z s).mpr hphaseS
  exact pending_shrinking_after_supported z (n := s) le_rfl hst hsNonempty

private theorem support_nonempty_measurable_at
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (Pending rate rewards C_star C_h control0 t.val z).Nonempty} := by
  classical
  have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      (Pending rate rewards C_star C_h control0 t.val z).Nonempty} =
      ⋃ i : Fin (p.m - 1),
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          i ∈ Pending rate rewards C_star C_h control0 t.val z} := by
    ext z
    simp [Finset.Nonempty]
  rw [hEq]
  exact MeasurableSet.iUnion fun i =>
    ReferenceFirstReplacementCollectionPendingFoundation.P_repl_mem_measurable
      rate rewards C_star C_h control0 t.val i

theorem sigma_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0)) := by
  intro n
  by_cases hnT : p.T + 1 ≤ n
  ·
    have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hb := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z
      exact hb.2.1.trans (hb.2.2.trans hnT)
    rw [hwhole]
    exact MeasurableSet.univ
  · have hnle : n ≤ p.T := by omega
    have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ n} =
        ⋃ k : Fin p.T,
          {z | k.val + 1 ≤ n ∧
            (Pending rate rewards C_star C_h control0 k.val z).Nonempty} := by
      ext z
      by_cases hS : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z).Nonempty
      · have hmin := Finset.min'_mem
          (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) z) hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_left hS]
        constructor
        · intro h
          refine ⟨⟨_, (mem_supportIndices_iff (rate := rate)
            (rewards := rewards) (C_star := C_star) (C_h := C_h) (control0 := control0) z _).1 hmin |>.1⟩,
            ?_, ?_⟩
          · omega
          · exact (mem_supportIndices_iff (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) (control0 := control0) z _).1 hmin |>.2
        · rintro ⟨k, hk, hnonempty⟩
          have hmem := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) z k.val).2 ⟨k.isLt, hnonempty⟩
          have hminle := Finset.min'_le
            (supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) (control0 := control0) z) k.val hmem
          omega
      · have hEmpty : supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_right hS]
        constructor
        · intro h
          omega
        · rintro ⟨k, _, hnonempty⟩
          have hmem := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) z k.val).2 ⟨k.isLt, hnonempty⟩
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
        (C_h := C_h) (control0 := control0) z ≤ n ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z < n ∧
        ¬ (Pending rate rewards C_star C_h control0 (n - 1) z).Nonempty := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      intro hnonempty
      have hmem := (mem_supportIndices_iff (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z (n - 1)).2
        ⟨by omega, hnonempty⟩
      have hle := Finset.le_max' S (n - 1) hmem
      omega
    · rintro ⟨hbegun, hcurrentEmpty⟩
      have hminNonempty := (mem_supportIndices_iff (rate := rate)
        (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) z _).1 hmin |>.2
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hcurrentEmpty
      by_contra hnot
      have hno := no_return_after_empty z
        (s := S.min' hS) (n := n - 1) (t := S.max' hS)
        (by omega) (by omega) hminNonempty hempty
      have hmaxNonempty := (mem_supportIndices_iff (rate := rate)
        (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (control0 := control0) z _).1 hmax |>.2
      rw [hno] at hmaxNonempty
      exact Finset.not_nonempty_empty hmaxNonempty
  ·
    have hsig : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega

theorem theta_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0)) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hempty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0) z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hrange := endpoint_bounds (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z
      omega
    rw [hempty]
    exact (_root_.Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 0).measurableSet_empty
  · by_cases hnT : p.T + 1 ≤ n
    · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) (control0 := control0) z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (endpoint_bounds (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z).2.2.trans hnT
      rw [hwhole]
      exact MeasurableSet.univ
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnle : n ≤ p.T := by omega
      have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) (control0 := control0) z ≤ n} =
          {z | sigma (rate := rate) (rewards := rewards)
                (C_star := C_star) (C_h := C_h) (control0 := control0) z < n} ∩
            {z | ¬ (Pending rate rewards C_star C_h control0 (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact theta_le_iff (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) z hnpos hnle
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

/-- The literal finite supported charge equals the phase waiting charge.
This holds for every real weight sequence, without probabilistic premises. -/
theorem supported_charge_eq_totalCharge
    (w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (∑ n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0) z, w n z) =
      PhaseServiceWaiting.totalCharge (Pending rate rewards C_star C_h control0)
        (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0))
        (theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (control0 := control0)) w p.T z := by
  classical
  unfold supportIndices PhaseServiceWaiting.totalCharge
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  have hphase := support_nonempty_iff_phase (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) z n
  by_cases hn : (Pending rate rewards C_star C_h control0 n z).Nonempty
  · have hb := hphase.mp hn
    rw [ite_eq_left hn]
    symm
    apply Set.indicator_of_mem
    exact ⟨hb.1, hb.2, hn⟩
  · rw [ite_eq_right hn]
    symm
    apply Set.indicator_of_notMem
    exact fun h => hn h.2.2

end Bandits.Support.ReferenceFirstReplacementCollectionPhaseSupport

end
