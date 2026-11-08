/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedTaskSupport

import Lean.Elab.Tactic.Omega

/-!
# Finite calendar for the first replacement awaited support

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240`,
`sources/zip4/manuscript/06_interruptions.tex:425-437,459-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-85,92-108,141-157`.

The endpoints below are the first and one-past-last dates in the literal
finite support of `Pnew`. They are internal support endpoints and carry no
identification with a physical cutoff or a later launch date.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- The actual new replacement support on the original source input. -/
abbrev Awaited (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
    rate rewards C_star C_h control0 n z

/-- The literal finite calendar of nonempty dates of `Pnew`. -/
def supportIndices (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset ℕ :=
  (Finset.range p.T).filter fun n =>
    (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
      rate rewards C_star C_h control0 n z).Nonempty

/-- First included round, with the horizon sentinel for empty support. -/
noncomputable def sigma (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices rate rewards C_star C_h control0 z).Nonempty then
    (supportIndices rate rewards C_star C_h control0 z).min' h + 1
  else p.T + 1

/-- First excluded round, with the same horizon sentinel for empty support. -/
noncomputable def theta (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices rate rewards C_star C_h control0 z).Nonempty then
    (supportIndices rate rewards C_star C_h control0 z).max' h + 2
  else p.T + 1

/-- Membership in the literal range-filter calendar. -/
theorem mem_supportIndices_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) :
    n ∈ supportIndices rate rewards C_star C_h control0 z ↔
      n < p.T ∧ (Awaited rate rewards C_star C_h control0 n z).Nonempty := by
  simp [supportIndices, Awaited]

/-- Once an actual supported date has occurred, every supported later date
contains only tasks that were still supported at any intervening date. -/
theorem supportIndices_convex (z : BootstrapPrivateRoundStreams.SourceInput p)
    {s t n : ℕ}
    (hs : s ∈ supportIndices rate rewards C_star C_h control0 z)
    (ht : t ∈ supportIndices rate rewards C_star C_h control0 z)
    (hsn : s ≤ n) (hnt : n ≤ t) :
    n ∈ supportIndices rate rewards C_star C_h control0 z := by
  rcases (mem_supportIndices_iff rate rewards C_star C_h control0 z s).mp hs with
    ⟨hsT, hsNonempty⟩
  rcases (mem_supportIndices_iff rate rewards C_star C_h control0 z t).mp ht with
    ⟨htT, htNonempty⟩
  have hnT : n < p.T := lt_of_le_of_lt hnt htT
  have hnest :=
    ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew_shrinking_after_supported
      rate rewards C_star C_h control0 z hsn hnt hsNonempty
  have hnNonempty : (Awaited rate rewards C_star C_h control0 n z).Nonempty := by
    rcases htNonempty with ⟨i, hi⟩
    exact ⟨i, hnest hi⟩
  exact (mem_supportIndices_iff rate rewards C_star C_h control0 z n).mpr
    ⟨hnT, hnNonempty⟩

/-- The calendar is exactly the closed span between its first and last
supported dates, written in zero-based source-date indices. -/
theorem supportIndices_eq_Ico (z : BootstrapPrivateRoundStreams.SourceInput p) :
    supportIndices rate rewards C_star C_h control0 z =
      Finset.Ico (sigma rate rewards C_star C_h control0 z - 1)
        (theta rate rewards C_star C_h control0 z - 1) := by
  classical
  let S := supportIndices rate rewards C_star C_h control0 z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem _ hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem _ hS
    have hspan : ∀ n, n ∈ S ↔ S.min' hS ≤ n ∧ n ≤ S.max' hS := by
      intro n
      constructor
      · intro hn
        exact ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
      · rintro ⟨hlo, hhi⟩
        exact supportIndices_convex rate rewards C_star C_h control0 z hmin hmax hlo hhi
    have hsig : sigma rate rewards C_star C_h control0 z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = S.max' hS + 2 := by
      simp [theta, S, hS]
    ext n
    change n ∈ S ↔ n ∈ Finset.Ico
      (sigma rate rewards C_star C_h control0 z - 1)
      (theta rate rewards C_star C_h control0 z - 1)
    rw [hspan, hsig, htheta]
    simp only [Finset.mem_Ico]
    omega
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hsig : sigma rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [theta, S, hS]
    change S = Finset.Ico
      (sigma rate rewards C_star C_h control0 z - 1)
      (theta rate rewards C_star C_h control0 z - 1)
    rw [hSempty, hsig, htheta]
    simp

/-- The endpoints are valid one-based phase bounds, including the empty
support sentinel branch. -/
theorem endpoint_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ sigma rate rewards C_star C_h control0 z ∧
      sigma rate rewards C_star C_h control0 z ≤ theta rate rewards C_star C_h control0 z ∧
      theta rate rewards C_star C_h control0 z ≤ p.T + 1 := by
  classical
  let S := supportIndices rate rewards C_star C_h control0 z
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hmaxT := (mem_supportIndices_iff rate rewards C_star C_h control0 z _).mp hmax |>.1
    have hsig : sigma rate rewards C_star C_h control0 z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega
  · have hsig : sigma rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    exact ⟨by omega, le_rfl, le_rfl⟩

/-- A date is supported exactly when its round number lies in the literal
endpoint interval. -/
theorem support_nonempty_iff_phase
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (Awaited rate rewards C_star C_h control0 n z).Nonempty ↔
      sigma rate rewards C_star C_h control0 z ≤ n + 1 ∧
        n + 1 < theta rate rewards C_star C_h control0 z := by
  by_cases hn : n < p.T
  · have hmember :
        n ∈ supportIndices rate rewards C_star C_h control0 z ↔
          (Awaited rate rewards C_star C_h control0 n z).Nonempty := by
      rw [mem_supportIndices_iff rate rewards C_star C_h control0 z n]
      exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
    rw [← hmember, supportIndices_eq_Ico rate rewards C_star C_h control0 z]
    simp only [Finset.mem_Ico]
    omega
  · have hnT : p.T ≤ n := by omega
    have hempty :=
      ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew_of_horizon_le
        rate rewards C_star C_h control0 n hnT z
    change (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
      rate rewards C_star C_h control0 n z).Nonempty ↔ _
    rw [hempty]
    constructor
    · intro h
      simp at h
    · intro hphase
      have hb := endpoint_bounds rate rewards C_star C_h control0 z
      omega

private theorem support_nonempty_measurable_at
    (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
          rate rewards C_star C_h control0 t.val z).Nonempty} := by
  classical
  have hEq :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
          rate rewards C_star C_h control0 t.val z).Nonempty} =
      ⋃ i : Fin (p.m - 1),
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          i ∈ ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
            rate rewards C_star C_h control0 t.val z} := by
    ext z
    simp [Finset.Nonempty]
  rw [hEq]
  exact MeasurableSet.iUnion fun i =>
    ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew_mem_measurable
      rate rewards C_star C_h control0 t.val i

/-- The first supported endpoint is a stopping time for the actual original
continuous source-prefix filtration. -/
theorem sigma_is_pre_round_stopping_time :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (sourcePrefixFiltration control0)
      (sigma rate rewards C_star C_h control0) := by
  intro n
  by_cases hnT : p.T + 1 ≤ n
  · have hwhole :
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          sigma rate rewards C_star C_h control0 z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (endpoint_bounds rate rewards C_star C_h control0 z).2.1.trans
        ((endpoint_bounds rate rewards C_star C_h control0 z).2.2.trans hnT)
    rw [hwhole]
    exact MeasurableSet.univ
  · have hnle : n ≤ p.T := by omega
    have hEq :
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          sigma rate rewards C_star C_h control0 z ≤ n} =
        ⋃ k : Fin p.T,
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            k.val + 1 ≤ n ∧
              (Awaited rate rewards C_star C_h control0 k.val z).Nonempty} := by
      ext z
      by_cases hS : (supportIndices rate rewards C_star C_h control0 z).Nonempty
      · have hmin := Finset.min'_mem
          (supportIndices rate rewards C_star C_h control0 z) hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_left hS]
        constructor
        · intro h
          have hmin' := (mem_supportIndices_iff rate rewards C_star C_h control0 z _).mp hmin
          refine ⟨⟨(supportIndices rate rewards C_star C_h control0 z).min' hS,
            hmin'.1⟩, ?_, hmin'.2⟩
          simpa using h
        · rintro ⟨k, hk, hnonempty⟩
          have hmem := (mem_supportIndices_iff rate rewards C_star C_h control0 z k.val).mpr
            ⟨k.isLt, hnonempty⟩
          have hminle := Finset.min'_le
            (supportIndices rate rewards C_star C_h control0 z) k.val hmem
          omega
      · have hEmpty : supportIndices rate rewards C_star C_h control0 z = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_right hS]
        constructor
        · intro h
          omega
        · rintro ⟨k, _, hnonempty⟩
          have hmem := (mem_supportIndices_iff rate rewards C_star C_h control0 z k.val).mpr
            ⟨k.isLt, hnonempty⟩
          rw [hEmpty] at hmem
          simp at hmem
    rw [hEq]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k.val + 1 ≤ n
    · have hdet := support_nonempty_measurable_at rate rewards C_star C_h control0 k
      have hdet' := (sourcePrefixFiltration control0).mono
        (by omega : k.val + 1 ≤ n) _ hdet
      simpa [hk] using hdet'
    · simp [hk]

private theorem theta_le_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) {n : ℕ}
    (hn0 : 0 < n) (hnT : n ≤ p.T) :
    theta rate rewards C_star C_h control0 z ≤ n ↔
      sigma rate rewards C_star C_h control0 z < n ∧
        ¬ (Awaited rate rewards C_star C_h control0 (n - 1) z).Nonempty := by
  classical
  let S := supportIndices rate rewards C_star C_h control0 z
  have hnsub : n - 1 < p.T := by omega
  have hidx :
      (Awaited rate rewards C_star C_h control0 (n - 1) z).Nonempty ↔ n - 1 ∈ S := by
    change (Awaited rate rewards C_star C_h control0 (n - 1) z).Nonempty ↔
      n - 1 ∈ supportIndices rate rewards C_star C_h control0 z
    rw [mem_supportIndices_iff rate rewards C_star C_h control0 z]
    exact ⟨fun h => ⟨hnsub, h⟩, fun h => h.2⟩
  by_cases hS : S.Nonempty
  · have hmin := Finset.min'_mem S hS
    have hmax := Finset.max'_mem S hS
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le S _ hmax
    have hsig : sigma rate rewards C_star C_h control0 z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = S.max' hS + 2 := by
      simp [theta, S, hS]
    have hAt :
        (Awaited rate rewards C_star C_h control0 (n - 1) z).Nonempty ↔
          S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
      have hspan : n - 1 ∈ S ↔
          S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
        constructor
        · intro h
          exact ⟨Finset.min'_le S _ h, Finset.le_max' S _ h⟩
        · rintro ⟨hlo, hhi⟩
          exact supportIndices_convex rate rewards C_star C_h control0 z hmin hmax hlo hhi
      exact hidx.trans hspan
    rw [hsig, htheta, hAt]
    omega
  · have hsig : sigma rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [sigma, S, hS]
    have htheta : theta rate rewards C_star C_h control0 z = p.T + 1 := by
      simp [theta, S, hS]
    rw [hsig, htheta]
    omega

/-- The last-supported endpoint is also a stopping time. Its sublevel event
is expressed using only the earlier start endpoint and the date just observed. -/
theorem theta_is_pre_round_stopping_time :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (sourcePrefixFiltration control0)
      (theta rate rewards C_star C_h control0) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hempty :
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta rate rewards C_star C_h control0 z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hb := endpoint_bounds rate rewards C_star C_h control0 z
      omega
    rw [hempty]
    exact (sourcePrefixFiltration control0 0).measurableSet_empty
  · by_cases hnT : p.T + 1 ≤ n
    · have hwhole :
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            theta rate rewards C_star C_h control0 z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (endpoint_bounds rate rewards C_star C_h control0 z).2.2.trans hnT
      rw [hwhole]
      exact MeasurableSet.univ
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnle : n ≤ p.T := by omega
      have hEq :
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            theta rate rewards C_star C_h control0 z ≤ n} =
          {z | sigma rate rewards C_star C_h control0 z < n} ∩
            {z | ¬ (Awaited rate rewards C_star C_h control0 (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact theta_le_iff rate rewards C_star C_h control0 z hnpos hnle
      rw [hEq]
      apply MeasurableSet.inter
      · have hsig := sigma_is_pre_round_stopping_time
          rate rewards C_star C_h control0 (n - 1)
        have hsig' := (sourcePrefixFiltration control0).mono
          (by omega : n - 1 ≤ n) _ hsig
        apply hsig'.congr
        ext z
        simp only [Set.mem_ofPred_eq]
        omega
      · have hdet := support_nonempty_measurable_at
          rate rewards C_star C_h control0 ⟨n - 1, by omega⟩
        have hnsub : (n - 1) + 1 = n := by omega
        rw [hnsub] at hdet
        exact hdet.compl

/-- Every nonempty supported date lies inside these same endpoints. -/
theorem phase_bounds_of_supported (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (h : (Awaited rate rewards C_star C_h control0 n z).Nonempty) :
    sigma rate rewards C_star C_h control0 z ≤ n + 1 ∧
      n + 1 < theta rate rewards C_star C_h control0 z :=
  (support_nonempty_iff_phase rate rewards C_star C_h control0 z n).mp h

/-- Within one supported phase the new task sets are nested, starting only
after the literal first supported date. -/
theorem Pnew_nested_within_phase (z : BootstrapPrivateRoundStreams.SourceInput p)
    {s t : ℕ} (hst : s ≤ t) (ht : t < p.T)
    (hstart : sigma rate rewards C_star C_h control0 z ≤ s + 1)
    (hend : t + 1 < theta rate rewards C_star C_h control0 z) :
    Awaited rate rewards C_star C_h control0 t z ⊆
      Awaited rate rewards C_star C_h control0 s z := by
  have hsT : s < p.T := lt_of_le_of_lt hst ht
  have hsBeforeEnd : s + 1 < theta rate rewards C_star C_h control0 z := by omega
  have hsNonempty :=
    (support_nonempty_iff_phase rate rewards C_star C_h control0 z s).mpr
      ⟨hstart, hsBeforeEnd⟩
  exact ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew_shrinking_after_supported
    rate rewards C_star C_h control0 z le_rfl hst hsNonempty

/-- Exact supported-date accounting for every real-valued weight. The
detecting supported service date is included by the literal nonempty test. -/
theorem supported_charge_eq_totalCharge
    (w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (∑ n ∈ Finset.range p.T,
      if (Awaited rate rewards C_star C_h control0 n z).Nonempty then w n z else 0) =
      PhaseServiceWaiting.totalCharge
        (Awaited rate rewards C_star C_h control0)
        (sigma rate rewards C_star C_h control0)
        (theta rate rewards C_star C_h control0) w p.T z := by
  classical
  simp only [PhaseServiceWaiting.totalCharge, PhaseServiceWaiting.A]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hP : (Awaited rate rewards C_star C_h control0 n z).Nonempty
  · have hphase :=
      (support_nonempty_iff_phase rate rewards C_star C_h control0 z n).mp hP
    simp [Set.indicator, hP, hphase.1, hphase.2]
  ·
    simp [Set.indicator, hP]

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport

end
