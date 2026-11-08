/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpDetectedQueueMask
public import Bandits.Support.ReferenceFirstCollectionDetectedPendingEndpoints

/-!
# Endpoints of UP-detected first-collection support

The analytical endpoints describe exactly the dates on which the existing
UP-detected task mask is nonempty. They use the unchanged source input and
source-prefix filtration.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionUpDetectedPendingEndpoints

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ}

/-- Calendar dates on which the actual UP-detected task mask has nonempty
support. -/
def supportIndices (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Finset ℕ :=
  (Finset.range p.T).filter fun n =>
    (ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty

/-- The first supported date, with the literal empty-support sentinel. -/
def sigma (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).min' h + 1
  else p.T + 1

/-- One plus the last supported date, with the literal empty-support
sentinel. -/
def theta (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).Nonempty then
    (supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z).max' h + 2
  else p.T + 1

/-- Between two supported UP-detected dates, later tasks remain at the earlier
date. The old detected interval and the persistent false UP-failure gate are
both obtained from actual support at the supplied endpoints. -/
private theorem Pup_backward_from_supported_pair
    (l a b : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hla : l ≤ a) (hab : a ≤ b) (hb : b < p.T)
    (hPl : (ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) l z).Nonempty)
    (hPb : (ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) b z).Nonempty) :
    ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) b z ⊆
    ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) a z := by
  have hOldL :
      (ReferenceFirstCollectionDetectedQueueMask.Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) l z).Nonempty := by
    rcases hPl with ⟨i, hi⟩
    exact ⟨i, ReferenceFirstCollectionUpDetectedQueueMask.Pup_subset_Pdetect
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) l z hi⟩
  have hOldB :
      (ReferenceFirstCollectionDetectedQueueMask.Pdetect
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) b z).Nonempty := by
    rcases hPb with ⟨i, hi⟩
    exact ⟨i, ReferenceFirstCollectionUpDetectedQueueMask.Pup_subset_Pdetect
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) b z hi⟩
  have hOldBoundsL :=
    (ReferenceFirstCollectionDetectedPendingEndpoints.Pdetect_nonempty_iff
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) z l).mp hOldL
  have hOldBoundsB :=
    (ReferenceFirstCollectionDetectedPendingEndpoints.Pdetect_nonempty_iff
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) z b).mp hOldB
  have hOldBack :=
    ReferenceFirstCollectionDetectedPendingEndpoints.Pdetect_endpoint_nested
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) a b hab hb z (by omega) hOldBoundsB.2
  intro i hi
  have hmem :=
    (ReferenceFirstCollectionUpDetectedQueueMask.mem_Pup_iff
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) i b z).mp hi
  have hflagA :
      ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h a z = false := by
    cases hfa : ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag
        rate rewards C_star C_h a z with
    | false => rfl
    | true =>
        have hfb := ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag_mono
          rate rewards C_star C_h z a b hab hfa
        rw [hmem.1] at hfb
        cases hfb
  have hOldA := hOldBack hmem.2
  exact (ReferenceFirstCollectionUpDetectedQueueMask.mem_Pup_iff
    (rate := rate) (rewards := rewards) (C_star := C_star)
    (C_h := C_h) i a z).mpr ⟨hflagA, hOldA⟩

/-- The UP-detected support is exactly the inclusive interval between its
first and last supported zero-based dates. -/
theorem supportIndices_eq_Ico
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z =
      Finset.Ico
        (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z - 1)
        (theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z - 1) := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hminT : S.min' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmin).1
    have hmaxT : S.max' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
    have hminlemax : S.min' hS ≤ S.max' hS := Finset.min'_le_max' S hS
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hminT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' < p.T := by
      simpa [S] using hminT
    have hmaxT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).max' hS' < p.T := by
      simpa [S] using hmaxT
    have hminmax' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' ≤
        (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
      simpa [S] using hminlemax
    have hminP :
        (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (S.min' hS) z).Nonempty :=
      (Finset.mem_filter.mp hmin).2
    have hmaxP :
        (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (S.max' hS) z).Nonempty :=
      (Finset.mem_filter.mp hmax).2
    ext n
    constructor
    · intro hn
      have hlemin : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).min' hS' ≤ n := by
        simpa [S] using Finset.min'_le S _ hn
      have hmaxle : n ≤ (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
        simpa [S] using Finset.le_max' S _ hn
      simp only [Finset.mem_Ico]
      simp only [sigma, theta, dite_eq_left hS']
      omega
    · intro hn
      simp only [Finset.mem_Ico] at hn
      simp only [sigma, theta, dite_eq_left hS'] at hn
      have hminEq :
          (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z).min' hS' = S.min' hS := by
        simp [S]
      have hmaxEq :
          (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z).max' hS' = S.max' hS := by
        simp [S]
      rw [hminEq, hmaxEq] at hn
      have hnT : n < p.T := by omega
      have hback := Pup_backward_from_supported_pair
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (l := S.min' hS) (a := n) (b := S.max' hS)
        z (by omega) (by omega) hmaxT hminP hmaxP
      have hmember : n ∈ S := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr hnT
        · rcases hmaxP with ⟨i, hi⟩
          exact ⟨i, hback hi⟩
      exact hmember
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hEmpty : supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hS'
    change supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z = _
    simp only [sigma, theta, dite_eq_right hS']
    rw [hEmpty]
    simp

/-- The first and one-past-last UP-detected dates are ordered and bounded by
the literal empty-support sentinel. -/
theorem sigma_theta_range
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ∧
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z ∧
      theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ p.T + 1 := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hminT : S.min' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmin).1
    have hmaxT : S.max' hS < p.T :=
      Finset.mem_range.mp (Finset.mem_filter.mp hmax).1
    have hminmax := Finset.min'_le_max' S hS
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hminT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' < p.T := by
      simpa [S] using hminT
    have hmaxT' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).max' hS' < p.T := by
      simpa [S] using hmaxT
    have hminmax' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).min' hS' ≤
        (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).max' hS' := by
      simpa [S] using hminmax
    simp only [sigma, theta, dite_eq_left hS']
    omega
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    simp [sigma, theta, hS']

/-- Full nonemptiness characterization of the UP-detected mask on every
natural date, including dates beyond the physical horizon. -/
theorem Pup_nonempty_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    (ReferenceFirstCollectionUpDetectedQueueMask.Pup
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) n z).Nonempty ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n + 1 ∧
      n + 1 < theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z := by
  have hsupport :
      (ReferenceFirstCollectionUpDetectedQueueMask.Pup
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) n z).Nonempty ↔
      n ∈ supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
    by_cases hn : n < p.T
    · simp only [supportIndices, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        exact ⟨hn, h⟩
      · rintro ⟨_, h⟩
        exact h
    · simp only [supportIndices, Finset.mem_filter, Finset.mem_range]
      simp [ReferenceFirstCollectionUpDetectedQueueMask.Pup,
        ReferenceFirstCollectionDetectedQueueMask.Pdetect, hn]
  rw [hsupport]
  have hIco := supportIndices_eq_Ico (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have hmemIco : n ∈ supportIndices (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) z ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1 ≤ n ∧
      n < theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z - 1 := by
    have h := congrArg (fun S : Finset ℕ => n ∈ S) hIco
    exact Iff.of_eq (by simpa only [Finset.mem_Ico] using h)
  rw [hmemIco]
  have hrange := sigma_theta_range (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  omega

/-- The endpoint inequalities hold at every finite date in the support. -/
theorem Pup_endpoint_phase :
    ∀ t, t < p.T → ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      (ReferenceFirstCollectionUpDetectedQueueMask.Pup
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) t z).Nonempty →
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ t + 1 ∧
      t + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z := by
  intro t ht z hP
  exact (Pup_nonempty_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z t).mp hP

/-- Exact interval nesting for the actual UP-detected task set. -/
theorem Pup_endpoint_nested
    (a b : ℕ) (hab : a ≤ b) (hb : b < p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ a + 1 →
      b + 1 < theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z →
      ReferenceFirstCollectionUpDetectedQueueMask.Pup
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) b z ⊆
      ReferenceFirstCollectionUpDetectedQueueMask.Pup
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) a z := by
  intro ha hbt
  have hPa := (Pup_nonempty_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z a).mpr ⟨ha, by omega⟩
  have hPb := (Pup_nonempty_iff (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z b).mpr ⟨by omega, hbt⟩
  exact Pup_backward_from_supported_pair
    (rate := rate) (rewards := rewards) (C_star := C_star)
    (C_h := C_h) a a b z le_rfl hab hb hPa hPb

private theorem Pup_nonempty_measurable_at
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (n + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z).Nonempty} := by
  have hEq :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) n z).Nonempty} =
        ⋃ i : Fin (p.m - 1), {z | i ∈
          ReferenceFirstCollectionUpDetectedQueueMask.Pup
            (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) n z} := by
    ext z
    simp [Finset.Nonempty]
  rw [hEq]
  exact MeasurableSet.iUnion fun i =>
    ReferenceFirstCollectionUpDetectedQueueMask.Pup_mem_measurable
      (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) control0 i n

/-- For intermediate observation indices, the event that the last supported
endpoint has passed is exactly the first-endpoint event and an empty current
UP-detected cell. -/
theorem theta_le_iff
    (n : ℕ) (hn : 0 < n) (hnT : n ≤ p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z ≤ n ↔
      sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) z < n ∧
      ¬ (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (n - 1) z).Nonempty := by
  classical
  let S := supportIndices (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) z
  have hmem :
      (ReferenceFirstCollectionUpDetectedQueueMask.Pup
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (n - 1) z).Nonempty ↔ n - 1 ∈ S := by
    have hn' : n - 1 < p.T := by omega
    simp [S, supportIndices, hn']
  by_cases hS : S.Nonempty
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hminmax : S.min' hS ≤ S.max' hS := Finset.min'_le_max' S hS
    have hInterval := supportIndices_eq_Ico
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z
    have hS' : (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hInterval' : S = Finset.Ico (S.min' hS) (S.max' hS + 1) := by
      simpa [S, sigma, theta, hS'] using hInterval
    have hintervalMem : n - 1 ∈ S ↔
        S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := by
      have h := congrArg (fun U : Finset ℕ => n - 1 ∈ U) hInterval'
      simp only [Finset.mem_Ico] at h
      constructor
      · intro hx
        have hx' := h.mp hx
        exact ⟨hx'.1, by omega⟩
      · rintro ⟨hx₁, hx₂⟩
        apply h.mpr
        exact ⟨hx₁, by omega⟩
    have hP :
        (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (n - 1) z).Nonempty ↔
        S.min' hS ≤ n - 1 ∧ n - 1 ≤ S.max' hS := hmem.trans hintervalMem
    have hσ : sigma (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.min' hS + 1 := by
      simp [sigma, S, hS]
    have hθ : theta (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z = S.max' hS + 2 := by
      simp [theta, S, hS]
    rw [hσ, hθ]
    rw [hP]
    omega
  · have hS' : ¬ (supportIndices (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).Nonempty := by
      simpa [S] using hS
    have hP :
        ¬ (ReferenceFirstCollectionUpDetectedQueueMask.Pup
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (n - 1) z).Nonempty := by
      intro h
      exact hS' ⟨n - 1, hmem.mp h⟩
    simp only [sigma, theta, dite_eq_right hS', hP]
    omega

/-- The first UP-detected date is a stopping time for the unchanged
source-prefix filtration, at every natural observation index. -/
theorem sigma_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (sigma (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hnT : p.T + 1 ≤ n
  · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
        sigma (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hr := sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z
      exact hr.2.1.trans (hr.2.2.trans hnT)
    rw [hwhole]
    exact MeasurableSet.univ
  · have hnle : n ≤ p.T := by omega
    have hEq :
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          sigma (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} =
        ⋃ k : Fin p.T,
          {z | k.val + 1 ≤ n ∧
            (ReferenceFirstCollectionUpDetectedQueueMask.Pup
              (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) k.val z).Nonempty} := by
      ext z
      by_cases hS : (supportIndices (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).Nonempty
      · have hmin : (supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z).min' hS ∈
          supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z := Finset.min'_mem _ hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_left hS]
        constructor
        · intro h
          refine ⟨⟨_, Finset.mem_range.mp
            (Finset.mem_filter.mp hmin).1⟩, ?_, ?_⟩
          · omega
          · exact (Finset.mem_filter.mp hmin).2
        · rintro ⟨k, hk, hdet⟩
          have hmem : k.val ∈ supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, hdet⟩
          have hminle := Finset.min'_le
            (supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z) k.val hmem
          omega
      · have hSempty : supportIndices (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) z = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hS
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, sigma, dite_eq_right hS]
        constructor
        · intro h
          omega
        · rintro ⟨k, _, hdet⟩
          have hmem : k.val ∈ supportIndices (rate := rate) (rewards := rewards)
              (C_star := C_star) (C_h := C_h) z :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, hdet⟩
          rw [hSempty] at hmem
          simp at hmem
    rw [hEq]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k.val + 1 ≤ n
    · have hdet := Pup_nonempty_measurable_at
        (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) control0 k.val
      have hdet' :=
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0).mono (by omega : k.val + 1 ≤ n) _ hdet
      simpa [hk] using hdet'
    · simp [hk]

/-- The last UP-detected endpoint is a stopping time. At intermediate source
dates its event is the earlier first-endpoint event and the empty test at the
immediately preceding UP-detected task set. -/
theorem theta_is_pre_round_stopping_time
    (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (theta (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h)) := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hempty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        theta (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) z ≤ 0} = ∅ := by
      ext z
      have hpos := (sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).1
      have hst := (sigma_theta_range (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) z).2.1
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [hempty]
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 0).measurableSet_empty
  · by_cases hnT : p.T + 1 ≤ n
    · have hwhole : {z : BootstrapPrivateRoundStreams.SourceInput p |
          theta (rate := rate) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) z ≤ n} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (sigma_theta_range (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) z).2.2.trans (by omega)
      rw [hwhole]
      exact MeasurableSet.univ
    · have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
      have hnT' : n ≤ p.T := by omega
      have hEq :
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            theta (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) z ≤ n} =
          {z | sigma (rate := rate) (rewards := rewards)
                (C_star := C_star) (C_h := C_h) z < n} ∩
            {z | ¬ (ReferenceFirstCollectionUpDetectedQueueMask.Pup
              (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) (n - 1) z).Nonempty} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        exact theta_le_iff (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) n hn0' hnT' z
      rw [hEq]
      apply (MeasurableSet.inter ?_ ?_)
      · have hsig := sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 (n - 1)
        have hsig' :=
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0).mono (by omega : n - 1 ≤ n) _ hsig
        apply hsig'.congr
        ext z
        simp only [Set.mem_ofPred_eq]
        omega
      · have hdet := Pup_nonempty_measurable_at
          (rate := rate) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) control0 (n - 1)
        have hdet' : MeasurableSet[
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
              control0 n]
            {z | (ReferenceFirstCollectionUpDetectedQueueMask.Pup
              (rate := rate) (rewards := rewards) (C_star := C_star)
              (C_h := C_h) (n - 1) z).Nonempty} := by
          have hnsub : (n - 1) + 1 = n := by omega
          rw [hnsub] at hdet
          exact hdet
        exact hdet'.compl

end Bandits.Support.ReferenceFirstCollectionUpDetectedPendingEndpoints

end
