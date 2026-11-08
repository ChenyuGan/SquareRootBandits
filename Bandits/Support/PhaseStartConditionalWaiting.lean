/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PhaseServiceWaiting
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional phase-start waiting bounds

This companion module localizes the integrated source phase-service bounds to
the stopped σ-algebra at the phase start. It uses the literal source-indexed
processes from `PhaseServiceWaiting`; protocol service, quota, stopping, and
within-phase nesting facts remain explicit inputs.

The source is `sources/zip4/manuscript/05_binary_transport.tex:180-240` and
`sources/zip4/manuscript/05_binary_transport.tex:244-285`.
-/

@[expose] public section

namespace Bandits.Support.PhaseStartConditionalWaiting

open MeasureTheory
open scoped BigOperators MeasureTheory Convex ENNReal

open Bandits.Support.PhaseServiceWaiting

/-- Convert a finite pre-round stopping time to Mathlib's `WithTop` stopping
time with the same bounded stopping convention. -/
theorem isStoppingTime_of_preRound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (ℱ : MeasureTheory.Filtration ℕ m) (τ : Ω → ℕ)
    (hτ : IsPreRoundStoppingTime ℱ τ) :
    MeasureTheory.IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)) := by
  intro n
  change MeasurableSet[ℱ n]
    {ω | (τ ω : WithTop ℕ) ≤ (n : WithTop ℕ)}
  have hset : {ω | (τ ω : WithTop ℕ) ≤ (n : WithTop ℕ)} =
      {ω | τ ω ≤ n} := by
    ext ω
    norm_cast
  rw [hset]
  exact hτ n

/-- The stopping σ-algebra supplied by Mathlib for the phase start. -/
@[instance_reducible] noncomputable def phaseStartSigmaAlgebra
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (ℱ : MeasureTheory.Filtration ℕ m) (sigma : Ω → ℕ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma) : MeasurableSpace Ω :=
  (isStoppingTime_of_preRound ℱ sigma hsigma).measurableSpace

/-- The literal task charge and service count are both zero immediately before
the phase starts. This includes `sigma = T + 1`, when the phase has no rounds
inside the horizon. -/
theorem start_state_zero
    {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (sigma theta : Ω → ℕ) (w : ℕ → Ω → ℝ)
    (hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (i : Fin d) (ω : Ω) :
    G P w i (sigma ω - 1) ω = 0 ∧ N P X i (sigma ω - 1) ω = 0 := by
  have hsigma_le_T : sigma ω - 1 ≤ T := by
    have hstart := hsigma_start ω
    have hle := hsigma_le_theta ω
    have hbound := htheta_bound ω
    omega
  have hbefore : ∀ t ∈ Finset.range (sigma ω - 1), i ∉ P t ω := by
    intro t ht hmem
    have htSigma : t + 1 < sigma ω := by
      have := Finset.mem_range.mp ht
      omega
    have htT : t < T := by omega
    have hsupport := (hphase t htT ω ⟨i, hmem⟩).1
    omega
  constructor
  · unfold G
    apply Finset.sum_eq_zero
    intro t ht
    have hnot := hbefore t ht
    simp [J, hnot]
  · unfold N
    apply Finset.sum_eq_zero
    intro t ht
    have hnot := hbefore t ht
    simp [hnot]

/-- The stopped σ-algebra is included in the ambient probability σ-algebra. -/
theorem phaseStartSigmaAlgebra_le
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (ℱ : MeasureTheory.Filtration ℕ m) (sigma : Ω → ℕ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma) :
    phaseStartSigmaAlgebra ℱ sigma hsigma ≤ m := by
  exact (isStoppingTime_of_preRound ℱ sigma hsigma).measurableSpace_le

/-- A stopped-measurable set, intersected with the task-active event for a
source round, is measurable before that round's service observation. -/
theorem phaseStart_inter_task_measurable
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {d T : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) (t : ℕ) (ht : t < T) :
    MeasurableSet[ℱ (t + 1)] (B ∩ {ω | i ∈ P t ω}) := by
  let hstop := isStoppingTime_of_preRound ℱ sigma hsigma
  have hBstop := (hstop.measurableSet B).mp hB
  have hBstart : MeasurableSet[ℱ (t + 1)]
      (B ∩ {ω | sigma ω ≤ t + 1}) := by
    have hset : B ∩ {ω | (sigma ω : WithTop ℕ) ≤ ((t + 1 : ℕ) : WithTop ℕ)} =
        B ∩ {ω | sigma ω ≤ t + 1} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨hBω, h⟩ <;>
        exact ⟨hBω, by exact_mod_cast h⟩
    rw [← hset]
    exact hBstop.2 (t + 1)
  have heq : B ∩ {ω | i ∈ P t ω} =
      (B ∩ {ω | sigma ω ≤ t + 1}) ∩ {ω | i ∈ P t ω} := by
    ext ω
    constructor
    · intro hω
      refine ⟨?_, hω.2⟩
      refine ⟨hω.1, ?_⟩
      have hne : (P t ω).Nonempty := ⟨i, hω.2⟩
      exact (hphase t ht ω hne).1
    · intro hω
      exact ⟨hω.1.1, hω.2⟩
  rw [heq]
  exact hBstart.inter (hP i t ht)

/-- Measurability of the phase-active event localized to a stopped-measurable
set, using only source phase support. -/
theorem phaseStart_inter_active_measurable
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {d T : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (sigma theta : Ω → ℕ)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (t : ℕ) (ht : t < T) :
    MeasurableSet[ℱ (t + 1)]
      (B ∩ {ω | (P t ω).Nonempty}) := by
  have heq : {ω | (P t ω).Nonempty} =
      ⋃ i : Fin d, {ω | i ∈ P t ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.Nonempty]
  have hactive : MeasurableSet[ℱ (t + 1)] {ω | (P t ω).Nonempty} := by
    rw [heq]
    exact MeasurableSet.iUnion fun i => hP i t ht
  have hBactive : MeasurableSet[ℱ (t + 1)]
      (B ∩ {ω | sigma ω ≤ t + 1}) := by
    have hBstop := ((isStoppingTime_of_preRound ℱ sigma hsigma).measurableSet B).mp hB
    have hset : B ∩ {ω | (sigma ω : WithTop ℕ) ≤ ((t + 1 : ℕ) : WithTop ℕ)} =
        B ∩ {ω | sigma ω ≤ t + 1} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨hBω, h⟩ <;>
        exact ⟨hBω, by exact_mod_cast h⟩
    rw [← hset]
    exact hBstop.2 (t + 1)
  have heq' : B ∩ {ω | (P t ω).Nonempty} =
      (B ∩ {ω | sigma ω ≤ t + 1}) ∩ {ω | (P t ω).Nonempty} := by
    ext ω
    constructor
    · intro hω
      exact ⟨⟨hω.1, (hphase t ht ω hω.2).1⟩, hω.2⟩
    · intro hω
      exact ⟨hω.1.1, hω.2⟩
  rw [heq']
  exact hBactive.inter hactive

/-- The source one-round exponential supermartingale inequality remains valid
after restricting to the portion of a stopped-measurable set already inside
the phase. -/
theorem localized_Z_step
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) (t : ℕ) (ht : t < T) :
    ∫ ω in B, Z P X w a i (t + 1) ω ∂μ ≤
      ∫ ω in B, Z P X w a i t ω ∂μ := by
  let stop := isStoppingTime_of_preRound ℱ sigma hsigma
  let E := B ∩ {ω | sigma ω ≤ t + 1}
  have hE : MeasurableSet[ℱ (t + 1)] E := by
    have hBstop := (stop.measurableSet B).mp hB
    have h := hBstop.2 (t + 1)
    have hset : B ∩ {ω | (sigma ω : WithTop ℕ) ≤ ((t + 1 : ℕ) : WithTop ℕ)} = E := by
      ext ω
      simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨hBω, h⟩ <;>
        exact ⟨hBω, by exact_mod_cast h⟩
    rw [← hset]
    exact h
  have hBambient : MeasurableSet[m] B :=
    (phaseStartSigmaAlgebra_le ℱ sigma hsigma) B hB
  have hEambient : MeasurableSet[m] E := (ℱ.le (t + 1)) E hE
  have hnextInt := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound hX_meas
    i (t + 1) (by omega)
  have hprevInt := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound hX_meas
    i t (by omega)
  have hstep := Z_supermartingale_step μ ℱ P X w a ha hP hw_meas hw_bound
    hX_meas hservice i t ht
  have hlocal :
      ∫ ω in E, Z P X w a i (t + 1) ω ∂μ ≤
        ∫ ω in E, Z P X w a i t ω ∂μ := by
    calc
      ∫ ω in E, Z P X w a i (t + 1) ω ∂μ =
          ∫ ω in E, μ[fun ω => Z P X w a i (t + 1) ω | ℱ (t + 1)] ω ∂μ := by
        symm
        exact setIntegral_condExp (ℱ.le (t + 1)) hnextInt hE
      _ ≤ ∫ ω in E, Z P X w a i t ω ∂μ :=
        setIntegral_mono_ae integrable_condExp.integrableOn hprevInt.integrableOn hstep
  have hzeroBefore : ∀ ω, sigma ω > t + 1 →
      Z P X w a i (t + 1) ω = Z P X w a i t ω := by
    intro ω hafter
    have hnot : ∀ s ∈ Finset.range (t + 1), i ∉ P s ω := by
      intro s hs hmem
      have hslt : s < t + 1 := Finset.mem_range.mp hs
      have hsT : s ≤ t := by omega
      have hsT' : s < T := lt_of_le_of_lt hsT ht
      have hsSupport := (hphase s hsT' ω ⟨i, hmem⟩).1
      have hindex : s + 1 ≤ t + 1 := Nat.add_le_add_right hsT 1
      omega
    have hG : G P w i (t + 1) ω = G P w i t ω := by
      have hzero : J P i t ω * w t ω = 0 := by
        have hnot := hnot t (Finset.mem_range.mpr (Nat.lt_succ_self t))
        simp [J, hnot]
      rw [G_succ, hzero, add_zero]
    have hN : N P X i (t + 1) ω = N P X i t ω := by
      rw [N_succ]
      have hnot := hnot t (Finset.mem_range.mpr (Nat.lt_succ_self t))
      simp [hnot]
    change Real.exp (kappa * a * G P w i (t + 1) ω -
      (N P X i (t + 1) ω : ℝ)) =
      Real.exp (kappa * a * G P w i t ω - (N P X i t ω : ℝ))
    rw [hG, hN]
  have hdiffSet :
      ∫ ω in B, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ =
        ∫ ω in E, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ := by
    rw [← integral_indicator hBambient, ← integral_indicator hEambient]
    apply integral_congr_ae
    apply ae_of_all
    intro ω
    by_cases hωB : ω ∈ B
    · by_cases hωStart : sigma ω ≤ t + 1
      · simp [E, hωB, hωStart]
      · have hz := hzeroBefore ω (Nat.lt_of_not_ge hωStart)
        simp [E, hωB, hωStart, hz]
    · simp [E, hωB]
  have hBdiff :
      ∫ ω in B, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ ≤ 0 := by
    rw [hdiffSet]
    have hsub := integral_sub' (μ := μ.restrict E) hnextInt.integrableOn
      hprevInt.integrableOn
    calc
      ∫ ω in E, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ =
          ∫ ω in E, Z P X w a i (t + 1) ω ∂μ -
            ∫ ω in E, Z P X w a i t ω ∂μ := hsub
      _ ≤ 0 := sub_nonpos.mpr hlocal
  have hsubB := integral_sub' (μ := μ.restrict B) hnextInt.integrableOn
    hprevInt.integrableOn
  have hidentity :
      ∫ ω in B, Z P X w a i (t + 1) ω ∂μ =
        ∫ ω in B, Z P X w a i t ω ∂μ +
          ∫ ω in B, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ := by
    calc
      ∫ ω in B, Z P X w a i (t + 1) ω ∂μ =
          ∫ ω in B, Z P X w a i t ω ∂μ +
            (∫ ω in B, Z P X w a i (t + 1) ω ∂μ -
              ∫ ω in B, Z P X w a i t ω ∂μ) := by ring
      _ = ∫ ω in B, Z P X w a i t ω ∂μ +
            ∫ ω in B, (Z P X w a i (t + 1) ω - Z P X w a i t ω) ∂μ := by
        congr 1
        exact hsubB.symm
  rw [hidentity]
  linarith

/-- Localized expectation of the source exponential process at a deterministic
prefix. The proof starts at one and adds only increments after the random
phase-start time; no value is supplied for an inactive phase. -/
theorem localized_Z_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) :
    ∫ ω in B, Z P X w a i T ω ∂μ ≤ μ.real B := by
  have hrec : ∀ v, v ≤ T →
      ∫ ω in B, Z P X w a i v ω ∂μ ≤ μ.real B := by
    intro v
    induction v with
    | zero =>
        intro _
        simp [Z, G, N, smul_eq_mul]
    | succ v ih =>
        intro hv
        have ht : v < T := by omega
        calc
          ∫ ω in B, Z P X w a i (v + 1) ω ∂μ ≤
              ∫ ω in B, Z P X w a i v ω ∂μ :=
            localized_Z_step μ ℱ P X w sigma theta a ha hsigma hP hphase
              hw_meas hw_bound hX_meas hservice B hB i v ht
          _ ≤ μ.real B := ih (by omega)
  exact hrec T le_rfl

/-- Integrability of the exponential of one task's literal predictable
charge, derived from the producer's boundedness and measurability lemmas. -/
theorem task_charge_exponential_integrable
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (i : Fin d) :
    Integrable (fun ω => Real.exp (kappa * a * G P w i T ω)) μ := by
  have hGsm := (G_stronglyMeasurable ℱ P w hP hw_meas i T le_rfl).mono
    (ℱ.le (T + 1))
  have hargSm : StronglyMeasurable[m]
      (fun ω => kappa * a * G P w i T ω) := by
    exact stronglyMeasurable_const.mul hGsm
  have hexpSm := Real.continuous_exp.comp_stronglyMeasurable hargSm
  have hG := fun ω => G_mem_Icc P w hw_bound i T le_rfl ω
  have hExpBound : ∀ ω,
      Real.exp (kappa * a * G P w i T ω) ∈
        Set.Icc (0 : ℝ) (Real.exp (a * (T : ℝ) * (K : ℝ))) := by
    intro ω
    have hmul : kappa * a * G P w i T ω ≤ a * G P w i T ω := by
      calc
        kappa * a * G P w i T ω = kappa * (a * G P w i T ω) := by ring
        _ ≤ 1 * (a * G P w i T ω) :=
          mul_le_mul_of_nonneg_right kappa_le_one (mul_nonneg ha.le (hG ω).1)
        _ = a * G P w i T ω := one_mul _
    have hupper : a * G P w i T ω ≤ a * ((T : ℝ) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (hG ω).2 ha.le
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_exp.mpr
      nlinarith [hmul, hupper]
  apply Integrable.of_mem_Icc (μ := μ) 0 _
    (hexpSm.aemeasurable (μ := μ))
  exact ae_of_all μ hExpBound

/-- Localized task exponential moment, with mass `mu(B)` retained. -/
theorem localized_task_exponential_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) :
    ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ ≤
      Real.exp (q : ℝ) * μ.real B := by
  have hZbound := localized_Z_integral_bound μ ℱ P X w sigma theta a ha hsigma
    hP hphase hw_meas hw_bound hX_meas hservice B hB i
  have hZint := Z_integrable μ ℱ P X w a ha hP hw_meas hw_bound hX_meas
    i T le_rfl
  have hExpInt := task_charge_exponential_integrable μ ℱ P w a ha
    hP hw_meas hw_bound i
  have hNle : ∀ ω, N P X i T ω ≤ q := by
    intro ω
    exact N_le_quota P X hquota i T le_rfl ω
  have hpoint : ∀ ω,
      Real.exp (kappa * a * G P w i T ω) ≤
        Real.exp (q : ℝ) * Z P X w a i T ω := by
    intro ω
    have hEq : Real.exp (kappa * a * G P w i T ω) =
        Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) := by
      calc
        Real.exp (kappa * a * G P w i T ω) =
            Real.exp ((kappa * a * G P w i T ω - (N P X i T ω : ℝ)) +
              (N P X i T ω : ℝ)) := by congr 1; ring
        _ = Real.exp (kappa * a * G P w i T ω -
              (N P X i T ω : ℝ)) * Real.exp (N P X i T ω : ℝ) := Real.exp_add _ _
        _ = Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) := by rw [Z]
    rw [hEq]
    have hNat : (N P X i T ω : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNle ω
    calc
      Z P X w a i T ω * Real.exp (N P X i T ω : ℝ) ≤
          Z P X w a i T ω * Real.exp (q : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hNat) (Real.exp_pos _).le
      _ = Real.exp (q : ℝ) * Z P X w a i T ω := mul_comm _ _
  calc
    ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ ≤
        ∫ ω in B, Real.exp (q : ℝ) * Z P X w a i T ω ∂μ :=
      setIntegral_mono_ae hExpInt.integrableOn (hZint.const_mul _).integrableOn
        (ae_of_all μ hpoint)
    _ = Real.exp (q : ℝ) * ∫ ω in B, Z P X w a i T ω ∂μ := by
      rw [integral_const_mul]
    _ ≤ Real.exp (q : ℝ) * μ.real B :=
      mul_le_mul_of_nonneg_left hZbound (Real.exp_pos _).le

/-- Integrability of a task's literal predictable charge from the producer's
measurability and pathwise bounds. -/
theorem task_charge_integrable
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K : ℕ} (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (w : ℕ → Ω → ℝ)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (i : Fin d) : Integrable (G P w i T) μ := by
  have hGsm := (G_stronglyMeasurable ℱ P w hP hw_meas i T le_rfl).mono
    (ℱ.le (T + 1))
  apply Integrable.of_mem_Icc (μ := μ) 0 ((T : ℝ) * (K : ℝ))
    (hGsm.aemeasurable (μ := μ))
  exact ae_of_all μ fun ω => G_mem_Icc P w hw_bound i T le_rfl ω

/-- A task's `J`-weighted integral over a set is the corresponding integral
over that set intersected with the task-active event. -/
theorem setIntegral_J_mul_eq
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (P : ℕ → Ω → Finset (Fin d))
    (i : Fin d) (t : ℕ) (B : Set Ω) (f : Ω → ℝ)
    (hP : MeasurableSet {ω | i ∈ P t ω}) :
    ∫ ω in B, J P i t ω * f ω ∂μ =
      ∫ ω in B ∩ {ω | i ∈ P t ω}, f ω ∂μ := by
  rw [J_mul_eq_indicator, setIntegral_indicator hP]

/-- The source task-wise predictable-charge estimate localized to every set in
the phase-start σ-algebra. -/
theorem phase_start_task_charge_setIntegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (_hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (_htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (_hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (_hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B)
    (i : Fin d) :
    ∫ ω in B, G P w i T ω ∂μ ≤ ((q : ℝ) / a) * μ.real B := by
  have hBambient : MeasurableSet[m] B :=
    (phaseStartSigmaAlgebra_le ℱ sigma hsigma) B hB
  have hwInt : ∀ t, t < T → Integrable (w t) μ := by
    intro t ht
    have hsm := (hw_meas t ht).mono (ℱ.le (t + 1))
    apply Integrable.of_mem_Icc (μ := μ) 0 (K : ℝ) (hsm.aemeasurable (μ := μ))
    exact ae_of_all μ (hw_bound t ht)
  have hobsInt : ∀ t, t < T → Integrable (observation X i t) μ := by
    intro t ht
    have hsm := (hX_meas i t ht).mono (ℱ.le (t + 2))
    apply Integrable.of_mem_Icc (μ := μ) 0 1 (hsm.aemeasurable (μ := μ))
    exact ae_of_all μ (observation_mem_unit_interval X i t)
  have hWtermInt : ∀ t, t < T →
      Integrable (fun ω => J P i t ω * w t ω) μ := by
    intro t ht
    have hJsm := (J_stronglyMeasurable ℱ P i t (hP i t ht)).mono
      (ℱ.le (t + 1))
    have hWsm := (hw_meas t ht).mono (ℱ.le (t + 1))
    have hsm := hJsm.mul hWsm
    have hbound : ∀ ω, J P i t ω * w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ) := by
      intro ω
      have hJ := J_mem_unit_interval P i t ω
      have hw := hw_bound t ht ω
      constructor
      · exact mul_nonneg hJ.1 hw.1
      · calc
          J P i t ω * w t ω ≤ 1 * w t ω :=
            mul_le_mul_of_nonneg_right hJ.2 hw.1
          _ = w t ω := one_mul _
          _ ≤ (K : ℝ) := hw.2
    apply Integrable.of_mem_Icc (μ := μ) 0 (K : ℝ)
      (hsm.aemeasurable (μ := μ))
    exact ae_of_all μ hbound
  have hXtermInt : ∀ t, t < T →
      Integrable (fun ω => J P i t ω * observation X i t ω) μ := by
    intro t ht
    have hJsm := (J_stronglyMeasurable ℱ P i t (hP i t ht)).mono
      (ℱ.le (t + 1))
    have hXsm := (hX_meas i t ht).mono (ℱ.le (t + 2))
    have hsm := hJsm.mul hXsm
    have hbound : ∀ ω,
        J P i t ω * observation X i t ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro ω
      have hJ := J_mem_unit_interval P i t ω
      have hX := observation_mem_unit_interval X i t ω
      constructor
      · exact mul_nonneg hJ.1 hX.1
      · calc
          J P i t ω * observation X i t ω ≤ 1 * observation X i t ω :=
            mul_le_mul_of_nonneg_right hJ.2 hX.1
          _ = observation X i t ω := one_mul _
          _ ≤ 1 := hX.2
    apply Integrable.of_mem_Icc (μ := μ) 0 1 (hsm.aemeasurable (μ := μ))
    exact ae_of_all μ hbound
  have hNsm : StronglyMeasurable[m]
      (fun ω => (N P X i T ω : ℝ)) := by
    have hNsm' : StronglyMeasurable[ℱ (T + 1)]
        (fun ω => (N P X i T ω : ℝ)) := by
      have heq : (fun ω => (N P X i T ω : ℝ)) =
          fun ω => ∑ t ∈ Finset.range T,
            J P i t ω * observation X i t ω := by
        funext ω
        exact N_cast_eq_source_sum P X i T ω
      rw [heq]
      apply Finset.stronglyMeasurable_fun_sum
      intro t ht
      have htT : t < T := Finset.mem_range.mp ht
      have hJsm := (J_stronglyMeasurable ℱ P i t (hP i t htT)).mono
        (ℱ.mono (by omega : t + 1 ≤ T + 1))
      have hXsm := (hX_meas i t htT).mono
        (ℱ.mono (by omega : t + 2 ≤ T + 1))
      exact hJsm.mul hXsm
    exact hNsm'.mono (ℱ.le (T + 1))
  have hNint : Integrable (fun ω => (N P X i T ω : ℝ)) μ := by
    have hbound : ∀ ω,
        (N P X i T ω : ℝ) ∈ Set.Icc (0 : ℝ) (q : ℝ) := by
      intro ω
      constructor
      · exact Nat.cast_nonneg _
      · exact_mod_cast N_le_quota P X hquota i T le_rfl ω
    apply Integrable.of_mem_Icc (μ := μ) 0 (q : ℝ)
      (hNsm.aemeasurable (μ := μ))
    exact ae_of_all μ hbound
  have hGsum :
      ∫ ω in B, G P w i T ω ∂μ =
        ∑ t ∈ Finset.range T, ∫ ω in B,
          J P i t ω * w t ω ∂μ := by
    change ∫ ω, (∑ t ∈ Finset.range T,
      J P i t ω * w t ω) ∂μ.restrict B = _
    rw [integral_finsetSum]
    intro t ht
    exact (hWtermInt t (Finset.mem_range.mp ht)).integrableOn
  have hNsum :
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ =
        ∑ t ∈ Finset.range T,
          ∫ ω in B, J P i t ω * observation X i t ω ∂μ := by
    calc
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ =
          ∫ ω, ∑ t ∈ Finset.range T,
            J P i t ω * observation X i t ω ∂μ.restrict B := by
        simp only [N_cast_eq_source_sum]
      _ = ∑ t ∈ Finset.range T,
          ∫ ω in B, J P i t ω * observation X i t ω ∂μ := by
        rw [integral_finsetSum]
        intro t ht
        exact (hXtermInt t (Finset.mem_range.mp ht)).integrableOn
  have hGsum' :
      ∫ ω in B, G P w i T ω ∂μ =
        ∑ t ∈ Finset.range T,
          ∫ ω in B ∩ {ω | i ∈ P t ω}, w t ω ∂μ := by
    calc
      ∫ ω in B, G P w i T ω ∂μ =
          ∑ t ∈ Finset.range T,
            ∫ ω in B, J P i t ω * w t ω ∂μ := hGsum
      _ = ∑ t ∈ Finset.range T,
          ∫ ω in B ∩ {ω | i ∈ P t ω}, w t ω ∂μ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_J_mul_eq μ P i t B (w t)
          ((ℱ.le (t + 1)) _ (hP i t (Finset.mem_range.mp ht)))
  have hNsum' :
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ =
        ∑ t ∈ Finset.range T,
          ∫ ω in B ∩ {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
    calc
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ =
          ∑ t ∈ Finset.range T,
            ∫ ω in B, J P i t ω * observation X i t ω ∂μ := hNsum
      _ = ∑ t ∈ Finset.range T,
          ∫ ω in B ∩ {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_J_mul_eq μ P i t B (observation X i t)
          ((ℱ.le (t + 1)) _ (hP i t (Finset.mem_range.mp ht)))
  have hserviceSum :
      (a : ℝ) * (∑ t ∈ Finset.range T,
        ∫ ω in B ∩ {ω | i ∈ P t ω}, w t ω ∂μ) ≤
        ∑ t ∈ Finset.range T,
          ∫ ω in B ∩ {ω | i ∈ P t ω}, observation X i t ω ∂μ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    let S := B ∩ {ω | i ∈ P t ω}
    have hS : MeasurableSet[ℱ (t + 1)] S := by
      exact phaseStart_inter_task_measurable ℱ P sigma theta hsigma hP _hphase
        B hB i t htT
    have hsvc : ∀ᵐ ω ∂μ, ω ∈ S →
        a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω := by
      filter_upwards [hservice i t htT] with ω hω
      intro hωS
      exact hω hωS.2
    have hstep := conditional_service_integral μ (ℱ (t + 1))
      (ℱ.le (t + 1)) (observation X i t) (w t) S hS a
      (hobsInt t htT) (hwInt t htT) hsvc
    simpa [S] using hstep
  have hserviceInt :
      (a : ℝ) * (∫ ω in B, G P w i T ω ∂μ) ≤
        ∫ ω in B, (N P X i T ω : ℝ) ∂μ := by
    rw [hGsum', hNsum']
    exact hserviceSum
  have hquotaInt :
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ ≤ (q : ℝ) * μ.real B := by
    calc
      ∫ ω in B, (N P X i T ω : ℝ) ∂μ ≤
          ∫ ω in B, (fun _ : Ω => (q : ℝ)) ω ∂μ :=
        setIntegral_mono_ae hNint.integrableOn (integrable_const _).integrableOn
          (ae_of_all μ fun ω => by
            change (N P X i T ω : ℝ) ≤ (q : ℝ)
            exact_mod_cast N_le_quota P X hquota i T le_rfl ω)
      _ = (q : ℝ) * μ.real B := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]
  have hcore := hserviceInt.trans hquotaInt
  calc
    ∫ ω in B, G P w i T ω ∂μ =
        (a : ℝ)⁻¹ * ((a : ℝ) * ∫ ω in B, G P w i T ω ∂μ) := by
      field_simp
    _ ≤ (a : ℝ)⁻¹ * ((q : ℝ) * μ.real B) :=
      mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr ha.le)
    _ = ((q : ℝ) / a) * μ.real B := by ring

/-- Set-integral localization is equivalent to an almost-everywhere upper
bound on the conditional expectation for the same σ-algebra. -/
theorem setIntegral_iff_condExp_le
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m' : MeasurableSpace Ω) (hm' : m' ≤ m)
    (f : Ω → ℝ) (c : ℝ) (hf : Integrable f μ) :
    (∀ B, MeasurableSet[m'] B →
      ∫ ω in B, f ω ∂μ ≤ c * μ.real B) ↔
        μ[f | m'] ≤ᵐ[μ] fun _ => c := by
  constructor
  · intro hset
    change (∀ᵐ ω ∂μ, μ[f | m'] ω ≤ c)
    rw [ae_le_const_iff_forall_gt_measure_zero]
    intro b hbc
    let B := {ω | b ≤ μ[f | m'] ω}
    have hB : MeasurableSet[m'] B := by
      exact stronglyMeasurable_const.measurableSet_le stronglyMeasurable_condExp
    have hBambient : MeasurableSet[m] B := hm' B hB
    by_contra hBne
    have hBfinite : μ B ≠ ∞ := measure_ne_top μ B
    have hBrealPos : 0 < μ.real B := ENNReal.toReal_pos hBne hBfinite
    have hmono :
        ∫ ω in B, (fun _ : Ω => b) ω ∂μ ≤ ∫ ω in B, μ[f | m'] ω ∂μ :=
      setIntegral_mono_on (integrable_const b).integrableOn
        integrable_condExp.integrableOn hBambient fun ω hω => hω
    have hconst :
        ∫ ω in B, (fun _ : Ω => b) ω ∂μ = b * μ.real B := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]
    have hceInt :
        ∫ ω in B, μ[f | m'] ω ∂μ = ∫ ω in B, f ω ∂μ :=
      setIntegral_condExp hm' hf hB
    have hbound := hset B hB
    have hcontr : b * μ.real B ≤ c * μ.real B := by
      calc
        b * μ.real B = ∫ ω in B, (fun _ : Ω => b) ω ∂μ := hconst.symm
        _ ≤ ∫ ω in B, μ[f | m'] ω ∂μ := hmono
        _ = ∫ ω in B, f ω ∂μ := hceInt
        _ ≤ c * μ.real B := hbound
    exact (not_le_of_gt (mul_pos (sub_pos.mpr hbc) hBrealPos))
      (by nlinarith [hcontr])
  · intro hce B hB
    calc
      ∫ ω in B, f ω ∂μ = ∫ ω in B, μ[f | m'] ω ∂μ :=
        (setIntegral_condExp hm' hf hB).symm
      _ ≤ ∫ ω in B, (fun _ : Ω => c) ω ∂μ :=
        setIntegral_mono_ae integrable_condExp.integrableOn
          (integrable_const c).integrableOn hce
      _ = c * μ.real B := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]

/-- The phase's localized exponential moment. It is obtained by taking the
maximum of the same nested task charges and summing their localized moments. -/
theorem phase_start_totalCharge_exponential_setIntegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B) :
    ∫ ω in B, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
      (d : ℝ) * Real.exp (q : ℝ) * μ.real B := by
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have htaskInt : ∀ i : Fin d,
      Integrable (fun ω => Real.exp (kappa * a * G P w i T ω)) μ := by
    intro i
    exact task_charge_exponential_integrable μ ℱ P w a ha hP hw_meas
      hw_bound i
  have hsumInt :
      Integrable (fun ω => ∑ i ∈ Finset.univ,
        Real.exp (kappa * a * G P w i T ω)) μ := by
    apply integrable_finsetSum
    intro i hi
    exact htaskInt i
  have hpoint : ∀ ω,
      Real.exp (kappa * a * totalCharge P sigma theta w T ω) ≤
        ∑ i ∈ Finset.univ, Real.exp (kappa * a * G P w i T ω) := by
    intro ω
    have hmax := totalCharge_eq_maxTaskCharge hd P sigma theta w
      hphase hnested (fun t ht ω => (hw_bound t ht ω).1) ω
    have hFinNonempty : (Finset.univ : Finset (Fin d)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
    obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup' hFinNonempty (fun i => G P w i T ω)
    rw [hmax]
    change Real.exp (kappa * a *
      Finset.univ.sup' hFinNonempty (fun j => G P w j T ω)) ≤ _
    rw [hsup]
    exact Finset.single_le_sum
      (f := fun j : Fin d => Real.exp (kappa * a * G P w j T ω))
      (fun j hj => (Real.exp_pos _).le) hi
  have hsumSet :
      ∫ ω in B, (∑ i ∈ Finset.univ,
        Real.exp (kappa * a * G P w i T ω)) ∂μ =
        ∑ i ∈ Finset.univ,
          ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ := by
    rw [integral_finsetSum]
    intro i hi
    exact (htaskInt i).integrableOn
  calc
    ∫ ω in B, Real.exp (kappa * a * totalCharge P sigma theta w T ω) ∂μ ≤
        ∫ ω in B, (∑ i ∈ Finset.univ,
          Real.exp (kappa * a * G P w i T ω)) ∂μ :=
      setIntegral_mono_ae htotalInt.2.integrableOn hsumInt.integrableOn
        (ae_of_all μ hpoint)
    _ = ∑ i ∈ Finset.univ,
        ∫ ω in B, Real.exp (kappa * a * G P w i T ω) ∂μ := hsumSet
    _ ≤ ∑ i ∈ Finset.univ,
        Real.exp (q : ℝ) * μ.real B := by
      apply Finset.sum_le_sum
      intro i hi
      exact localized_task_exponential_bound μ ℱ P X w sigma theta a ha
        hsigma hP hphase hw_meas hw_bound hX_meas hquota hservice B hB i
    _ = (d : ℝ) * Real.exp (q : ℝ) * μ.real B := by simp [mul_assoc]

/-- The localized exponential moment and restricted-set Jensen yield the
source total-charge estimate with the exact factor `mu(B)`, including null
sets. -/
theorem phase_start_totalCharge_setIntegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (B : Set Ω) (hB : MeasurableSet[phaseStartSigmaAlgebra ℱ sigma hsigma] B) :
    ∫ ω in B, totalCharge P sigma theta w T ω ∂μ ≤
      (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) * μ.real B := by
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have hcpos : 0 < kappa * a := mul_pos kappa_pos ha
  by_cases hBzero : μ B = 0
  · have hBreal : μ.real B = 0 := by simp [measureReal_def, hBzero]
    have hrestrict : μ.restrict B = 0 := Measure.restrict_eq_zero.2 hBzero
    change ∫ ω, totalCharge P sigma theta w T ω ∂μ.restrict B ≤ _
    rw [hrestrict, integral_zero_measure]
    simp [hBreal]
  · have hBfinite : μ B ≠ ∞ := measure_ne_top μ B
    have hBrealPos : 0 < μ.real B := ENNReal.toReal_pos hBzero hBfinite
    let c : ℝ := kappa * a
    have hconvex : ConvexOn ℝ Set.univ
        (fun x : ℝ => Real.exp (c * x)) := by
      convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ c) using 1
    have hJensen :
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
          ⨍ ω in B,
            Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := by
      simpa [Function.comp_def, c] using
        hconvex.map_set_average_le
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
          isClosed_univ hBzero hBfinite
          (ae_of_all (μ.restrict B) fun _ => Set.mem_univ _)
          htotalInt.1.integrableOn htotalInt.2.integrableOn
    have hExpSet := phase_start_totalCharge_exponential_setIntegral_bound
      μ hd _hT _hK _hq ℱ P X w sigma theta a ha hsigma htheta
      _hsigma_start _hsigma_le_theta _htheta_bound hP hphase hnested
      hw_meas hw_bound hX_meas hquota hservice B hB
    have hAvgExp :
        (⨍ ω in B,
          Real.exp (c * totalCharge P sigma theta w T ω) ∂μ) ≤
          (d : ℝ) * Real.exp (q : ℝ) := by
      rw [setAverage_eq]
      calc
        (μ.real B)⁻¹ * ∫ ω in B,
            Real.exp (c * totalCharge P sigma theta w T ω) ∂μ ≤
          (μ.real B)⁻¹ *
            ((d : ℝ) * Real.exp (q : ℝ) * μ.real B) :=
          mul_le_mul_of_nonneg_left hExpSet (inv_nonneg.mpr hBrealPos.le)
        _ = (d : ℝ) * Real.exp (q : ℝ) := by
          field_simp [ne_of_gt hBrealPos]
    have hmeanExp :
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
          Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
      calc
        Real.exp (c * (⨍ ω in B, totalCharge P sigma theta w T ω ∂μ)) ≤
            ⨍ ω in B,
              Real.exp (c * totalCharge P sigma theta w T ω) ∂μ := hJensen
        _ ≤ (d : ℝ) * Real.exp (q : ℝ) := hAvgExp
        _ = Real.exp (Real.log (d : ℝ) + (q : ℝ)) := by
          rw [Real.exp_add]
          congr 1
          exact (Real.exp_log (Nat.cast_pos.mpr hd)).symm
    have hmean := Real.exp_le_exp.mp hmeanExp
    have havgIntegral := measure_smul_setAverage
      (fun ω => totalCharge P sigma theta w T ω) hBfinite
    have hscaled :
        c * (∫ ω in B, totalCharge P sigma theta w T ω ∂μ) ≤
          ((q : ℝ) + Real.log (d : ℝ)) * μ.real B := by
      calc
        c * (∫ ω in B, totalCharge P sigma theta w T ω ∂μ) =
            μ.real B * (c * (⨍ ω in B,
              totalCharge P sigma theta w T ω ∂μ)) := by
          rw [← havgIntegral]
          simp only [smul_eq_mul]
          ring
        _ ≤ μ.real B * ((q : ℝ) + Real.log (d : ℝ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hmean])
            (measureReal_nonneg)
        _ = ((q : ℝ) + Real.log (d : ℝ)) * μ.real B := mul_comm _ _
    calc
      ∫ ω in B, totalCharge P sigma theta w T ω ∂μ =
          c⁻¹ * (c * ∫ ω in B, totalCharge P sigma theta w T ω ∂μ) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
      _ ≤ c⁻¹ * (((q : ℝ) + Real.log (d : ℝ)) * μ.real B) :=
        mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hcpos.le)
      _ = (((q : ℝ) + Real.log (d : ℝ)) / c) * μ.real B := by
        rw [div_eq_mul_inv]
        ring

/-- The task-wise waiting bound as an almost-everywhere conditional
expectation inequality under the actual Mathlib stopping σ-algebra. -/
theorem phase_start_task_charge_condExp_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (_htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (_hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (_hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω)
    (i : Fin d) :
    μ[(fun ω => G P w i T ω) | phaseStartSigmaAlgebra ℱ sigma hsigma] ≤ᵐ[μ]
      fun _ => (q : ℝ) / a := by
  let mσ := phaseStartSigmaAlgebra ℱ sigma hsigma
  have hmσ : mσ ≤ m := phaseStartSigmaAlgebra_le ℱ sigma hsigma
  have hGint := task_charge_integrable μ ℱ P w hP hw_meas hw_bound i
  have hset : ∀ B, MeasurableSet[mσ] B →
      ∫ ω in B, G P w i T ω ∂μ ≤ ((q : ℝ) / a) * μ.real B := by
    intro B hB
    exact phase_start_task_charge_setIntegral_bound μ hd _hT _hK _hq
      ℱ P X w sigma theta a ha hsigma _htheta _hsigma_start
      _hsigma_le_theta _htheta_bound hP _hphase _hnested hw_meas hw_bound
      hX_meas hquota hservice B hB i
  exact (setIntegral_iff_condExp_le μ mσ hmσ (fun ω => G P w i T ω)
    ((q : ℝ) / a)
    hGint).mp hset

/-- The total phase waiting bound as an almost-everywhere conditional
expectation inequality under the actual Mathlib stopping σ-algebra. -/
theorem phase_start_totalCharge_condExp_bound
    {Ω : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d T K q : ℕ} (hd : 0 < d) (_hT : 0 < T) (_hK : 0 < K) (_hq : 0 < q)
    (ℱ : MeasureTheory.Filtration ℕ m)
    (P : ℕ → Ω → Finset (Fin d)) (X : Fin d → ℕ → Ω → Bool)
    (w : ℕ → Ω → ℝ) (sigma theta : Ω → ℕ) (a : ℝ) (ha : 0 < a)
    (hsigma : IsPreRoundStoppingTime ℱ sigma)
    (htheta : IsPreRoundStoppingTime ℱ theta)
    (_hsigma_start : ∀ ω, 1 ≤ sigma ω)
    (_hsigma_le_theta : ∀ ω, sigma ω ≤ theta ω)
    (_htheta_bound : ∀ ω, theta ω ≤ T + 1)
    (hP : ∀ i t, t < T →
      MeasurableSet[ℱ (t + 1)] {ω | i ∈ P t ω})
    (hphase : ∀ t, t < T → ∀ ω, (P t ω).Nonempty →
      sigma ω ≤ t + 1 ∧ t + 1 < theta ω)
    (hnested : ∀ s t, s ≤ t → t < T → ∀ ω,
      sigma ω ≤ s + 1 → t + 1 < theta ω → P t ω ⊆ P s ω)
    (hw_meas : ∀ t, t < T →
      StronglyMeasurable[ℱ (t + 1)] (w t))
    (hw_bound : ∀ t, t < T → ∀ ω,
      w t ω ∈ Set.Icc (0 : ℝ) (K : ℝ))
    (hX_meas : ∀ i t, t < T →
      StronglyMeasurable[ℱ (t + 2)] (observation X i t))
    (hquota : ∀ i t, t < T → ∀ ω, i ∈ P t ω → N P X i t ω < q)
    (hservice : ∀ i t, t < T → ∀ᵐ ω ∂μ, i ∈ P t ω →
      a * w t ω ≤ μ[observation X i t | ℱ (t + 1)] ω) :
    μ[totalCharge P sigma theta w T | phaseStartSigmaAlgebra ℱ sigma hsigma]
      ≤ᵐ[μ] fun _ =>
        ((q : ℝ) + Real.log (d : ℝ)) / (kappa * a) := by
  let mσ := phaseStartSigmaAlgebra ℱ sigma hsigma
  have hmσ : mσ ≤ m := phaseStartSigmaAlgebra_le ℱ sigma hsigma
  have htotalInt := totalCharge_exp_integrable μ ℱ P sigma theta w a ha
    hsigma htheta hP hw_meas hphase hw_bound
  have hset : ∀ B, MeasurableSet[mσ] B →
      ∫ ω in B, totalCharge P sigma theta w T ω ∂μ ≤
        (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) * μ.real B := by
    intro B hB
    exact phase_start_totalCharge_setIntegral_bound μ hd _hT _hK _hq
      ℱ P X w sigma theta a ha hsigma htheta _hsigma_start
      _hsigma_le_theta _htheta_bound hP hphase hnested hw_meas hw_bound
      hX_meas hquota hservice B hB
  exact (setIntegral_iff_condExp_le μ mσ hmσ
    (totalCharge P sigma theta w T)
    (((q : ℝ) + Real.log (d : ℝ)) / (kappa * a)) htotalInt.1).mp hset

end Bandits.Support.PhaseStartConditionalWaiting
