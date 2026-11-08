/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalLaterReleasePredictableService
public import Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseSignedCost

import Mathlib.Tactic

/-!
# Conditional signed cost of an original later-installation release phase

The fixed installation label is retained throughout the conditional
expectation. The phase is stopped at the original release endpoints.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseServiceWaiting
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase
open Bandits.Support.ReferenceOriginalLaterReleasePredictableService
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalInstallationReleaseWaitingCost

variable {p : ConstructorDimensions.Parameters}

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev RateInput (p : ConstructorDimensions.Parameters) :=
  ReferenceActivePhysicalStep.RateInput p
abbrev GridRewardTable (p : ConstructorDimensions.Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual DATA release weight charged while this fixed follower is
pending in the later-installation analysis. -/
public def followerCharge (i : Fin (p.m - 1)) (s : ℕ) (z : Source p) : ℝ :=
  ∑ t : Fin p.T,
    if i ∈ Plate rate rewards C_star C_h s t.val z then
      c_i rate rewards C_star C_h i s t.val z else 0

/-- The auxiliary-arm collision weight charged on rounds with an actually
pending later follower. -/
public def auxiliaryCharge (s : ℕ) (z : Source p) : ℝ :=
  ∑ t : Fin p.T,
    (if (Plate rate rewards C_star C_h s t.val z).Nonempty then (1 : ℝ) else 0) *
      omega rate rewards C_star C_h s t.val z

/-- The original signed release deficit, masked only by the fixed-label later
analysis support. -/
public def laterSignedCharge (s : ℕ) (z : Source p) : ℝ :=
  ∑ t : Fin p.T, Dlate rate rewards C_star C_h s t.val z

private def followerSingletonPending (i : Fin (p.m - 1)) (s : ℕ) :
    ℕ → Source p → Finset (Fin 1) :=
  fun k z => if i ∈ Plate rate rewards C_star C_h s k z then {0} else ∅

private def followerSingletonObservation (i : Fin (p.m - 1)) :
    Fin 1 → ℕ → Source p → Bool :=
  fun _ k z => dataObservation rate rewards C_star C_h i k z

private theorem followerSingleton_mem_iff (i : Fin (p.m - 1)) (s k : ℕ)
    (z : Source p) :
    (0 : Fin 1) ∈ followerSingletonPending rate rewards C_star C_h i s k z ↔
      i ∈ Plate rate rewards C_star C_h s k z := by
  by_cases h : i ∈ Plate rate rewards C_star C_h s k z <;>
    simp [followerSingletonPending, h]

private theorem followerSingleton_count_eq (i : Fin (p.m - 1)) (s v : ℕ)
    (z : Source p) :
    PhaseServiceWaiting.N (followerSingletonPending rate rewards C_star C_h i s)
        (followerSingletonObservation rate rewards C_star C_h i) 0 v z =
      PhaseServiceWaiting.N (Plate rate rewards C_star C_h s)
        (fun j k z => dataObservation rate rewards C_star C_h j k z) i v z := by
  unfold PhaseServiceWaiting.N
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : i ∈ Plate rate rewards C_star C_h s k z
  · simp [followerSingletonPending, followerSingletonObservation, h]
  · simp [followerSingletonPending, followerSingletonObservation, h]

private theorem followerCharge_eq_singleton_G (i : Fin (p.m - 1)) (s : ℕ)
    (z : Source p) :
    followerCharge rate rewards C_star C_h i s z =
      G (followerSingletonPending rate rewards C_star C_h i s)
        (fun k z => c_i rate rewards C_star C_h i s k z) 0 p.T z := by
  unfold followerCharge G
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : i ∈ Plate rate rewards C_star C_h s t.val z
  · simp [PhaseServiceWaiting.J, followerSingletonPending, h]
  · simp [PhaseServiceWaiting.J, followerSingletonPending, h]

private theorem auxiliaryCharge_eq_totalCharge (_control0 : TimeControl p)
    (s : ℕ) (z : Source p) :
    auxiliaryCharge rate rewards C_star C_h s z =
      totalCharge (Plate rate rewards C_star C_h s)
        (sigmaR rate rewards C_star C_h s) (thetaR rate rewards C_star C_h s)
        (fun k z => omega rate rewards C_star C_h s k z) p.T z := by
  unfold auxiliaryCharge PhaseServiceWaiting.totalCharge
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hne : (Plate rate rewards C_star C_h s t.val z).Nonempty
  · have hphase :
        sigmaR rate rewards C_star C_h s z ≤ t.val + 1 ∧
          t.val + 1 < thetaR rate rewards C_star C_h s z := by
      by_contra h
      have hempty := Plate_empty_outside_interval rate rewards C_star C_h s t.val z h
      simp [hempty] at hne
    simp [PhaseServiceWaiting.A, hne, hphase.1, hphase.2]
  · simp [PhaseServiceWaiting.A, hne]

private theorem laterSignedCharge_integrable (control0 : TimeControl p) (s : ℕ) :
    Integrable (laterSignedCharge rate rewards C_star C_h s) (sourceInputLaw p) := by
  unfold laterSignedCharge
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact Dlate_integrable_nat rate rewards C_star C_h control0 s t.val

private theorem roundEnvelope_integrable (control0 : TimeControl p) (s k : ℕ)
    (_hk : k < p.T) :
    Integrable
      (fun z : Source p =>
        (∑ i ∈ Plate rate rewards C_star C_h s k z,
          c_i rate rewards C_star C_h i s k z) +
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z)
      (sourceInputLaw p) := by
  let F := sourcePrefixFiltration control0
  let f : Finset (Fin (p.m - 1)) → Source p → ℝ := fun A z =>
    ∑ i ∈ A, c_i rate rewards C_star C_h i s k z
  have hci : ∀ i, StronglyMeasurable[F (k + 1)]
      (c_i rate rewards C_star C_h i s k) := by
    intro i
    exact (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
      control0 i s k).fst
  have hPlate : ∀ i, MeasurableSet[F (k + 1)]
      {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
    intro i
    exact Plate_mem_preRound_measurable_nat rate rewards C_star C_h control0 s k i
  have hRoundData : Integrable (fun z => f (Plate rate rewards C_star C_h s k z) z)
      (sourceInputLaw p) := by
    have hsumMeas : StronglyMeasurable[F (k + 1)]
        (fun z : Source p =>
          ∑ i : Fin (p.m - 1),
            if i ∈ Plate rate rewards C_star C_h s k z then
              c_i rate rewards C_star C_h i s k z else 0) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro i hi
      exact StronglyMeasurable.ite (hPlate i) (hci i) stronglyMeasurable_const
    have hsumMeas' := hsumMeas.mono (F.le (k + 1))
    have hsumEq : (fun z => f (Plate rate rewards C_star C_h s k z) z) = fun z =>
        ∑ i : Fin (p.m - 1),
          if i ∈ Plate rate rewards C_star C_h s k z then
            c_i rate rewards C_star C_h i s k z else 0 := by
      funext z
      have hfilter : Plate rate rewards C_star C_h s k z =
          Finset.univ.filter (fun i : Fin (p.m - 1) =>
            i ∈ Plate rate rewards C_star C_h s k z) := by
        ext i
        simp
      change (∑ i ∈ Plate rate rewards C_star C_h s k z,
          c_i rate rewards C_star C_h i s k z) = _
      rw [hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      simp
    rw [hsumEq]
    apply Integrable.of_mem_Icc (μ := sourceInputLaw p) 0 (p.m - 1 : ℝ)
      (hsumMeas'.aemeasurable (μ := sourceInputLaw p))
    refine ae_of_all _ fun z => ?_
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs with h
      · exact (c_i_bounds rate rewards C_star C_h control0 i s k z).1
      · simp
    · calc
        (∑ i : Fin (p.m - 1),
            if i ∈ Plate rate rewards C_star C_h s k z then
              c_i rate rewards C_star C_h i s k z else 0) ≤
            ∑ _i : Fin (p.m - 1), (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i hi
              split_ifs with h
              · exact (c_i_bounds rate rewards C_star C_h control0 i s k z).2
              · norm_num
        _ = ((p.m - 1 : ℕ) : ℝ) := by simp
        _ ≤ (p.m : ℝ) - 1 := by
          rw [Nat.cast_sub (by have hm := p.two_le_m; omega)]
          norm_num
  have homega : StronglyMeasurable[F (k + 1)]
      (omega rate rewards C_star C_h s k) :=
    (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
      control0 ⟨0, by have hm := p.two_le_m; omega⟩ s k).snd
  have hnonempty : MeasurableSet[F (k + 1)]
      {z : Source p | (Plate rate rewards C_star C_h s k z).Nonempty} := by
    have heq : {z : Source p | (Plate rate rewards C_star C_h s k z).Nonempty} =
        ⋃ i : Fin (p.m - 1),
          {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.Nonempty]
    rw [heq]
    exact MeasurableSet.iUnion hPlate
  have hroundAuxSM : StronglyMeasurable[F (k + 1)]
      (fun z : Source p =>
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z) := by
    have hzero : StronglyMeasurable[F (k + 1)] (fun _ : Source p => (0 : ℝ)) :=
      stronglyMeasurable_const
    have hone : StronglyMeasurable[F (k + 1)] (fun _ : Source p => (1 : ℝ)) :=
      stronglyMeasurable_const
    exact (StronglyMeasurable.ite hnonempty hone hzero).mul homega
  have hroundAuxSM' := hroundAuxSM.mono (F.le (k + 1))
  have hroundAux : Integrable
      (fun z : Source p =>
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z) (sourceInputLaw p) := by
    apply Integrable.of_mem_Icc (μ := sourceInputLaw p) 0 1
      (hroundAuxSM'.aemeasurable (μ := sourceInputLaw p))
    refine ae_of_all _ fun z => ?_
    by_cases hpending : (Plate rate rewards C_star C_h s k z).Nonempty
    · simpa [hpending] using omega_bounds rate rewards C_star C_h control0 s k z
    · simp [hpending]
  have hdata : Integrable (fun z => f (Plate rate rewards C_star C_h s k z) z)
      (sourceInputLaw p) := hRoundData
  have hdata' : Integrable
      (fun z =>
        (∑ i ∈ Plate rate rewards C_star C_h s k z,
          c_i rate rewards C_star C_h i s k z)) (sourceInputLaw p) := by
    simpa [f] using hdata
  exact hdata'.add hroundAux


private theorem followerCharge_setIntegral_bound (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (s : ℕ) (B : Set (Source p))
    (hB : MeasurableSet[
      phaseStartSigmaAlgebra (sourcePrefixFiltration control0)
        (sigmaR rate rewards C_star C_h s)
        (sigmaR_stopping rate rewards C_star C_h control0 s)] B) :
    ∫ z in B, followerCharge rate rewards C_star C_h i s z ∂sourceInputLaw p ≤
      (2 * (p.K : ℝ)) * (sourceInputLaw p).real B := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let sigma : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    sigmaR rate rewards C_star C_h s
  let theta : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    thetaR rate rewards C_star C_h s
  let P : ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin 1) :=
    followerSingletonPending rate rewards C_star C_h i s
  let X : Fin 1 → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool :=
    followerSingletonObservation rate rewards C_star C_h i
  let w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    fun k z => c_i rate rewards C_star C_h i s k z
  let aData : ℝ := 1 / (2 * (p.K : ℝ))
  have hdim : 0 < 1 := by norm_num
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < 1 := by norm_num
  have hq : 0 < 1 := by norm_num
  have hKreal : 0 < (p.K : ℝ) := by exact_mod_cast ConstructorDimensions.K_pos p
  have ha : 0 < aData := by dsimp [aData]; positivity
  have hsigma := sigmaR_stopping rate rewards C_star C_h control0 s
  have htheta := thetaR_stopping rate rewards C_star C_h control0 s
  have hP : ∀ j k, k < p.T →
      MeasurableSet[F (k + 1)] {z : Source p | j ∈ P k z} := by
    intro j k hk
    have hj : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have heq : {z : Source p | (0 : Fin 1) ∈ P k z} =
        {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
      ext z
      exact followerSingleton_mem_iff rate rewards C_star C_h i s k z
    rw [heq]
    exact Plate_mem_preRound_measurable_nat rate rewards C_star C_h control0 s k i
  have hphase : ∀ k, k < p.T → ∀ z,
      (P k z).Nonempty → sigma z ≤ k + 1 ∧ k + 1 < theta z := by
    intro k hk z hne
    have hmem : i ∈ Plate rate rewards C_star C_h s k z := by
      by_contra hnot
      have hempty : P k z = ∅ := by simp [P, followerSingletonPending, hnot]
      simp [P, hempty] at hne
    have hpending : (Plate rate rewards C_star C_h s k z).Nonempty := ⟨i, hmem⟩
    by_contra h
    have hout : ¬ (sigmaR rate rewards C_star C_h s z ≤ k + 1 ∧
        k + 1 < thetaR rate rewards C_star C_h s z) := h
    have hempty := Plate_empty_outside_interval rate rewards C_star C_h s k z hout
    simp [hempty] at hpending
  have hnested : ∀ j k, j ≤ k → k < p.T → ∀ z,
      sigma z ≤ j + 1 → k + 1 < theta z → P k z ⊆ P j z := by
    intro j k hjk hk z hstart hexit q hqmem
    have hq0 : q = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst q
    have hmem := (followerSingleton_mem_iff rate rewards C_star C_h i s k z).mp hqmem
    have hsub := Plate_nested_inside_interval rate rewards C_star C_h s z j k hjk
      hstart hexit
    exact (followerSingleton_mem_iff rate rewards C_star C_h i s j z).mpr (hsub hmem)
  have hw_meas : ∀ k, k < p.T → StronglyMeasurable[F (k + 1)] (w k) := by
    intro k hk
    exact (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
      control0 i s k).fst
  have hw_bound : ∀ k, k < p.T → ∀ z, w k z ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
    intro k hk z
    simpa using c_i_bounds rate rewards C_star C_h control0 i s k z
  have hX_meas : ∀ j k, k < p.T →
      StronglyMeasurable[F (k + 2)] (observation X j k) := by
    intro j k hk
    have hj : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    let t : Fin p.T := ⟨k, hk⟩
    have hflags := flags_stronglyMeasurable rate rewards C_star C_h control0 i t
    have hobs : observation X 0 k = fun z =>
        if actualData rate rewards C_star C_h i t z then (1 : ℝ) else 0 := by
      funext z
      simp [PhaseServiceWaiting.observation, X, followerSingletonObservation,
        dataObservation, t, hk]
    rw [hobs]
    exact hflags.2.1
  have hquota : ∀ j k, k < p.T → ∀ z, j ∈ P k z →
      PhaseServiceWaiting.N P X j k z < 1 := by
    intro j k hk z hj
    have hj0 : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have hmem := (followerSingleton_mem_iff rate rewards C_star C_h i s k z).mp hj
    have hprior := Plate_strict_prior_N_lt_one rate rewards C_star C_h s z k i hmem
    calc
      PhaseServiceWaiting.N P X 0 k z =
          PhaseServiceWaiting.N (Plate rate rewards C_star C_h s)
            (fun q n z => dataObservation rate rewards C_star C_h q n z) i k z :=
        followerSingleton_count_eq rate rewards C_star C_h i s k z
      _ < 1 := hprior.2
  have hservice : ∀ j k, k < p.T → ∀ᵐ z ∂μ,
      j ∈ P k z → aData * w k z ≤ μ[observation X j k | F (k + 1)] z := by
    intro j k hk
    let t : Fin p.T := ⟨k, hk⟩
    have hserviceAll := actual_service_condExp_all rate rewards C_star C_h control0
    filter_upwards [hserviceAll] with z hz
    intro hj
    have hj0 : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have hmem := (followerSingleton_mem_iff rate rewards C_star C_h i s k z).mp hj
    have hmean := (hz s t i hmem).1
    have hscale : aData * w k z =
        c_i rate rewards C_star C_h i s k z / (2 * (p.K : ℝ)) := by
      dsimp [aData, w]
      rw [div_eq_mul_inv]
      ring
    rw [hscale]
    have hobs : observation X 0 k = fun y =>
        if actualData rate rewards C_star C_h i t y then (1 : ℝ) else 0 := by
      funext y
      simp [PhaseServiceWaiting.observation, X, followerSingletonObservation,
        dataObservation, t, hk]
    have hmean' := hmean
    rw [← hobs] at hmean'
    rw [← hmean']
  have hends : (∀ z, 1 ≤ sigma z) ∧ (∀ z, sigma z ≤ theta z) ∧
      (∀ z, theta z ≤ p.T + 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro z
    · exact (sigmaR_bounds rate rewards C_star C_h s z).1
    · exact (sigmaR_bounds rate rewards C_star C_h s z).2.1
    · exact (sigmaR_bounds rate rewards C_star C_h s z).2.2
  have hwaiting := phase_start_task_charge_setIntegral_bound μ hdim hT hK hq
    F P X w sigma theta aData ha hsigma htheta hends.1 hends.2.1 hends.2.2
    hP hphase hnested hw_meas
      (by intro k hk z; simpa using hw_bound k hk z)
      hX_meas hquota hservice B hB 0
  have hconstant : (1 : ℝ) / aData = 2 * (p.K : ℝ) := by
    dsimp [aData]
    field_simp [ne_of_gt hKreal]
  have hfunc : (fun z : Source p => followerCharge rate rewards C_star C_h i s z) =
      fun z => G P w 0 p.T z := by
    funext z
    exact followerCharge_eq_singleton_G rate rewards C_star C_h i s z
  have hbound : ∫ z in B, (fun z : Source p => G P w 0 p.T z) z ∂μ ≤
      ((1 : ℝ) / aData) * μ.real B := by
    simpa [hq] using hwaiting
  rw [hfunc]
  simpa only [hconstant] using hbound


private theorem auxiliaryCharge_setIntegral_bound (control0 : TimeControl p)
    (s : ℕ) (B : Set (Source p))
    (hB : MeasurableSet[
      phaseStartSigmaAlgebra (sourcePrefixFiltration control0)
        (sigmaR rate rewards C_star C_h s)
        (sigmaR_stopping rate rewards C_star C_h control0 s)] B) :
    ∫ z in B, auxiliaryCharge rate rewards C_star C_h s z ∂sourceInputLaw p ≤
      (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1)) *
          (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) * (sourceInputLaw p).real B := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let d : ℕ := p.m - 1
  let sigma : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    sigmaR rate rewards C_star C_h s
  let theta : BootstrapPrivateRoundStreams.SourceInput p → ℕ :=
    thetaR rate rewards C_star C_h s
  let P : ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin d) :=
    Plate rate rewards C_star C_h s
  let X : Fin d → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool := fun i k z =>
    upObservation rate rewards C_star C_h i k z
  let w : ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    fun k z => omega rate rewards C_star C_h s k z
  let aUp : ℝ := 1 / (12 * ((p.m : ℝ) - 1) * (p.K : ℝ))
  have hd : 0 < d := by dsimp [d]; have hm := p.two_le_m; omega
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < 1 := by norm_num
  have hq : 0 < 1 := by norm_num
  have hKreal : 0 < (p.K : ℝ) := by exact_mod_cast ConstructorDimensions.K_pos p
  have hmReal : (1 : ℝ) < (p.m : ℝ) := by
    have hm := p.two_le_m
    exact_mod_cast (show 1 < p.m by omega)
  have ha : 0 < aUp := by
    dsimp [aUp]
    positivity
  have hsigma := sigmaR_stopping rate rewards C_star C_h control0 s
  have htheta := thetaR_stopping rate rewards C_star C_h control0 s
  have hP : ∀ i k, k < p.T →
      MeasurableSet[F (k + 1)] {z : Source p | i ∈ P k z} := by
    intro i k hk
    exact Plate_mem_preRound_measurable_nat rate rewards C_star C_h control0 s k i
  have hphase : ∀ k, k < p.T → ∀ z,
      (P k z).Nonempty → sigma z ≤ k + 1 ∧ k + 1 < theta z := by
    intro k hk z hne
    by_contra h
    have hout : ¬ (sigmaR rate rewards C_star C_h s z ≤ k + 1 ∧
        k + 1 < thetaR rate rewards C_star C_h s z) := h
    have hempty := Plate_empty_outside_interval rate rewards C_star C_h s k z hout
    simp [P, hempty] at hne
  have hnested : ∀ j k, j ≤ k → k < p.T → ∀ z,
      sigma z ≤ j + 1 → k + 1 < theta z → P k z ⊆ P j z := by
    intro j k hjk hk z hstart hexit
    exact Plate_nested_inside_interval rate rewards C_star C_h s z j k hjk hstart hexit
  have hw_meas : ∀ k, k < p.T → StronglyMeasurable[F (k + 1)] (w k) := by
    intro k hk
    exact (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
      control0 ⟨0, by have hm := p.two_le_m; omega⟩ s k).snd
  have hw_bound : ∀ k, k < p.T → ∀ z, w k z ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
    intro k hk z
    simpa [w] using omega_bounds rate rewards C_star C_h control0 s k z
  have hX_meas : ∀ i k, k < p.T →
      StronglyMeasurable[F (k + 2)] (observation X i k) := by
    intro i k hk
    let t : Fin p.T := ⟨k, hk⟩
    have hflags := flags_stronglyMeasurable rate rewards C_star C_h control0 i t
    have hobs : observation X i k = fun z =>
        if actualUp rate rewards C_star C_h i t z then (1 : ℝ) else 0 := by
      funext z
      simp [PhaseServiceWaiting.observation, X, upObservation, t, hk]
    rw [hobs]
    exact hflags.1
  have hquota : ∀ i k, k < p.T → ∀ z, i ∈ P k z →
      PhaseServiceWaiting.N P X i k z < 1 := by
    intro i k hk z hi
    exact (Plate_strict_prior_N_lt_one rate rewards C_star C_h s z k i hi).1
  have hservice : ∀ i k, k < p.T → ∀ᵐ z ∂μ,
      i ∈ P k z → aUp * w k z ≤ μ[observation X i k | F (k + 1)] z := by
    intro i k hk
    let t : Fin p.T := ⟨k, hk⟩
    have hserviceAll := actual_service_condExp_all rate rewards C_star C_h control0
    filter_upwards [hserviceAll] with z hz
    intro hi
    have hmean := (hz s t i hi).2
    have hscale : aUp * w k z =
        omega rate rewards C_star C_h s k z /
          (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) := by
      dsimp [aUp, w, d]
      rw [div_eq_mul_inv]
      ring
    have hobs : observation X i k = fun y =>
        if actualUp rate rewards C_star C_h i t y then (1 : ℝ) else 0 := by
      funext y
      simp [PhaseServiceWaiting.observation, X, upObservation, t, hk]
    calc
      aUp * w k z = omega rate rewards C_star C_h s k z /
          (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) := hscale
      _
        ≤ μ[(fun y => if actualUp rate rewards C_star C_h i t y then (1 : ℝ) else 0) |
          F (k + 1)] z := hmean
      _ = μ[observation X i k | F (k + 1)] z := by rw [← hobs]
  have hends : (∀ z, 1 ≤ sigma z) ∧ (∀ z, sigma z ≤ theta z) ∧
      (∀ z, theta z ≤ p.T + 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro z
    · exact (sigmaR_bounds rate rewards C_star C_h s z).1
    · exact (sigmaR_bounds rate rewards C_star C_h s z).2.1
    · exact (sigmaR_bounds rate rewards C_star C_h s z).2.2
  have hwaiting := phase_start_totalCharge_setIntegral_bound μ hd hT hK hq
    F P X w sigma theta aUp ha hsigma htheta hends.1 hends.2.1 hends.2.2
    hP hphase hnested hw_meas
      (by intro k hk z; simpa using hw_bound k hk z)
      hX_meas hquota hservice B hB
  have hauxeq : (fun z : Source p => auxiliaryCharge rate rewards C_star C_h s z) =
      fun z => totalCharge P sigma theta w p.T z := by
    funext z
    exact auxiliaryCharge_eq_totalCharge rate rewards C_star C_h control0 s z
  have hkappa : 0 < 1 - Real.exp (-1) := by
    change 0 < PhaseServiceWaiting.kappa
    exact PhaseServiceWaiting.kappa_pos
  have hdm : (d : ℝ) = (p.m : ℝ) - 1 := by
    dsimp [d]
    rw [Nat.cast_sub (by have hm := p.two_le_m; omega)]
    norm_num
  have hconstant :
      ((1 : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * aUp) =
        (12 * (d : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) * (Real.log (d : ℝ) + 1)) := by
    dsimp [aUp]
    simp only [PhaseServiceWaiting.kappa]
    rw [← hdm]
    have hden : 0 < 12 * (d : ℝ) * (p.K : ℝ) := by positivity
    field_simp [ne_of_gt hkappa, ne_of_gt hden]
    ring
  have hbound :
      ∫ z in B, (fun z : Source p => totalCharge P sigma theta w p.T z) z ∂μ ≤
        (((1 : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * aUp)) * μ.real B := by
    simpa [d] using hwaiting
  rw [hauxeq]
  simpa [d, hconstant] using hbound


private theorem followerRoundCharge_integrable (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (s k : ℕ) (_hk : k < p.T) :
    Integrable
      (fun z : Source p => if i ∈ Plate rate rewards C_star C_h s k z then
        c_i rate rewards C_star C_h i s k z else 0) (sourceInputLaw p) := by
  let F := sourcePrefixFiltration control0
  have hset := Plate_mem_preRound_measurable_nat rate rewards C_star C_h control0 s k i
  have hc := (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
    control0 i s k).fst
  have hc' : StronglyMeasurable[F (k + 1)]
      (c_i rate rewards C_star C_h i s k) := by
    simpa only [Prod.fst] using hc
  have hzero : StronglyMeasurable[F (k + 1)] (fun _ : Source p => (0 : ℝ)) :=
    stronglyMeasurable_const
  have hsm : StronglyMeasurable[sourcePrefixFiltration control0 (k + 1)]
      (fun z : Source p => if i ∈ Plate rate rewards C_star C_h s k z then
        c_i rate rewards C_star C_h i s k z else 0) := by
    exact StronglyMeasurable.ite hset hc' hzero
  have hsmAmbient : StronglyMeasurable
      (fun z : Source p => if i ∈ Plate rate rewards C_star C_h s k z then
        c_i rate rewards C_star C_h i s k z else 0) :=
    hsm.mono (F.le (k + 1))
  apply Integrable.of_mem_Icc (μ := sourceInputLaw p) 0 1
    (hsmAmbient.aemeasurable (μ := sourceInputLaw p))
  refine ae_of_all _ fun z => ?_
  by_cases hi : i ∈ Plate rate rewards C_star C_h s k z
  · simpa [hi] using c_i_bounds rate rewards C_star C_h control0 i s k z
  · simp [hi]

private theorem auxiliaryRoundCharge_integrable (control0 : TimeControl p)
    (s k : ℕ) (_hk : k < p.T) :
    Integrable
      (fun z : Source p =>
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z) (sourceInputLaw p) := by
  let F := sourcePrefixFiltration control0
  have hPlate : ∀ i, MeasurableSet[F (k + 1)]
      {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
    intro i
    exact Plate_mem_preRound_measurable_nat rate rewards C_star C_h control0 s k i
  have hnonempty : MeasurableSet[F (k + 1)]
      {z : Source p | (Plate rate rewards C_star C_h s k z).Nonempty} := by
    have heq : {z : Source p | (Plate rate rewards C_star C_h s k z).Nonempty} =
        ⋃ i : Fin (p.m - 1),
          {z : Source p | i ∈ Plate rate rewards C_star C_h s k z} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.Nonempty]
    rw [heq]
    exact MeasurableSet.iUnion hPlate
  have homega : StronglyMeasurable[F (k + 1)]
      (omega rate rewards C_star C_h s k) :=
    (service_preRound_stronglyMeasurable_nat rate rewards C_star C_h
      control0 ⟨0, by have hm := p.two_le_m; omega⟩ s k).snd
  have hzero : StronglyMeasurable[F (k + 1)] (fun _ : Source p => (0 : ℝ)) :=
    stronglyMeasurable_const
  have hone : StronglyMeasurable[F (k + 1)] (fun _ : Source p => (1 : ℝ)) :=
    stronglyMeasurable_const
  have hsm : StronglyMeasurable[sourcePrefixFiltration control0 (k + 1)]
      (fun z : Source p =>
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z) := by
    exact (StronglyMeasurable.ite hnonempty hone hzero).mul homega
  have hsmAmbient : StronglyMeasurable
      (fun z : Source p =>
        (if (Plate rate rewards C_star C_h s k z).Nonempty then (1 : ℝ) else 0) *
          omega rate rewards C_star C_h s k z) :=
    hsm.mono (F.le (k + 1))
  apply Integrable.of_mem_Icc (μ := sourceInputLaw p) 0 1
    (hsmAmbient.aemeasurable (μ := sourceInputLaw p))
  refine ae_of_all _ fun z => ?_
  by_cases hpending : (Plate rate rewards C_star C_h s k z).Nonempty
  · simpa [hpending] using omega_bounds rate rewards C_star C_h control0 s k z
  · simp [hpending]

/-- Integrability of the three literal finite charges under the original
source-input law. -/
public theorem laterReleaseFiniteCharges_integrable (control0 : TimeControl p)
    (s : ℕ) :
    (∀ i : Fin (p.m - 1),
      Integrable (followerCharge rate rewards C_star C_h i s) (sourceInputLaw p)) ∧
    Integrable (auxiliaryCharge rate rewards C_star C_h s) (sourceInputLaw p) ∧
    Integrable (laterSignedCharge rate rewards C_star C_h s) (sourceInputLaw p) := by
  constructor
  · intro i
    unfold followerCharge
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact followerRoundCharge_integrable rate rewards C_star C_h control0 i s t.val t.isLt
  constructor
  · unfold auxiliaryCharge
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact auxiliaryRoundCharge_integrable rate rewards C_star C_h control0 s t.val t.isLt
  · exact laterSignedCharge_integrable rate rewards C_star C_h control0 s


/-- The literal signed release charge is bounded on every set in the actual
stopped phase-start field. -/
public theorem laterSignedCharge_setIntegral_bound (control0 : TimeControl p)
    (s : ℕ) (B : Set (Source p))
    (hB : MeasurableSet[
      phaseStartSigmaAlgebra (sourcePrefixFiltration control0)
        (sigmaR rate rewards C_star C_h s)
        (sigmaR_stopping rate rewards C_star C_h control0 s)] B) :
    ∫ z in B, laterSignedCharge rate rewards C_star C_h s z ∂sourceInputLaw p ≤
      (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
        12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) *
        (sourceInputLaw p).real B := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let sigma := sigmaR rate rewards C_star C_h s
  let theta := thetaR rate rewards C_star C_h s
  let m0 : MeasurableSpace (Source p) := Prod.instMeasurableSpace
  let mSigma := phaseStartSigmaAlgebra F sigma
    (sigmaR_stopping rate rewards C_star C_h control0 s)
  let R : Fin p.T → Source p → ℝ := fun t z =>
    (∑ i ∈ Plate rate rewards C_star C_h s t.val z,
      c_i rate rewards C_star C_h i s t.val z) +
    (if (Plate rate rewards C_star C_h s t.val z).Nonempty then (1 : ℝ) else 0) *
      omega rate rewards C_star C_h s t.val z
  have hchargeInt := laterReleaseFiniteCharges_integrable rate rewards C_star C_h
    control0 s
  have hmSigma : mSigma ≤ m0 :=
    phaseStartSigmaAlgebra_le (m := m0) F sigma
      (sigmaR_stopping rate rewards C_star C_h control0 s)
  have hBambient : MeasurableSet[m0] B := hmSigma B hB
  have hBstop :=
    (isStoppingTime_of_preRound F sigma
      (sigmaR_stopping rate rewards C_star C_h control0 s)).measurableSet B
  have hBstop := hBstop.mp hB
  have hce := Dlate_condExp_signed_envelope_nat rate rewards C_star C_h control0
  have hroundBound : ∀ t : Fin p.T,
      ∫ z in B, Dlate rate rewards C_star C_h s t.val z ∂μ ≤
        ∫ z in B, R t z ∂μ := by
    intro t
    let E : Set (Source p) := B ∩ {z | sigma z ≤ t.val + 1}
    have hE : MeasurableSet[F (t.val + 1)] E := by
      have hprefix := hBstop.2 (t.val + 1)
      have hset : B ∩
          {z : Source p | (sigma z : WithTop ℕ) ≤ ((t.val + 1 : ℕ) : WithTop ℕ)} = E := by
        ext z
        simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨hBz, htime⟩ <;>
          exact ⟨hBz, by exact_mod_cast htime⟩
      rw [← hset]
      exact hprefix
    have hEambient : MeasurableSet[m0] E :=
      F.le (t.val + 1) E hE
    have hDzero : ∀ z, sigma z > t.val + 1 →
        Dlate rate rewards C_star C_h s t.val z = 0 := by
      intro z hstart
      dsimp [sigma] at hstart
      have hnotSupport : ¬ supportAt rate rewards C_star C_h s t.val z := by
        intro hsupp
        have hinterval :=
          (supportAt_iff_interval rate rewards C_star C_h s t.val z).mp hsupp
        omega
      apply Dlate_eq_zero_of_not_Llate
      intro hlate
      exact hnotSupport hlate.2
    have hnotLlate : ∀ z, sigma z > t.val + 1 →
        ¬ Llate rate rewards C_star C_h s t.val z := by
      intro z hstart hlate
      dsimp [sigma] at hstart
      have hnotSupport : ¬ supportAt rate rewards C_star C_h s t.val z := by
        intro hsupp
        have hinterval :=
          (supportAt_iff_interval rate rewards C_star C_h s t.val z).mp hsupp
        omega
      exact hnotSupport hlate.2
    have hRzero : ∀ z, sigma z > t.val + 1 → R t z = 0 := by
      intro z hstart
      have hnot := hnotLlate z hstart
      have hempty := Plate_eq_empty_of_not_Llate rate rewards C_star C_h s t.val z hnot
      simp [R, hempty]
    have hDloc :
        ∫ z in B, Dlate rate rewards C_star C_h s t.val z ∂μ =
          ∫ z in E, Dlate rate rewards C_star C_h s t.val z ∂μ := by
      rw [← integral_indicator hBambient, ← integral_indicator hEambient]
      apply integral_congr_ae
      apply ae_of_all μ
      intro z
      by_cases hzB : z ∈ B
      · by_cases hzStart : sigma z ≤ t.val + 1
        · simp [E, hzB, hzStart]
        · have hzZero := hDzero z (Nat.not_le.mp hzStart)
          simp [E, hzB, hzStart, hzZero]
      · simp [E, hzB]
    have hRloc : ∫ z in B, R t z ∂μ = ∫ z in E, R t z ∂μ := by
      rw [← integral_indicator hBambient, ← integral_indicator hEambient]
      apply integral_congr_ae
      apply ae_of_all μ
      intro z
      by_cases hzB : z ∈ B
      · by_cases hzStart : sigma z ≤ t.val + 1
        · simp [E, hzB, hzStart]
        · have hzZero := hRzero z (Nat.not_le.mp hzStart)
          simp [E, hzB, hzStart, hzZero]
      · simp [E, hzB]
    have hDint := Dlate_integrable_nat rate rewards C_star C_h control0 s t.val
    have hRint := roundEnvelope_integrable rate rewards C_star C_h control0 s t.val t.isLt
    have hceRound : ∀ᵐ z ∂μ,
        μ[Dlate rate rewards C_star C_h s t.val |
          F (t.val + 1)] z ≤ R t z := by
      filter_upwards [hce] with z hz
      simpa [R] using hz s t.val
    calc
      ∫ z in B, Dlate rate rewards C_star C_h s t.val z ∂μ =
          ∫ z in E, Dlate rate rewards C_star C_h s t.val z ∂μ := hDloc
      _ = ∫ z in E,
          μ[Dlate rate rewards C_star C_h s t.val | F (t.val + 1)] z ∂μ :=
        (setIntegral_condExp (F.le (t.val + 1)) hDint hE).symm
      _ ≤ ∫ z in E, R t z ∂μ :=
        setIntegral_mono_ae integrable_condExp.integrableOn hRint.integrableOn hceRound
      _ = ∫ z in B, R t z ∂μ := hRloc.symm
  have hDsum :
      ∫ z in B, laterSignedCharge rate rewards C_star C_h s z ∂μ =
        ∑ t : Fin p.T,
          ∫ z in B, Dlate rate rewards C_star C_h s t.val z ∂μ := by
    unfold laterSignedCharge
    rw [integral_finsetSum (Finset.univ : Finset (Fin p.T)) (fun t ht =>
      (Dlate_integrable_nat rate rewards C_star C_h control0 s t.val).integrableOn)]
  have hRsum :
      ∫ z in B, (fun z : Source p => ∑ t : Fin p.T, R t z) z ∂μ =
        ∑ t : Fin p.T, ∫ z in B, R t z ∂μ := by
    rw [integral_finsetSum (Finset.univ : Finset (Fin p.T)) (fun t ht =>
      (roundEnvelope_integrable rate rewards C_star C_h control0 s t.val t.isLt).integrableOn)]
  have hEnvInt : Integrable (fun z : Source p => ∑ t : Fin p.T, R t z) μ :=
    integrable_finsetSum (Finset.univ : Finset (Fin p.T)) (fun t ht =>
      roundEnvelope_integrable rate rewards C_star C_h control0 s t.val t.isLt)
  have hsumBound :
      ∫ z in B, laterSignedCharge rate rewards C_star C_h s z ∂μ ≤
        ∫ z in B, (fun z : Source p => ∑ t : Fin p.T, R t z) z ∂μ := by
    rw [hDsum, hRsum]
    exact Finset.sum_le_sum fun t ht => hroundBound t
  have hEnvelopeDecomp :
      (fun z : Source p => ∑ t : Fin p.T, R t z) =
        fun z =>
          (∑ i : Fin (p.m - 1), followerCharge rate rewards C_star C_h i s z) +
            auxiliaryCharge rate rewards C_star C_h s z := by
    funext z
    simp only [R]
    rw [Finset.sum_add_distrib]
    have hdata :
        (∑ t : Fin p.T,
          ∑ i ∈ Plate rate rewards C_star C_h s t.val z,
            c_i rate rewards C_star C_h i s t.val z) =
          ∑ i : Fin (p.m - 1),
            ∑ t : Fin p.T,
              if i ∈ Plate rate rewards C_star C_h s t.val z then
                c_i rate rewards C_star C_h i s t.val z else 0 := by
      calc
        _ = ∑ t : Fin p.T,
            ∑ i : Fin (p.m - 1),
              if i ∈ Plate rate rewards C_star C_h s t.val z then
                c_i rate rewards C_star C_h i s t.val z else 0 := by
              apply Finset.sum_congr rfl
              intro t ht
              have hfilter : Plate rate rewards C_star C_h s t.val z =
                  Finset.univ.filter (fun i : Fin (p.m - 1) =>
                    i ∈ Plate rate rewards C_star C_h s t.val z) := by
                ext i
                simp
              rw [hfilter, Finset.sum_filter]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        _ = _ := Finset.sum_comm
    rw [hdata]
    rfl
  have hFollowSumInt : Integrable
      (fun z : Source p =>
        ∑ i : Fin (p.m - 1), followerCharge rate rewards C_star C_h i s z) μ :=
    integrable_finsetSum (Finset.univ : Finset (Fin (p.m - 1)))
      (fun i hi => hchargeInt.1 i)
  have hsumBound' :
      ∫ z in B,
          (∑ i : Fin (p.m - 1), followerCharge rate rewards C_star C_h i s z) +
            auxiliaryCharge rate rewards C_star C_h s z ∂μ ≤
        (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) * μ.real B := by
    rw [integral_add hFollowSumInt.integrableOn hchargeInt.2.1.integrableOn]
    rw [integral_finsetSum (Finset.univ : Finset (Fin (p.m - 1))) (fun i hi =>
      (hchargeInt.1 i).integrableOn)]
    have hdataBound :
        (∑ i : Fin (p.m - 1),
          ∫ z in B, followerCharge rate rewards C_star C_h i s z ∂μ) ≤
          (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) * μ.real B := by
      calc
        _ ≤ ∑ _i : Fin (p.m - 1),
            (2 * (p.K : ℝ)) * μ.real B :=
          Finset.sum_le_sum fun i hi =>
            followerCharge_setIntegral_bound rate rewards C_star C_h control0 i s B hB
        _ = (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) * μ.real B := by
          simp [Finset.sum_const]
          ring
    have hauxBound := auxiliaryCharge_setIntegral_bound rate rewards C_star C_h control0 s B hB
    calc
      (∑ i : Fin (p.m - 1),
          ∫ z in B, followerCharge rate rewards C_star C_h i s z ∂μ) +
        ∫ z in B, auxiliaryCharge rate rewards C_star C_h s z ∂μ ≤
          (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) * μ.real B +
            (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
              (1 - Real.exp (-1)) *
                (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) * μ.real B :=
        add_le_add hdataBound hauxBound
      _ = _ := by ring
  rw [hEnvelopeDecomp] at hsumBound
  exact hsumBound.trans hsumBound'

/-- Conditional expectation of the original signed later-release deficit at
the existing stopped release field. -/
public theorem laterSignedCharge_condExp_bound (control0 : TimeControl p)
    (s : ℕ) :
    (sourceInputLaw p)[laterSignedCharge rate rewards C_star C_h s |
      phaseStartSigmaAlgebra
        (sourcePrefixFiltration control0)
        (sigmaR rate rewards C_star C_h s)
        (sigmaR_stopping rate rewards C_star C_h control0 s)] ≤ᵐ[
          sourceInputLaw p]
      fun _ =>
        2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0
  let sigma := sigmaR rate rewards C_star C_h s
  let mSigma := phaseStartSigmaAlgebra F sigma
    (sigmaR_stopping rate rewards C_star C_h control0 s)
  let m0 : MeasurableSpace (Source p) := Prod.instMeasurableSpace
  have hmSigma : mSigma ≤ m0 :=
    phaseStartSigmaAlgebra_le (m := m0) F sigma
      (sigmaR_stopping rate rewards C_star C_h control0 s)
  have hint :=
    (laterReleaseFiniteCharges_integrable rate rewards C_star C_h control0 s).2.2
  have hset : ∀ B, MeasurableSet[mSigma] B →
      ∫ z in B, laterSignedCharge rate rewards C_star C_h s z ∂μ ≤
        (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
          12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
            (1 - Real.exp (-1)) *
              (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) * μ.real B := by
    intro B hB
    exact laterSignedCharge_setIntegral_bound rate rewards C_star C_h control0 s B hB
  exact (setIntegral_iff_condExp_le (m := m0) μ mSigma hmSigma
    (laterSignedCharge rate rewards C_star C_h s)
    (2 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) +
      12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1)) *
          (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) hint).mp hset

/-- At an actual later installation, the fixed-label analysis support and
charge specialize pointwise to the original stopped release interval. -/
public theorem laterSignedCharge_actualLater_specialization
    (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
    (∀ k : ℕ,
      Llate rate rewards C_star C_h s k z ↔ supportAt rate rewards C_star C_h s k z) ∧
    (∀ k : ℕ,
      Plate rate rewards C_star C_h s k z = pendingAt rate rewards C_star C_h s k z) ∧
    laterSignedCharge rate rewards C_star C_h s z =
      ∑ t : Fin p.T,
        if supportAt rate rewards C_star C_h s t.val z then
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h s t z else 0 := by
  dsimp
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
  have hprojection := projections_at_actualLater rate rewards C_star C_h z b hb
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (hprojection k).1
  · intro k
    exact (hprojection k).2
  · unfold laterSignedCharge
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hsupp : supportAt rate rewards C_star C_h s t.val z
    · have hlate : Llate rate rewards C_star C_h s t.val z :=
        (hprojection t.val).1.mpr hsupp
      rw [Dlate_eq_signed_of_Llate rate rewards C_star C_h s t.val z hlate t.isLt]
      simp [s, hsupp]
    · have hnotLate : ¬ Llate rate rewards C_star C_h s t.val z :=
        fun hlate => hsupp hlate.2
      rw [Dlate_eq_zero_of_not_Llate rate rewards C_star C_h s t.val z hnotLate]
      simp [s, hsupp]

end Bandits.Support.ReferenceOriginalInstallationReleaseWaitingCost

end
