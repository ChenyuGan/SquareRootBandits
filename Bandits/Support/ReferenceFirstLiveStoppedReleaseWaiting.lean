/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseService
public import Bandits.Support.PhaseStartConditionalWaiting

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual first-release waiting charges

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240,293-345`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`, and
`sources/zip4/manuscript/06_interruptions.tex:425-426`.

These internal estimates apply the phase-start waiting theorem to the actual
first-release pending process and its whole-source service readouts. They
bound waiting charges only; they do not assemble signed release costs or close
a manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveStoppedReleaseWaiting

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

abbrev Source (p₀ : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p₀

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "P" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h
local notation "Xdata" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData rate rewards C_star C_h
local notation "Xup" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp rate rewards C_star C_h
local notation "Hfield" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "sigma" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
    rate rewards C_star C_h
local notation "theta" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
    rate rewards C_star C_h
local notation "chi" =>
  ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAssignedChi
    rate rewards C_star C_h control0
local notation "omega" =>
  ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAuxiliaryWeight
    rate rewards C_star C_h control0

/-- The singleton task family used to apply the task estimate to one actual
DATA follower while retaining the original pending gate. -/
def dataSingletonPending (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) :
    Finset (Fin 1) :=
  if i ∈ P k z then {0} else ∅

/-- The singleton family's observation is the original ungated DATA flag. -/
def dataSingletonObservation (i : Fin (p.m - 1)) (_j : Fin 1)
    (k : ℕ) (z : Source p) : Bool := Xdata i k z

theorem dataSingletonPending_zero_mem_iff (i : Fin (p.m - 1)) (k : ℕ)
    (z : Source p) :
    (0 : Fin 1) ∈ dataSingletonPending rate rewards C_star C_h i k z ↔
      i ∈ P k z := by
  by_cases hpending : i ∈ P k z <;> simp [dataSingletonPending, hpending]

/-- The actual source DATA count is unchanged by the singleton reindexing. -/
theorem dataSingleton_count_eq (i : Fin (p.m - 1)) (v : ℕ) (z : Source p) :
    PhaseServiceWaiting.N
        (dataSingletonPending rate rewards C_star C_h i)
        (dataSingletonObservation rate rewards C_star C_h i) 0 v z =
      PhaseServiceWaiting.N P Xdata i v z := by
  unfold PhaseServiceWaiting.N
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpending : i ∈ P k z
  · simp [dataSingletonPending, dataSingletonObservation, hpending]
  · simp [dataSingletonPending, dataSingletonObservation, hpending]

/-- The singleton source DATA charge equals the literal charge of this
follower under the original pending process. -/
theorem dataSingleton_charge_eq (i : Fin (p.m - 1)) (v : ℕ) (z : Source p) :
    PhaseServiceWaiting.G
        (dataSingletonPending rate rewards C_star C_h i)
        (fun k z => chi i k z) 0 v z =
      PhaseServiceWaiting.G P (fun k z => chi i k z) i v z := by
  unfold PhaseServiceWaiting.G
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpending : i ∈ P k z
  · simp [PhaseServiceWaiting.J, dataSingletonPending, hpending]
  · simp [PhaseServiceWaiting.J, dataSingletonPending, hpending]

private theorem pending_measurable (i : Fin (p.m - 1)) (k : ℕ)
    (hk : k < p.T) :
    MeasurableSet[Hfield (k + 1)] {z : Source p | i ∈ P k z} := by
  have hset :
      {z : Source p | i ∈ P k z} =
        {z : Source p | i ∈
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
            rate rewards C_star C_h z ⟨k, hk⟩} := by
    ext z
    have hfin : P k z =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rate rewards C_star C_h z ⟨k, hk⟩ :=
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
        rate rewards C_star C_h ⟨k, hk⟩ z
    change i ∈ P k z ↔ i ∈
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
        rate rewards C_star C_h z ⟨k, hk⟩
    rw [hfin]
  rw [hset]
  exact ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_pending_adapted
    rate rewards C_star C_h control0 ⟨k, hk⟩ i

private theorem pending_in_interval (k : ℕ) (z : Source p)
    (hpending : (P k z).Nonempty) :
    sigma z ≤ k + 1 ∧ k + 1 < theta z := by
  constructor
  · by_contra hstart
    have hout : ¬ (sigma z ≤ k + 1 ∧ k + 1 < theta z) := by
      rintro ⟨hstart', _⟩
      exact hstart hstart'
    have hempty :=
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_empty_outside_interval
        rate rewards C_star C_h z k hout
    simp [hempty] at hpending
  · by_contra hexit
    have hout : ¬ (sigma z ≤ k + 1 ∧ k + 1 < theta z) := by
      rintro ⟨_, hexit'⟩
      exact hexit hexit'
    have hempty :=
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_empty_outside_interval
        rate rewards C_star C_h z k hout
    simp [hempty] at hpending

private theorem pending_nested (s t : ℕ) (hst : s ≤ t) (_ht : t < p.T)
    (z : Source p) (hstart : sigma z ≤ s + 1)
    (hexit : t + 1 < theta z) : P t z ⊆ P s z :=
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_nested_inside_interval
    rate rewards C_star C_h z s t hst hstart hexit

/-- The natural-calendar total waiting charge is exactly the sum over actual
pre-choice pending support; the interval indicator contributes no extra
charge because pending is empty outside the actual stopped interval. -/
theorem totalCharge_eq_pending_sum (z : Source p) :
    PhaseServiceWaiting.totalCharge P sigma theta (fun k z => omega k z) p.T z =
      ∑ k ∈ Finset.range p.T,
        if (P k z).Nonempty then omega k z else 0 := by
  unfold PhaseServiceWaiting.totalCharge
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpending : (P k z).Nonempty
  · have hphase := pending_in_interval rate rewards C_star C_h k z hpending
    simp [PhaseServiceWaiting.A, hpending, hphase.1, hphase.2]
  · simp [PhaseServiceWaiting.A, hpending]

/-- The same charge, written over the actual finite `Fin T` calendar and
endpoint pending set. -/
theorem totalCharge_eq_actual_fin_sum (z : Source p) :
    PhaseServiceWaiting.totalCharge P sigma theta (fun k z => omega k z) p.T z =
      ∑ t : Fin p.T,
        if (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rate rewards C_star C_h z t).Nonempty then
          ReferenceFirstLiveSourceStoppedReleaseService.o
            rate rewards C_star C_h control0 t z
        else 0 := by
  rw [totalCharge_eq_pending_sum rate rewards C_star C_h control0 z]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
        rate rewards C_star C_h t z,
      ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_fin
        rate rewards C_star C_h control0 t z]

/-- The natural-calendar DATA charge is the literal sum over actual pending
follower dates. -/
theorem dataCharge_eq_pending_sum (i : Fin (p.m - 1)) (z : Source p) :
    PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z =
      ∑ k ∈ Finset.range p.T,
        if i ∈ P k z then chi i k z else 0 := by
  unfold PhaseServiceWaiting.G
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpending : i ∈ P k z
  · simp [PhaseServiceWaiting.J, hpending]
  · simp [PhaseServiceWaiting.J, hpending]

/-- The DATA sum also has its exact finite-calendar form, with E's actual
pre-choice pending set and the service module's finite readout. -/
theorem dataCharge_eq_actual_fin_sum (i : Fin (p.m - 1)) (z : Source p) :
    PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z =
      ∑ t : Fin p.T,
        if i ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rate rewards C_star C_h z t then
          ReferenceFirstLiveSourceStoppedReleaseService.c
            rate rewards C_star C_h control0 i t z
        else 0 := by
  rw [dataCharge_eq_pending_sum rate rewards C_star C_h control0 i z]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
        rate rewards C_star C_h t z,
      ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_fin
        rate rewards C_star C_h control0 i t z]

private theorem waiting_endpoint_bounds :
    (∀ z : Source p, 1 ≤ sigma z) ∧
    (∀ z : Source p, sigma z ≤ theta z) ∧
    (∀ z : Source p, theta z ≤ p.T + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    exact (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
      rate rewards C_star C_h z).2.1
  · intro z
    exact (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
      rate rewards C_star C_h z).2.2.1
  · intro z
    exact (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
      rate rewards C_star C_h z).2.2.2

private theorem waiting_stopping_times :
    PhaseServiceWaiting.IsPreRoundStoppingTime Hfield sigma ∧
    PhaseServiceWaiting.IsPreRoundStoppingTime Hfield theta := by
  exact ⟨
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0,
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_theta_stopping
      rate rewards C_star C_h control0⟩

/-- Every fixed follower's actual DATA waiting charge has the phase-start
conditional bound under the original source law and source-prefix field. -/
theorem data_charge_condExp_bound (i : Fin (p.m - 1)) :
    μ[(fun z : Source p =>
        PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z) |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
        (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
          rate rewards C_star C_h control0)] ≤ᵐ[μ]
      fun _ => 2 * (p.K : ℝ) := by
  let Fσ := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0)
  let d : ℕ := 1
  let aData : ℝ := 1 / (2 * (p.K : ℝ))
  have hdim : 0 < d := by simp [d]
  have hT : 0 < p.T := lt_of_lt_of_le Nat.zero_lt_one p.one_le_T
  have hK : 0 < (1 : ℕ) := by norm_num
  have hq : 0 < (1 : ℕ) := by norm_num
  have hKreal : 0 < (p.K : ℝ) := by
    exact_mod_cast ConstructorDimensions.K_pos p
  have ha : 0 < aData := by
    dsimp [aData]
    positivity
  have hbounds := waiting_endpoint_bounds rate rewards C_star C_h
  have hP : ∀ j k, k < p.T →
      MeasurableSet[Hfield (k + 1)]
        {z : Source p | j ∈ dataSingletonPending rate rewards C_star C_h i k z} := by
    intro j k hk
    have hj : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have hset :
        {z : Source p | (0 : Fin 1) ∈
          dataSingletonPending rate rewards C_star C_h i k z} =
          {z : Source p | i ∈ P k z} := by
      ext z
      exact dataSingletonPending_zero_mem_iff rate rewards C_star C_h i k z
    rw [hset]
    exact pending_measurable rate rewards C_star C_h control0 i k hk
  have hphase : ∀ k, k < p.T → ∀ z,
      (dataSingletonPending rate rewards C_star C_h i k z).Nonempty →
        sigma z ≤ k + 1 ∧ k + 1 < theta z := by
    intro k _hk z hne
    have hpending : (P k z).Nonempty := by
      by_contra hnot
      have hno : ¬ i ∈ P k z := by
        intro hmem
        exact hnot ⟨i, hmem⟩
      have hempty : dataSingletonPending rate rewards C_star C_h i k z = ∅ := by
        simp [dataSingletonPending, hno]
      simp [hempty] at hne
    exact pending_in_interval rate rewards C_star C_h k z hpending
  have hnested : ∀ s k, s ≤ k → k < p.T → ∀ z,
      sigma z ≤ s + 1 → k + 1 < theta z →
        dataSingletonPending rate rewards C_star C_h i k z ⊆
          dataSingletonPending rate rewards C_star C_h i s z := by
    intro s k hsk hk z hstart hexit
    have hsubset := pending_nested rate rewards C_star C_h s k hsk hk z hstart hexit
    intro j hj
    have hj0 : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have hpending :=
      (dataSingletonPending_zero_mem_iff rate rewards C_star C_h i k z).mp hj
    have hprior := hsubset hpending
    exact (dataSingletonPending_zero_mem_iff rate rewards C_star C_h i s z).mpr hprior
  have hw_meas : ∀ k, k < p.T →
      StronglyMeasurable[Hfield (k + 1)] (fun z : Source p => chi i k z) := by
    intro k hk
    exact ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_predictable
      rate rewards C_star C_h control0 i k hk
  have hw_bound : ∀ k, k < p.T →
      ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      chi i k z ∈ Set.Icc (0 : ℝ) ((1 : ℕ) : ℝ) := by
    intro k _hk z
    simpa using ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_bounds
      rate rewards C_star C_h control0 i k z
  have hX_meas : ∀ j k, k < p.T →
      StronglyMeasurable[Hfield (k + 2)]
        (PhaseServiceWaiting.observation
          (dataSingletonObservation rate rewards C_star C_h i) j k) := by
    intro j k hk
    change StronglyMeasurable[Hfield (k + 2)]
      (PhaseServiceWaiting.observation Xdata i k)
    exact ReferenceFirstLiveSourceStoppedReleaseService.data_observation_predictable
      rate rewards C_star C_h control0 i k hk
  have hquota : ∀ j k, k < p.T → ∀ z,
      j ∈ dataSingletonPending rate rewards C_star C_h i k z →
        PhaseServiceWaiting.N
          (dataSingletonPending rate rewards C_star C_h i)
          (dataSingletonObservation rate rewards C_star C_h i) j k z < 1 := by
    intro j k _hk z hj
    have hj0 : j = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst j
    have hpending :=
      (dataSingletonPending_zero_mem_iff rate rewards C_star C_h i k z).mp hj
    have hzero :=
      (ReferenceFirstLiveSourceStoppedReleaseQuota.actual_first_release_strict_prior_zero_at_pending
        rate rewards C_star C_h z k i hpending).2.1
    calc
      PhaseServiceWaiting.N
          (dataSingletonPending rate rewards C_star C_h i)
          (dataSingletonObservation rate rewards C_star C_h i) 0 k z =
        PhaseServiceWaiting.N P Xdata i k z :=
          dataSingleton_count_eq rate rewards C_star C_h i k z
      _ = 0 := hzero
      _ < 1 := by norm_num
  have hservice : ∀ j k, k < p.T → ∀ᵐ z ∂μ,
      j ∈ dataSingletonPending rate rewards C_star C_h i k z →
        aData * chi i k z ≤
          μ[PhaseServiceWaiting.observation
              (dataSingletonObservation rate rewards C_star C_h i) j k |
            Hfield (k + 1)] z := by
    intro j k hk
    let t : Fin p.T := ⟨k, hk⟩
    filter_upwards [
      ReferenceFirstLiveSourceStoppedReleaseService.actual_service_means
        rate rewards C_star C_h control0] with z hmeans
    intro hj
    have hpending :=
      (dataSingletonPending_zero_mem_iff rate rewards C_star C_h i k z).mp (by
        have hj0 : j = (0 : Fin 1) := by
          apply Fin.ext
          omega
        simpa [hj0] using hj)
    have hdata := (hmeans i t hpending).1
    change aData * chi i k z ≤
      μ[PhaseServiceWaiting.observation Xdata i k | Hfield (k + 1)] z
    have hscale : aData * chi i k z =
        ReferenceFirstLiveSourceStoppedReleaseService.c
          rate rewards C_star C_h control0 i t z /
          (2 * (p.K : ℝ)) := by
      rw [ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_fin
        rate rewards C_star C_h control0 i t z]
      dsimp [aData]
      rw [div_eq_mul_inv]
      ring
    rw [hscale, ← hdata]
    exact le_rfl
  have hwaiting :=
    PhaseStartConditionalWaiting.phase_start_task_charge_condExp_bound
      μ hdim hT hK hq Hfield
      (dataSingletonPending rate rewards C_star C_h i)
      (dataSingletonObservation rate rewards C_star C_h i)
      (fun k z => chi i k z) sigma theta aData
      ha
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0)
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_theta_stopping
        rate rewards C_star C_h control0)
      hbounds.1 hbounds.2.1 hbounds.2.2
      hP hphase hnested hw_meas hw_bound hX_meas hquota hservice 0
  have hfun :
      (fun z : Source p =>
        PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z) =
      (fun z : Source p =>
        PhaseServiceWaiting.G
          (dataSingletonPending rate rewards C_star C_h i)
          (fun k z => chi i k z) 0 p.T z) := by
    funext z
    exact (dataSingleton_charge_eq rate rewards C_star C_h control0 i p.T z).symm
  have hCE := congrArg
    (fun f : Source p → ℝ => μ[f | Fσ]) hfun
  have hconst : (1 : ℝ) / aData = 2 * (p.K : ℝ) := by
    dsimp [aData]
    field_simp [ne_of_gt hKreal]
  have hwaiting' :
      μ[(fun ω =>
          PhaseServiceWaiting.G
            (dataSingletonPending rate rewards C_star C_h i)
            (fun k z => chi i k z) 0 p.T ω) |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
          (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
            rate rewards C_star C_h control0)] ≤ᵐ[μ]
        fun _ => (1 : ℝ) / aData := by
    convert hwaiting using 1 <;>
      all_goals first
      | rfl
      | (funext x; norm_num)
  filter_upwards [hwaiting'] with z hz
  calc
    μ[(fun z : Source p =>
        PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z) |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
          (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
            rate rewards C_star C_h control0)] z =
      μ[(fun z : Source p =>
          PhaseServiceWaiting.G
            (dataSingletonPending rate rewards C_star C_h i)
            (fun k z => chi i k z) 0 p.T z) |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
          (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
            rate rewards C_star C_h control0)] z :=
          congrFun hCE z
    _ ≤ (1 : ℝ) / aData := hz
    _ = 2 * (p.K : ℝ) := hconst

private theorem follower_count_cast (d : ℕ) (hd : 1 ≤ d) :
    ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
  rw [Nat.cast_sub hd]
  norm_num

/-- The actual total UP waiting charge has the phase-start conditional bound
with the common whole-source auxiliary weight. -/
theorem up_totalCharge_condExp_bound :
    μ[PhaseServiceWaiting.totalCharge P sigma theta
        (fun k z => omega k z) p.T |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
        (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
          rate rewards C_star C_h control0)] ≤ᵐ[μ]
      fun _ =>
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) /
            (1 - Real.exp (-1)) *
          (Real.log ((p.m : ℝ) - 1) + 1) := by
  let Fσ := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0)
  let d : ℕ := p.m - 1
  let aUp : ℝ := 1 / (12 * (d : ℝ) * (p.K : ℝ))
  have hm : 2 ≤ p.m := p.two_le_m
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hT : 0 < p.T := lt_of_lt_of_le Nat.zero_lt_one p.one_le_T
  have hK : 0 < (1 : ℕ) := by norm_num
  have hq : 0 < (1 : ℕ) := by norm_num
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hKreal : 0 < (p.K : ℝ) := by
    exact_mod_cast ConstructorDimensions.K_pos p
  have hdcast : (d : ℝ) = (p.m : ℝ) - 1 := by
    dsimp [d]
    exact follower_count_cast p.m
      (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)
  have hden : 0 < 12 * (d : ℝ) * (p.K : ℝ) := by positivity
  have hkappa : 0 < 1 - Real.exp (-1) := by
    simp
  have ha : 0 < aUp := by
    dsimp [aUp]
    positivity
  have hbounds := waiting_endpoint_bounds rate rewards C_star C_h
  have hP : ∀ i k, k < p.T →
      MeasurableSet[Hfield (k + 1)] {z : Source p | i ∈ P k z} := by
    intro i k hk
    exact pending_measurable rate rewards C_star C_h control0 i k hk
  have hphase : ∀ k, k < p.T → ∀ z, (P k z).Nonempty →
      sigma z ≤ k + 1 ∧ k + 1 < theta z := by
    intro k _hk z hpending
    exact pending_in_interval rate rewards C_star C_h k z hpending
  have hnested : ∀ s k, s ≤ k → k < p.T → ∀ z,
      sigma z ≤ s + 1 → k + 1 < theta z → P k z ⊆ P s z := by
    intro s k hsk hk z hstart hexit
    exact pending_nested rate rewards C_star C_h s k hsk hk z hstart hexit
  have hw_meas : ∀ k, k < p.T →
      StronglyMeasurable[Hfield (k + 1)] (fun z : Source p => omega k z) := by
    intro k hk
    exact ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_predictable
      rate rewards C_star C_h control0 k hk
  have hw_bound : ∀ k, k < p.T →
      ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      omega k z ∈ Set.Icc (0 : ℝ) ((1 : ℕ) : ℝ) := by
    intro k _hk z
    simpa using ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_bounds
      rate rewards C_star C_h control0 k z
  have hX_meas : ∀ i k, k < p.T →
      StronglyMeasurable[Hfield (k + 2)]
        (PhaseServiceWaiting.observation Xup i k) := by
    intro i k hk
    exact ReferenceFirstLiveSourceStoppedReleaseService.up_observation_predictable
      rate rewards C_star C_h control0 i k hk
  have hquota : ∀ i k, k < p.T → ∀ z, i ∈ P k z →
      PhaseServiceWaiting.N P Xup i k z < 1 := by
    intro i k _hk z hpending
    have hzero :=
      (ReferenceFirstLiveSourceStoppedReleaseQuota.actual_first_release_strict_prior_zero_at_pending
        rate rewards C_star C_h z k i hpending).1
    calc
      PhaseServiceWaiting.N P Xup i k z = 0 := hzero
      _ < 1 := by norm_num
  have hservice : ∀ i k, k < p.T → ∀ᵐ z ∂μ,
      i ∈ P k z → aUp * omega k z ≤
        μ[PhaseServiceWaiting.observation Xup i k | Hfield (k + 1)] z := by
    intro i k hk
    let t : Fin p.T := ⟨k, hk⟩
    filter_upwards [
      ReferenceFirstLiveSourceStoppedReleaseService.actual_service_means
        rate rewards C_star C_h control0] with z hmeans
    intro hpending
    have hup := (hmeans i t hpending).2
    have hscale : aUp * omega k z =
        ReferenceFirstLiveSourceStoppedReleaseService.o
          rate rewards C_star C_h control0 t z /
          ((12 * (p.m : ℝ) - 12) * (p.K : ℝ)) := by
      rw [ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_fin
        rate rewards C_star C_h control0 t z]
      dsimp [aUp]
      rw [hdcast, div_eq_mul_inv]
      ring
    have hden_eq : (12 * (p.m : ℝ) - 12) * (p.K : ℝ) =
        12 * (p.m - 1 : ℝ) * (p.K : ℝ) := by ring
    rw [hden_eq] at hscale
    calc
      aUp * omega k z =
          ReferenceFirstLiveSourceStoppedReleaseService.o
            rate rewards C_star C_h control0 t z /
              (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) := hscale
      _ ≤ μ[PhaseServiceWaiting.observation Xup i k | Hfield (k + 1)] z := hup
  have hwaiting :=
    PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
      μ hd hT hK hq Hfield P Xup (fun k z => omega k z) sigma theta aUp
      ha
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0)
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_theta_stopping
        rate rewards C_star C_h control0)
      hbounds.1 hbounds.2.1 hbounds.2.2
      hP hphase hnested hw_meas hw_bound hX_meas hquota hservice
  have hconstant :
      ((1 : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * aUp) =
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) /
            (1 - Real.exp (-1)) *
          (Real.log ((p.m : ℝ) - 1) + 1) := by
    calc
      ((1 : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * aUp) =
        (12 * (d : ℝ) * (p.K : ℝ)) /
            (1 - Real.exp (-1)) * (Real.log (d : ℝ) + 1) := by
          rw [PhaseServiceWaiting.kappa]
          dsimp [aUp]
          field_simp [ne_of_gt hden, ne_of_gt hkappa]
          ; ring
      _ = (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) /
            (1 - Real.exp (-1)) *
          (Real.log ((p.m : ℝ) - 1) + 1) := by
          rw [hdcast]
  have hwaiting' :
      μ[PhaseServiceWaiting.totalCharge P sigma theta
            (fun k z => omega k z) p.T |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
          (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
            rate rewards C_star C_h control0)] ≤ᵐ[μ]
        fun _ => ((1 : ℝ) + Real.log (d : ℝ)) /
          (PhaseServiceWaiting.kappa * aUp) := by
    convert hwaiting using 1 <;>
      all_goals first
      | rfl
      | (funext x; norm_num)
  filter_upwards [hwaiting'] with z hz
  calc
    μ[PhaseServiceWaiting.totalCharge P sigma theta
        (fun k z => omega k z) p.T |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra Hfield sigma
          (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
            rate rewards C_star C_h control0)] z ≤
      ((1 : ℝ) + Real.log (d : ℝ)) /
        (PhaseServiceWaiting.kappa * aUp) := by
          exact hz
    _ = (12 * ((p.m : ℝ) - 1) * (p.K : ℝ)) /
          (1 - Real.exp (-1)) *
        (Real.log ((p.m : ℝ) - 1) + 1) := hconstant

end Bandits.Support.ReferenceFirstLiveStoppedReleaseWaiting

end noncomputable section
