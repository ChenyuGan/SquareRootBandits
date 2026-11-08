/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationHandoverFreshService
public import Bandits.Support.ReferenceOriginalLaterHandoverStoppedQuota
public import Bandits.Support.ReferenceOriginalInitialHandoverIncomingQuota

import Mathlib.Tactic

/-!
# Uncapped waiting cost for one original fixed installation

The charge, pending tasks, and physical observations are read from the same
fixed calendar installation on the original source execution. Both initial
and later births use the original raw start and retain the inclusive first-bad
update.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:431-490,523-533`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport
open Bandits.Support.ReferenceOriginalInstallationHandoverFreshService
open Bandits.Support.PhaseServiceWaiting
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceOriginalFixedInstallationHandoverWaitingCost

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "rawSigma" =>
  ReferenceOriginalFixedInstallationHandoverSupport.rawSigma rate rewards C_star C_h
local notation "rawTheta" =>
  ReferenceOriginalFixedInstallationHandoverSupport.rawTheta rate rewards C_star C_h
local notation "fixedPending" =>
  ReferenceOriginalFixedInstallationHandoverSupport.pendingSet rate rewards C_star C_h

local notation "quotaH" => 2 * AffineBatchDecoder.quota p + 1
local notation "aH" =>
  1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

/-- The actual fixed-installation pending set on natural source rounds, with
the horizon sentinel convention used by the generic waiting process. -/
public def P_H (ell : Fin p.T) (t : ℕ) (z : Source) : Finset (Fin (p.m - 1)) :=
  if ht : t < p.T then fixedPending ell ⟨t, ht⟩ z else ∅

/-- The Boolean encoding of the actual sum of the before- and after-acceptance
physical service observations. -/
public def X_H (ell : Fin p.T) (i : Fin (p.m - 1)) (t : ℕ) (z : Source) : Bool :=
  if ht : t < p.T then
    decide (Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.X_before
      rate rewards C_star C_h ell ⟨t, ht⟩ i z +
      Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.X_after
      rate rewards C_star C_h ell ⟨t, ht⟩ i z = 1)
  else false

/-- The uncapped whole-row positive-reward count, extended by zero beyond the
source horizon. -/
public def g_H (t : ℕ) (_z : Source) : ℝ :=
  if ht : t < p.T then
    (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards ⟨t, ht⟩ : ℝ)
  else 0

/-- Literal uncapped support charge for one actual fixed installation. -/
public def G_H (ell : Fin p.T) (z : Source) : ℝ :=
  ∑ t : Fin p.T,
    if (fixedPending ell t z).Nonempty then
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
    else 0

/-- The manuscript constant for one handover, with the source exponential
denominator written as its literal value. -/
public def B_hand : ℝ :=
  8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
    (1 - Real.exp (-1)) *
      (2 * (AffineBatchDecoder.quota p : ℝ) +
        Real.log ((p.m - 1 : ℕ) : ℝ) + 1)

private theorem fin_sum_eq_range_real {T : ℕ} (f : Fin T → ℝ) :
    (∑ t : Fin T, f t) =
      ∑ n ∈ Finset.range T,
        if hn : n < T then f ⟨n, hn⟩ else 0 := by
  classical
  let g : ℕ → ℝ := fun n => if hn : n < T then f ⟨n, hn⟩ else 0
  calc
    (∑ t : Fin T, f t) = ∑ t : Fin T, g t.val := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [g, t.isLt]
    _ = ∑ n ∈ Finset.range T, g n := Fin.sum_univ_eq_sum_range g T
    _ = ∑ n ∈ Finset.range T,
        if hn : n < T then f ⟨n, hn⟩ else 0 := rfl

/-- The Boolean service process represents exactly the real physical
before-plus-after observation, including all zero branches. -/
theorem observation_X_H_eq (ell : Fin p.T) (i : Fin (p.m - 1))
    (t : ℕ) (z : Source) :
    PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell)
        i t z =
      if ht : t < p.T then
        Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.X_before
            rate rewards C_star C_h ell ⟨t, ht⟩ i z +
          Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.X_after
            rate rewards C_star C_h ell ⟨t, ht⟩ i z
      else 0 := by
  classical
  by_cases ht : t < p.T
  · have hzeroOne := Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.service_zero_or_one
      rate rewards C_star C_h ell ⟨t, ht⟩ i z
    simp only [X_H, dite_eq_left ht, PhaseServiceWaiting.observation]
    rcases hzeroOne with hzero | hone
    · simp [hzero]
    · simp [hone]
  · simp [X_H, ht, PhaseServiceWaiting.observation]

/-- The generic total charge is the literal finite fixed-calendar support
charge, including absent births and dates erased by the inclusive bad mask. -/
theorem totalCharge_eq_G_H (ell : Fin p.T) (z : Source) :
    PhaseServiceWaiting.totalCharge (P_H rate rewards C_star C_h ell)
      (rawSigma ell) (rawTheta ell) (g_H rewards)
      p.T z = G_H rate rewards C_star C_h ell z := by
  classical
  unfold PhaseServiceWaiting.totalCharge G_H
  let f : ℕ → ℝ := fun n =>
    if hn : n < p.T then
      if (fixedPending ell ⟨n, hn⟩ z).Nonempty then
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards
          ⟨n, hn⟩ : ℝ)
      else 0
    else 0
  have hleft :
      (∑ n ∈ Finset.range p.T,
        PhaseServiceWaiting.A (P_H rate rewards C_star C_h ell)
          (rawSigma ell) (rawTheta ell) (g_H rewards) n z) =
      ∑ n ∈ Finset.range p.T, f n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnT : n < p.T := Finset.mem_range.mp hn
    let t : Fin p.T := ⟨n, hnT⟩
    have hsupport := ReferenceOriginalFixedInstallationHandoverSupport.pending_nonempty_iff_interval
      rate rewards C_star C_h ell t z
    simp only [PhaseServiceWaiting.A, Set.indicator_apply, Set.mem_ofPred_eq]
    change (if rawSigma ell z ≤ n + 1 ∧ n + 1 < rawTheta ell z ∧
        (P_H rate rewards C_star C_h ell n z).Nonempty then
          g_H rewards n z else 0) = f n
    by_cases hP : (fixedPending ell t z).Nonempty
    · have hpending : ∃ i : Fin (p.m - 1),
          ReferenceOriginalFixedInstallationHandoverSupport.pending
            rate rewards C_star C_h ell t i z := by
        rcases hP with ⟨i, hi⟩
        exact ⟨i, (ReferenceOriginalFixedInstallationHandoverSupport.mem_pendingSet_iff
          rate rewards C_star C_h ell t i z).mp hi⟩
      have hinterval := (hsupport).mp hpending
      rcases hinterval with ⟨_, hsigma, htheta⟩
      have hg : g_H rewards n z =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) := by
        simp [g_H, t, hnT]
      simp [t, P_H, hP, hsigma, htheta, f, hnT, hg]
    · simp [t, P_H, hP, f, hnT]
  have hright :
      (∑ t : Fin p.T,
        if (fixedPending ell t z).Nonempty then
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
        else 0) = ∑ n ∈ Finset.range p.T, f n := by
    rw [fin_sum_eq_range_real (fun t : Fin p.T =>
      if (fixedPending ell t z).Nonempty then
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)
      else 0)]
  exact hleft.trans hright.symm

private theorem waiting_parameter_pos :
    0 < p.m - 1 ∧ 0 < p.T ∧ 0 < p.K ∧ 0 < quotaH ∧ 0 < aH := by
  have hd : 0 < p.m - 1 := Nat.sub_pos_of_lt
    (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hq : 0 < 2 * AffineBatchDecoder.quota p + 1 := by omega
  have ha : 0 < aH := by
    have hdR : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hd
    have hKR : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    positivity
  exact ⟨hd, ConstructorDimensions.T_pos p, ConstructorDimensions.K_pos p, hq, ha⟩

public theorem phase_bounds (ell : Fin p.T) (t : ℕ) (ht : t < p.T) (z : Source)
    (hne : (P_H rate rewards C_star C_h ell t z).Nonempty) :
    rawSigma ell z ≤ t + 1 ∧ t + 1 < rawTheta ell z := by
  have hfin : (fixedPending ell ⟨t, ht⟩ z).Nonempty := by
    simpa [P_H, ht] using hne
  have h := ReferenceOriginalFixedInstallationHandoverSupport.pending_nonempty_iff_interval
    rate rewards C_star C_h ell ⟨t, ht⟩ z
  rcases h.mp (by
    rcases hfin with ⟨i, hi⟩
    exact ⟨i, (ReferenceOriginalFixedInstallationHandoverSupport.mem_pendingSet_iff
      rate rewards C_star C_h ell ⟨t, ht⟩ i z).mp hi⟩) with
    ⟨_, hs, he⟩
  exact ⟨hs, he⟩

public theorem g_H_bounds (t : ℕ) (ht : t < p.T) (z : Source) :
    g_H rewards t z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
  have hcard : ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards
      ⟨t, ht⟩ ≤ p.K := by
    unfold ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms
    calc
      (Finset.univ.filter fun a : Fin p.K => 0 < rewards ⟨t, ht⟩ a).card ≤
          (Finset.univ : Finset (Fin p.K)).card := Finset.card_filter_le _ _
      _ = p.K := by simp
  simp only [g_H, dite_eq_left ht]
  exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hcard⟩

public theorem pending_preRound_measurable (ell : Fin p.T) (i : Fin (p.m - 1))
    (t : ℕ) (ht : t < p.T) :
    MeasurableSet[F (t + 1)] {z : Source | i ∈ P_H rate rewards C_star C_h ell t z} := by
  let ft : Fin p.T := ⟨t, ht⟩
  have h := ReferenceOriginalFixedInstallationHandoverSupport.pending_measurableSet
    rate rewards C_star C_h control0 ell ft i
  have hset : {z : Source | i ∈ P_H rate rewards C_star C_h ell t z} =
      {z : Source | ReferenceOriginalFixedInstallationHandoverSupport.pending
        rate rewards C_star C_h ell ft i z} := by
    ext z
    simp [P_H, ft, ht, ReferenceOriginalFixedInstallationHandoverSupport.pendingSet,
      ReferenceOriginalFixedInstallationHandoverSupport.pending]
  rw [hset]
  exact h

public theorem pending_in_phase_nested (ell : Fin p.T) (s t : ℕ) (hst : s ≤ t)
    (ht : t < p.T) (z : Source) (hsigma : rawSigma ell z ≤ s + 1)
    (_htheta : t + 1 < rawTheta ell z) :
    P_H rate rewards C_star C_h ell t z ⊆ P_H rate rewards C_star C_h ell s z := by
  have hs : s < p.T := lt_of_le_of_lt hst ht
  have hbirth := (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_le_iff
    rate rewards C_star C_h ell z (s + 1)).mp hsigma
  have hell : ell.val ≤ s := by
    rcases hbirth with hterminal | ⟨hdate, _⟩
    · omega
    · omega
  intro i hi
  have hmem : i ∈ fixedPending ell ⟨t, ht⟩ z := by
    simpa [P_H, ht] using hi
  have hraw := (ReferenceOriginalFixedInstallationHandoverSupport.mem_pendingSet_iff
    rate rewards C_star C_h ell ⟨t, ht⟩ i z).mp hmem
  have hback := ReferenceOriginalFixedInstallationHandoverSupport.pending_backward
    rate rewards C_star C_h ell ⟨s, hs⟩ ⟨t, ht⟩ i z hell hst hraw
  have hback' := (ReferenceOriginalFixedInstallationHandoverSupport.mem_pendingSet_iff
    rate rewards C_star C_h ell ⟨s, hs⟩ i z).mpr hback
  simpa [P_H, hs] using hback'

public theorem weight_preRound_stronglyMeasurable (t : ℕ) (ht : t < p.T) :
    StronglyMeasurable[F (t + 1)] (g_H rewards t) := by
  have heq : g_H rewards t = fun _ : Source =>
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards
        ⟨t, ht⟩ : ℝ) := by
    funext z
    simp [g_H, ht]
  rw [heq]
  exact stronglyMeasurable_const

public theorem observation_roundEnd_stronglyMeasurable (ell : Fin p.T)
    (i : Fin (p.m - 1)) (t : ℕ) (ht : t < p.T) :
    StronglyMeasurable[F (t + 2)]
      (PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell) i t) := by
  let ft : Fin p.T := ⟨t, ht⟩
  have hcombined := Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.combined_roundEnd_stronglyMeasurable
    rate rewards C_star C_h control0 ell ft i
  have hEq : (fun z : Source => PhaseServiceWaiting.observation
      (X_H rate rewards C_star C_h ell) i t z) =
      (fun z => X_before
        rate rewards C_star C_h ell ft i z +
        X_after
          rate rewards C_star C_h ell ft i z) := by
    funext z
    rw [observation_X_H_eq]
    simp [ht, ft]
  simpa only [← hEq] using hcombined

public theorem service_inequality (ell : Fin p.T) (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂μ, i ∈ fixedPending ell t z →
      aH * g_H rewards t.val z ≤
        μ[PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell)
          i t.val | F (t.val + 1)] z := by
  have hLaw := Bandits.Support.ReferenceOriginalInstallationHandoverFreshService.combined_condExp_integral
    rate rewards C_star C_h control0 ell t i
  have hEq : (fun z : Source => PhaseServiceWaiting.observation
      (X_H rate rewards C_star C_h ell) i t.val z) =
      (fun z => X_before
        rate rewards C_star C_h ell t i z +
        X_after
          rate rewards C_star C_h ell t i z) := by
    funext z
    rw [observation_X_H_eq]
    simp [t.isLt]
  have hCE :
      μ[PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell)
          i t.val | F (t.val + 1)] =ᵐ[μ]
        μ[(fun z => X_before rate rewards C_star C_h ell t i z +
          X_after rate rewards C_star C_h ell t i z) | F (t.val + 1)] := by
    exact MeasureTheory.condExp_congr_ae (m := F (t.val + 1))
      (ae_of_all μ fun z => congrFun hEq z)
  have hcount : ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t =
      (Finset.univ.filter fun a : Fin p.K => 0 < (rewards t a).val).card := by
    unfold ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms
    congr 1
  have hcoef (z : Source) : aH * g_H rewards t.val z =
      serviceCoefficient
        rewards t := by
    simp only [g_H, dite_eq_left t.isLt, serviceCoefficient]
    rw [hcount]
    ring
  filter_upwards [hCE, hLaw] with z hzEq hzLaw
  intro hi
  have hpending := (ReferenceOriginalFixedInstallationHandoverSupport.mem_pendingSet_iff
    rate rewards C_star C_h ell t i z).mp hi
  have hcoef' := hcoef z
  have hzLaw' : μ[(fun z =>
        X_before
          rate rewards C_star C_h ell t i z +
        X_after
          rate rewards C_star C_h ell t i z) | F (t.val + 1)] z =
      serviceCoefficient
        rewards t := by
    simpa [ReferenceOriginalFixedInstallationHandoverSupport.pending, hpending] using hzLaw
  calc
    aH * g_H rewards t.val z =
        serviceCoefficient
          rewards t := hcoef'
    _ = μ[(fun z =>
        X_before
          rate rewards C_star C_h ell t i z +
        X_after
          rate rewards C_star C_h ell t i z) | F (t.val + 1)] z := hzLaw'.symm
    _ = μ[PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell)
        i t.val | F (t.val + 1)] z := hzEq.symm
    _ ≤ μ[PhaseServiceWaiting.observation (X_H rate rewards C_star C_h ell)
        i t.val | F (t.val + 1)] z := le_rfl

/-- Integrability of the uncapped literal support charge on the original
source law. -/
theorem integrable_G_H (control0 : ContinuousLearningRows.TimeControl p)
    (ell : Fin p.T) : Integrable (G_H rate rewards C_star C_h ell) μ := by
  obtain ⟨_, _, _, _, ha⟩ := waiting_parameter_pos (p := p)
  have hSigma := ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_preRoundStoppingTime
    rate rewards C_star C_h control0 ell
  have hTheta := ReferenceOriginalFixedInstallationHandoverSupport.rawTheta_preRoundStoppingTime
    rate rewards C_star C_h control0 ell
  have hgeneric := PhaseServiceWaiting.totalCharge_exp_integrable μ
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (P_H rate rewards C_star C_h ell) (rawSigma ell) (rawTheta ell)
    (g_H rewards) aH ha hSigma hTheta
    (fun i t ht => pending_preRound_measurable rate rewards C_star C_h control0 ell i t ht)
    (weight_preRound_stronglyMeasurable rewards control0)
    (phase_bounds rate rewards C_star C_h ell)
    (g_H_bounds rewards)
  apply hgeneric.1.congr
  exact Filter.Eventually.of_forall fun z =>
    totalCharge_eq_G_H rate rewards C_star C_h ell z

/-- The actual source-prefix stopping σ-algebra at the original raw birth
start for this fixed calendar installation. -/
@[instance_reducible] noncomputable def phaseStartSigmaAlgebra (ell : Fin p.T) : MeasurableSpace Source :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (rawSigma ell)
    (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_preRoundStoppingTime
      rate rewards C_star C_h control0 ell)

/-- The generic waiting constant is exactly the manuscript handover constant. -/
theorem waiting_constant_eq_B_hand :
    (((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
      (PhaseServiceWaiting.kappa * aH)) = B_hand (p := p) := by
  have hd : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr
    (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m))
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hk : PhaseServiceWaiting.kappa ≠ 0 :=
    ne_of_gt PhaseServiceWaiting.kappa_pos
  have hden : (8 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) ≠ 0 := by positivity
  dsimp [B_hand, PhaseServiceWaiting.kappa]
  field_simp [hk, hden]
  ring

private theorem X_H_true_iff (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    X_H rate rewards C_star C_h ell i t.val z = true ↔
      (before rate rewards C_star C_h ell t i z ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_before rate rewards C_star C_h i t z) ∨
      (after rate rewards C_star C_h ell t i z ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_after rate rewards C_star C_h i t z) := by
  classical
  simp only [X_H, dite_eq_left t.isLt, X_before, X_after]
  have hdis := stages_disjoint rate rewards C_star C_h ell t i z
  by_cases hb : before rate rewards C_star C_h ell t i z <;>
    by_cases ha : after rate rewards C_star C_h ell t i z <;>
    by_cases hvb : ReferenceFirstLiveHandoverBoundaryFactorization.V_before
      rate rewards C_star C_h i t z <;>
    by_cases hva : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
      rate rewards C_star C_h i t z <;> simp_all

private theorem status_success (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (k : Fin 3) (h : preRoundStatus rate rewards C_star C_h t i z = some k) :
    ∃ state memory,
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i z = .inr (.success state memory) ∧ state.status = k := by
  unfold preRoundStatus at h
  cases he : ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
      rate rewards C_star C_h t i z with
  | inl u => simp [he, startStatusCode] at h
  | inr result =>
    cases result with
    | success state memory =>
      exact ⟨state, memory, rfl, by simpa only [he, startStatusCode, Option.some.injEq] using h⟩
    | failure error => simp [he, startStatusCode] at h

private theorem later_pending_record (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hb : b.val = ell.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (hlater : laterBirthAt rate rewards C_star C_h ell z)
    (hp : rawPending rate rewards C_star C_h ell t i z) :
    ∃ j : Fin (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b).length,
      (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b)[j.val].input.time = t ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
          rate rewards C_star C_h z b)[j.val].input,
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
          rate rewards C_star C_h z b)[j.val].output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice := by
  rcases hp with ⟨r, hr, hf, ht, hs, _⟩ | ⟨b', hb', _, _, _, _, _, _, _, _, _, rest⟩
  · exact (initialBirthAt_not_laterBirthAt rate rewards C_star C_h ell z
      ⟨r, hr, hf, ht, hs⟩ hlater).elim
  · have he : b' = b := Fin.ext (hb'.trans hb.symm)
    subst b'
    exact rest

/-- Each true fixed-installation service on a later birth is the SAME actual
physical tick, with its incoming pending set and inclusive bad-date mask. -/
theorem later_X_H_physicalTick (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hb : b.val = ell.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (hlater : laterBirthAt rate rewards C_star C_h ell z)
    (hx : X_H rate rewards C_star C_h ell i t.val z = true) :
    ReferenceOriginalLaterHandoverStoppedQuota.originalHandoverPhysicalTick
      rate rewards C_star C_h z b i t = 1 := by
  have hservice := (X_H_true_iff rate rewards C_star C_h ell t i z).mp hx
  have hp : pending rate rewards C_star C_h ell t i z := by
    rcases hservice with h | h
    · exact h.1.1
    · exact h.1.1
  obtain ⟨j, ht, selected, hs, hi⟩ :=
    later_pending_record rate rewards C_star C_h ell t i z b hb hlater hp.2
  unfold ReferenceOriginalLaterHandoverStoppedQuota.originalHandoverPhysicalTick
  apply ite_eq_left
  refine ⟨j, ht, selected, hs, hi, hp.1, ?_⟩
  rcases hservice with ⟨hbefore, hv⟩ | ⟨hafter, hv⟩
  · obtain ⟨state, memory, hstate, hstatus⟩ :=
      status_success rate rewards C_star C_h t i z 0 hbefore.2
    exact Or.inl ⟨state, memory, hstate, hstatus, hv⟩
  · obtain ⟨state, memory, hstate, hstatus⟩ :=
      status_success rate rewards C_star C_h t i z 1 hafter.2
    exact Or.inr ⟨state, memory, hstate, hstatus, hv⟩

private theorem range_fin_sum (T n : ℕ) (f : Fin T → ℕ) :
    (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
      ∑ t : Fin T, if t.val < n then f t else 0 := by
  classical
  let g : ℕ → ℕ := fun r =>
    if hr : r < T then if r < n then f ⟨r, hr⟩ else 0 else 0
  have hleft :
      (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
        ∑ r ∈ Finset.range n, g r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    by_cases hrT : r < T <;> simp [g, hrn, hrT]
  have hright :
      (∑ t : Fin T, if t.val < n then f t else 0) =
        ∑ r ∈ Finset.range T, g r := by
    calc
      (∑ t : Fin T, if t.val < n then f t else 0) =
          ∑ t : Fin T, g t.val := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases htn : t.val < n <;> simp [g, t.isLt, htn]
      _ = ∑ r ∈ Finset.range T, g r := Fin.sum_univ_eq_sum_range g T
  have heq : (∑ r ∈ Finset.range n, g r) = ∑ r ∈ Finset.range T, g r := by
    by_cases hn : n ≤ T
    · apply Finset.sum_subset (Finset.range_subset_range.mpr hn)
      intro r _ hrn
      have hnlt : ¬ r < n := fun h => hrn (Finset.mem_range.mpr h)
      simp [g, hnlt]
    · symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hn)))
      intro r _ hrT
      have hTlt : ¬ r < T := fun h => hrT (Finset.mem_range.mpr h)
      simp [g, hTlt]
  exact hleft.trans (heq.trans hright.symm)

private theorem N_le_physical_count (ell : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (n : ℕ) (f : Fin p.T → ℕ)
    (hf : ∀ t : Fin p.T, X_H rate rewards C_star C_h ell i t.val z = true → 1 ≤ f t) :
    PhaseServiceWaiting.N (P_H rate rewards C_star C_h ell)
        (X_H rate rewards C_star C_h ell) i n z ≤
      ∑ t : Fin p.T, if t.val < n then f t else 0 := by
  rw [← range_fin_sum p.T n f]
  unfold PhaseServiceWaiting.N
  apply Finset.sum_le_sum
  intro s _
  by_cases hsT : s < p.T
  · rw [dite_eq_left hsT]
    by_cases hx : i ∈ P_H rate rewards C_star C_h ell s z ∧
        X_H rate rewards C_star C_h ell i s z = true
    · rw [ite_eq_left hx]
      exact hf ⟨s, hsT⟩ hx.2
    · rw [ite_eq_right hx]
      exact Nat.zero_le _
  · simp [P_H, hsT]

/-- At every natural prefix, the fixed-installation count is dominated by
the SAME actual later-H physical count. No truncation or replay relabeling is
used in this bridge. -/
theorem N_le_originalHandoverPhysicalCount (ell : Fin p.T) (i : Fin (p.m - 1))
    (z : Source)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hb : b.val = ell.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (hlater : laterBirthAt rate rewards C_star C_h ell z) (n : ℕ) :
    PhaseServiceWaiting.N (P_H rate rewards C_star C_h ell)
        (X_H rate rewards C_star C_h ell) i n z ≤
      ReferenceOriginalLaterHandoverStoppedQuota.originalHandoverPhysicalCount
        rate rewards C_star C_h z b i n := by
  exact N_le_physical_count rate rewards C_star C_h ell i z n
    (ReferenceOriginalLaterHandoverStoppedQuota.originalHandoverPhysicalTick
      rate rewards C_star C_h z b i)
    (fun t hx => (later_X_H_physicalTick rate rewards C_star C_h ell t i z b hb hlater hx).ge)

/-- The natural-prefix count is exactly the literal finite physical-service
sum used by the initial quota producer, at the unchanged prefix. -/
theorem N_eq_initial_service_sum (ell : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) (n : ℕ) :
    PhaseServiceWaiting.N (P_H rate rewards C_star C_h ell)
        (X_H rate rewards C_star C_h ell) i n z =
      ∑ s : Fin p.T,
        if s.val < n ∧ i ∈ fixedPending ell s z ∧
          X_before rate rewards C_star C_h ell s i z +
            X_after rate rewards C_star C_h ell s i z = 1
        then (1 : ℕ) else 0 := by
  classical
  unfold PhaseServiceWaiting.N
  have heq :
      (∑ r ∈ Finset.range n,
        if i ∈ P_H rate rewards C_star C_h ell r z ∧
            X_H rate rewards C_star C_h ell i r z = true then 1 else 0) =
      ∑ r ∈ Finset.range n,
        if hr : r < p.T then
          (if i ∈ fixedPending ell ⟨r, hr⟩ z ∧
            X_before rate rewards C_star C_h ell ⟨r, hr⟩ i z +
              X_after rate rewards C_star C_h ell ⟨r, hr⟩ i z = 1
          then (1 : ℕ) else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r < p.T <;> simp [P_H, X_H, hr]
  rw [heq, range_fin_sum p.T n (fun s : Fin p.T =>
    if i ∈ fixedPending ell s z ∧
        X_before rate rewards C_star C_h ell s i z +
          X_after rate rewards C_star C_h ell s i z = 1 then 1 else 0)]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.val < n <;> simp [hs]

/-- Strict incoming quota for the actual Boolean service process, on both
original birth branches. The prefix excludes the incoming round, while the
pending event retains the first detecting update inclusively. -/
theorem incoming_quota (ell : Fin p.T) (i : Fin (p.m - 1))
    (t : ℕ) (ht : t < p.T) (z : Source)
    (hi : i ∈ P_H rate rewards C_star C_h ell t z) :
    PhaseServiceWaiting.N (P_H rate rewards C_star C_h ell)
      (X_H rate rewards C_star C_h ell) i t z < quotaH := by
  let ft : Fin p.T := ⟨t, ht⟩
  have hmem : i ∈ fixedPending ell ft z := by simpa [P_H, ht, ft] using hi
  obtain ⟨hgate, hraw⟩ :=
    (mem_pendingSet_iff rate rewards C_star C_h ell ft i z).mp hmem
  rcases hraw with hinitial | hlater
  · obtain ⟨r, hr, hf, htime, hstart, _⟩ := hinitial
    rw [N_eq_initial_service_sum]
    exact ReferenceOriginalInitialHandoverIncomingQuota.initial_incoming_quota
      rate rewards C_star C_h ell ft i z ⟨r, hr, hf, htime, hstart⟩ hmem
  · obtain ⟨b, hb, htime, hlookup, payload, ledger, saved, hc, he,
      installed, hinst, j, hj, selected, hs, hp⟩ := hlater
    have hbirth : laterBirthAt rate rewards C_star C_h ell z :=
      ⟨b, hb, htime, hlookup, payload, ledger, saved, hc, he, installed, hinst⟩
    have hchosen := laterBirthAt_is_laterChosen rate rewards C_star C_h
      z b payload ledger saved hc he
    obtain ⟨_payload, _before, _memory, _hbirth, _hbefore, _hdom, hstrict⟩ :=
      ReferenceOriginalLaterHandoverStoppedQuota.original_later_handover_physical_service_domination
        rate rewards C_star C_h z b i hchosen
    have hgate' :
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
          rate rewards C_star C_h z b)[j.val].input.time.val + 1 ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
      rw [hj]
      exact hgate
    have hstrict' := hstrict j selected hs hp hgate'
    rw [hj] at hstrict'
    exact lt_of_le_of_lt
      (N_le_originalHandoverPhysicalCount rate rewards C_star C_h ell i z b hb hbirth t)
      hstrict'

/-- Full original-law conditional bound at the analytical source-prefix
stopped field of the original raw start. The charge is uncapped. -/
theorem condExp_G_H_le_B_hand (ell : Fin p.T) :
    μ[G_H rate rewards C_star C_h ell |
        phaseStartSigmaAlgebra rate rewards C_star C_h control0 ell] ≤ᵐ[μ]
      fun _ => B_hand (p := p) := by
  obtain ⟨hd, hT, hK, hq, ha⟩ := waiting_parameter_pos (p := p)
  have hSigma := rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell
  have hTheta := rawTheta_preRoundStoppingTime rate rewards C_star C_h control0 ell
  have hbound := PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
    μ hd hT hK hq F
    (P_H rate rewards C_star C_h ell) (X_H rate rewards C_star C_h ell)
    (g_H rewards) (rawSigma ell) (rawTheta ell) aH ha hSigma hTheta
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).1)
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).2.1)
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).2.2)
    (pending_preRound_measurable rate rewards C_star C_h control0 ell)
    (phase_bounds rate rewards C_star C_h ell)
    (pending_in_phase_nested rate rewards C_star C_h ell)
    (weight_preRound_stronglyMeasurable rewards control0)
    (g_H_bounds rewards)
    (observation_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 ell)
    (incoming_quota rate rewards C_star C_h ell)
    (fun i t ht => by
      simpa only [P_H, dite_eq_left ht] using
        service_inequality rate rewards C_star C_h control0 ell ⟨t, ht⟩ i)
  have hcharge :
      PhaseServiceWaiting.totalCharge (P_H rate rewards C_star C_h ell)
        (rawSigma ell) (rawTheta ell) (g_H rewards) p.T =
      G_H rate rewards C_star C_h ell :=
    funext (totalCharge_eq_G_H rate rewards C_star C_h ell)
  rw [hcharge] at hbound
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hbound
  rw [waiting_constant_eq_B_hand (p := p)] at hbound
  exact hbound

/-- Every event measurable at the same original raw phase start satisfies the
localized uncapped support-cost bound. -/
theorem setIntegral_G_H_le_B_hand (ell : Fin p.T) (B : Set Source)
    (hB : MeasurableSet[phaseStartSigmaAlgebra rate rewards C_star C_h control0 ell] B) :
    ∫ z in B, G_H rate rewards C_star C_h ell z ∂μ ≤
      B_hand (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  obtain ⟨hd, hT, hK, hq, ha⟩ := waiting_parameter_pos (p := p)
  have hSigma := rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell
  have hTheta := rawTheta_preRoundStoppingTime rate rewards C_star C_h control0 ell
  have hbound := PhaseStartConditionalWaiting.phase_start_totalCharge_setIntegral_bound
    μ hd hT hK hq F
    (P_H rate rewards C_star C_h ell) (X_H rate rewards C_star C_h ell)
    (g_H rewards) (rawSigma ell) (rawTheta ell) aH ha hSigma hTheta
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).1)
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).2.1)
    (fun z => (rawEndpoints_bounds rate rewards C_star C_h ell z).2.2)
    (pending_preRound_measurable rate rewards C_star C_h control0 ell)
    (phase_bounds rate rewards C_star C_h ell)
    (pending_in_phase_nested rate rewards C_star C_h ell)
    (weight_preRound_stronglyMeasurable rewards control0)
    (g_H_bounds rewards)
    (observation_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 ell)
    (incoming_quota rate rewards C_star C_h ell)
    (fun i t ht => by
      simpa only [P_H, dite_eq_left ht] using
        service_inequality rate rewards C_star C_h control0 ell ⟨t, ht⟩ i)
    B hB
  have hcharge :
      PhaseServiceWaiting.totalCharge (P_H rate rewards C_star C_h ell)
        (rawSigma ell) (rawTheta ell) (g_H rewards) p.T =
      G_H rate rewards C_star C_h ell :=
    funext (totalCharge_eq_G_H rate rewards C_star C_h ell)
  rw [hcharge] at hbound
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hbound
  rw [waiting_constant_eq_B_hand (p := p)] at hbound
  exact hbound

end Bandits.Support.ReferenceOriginalFixedInstallationHandoverWaitingCost

end
