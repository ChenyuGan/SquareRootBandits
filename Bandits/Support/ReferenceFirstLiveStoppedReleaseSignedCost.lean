/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseCalendarSignedCost
public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSentinelBound

/-!
# Conditional signed cost on the actual stopped first release

This file integrates the actual signed physical deficit over the original
whole-source law. It combines the calendar deficit with actual DATA charges
and tests the stopped reward-weighted sentinel only on the phase-active part
of a phase-start measurable set.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

abbrev Source (p₀ : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p₀

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "H" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "P" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h
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
local notation "Fσ" =>
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra H sigma
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0)

/-- The actual DATA waiting charge of follower `i` on the original stopped
pending readout. -/
def actualFirstReleaseFollowerCharge
    (i : Fin (p.m - 1)) (z : Source p) : ℝ :=
  PhaseServiceWaiting.G P (fun k z => chi i k z) i p.T z

/-- The actual auxiliary waiting charge on the original stopped pending
readout. -/
def actualFirstReleaseAuxiliaryCharge (z : Source p) : ℝ :=
  PhaseServiceWaiting.totalCharge P sigma theta (fun k z => omega k z) p.T z

private theorem pending_member_measurable (i : Fin (p.m - 1)) (k : ℕ)
    (hk : k < p.T) :
    MeasurableSet[H (k + 1)] {z : Source p | i ∈ P k z} := by
  change MeasurableSet[H (k + 1)]
    {z : Source p | i ∈
      ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
        rate rewards C_star C_h (⟨k, hk⟩ : Fin p.T).val z}
  simpa [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat, hk] using
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_pending_adapted
      rate rewards C_star C_h control0 ⟨k, hk⟩ i

private theorem pending_members_measurable :
    ∀ i k, k < p.T →
      MeasurableSet[H (k + 1)] {z : Source p | i ∈ P k z} := by
  intro i k hk
  exact pending_member_measurable rate rewards C_star C_h control0 i k hk

private theorem pending_nonempty_inside_phase :
    ∀ k, k < p.T → ∀ z : Source p, (P k z).Nonempty →
      sigma z ≤ k + 1 ∧ k + 1 < theta z := by
  intro k hk z hne
  by_contra hout
  have hempty :=
    ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_empty_outside_interval
      rate rewards C_star C_h z k hout
  simp [hempty] at hne

private theorem assigned_chi_integrable (i : Fin (p.m - 1)) (k : ℕ)
    (hk : k < p.T) : Integrable (fun z : Source p => chi i k z) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hsm :=
    (ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_predictable
      rate rewards C_star C_h control0 i k hk).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (k + 1))
  apply Integrable.of_mem_Icc 0 1 hsm.aemeasurable
  filter_upwards with z
  have hz :=
    ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_bounds
      rate rewards C_star C_h control0 i k z
  exact ⟨hz.1, hz.2⟩

private def followerStepTerm (i : Fin (p.m - 1)) (k : ℕ)
    (z : Source p) : ℝ :=
  if i ∈ P k z then chi i k z else 0

private def followerStepTotal (k : ℕ) (z : Source p) : ℝ :=
  ∑ i : Fin (p.m - 1), followerStepTerm rate rewards C_star C_h control0 i k z

private theorem followerStepTotal_eq_pending_sum (k : ℕ) (z : Source p) :
    followerStepTotal rate rewards C_star C_h control0 k z =
      ∑ i ∈ P k z, chi i k z := by
  classical
  simp [followerStepTotal, followerStepTerm, Finset.sum_ite_mem]

private theorem follower_step_term_integrable (i : Fin (p.m - 1)) (k : ℕ)
    (hk : k < p.T) : Integrable (followerStepTerm rate rewards C_star C_h control0 i k) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hset : MeasurableSet {z : Source p | i ∈ P k z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (k + 1) _
      (pending_member_measurable rate rewards C_star C_h control0 i k hk)
  have hchi := assigned_chi_integrable rate rewards C_star C_h control0 i k hk
  have h := hchi.indicator hset
  convert h using 1
  ext z
  simp [followerStepTerm, Set.indicator]

private theorem follower_step_total_integrable (k : ℕ) (hk : k < p.T) :
    Integrable (followerStepTotal rate rewards C_star C_h control0 k) μ := by
  classical
  unfold followerStepTotal
  exact integrable_finsetSum _ (fun i _ =>
    follower_step_term_integrable rate rewards C_star C_h control0 i k hk)

private theorem follower_step_total_setIntegral (B : Set (Source p))
    (k : ℕ) (hk : k < p.T) :
    ∫ z in B, followerStepTotal rate rewards C_star C_h control0 k z ∂μ =
      ∑ i : Fin (p.m - 1),
        ∫ z in B, followerStepTerm rate rewards C_star C_h control0 i k z ∂μ := by
  classical
  unfold followerStepTotal
  rw [integral_finsetSum]
  intro i hi
  exact (follower_step_term_integrable rate rewards C_star C_h control0 i k hk).integrableOn

private theorem follower_charge_setIntegral_eq_round_sum (B : Set (Source p))
    (hB : MeasurableSet B) (i : Fin (p.m - 1)) :
    ∫ z in B, actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ =
      ∑ t : Fin p.T,
        ∫ z in B, followerStepTerm rate rewards C_star C_h control0 i t.val z ∂μ := by
  classical
  have hterms (t : Fin p.T) :
      (fun z : Source p =>
        if i ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
            rate rewards C_star C_h z t then
          ReferenceFirstLiveSourceStoppedReleaseService.c
            rate rewards C_star C_h control0 i t z
        else 0) =
      (fun z => followerStepTerm rate rewards C_star C_h control0 i t.val z) := by
    funext z
    dsimp [followerStepTerm]
    rw [← ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
          rate rewards C_star C_h t z,
        ← ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_fin
          rate rewards C_star C_h control0 i t z]
  calc
    ∫ z in B, actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ
        = ∫ z in B,
            (fun z : Source p =>
              ∑ t : Fin p.T,
                if i ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
                    rate rewards C_star C_h z t then
                  ReferenceFirstLiveSourceStoppedReleaseService.c
                    rate rewards C_star C_h control0 i t z
                else 0) z ∂μ := by
          apply setIntegral_congr_fun hB
          intro z _
          exact ReferenceFirstLiveStoppedReleaseWaiting.dataCharge_eq_actual_fin_sum
            rate rewards C_star C_h control0 i z
    _ = ∑ t : Fin p.T,
          ∫ z in B,
            (fun z : Source p =>
              if i ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
                  rate rewards C_star C_h z t then
                ReferenceFirstLiveSourceStoppedReleaseService.c
                  rate rewards C_star C_h control0 i t z
              else 0) z ∂μ := by
          rw [integral_finsetSum]
          intro t ht
          rw [hterms t]
          exact (follower_step_term_integrable rate rewards C_star C_h control0 i t.val t.isLt).integrableOn
    _ = ∑ t : Fin p.T,
          ∫ z in B, followerStepTerm rate rewards C_star C_h control0 i t.val z ∂μ := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hterms t]

private theorem auxiliary_mask_term_eq_actual (t : Fin p.T) (z : Source p) :
    (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z =
      if (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rate rewards C_star C_h z t).Nonempty then
        ReferenceFirstLiveSourceStoppedReleaseService.o
          rate rewards C_star C_h control0 t z
      else 0 := by
  rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
        rate rewards C_star C_h t z,
      ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_fin
        rate rewards C_star C_h control0 t z]
  by_cases hp : (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
      rate rewards C_star C_h z t).Nonempty <;> simp [hp]

private theorem auxiliary_mask_sum_eq_actual (z : Source p) :
    (∑ t : Fin p.T,
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z) =
      actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z := by
  calc
    _ = ∑ t : Fin p.T,
          if (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rate rewards C_star C_h z t).Nonempty then
            ReferenceFirstLiveSourceStoppedReleaseService.o
              rate rewards C_star C_h control0 t z
          else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            exact auxiliary_mask_term_eq_actual rate rewards C_star C_h control0 t z
    _ = actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z :=
      (ReferenceFirstLiveStoppedReleaseWaiting.totalCharge_eq_actual_fin_sum
        rate rewards C_star C_h control0 z).symm

/-- Actual DATA waiting charges are integrable on the original private-source
law, using the stopped pending adaptation and the actual assigned coefficient. -/
theorem actual_first_release_follower_charge_integrable
    (i : Fin (p.m - 1)) :
    Integrable (actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact PhaseStartConditionalWaiting.task_charge_integrable (K := 1) μ H P
    (fun k z => chi i k z)
    (pending_members_measurable rate rewards C_star C_h control0)
    (fun k hk =>
      (ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_predictable
        rate rewards C_star C_h control0 i k hk))
    (fun k hk z => by
      simpa [Set.mem_Icc] using
        ReferenceFirstLiveSourceStoppedReleaseService.assignedChi_bounds
          rate rewards C_star C_h control0 i k z)
    i

/-- The actual auxiliary UP waiting charge is integrable on the original
private-source law, with its actual stopping interval and auxiliary readout. -/
theorem actual_first_release_auxiliary_charge_integrable :
    Integrable (actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have h := PhaseServiceWaiting.totalCharge_exp_integrable (K := 1) μ H P sigma theta
    (fun k z => omega k z) (1 : ℝ) (by norm_num)
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0)
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_theta_stopping
      rate rewards C_star C_h control0)
    (pending_members_measurable rate rewards C_star C_h control0)
    (fun k hk =>
      ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_predictable
        rate rewards C_star C_h control0 k hk)
    (pending_nonempty_inside_phase rate rewards C_star C_h)
    (fun k hk z => by
      simpa [Set.mem_Icc] using
        ReferenceFirstLiveSourceStoppedReleaseService.auxiliaryWeight_bounds
          rate rewards C_star C_h control0 k z)
  exact h.1

private theorem stopped_sentinel_setIntegral_bound (B : Set (Source p))
    (hB : MeasurableSet[Fσ] B) (t : Fin p.T) :
    ∫ z in B,
        ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
          rate rewards C_star C_h t z ∂μ ≤
      ∫ z in B,
        (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ := by
  classical
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let A : Set (Source p) := {z | (P t.val z).Nonempty}
  let E : Set (Source p) := B ∩ A
  have hA : MeasurableSet[H (t.val + 1)] A := by
    rw [show A = ⋃ i : Fin (p.m - 1), {z : Source p | i ∈ P t.val z} by
      ext z
      simp [A, Finset.Nonempty]]
    exact MeasurableSet.iUnion fun i =>
      pending_members_measurable rate rewards C_star C_h control0 i t.val t.isLt
  have hE : MeasurableSet[H (t.val + 1)] E :=
    PhaseStartConditionalWaiting.phaseStart_inter_active_measurable
      H P sigma theta
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0)
      (pending_members_measurable rate rewards C_star C_h control0)
      (pending_nonempty_inside_phase rate rewards C_star C_h) B hB t.val t.isLt
  have hFAmbient : MeasurableSet B :=
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H sigma
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0)) B hB
  have hAAmbient : MeasurableSet A :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
      (t.val + 1) A hA
  have hfInt :=
    ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel_integrable
      rate rewards C_star C_h control0 t
  have hgInt :=
    ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedAuxiliaryWeight_integrable
      rate rewards C_star C_h control0 t
  have hcond :=
    ReferenceFirstLiveStoppedReleaseSentinelBound.stoppedPendingMaskedSentinel_condExp_le
      rate rewards C_star C_h control0 t
  have htest :
      ∫ z in E,
          ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
            rate rewards C_star C_h control0 t z ∂μ ≤
        ∫ z in E,
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ := by
    calc
      _ = ∫ z in E,
            μ[ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
                rate rewards C_star C_h control0 t | H (t.val + 1)] z ∂μ := by
          symm
          exact setIntegral_condExp
            ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
              (t.val + 1)) hfInt hE
      _ ≤ ∫ z in E,
            (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn hgInt.integrableOn hcond
  have hSentinel_eq : ∀ z,
      ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
        rate rewards C_star C_h t z =
      ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
        rate rewards C_star C_h control0 t z := by
    intro z
    rw [ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel_eq_pending_mask
      rate rewards C_star C_h t z]
    rfl
  have hSentinel_supported : ∀ z,
      ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
        rate rewards C_star C_h control0 t z =
      A.indicator (fun z =>
        ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
          rate rewards C_star C_h control0 t z) z := by
    intro z
    by_cases hp : (P t.val z).Nonempty
    · simp [Set.indicator, A, hp]
    · simp [Set.indicator, A, hp,
        ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel]
  have hWeight_supported : ∀ z,
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z =
        A.indicator (fun z =>
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z) z := by
    intro z
    by_cases hp : (P t.val z).Nonempty <;> simp [Set.indicator, A, hp]
  have hleft :
      ∫ z in B,
          ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
            rate rewards C_star C_h t z ∂μ =
        ∫ z in E,
          ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
            rate rewards C_star C_h control0 t z ∂μ := by
    calc
      _ = ∫ z in B,
            ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
              rate rewards C_star C_h control0 t z ∂μ := by
          apply setIntegral_congr_fun hFAmbient
          intro z _
          exact hSentinel_eq z
      _ = ∫ z in B, A.indicator (fun z =>
            ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
              rate rewards C_star C_h control0 t z) z ∂μ := by
          apply setIntegral_congr_fun hFAmbient
          intro z _
          exact hSentinel_supported z
      _ = ∫ z in E,
            ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedSentinel
              rate rewards C_star C_h control0 t z ∂μ := by
          simpa [E] using
            (setIntegral_indicator hAAmbient)
  have hright :
      ∫ z in B,
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ =
        ∫ z in E,
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ := by
    calc
      _ = ∫ z in B, A.indicator (fun z =>
            (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z) z ∂μ := by
          apply setIntegral_congr_fun hFAmbient
          intro z _
          exact hWeight_supported z
      _ = ∫ z in E,
            (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ := by
          simpa [E] using
            (setIntegral_indicator hAAmbient)
  rw [hleft, hright]
  exact htest

/-- Set-integral form of the actual first-release signed conditional cost
bound, valid for every set measurable at the actual phase start. -/
theorem actual_first_release_signed_cost_setIntegral_bound
    (B : Set (Source p)) (hB : MeasurableSet[Fσ] B) :
    ∫ z in B,
        ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
          rate rewards C_star C_h z ∂μ ≤
      (2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
          (Real.log ((p.m : ℝ) - 1) + 1)) * Measure.real μ B := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let hSigmaStop :=
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0
  have hBambient : MeasurableSet B :=
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H sigma hSigmaStop) B hB
  have hJsum :
      ∫ z in B,
          ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
            rate rewards C_star C_h z ∂μ =
        ∑ t : Fin p.T,
          ∫ z in B,
            ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
              rate rewards C_star C_h t z ∂μ := by
    unfold ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
    rw [integral_finsetSum]
    intro t ht
    exact (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep_integrable
      rate rewards C_star C_h control0 t).integrableOn
  have hStepBound (t : Fin p.T) :
      ∫ z in B,
          ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
            rate rewards C_star C_h t z ∂μ ≤
        ∫ z in B, followerStepTotal rate rewards C_star C_h control0 t.val z ∂μ +
          ∫ z in B,
            ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
              rate rewards C_star C_h t z ∂μ := by
    have hDataInt := follower_step_total_integrable
      rate rewards C_star C_h control0 t.val t.isLt
    have hSentInt :=
      ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel_integrable
        rate rewards C_star C_h control0 t
    have hpoint : ∀ z : Source p,
        ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
            rate rewards C_star C_h t z ≤
          followerStepTotal rate rewards C_star C_h control0 t.val z +
            ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
              rate rewards C_star C_h t z := by
      intro z
      calc
        _ ≤ (∑ i ∈ P t.val z, chi i t.val z) +
              ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
                rate rewards C_star C_h t z :=
          (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.actual_first_release_calendar_signed_bound
            rate rewards C_star C_h control0 t z).1
        _ = _ := by rw [followerStepTotal_eq_pending_sum]
    calc
      _ ≤ ∫ z in B,
            (fun z => followerStepTotal rate rewards C_star C_h control0 t.val z +
              ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
                rate rewards C_star C_h t z) z ∂μ :=
          setIntegral_mono_ae
            (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep_integrable
              rate rewards C_star C_h control0 t).integrableOn
            (hDataInt.add hSentInt).integrableOn
            (ae_of_all μ hpoint)
      _ = _ := integral_add hDataInt.integrableOn hSentInt.integrableOn
  have hSentinelBound (t : Fin p.T) :=
    stopped_sentinel_setIntegral_bound rate rewards C_star C_h control0 B hB t
  have hDataSum :
      (∑ t : Fin p.T,
        ∫ z in B, followerStepTotal rate rewards C_star C_h control0 t.val z ∂μ) =
      ∑ i : Fin (p.m - 1),
        ∫ z in B,
          actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ := by
    classical
    calc
      _ = ∑ t : Fin p.T, ∑ i : Fin (p.m - 1),
            ∫ z in B, followerStepTerm rate rewards C_star C_h control0 i t.val z ∂μ := by
          apply Finset.sum_congr rfl
          intro t ht
          exact follower_step_total_setIntegral rate rewards C_star C_h control0 B
            t.val t.isLt
      _ = ∑ i : Fin (p.m - 1), ∑ t : Fin p.T,
            ∫ z in B, followerStepTerm rate rewards C_star C_h control0 i t.val z ∂μ :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (follower_charge_setIntegral_eq_round_sum
            rate rewards C_star C_h control0 B hBambient i).symm
  have hAuxSum :
      (∑ t : Fin p.T,
        ∫ z in B,
          (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ) =
      ∫ z in B,
        actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z ∂μ := by
    classical
    calc
      _ = ∫ z in B,
            (fun z : Source p =>
              ∑ t : Fin p.T,
                (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z) z ∂μ := by
          symm
          rw [integral_finsetSum]
          intro t ht
          exact
            (ReferenceFirstLiveStoppedReleaseSentinelBound.pendingMaskedAuxiliaryWeight_integrable
              rate rewards C_star C_h control0 t).integrableOn
      _ = ∫ z in B,
            actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z ∂μ := by
          apply setIntegral_congr_fun hBambient
          intro z _
          exact auxiliary_mask_sum_eq_actual rate rewards C_star C_h control0 z
  have hIntegratedAccounting :
      ∫ z in B,
          ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
            rate rewards C_star C_h z ∂μ ≤
        (∑ i : Fin (p.m - 1),
          ∫ z in B,
            actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ) +
          ∫ z in B,
            actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z ∂μ := by
    calc
      _ = ∑ t : Fin p.T,
            ∫ z in B,
              ReferenceFirstLiveStoppedReleaseCalendarSignedCost.signedStep
                rate rewards C_star C_h t z ∂μ := hJsum
      _ ≤ ∑ t : Fin p.T,
            (∫ z in B, followerStepTotal rate rewards C_star C_h control0 t.val z ∂μ +
              ∫ z in B,
                ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
                  rate rewards C_star C_h t z ∂μ) :=
          Finset.sum_le_sum fun t _ => hStepBound t
      _ = (∑ t : Fin p.T,
            ∫ z in B, followerStepTotal rate rewards C_star C_h control0 t.val z ∂μ) +
          ∑ t : Fin p.T,
            ∫ z in B,
              ReferenceFirstLiveStoppedReleaseCalendarSignedCost.stoppedSentinel
                rate rewards C_star C_h t z ∂μ := by
          rw [Finset.sum_add_distrib]
      _ ≤ (∑ t : Fin p.T,
            ∫ z in B, followerStepTotal rate rewards C_star C_h control0 t.val z ∂μ) +
          ∑ t : Fin p.T,
            ∫ z in B,
              (if (P t.val z).Nonempty then (1 : ℝ) else 0) * omega t.val z ∂μ :=
          add_le_add le_rfl (Finset.sum_le_sum fun t _ => hSentinelBound t)
      _ = _ := by rw [hDataSum, hAuxSum]
  let d : ℕ := p.m - 1
  have hdcast : (d : ℝ) = (p.m : ℝ) - 1 := by
    dsimp [d]
    rw [Nat.cast_sub (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)]
    norm_num
  have hDataBounds :
      ∀ i : Fin (p.m - 1),
        ∫ z in B,
          actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ ≤
        2 * (p.K : ℝ) * Measure.real μ B := by
    intro i
    have hInt := actual_first_release_follower_charge_integrable
      rate rewards C_star C_h control0 i
    have hCond :=
      ReferenceFirstLiveStoppedReleaseWaiting.data_charge_condExp_bound
        rate rewards C_star C_h control0 i
    calc
      _ = ∫ z in B,
            μ[actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i | Fσ] z ∂μ := by
          symm
          exact setIntegral_condExp
            (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H sigma hSigmaStop)
            hInt hB
      _ ≤ ∫ z in B, (fun _ : Source p => 2 * (p.K : ℝ)) z ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn
            (integrable_const _).integrableOn hCond
      _ = 2 * (p.K : ℝ) * Measure.real μ B := by
          rw [setIntegral_const]
          simp [smul_eq_mul, mul_comm]
  have hAuxBound :
      ∫ z in B,
          actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z ∂μ ≤
        (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
          (Real.log ((p.m : ℝ) - 1) + 1) * Measure.real μ B := by
    have hInt := actual_first_release_auxiliary_charge_integrable
      rate rewards C_star C_h control0
    have hCond :=
      ReferenceFirstLiveStoppedReleaseWaiting.up_totalCharge_condExp_bound
        rate rewards C_star C_h control0
    calc
      _ = ∫ z in B,
            μ[actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 | Fσ] z ∂μ := by
          symm
          exact setIntegral_condExp
            (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H sigma hSigmaStop)
            hInt hB
      _ ≤ ∫ z in B,
            (fun _ : Source p =>
              12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1)) *
                (Real.log ((p.m : ℝ) - 1) + 1)) z ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn
            (integrable_const _).integrableOn hCond
      _ = (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
            (Real.log ((p.m : ℝ) - 1) + 1) * Measure.real μ B := by
          rw [setIntegral_const]
          simp [smul_eq_mul, mul_comm, mul_assoc]
  have hSumDataBound :
      (∑ i : Fin (p.m - 1),
        ∫ z in B,
          actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ) ≤
        (2 * ((p.m : ℝ) - 1) * (p.K : ℝ)) * Measure.real μ B := by
    calc
      _ ≤ ∑ _i : Fin (p.m - 1), 2 * (p.K : ℝ) * Measure.real μ B :=
        Finset.sum_le_sum fun i _ => hDataBounds i
      _ = (2 * ((p.m : ℝ) - 1) * (p.K : ℝ)) * Measure.real μ B := by
        have hcastNat : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
          simpa [d] using hdcast
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hcastNat]
        ring
  calc
    _ ≤
        (∑ i : Fin (p.m - 1),
          ∫ z in B,
            actualFirstReleaseFollowerCharge rate rewards C_star C_h control0 i z ∂μ) +
          ∫ z in B,
            actualFirstReleaseAuxiliaryCharge rate rewards C_star C_h control0 z ∂μ :=
      hIntegratedAccounting
    _ ≤ (2 * ((p.m : ℝ) - 1) * (p.K : ℝ)) * Measure.real μ B +
          (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
            (Real.log ((p.m : ℝ) - 1) + 1) * Measure.real μ B :=
      add_le_add hSumDataBound hAuxBound
    _ = _ := by ring

/-- Almost-everywhere conditional bound for the actual first-release signed
cost, using the original sigma, reward table, source law, and phase-start field. -/
theorem actual_first_release_signed_cost_condExp_bound :
    μ[ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
        rate rewards C_star C_h | Fσ] ≤ᵐ[μ]
      fun _ =>
        2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
          (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
            (Real.log ((p.m : ℝ) - 1) + 1) := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le μ Fσ
    (PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le H sigma
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
        rate rewards C_star C_h control0))
    (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost
      rate rewards C_star C_h)
    (2 * ((p.m : ℝ) - 1) * (p.K : ℝ) +
      (12 * ((p.m : ℝ) - 1) * (p.K : ℝ) / (1 - Real.exp (-1))) *
        (Real.log ((p.m : ℝ) - 1) + 1))
    (ReferenceFirstLiveStoppedReleaseCalendarSignedCost.totalSignedCost_integrable
      rate rewards C_star C_h control0)).1
    (actual_first_release_signed_cost_setIntegral_bound
      rate rewards C_star C_h control0)

end Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

end
