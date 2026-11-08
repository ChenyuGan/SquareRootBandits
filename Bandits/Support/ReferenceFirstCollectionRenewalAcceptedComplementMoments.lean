/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual first-renewal accepted complement moments

The literal actual second-source incoming queue determines whether the
complement estimator is stopped before this renewal update. On the existing
finite unnormalized pair law, actual insertion identifies that strict-past
test almost everywhere with the retained first-source field. The recorder
and queue identities below consume the same successful renewal call.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments

abbrev Params := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Source {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
abbrev Pair {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
abbrev RetainedCoordinates (p : Params) :=
  ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p

variable {p : Params}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : TimeControl p)

local instance sourceInputMeasurableSpace (p : Params) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" => Pair rate rewards C_star C_h u t
local notation "Z" => Source rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "R" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R
  (inferInstance : MeasurableSpace (RetainedCoordinates p))

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- The actual first-renewal complement estimate, stopped by the incoming
queue flag of the actual second source before the current update. -/
def acceptedA (j : Fin p.K) (b : B) : ℝ :=
  if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow then 0
  else ReferenceFirstCollectionRenewalComplementMoments.a
    rate rewards C_star C_h u t b j

private theorem measurable_actualIncomingOverflow :
    Measurable (fun b : B =>
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow) := by
  have hread : Measurable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t b.2) :=
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t).comp measurable_snd
  change Measurable (fun b : B =>
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t b.2).2.1)
  exact measurable_fst.comp (measurable_snd.comp hread)

/-- Ambient Borel measurability of the actual stopped estimator. -/
theorem measurable_acceptedA (j : Fin p.K) :
    Measurable (fun b : B => acceptedA rate rewards C_star C_h u t j b) := by
  have hstop : MeasurableSet {b : B |
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = true} :=
    (measurable_actualIncomingOverflow rate rewards C_star C_h u t)
      (MeasurableSet.singleton true)
  change Measurable (fun b : B =>
    if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow then 0
    else ReferenceFirstCollectionRenewalComplementMoments.a
      rate rewards C_star C_h u t b j)
  exact Measurable.ite hstop measurable_const
    (ReferenceFirstCollectionRenewalComplementMoments.measurable_a
      rate rewards C_star C_h u t j)

/-- On the same pair law, actual insertion identifies the actual second
source's overflow flag with the retained first-source representative. -/
private theorem ae_actual_overflow_eq_retained :
    ∀ᵐ b : B ∂mu,
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
        rate rewards C_star C_h u t control0 b).overflow := by
  filter_upwards [
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
      rate rewards C_star C_h u t control0] with b hb
  exact congrArg (fun x => x.2.1) hb

/-- The actual stopped estimator is the retained-field indicator times the
original complement readout, almost everywhere under the unchanged law. -/
theorem ae_acceptedA_eq_retained_indicator (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      acceptedA rate rewards C_star C_h u t j b =
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.a
            rate rewards C_star C_h u t b j) b := by
  filter_upwards [
    ae_actual_overflow_eq_retained rate rewards C_star C_h u t control0] with b hb
  change (if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow then 0 else _ ) = _
  by_cases ho : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = true
  · have hnot : b ∉ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0 := by
      change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
        rate rewards C_star C_h u t control0 b).overflow ≠ false
      rw [← hb, ho]
      decide
    simp [ho, hnot]
  · have hfalse : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = false := by
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2).overflow <;> simp_all
    have hin : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0 := by
      change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
        rate rewards C_star C_h u t control0 b).overflow = false
      rw [← hb, hfalse]
    simp [hfalse, hin]

/-- The actual accepted estimator is pointwise nonnegative and bounded by the
source's canonical inverse recording floor. -/
theorem acceptedA_bounds (b : B) (j : Fin p.K) :
    0 ≤ acceptedA rate rewards C_star C_h u t j b ∧
      acceptedA rate rewards C_star C_h u t j b ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  by_cases ho : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow
  · have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
    constructor
    · simp [acceptedA, ho]
    · simp [acceptedA, ho]
      positivity
  · simpa [acceptedA, ho] using
      (show 0 ≤ ReferenceFirstCollectionRenewalComplementMoments.a
          rate rewards C_star C_h u t b j ∧
        ReferenceFirstCollectionRenewalComplementMoments.a
          rate rewards C_star C_h u t b j ≤
            1 / CanonicalRecordingRates.beta p rate.eta.val from
        ⟨(ReferenceFirstCollectionRenewalComplementMoments.uniform_readout_bounds
            rate rewards C_star C_h u t b j).1,
          (ReferenceFirstCollectionRenewalComplementMoments.uniform_readout_bounds
            rate rewards C_star C_h u t b j).2.1⟩)

private theorem integrable_of_norm_le_const {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) : Integrable f ν := by
  have hconst : Integrable (fun _ : α => C) ν := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa using hbound x

/-- The actual first moment is integrable on the original finite pair law. -/
theorem integrable_acceptedA (j : Fin p.K) :
    Integrable (fun b : B => acceptedA rate rewards C_star C_h u t j b) mu := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  apply integrable_of_norm_le_const (ν := mu)
    (measurable_acceptedA rate rewards C_star C_h u t j)
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
  intro b
  have hb := acceptedA_bounds rate rewards C_star C_h u t b j
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

/-- The square of the actual first moment is integrable on the same law. -/
theorem integrable_acceptedA_sq (j : Fin p.K) :
    Integrable (fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) mu := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hm := (measurable_acceptedA rate rewards C_star C_h u t j).pow_const 2
  apply integrable_of_norm_le_const (ν := mu) hm
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
  intro b
  have hb := acceptedA_bounds rate rewards C_star C_h u t b j
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hsq := mul_le_mul hb.2 hb.2 hb.1
    (div_nonneg (by norm_num) hbeta.le)
  simpa [pow_two] using hsq

private def retainedIndicator : B → ℝ :=
  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0).indicator (fun _ => (1 : ℝ))

/-- The retained event and both coefficient readouts are measurable in the
exact existing comap field. -/
theorem measurable_retained_coefficient_indicators (j : Fin p.K) :
    Measurable[F_R] (fun b : B =>
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
        (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
          rate rewards C_star C_h u t b j) b) ∧
    Measurable[F_R] (fun b : B =>
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
        (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
          rate rewards C_star C_h u t b j) b) := by
  have hG := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hc := ReferenceFirstCollectionRenewalComplementMoments.measurable_retained_readouts
    rate rewards C_star C_h u t control0 j
  exact ⟨hc.2.1.indicator hG, hc.2.2.indicator hG⟩

private theorem retainedIndicator_measurable : Measurable[F_R]
    (retainedIndicator rate rewards C_star C_h u t control0) := by
  exact measurable_const.indicator
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
      rate rewards C_star C_h u t control0)

private theorem retainedIndicator_integrable :
    Integrable (retainedIndicator rate rewards C_star C_h u t control0) mu := by
  apply integrable_of_norm_le_const (ν := mu)
    ((retainedIndicator_measurable rate rewards C_star C_h u t control0).mono
      (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
        rate rewards C_star C_h u t control0) le_rfl) 1
  intro b
  by_cases hb : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
      rate rewards C_star C_h u t control0 <;>
    simp [retainedIndicator, hb]

private theorem retainedIndicator_stronglyMeasurable :
    StronglyMeasurable[F_R]
      (retainedIndicator rate rewards C_star C_h u t control0) :=
  (retainedIndicator_measurable rate rewards C_star C_h u t control0).stronglyMeasurable

/-- First conditional moment on the exact retained field and same unnormalized
pair law. -/
theorem condExp_acceptedA (j : Fin p.K) :
    mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] =ᵐ[mu]
      (fun b => (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
            rate rewards C_star C_h u t b j) b) := by
  let q := fun b : B => ReferenceFirstCollectionRenewalComplementMoments.a
    rate rewards C_star C_h u t b j
  let g := retainedIndicator rate rewards C_star C_h u t control0
  have haInt := ReferenceFirstCollectionRenewalComplementMoments.integrable_readouts
    rate rewards C_star C_h u t j
  have hprod : Integrable (fun b : B => g b * q b) mu := by
    have hEq : (fun b : B => g b * q b) =ᵐ[mu]
        (fun b => acceptedA rate rewards C_star C_h u t j b) := by
      filter_upwards [ae_acceptedA_eq_retained_indicator
        rate rewards C_star C_h u t control0 j] with b hb
      simpa [g, q, retainedIndicator, Set.indicator] using hb.symm
    exact (integrable_acceptedA rate rewards C_star C_h u t j).congr hEq.symm
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (retainedIndicator_stronglyMeasurable rate rewards C_star C_h u t control0)
    hprod haInt.1
  have hq := ReferenceFirstCollectionRenewalComplementMoments.condExp_first_moment
    rate rewards C_star C_h u t control0 j
  calc
    mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] =ᵐ[mu]
        mu[(fun b : B => g b * q b) | F_R] := by
      exact condExp_congr_ae (by
        filter_upwards [ae_acceptedA_eq_retained_indicator
          rate rewards C_star C_h u t control0 j] with b hb
        simpa [g, q, retainedIndicator, Set.indicator] using hb)
    _ =ᵐ[mu] (fun b => g b * mu[q | F_R] b) := hpull
    _ =ᵐ[mu] (fun b =>
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
            rate rewards C_star C_h u t b j) b) := by
      filter_upwards [hq] with b hb
      rw [hb]
      simp [g, retainedIndicator, Set.indicator]

/-- Conditional square moment on the exact retained field and same
unnormalized pair law. -/
theorem condExp_acceptedA_sq (j : Fin p.K) :
    mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] =ᵐ[mu]
      (fun b => (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
            rate rewards C_star C_h u t b j) b) := by
  let q := fun b : B =>
    (ReferenceFirstCollectionRenewalComplementMoments.a
      rate rewards C_star C_h u t b j) ^ 2
  let g := retainedIndicator rate rewards C_star C_h u t control0
  have haInt := ReferenceFirstCollectionRenewalComplementMoments.integrable_readouts
    rate rewards C_star C_h u t j
  have hprod : Integrable (fun b : B => g b * q b) mu := by
    have hEq : (fun b : B => g b * q b) =ᵐ[mu]
        (fun b => (acceptedA rate rewards C_star C_h u t j b) ^ 2) := by
      filter_upwards [ae_acceptedA_eq_retained_indicator
        rate rewards C_star C_h u t control0 j] with b hb
      rw [hb]
      simp [g, q, retainedIndicator, Set.indicator]
    exact (integrable_acceptedA_sq rate rewards C_star C_h u t j).congr hEq.symm
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (retainedIndicator_stronglyMeasurable rate rewards C_star C_h u t control0)
    hprod haInt.2.1
  have hq := ReferenceFirstCollectionRenewalComplementMoments.condExp_second_moment
    rate rewards C_star C_h u t control0 j
  calc
    mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] =ᵐ[mu]
        mu[(fun b : B => g b * q b) | F_R] := by
      exact condExp_congr_ae (by
        filter_upwards [ae_acceptedA_eq_retained_indicator
          rate rewards C_star C_h u t control0 j] with b hb
        rw [hb]
        simp [g, q, retainedIndicator, Set.indicator])
    _ =ᵐ[mu] (fun b => g b * mu[q | F_R] b) := hpull
    _ =ᵐ[mu] (fun b =>
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
            rate rewards C_star C_h u t b j) b) := by
      filter_upwards [hq] with b hb
      rw [hb]
      simp [g, retainedIndicator, Set.indicator]

/-- Both coefficient indicators are integrable on the original finite pair
law, and are measurable in its exact retained comap field. -/
theorem integrable_retained_coefficient_indicators (j : Fin p.K) :
    Integrable (fun b : B =>
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
        (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
          rate rewards C_star C_h u t b j) b) mu ∧
    Integrable (fun b : B =>
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
        (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
          rate rewards C_star C_h u t b j) b) mu := by
  have hmeas := measurable_retained_coefficient_indicators
    rate rewards C_star C_h u t control0 j
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  refine ⟨?_, ?_⟩
  · apply integrable_of_norm_le_const (ν := mu) (hmeas.1.mono hdom le_rfl) 1
    intro b
    by_cases hb : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0
    · have hc := (ReferenceFirstCollectionRenewalComplementMoments.c1_bounds
          rate rewards C_star C_h u t b j)
      have hchi : 0 ≤ ReferenceFirstCollectionRenewalComplementMoments.chi
          rate rewards C_star C_h u t b j ∧
          ReferenceFirstCollectionRenewalComplementMoments.chi
            rate rewards C_star C_h u t b j ≤ 1 := by
        unfold ReferenceFirstCollectionRenewalComplementMoments.chi
        split <;> norm_num
      have hr := RealRewardGridCount.realRewardGridValue_mem_Icc
        (D p) (D_pos p) (rewards t j)
      have htop : ReferenceFirstCollectionRenewalComplementMoments.c1
          rate rewards C_star C_h u t b j ≤ 1 := by
        calc
          _ ≤ ReferenceFirstCollectionRenewalComplementMoments.chi
                rate rewards C_star C_h u t b j *
              ReferenceFirstCollectionRenewalComplementMoments.r rewards t j := hc.2.2
          _ ≤ 1 := by
            calc
              _ ≤ 1 * ReferenceFirstCollectionRenewalComplementMoments.r rewards t j :=
                mul_le_mul_of_nonneg_right hchi.2 hr.1
              _ ≤ 1 := by
                simpa [ReferenceFirstCollectionRenewalComplementMoments.r] using hr.2
      simp only [Set.indicator_of_mem hb]
      rw [Real.norm_of_nonneg hc.1]
      exact htop
    · simp [Set.indicator, hb]
  · apply integrable_of_norm_le_const (ν := mu) (hmeas.2.mono hdom le_rfl)
      (1 / CanonicalRecordingRates.beta p rate.eta.val)
    intro b
    by_cases hb : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0
    · have hc := (ReferenceFirstCollectionRenewalComplementMoments.c2_bounds
          rate rewards C_star C_h u t b j)
      have htop := (ReferenceFirstCollectionRenewalComplementMoments.uniform_readout_bounds
          rate rewards C_star C_h u t b j).2.2.2.2.2
      simp only [Set.indicator_of_mem hb]
      rw [Real.norm_of_nonneg hc.1]
      exact htop
    · simp [Set.indicator, hb]
      positivity

/-- First-moment equality on every measurable retained-coordinate cylinder
for the actual stopped estimator. -/
theorem first_moment_setIntegral (j : Fin p.K) (Hset : Set (RetainedCoordinates p))
    (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset},
        acceptedA rate rewards C_star C_h u t j b ∂mu =
      ∫ b in {b : B | R b ∈ Hset},
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
            rate rewards C_star C_h u t b j) b ∂mu := by
  let S : Set B := {b | R b ∈ Hset}
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hS : MeasurableSet[F_R] S := hHset.preimage (comap_measurable _)
  have hce := condExp_acceptedA rate rewards C_star C_h u t control0 j
  have hceS : ∀ᵐ b ∂mu, b ∈ S →
      mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] b =
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c1
            rate rewards C_star C_h u t b j) b :=
    hce.mono fun b hb _ => hb
  calc
    _ = ∫ b in S,
        mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] b ∂mu :=
      (setIntegral_condExp hdom
        (integrable_acceptedA rate rewards C_star C_h u t j) hS).symm
    _ = _ := setIntegral_congr_ae (hdom _ hS) hceS

/-- Square-moment equality on every measurable retained-coordinate cylinder
for the actual stopped estimator. -/
theorem second_moment_setIntegral (j : Fin p.K) (Hset : Set (RetainedCoordinates p))
    (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset},
        (acceptedA rate rewards C_star C_h u t j b) ^ 2 ∂mu =
      ∫ b in {b : B | R b ∈ Hset},
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
            rate rewards C_star C_h u t b j) b ∂mu := by
  let S : Set B := {b | R b ∈ Hset}
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hS : MeasurableSet[F_R] S := hHset.preimage (comap_measurable _)
  have hce := condExp_acceptedA_sq rate rewards C_star C_h u t control0 j
  have hceS : ∀ᵐ b ∂mu, b ∈ S →
      mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] b =
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.c2
            rate rewards C_star C_h u t b j) b :=
    hce.mono fun b hb _ => hb
  calc
    _ = ∫ b in S,
        mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] b ∂mu :=
      (setIntegral_condExp hdom
        (integrable_acceptedA_sq rate rewards C_star C_h u t j) hS).symm
    _ = _ := setIntegral_congr_ae (hdom _ hS) hceS

/-- First conditional bounds retain every source coefficient and the
canonical denominator. -/
theorem condExp_acceptedA_bounds (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      0 ≤ mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] b ∧
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.chi
              rate rewards C_star C_h u t b j *
            (ReferenceFirstCollectionRenewalComplementMoments.r rewards t j -
              ReferenceFirstCollectionRenewalComplementMoments.xi
                rate rewards C_star C_h u t b j /
                (rate.eta.val * (D p : ℝ)))) b ≤
        mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] b ∧
      mu[(fun b : B => acceptedA rate rewards C_star C_h u t j b) | F_R] b ≤
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.chi
              rate rewards C_star C_h u t b j *
            ReferenceFirstCollectionRenewalComplementMoments.r rewards t j) b := by
  have hce := condExp_acceptedA rate rewards C_star C_h u t control0 j
  filter_upwards [hce] with b hce
  by_cases hg : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
      rate rewards C_star C_h u t control0
  · have hc := ReferenceFirstCollectionRenewalComplementMoments.c1_bounds
      rate rewards C_star C_h u t b j
    simp only [Set.indicator_of_mem hg] at hce ⊢
    rw [hce]
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  · rw [hce]
    simp [Set.indicator, hg]

/-- Square conditional bounds retain the complement rate and xi denominator. -/
theorem condExp_acceptedA_sq_bounds (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      0 ≤ mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] b ∧
      mu[(fun b : B => (acceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] b ≤
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => ReferenceFirstCollectionRenewalComplementMoments.chi
              rate rewards C_star C_h u t b j *
            (ReferenceFirstCollectionRenewalComplementMoments.r rewards t j) ^ 2 /
              ReferenceFirstCollectionRenewalComplementMoments.xi
                rate rewards C_star C_h u t b j) b := by
  have hce := condExp_acceptedA_sq rate rewards C_star C_h u t control0 j
  filter_upwards [hce] with b hce
  by_cases hg : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
      rate rewards C_star C_h u t control0
  · have hc := ReferenceFirstCollectionRenewalComplementMoments.c2_bounds
      rate rewards C_star C_h u t b j
    simp only [Set.indicator_of_mem hg] at hce ⊢
    rw [hce]
    exact hc
  · rw [hce]
    simp [Set.indicator, hg]

/-- The no-overflow retained event is exactly the strict all-prefix test on
the same actual second source. This tests every previous prefix, including
the first overflow update, rather than only the drained endpoint backlog. -/
theorem ae_actual_strict_past_identification :
    ∀ᵐ b : B ∂mu,
      b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0 ↔
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
            rate rewards C_star C_h u t b.2 <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
              rate rewards C_star C_h u t b.2) :=
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_G_R_iff_firstOverflow
    rate rewards C_star C_h u t control0

abbrev ActualCall (b : B) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
    rate rewards C_star C_h u t b.2

/-- The literal numerical queue input associated with the actual successful
renewal recorder. It uses its actual gate arm, enables the successful renewal,
keeps the whole fixed reward vector, and uses canonical xi at the same
reconstructed current weight. -/
def actualNumericalCell (b : B) (d : ActualCall rate rewards C_star C_h u t b)
    (recording : CoordinatorRecordingOperation.Output p) :
    RecordedQueueRun.RoundInput p.K where
  enabled := true
  recordedArm := recording.gateArm
  reward := fun j => ReferenceFirstCollectionRenewalComplementMoments.r rewards t j
  rate := fun j => CanonicalRecordingRates.xi p rate.eta.val
    (AssignmentScoreReconstruction.currentWeight d.out) j
  reward_nonneg := by
    intro j
    exact (RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards t j)).1
  reward_le_one := by
    intro j
    exact (RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards t j)).2
  rate_pos := by
    intro j
    exact CanonicalRecordingRates.xi_pos p rate.eta.property
      (AssignmentScoreReconstruction.currentWeight d.out) j

private theorem actualCell_quantized_arrival_of_recorded
    (b : B) (d : ActualCall rate rewards C_star C_h u t b)
    (recording : CoordinatorRecordingOperation.Output p)
    (hweight : ReferenceFirstCollectionRenewalComplementMoments.v
        rate rewards C_star C_h u t b =
      AssignmentScoreReconstruction.currentWeight d.out)
    (j : Fin p.K) (hrecorded : recording.gateArm = some j) :
    (RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (actualNumericalCell rate rewards C_star C_h u t b d recording) j : ℝ) =
      ReferenceFirstCollectionRenewalComplementMoments.q
        rate rewards C_star C_h u t b j * (rate.eta.val * (D p : ℝ)) := by
  have hcellArm :
      (actualNumericalCell rate rewards C_star C_h u t b d recording).recordedArm =
        some j := by
    exact hrecorded
  rw [RecordedQueueRun.quantizedArrival_eq_floor
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (actualNumericalCell rate rewards C_star C_h u t b d recording) j hcellArm]
  have hxi :
      (actualNumericalCell rate rewards C_star C_h u t b d recording).rate j =
        ReferenceFirstCollectionRenewalComplementMoments.xi
          rate rewards C_star C_h u t b j := by
    change CanonicalRecordingRates.xi p rate.eta.val
        (AssignmentScoreReconstruction.currentWeight d.out) j =
      CanonicalRecordingRates.xi p rate.eta.val
        (ReferenceFirstCollectionRenewalComplementMoments.v
          rate rewards C_star C_h u t b) j
    exact (congrArg (fun w : Fin p.K → ℝ =>
      CanonicalRecordingRates.xi p rate.eta.val w j) hweight).symm
  have hr :
      (actualNumericalCell rate rewards C_star C_h u t b d recording).reward j =
        ReferenceFirstCollectionRenewalComplementMoments.r rewards t j := rfl
  have harg :
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) *
          (actualNumericalCell rate rewards C_star C_h u t b d recording).reward j /
            (actualNumericalCell rate rewards C_star C_h u t b d recording).rate j =
        (D p : ℝ) * rate.eta.val *
          ReferenceFirstCollectionRenewalComplementMoments.r rewards t j /
            ReferenceFirstCollectionRenewalComplementMoments.xi
              rate rewards C_star C_h u t b j := by
    rw [ReferenceFirstLaunchNumericalCell.queueParameters, hr, hxi]
    rw [rate.n_scale]
    ring
  rw [ReferenceFirstCollectionRenewalComplementMoments.q,
    QuantizedRecordingMoments.quantizedValue,
    QuantizedRecordingMoments.quantizedIndex]
  rw [harg]
  exact (div_mul_cancel₀ _
    (ne_of_gt (mul_pos rate.eta.property (Nat.cast_pos.mpr (D_pos p))))).symm

private theorem acceptedA_eq_actualAcceptedRecord
    (b : B) (d : ActualCall rate rewards C_star C_h u t b)
    (recording : CoordinatorRecordingOperation.Output p)
    (hweight : ReferenceFirstCollectionRenewalComplementMoments.v
        rate rewards C_star C_h u t b =
      AssignmentScoreReconstruction.currentWeight d.out)
    (hgate : ∀ j : Fin p.K, recording.gateArm = some j ↔
      b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
        rate rewards C_star C_h u t j)
    (hestimate : ∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalComplementMoments.a
          rate rewards C_star C_h u t b j =
        if recording.gateArm = some j then
          (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ)) else 0)
    (j : Fin p.K) :
    acceptedA rate rewards C_star C_h u t j b =
      ((RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2)
        (actualNumericalCell rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
          (rate.eta.val * (D p : ℝ)) := by
  let state := ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t b.2
  let cell := actualNumericalCell rate rewards C_star C_h u t b d recording
  have hden : 0 < rate.eta.val * (D p : ℝ) :=
    mul_pos rate.eta.property (Nat.cast_pos.mpr (D_pos p))
  cases hflag : state.overflow with
  | true =>
      simp [acceptedA, state, hflag, RecordedQueueRun.acceptedRecord]
  | false =>
      by_cases hrecorded : recording.gateArm = some j
      · have hmem := (hgate j).mp hrecorded
        have haq : ReferenceFirstCollectionRenewalComplementMoments.a
            rate rewards C_star C_h u t b j =
            ReferenceFirstCollectionRenewalComplementMoments.q
              rate rewards C_star C_h u t b j := by
          simp [ReferenceFirstCollectionRenewalComplementMoments.a, hmem]
        have hraw : ReferenceFirstCollectionRenewalComplementMoments.q
            rate rewards C_star C_h u t b j =
            (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ)) := by
          calc
            _ = ReferenceFirstCollectionRenewalComplementMoments.a
                rate rewards C_star C_h u t b j := haq.symm
            _ = _ := by simpa [hrecorded] using hestimate j
        have harrival := actualCell_quantized_arrival_of_recorded
          rate rewards C_star C_h u t b d recording hweight j hrecorded
        have harrivalRaw :
            (RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j : ℝ) =
              recording.rawArrival := by
          calc
            _ = ReferenceFirstCollectionRenewalComplementMoments.q
                rate rewards C_star C_h u t b j * (rate.eta.val * (D p : ℝ)) := harrival
            _ = _ := by
              rw [hraw]
              exact div_mul_cancel₀ _ (ne_of_gt hden)
        have haccepted :
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell j).2 =
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j := by
          simp [RecordedQueueRun.acceptedRecord, state, cell,
            actualNumericalCell, hflag]
        calc
          acceptedA rate rewards C_star C_h u t j b =
              ReferenceFirstCollectionRenewalComplementMoments.a
                rate rewards C_star C_h u t b j := by
            simp [acceptedA, state, hflag]
          _ = ReferenceFirstCollectionRenewalComplementMoments.q
                rate rewards C_star C_h u t b j := haq
          _ = (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ)) := hraw
          _ = ((RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell j).2 : ℝ) /
                (rate.eta.val * (D p : ℝ)) := by
            rw [haccepted, harrivalRaw]
      · have hnotmem : b ∉ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
            rate rewards C_star C_h u t j := by
          intro hmem
          exact hrecorded ((hgate j).mpr hmem)
        have hzero : ReferenceFirstCollectionRenewalComplementMoments.a
            rate rewards C_star C_h u t b j = 0 := by
          simpa [hrecorded] using hestimate j
        have hnoArrival : cell.recordedArm ≠ some j := by
          change recording.gateArm ≠ some j
          exact hrecorded
        have hzeroArrival :
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j = 0 :=
          RecordedQueueRun.quantizedArrival_eq_zero
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j hnoArrival
        have haccepted :
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell j).2 = 0 := by
          simpa [RecordedQueueRun.acceptedRecord, state, cell, hflag,
            actualNumericalCell] using hzeroArrival
        rw [haccepted]
        simp [acceptedA, state, hflag, hzero]

/-- On the same unnormalized pair law, the physical recorder and the
retained incoming queue use one actual renewal call and one actual record.
The same call supplies the canonical current weight, gate arm, DATA feedback,
and incoming queue registers. The current cell is accepted according to the
PREVIOUS overflow flag; a crossing caused by this cell remains its arrival. -/
theorem ae_actual_recorder_acceptedRecord_identity :
    ∀ᵐ b : B ∂mu,
      ∃ d : ActualCall rate rewards C_star C_h u t b,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2 ∧
          d.record.output.coordinator.recording = some recording ∧
          ReferenceFirstCollectionRenewalComplementMoments.v
              rate rewards C_star C_h u t b =
            AssignmentScoreReconstruction.currentWeight d.out ∧
          (∀ j : Fin p.K, recording.gateArm = some j ↔
            b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
              rate rewards C_star C_h u t j) ∧
          (∀ j : Fin p.K, recording.gateArm = some j →
            PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
                PublicDiscreteDraws.dataSlot ∧
            PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
                (d.record.input.row.2 d.record.input.time).1 =
              ActiveRoundActions.coordinator p.two_le_m ∧
            d.record.output.preparation.feedback.feedback
                (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
            d.record.output.preparation.coordinatorObservation = rewards t j ∧
            (d.record.output.preparation.feedback.observations
                (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) ∧
          ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
              rate rewards C_star C_h u t b.2).overflow = false ↔
            ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
                rate rewards C_star C_h u t b.2 <
              UnstoppedRecordedQueueComparison.firstOverflowPrefix
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                  rate rewards C_star C_h u t b.2)) ∧
          (∀ j : Fin p.K,
            acceptedA rate rewards C_star C_h u t j b =
              if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2).overflow then 0
              else if recording.gateArm = some j then
                (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ))
              else 0) ∧
          (∀ j : Fin p.K, b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
              rate rewards C_star C_h u t control0 →
            (AssignmentScoreReconstruction.sourceScore d.out j,
              AssignmentScoreReconstruction.initialQueue d.out j) =
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2).registers j) ∧
          (∀ j : Fin p.K,
            acceptedA rate rewards C_star C_h u t j b =
              ((RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2)
                (actualNumericalCell rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
                (rate.eta.val * (D p : ℝ))) := by
  filter_upwards [
    ReferenceFirstCollectionRenewalComplementMoments.ae_actual_recording_identification
      rate rewards C_star C_h u t,
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_actual_incoming_factor
      rate rewards C_star C_h u t control0,
    ReferenceFirstCollectionRenewalRecordingFeedback.ae_pairLaw_actual_recording_feedback
      rate rewards C_star C_h u t,
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_G_R_iff_firstOverflow
      rate rewards C_star C_h u t control0] with b hQ hP hN hStrict
  rcases hQ with ⟨dQ, recordingQ, hrecordingQ, hweightQ, hgateQ, hestimateQ⟩
  rcases hP with ⟨_, hincoming, d, hcallD, hregistersD⟩
  rcases hN with ⟨dN, consistent, output, hlocal, clockData, installed, selection,
    recordingN, serviced, hstart, hvector, hreconstruction, hsuccessful, hslow,
    hinSlow, hclock, hins, hanchor, hdispatch, hpreparation, hcoordinator,
    hpostChoice, hrun, hservice, hrecordingN, hstates, hlive, hpending, hu,
    hsigma, hclockU, hinstalledSigma, hpostFeedback⟩
  rcases hpostFeedback with ⟨hnotFrozen, hrawN, hfeedbackN⟩
  have hcallQ := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t b.2 dQ
  have hcallN := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t b.2 dN
  have hcallDQ : d.record = dQ.record := hcallD.trans hcallQ.symm
  have hcallDN : dN.record = d.record := hcallN.trans hcallD.symm
  have hrecD : d.record.output.coordinator.recording = some recordingQ := by
    exact (congrArg (fun r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate =>
      r.output.coordinator.recording) hcallDQ).trans hrecordingQ
  have hrecording_eq : recordingN = recordingQ := by
    apply Option.some.inj
    exact hrecordingN.symm.trans
      ((congrArg (fun r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate =>
        r.output.coordinator.recording) (hcallN.trans hcallQ.symm)).trans hrecordingQ)
  have hfeedback : ∀ j : Fin p.K, recordingQ.gateArm = some j →
      PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
          PublicDiscreteDraws.dataSlot ∧
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
          (d.record.input.row.2 d.record.input.time).1 =
        ActiveRoundActions.coordinator p.two_le_m ∧
      d.record.output.preparation.feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
      d.record.output.preparation.coordinatorObservation = rewards t j ∧
      (d.record.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j) := by
    intro j hj
    have hjN : recordingN.gateArm = some j := by simpa [hrecording_eq] using hj
    rcases hfeedbackN j hjN with ⟨hdata, hsource, _haction, _hslow, _hmask,
      _hcollision, hfb, hobs, hgrid⟩
    rw [hcallDN] at hdata hsource hfb hobs hgrid
    exact ⟨hdata, hsource, hfb, hobs, hgrid⟩
  have hweight : ReferenceFirstCollectionRenewalComplementMoments.v
      rate rewards C_star C_h u t b =
        AssignmentScoreReconstruction.currentWeight d.out := by
    have hselQ := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
      dQ.old _ dQ.instruction dQ.out dQ.reconstruction_eq dQ.renewal).1
    have hselD := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
      d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1
    have hparQ := congrArg Prod.snd dQ.parameter_eq
    have hparD := congrArg Prod.snd d.parameter_eq
    calc
      ReferenceFirstCollectionRenewalComplementMoments.v
          rate rewards C_star C_h u t b =
        AssignmentScoreReconstruction.currentWeight dQ.out := hweightQ
      _ = (LaterAssignmentStartMeasurability.selectedSamplerParameters
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u dQ.record.input dQ.old dQ.ledger dQ.saved).payload
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                rate u dQ.record.input dQ.old dQ.ledger dQ.saved) dQ.core.payload_n_eq)
            dQ.instruction dQ.out dQ.reconstruction_eq).2 := hselQ.symm
      _ = (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t b.2).2 := hparQ.symm
      _ = (LaterAssignmentStartMeasurability.selectedSamplerParameters
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u d.record.input d.old d.ledger d.saved).payload
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq)
            d.instruction d.out d.reconstruction_eq).2 := hparD
      _ = AssignmentScoreReconstruction.currentWeight d.out := hselD
  have hstrict : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false ↔
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
          rate rewards C_star C_h u t b.2 <
        UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t b.2) := by
    have hflag : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
        rate rewards C_star C_h u t control0 b).overflow :=
      congrArg (fun s : RecordedQueueRun.RunState p.K => s.overflow) hincoming
    calc
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2).overflow = false ↔
        b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0 := by
            rw [hflag]
            rfl
      _ ↔ ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
            rate rewards C_star C_h u t b.2 <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
              rate rewards C_star C_h u t b.2) := hStrict
  have hrawIdentity : ∀ j : Fin p.K,
      acceptedA rate rewards C_star C_h u t j b =
        if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t b.2).overflow then 0
        else if recordingQ.gateArm = some j then
          (recordingQ.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ)) else 0 := by
    intro j
    simp [acceptedA, hestimateQ j]
  refine ⟨d, recordingQ, hcallD, hrecD, hweight, hgateQ, hfeedback, hstrict,
    hrawIdentity, ?_, ?_⟩
  · intro j hG
    exact hregistersD hG j
  · intro j
    exact acceptedA_eq_actualAcceptedRecord rate rewards C_star C_h u t b d
      recordingQ hweight hgateQ hestimateQ j

end Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments

end
