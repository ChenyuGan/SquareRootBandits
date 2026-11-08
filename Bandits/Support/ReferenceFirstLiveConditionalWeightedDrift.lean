/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveQueueEnergyEnvelope

import Mathlib.Tactic

/-!
# First-live conditional weighted queue drift

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module conditions the accepted queue-energy envelope on the exact
current-control-erased prefix field and inherited, finite, unnormalized
first-live branch measure. It keeps the actual first crossing update and
records the canonical anchor-rate sum explicitly. The integrated estimate is
on that same branch measure; this module does not compare the rate sum with
`R`, identify the prefix field with manuscript history, or close a queue or
regret assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift

abbrev Parameters := ReferenceFirstLiveQueueEnergyEnvelope.Parameters
abbrev RateInput := ReferenceFirstLiveQueueEnergyEnvelope.RateInput
abbrev RewardTable := ReferenceFirstLiveQueueEnergyEnvelope.RewardTable
abbrev TimeControl := ReferenceFirstLiveQueueEnergyEnvelope.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
local notation "muPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
local notation "Fplus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
    rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
local notation "thetaBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
    rate rewards C_star C_h q t s hs control0
local notation "weightedBacklogBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialAfter" =>
  ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
    rate rewards C_star C_h q t s hs control0
local notation "backlogBefore" =>
  ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore
    rate rewards C_star C_h q t s hs control0
local notation "acceptedA" =>
  ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
    rate rewards C_star C_h q t s hs control0
local notation "markerRatePlus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
    rate rewards C_star C_h q t s hs control0
local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate
local notation "Bcap" => 1 / (32 * rate.eta.val)

local instance instFiniteBranchMeasure : IsFiniteMeasure muPlus :=
  ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
    rate rewards C_star C_h q t s hs control0

local instance instFinitePrefixTrim : IsFiniteMeasure
    ((muPlus).trim
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0)) :=
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
    rate rewards C_star C_h q t s hs control0

private theorem integrable_of_norm_le_uniform
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} {C : ℝ} (hf : Measurable f) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  have habs : |C| = C := abs_of_nonneg hC
  simpa only [Real.norm_eq_abs, habs] using hbound x

/-- The literal sum of the actual anchor rates weighted by the strict-past
inclusion marginals. The rates are the canonical rates on the inherited
source cylinders. -/
def markerRateWeightSum (z : Zplus) : ℝ :=
  ∑ j : Fin p.K, thetaBefore j z / markerRatePlus j z

/-- The canonical rate sum is measurable on the exact prefix field. -/
theorem measurable_markerRateWeightSum :
    Measurable[Fplus] (markerRateWeightSum rate rewards C_star C_h q t s hs control0) := by
  unfold markerRateWeightSum
  apply Finset.measurable_sum
  intro j hj
  exact (ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).div
    (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_markerRatePlus
      rate rewards C_star C_h q t s hs control0 j)

/-- The same rate sum is measurable in the ambient source-cylinder sigma
algebra. -/
theorem measurable_markerRateWeightSum_ambient :
    Measurable (markerRateWeightSum rate rewards C_star C_h q t s hs control0) := by
  exact (measurable_markerRateWeightSum rate rewards C_star C_h q t s hs control0).mono
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0) le_rfl

/-- The literal rate sum is nonnegative and is bounded by `m / beta`, using
the sum of the actual inclusion marginals and the actual canonical rate floor.
-/
theorem markerRateWeightSum_bounds (z : Zplus) :
    0 ≤ markerRateWeightSum rate rewards C_star C_h q t s hs control0 z ∧
      markerRateWeightSum rate rewards C_star C_h q t s hs control0 z ≤
        (p.m : ℝ) / beta := by
  have hbeta : 0 < beta :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hsum := ReferenceFirstLiveQueueEnergyEnvelope.sum_thetaBefore_eq_m
    rate rewards C_star C_h q t s hs control0 z
  unfold markerRateWeightSum
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    have htheta := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
    have hrate := ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus_bounds
      rate rewards C_star C_h q t s hs control0 j z
    exact div_nonneg htheta.1 (le_of_lt (hrate.1.trans_le hrate.2.1))
  · calc
      _ ≤ ∑ j : Fin p.K,
          ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
              rate rewards C_star C_h q t s hs control0 j z / beta :=
        Finset.sum_le_sum fun j hj => by
          have htheta := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
            rate rewards C_star C_h q t s hs control0 j z
          have hrate := ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus_bounds
            rate rewards C_star C_h q t s hs control0 j z
          have hrecip : 1 / markerRatePlus j z ≤ 1 / beta :=
            one_div_le_one_div_of_le hbeta hrate.2.1
          calc
            _ = thetaBefore j z * (1 / markerRatePlus j z) := by ring
            _ ≤ thetaBefore j z * (1 / beta) :=
              mul_le_mul_of_nonneg_left hrecip htheta.1
            _ = thetaBefore j z / beta := by ring
      _ = (∑ j : Fin p.K, thetaBefore j z) * (1 / beta) := by
        calc
          _ = ∑ j : Fin p.K, thetaBefore j z * (1 / beta) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by
            symm
            exact Finset.sum_mul (Finset.univ)
              (fun j : Fin p.K => thetaBefore j z) (1 / beta)
      _ = (p.m : ℝ) / beta := by
        rw [hsum]
        ring

/-- The bounded canonical rate sum is integrable under the same finite branch
measure, including the zero-measure case. -/
theorem integrable_markerRateWeightSum :
    Integrable (markerRateWeightSum rate rewards C_star C_h q t s hs control0) muPlus := by
  have hmeas := measurable_markerRateWeightSum_ambient
    rate rewards C_star C_h q t s hs control0
  have hbeta : 0 < beta :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  apply integrable_of_norm_le_uniform (C := (p.m : ℝ) / beta) hmeas
    (div_nonneg hm hbeta.le)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (markerRateWeightSum_bounds rate rewards C_star C_h q t s hs control0 z).1]
  exact (markerRateWeightSum_bounds rate rewards C_star C_h q t s hs control0 z).2

private theorem integrable_thetaBefore (j : Fin p.K) :
    Integrable (fun z : Zplus => thetaBefore j z) muPlus := by
  have hmeas : Measurable (fun z : Zplus => thetaBefore j z) :=
    (ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  apply integrable_of_norm_le_uniform (C := (1 : ℝ)) hmeas (by norm_num)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z).1]
  exact (ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
    rate rewards C_star C_h q t s hs control0 j z).2

private theorem measurable_armCoefficient (j : Fin p.K) :
    Measurable[Fplus] (fun z : Zplus =>
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) := by
  exact (ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_const.mul
        (ReferenceFirstLiveQueueEnergyEnvelope.measurable_backlogBefore
          rate rewards C_star C_h q t s hs control0 j)).add measurable_const)

private theorem armCoefficient_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) ∧
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) ≤
        4 * Bcap + (1 / 2 : ℝ) := by
  have htheta := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
    rate rewards C_star C_h q t s hs control0 j z
  have hb0 := ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_nonneg
    rate rewards C_star C_h q t s hs control0 j z
  have hb := ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_le_two_Bcap
    rate rewards C_star C_h q t s hs control0 j z
  have hfactor : 0 ≤ 2 * backlogBefore j z + (1 / 2 : ℝ) ∧
      2 * backlogBefore j z + (1 / 2 : ℝ) ≤ 4 * Bcap + (1 / 2 : ℝ) := by
    constructor
    · linarith
    · calc
        2 * backlogBefore j z + (1 / 2 : ℝ) ≤
            2 * (2 * Bcap) + (1 / 2 : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
          linarith only [hmul]
        _ = 4 * Bcap + (1 / 2 : ℝ) := by ring
  constructor
  · exact mul_nonneg htheta.1 hfactor.1
  · calc
      _ ≤ 1 * (2 * backlogBefore j z + (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right htheta.2 hfactor.1
      _ ≤ 1 * (4 * Bcap + (1 / 2 : ℝ)) := by exact mul_le_mul_of_nonneg_left hfactor.2 (by norm_num)
      _ = 4 * Bcap + (1 / 2 : ℝ) := by ring

/-- Integrability of the complete first-drift coefficient times the accepted
arrival follows from the actual queue cap and M's accepted-arrival bound. -/
theorem integrable_weightedAcceptedArrivalCoefficient (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      thetaBefore j z * ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z))
      muPlus := by
  have haccepted := ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hcoef := measurable_armCoefficient rate rewards C_star C_h q t s hs control0 j
  have hcoefAmbient : Measurable (fun z : Zplus =>
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) :=
    hcoef.mono (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0) le_rfl
  have hbound : ∀ᵐ z ∂muPlus,
      ‖thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))‖ ≤
        4 * Bcap + (1 / 2 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (armCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).1]
    exact (armCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2
  have hmul := haccepted.bdd_mul hcoefAmbient.aestronglyMeasurable hbound
  apply hmul.congr
  filter_upwards [] with z
  ring

/-- Integrability of the weighted accepted square follows from the actual
inclusion bound and M's accepted-square integrability. -/
theorem integrable_weightedAcceptedArrivalSq (j : Fin p.K) :
    Integrable (fun z : Zplus => thetaBefore j z * (acceptedA j z) ^ 2) muPlus := by
  have htheta := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hthetaMeas : AEStronglyMeasurable (fun z : Zplus => thetaBefore j z) muPlus :=
    ((ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂muPlus, ‖thetaBefore j z‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z).1]
    exact (ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z).2
  have hsquare := ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA_sq
    rate rewards C_star C_h q t s hs control0 j
  have hmul := hsquare.bdd_mul hthetaMeas hbound
  exact hmul

private theorem integrable_armEnvelope (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
      muPlus := by
  have hfirst := integrable_weightedAcceptedArrivalCoefficient
    rate rewards C_star C_h q t s hs control0 j
  have hsquare := integrable_weightedAcceptedArrivalSq
    rate rewards C_star C_h q t s hs control0 j
  have hbacklog :=
    ReferenceFirstLiveQueueEnergyEnvelope.integrable_thetaBefore_mul_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have htheta := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hpieces : Integrable (fun z : Zplus =>
      thetaBefore j z * ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) +
        thetaBefore j z * (acceptedA j z) ^ 2 +
        (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
        16 * thetaBefore j z) muPlus := by
    exact ((hfirst.add hsquare).add (hbacklog.const_mul (-(15 / 2 : ℝ))))
      |>.add (htheta.const_mul 16)
  apply hpieces.congr
  filter_upwards [] with z
  ring

private theorem integrable_driftEnvelope :
    Integrable (fun z : Zplus =>
      ∑ j : Fin p.K,
        thetaBefore j z *
          ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
            (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) muPlus := by
  apply integrable_finsetSum
  intro j hj
  exact integrable_armEnvelope rate rewards C_star C_h q t s hs control0 j

private theorem integrable_driftRateRhs :
    Integrable (fun z : Zplus =>
      -(11 / 2 : ℝ) * weightedBacklogBefore z +
        markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
        (33 / 2 : ℝ) * p.m) muPlus := by
  have hbacklog := ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  have hrate := integrable_markerRateWeightSum rate rewards C_star C_h q t s hs control0
  convert ((hbacklog.const_mul (-(11 / 2 : ℝ))).add hrate).add
    (integrable_const ((33 / 2 : ℝ) * p.m)) using 1

private theorem measurable_driftRateRhs :
    Measurable[Fplus] (fun z : Zplus =>
      -(11 / 2 : ℝ) * weightedBacklogBefore z +
        markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
        (33 / 2 : ℝ) * p.m) := by
  exact ((measurable_const.mul
      (ReferenceFirstLiveQueueEnergyEnvelope.measurable_weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0)).add
      (measurable_markerRateWeightSum rate rewards C_star C_h q t s hs control0)).add
    measurable_const

private theorem measurableSet_G : MeasurableSet[Fplus] G :=
  ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0

private theorem measurableSet_G_ambient : MeasurableSet G :=
  ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0

/-- Each arm's conditional drift term pulls its actual adapted coefficients
through conditional expectation. All product integrability is derived above. -/
private theorem condExp_armEnvelope (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) | Fplus] =ᵐ[muPlus]
      (fun z : Zplus =>
        thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
            muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z +
          thetaBefore j z *
            muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z +
          (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
          16 * thetaBefore j z) := by
  have hcoeffMeas := measurable_armCoefficient rate rewards C_star C_h q t s hs control0 j
  have hcoeffIntegrable := integrable_weightedAcceptedArrivalCoefficient
    rate rewards C_star C_h q t s hs control0 j
  have hcoeffProductIntegrable : Integrable (fun z : Zplus =>
      (thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) * acceptedA j z)
      muPlus :=
    hcoeffIntegrable.congr (ae_of_all muPlus fun z => by ring)
  have haccepted := ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hthetaMeas :=
    ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j
  have hthetaSqIntegrable := integrable_weightedAcceptedArrivalSq
    rate rewards C_star C_h q t s hs control0 j
  have hsquare := ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA_sq
    rate rewards C_star C_h q t s hs control0 j
  have hthetaBacklog :=
    ReferenceFirstLiveQueueEnergyEnvelope.integrable_thetaBefore_mul_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have hthetaIntegrable := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hbacklogMeas :=
    ReferenceFirstLiveQueueEnergyEnvelope.measurable_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have hbacklogField : Measurable[Fplus] (fun z : Zplus => backlogBefore j z) :=
    hbacklogMeas
  have hcoeffPull := condExp_mul_of_aestronglyMeasurable_left
    hcoeffMeas.aestronglyMeasurable
    hcoeffProductIntegrable haccepted
  have hthetaPull := condExp_mul_of_aestronglyMeasurable_left
    hthetaMeas.aestronglyMeasurable hthetaSqIntegrable hsquare
  have hbacklogFixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0)
    (hthetaMeas.mul hbacklogField).aestronglyMeasurable hthetaBacklog
  have hthetaFixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0)
    hthetaMeas.aestronglyMeasurable hthetaIntegrable
  have hscaleBacklog := condExp_smul (μ := muPlus) (m := Fplus)
    (-(15 / 2 : ℝ))
    (fun z : Zplus => thetaBefore j z * backlogBefore j z)
  have hscaleTheta := condExp_smul (μ := muPlus) (m := Fplus)
    (16 : ℝ) (fun z : Zplus => thetaBefore j z)
  have hshape : (fun z : Zplus =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) =
      ((fun z : Zplus =>
          thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) +
        (fun z : Zplus => thetaBefore j z * (acceptedA j z) ^ 2)) +
      ((fun z : Zplus => (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z)) +
        (fun z : Zplus => 16 * thetaBefore j z)) := by
    funext z
    simp only [Pi.add_apply]
    ring_nf
  have hcoeffFunctionEq :
      (fun z : Zplus =>
        thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) =
      (fun z : Zplus => thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) *
        acceptedA j := by
    funext z
    rfl
  have hthetaFunctionEq :
      (fun z : Zplus => thetaBefore j z * (acceptedA j z) ^ 2) =
      thetaBefore j * (fun z : Zplus => (acceptedA j z) ^ 2) := by
    funext z
    rfl
  have hscaleBacklogFunctionEq :
      (fun z : Zplus => (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z)) =
      (-(15 / 2 : ℝ)) • (fun z : Zplus => thetaBefore j z * backlogBefore j z) := by
    funext z
    rfl
  have hscaleThetaFunctionEq :
      (fun z : Zplus => (16 : ℝ) * thetaBefore j z) = (16 : ℝ) • thetaBefore j := by
    funext z
    rfl
  have hbacklogFunctionEq :
      (fun z : Zplus => thetaBefore j z * backlogBefore j z) =
        thetaBefore j * (fun z : Zplus => backlogBefore j z) := by
    funext z
    rfl
  have hcoeffCondEq := condExp_congr_ae (m := Fplus)
    (ae_of_all muPlus fun z => congrFun hcoeffFunctionEq z)
  have hthetaCondEq := condExp_congr_ae (m := Fplus)
    (ae_of_all muPlus fun z => congrFun hthetaFunctionEq z)
  have hscaleBacklogCondEq := condExp_congr_ae (m := Fplus)
    (ae_of_all muPlus fun z => congrFun hscaleBacklogFunctionEq z)
  have hscaleThetaCondEq := condExp_congr_ae (m := Fplus)
    (ae_of_all muPlus fun z => congrFun hscaleThetaFunctionEq z)
  have hbacklogCondEq := condExp_congr_ae (m := Fplus)
    (ae_of_all muPlus fun z => congrFun hbacklogFunctionEq z)
  have hsumFirst := condExp_add hcoeffProductIntegrable hthetaSqIntegrable Fplus
  have hsumLast := condExp_add
    (hthetaBacklog.const_mul (-(15 / 2 : ℝ)))
    (hthetaIntegrable.const_mul 16) Fplus
  have hsumAll := condExp_add
    (hcoeffProductIntegrable.add hthetaSqIntegrable)
    ((hthetaBacklog.const_mul (-(15 / 2 : ℝ))).add
      (hthetaIntegrable.const_mul 16)) Fplus
  filter_upwards [hsumAll, hsumFirst, hsumLast, hcoeffPull, hthetaPull,
    hbacklogFixed, hthetaFixed, hscaleBacklog, hscaleTheta,
    hcoeffCondEq, hthetaCondEq, hscaleBacklogCondEq, hscaleThetaCondEq,
    hbacklogCondEq] with z
    htotal hfirst hlast hcoeff htheta hsBacklog hsTheta hscaleB hscaleT
    hcoeffBridge hthetaBridge hscaleBacklogBridge hscaleThetaBridge hbacklogBridge
  calc
    _ = muPlus[
        ((fun x : Zplus =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
          (fun x : Zplus => thetaBefore j x * (acceptedA j x) ^ 2)) +
        ((fun x : Zplus => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
          (fun x : Zplus => 16 * thetaBefore j x)) | Fplus] z := by
      rw [hshape]
    _ = (muPlus[
          (fun x : Zplus =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
            (fun x : Zplus => thetaBefore j x * (acceptedA j x) ^ 2) | Fplus] +
        muPlus[
          (fun x : Zplus => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
            (fun x : Zplus => 16 * thetaBefore j x) | Fplus]) z := htotal
    _ = muPlus[
          (fun x : Zplus =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
            (fun x : Zplus => thetaBefore j x * (acceptedA j x) ^ 2) | Fplus] z +
        muPlus[
          (fun x : Zplus => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
            (fun x : Zplus => 16 * thetaBefore j x) | Fplus] z := rfl
    _ = (muPlus[(fun x : Zplus =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) | Fplus] +
          muPlus[(fun x : Zplus => thetaBefore j x * (acceptedA j x) ^ 2) | Fplus]) z +
        (muPlus[(fun x : Zplus => (-(15 / 2 : ℝ)) *
            (thetaBefore j x * backlogBefore j x)) | Fplus] +
          muPlus[(fun x : Zplus => 16 * thetaBefore j x) | Fplus]) z := by
      rw [hfirst, hlast]
    _ = thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
          muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z +
        thetaBefore j z * muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z +
        (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
        16 * thetaBefore j z := by
      simp only [Pi.add_apply]
      rw [hcoeffBridge, hthetaBridge, hscaleBacklogBridge, hscaleThetaBridge,
        hcoeff, htheta, hscaleB, hscaleT]
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      rw [hbacklogBridge, hsBacklog, hsTheta]
      simp only [Pi.mul_apply]
      ring_nf

/-- The conditional envelope after summing finitely many arms keeps the same
`G` indicator and the actual canonical rate sum. -/
private theorem condExp_driftEnvelope_bound :
    muPlus[(fun z : Zplus => Set.indicator G
      (fun x : Zplus =>
        ∑ j : Fin p.K,
          thetaBefore j x *
            ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
              (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16)) z)
      | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m) := by
  have henvIntegrable := integrable_driftEnvelope rate rewards C_star C_h q t s hs control0
  have hG := measurableSet_G rate rewards C_star C_h q t s hs control0
  have hmask := condExp_indicator henvIntegrable hG
  have hsumCE :
      muPlus[(fun z : Zplus =>
        ∑ j : Fin p.K,
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        | Fplus] =ᵐ[muPlus]
        (fun z : Zplus =>
          ∑ j : Fin p.K,
            muPlus[(fun x : Zplus =>
              thetaBefore j x *
                ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                  (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
              | Fplus] z) := by
    have hpointwise : (fun z : Zplus =>
        ∑ j : Fin p.K,
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) =
        ∑ j : Fin p.K, fun z : Zplus =>
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16) := by
      funext z
      simp only [Finset.sum_apply]
    have hpointwiseAE := ae_of_all muPlus (fun z => congrFun hpointwise z)
    have hchange := condExp_congr_ae (m := Fplus) hpointwiseAE
    filter_upwards [hchange,
      (condExp_finsetSum
        (s := Finset.univ)
        (f := fun j : Fin p.K => fun z : Zplus =>
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        (by
          intro j hj
          exact integrable_armEnvelope rate rewards C_star C_h q t s hs control0 j)
        Fplus)] with z hchange hsum
    simpa only [Finset.sum_apply] using hchange.trans hsum
  have harmEq : ∀ j : Fin p.K,
      muPlus[(fun z : Zplus =>
        thetaBefore j z *
          ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
            (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        | Fplus] =ᵐ[muPlus]
        (fun z : Zplus =>
          thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
              muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z +
            thetaBefore j z *
              muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z +
            (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
            16 * thetaBefore j z) := by
    intro j
    exact condExp_armEnvelope rate rewards C_star C_h q t s hs control0 j
  have hfirst : ∀ j : Fin p.K,
      muPlus[(fun z : Zplus => acceptedA j z) | Fplus] ≤ᵐ[muPlus]
        (fun _ : Zplus => 1) := by
    intro j
    exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_first_bounds
      rate rewards C_star C_h q t s hs control0 j).2.1.trans
      ((ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_first_bounds
        rate rewards C_star C_h q t s hs control0 j).2.2)
  have hsquare : ∀ j : Fin p.K,
      muPlus[(fun z : Zplus => (acceptedA j z) ^ 2) | Fplus] ≤ᵐ[muPlus]
        (Set.indicator G (fun z : Zplus => 1 / markerRatePlus j z)) := by
    intro j
    exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_second_bounds
      rate rewards C_star C_h q t s hs control0 j).2.1.trans
      ((ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_second_bounds
        rate rewards C_star C_h q t s hs control0 j).2.2.1)
  have hfiniteArmEq : ∀ᵐ z ∂muPlus, ∀ j : Fin p.K,
      muPlus[(fun x : Zplus =>
        thetaBefore j x *
          ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
            (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
        | Fplus] z =
        thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
            muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z +
          thetaBefore j z *
            muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z +
          (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
          16 * thetaBefore j z := by
    exact ae_all_iff.mpr harmEq
  have hfiniteFirst : ∀ᵐ z ∂muPlus, ∀ j : Fin p.K,
      muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z ≤ 1 := by
    exact ae_all_iff.mpr hfirst
  have hfiniteSquare : ∀ᵐ z ∂muPlus, ∀ j : Fin p.K,
      muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z ≤
        Set.indicator G (fun x : Zplus => 1 / markerRatePlus j x) z := by
    exact ae_all_iff.mpr hsquare
  filter_upwards [hmask, hsumCE, hfiniteArmEq, hfiniteFirst, hfiniteSquare]
    with z hmaskAt hsumAt hEqAll hFirstAll hSquareAll
  rw [hmaskAt]
  have hconditionalSum :
      Set.indicator G
        (muPlus[(fun x : Zplus =>
          ∑ j : Fin p.K,
            thetaBefore j x *
              ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
          | Fplus]) z =
      Set.indicator G (fun x : Zplus =>
        ∑ j : Fin p.K,
          muPlus[(fun y : Zplus =>
            thetaBefore j y *
              ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
                (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
            | Fplus] x) z := by
    by_cases hz : z ∈ G
    · simpa [Set.indicator, hz] using hsumAt
    · simp [Set.indicator, hz]
  rw [hconditionalSum]
  have hindicatorSum (f : Fin p.K → Zplus → ℝ) :
      Set.indicator G (fun x : Zplus => ∑ j : Fin p.K, f j x) z =
        ∑ j : Fin p.K, Set.indicator G (f j) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
    · simp [Set.indicator, hz]
  rw [hindicatorSum]
  have hArmIneq (j : Fin p.K) :
      Set.indicator G (fun x : Zplus =>
        muPlus[(fun y : Zplus =>
          thetaBefore j y *
            ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
              (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
          | Fplus] x) z ≤
      Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / markerRatePlus j x +
          (33 / 2 : ℝ) * thetaBefore j x) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      have htheta := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z
      have hb0 := ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_nonneg
        rate rewards C_star C_h q t s hs control0 j z
      have hcoef := armCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z
      have hrate := ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus_bounds
        rate rewards C_star C_h q t s hs control0 j z
      have hceA := hFirstAll j
      have hceAsq := hSquareAll j
      have hceAsq' :
          muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z ≤
            1 / markerRatePlus j z := by
        simpa only [Set.indicator_of_mem hz] using hceAsq
      rw [hEqAll j]
      calc
        _ ≤ thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) +
              thetaBefore j z * (1 / markerRatePlus j z) +
              (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
              16 * thetaBefore j z := by
          have hfirstMul :
              thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
                  muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z ≤
                thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hceA hcoef.1
          have hsquareMul :
              thetaBefore j z *
                  muPlus[(fun x : Zplus => (acceptedA j x) ^ 2) | Fplus] z ≤
                thetaBefore j z * (1 / markerRatePlus j z) :=
            mul_le_mul_of_nonneg_left hceAsq' htheta.1
          linarith only [hfirstMul, hsquareMul]
        _ = -(11 / 2 : ℝ) * (thetaBefore j z * backlogBefore j z) +
              thetaBefore j z / markerRatePlus j z +
              (33 / 2 : ℝ) * thetaBefore j z := by ring
    · simp [Set.indicator, hz]
  have hsumIneq :
      (∑ j : Fin p.K, Set.indicator G (fun x : Zplus =>
        muPlus[(fun y : Zplus =>
          thetaBefore j y *
            ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
              (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
          | Fplus] x) z) ≤
      ∑ j : Fin p.K, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / markerRatePlus j x +
          (33 / 2 : ℝ) * thetaBefore j x) z :=
    Finset.sum_le_sum fun j hj => hArmIneq j
  have htargetIndicator :
      Set.indicator G (fun x : Zplus =>
        ∑ j : Fin p.K,
          (-(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
            thetaBefore j x / markerRatePlus j x +
            (33 / 2 : ℝ) * thetaBefore j x)) z =
      ∑ j : Fin p.K, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / markerRatePlus j x +
          (33 / 2 : ℝ) * thetaBefore j x) z :=
    hindicatorSum _
  have hweightedBacklog :
      (∑ j : Fin p.K, thetaBefore j z * backlogBefore j z) =
        weightedBacklogBefore z := by
    unfold ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
      RecordedWeightedDrift.weightedBacklog
    apply Finset.sum_congr rfl
    intro j hj
    rw [ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_eq_normalized
      rate rewards C_star C_h q t s hs control0 j z]
    rfl
  have hthetaSum := ReferenceFirstLiveQueueEnergyEnvelope.sum_thetaBefore_eq_m
    rate rewards C_star C_h q t s hs control0 z
  have hterms :
      (∑ j : Fin p.K,
        (-(11 / 2 : ℝ) * (thetaBefore j z * backlogBefore j z) +
          thetaBefore j z / markerRatePlus j z +
          (33 / 2 : ℝ) * thetaBefore j z)) =
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m := by
    unfold markerRateWeightSum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hweightedBacklog, hthetaSum]
  calc
    _ ≤ ∑ j : Fin p.K, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / markerRatePlus j x +
          (33 / 2 : ℝ) * thetaBefore j x) z := hsumIneq
    _ = Set.indicator G (fun x : Zplus =>
        ∑ j : Fin p.K,
          (-(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
            thetaBefore j x / markerRatePlus j x +
            (33 / 2 : ℝ) * thetaBefore j x)) z := htargetIndicator.symm
    _ = Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z := by
      by_cases hz : z ∈ G
      · simpa [Set.indicator, hz] using hterms
      · simp [Set.indicator, hz]

/-- The conditional expectation of the actual potential difference is bounded
almost everywhere on the original unnormalized branch by the actual rate-sum
readout. The first overflow update is part of `potentialAfter`. -/
theorem potential_drift_conditional_rate_sum :
    muPlus[(fun z : Zplus => potentialAfter z - potentialBefore z) | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m) := by
  have hGambient := measurableSet_G_ambient rate rewards C_star C_h q t s hs control0
  have hDifferenceInt :=
    ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialDifference
      rate rewards C_star C_h q t s hs control0
  have hEnvelopeInt := integrable_driftEnvelope rate rewards C_star C_h q t s hs control0
  have hDifferenceMaskInt := hDifferenceInt.indicator hGambient
  have hEnvelopeMaskInt := hEnvelopeInt.indicator hGambient
  have hDifferenceMask : (fun z : Zplus => potentialAfter z - potentialBefore z) =ᵐ[muPlus]
      (fun z : Zplus => Set.indicator G
        (fun x : Zplus => potentialAfter x - potentialBefore x) z) := by
    filter_upwards [] with z
    by_cases hz : z ∈ G
    · simp [Set.indicator, hz]
    · have hOff := ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter_eq_potentialBefore_off_G
        rate rewards C_star C_h q t s hs control0 z hz
      simp [Set.indicator, hz, hOff]
  have hpoint : (fun z : Zplus => Set.indicator G
      (fun x : Zplus => potentialAfter x - potentialBefore x) z) ≤ᵐ[muPlus]
      (fun z : Zplus => Set.indicator G
        (fun x : Zplus =>
          ∑ j : Fin p.K,
            thetaBefore j x *
              ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16)) z) :=
    ae_of_all muPlus fun z =>
      ReferenceFirstLiveQueueEnergyEnvelope.potential_drift_envelope_indicator
        rate rewards C_star C_h q t s hs control0 z
  have hmono := condExp_mono (m := Fplus) hDifferenceMaskInt hEnvelopeMaskInt hpoint
  have hmaskEq := condExp_congr_ae (m := Fplus) hDifferenceMask
  have henvelopeConditional :=
    condExp_driftEnvelope_bound rate rewards C_star C_h q t s hs control0
  exact hmaskEq.trans_le (hmono.trans henvelopeConditional)

/-- Integrating the conditional estimate gives the one-step drift bound on
the same finite `muPlus` measure. No normalization or splice to another
`q,s,t` branch is performed. -/
theorem potential_drift_integral_rate_sum :
    (∫ z : Zplus, potentialAfter z - potentialBefore z ∂muPlus) ≤
      ∫ z : Zplus, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z ∂muPlus := by
  have hfieldle := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have hRhsInt := integrable_driftRateRhs rate rewards C_star C_h q t s hs control0
  have hRhsMaskInt := hRhsInt.indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z : Zplus,
        muPlus[(fun x : Zplus => potentialAfter x - potentialBefore x) | Fplus] z ∂muPlus :=
      (integral_condExp hfieldle).symm
    _ ≤ ∫ z : Zplus, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z ∂muPlus :=
      integral_mono_ae integrable_condExp hRhsMaskInt
        (potential_drift_conditional_rate_sum rate rewards C_star C_h q t s hs control0)

end Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift

end
