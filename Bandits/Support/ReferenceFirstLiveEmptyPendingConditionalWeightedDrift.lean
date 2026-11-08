/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope

import Mathlib.Tactic

/-!
# Conditional weighted drift on the original empty-pending stratum

This module conditions the actual empty-pending queue-energy envelope on the
same current-control-erased prefix field and finite, unnormalized source
measure. It records the literal canonical rate sum and integrates the resulting
one-step bound. No sharp rate-sum estimate or manuscript queue theorem is
proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalWeightedDrift

abbrev Parameters := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.Parameters
abbrev RateInput := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.RateInput
abbrev RewardTable := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.RewardTable
abbrev TimeControl := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0
local notation "muE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
local notation "Fempty" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
    rate rewards C_star C_h q t s hs control0
local notation "xofE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
    rate rewards C_star C_h q t s hs control0
local notation "xiE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
    rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveEmptyPendingAcceptedMoments.G
    rate rewards C_star C_h q t s hs control0
local notation "thetaBefore" =>
  ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
    rate rewards C_star C_h q t s hs control0
local notation "backlogBefore" =>
  ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore
    rate rewards C_star C_h q t s hs control0
local notation "weightedBacklogBefore" =>
  ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialBefore" =>
  ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialAfter" =>
  ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
    rate rewards C_star C_h q t s hs control0
local notation "acceptedA" =>
  ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
    rate rewards C_star C_h q t s hs control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Bcap" => 1 / (32 * rate.eta.val)

/-- The literal sum of the actual canonical rates weighted by the strict-past
inclusion marginals on the same empty-pending source point. -/
def markerRateWeightSum (z : Ze) : ℝ :=
  ∑ j : Fin p.K, thetaBefore j z / xiE (xofE z) j

/-- Coordinate measurability composes the adapted marginal and actual
empty-payload rate on the original prefix field. -/
theorem measurable_markerRateWeightSum :
    Measurable[Fempty]
      (markerRateWeightSum rate rewards C_star C_h q t s hs control0) := by
  unfold markerRateWeightSum
  apply Finset.measurable_sum
  intro j hj
  exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).div
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty_source
      rate rewards C_star C_h q t s hs control0 j)

/-- The same literal sum is Borel on the ambient empty source carrier. -/
theorem measurable_markerRateWeightSum_ambient :
    Measurable
      (markerRateWeightSum rate rewards C_star C_h q t s hs control0) := by
  exact (measurable_markerRateWeightSum rate rewards C_star C_h q t s hs control0).mono
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) le_rfl

private theorem xiEmpty_pos_lower_bound (j : Fin p.K) (z : Ze) :
    0 < xiE (xofE z) j ∧ beta ≤ xiE (xofE z) j := by
  change 0 < CanonicalRecordingRates.xi p rate.eta.val
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
        rate rewards C_star C_h q t s hs control0 (xofE z)).view.payload.anchor j ∧
    CanonicalRecordingRates.beta p rate.eta.val ≤ CanonicalRecordingRates.xi p rate.eta.val
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
        rate rewards C_star C_h q t s hs control0 (xofE z)).view.payload.anchor j
  exact ⟨CanonicalRecordingRates.xi_pos p rate.eta.property _ _,
    CanonicalRecordingRates.beta_le_xi p rate.eta.property _ _⟩

/-- The actual rate sum is nonnegative and has the canonical finite bound.
The lower bound for each denominator is derived from E's selected payload and
the canonical rate definition. -/
theorem markerRateWeightSum_bounds (z : Ze) :
    0 ≤ markerRateWeightSum rate rewards C_star C_h q t s hs control0 z ∧
      markerRateWeightSum rate rewards C_star C_h q t s hs control0 z ≤
        (p.m : ℝ) / beta := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hsum := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.sum_thetaBefore_eq_m
    rate rewards C_star C_h q t s hs control0 z
  unfold markerRateWeightSum
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    have htheta := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
    have hrate := xiEmpty_pos_lower_bound rate rewards C_star C_h q t s hs control0 j z
    exact div_nonneg htheta.1 hrate.1.le
  · calc
      _ ≤ ∑ j : Fin p.K,
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
              rate rewards C_star C_h q t s hs control0 j z / beta :=
        Finset.sum_le_sum fun j hj => by
          have htheta := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
            rate rewards C_star C_h q t s hs control0 j z
          have hrate := xiEmpty_pos_lower_bound rate rewards C_star C_h q t s hs control0 j z
          have hrecip : 1 / xiE (xofE z) j ≤ 1 / beta :=
            one_div_le_one_div_of_le hbeta hrate.2
          calc
            _ = thetaBefore j z * (1 / xiE (xofE z) j) := by ring
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

/-- The bounded actual rate sum is integrable on the same finite,
unnormalized empty-source measure. -/
theorem integrable_markerRateWeightSum :
    Integrable
      (markerRateWeightSum rate rewards C_star C_h q t s hs control0) muE := by
  have hmeas := measurable_markerRateWeightSum_ambient
    rate rewards C_star C_h q t s hs control0
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hbound : ∀ᵐ z ∂muE,
      ‖markerRateWeightSum rate rewards C_star C_h q t s hs control0 z‖ ≤
        (p.m : ℝ) / beta := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (markerRateWeightSum_bounds rate rewards C_star C_h q t s hs control0 z).1]
    exact (markerRateWeightSum_bounds rate rewards C_star C_h q t s hs control0 z).2
  exact Integrable.of_bound hmeas.aestronglyMeasurable ((p.m : ℝ) / beta) hbound

private theorem integrable_thetaBefore (j : Fin p.K) :
    Integrable (fun z : Ze => thetaBefore j z) muE := by
  have hmeas : Measurable (fun z : Ze => thetaBefore j z) :=
    (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl
  have hbound : ∀ᵐ z ∂muE, ‖thetaBefore j z‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z).1]
    exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z).2
  exact Integrable.of_bound hmeas.aestronglyMeasurable 1 hbound

private theorem measurable_armCoefficient (j : Fin p.K) :
    Measurable[Fempty] (fun z : Ze =>
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) := by
  exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_const.mul
        (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_backlogBefore
          rate rewards C_star C_h q t s hs control0 j)).add measurable_const)

private theorem armCoefficient_bounds (j : Fin p.K) (z : Ze) :
    0 ≤ thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) ∧
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) ≤
        4 * Bcap + (1 / 2 : ℝ) := by
  have htheta := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
    rate rewards C_star C_h q t s hs control0 j z
  have hb0 := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_nonneg
    rate rewards C_star C_h q t s hs control0 j z
  have hb := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_le_two_Bcap
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
      _ ≤ 1 * (4 * Bcap + (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactor.2 (by norm_num)
      _ = 4 * Bcap + (1 / 2 : ℝ) := by ring

/-- The adapted first-drift coefficient times the actual accepted arrival is
integrable from its derived uniform coefficient bound and A's actual arrival
integrability. -/
theorem integrable_weightedAcceptedArrivalCoefficient (j : Fin p.K) :
    Integrable (fun z : Ze =>
      thetaBefore j z * ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z))
      muE := by
  have haccepted := ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hcoef := measurable_armCoefficient rate rewards C_star C_h q t s hs control0 j
  have hcoefAmbient : Measurable (fun z : Ze =>
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) :=
    hcoef.mono (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) le_rfl
  have hbound : ∀ᵐ z ∂muE,
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

/-- The adapted inclusion marginal times the actual accepted square is
integrable from A's square integrability and the proved marginal bound. -/
theorem integrable_weightedAcceptedArrivalSq (j : Fin p.K) :
    Integrable (fun z : Ze => thetaBefore j z * (acceptedA j z) ^ 2) muE := by
  have htheta := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hthetaMeas : AEStronglyMeasurable (fun z : Ze => thetaBefore j z) muE :=
    ((ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂muE, ‖thetaBefore j z‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z).1]
    exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z).2
  have hsquare := ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA_sq
    rate rewards C_star C_h q t s hs control0 j
  have hmul := hsquare.bdd_mul hthetaMeas hbound
  exact hmul

private theorem integrable_armEnvelope (j : Fin p.K) :
    Integrable (fun z : Ze =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
      muE := by
  have hfirst := integrable_weightedAcceptedArrivalCoefficient
    rate rewards C_star C_h q t s hs control0 j
  have hsquare := integrable_weightedAcceptedArrivalSq
    rate rewards C_star C_h q t s hs control0 j
  have hbacklog :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_thetaBefore_mul_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have htheta := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hpieces : Integrable (fun z : Ze =>
      thetaBefore j z * ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) +
        thetaBefore j z * (acceptedA j z) ^ 2 +
        (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
        16 * thetaBefore j z) muE := by
    exact ((hfirst.add hsquare).add (hbacklog.const_mul (-(15 / 2 : ℝ))))
      |>.add (htheta.const_mul 16)
  apply hpieces.congr
  filter_upwards [] with z
  ring

private theorem integrable_driftEnvelope :
    Integrable (fun z : Ze =>
      ∑ j : Fin p.K,
        thetaBefore j z *
          ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
            (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) muE := by
  apply integrable_finsetSum
  intro j hj
  exact integrable_armEnvelope rate rewards C_star C_h q t s hs control0 j

private theorem integrable_driftRateRhs :
    Integrable (fun z : Ze =>
      -(11 / 2 : ℝ) * weightedBacklogBefore z +
        markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
        (33 / 2 : ℝ) * p.m) muE := by
  have hbacklog :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0
  have hrate := integrable_markerRateWeightSum rate rewards C_star C_h q t s hs control0
  convert ((hbacklog.const_mul (-(11 / 2 : ℝ))).add hrate).add
    (integrable_const ((33 / 2 : ℝ) * p.m)) using 1

private theorem measurable_driftRateRhs :
    Measurable[Fempty] (fun z : Ze =>
      -(11 / 2 : ℝ) * weightedBacklogBefore z +
        markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
        (33 / 2 : ℝ) * p.m) := by
  exact ((measurable_const.mul
      (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0)).add
      (measurable_markerRateWeightSum rate rewards C_star C_h q t s hs control0)).add
    measurable_const

private theorem measurableSet_G : MeasurableSet[Fempty] G :=
  ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G
    rate rewards C_star C_h q t s hs control0

private theorem measurableSet_G_ambient : MeasurableSet G :=
  ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
    rate rewards C_star C_h q t s hs control0

/-- Conditional expectation pulls the actual adapted first and square
coefficients through A's same-measure accepted moments. -/
private theorem condExp_armEnvelope (j : Fin p.K) :
    muE[(fun z : Ze =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) | Fempty] =ᵐ[muE]
      (fun z : Ze =>
        thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
            muE[(fun x : Ze => acceptedA j x) | Fempty] z +
          thetaBefore j z *
            muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z +
          (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
          16 * thetaBefore j z) := by
  have hcoeffMeas := measurable_armCoefficient rate rewards C_star C_h q t s hs control0 j
  have hcoeffIntegrable := integrable_weightedAcceptedArrivalCoefficient
    rate rewards C_star C_h q t s hs control0 j
  have hcoeffProductIntegrable : Integrable (fun z : Ze =>
      (thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) * acceptedA j z)
      muE :=
    hcoeffIntegrable.congr (ae_of_all muE fun z => by ring)
  have haccepted := ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hthetaMeas :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j
  have hthetaSqIntegrable := integrable_weightedAcceptedArrivalSq
    rate rewards C_star C_h q t s hs control0 j
  have hsquare := ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA_sq
    rate rewards C_star C_h q t s hs control0 j
  have hthetaBacklog :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_thetaBefore_mul_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have hthetaIntegrable := integrable_thetaBefore rate rewards C_star C_h q t s hs control0 j
  have hbacklogMeas :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_backlogBefore
      rate rewards C_star C_h q t s hs control0 j
  have hbacklogField : Measurable[Fempty] (fun z : Ze => backlogBefore j z) :=
    hbacklogMeas
  have hcoeffPull := condExp_mul_of_aestronglyMeasurable_left
    hcoeffMeas.aestronglyMeasurable hcoeffProductIntegrable haccepted
  have hthetaPull := condExp_mul_of_aestronglyMeasurable_left
    hthetaMeas.aestronglyMeasurable hthetaSqIntegrable hsquare
  have hbacklogFixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0)
    (hthetaMeas.mul hbacklogField).aestronglyMeasurable hthetaBacklog
  have hthetaFixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0)
    hthetaMeas.aestronglyMeasurable hthetaIntegrable
  have hscaleBacklog := condExp_smul (μ := muE) (m := Fempty)
    (-(15 / 2 : ℝ)) (fun z : Ze => thetaBefore j z * backlogBefore j z)
  have hscaleTheta := condExp_smul (μ := muE) (m := Fempty)
    (16 : ℝ) (fun z : Ze => thetaBefore j z)
  have hshape : (fun z : Ze =>
      thetaBefore j z *
        ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
          (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) =
      ((fun z : Ze =>
          thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) +
        (fun z : Ze => thetaBefore j z * (acceptedA j z) ^ 2)) +
      ((fun z : Ze => (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z)) +
        (fun z : Ze => 16 * thetaBefore j z)) := by
    funext z
    simp only [Pi.add_apply]
    ring_nf
  have hcoeffFunctionEq : (fun z : Ze =>
      thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z) =
      (fun z : Ze => thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ))) *
        acceptedA j := by
    funext z
    rfl
  have hthetaFunctionEq : (fun z : Ze => thetaBefore j z * (acceptedA j z) ^ 2) =
      thetaBefore j * (fun z : Ze => (acceptedA j z) ^ 2) := by
    funext z
    rfl
  have hscaleBacklogFunctionEq : (fun z : Ze =>
      (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z)) =
      (-(15 / 2 : ℝ)) • (fun z : Ze => thetaBefore j z * backlogBefore j z) := by
    funext z
    rfl
  have hscaleThetaFunctionEq : (fun z : Ze => (16 : ℝ) * thetaBefore j z) =
      (16 : ℝ) • thetaBefore j := by
    funext z
    rfl
  have hbacklogFunctionEq : (fun z : Ze => thetaBefore j z * backlogBefore j z) =
      thetaBefore j * (fun z : Ze => backlogBefore j z) := by
    funext z
    rfl
  have hcoeffCondEq := condExp_congr_ae (m := Fempty)
    (ae_of_all muE fun z => congrFun hcoeffFunctionEq z)
  have hthetaCondEq := condExp_congr_ae (m := Fempty)
    (ae_of_all muE fun z => congrFun hthetaFunctionEq z)
  have hscaleBacklogCondEq := condExp_congr_ae (m := Fempty)
    (ae_of_all muE fun z => congrFun hscaleBacklogFunctionEq z)
  have hscaleThetaCondEq := condExp_congr_ae (m := Fempty)
    (ae_of_all muE fun z => congrFun hscaleThetaFunctionEq z)
  have hbacklogCondEq := condExp_congr_ae (m := Fempty)
    (ae_of_all muE fun z => congrFun hbacklogFunctionEq z)
  have hsumFirst := condExp_add hcoeffProductIntegrable hthetaSqIntegrable Fempty
  have hsumLast := condExp_add
    (hthetaBacklog.const_mul (-(15 / 2 : ℝ)))
    (hthetaIntegrable.const_mul 16) Fempty
  have hsumAll := condExp_add
    (hcoeffProductIntegrable.add hthetaSqIntegrable)
    ((hthetaBacklog.const_mul (-(15 / 2 : ℝ))).add
      (hthetaIntegrable.const_mul 16)) Fempty
  filter_upwards [hsumAll, hsumFirst, hsumLast, hcoeffPull, hthetaPull,
    hbacklogFixed, hthetaFixed, hscaleBacklog, hscaleTheta,
    hcoeffCondEq, hthetaCondEq, hscaleBacklogCondEq, hscaleThetaCondEq,
    hbacklogCondEq] with z htotal hfirst hlast hcoeff htheta hsBacklog hsTheta
      hscaleB hscaleT hcoeffBridge hthetaBridge hscaleBacklogBridge
      hscaleThetaBridge hbacklogBridge
  calc
    _ = muE[
        ((fun x : Ze =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
          (fun x : Ze => thetaBefore j x * (acceptedA j x) ^ 2)) +
        ((fun x : Ze => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
          (fun x : Ze => 16 * thetaBefore j x)) | Fempty] z := by rw [hshape]
    _ = (muE[
          (fun x : Ze =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
            (fun x : Ze => thetaBefore j x * (acceptedA j x) ^ 2) | Fempty] +
        muE[
          (fun x : Ze => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
            (fun x : Ze => 16 * thetaBefore j x) | Fempty]) z := htotal
    _ = muE[
          (fun x : Ze =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x) +
            (fun x : Ze => thetaBefore j x * (acceptedA j x) ^ 2) | Fempty] z +
        muE[
          (fun x : Ze => (-(15 / 2 : ℝ)) * (thetaBefore j x * backlogBefore j x)) +
            (fun x : Ze => 16 * thetaBefore j x) | Fempty] z := rfl
    _ = (muE[(fun x : Ze =>
            thetaBefore j x * (2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x)
            | Fempty] +
          muE[(fun x : Ze => thetaBefore j x * (acceptedA j x) ^ 2) | Fempty]) z +
        (muE[(fun x : Ze => (-(15 / 2 : ℝ)) *
            (thetaBefore j x * backlogBefore j x)) | Fempty] +
          muE[(fun x : Ze => 16 * thetaBefore j x) | Fempty]) z := by
      rw [hfirst, hlast]
    _ = thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
          muE[(fun x : Ze => acceptedA j x) | Fempty] z +
        thetaBefore j z * muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z +
        (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
        16 * thetaBefore j z := by
      simp only [Pi.add_apply]
      rw [hcoeffBridge, hthetaBridge, hscaleBacklogBridge, hscaleThetaBridge,
        hcoeff, htheta, hscaleB, hscaleT]
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      rw [hbacklogBridge, hsBacklog, hsTheta]
      simp only [Pi.mul_apply]
      ring_nf

private theorem condExp_driftEnvelope_bound :
    muE[(fun z : Ze => Set.indicator G
      (fun x : Ze =>
        ∑ j : Fin p.K,
          thetaBefore j x *
            ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
              (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16)) z)
      | Fempty] ≤ᵐ[muE]
      Set.indicator G (fun z : Ze =>
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m) := by
  have henvIntegrable := integrable_driftEnvelope rate rewards C_star C_h q t s hs control0
  have hG := measurableSet_G rate rewards C_star C_h q t s hs control0
  have hmask := condExp_indicator henvIntegrable hG
  have hsumCE :
      muE[(fun z : Ze =>
        ∑ j : Fin p.K,
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        | Fempty] =ᵐ[muE]
        (fun z : Ze =>
          ∑ j : Fin p.K,
            muE[(fun x : Ze =>
              thetaBefore j x *
                ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                  (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
              | Fempty] z) := by
    have hpointwise : (fun z : Ze =>
        ∑ j : Fin p.K,
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16)) =
        ∑ j : Fin p.K, fun z : Ze =>
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16) := by
      funext z
      simp only [Finset.sum_apply]
    have hpointwiseAE := ae_of_all muE (fun z => congrFun hpointwise z)
    have hchange := condExp_congr_ae (m := Fempty) hpointwiseAE
    filter_upwards [hchange,
      (condExp_finsetSum
        (s := Finset.univ)
        (f := fun j : Fin p.K => fun z : Ze =>
          thetaBefore j z *
            ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
              (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        (by
          intro j hj
          exact integrable_armEnvelope rate rewards C_star C_h q t s hs control0 j)
        Fempty)] with z hchange hsum
    simpa only [Finset.sum_apply] using hchange.trans hsum
  have harmEq : ∀ j : Fin p.K,
      muE[(fun z : Ze =>
        thetaBefore j z *
          ((2 * backlogBefore j z + (1 / 2 : ℝ)) * acceptedA j z +
            (acceptedA j z) ^ 2 - (15 / 2 : ℝ) * backlogBefore j z + 16))
        | Fempty] =ᵐ[muE]
        (fun z : Ze =>
          thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
              muE[(fun x : Ze => acceptedA j x) | Fempty] z +
            thetaBefore j z *
              muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z +
            (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
            16 * thetaBefore j z) := by
    intro j
    exact condExp_armEnvelope rate rewards C_star C_h q t s hs control0 j
  have hfirst : ∀ j : Fin p.K,
      muE[(fun z : Ze => acceptedA j z) | Fempty] ≤ᵐ[muE]
        (fun _ : Ze => 1) := by
    intro j
    have hfirstRho :=
      (ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_first_bounds
        rate rewards C_star C_h q t s hs control0 j).2
    filter_upwards [hfirstRho] with z hz
    by_cases hg : z ∈ G
    · have hrho := ReferenceFirstLiveEmptyPendingSourceMoments.rho_bounds
        rate rewards C_star C_h q t s hs control0 j
      have hupper : (G).indicator
          (fun _ : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.rho
            rate rewards C_star C_h q t s hs control0 j) z ≤ 1 := by
        simpa only [Set.indicator_of_mem hg] using hrho.2
      exact hz.trans hupper
    · have hupper : (G).indicator
          (fun _ : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.rho
            rate rewards C_star C_h q t s hs control0 j) z ≤ 1 := by
        simp only [Set.indicator_of_notMem hg]
        norm_num
      exact hz.trans hupper
  have hsquare : ∀ j : Fin p.K,
      muE[(fun z : Ze => (acceptedA j z) ^ 2) | Fempty] ≤ᵐ[muE]
        (Set.indicator G (fun z : Ze => 1 / xiE (xofE z) j)) := by
    intro j
    exact (ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_second_bounds
      rate rewards C_star C_h q t s hs control0 j).2.1.trans
      ((ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_second_bounds
        rate rewards C_star C_h q t s hs control0 j).2.2)
  have hfiniteArmEq : ∀ᵐ z ∂muE, ∀ j : Fin p.K,
      muE[(fun x : Ze =>
        thetaBefore j x *
          ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
            (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
        | Fempty] z =
        thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
            muE[(fun x : Ze => acceptedA j x) | Fempty] z +
          thetaBefore j z *
            muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z +
          (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
          16 * thetaBefore j z :=
    ae_all_iff.mpr harmEq
  have hfiniteFirst : ∀ᵐ z ∂muE, ∀ j : Fin p.K,
      muE[(fun x : Ze => acceptedA j x) | Fempty] z ≤ 1 :=
    ae_all_iff.mpr hfirst
  have hfiniteSquare : ∀ᵐ z ∂muE, ∀ j : Fin p.K,
      muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z ≤
        Set.indicator G (fun x : Ze => 1 / xiE (xofE x) j) z :=
    ae_all_iff.mpr hsquare
  filter_upwards [hmask, hsumCE, hfiniteArmEq, hfiniteFirst, hfiniteSquare]
    with z hmaskAt hsumAt hEqAll hFirstAll hSquareAll
  rw [hmaskAt]
  have hconditionalSum :
      Set.indicator G
        (muE[(fun x : Ze =>
          ∑ j : Fin p.K,
            thetaBefore j x *
              ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16))
          | Fempty]) z =
      Set.indicator G (fun x : Ze =>
        ∑ j : Fin p.K,
          muE[(fun y : Ze =>
            thetaBefore j y *
              ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
                (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
            | Fempty] x) z := by
    by_cases hz : z ∈ G
    · simpa [Set.indicator, hz] using hsumAt
    · simp [Set.indicator, hz]
  rw [hconditionalSum]
  have hindicatorSum (f : Fin p.K → Ze → ℝ) :
      Set.indicator G (fun x : Ze => ∑ j : Fin p.K, f j x) z =
        ∑ j : Fin p.K, Set.indicator G (f j) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
    · simp [Set.indicator, hz]
  rw [hindicatorSum]
  have hArmIneq (j : Fin p.K) :
      Set.indicator G (fun x : Ze =>
        muE[(fun y : Ze =>
          thetaBefore j y *
            ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
              (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
          | Fempty] x) z ≤
      Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / xiE (xofE x) j +
          (33 / 2 : ℝ) * thetaBefore j x) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      have htheta := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
        rate rewards C_star C_h q t s hs control0 j z
      have hb0 := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_nonneg
        rate rewards C_star C_h q t s hs control0 j z
      have hcoef := armCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z
      have hrate := xiEmpty_pos_lower_bound rate rewards C_star C_h q t s hs control0 j z
      have hceA := hFirstAll j
      have hceAsq := hSquareAll j
      have hceAsq' :
          muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z ≤
            1 / xiE (xofE z) j := by
        simpa only [Set.indicator_of_mem hz] using hceAsq
      rw [hEqAll j]
      calc
        _ ≤ thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) +
              thetaBefore j z * (1 / xiE (xofE z) j) +
              (-(15 / 2 : ℝ)) * (thetaBefore j z * backlogBefore j z) +
              16 * thetaBefore j z := by
          have hfirstMul :
              thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) *
                  muE[(fun x : Ze => acceptedA j x) | Fempty] z ≤
                thetaBefore j z * (2 * backlogBefore j z + (1 / 2 : ℝ)) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hceA hcoef.1
          have hsquareMul :
              thetaBefore j z *
                  muE[(fun x : Ze => (acceptedA j x) ^ 2) | Fempty] z ≤
                thetaBefore j z * (1 / xiE (xofE z) j) :=
            mul_le_mul_of_nonneg_left hceAsq' htheta.1
          linarith only [hfirstMul, hsquareMul]
        _ = -(11 / 2 : ℝ) * (thetaBefore j z * backlogBefore j z) +
              thetaBefore j z / xiE (xofE z) j +
              (33 / 2 : ℝ) * thetaBefore j z := by ring
    · simp [Set.indicator, hz]
  have hsumIneq :
      (∑ j : Fin p.K, Set.indicator G (fun x : Ze =>
        muE[(fun y : Ze =>
          thetaBefore j y *
            ((2 * backlogBefore j y + (1 / 2 : ℝ)) * acceptedA j y +
              (acceptedA j y) ^ 2 - (15 / 2 : ℝ) * backlogBefore j y + 16))
          | Fempty] x) z) ≤
      ∑ j : Fin p.K, Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / xiE (xofE x) j +
          (33 / 2 : ℝ) * thetaBefore j x) z :=
    Finset.sum_le_sum fun j hj => hArmIneq j
  have htargetIndicator :
      Set.indicator G (fun x : Ze =>
        ∑ j : Fin p.K,
          (-(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
            thetaBefore j x / xiE (xofE x) j +
            (33 / 2 : ℝ) * thetaBefore j x)) z =
      ∑ j : Fin p.K, Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / xiE (xofE x) j +
          (33 / 2 : ℝ) * thetaBefore j x) z := hindicatorSum _
  have hweightedBacklog :
      (∑ j : Fin p.K, thetaBefore j z * backlogBefore j z) =
        weightedBacklogBefore z := by
    unfold ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
      RecordedWeightedDrift.weightedBacklog
    apply Finset.sum_congr rfl
    intro j hj
    rw [ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_eq_normalized
      rate rewards C_star C_h q t s hs control0 j z]
    rfl
  have hthetaSum := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.sum_thetaBefore_eq_m
    rate rewards C_star C_h q t s hs control0 z
  have hterms :
      (∑ j : Fin p.K,
        (-(11 / 2 : ℝ) * (thetaBefore j z * backlogBefore j z) +
          thetaBefore j z / xiE (xofE z) j +
          (33 / 2 : ℝ) * thetaBefore j z)) =
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m := by
    unfold markerRateWeightSum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hweightedBacklog, hthetaSum]
  calc
    _ ≤ ∑ j : Fin p.K, Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
          thetaBefore j x / xiE (xofE x) j +
          (33 / 2 : ℝ) * thetaBefore j x) z := hsumIneq
    _ = Set.indicator G (fun x : Ze =>
        ∑ j : Fin p.K,
          (-(11 / 2 : ℝ) * (thetaBefore j x * backlogBefore j x) +
            thetaBefore j x / xiE (xofE x) j +
            (33 / 2 : ℝ) * thetaBefore j x)) z := htargetIndicator.symm
    _ = Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z := by
      by_cases hz : z ∈ G
      · simpa [Set.indicator, hz] using hterms
      · simp [Set.indicator, hz]

/-- The conditional expectation of the actual empty-branch potential
difference is bounded under the original measure by the actual canonical
rate sum. The enabled first overflow update remains in the post potential. -/
theorem potential_drift_conditional_rate_sum :
    muE[(fun z : Ze => potentialAfter z - potentialBefore z) | Fempty] ≤ᵐ[muE]
      Set.indicator G (fun z : Ze =>
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * p.m) := by
  have hfieldle := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hDifferenceInt :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_potentialDifference
      rate rewards C_star C_h q t s hs control0
  have hEnvelopeInt := integrable_driftEnvelope rate rewards C_star C_h q t s hs control0
  have hDifferenceMaskInt := hDifferenceInt.indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)
  have hEnvelopeMaskInt := hEnvelopeInt.indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)
  have hDifferenceMask : (fun z : Ze => potentialAfter z - potentialBefore z) =ᵐ[muE]
      (fun z : Ze => Set.indicator G
        (fun x : Ze => potentialAfter x - potentialBefore x) z) := by
    filter_upwards [] with z
    by_cases hz : z ∈ G
    · simp [Set.indicator, hz]
    · have hOff :=
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter_eq_potentialBefore_off_G
          rate rewards C_star C_h q t s hs control0 z hz
      simp [Set.indicator, hz, hOff]
  have hpoint : (fun z : Ze => Set.indicator G
      (fun x : Ze => potentialAfter x - potentialBefore x) z) ≤ᵐ[muE]
      (fun z : Ze => Set.indicator G
        (fun x : Ze =>
          ∑ j : Fin p.K,
            thetaBefore j x *
              ((2 * backlogBefore j x + (1 / 2 : ℝ)) * acceptedA j x +
                (acceptedA j x) ^ 2 - (15 / 2 : ℝ) * backlogBefore j x + 16)) z) :=
    ae_of_all muE fun z => by
      by_cases hz : z ∈ G
      · simpa [Set.indicator, hz] using
          (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potential_drift_envelope_indicator
            rate rewards C_star C_h q t s hs control0 z)
      · simp [Set.indicator, hz]
  have hmono := condExp_mono (m := Fempty) hDifferenceMaskInt hEnvelopeMaskInt hpoint
  have hmaskEq := condExp_congr_ae (m := Fempty) hDifferenceMask
  have henvelopeConditional :=
    condExp_driftEnvelope_bound rate rewards C_star C_h q t s hs control0
  exact hmaskEq.trans_le (hmono.trans henvelopeConditional)

/-- Integrating the conditional estimate gives the one-step bound under the
same finite, unnormalized empty-source measure. -/
theorem potential_drift_integral_rate_sum :
    (∫ z : Ze, potentialAfter z - potentialBefore z ∂muE) ≤
      ∫ z : Ze, Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z ∂muE := by
  have hfieldle := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hRhsInt := integrable_driftRateRhs rate rewards C_star C_h q t s hs control0
  have hRhsMaskInt := hRhsInt.indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z : Ze,
        muE[(fun x : Ze => potentialAfter x - potentialBefore x) | Fempty] z ∂muE :=
      (integral_condExp hfieldle).symm
    _ ≤ ∫ z : Ze, Set.indicator G (fun x : Ze =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          markerRateWeightSum rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z ∂muE :=
      integral_mono_ae integrable_condExp hRhsMaskInt
        (potential_drift_conditional_rate_sum rate rewards C_star C_h q t s hs control0)

end Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalWeightedDrift

end
