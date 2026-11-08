/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarWeightedBacklogBound

import Mathlib.Tactic

/-!
# Linear moments of the actual first-live source window

The calendar arrivals below are zero extensions of actual accepted-record
readouts. All branch integrals use the inherited unnormalized source measures.
The incoming inclusion marginal is multiplied before conditional integration.
The comparator lower mean retains its negative floor error.

Sources: `04_slow_fast_learner.tex:140-188,256-264,428-466`,
`06_interruptions.tex:391-397,410-426`, and
`appendix_a_local_protocol.tex:28-64`, under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveOriginalCalendarArrivalMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate
local notation "L" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells rate rewards C_star C_h
local notation "a" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart rate rewards C_star C_h
local notation "u" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt rate rewards C_star C_h
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)

/-- The accepted normalized arrival, extended by zero outside the actual list. -/
def calendarAcceptedArrival (t : Fin p.T) (j : Fin p.K) (omega : SourceInput p) : ℝ :=
  if a omega ≤ t.val then
    match (L omega)[t.val - a omega]? with
    | none => 0
    | some cell =>
        (RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord Q (u t.val omega) cell j) : ℝ) / (rate.n : ℝ)
  else 0

/-- The incoming marginal of the actual score vector at this calendar boundary. -/
def calendarTheta (t : Fin p.T) (j : Fin p.K) (omega : SourceInput p) : ℝ :=
  ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q (u t.val omega)) j

/-- The actual current rate, extended by zero outside the actual window. -/
def calendarRate (t : Fin p.T) (j : Fin p.K) (omega : SourceInput p) : ℝ :=
  if a omega ≤ t.val then
    match (L omega)[t.val - a omega]? with
    | none => 0
    | some cell => cell.rate j
  else 0

/-- The rounded reward ratio from the unchanged whole reward table. -/
def roundedReward (t : Fin p.T) (j : Fin p.K) : ℝ :=
  ((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ)

private theorem integral_predictable_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) [SigmaFinite (μ.trim hF)]
    {w f : Ω → ℝ} (hw : Measurable[F] w) (hbound : ∀ x, ‖w x‖ ≤ 1)
    (hf : Integrable f μ) :
    (∫ x, w x * f x ∂μ) = ∫ x, w x * (μ[f | F]) x ∂μ := by
  have hwμ : AEStronglyMeasurable[mΩ] w μ := (hw.mono hF le_rfl).aestronglyMeasurable
  have hprod : Integrable (fun x => w x * f x) μ :=
    hf.bdd_mul hwμ (Filter.Eventually.of_forall hbound)
  have hce := condExp_mul_of_aestronglyMeasurable_left
    hw.aestronglyMeasurable hprod hf
  exact (integral_condExp (f := fun x => w x * f x) hF).symm.trans (integral_congr_ae hce)

section Nonempty

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Fplus" => ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
  rate rewards C_star C_h q t s hs control0
local notation "G" => ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
  rate rewards C_star C_h q t s hs control0
local notation "theta" => ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
  rate rewards C_star C_h q t s hs control0
local notation "A" => ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
  rate rewards C_star C_h q t s hs control0
local notation "c" => ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
  rate rewards C_star C_h q t s hs control0
local notation "xi" => ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
  rate rewards C_star C_h q t s hs control0

local instance : IsFiniteMeasure muPlus :=
  ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
    rate rewards C_star C_h q t s hs control0

local instance : IsFiniteMeasure ((muPlus).trim
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0)) :=
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
    rate rewards C_star C_h q t s hs control0

private theorem nonempty_theta_norm (j : Fin p.K) (z : Zplus) : ‖theta j z‖ ≤ 1 := by
  have h := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
    rate rewards C_star C_h q t s hs control0 j z
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- The incoming marginal times the actual arrival is integrable on `muPlus`. -/
theorem integrable_nonemptyWeightedArrival (j : Fin p.K) :
    Integrable (fun z : Zplus => theta j z * A j z) muPlus := by
  exact (ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j).bdd_mul
    ((ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (nonempty_theta_norm rate rewards C_star C_h q t s hs control0 j))

private theorem integrable_nonemptyCoefficient (j : Fin p.K) :
    Integrable ((G).indicator (c j)) muPlus := by
  have hmeas := (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_firstCoefficientPlus
    rate rewards C_star C_h q t s hs control0 j).mono
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0) le_rfl
  have hbound : ∀ z : Zplus, ‖c j z‖ ≤ 1 := by
    intro z
    have h := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
      rate rewards C_star C_h q t s hs control0 j z
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.2.1.trans h.2.2.2
  exact (Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hbound)).indicator
    ((ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0) _
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
        rate rewards C_star C_h q t s hs control0))

private theorem integrable_nonemptyWeightedCoefficient (j : Fin p.K) :
    Integrable (fun z : Zplus => theta j z * (G).indicator (c j) z) muPlus := by
  exact (integrable_nonemptyCoefficient rate rewards C_star C_h q t s hs control0 j).bdd_mul
    ((ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (nonempty_theta_norm rate rewards C_star C_h q t s hs control0 j))

/-- Conditional integration retains the actual incoming marginal coefficient. -/
theorem integral_nonemptyWeightedArrival_eq (j : Fin p.K) :
    (∫ z : Zplus, theta j z * A j z ∂muPlus) =
      ∫ z : Zplus, theta j z * (G).indicator (c j) z ∂muPlus := by
  rw [integral_predictable_mul
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0)
    (ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j)
    (nonempty_theta_norm rate rewards C_star C_h q t s hs control0 j)
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j)]
  apply integral_congr_ae
  filter_upwards [ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 j] with z hz
  rw [hz]

/-- The nonempty contribution is at most `m` times its retained branch mass. -/
theorem integral_nonemptyWeightedArrival_le :
    (∫ z : Zplus, ∑ j : Fin p.K, theta j z * A j z ∂muPlus) ≤
      (p.m : ℝ) * (muPlus).real G := by
  have hG : MeasurableSet G :=
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0) _
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
        rate rewards C_star C_h q t s hs control0)
  rw [integral_finsetSum _ (fun j _ =>
    integrable_nonemptyWeightedArrival rate rewards C_star C_h q t s hs control0 j)]
  simp_rw [integral_nonemptyWeightedArrival_eq rate rewards C_star C_h q t s hs control0]
  rw [← integral_finsetSum _ (fun j _ =>
    integrable_nonemptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j)]
  calc
    _ ≤ ∫ z : Zplus, (G).indicator (fun _ => (p.m : ℝ)) z ∂muPlus := by
      apply integral_mono
        (integrable_finsetSum _ (fun j _ =>
          integrable_nonemptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j))
        ((integrable_const (p.m : ℝ)).indicator hG)
      intro z
      by_cases hz : z ∈ G
      · simp only [Set.indicator_of_mem hz]
        calc
          _ ≤ ∑ j : Fin p.K, theta j z * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have htheta := ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
              rate rewards C_star C_h q t s hs control0 j z
            have hc := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
              rate rewards C_star C_h q t s hs control0 j z
            exact mul_le_mul_of_nonneg_left (hc.2.2.1.trans hc.2.2.2) htheta.1
          _ = (p.m : ℝ) := by
            simpa only [mul_one] using
              ReferenceFirstLiveQueueEnergyEnvelope.sum_thetaBefore_eq_m
                rate rewards C_star C_h q t s hs control0 z
      · simp [Set.indicator_of_notMem hz]
    _ = (p.m : ℝ) * (muPlus).real G := by
      rw [integral_indicator_const _ hG]
      simp only [smul_eq_mul, mul_comm]

private theorem nonempty_measurableSet_G : MeasurableSet G :=
  ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0

private theorem integrable_nonemptyTheta (j : Fin p.K) :
    Integrable (theta j) muPlus := by
  exact Integrable.of_bound
    ((ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall
      (nonempty_theta_norm rate rewards C_star C_h q t s hs control0 j))

/-- Integrability of the literal raw comparator gap on the continuing branch. -/
theorem integrable_nonemptyRawGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun z : Zplus => (∑ j ∈ S.val, A j z) -
      ∑ j : Fin p.K, theta j z * A j z) muPlus := by
  exact (integrable_finsetSum _ (fun j _ =>
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j)).sub
    (integrable_finsetSum _ (fun j _ =>
      integrable_nonemptyWeightedArrival rate rewards C_star C_h q t s hs control0 j))

/-- The exact floor loss remains a separate integrable observable. -/
theorem integrable_nonemptyFloorLoss (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((G).indicator (fun z : Zplus => ∑ j ∈ S.val, xi j z / scale)) muPlus := by
  apply Integrable.indicator _
    (nonempty_measurableSet_G rate rewards C_star C_h q t s hs control0)
  apply integrable_finsetSum
  intro j hj
  apply Integrable.div_const
  apply Integrable.of_bound
    ((ReferenceFirstLiveAllArmPrefixAdaptation.measurable_markerRatePlus
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable 1
  filter_upwards [] with z
  have h := ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus_bounds
    rate rewards C_star C_h q t s hs control0 j z
  simpa only [Real.norm_eq_abs, abs_of_nonneg (h.1.le.trans h.2.1)] using h.2.2

/-- Rounded comparator integrability uses only the bounded incoming marginals. -/
theorem integrable_nonemptyRoundedGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((G).indicator (fun z : Zplus =>
      (∑ j ∈ S.val, roundedReward rewards t j) -
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j)) muPlus := by
  apply Integrable.indicator _
    (nonempty_measurableSet_G rate rewards C_star C_h q t s hs control0)
  exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ =>
    (integrable_nonemptyTheta rate rewards C_star C_h q t s hs control0 j).mul_const _))

/-- The branch comparison keeps the exact positive floor-loss integral. -/
theorem integral_nonemptyRoundedGap_le_raw (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : Zplus, (G).indicator (fun z =>
      (∑ j ∈ S.val, roundedReward rewards t j) -
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j) z ∂muPlus) ≤
      (∫ z : Zplus, (∑ j ∈ S.val, A j z) -
        ∑ j : Fin p.K, theta j z * A j z ∂muPlus) +
      ∫ z : Zplus, (G).indicator (fun z => ∑ j ∈ S.val, xi j z / scale) z ∂muPlus := by
  have hci := fun j => integrable_nonemptyCoefficient rate rewards C_star C_h q t s hs control0 j
  have hwci := fun j => integrable_nonemptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j
  have hai := fun j => ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hwai := fun j => integrable_nonemptyWeightedArrival rate rewards C_star C_h q t s hs control0 j
  have hmean (j : Fin p.K) : (∫ z : Zplus, A j z ∂muPlus) =
      ∫ z : Zplus, (G).indicator (c j) z ∂muPlus := by
    exact (integral_condExp (f := A j)
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0)).symm.trans
      (integral_congr_ae
        (ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_firstMoment
          rate rewards C_star C_h q t s hs control0 j))
  have hraw : (∫ z : Zplus, (∑ j ∈ S.val, A j z) -
        ∑ j : Fin p.K, theta j z * A j z ∂muPlus) =
      ∫ z : Zplus, (∑ j ∈ S.val, (G).indicator (c j) z) -
        ∑ j : Fin p.K, theta j z * (G).indicator (c j) z ∂muPlus := by
    rw [integral_sub (integrable_finsetSum _ (fun j _ => hai j))
      (integrable_finsetSum _ (fun j _ => hwai j)),
      integral_sub (integrable_finsetSum _ (fun j _ => hci j))
      (integrable_finsetSum _ (fun j _ => hwci j)),
      integral_finsetSum _ (fun j _ => hai j), integral_finsetSum _ (fun j _ => hci j),
      integral_finsetSum _ (fun j _ => hwai j), integral_finsetSum _ (fun j _ => hwci j)]
    simp_rw [hmean, integral_nonemptyWeightedArrival_eq rate rewards C_star C_h q t s hs control0]
  have hcoeff : Integrable (fun z : Zplus => (∑ j ∈ S.val, (G).indicator (c j) z) -
      ∑ j : Fin p.K, theta j z * (G).indicator (c j) z) muPlus :=
    (integrable_finsetSum _ (fun j _ => hci j)).sub
      (integrable_finsetSum _ (fun j _ => hwci j))
  rw [hraw, ← integral_add hcoeff
    (integrable_nonemptyFloorLoss rate rewards C_star C_h q t s hs control0 S)]
  apply integral_mono
    (integrable_nonemptyRoundedGap rate rewards C_star C_h q t s hs control0 S)
    (((integrable_finsetSum _ (fun j _ => hci j)).sub
      (integrable_finsetSum _ (fun j _ => hwci j))).add
      (integrable_nonemptyFloorLoss rate rewards C_star C_h q t s hs control0 S))
  intro z
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hz : z ∈ G
  · simp only [Set.indicator_of_mem hz]
    have hlower : (∑ j ∈ S.val, (roundedReward rewards t j - xi j z / scale)) ≤
        ∑ j ∈ S.val, c j z := by
      apply Finset.sum_le_sum
      intro j hj
      exact (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
        rate rewards C_star C_h q t s hs control0 j z).2.1
    have hupper : (∑ j : Fin p.K, theta j z * c j z) ≤
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.2.1
        (ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
          rate rewards C_star C_h q t s hs control0 j z).1
    rw [Finset.sum_sub_distrib] at hlower
    linarith
  · simp [Set.indicator_of_notMem hz]

end Nonempty

section Empty

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muE" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "Fempty" => ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
  rate rewards C_star C_h q t s hs control0
local notation "G" => ReferenceFirstLiveEmptyPendingAcceptedMoments.G
  rate rewards C_star C_h q t s hs control0
local notation "theta" => ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
  rate rewards C_star C_h q t s hs control0
local notation "A" => ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
  rate rewards C_star C_h q t s hs control0
local notation "c" => ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient
  rate rewards C_star C_h q t s hs control0
local notation "xi" => fun (j : Fin p.K) (z : Ze) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z) j

private theorem empty_theta_norm (j : Fin p.K) (z : Ze) : ‖theta j z‖ ≤ 1 := by
  have h := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
    rate rewards C_star C_h q t s hs control0 j z
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- The incoming marginal times the actual arrival is integrable on `muE`. -/
theorem integrable_emptyWeightedArrival (j : Fin p.K) :
    Integrable (fun z : Ze => theta j z * A j z) muE := by
  exact (ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j).bdd_mul
    ((ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (empty_theta_norm rate rewards C_star C_h q t s hs control0 j))

private theorem integrable_emptyCoefficient (j : Fin p.K) :
    Integrable ((G).indicator (c j)) muE := by
  have hmeas := (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurable_firstCoefficient
    rate rewards C_star C_h q t s hs control0 j).mono
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) le_rfl
  have hbound : ∀ z : Ze, ‖c j z‖ ≤ 1 := by
    intro z
    have h := ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
      rate rewards C_star C_h q t s hs control0 j z
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.2.1] using h.2.2.1.trans h.2.2.2
  exact (Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hbound)).indicator
    ((ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) _
      (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G
        rate rewards C_star C_h q t s hs control0))

private theorem integrable_emptyWeightedCoefficient (j : Fin p.K) :
    Integrable (fun z : Ze => theta j z * (G).indicator (c j) z) muE := by
  exact (integrable_emptyCoefficient rate rewards C_star C_h q t s hs control0 j).bdd_mul
    ((ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (empty_theta_norm rate rewards C_star C_h q t s hs control0 j))

/-- Conditional integration retains the actual incoming marginal coefficient. -/
theorem integral_emptyWeightedArrival_eq (j : Fin p.K) :
    (∫ z : Ze, theta j z * A j z ∂muE) =
      ∫ z : Ze, theta j z * (G).indicator (c j) z ∂muE := by
  rw [integral_predictable_mul
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0)
    (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j)
    (empty_theta_norm rate rewards C_star C_h q t s hs control0 j)
    (ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j)]
  apply integral_congr_ae
  filter_upwards [ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 j] with z hz
  rw [hz]

/-- The empty contribution is at most `m` times its retained branch mass. -/
theorem integral_emptyWeightedArrival_le :
    (∫ z : Ze, ∑ j : Fin p.K, theta j z * A j z ∂muE) ≤
      (p.m : ℝ) * (muE).real G := by
  have hG : MeasurableSet G :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) _
      (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G
        rate rewards C_star C_h q t s hs control0)
  rw [integral_finsetSum _ (fun j _ =>
    integrable_emptyWeightedArrival rate rewards C_star C_h q t s hs control0 j)]
  simp_rw [integral_emptyWeightedArrival_eq rate rewards C_star C_h q t s hs control0]
  rw [← integral_finsetSum _ (fun j _ =>
    integrable_emptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j)]
  calc
    _ ≤ ∫ z : Ze, (G).indicator (fun _ => (p.m : ℝ)) z ∂muE := by
      apply integral_mono
        (integrable_finsetSum _ (fun j _ =>
          integrable_emptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j))
        ((integrable_const (p.m : ℝ)).indicator hG)
      intro z
      by_cases hz : z ∈ G
      · simp only [Set.indicator_of_mem hz]
        calc
          _ ≤ ∑ j : Fin p.K, theta j z * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have htheta := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
              rate rewards C_star C_h q t s hs control0 j z
            have hc := ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
              rate rewards C_star C_h q t s hs control0 j z
            exact mul_le_mul_of_nonneg_left (hc.2.2.1.trans hc.2.2.2) htheta.1
          _ = (p.m : ℝ) := by
            simpa only [mul_one] using
              ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.sum_thetaBefore_eq_m
                rate rewards C_star C_h q t s hs control0 z
      · simp [Set.indicator_of_notMem hz]
    _ = (p.m : ℝ) * (muE).real G := by
      rw [integral_indicator_const _ hG]
      simp only [smul_eq_mul, mul_comm]

private theorem empty_measurableSet_G : MeasurableSet G :=
  ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
    rate rewards C_star C_h q t s hs control0

private theorem integrable_emptyTheta (j : Fin p.K) :
    Integrable (theta j) muE := by
  exact Integrable.of_bound
    ((ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall
      (empty_theta_norm rate rewards C_star C_h q t s hs control0 j))

/-- Integrability of the literal raw comparator gap on the continuing branch. -/
theorem integrable_emptyRawGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun z : Ze => (∑ j ∈ S.val, A j z) -
      ∑ j : Fin p.K, theta j z * A j z) muE := by
  exact (integrable_finsetSum _ (fun j _ =>
    ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j)).sub
    (integrable_finsetSum _ (fun j _ =>
      integrable_emptyWeightedArrival rate rewards C_star C_h q t s hs control0 j))

/-- The exact floor loss remains a separate integrable observable. -/
theorem integrable_emptyFloorLoss (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((G).indicator (fun z : Ze => ∑ j ∈ S.val, xi j z / scale)) muE := by
  apply Integrable.indicator _
    (empty_measurableSet_G rate rewards C_star C_h q t s hs control0)
  apply integrable_finsetSum
  intro j hj
  apply Integrable.div_const
  apply Integrable.of_bound
    ((ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty_source
      rate rewards C_star C_h q t s hs control0 j).mono
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0) le_rfl).aestronglyMeasurable 1
  filter_upwards [] with z
  have hpos := (ReferenceFirstLiveEmptyPendingSourceMoments.xi_bounds
    rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z) j).1
  let payload := (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
    rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z)).view.payload
  have hsum := CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
    payload.anchor payload.anchor_pos
  have hle := Finset.single_le_sum
    (s := Finset.univ) (f := fun i => CanonicalRecordingRates.xi p rate.eta.val payload.anchor i)
    (fun i _ => (CanonicalRecordingRates.xi_pos p rate.eta.property payload.anchor i).le)
    (Finset.mem_univ j)
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact hle.trans hsum

/-- Rounded comparator integrability uses only the bounded incoming marginals. -/
theorem integrable_emptyRoundedGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((G).indicator (fun z : Ze =>
      (∑ j ∈ S.val, roundedReward rewards t j) -
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j)) muE := by
  apply Integrable.indicator _
    (empty_measurableSet_G rate rewards C_star C_h q t s hs control0)
  exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ =>
    (integrable_emptyTheta rate rewards C_star C_h q t s hs control0 j).mul_const _))

/-- The branch comparison keeps the exact positive floor-loss integral. -/
theorem integral_emptyRoundedGap_le_raw (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : Ze, (G).indicator (fun z =>
      (∑ j ∈ S.val, roundedReward rewards t j) -
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j) z ∂muE) ≤
      (∫ z : Ze, (∑ j ∈ S.val, A j z) -
        ∑ j : Fin p.K, theta j z * A j z ∂muE) +
      ∫ z : Ze, (G).indicator (fun z => ∑ j ∈ S.val, xi j z / scale) z ∂muE := by
  have hci := fun j => integrable_emptyCoefficient rate rewards C_star C_h q t s hs control0 j
  have hwci := fun j => integrable_emptyWeightedCoefficient rate rewards C_star C_h q t s hs control0 j
  have hai := fun j => ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hwai := fun j => integrable_emptyWeightedArrival rate rewards C_star C_h q t s hs control0 j
  have hmean (j : Fin p.K) : (∫ z : Ze, A j z ∂muE) =
      ∫ z : Ze, (G).indicator (c j) z ∂muE := by
    exact (integral_condExp (f := A j)
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
        rate rewards C_star C_h q t s hs control0)).symm.trans
      (integral_congr_ae
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_firstMoment
          rate rewards C_star C_h q t s hs control0 j))
  have hraw : (∫ z : Ze, (∑ j ∈ S.val, A j z) -
        ∑ j : Fin p.K, theta j z * A j z ∂muE) =
      ∫ z : Ze, (∑ j ∈ S.val, (G).indicator (c j) z) -
        ∑ j : Fin p.K, theta j z * (G).indicator (c j) z ∂muE := by
    rw [integral_sub (integrable_finsetSum _ (fun j _ => hai j))
      (integrable_finsetSum _ (fun j _ => hwai j)),
      integral_sub (integrable_finsetSum _ (fun j _ => hci j))
      (integrable_finsetSum _ (fun j _ => hwci j)),
      integral_finsetSum _ (fun j _ => hai j), integral_finsetSum _ (fun j _ => hci j),
      integral_finsetSum _ (fun j _ => hwai j), integral_finsetSum _ (fun j _ => hwci j)]
    simp_rw [hmean, integral_emptyWeightedArrival_eq rate rewards C_star C_h q t s hs control0]
  have hcoeff : Integrable (fun z : Ze => (∑ j ∈ S.val, (G).indicator (c j) z) -
      ∑ j : Fin p.K, theta j z * (G).indicator (c j) z) muE :=
    (integrable_finsetSum _ (fun j _ => hci j)).sub
      (integrable_finsetSum _ (fun j _ => hwci j))
  rw [hraw, ← integral_add hcoeff
    (integrable_emptyFloorLoss rate rewards C_star C_h q t s hs control0 S)]
  apply integral_mono
    (integrable_emptyRoundedGap rate rewards C_star C_h q t s hs control0 S)
    (((integrable_finsetSum _ (fun j _ => hci j)).sub
      (integrable_finsetSum _ (fun j _ => hwci j))).add
      (integrable_emptyFloorLoss rate rewards C_star C_h q t s hs control0 S))
  intro z
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases hz : z ∈ G
  · simp only [Set.indicator_of_mem hz]
    have hlower : (∑ j ∈ S.val, (roundedReward rewards t j - xi j z / scale)) ≤
        ∑ j ∈ S.val, c j z := by
      apply Finset.sum_le_sum
      intro j hj
      exact (ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
        rate rewards C_star C_h q t s hs control0 j z).1
    have hupper : (∑ j : Fin p.K, theta j z * c j z) ≤
        ∑ j : Fin p.K, theta j z * roundedReward rewards t j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.2.1
        (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
          rate rewards C_star C_h q t s hs control0 j z).1
    rw [Finset.sum_sub_distrib] at hlower
    linarith
  · simp [Set.indicator_of_notMem hz]

end Empty


section Readouts

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "cells" => ReferenceFirstLiveSourceCellReadout.cells
  rate rewards C_star C_h q t s hs control0
local notation "cell" => ReferenceFirstLiveSourceCellReadout.cell
  rate rewards C_star C_h q t s hs control0
local notation "ecells" => ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
  rate rewards C_star C_h q t s hs control0
local notation "ecell" => ReferenceFirstLiveEmptyPendingSourceMoments.cell
  rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s

private theorem stratum_start (z : Z) : a z.val = s := by
  exact z.property.2.2

/-- The calendar past and the accepted nonempty-branch past are the same run. -/
theorem calendarRunAt_nonempty (z : Zplus) :
    u t.val z.val.val = RecordedQueueRun.run Q ((cells z).take n) := by
  unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
  rw [stratum_start rate rewards C_star C_h q t s hs z.val]
  exact congrArg (RecordedQueueRun.run Q)
    ((ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum_prefix
      rate rewards C_star C_h q t s hs z.val n (by omega)).trans
      (congrArg (List.take n)
        (ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_eq_sourceCells
          rate rewards C_star C_h q t s hs control0 z)))

private theorem calendarCell_nonempty (z : Zplus) :
    (L z.val.val)[n]? = some (cell z).input := by
  have h := congrArg (fun l : List (RecordedQueueRun.RoundInput p.K) => l[n]?)
    (ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum
      rate rewards C_star C_h q t s hs z.val)
  rw [List.getElem?_take_of_lt (by omega),
    ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_eq_sourceCells
      rate rewards C_star C_h q t s hs control0 z] at h
  have hidx : n < (cells z).length := by
    rw [ReferenceFirstLiveSourceCellReadout.cells_length]
    unfold ReferenceFirstLiveSourceCellReadout.sourceCurrentCount
    omega
  rw [List.getElem?_eq_getElem hidx, ReferenceFirstLiveSourceCellReadout.cells_current] at h
  exact h

/-- Actual accepted arrivals agree on the same original nonempty source point. -/
theorem calendarAcceptedArrival_nonempty (j : Fin p.K) (z : Zplus) :
    calendarAcceptedArrival rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
        rate rewards C_star C_h q t s hs control0 j z := by
  unfold calendarAcceptedArrival
  rw [stratum_start rate rewards C_star C_h q t s hs z.val, ite_eq_left hs,
    calendarCell_nonempty rate rewards C_star C_h q t s hs control0 z,
    calendarRunAt_nonempty rate rewards C_star C_h q t s hs control0 z]
  unfold ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
  rw [rate.n_scale]
  rfl

/-- The current calendar marginal is the existing predictable incoming marginal. -/
theorem calendarTheta_nonempty (j : Fin p.K) (z : Zplus) :
    calendarTheta rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  unfold calendarTheta
  rw [calendarRunAt_nonempty rate rewards C_star C_h q t s hs control0 z]
  rfl

/-- The calendar rate is the inherited marker rate, without dropping any arm. -/
theorem calendarRate_nonempty (j : Fin p.K) (z : Zplus) :
    calendarRate rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
        rate rewards C_star C_h q t s hs control0 j z := by
  unfold calendarRate
  rw [stratum_start rate rewards C_star C_h q t s hs z.val, ite_eq_left hs,
    calendarCell_nonempty rate rewards C_star C_h q t s hs control0 z]
  exact (ReferenceFirstLiveSourceCellReadout.source_current_cell_fields
    rate rewards C_star C_h q t s hs control0 z).2.2.1 j

private theorem empty_sourceCells (z : Ze) :
    ReferenceFirstLiveBranchIntegralTransport.actualSourceCells rate rewards C_star C_h q t s hs z.val =
      ecells z := by
  unfold ReferenceFirstLiveBranchIntegralTransport.actualSourceCells
    ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
  congr 1

/-- The calendar past is the existing empty-pending past, including its stop flag. -/
theorem calendarRunAt_empty (z : Ze) :
    u t.val z.val.val = ReferenceFirstLiveEmptyPendingAcceptedMoments.past
      rate rewards C_star C_h q t s hs control0 z := by
  unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
  rw [stratum_start rate rewards C_star C_h q t s hs z.val]
  have h := ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum_prefix
    rate rewards C_star C_h q t s hs z.val n (by omega)
  rw [empty_sourceCells rate rewards C_star C_h q t s hs control0 z] at h
  change RecordedQueueRun.run Q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take n) = _
  rw [h]
  exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take
    rate rewards C_star C_h q t s hs control0 z).symm

private theorem calendarCell_empty (z : Ze) : (L z.val.val)[n]? = some (ecell z) := by
  have h := congrArg (fun l : List (RecordedQueueRun.RoundInput p.K) => l[n]?)
    (ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum
      rate rewards C_star C_h q t s hs z.val)
  rw [List.getElem?_take_of_lt (by omega),
    empty_sourceCells rate rewards C_star C_h q t s hs control0 z] at h
  have hlen : (ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells
      rate rewards C_star C_h q t s hs control0 z).length = n := by
    have heq := congrArg List.length
      (ReferenceFirstLiveEmptyPendingSourceMoments.actualCells_eq_past_append_cell
        rate rewards C_star C_h q t s hs control0 z)
    rw [ReferenceFirstLiveEmptyPendingSourceMoments.actualCells_length] at heq
    simp only [List.length_append, List.length_singleton] at heq
    omega
  rw [ReferenceFirstLiveEmptyPendingSourceMoments.actualCells_eq_past_append_cell,
    List.getElem?_append_right (by omega), hlen, Nat.sub_self] at h
  exact h

/-- Actual accepted arrivals agree on the original empty-pending source point. -/
theorem calendarAcceptedArrival_empty (j : Fin p.K) (z : Ze) :
    calendarAcceptedArrival rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
        rate rewards C_star C_h q t s hs control0 j z := by
  unfold calendarAcceptedArrival
  rw [stratum_start rate rewards C_star C_h q t s hs z.val, ite_eq_left hs,
    calendarCell_empty rate rewards C_star C_h q t s hs control0 z,
    calendarRunAt_empty rate rewards C_star C_h q t s hs control0 z]
  unfold ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
  rw [rate.n_scale]
  rfl

/-- The empty-pending calendar marginal is the incoming predictable coefficient. -/
theorem calendarTheta_empty (j : Fin p.K) (z : Ze) :
    calendarTheta rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  unfold calendarTheta
  rw [calendarRunAt_empty rate rewards C_star C_h q t s hs control0 z]
  rfl

/-- The empty-pending calendar rate is the actual selected payload rate. -/
theorem calendarRate_empty (j : Fin p.K) (z : Ze) :
    calendarRate rate rewards C_star C_h t j z.val.val =
      ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
          rate rewards C_star C_h q t s hs control0 z) j := by
  unfold calendarRate
  rw [stratum_start rate rewards C_star C_h q t s hs z.val, ite_eq_left hs,
    calendarCell_empty rate rewards C_star C_h q t s hs control0 z]
  exact congrFun (ReferenceFirstLiveEmptyPendingSourceMoments.cell_actual_facts
    rate rewards C_star C_h q t s hs control0 z).2.2.1 j

end Readouts


private theorem retained_iff_of_actualCell (t : Fin p.T) (omega : SourceInput p)
    (cell : RecordedQueueRun.RoundInput p.K)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true)
    (hstart : a omega ≤ t.val) (hcell : (L omega)[t.val - a omega]? = some cell)
    (henabled : cell.enabled = true) :
    omega ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t ↔ (u t.val omega).overflow = false := by
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp hcell
  constructor
  · exact fun h => h.2.2.choose_spec.2
  · intro hsafe
    exact ⟨hc, hstart, hidx, hget ▸ henabled, hsafe⟩

/-- The retained calendar mask is precisely the accepted nonempty strict past. -/
theorem calendarRetained_nonempty
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t s hs control0) :
    z.val.val ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t ↔
    z ∈ ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
      rate rewards C_star C_h q t s hs control0 := by
  have hstart := stratum_start rate rewards C_star C_h q t s hs z.val
  rw [retained_iff_of_actualCell rate rewards C_star C_h t z.val.val
    (ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0 z).input
    z.val.property.2.1 (by simpa only [hstart] using hs) (by
      rw [hstart]
      exact calendarCell_nonempty rate rewards C_star C_h q t s hs control0 z)
    (ReferenceFirstLiveAllArmAcceptedConditionalMoments.currentCell_enabled
      rate rewards C_star C_h q t s hs control0 z),
    calendarRunAt_nonempty rate rewards C_star C_h q t s hs control0 z]
  rfl

/-- The empty-pending retained mask tests the same incoming queue flag. -/
theorem calendarRetained_empty
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    z.val.val ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t ↔
    z ∈ ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0 := by
  have hstart := stratum_start rate rewards C_star C_h q t s hs z.val
  rw [retained_iff_of_actualCell rate rewards C_star C_h t z.val.val
    (ReferenceFirstLiveEmptyPendingSourceMoments.cell rate rewards C_star C_h q t s hs control0 z)
    z.val.property.2.1 (by simpa only [hstart] using hs) (by
      rw [hstart]
      exact calendarCell_empty rate rewards C_star C_h q t s hs control0 z)
    (ReferenceFirstLiveEmptyPendingSourceMoments.cell_actual_facts
      rate rewards C_star C_h q t s hs control0 z).1,
    calendarRunAt_empty rate rewards C_star C_h q t s hs control0 z]
  rfl

section Birth

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (control0 : TimeControl p)

local notation "Zbirth" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muBirth" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "Y" => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rate rewards C_star C_h q t control0
local notation "firstCell" => ReferenceFirstLaunchCommonUpdateSource.firstCell
  rate rewards C_star C_h q t control0
local notation "theta0" => ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))

private theorem birth_start (z : Zbirth) : a z.val = t.val :=
  ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z

/-- Birth has the actual zero incoming state, without conditioning on positive mass. -/
theorem calendarRunAt_birth (z : Zbirth) : u t.val z.val = RecordedQueueRun.initialState p.K := by
  unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
  rw [birth_start rate rewards C_star C_h q t z, Nat.sub_self]
  rfl

private theorem calendarCell_birth (z : Zbirth) : (L z.val)[0]? = some (firstCell z) := by
  have h := congrArg (fun l : List (RecordedQueueRun.RoundInput p.K) => l[0]?)
    (ReferenceFirstLiveCalendarPrefixReadout.firstWindowBirthCells_take_one
      rate rewards C_star C_h q t control0 z)
  simpa only [List.getElem?_take_of_lt (by omega : 0 < 1), List.getElem?_cons_zero,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using h

/-- The actual birth arrival is exactly the conserved first-update readout. -/
theorem calendarAcceptedArrival_birth (j : Fin p.K) (z : Zbirth) :
    calendarAcceptedArrival rate rewards C_star C_h t j z.val = Y z j := by
  unfold calendarAcceptedArrival
  rw [birth_start rate rewards C_star C_h q t z, ite_eq_left le_rfl, Nat.sub_self,
    calendarCell_birth rate rewards C_star C_h q t control0 z,
    calendarRunAt_birth rate rewards C_star C_h q t z]
  have htotal := (ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h q t control0 z).1 j |>.2.2
  unfold ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rw [htotal, ← rate.n_scale]
  rfl

/-- Birth uses all-one weights and the constant full `m`-marginal. -/
theorem calendarTheta_birth (j : Fin p.K) (z : Zbirth) :
    calendarTheta rate rewards C_star C_h t j z.val = theta0 j := by
  unfold calendarTheta
  rw [calendarRunAt_birth rate rewards C_star C_h q t z]
  rfl

include control0 in
/-- The first cell is retained, including a first update that overflows. -/
theorem calendarRetained_birth (z : Zbirth) :
    z.val ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t := by
  apply (retained_iff_of_actualCell rate rewards C_star C_h t z.val (firstCell z)
    z.property.2.1 (by rw [birth_start rate rewards C_star C_h q t z]) (by
      rw [birth_start rate rewards C_star C_h q t z, Nat.sub_self]
      exact calendarCell_birth rate rewards C_star C_h q t control0 z) rfl).mpr
  rw [calendarRunAt_birth rate rewards C_star C_h q t z]
  rfl

/-- The birth stratum and remainder have the same unnormalized mass. -/
theorem birth_mass_eq_remainder_mass : muBirth Set.univ = muC Set.univ := by
  have h := congrArg (fun μ => μ Set.univ)
    (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h q t control0)
  rw [Measure.map_apply
    (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0) MeasurableSet.univ, Set.preimage_univ] at h
  have hm : ((ContinuousControlSlice.assignmentLaw p.K).prod
      (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p)) Set.univ = 1 := measure_univ
  rw [← Set.univ_prod_univ, Measure.prod_prod, hm, mul_one] at h
  exact h

/-- The original birth first mean, retaining its original branch mass. -/
theorem integral_birthArrival_eq (j : Fin p.K) :
    (∫ z : Zbirth, Y z j ∂muBirth) = (muBirth).real Set.univ *
      (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
        QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
          (roundedReward rewards t j)) := by
  have h := (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ).2.2.2.2.1
  simp only [Set.mem_univ, and_self, Set.ofPred_true, setIntegral_univ, measure_univ,
    ENNReal.toReal_one, mul_one] at h
  rw [Measure.real, birth_mass_eq_remainder_mass rate rewards C_star C_h q t control0]
  exact h.trans (by unfold roundedReward; ring)

/-- The actual incoming weighted birth arrivals are integrable. -/
theorem integrable_birthWeightedArrival :
    Integrable (fun z : Zbirth => ∑ j : Fin p.K, theta0 j * Y z j) muBirth := by
  apply integrable_finsetSum
  intro j hj
  exact ((ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j Set.univ Set.univ
    MeasurableSet.univ MeasurableSet.univ).2.2.1).const_mul _

/-- The birth weighted first mean costs at most `m` times the birth mass. -/
theorem integral_birthWeightedArrival_le :
    (∫ z : Zbirth, ∑ j : Fin p.K, theta0 j * Y z j ∂muBirth) ≤
      (p.m : ℝ) * (muBirth).real Set.univ := by
  rw [integral_finsetSum _ (fun j _ =>
    ((ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1).const_mul (theta0 j))]
  simp_rw [integral_const_mul, integral_birthArrival_eq rate rewards C_star C_h q t control0]
  calc
    _ ≤ ∑ j : Fin p.K, theta0 j * (muBirth).real Set.univ := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
        rate rewards t j
      have hr := ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus_bounds rewards t j
      have ht : 0 ≤ theta0 j := (ProductSetLaw.theta_pos (fun _ => 1) j
        (ConstructorDimensions.m_pos p) p.m_lt_K (by intro i; norm_num)).le
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (measureReal_nonneg) (hc.2.1.trans hr.2)) ht
    _ = (p.m : ℝ) * (muBirth).real Set.univ := by
      rw [← Finset.sum_mul, ProductSetLaw.sum_theta_eq_card]
      · exact ConstructorDimensions.m_pos p
      · exact p.m_lt_K
      · intro i
        norm_num

include control0 in
/-- The actual first-cell rate uses the same all-one launch anchor. -/
theorem calendarRate_birth (j : Fin p.K) (z : Zbirth) :
    calendarRate rate rewards C_star C_h t j z.val =
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j := by
  unfold calendarRate
  rw [birth_start rate rewards C_star C_h q t z, ite_eq_left le_rfl, Nat.sub_self,
    calendarCell_birth rate rewards C_star C_h q t control0 z]
  rfl

/-- Both original birth floor signs, with the original unnormalized mass. -/
theorem integral_birthArrival_bounds (j : Fin p.K) :
    (muBirth).real Set.univ * (roundedReward rewards t j -
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j / scale) ≤
      (∫ z : Zbirth, Y z j ∂muBirth) ∧
    (∫ z : Zbirth, Y z j ∂muBirth) ≤ (muBirth).real Set.univ * roundedReward rewards t j := by
  rw [integral_birthArrival_eq rate rewards C_star C_h q t control0 j]
  have h := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds rate rewards t j
  exact ⟨mul_le_mul_of_nonneg_left h.1 measureReal_nonneg,
    mul_le_mul_of_nonneg_left h.2.1 measureReal_nonneg⟩

end Birth


section OriginalMeasure

variable (t : Fin p.T) (control0 : TimeControl p)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t
local notation "BirthZ" => fun q => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muB" => fun q => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "PlusZ" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muP" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "EmptyZ" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muE" => fun q (v : Fin (t.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0

private theorem arrival_zero_on_exception (j : Fin p.K) (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    calendarAcceptedArrival rate rewards C_star C_h t j omega = 0 := by
  rcases h with h | h | h
  · have hL := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega h).2.1
    unfold calendarAcceptedArrival
    simp only [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells, hL,
      List.getElem?_nil, ite_self]
  · have hfuture : t.val < a omega := h.2
    exact ite_eq_right (Nat.not_le_of_lt hfuture)
  · have hlen : (L omega).length ≤ t.val - a omega := by
      exact (ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h omega).trans_le h.2.2
    unfold calendarAcceptedArrival
    rw [List.getElem?_eq_none hlen]
    simp

/-- Gluing actual component integrability and integrals uses the exact original
source decomposition. No global Borel marginal theorem is assumed. -/
private theorem integrate_original_components (f : SourceInput p → ℝ)
    (hzero : ∀ omega, omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5 → f omega = 0)
    (hb : ∀ q, Integrable (fun z : BirthZ q => f z.val) (muB q))
    (hp : ∀ q v, Integrable (fun z : PlusZ q v => f z.val.val) (muP q v))
    (he : ∀ q v, Integrable (fun z : EmptyZ q v => f z.val.val) (muE q v)) :
    Integrable f mu ∧ (∫ omega, f omega ∂mu) =
      (∑ q, ∫ z : BirthZ q, f z.val ∂muB q) +
      ∑ q, ∑ v : Fin (t.val + 1),
        ((∫ z : PlusZ q v, f z.val.val ∂muP q v) +
          ∫ z : EmptyZ q v, f z.val.val ∂muE q v) := by
  let embB q := MeasurableEmbedding.subtype_coe
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
  let embP q (v : Fin (t.val + 1)) :=
    ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let embE q (v : Fin (t.val + 1)) :=
    ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let b q := (muB q).map (Subtype.val : BirthZ q → SourceInput p)
  let c q v := (muP q v).map
    (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
    (muE q v).map (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0)
  have hbi q : Integrable f (b q) := (embB q).integrable_map_iff.mpr (hb q)
  have hpi q v : Integrable f ((muP q v).map
      (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := (embP q v).integrable_map_iff.mpr (hp q v)
  have hei q v : Integrable f ((muE q v).map
      (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
        v.val (Nat.lt_succ_iff.mp v.isLt) control0)) := (embE q v).integrable_map_iff.mpr (he q v)
  have hci q v : Integrable f (c q v) := (hpi q v).add_measure (hei q v)
  have hbs : Integrable f (∑ q, b q) := integrable_finsetSum_measure.mpr (fun q _ => hbi q)
  have hcs q : Integrable f (∑ v, c q v) := integrable_finsetSum_measure.mpr (fun v _ => hci q v)
  have hcss : Integrable f (∑ q, ∑ v, c q v) :=
    integrable_finsetSum_measure.mpr (fun q _ => hcs q)
  have hz (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5) :
      f =ᵐ[(mu).restrict (phase i)] 0 := by
    filter_upwards [ae_restrict_mem
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h t control0 i)] with omega homega
    rcases hi with rfl | rfl | rfl
    · exact hzero omega (Or.inl homega)
    · exact hzero omega (Or.inr (Or.inl homega))
    · exact hzero omega (Or.inr (Or.inr homega))
  have h0 : Integrable f ((mu).restrict (phase 0)) := (integrable_const (0 : ℝ)).congr (hz 0 (by simp)).symm
  have h1 : Integrable f ((mu).restrict (phase 1)) := (integrable_const (0 : ℝ)).congr (hz 1 (by simp)).symm
  have h5 : Integrable f ((mu).restrict (phase 5)) := (integrable_const (0 : ℝ)).congr (hz 5 (by simp)).symm
  have h01 := h0.add_measure h1
  have h015 := h01.add_measure h5
  have h015b := h015.add_measure hbs
  have hdecomp : mu = (mu).restrict (phase 0) + (mu).restrict (phase 1) +
      (mu).restrict (phase 5) + (∑ q, b q) + ∑ q, ∑ v, c q v :=
    ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
      rate rewards C_star C_h t control0
  constructor
  · rw [hdecomp]
    exact h015b.add_measure hcss
  · rw [hdecomp, integral_add_measure h015b hcss, integral_add_measure h015 hbs,
      integral_add_measure h01 h5, integral_add_measure h0 h1,
      integral_congr_ae (hz 0 (by simp)), integral_congr_ae (hz 1 (by simp)),
      integral_congr_ae (hz 5 (by simp))]
    simp only [Pi.zero_apply, integral_zero, zero_add]
    rw [integral_finsetSum_measure (fun q _ => hbi q),
      integral_finsetSum_measure (fun q _ => hcs q)]
    congr 1
    · apply Finset.sum_congr rfl
      intro q hq
      exact (embB q).integral_map f
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_finsetSum_measure (fun v _ => hci q v)]
      apply Finset.sum_congr rfl
      intro v hv
      rw [integral_add_measure (hpi q v) (hei q v)]
      exact congrArg₂ (· + ·) ((embP q v).integral_map f) ((embE q v).integral_map f)

include control0 in
private theorem retained_not_exception (omega : SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    omega ∉ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t := by
  intro hk
  rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
    rate rewards C_star C_h t control0] at hk
  obtain ⟨i, hi, hωi⟩ : ∃ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 5) ∧ omega ∈ phase i := by
    rcases h with h | h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr (Or.inl rfl), h⟩
    · exact ⟨5, Or.inr (Or.inr rfl), h⟩
  obtain ⟨j, hj, hωj⟩ : ∃ j : Fin 6, (j = 2 ∨ j = 3 ∨ j = 4) ∧ omega ∈ phase j := by
    rcases hk.1 with h | h | h
    · exact ⟨2, Or.inl rfl, h⟩
    · exact ⟨3, Or.inr (Or.inl rfl), h⟩
    · exact ⟨4, Or.inr (Or.inr rfl), h⟩
  have hij : i ≠ j := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> decide
  exact Set.disjoint_left.mp
    (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint rate rewards C_star C_h t hij) hωi hωj

include control0 in
/-- The sharp original-calendar first moment and its genuine integrability. -/
theorem calendarWeightedArrival_moments :
    Integrable (fun omega : SourceInput p => ∑ j : Fin p.K,
      calendarTheta rate rewards C_star C_h t j omega *
        calendarAcceptedArrival rate rewards C_star C_h t j omega) mu ∧
    (∫ omega : SourceInput p, ∑ j : Fin p.K,
      calendarTheta rate rewards C_star C_h t j omega *
        calendarAcceptedArrival rate rewards C_star C_h t j omega ∂mu) ≤
      (p.m : ℝ) * (mu).real
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
          rate rewards C_star C_h t) := by
  let f := fun omega : SourceInput p => ∑ j : Fin p.K,
    calendarTheta rate rewards C_star C_h t j omega *
      calendarAcceptedArrival rate rewards C_star C_h t j omega
  let K := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  let g := K.indicator (fun _ : SourceInput p => (p.m : ℝ))
  have hf := integrate_original_components rate rewards C_star C_h t control0 f
    (fun omega h => by
      simp only [f, arrival_zero_on_exception rate rewards C_star C_h t _ omega h, mul_zero,
        Finset.sum_const_zero])
    (fun q => by
      simpa only [f, calendarTheta_birth rate rewards C_star C_h q t,
        calendarAcceptedArrival_birth rate rewards C_star C_h q t control0] using
        integrable_birthWeightedArrival rate rewards C_star C_h q t control0)
    (fun q v => by
      simpa only [f, calendarTheta_nonempty rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0,
        calendarAcceptedArrival_nonempty rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0] using
        integrable_finsetSum Finset.univ (fun j _ => integrable_nonemptyWeightedArrival
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j))
    (fun q v => by
      simpa only [f, calendarTheta_empty rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0,
        calendarAcceptedArrival_empty rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0] using
        integrable_finsetSum Finset.univ (fun j _ => integrable_emptyWeightedArrival
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j))
  have hgb q : Integrable (fun z : BirthZ q => g z.val) (muB q) := by
    simpa only [g, K, Set.indicator, calendarRetained_birth rate rewards C_star C_h q t control0,
      ite_true] using (integrable_const (p.m : ℝ) : Integrable (fun _ : BirthZ q => (p.m : ℝ)) (muB q))
  have hgp q v : Integrable (fun z : PlusZ q v => g z.val.val) (muP q v) := by
    have : IsFiniteMeasure (muP q v) :=
      ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
    convert (integrable_const (μ := muP q v) (p.m : ℝ)).indicator
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) using 1
    funext z
    simp only [g, K, Set.indicator, calendarRetained_nonempty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  have hge q v : Integrable (fun z : EmptyZ q v => g z.val.val) (muE q v) := by
    have : IsFiniteMeasure (muE q v) :=
      ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty_finite
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
    convert (integrable_const (μ := muE q v) (p.m : ℝ)).indicator
      (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) using 1
    funext z
    simp only [g, K, Set.indicator, calendarRetained_empty rate rewards C_star C_h q t
      v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  have hg := integrate_original_components rate rewards C_star C_h t control0 g
    (fun omega h => Set.indicator_of_notMem
      (retained_not_exception rate rewards C_star C_h t control0 omega h) _) hgb hgp hge
  refine ⟨hf.1, ?_⟩
  have hle : (∫ omega, f omega ∂mu) ≤ ∫ omega, g omega ∂mu := by
    rw [hf.2, hg.2]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro q hq
      simpa only [f, g, K, calendarTheta_birth rate rewards C_star C_h q t,
        calendarAcceptedArrival_birth rate rewards C_star C_h q t control0,
        Set.indicator, calendarRetained_birth rate rewards C_star C_h q t control0, ite_true,
        integral_const, smul_eq_mul, mul_comm] using
        integral_birthWeightedArrival_le rate rewards C_star C_h q t control0
    · apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro v hv
      apply add_le_add
      · simpa only [f, g, K, calendarTheta_nonempty rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0,
          calendarAcceptedArrival_nonempty rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0,
          Set.indicator, calendarRetained_nonempty rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0] using
          (integral_nonemptyWeightedArrival_le rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0).trans_eq
            (by
              simpa only [smul_eq_mul, mul_comm, Set.indicator] using
                (integral_indicator_const (μ := muP q v) (p.m : ℝ)
                  (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
                    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0)).symm)
      · simpa only [f, g, K, calendarTheta_empty rate rewards C_star C_h q t v.val
          (Nat.lt_succ_iff.mp v.isLt) control0,
          calendarAcceptedArrival_empty rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0,
          Set.indicator, calendarRetained_empty rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0] using
          (integral_emptyWeightedArrival_le rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0).trans_eq
            (by
              simpa only [smul_eq_mul, mul_comm, Set.indicator] using
                (integral_indicator_const (μ := muE q v) (p.m : ℝ)
                  (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
                    rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0)).symm)
  calc
    _ ≤ ∫ omega, g omega ∂mu := hle
    _ = _ := by
      rw [integral_indicator_const _
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.measurableSet_retainedEnabledEvent
          rate rewards C_star C_h t control0)]
      exact mul_comm _ _

include control0 in
/-- Every actual calendar accepted arrival is integrable under the original law. -/
theorem integrable_calendarAcceptedArrival (j : Fin p.K) :
    Integrable (calendarAcceptedArrival rate rewards C_star C_h t j) mu := by
  exact (integrate_original_components rate rewards C_star C_h t control0
    (calendarAcceptedArrival rate rewards C_star C_h t j)
    (arrival_zero_on_exception rate rewards C_star C_h t j)
    (fun q => by
      simpa only [calendarAcceptedArrival_birth rate rewards C_star C_h q t control0] using
        (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
          rate rewards C_star C_h q t control0 j Set.univ Set.univ
          MeasurableSet.univ MeasurableSet.univ).2.2.1)
    (fun q v => by
      simpa only [calendarAcceptedArrival_nonempty rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0] using
        ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j)
    (fun q v => by
      simpa only [calendarAcceptedArrival_empty rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0] using
        ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 j)).1

include control0 in
/-- The literal original-calendar raw gap is integrable. -/
theorem integrable_calendarRawGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun omega : SourceInput p =>
      (∑ j ∈ S.val, calendarAcceptedArrival rate rewards C_star C_h t j omega) -
      ∑ j : Fin p.K, calendarTheta rate rewards C_star C_h t j omega *
        calendarAcceptedArrival rate rewards C_star C_h t j omega) mu := by
  exact (integrable_finsetSum S.val (fun j _ =>
    integrable_calendarAcceptedArrival rate rewards C_star C_h t control0 j)).sub
    (calendarWeightedArrival_moments rate rewards C_star C_h t control0).1

include control0 in
/-- Integrability of the retained rounded gap comes from its physical components. -/
theorem integrable_calendarRoundedGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t).indicator (fun omega : SourceInput p =>
        (∑ j ∈ S.val, roundedReward rewards t j) -
          ∑ j : Fin p.K, calendarTheta rate rewards C_star C_h t j omega * roundedReward rewards t j)) mu := by
  apply (integrate_original_components rate rewards C_star C_h t control0 _ ?_ ?_ ?_ ?_).1
  · intro omega h
    exact Set.indicator_of_notMem (retained_not_exception rate rewards C_star C_h t control0 omega h) _
  · intro q
    simpa only [Set.indicator, calendarRetained_birth rate rewards C_star C_h q t control0,
      ite_true, calendarTheta_birth rate rewards C_star C_h q t] using
      (integrable_const ((∑ j ∈ S.val, roundedReward rewards t j) -
        ∑ j : Fin p.K, ProductSetLaw.theta p.m (fun _ => 1) j * roundedReward rewards t j) :
        Integrable (fun _ : BirthZ q => _) (muB q))
  · intro q v
    convert integrable_nonemptyRoundedGap rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0 S using 1
    funext z
    simp only [Set.indicator, calendarRetained_nonempty rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0,
      calendarTheta_nonempty rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  · intro q v
    convert integrable_emptyRoundedGap rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0 S using 1
    funext z
    simp only [Set.indicator, calendarRetained_empty rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0,
      calendarTheta_empty rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]

include control0 in
/-- The exact retained floor loss is integrable before any unit-rate relaxation. -/
theorem integrable_calendarFloorLoss (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t).indicator (fun omega : SourceInput p =>
        ∑ j ∈ S.val, calendarRate rate rewards C_star C_h t j omega / scale)) mu := by
  apply (integrate_original_components rate rewards C_star C_h t control0 _ ?_ ?_ ?_ ?_).1
  · intro omega h
    exact Set.indicator_of_notMem (retained_not_exception rate rewards C_star C_h t control0 omega h) _
  · intro q
    simpa only [Set.indicator, calendarRetained_birth rate rewards C_star C_h q t control0,
      ite_true, calendarRate_birth rate rewards C_star C_h q t control0] using
      (integrable_const (∑ j ∈ S.val, CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j / scale) :
        Integrable (fun _ : BirthZ q => _) (muB q))
  · intro q v
    convert integrable_nonemptyFloorLoss rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0 S using 1
    funext z
    simp only [Set.indicator, calendarRetained_nonempty rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0,
      calendarRate_nonempty rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]
  · intro q v
    convert integrable_emptyFloorLoss rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0 S using 1
    funext z
    simp only [Set.indicator, calendarRetained_empty rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0,
      calendarRate_empty rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0]

end OriginalMeasure


/-- The exact actual source list ends by the physical horizon. -/
theorem firstLiveStart_add_length_le_T (omega : SourceInput p) :
    a omega + (L omega).length ≤ p.T := by
  have hs : a omega ≤ p.T :=
    ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate omega rewards C_star C_h).crossing.isSome = true
  · let sf : Fin (p.T + 1) := ⟨a omega, by omega⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h sf.val :=
      ⟨omega, hc, rfl⟩
    have hwhole := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h sf x).2
    have hlen := ReferenceFirstLiveOverflowReadout.firstLiveLength_le_count
      rate rewards C_star C_h sf.val (p.T - sf.val)
      (ReferenceFirstLiveOverflowReadout.maximal_span sf) x
    have hbound : (L omega).length ≤ p.T - a omega := by
      change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h omega).length ≤ p.T - sf.val
      rw [hwhole, ReferenceFirstLiveOverflowReadout.firstLiveCells_length]
      exact hlen
    omega
  · have hL : L omega = [] := by
      rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells, dite_eq_right hc]
    rw [hL, List.length_nil, Nat.add_zero]
    exact hs

/-- Calendar support reindexes to the very same chronological list and run. -/
theorem sum_calendarWeightedArrival_eq_firstWindow (omega : SourceInput p) :
    (∑ t : Fin p.T, ∑ j : Fin p.K, calendarTheta rate rewards C_star C_h t j omega *
      calendarAcceptedArrival rate rewards C_star C_h t j omega) =
    ∑ k : Fin (L omega).length, ∑ j : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m (L omega) k.val j *
        ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
          (RecordedQueueRun.run Q ((L omega).take k.val)) (L omega)[k.val] j) : ℝ) /
            (rate.n : ℝ)) := by
  let f := fun t : Fin p.T => ∑ j : Fin p.K,
    calendarTheta rate rewards C_star C_h t j omega *
      calendarAcceptedArrival rate rewards C_star C_h t j omega
  let kept := Finset.univ.filter (fun t : Fin p.T =>
    a omega ≤ t.val ∧ t.val - a omega < (L omega).length)
  have hrestrict : (∑ t ∈ kept, f t) = ∑ t : Fin p.T, f t := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht hnot
    have hnot' : ¬ (a omega ≤ t.val ∧ t.val - a omega < (L omega).length) := by
      simpa only [kept, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    apply Finset.sum_eq_zero
    intro j hj
    have hz : calendarAcceptedArrival rate rewards C_star C_h t j omega = 0 := by
      unfold calendarAcceptedArrival
      by_cases hstart : a omega ≤ t.val
      · rw [ite_eq_left hstart, List.getElem?_eq_none (by omega)]
      · exact ite_eq_right hstart
    rw [hz, mul_zero]
  rw [← hrestrict]
  apply Finset.sum_bij
    (fun t ht => (⟨t.val - a omega, (Finset.mem_filter.mp ht).2.2⟩ : Fin (L omega).length))
  · intro t ht
    exact Finset.mem_univ _
  · intro t ht v hv heq
    have ht' := (Finset.mem_filter.mp ht).2.1
    have hv' := (Finset.mem_filter.mp hv).2.1
    have heq' := congrArg Fin.val heq
    apply Fin.ext
    dsimp only at heq'
    omega
  · intro k hk
    let t : Fin p.T := ⟨a omega + k.val, by
      have hspan := firstLiveStart_add_length_le_T rate rewards C_star C_h omega
      omega⟩
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        dsimp only [t]
        rw [Nat.add_sub_cancel_left]
        exact ⟨Nat.le_add_right _ _, k.isLt⟩⟩
    · apply Fin.ext
      exact Nat.add_sub_cancel_left _ _
  · intro t ht
    have hstart := (Finset.mem_filter.mp ht).2.1
    have hidx := (Finset.mem_filter.mp ht).2.2
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    unfold calendarTheta calendarAcceptedArrival
    rw [ite_eq_left hstart, List.getElem?_eq_getElem hidx]
    rfl

/-- Integrability of the literal list-indexed weighted first moment under the
complete original source law. -/
theorem integrable_firstWindowWeightedAcceptedArrival (control0 : TimeControl p) :
    Integrable (fun omega : SourceInput p => ∑ k : Fin (L omega).length, ∑ j : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m (L omega) k.val j *
        ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
          (RecordedQueueRun.run Q ((L omega).take k.val)) (L omega)[k.val] j) : ℝ) /
            (rate.n : ℝ))) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (integrable_finsetSum Finset.univ (fun t _ =>
    (calendarWeightedArrival_moments rate rewards C_star C_h t control0).1)).congr
      (Filter.Eventually.of_forall
        (sum_calendarWeightedArrival_eq_firstWindow rate rewards C_star C_h))

/-- The actual first-window incoming weighted arrivals have original mean at
most `m * T`, with no finite canonical path-law substitution. -/
theorem integral_firstWindowWeightedAcceptedArrival_le (control0 : TimeControl p) :
    (∫ omega : SourceInput p, ∑ k : Fin (L omega).length, ∑ j : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m (L omega) k.val j *
        ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
          (RecordedQueueRun.run Q ((L omega).take k.val)) (L omega)[k.val] j) : ℝ) /
            (rate.n : ℝ)) ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      (p.m : ℝ) * (p.T : ℝ) := by
  rw [← integral_congr_ae (Filter.Eventually.of_forall
    (sum_calendarWeightedArrival_eq_firstWindow rate rewards C_star C_h)),
    integral_finsetSum _ (fun t _ =>
      (calendarWeightedArrival_moments rate rewards C_star C_h t control0).1)]
  calc
    _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact (calendarWeightedArrival_moments rate rewards C_star C_h t control0).2.trans
        (mul_le_of_le_one_right (Nat.cast_nonneg _) measureReal_le_one)
    _ = (p.m : ℝ) * (p.T : ℝ) := by simp [mul_comm]

end Bandits.Support.ReferenceFirstLiveOriginalCalendarArrivalMoments
