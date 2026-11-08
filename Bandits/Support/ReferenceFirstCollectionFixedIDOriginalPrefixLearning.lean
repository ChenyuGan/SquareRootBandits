/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFixedIDWeightedArrivalBudget
public import Bandits.Support.ReferenceFirstCollectionFixedIDWeightedCostBudget

import Mathlib.Tactic

/-!
# Fixed-ID first-invocation raw learning bound

This module transports the original-source prefix integrability to the literal
fixed-ID source law and localizes the same potential bound before cancelling
the positive ID atom.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixLearning

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)
  (S : ProductSetLaw.ProductSet p.K p.m)

local notation "μ" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "ν" => ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
local notation "atom" =>
  Measure.real (CompletePublicTable.idArrayMeasure p)
    (Set.singleton ids)
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "λ" => RecordedPotentialStep.potentialLambda Q
local notation "base" =>
  Real.log (Nat.choose p.K p.m : ℝ) / λ +
    16 * (p.m : ℝ) ^ 2 * λ * (p.T : ℝ) +
    (p.m : ℝ) / (16 * rate.eta.val)
local notation "corr" =>
  ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
    rate.eta.val * (p.T : ℝ)

private local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private theorem firstInvocationRawGap_pointwise
    (z : SourceInput p) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ≤
      base + 8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z) := by
  have hRaw :=
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_le
      rate rewards C_star C_h S z
  have hCorrection :=
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection_le
      rate rewards C_star C_h z
  calc
    _ ≤ base + ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection
        rate rewards C_star C_h z := hRaw
    _ ≤ _ := add_le_add le_rfl hCorrection

include control0 in
/-- The actual raw comparator gap is integrable under every literal fixed-ID
source law, by restriction and finite positive atom scaling of its original
source integrability. -/
public theorem firstInvocationRawGap_integrable_fixedID :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S) ν := by
  have hOriginal :=
    ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
      rate rewards C_star C_h control0 S
  have hRestricted : Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S) ((sourceInputLaw p).restrict D) := hOriginal.integrableOn
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection] at hRestricted
  have hAtom : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff
      (h := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top ids).ne)).mp
        (ne_of_gt (ReferenceFixedIDSourceSection.idArrayAtom_positive ids))
  have hAtomTop := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top ids).ne
  exact (integrable_smul_measure hAtom hAtomTop).mp hRestricted

include control0 in
/-- The first-invocation raw gap obeys the exact source coefficients on the
original-law cylinder for this fixed ID, before its atom is cancelled. -/
public theorem integral_firstInvocationRawGap_fixedID_cylinder_le :
    (∫ z in D,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ∂μ) ≤ atom * (base + corr) := by
  have hRaw :=
    ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
      rate rewards C_star C_h control0 S
  have hCost :=
    ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_integrable
      rate rewards C_star C_h control0
  have hArrival :=
    ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable
      rate rewards C_star C_h control0
  have hFactor : Integrable
      (fun z : SourceInput p => 8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z)) μ :=
    (hCost.add hArrival).const_mul (8 * rate.eta.val)
  have hMajorant : IntegrableOn
      (fun z : SourceInput p => base + 8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z)) D μ :=
    (integrable_const base).add hFactor |>.integrableOn
  have hLocalRaw : IntegrableOn
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S) D μ := hRaw.integrableOn
  have hPoint (z : SourceInput p) :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S z ≤
        base + 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z +
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z) :=
    firstInvocationRawGap_pointwise rate rewards C_star C_h S z
  have hConstant : (∫ z in D, base ∂μ) = base * atom := by
    rw [setIntegral_const, smul_eq_mul]
    have hMass : (sourceInputLaw p).real D = atom :=
      ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection ids
    rw [← hMass]
    ring
  have hFactorIntegral :
      (∫ z in D, 8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z) ∂μ) =
        8 * rate.eta.val *
          ((∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z ∂μ) := by
    rw [integral_const_mul, integral_add hCost.integrableOn hArrival.integrableOn]
  have hCostBudget :=
    ReferenceFirstCollectionFixedIDWeightedCostBudget.fixedIDFirstInvocationCostBudget
      rate rewards C_star C_h control0 ids
  have hCostMean :
      (∫ z in D,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
          rate rewards C_star C_h z ∂μ) ≤
        (2 / 11 : ℝ) *
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (p.T : ℝ) * atom := by
    calc
      _ = (2 / 11 : ℝ) * ((11 / 2 : ℝ) *
          (∫ z in D,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z ∂μ)) := by ring
      _ ≤ (2 / 11 : ℝ) *
          ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (p.T : ℝ) * atom) :=
          mul_le_mul_of_nonneg_left hCostBudget (by norm_num)
      _ = _ := by ring
  have hArrivalBudget :=
    ReferenceFirstCollectionFixedIDWeightedArrivalBudget.firstInvocationWeightedArrival_setIntegral_fixedID_le
      rate rewards C_star C_h control0 ids
  have hCorrectionMean :
      8 * rate.eta.val *
        ((∫ z in D,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z ∂μ) +
          ∫ z in D,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z ∂μ) ≤ corr * atom := by
    calc
      _ ≤ 8 * rate.eta.val *
          ((2 / 11 : ℝ) *
              (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              (p.T : ℝ) * atom + atom * (p.m : ℝ) * (p.T : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hCostMean hArrivalBudget)
          (mul_nonneg (by norm_num) rate.eta.property.le)
      _ = corr * atom := by
        ring
  calc
    _ ≤ (∫ z in D, base ∂μ) +
        ∫ z in D, 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z +
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z) ∂μ := by
      calc
        _ ≤ ∫ z in D, (base + 8 * rate.eta.val *
            (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z +
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z)) ∂μ :=
          integral_mono hLocalRaw hMajorant hPoint
        _ = _ := integral_add (integrable_const base).integrableOn hFactor.integrableOn
    _ = base * atom +
        8 * rate.eta.val *
          ((∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z ∂μ) := by
      rw [hConstant, hFactorIntegral]
    _ ≤ atom * (base + corr) := by
      calc
        _ ≤ base * atom + corr * atom := add_le_add le_rfl hCorrectionMean
        _ = atom * (base + corr) := by ring

include control0 in
/-- Expected raw comparator gap under the literal fixed-ID law. The bound
retains the original potential normalizer and exact first-invocation charges. -/
public theorem integral_firstInvocationRawGap_fixedID_le :
    (∫ z,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ∂ν) ≤ base + corr := by
  have hLocal :=
    integral_firstInvocationRawGap_fixedID_cylinder_le
      rate rewards C_star C_h control0 ids S
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
    (p := p) ids
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S)] at hLocal
  have hAtomPos : 0 < atom := ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply le_of_mul_le_mul_left _ hAtomPos
  exact hLocal

end Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixLearning

end
