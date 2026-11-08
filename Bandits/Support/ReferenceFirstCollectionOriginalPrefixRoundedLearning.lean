/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalCalendarRoundingJoin
public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning

import Mathlib.Tactic

/-!
# Original-source rounded learning bound through the first invocation

The literal original-calendar rounded comparator is aligned pointwise with the
actual first-invocation raw comparator. Its source-law mean then uses one
potential normalizer and the single shared horizon floor charge.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOriginalPrefixRoundedLearning

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "μ" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

private local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- On every original source input, the calendar raw comparator is exactly the
actual first-invocation raw comparator. -/
public theorem originalCalendarRawGap_eq_firstInvocationRawGap
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
        rate rewards C_star C_h S z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z := by
  have hLive :=
    ReferenceFirstLiveOriginalCalendarRoundedComparison.sum_calendarRawGap_eq_firstWindowRawGap
      rate rewards C_star C_h S z
  have hOld :
      (∑ t : Fin p.T,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap
          rate rewards C_star C_h t S z) =
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldRawGap
          rate rewards C_star C_h S z := by
    unfold ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldRawGap
    apply Finset.sum_congr rfl
    intro t ht
    rfl
  rw [ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_decomposition]
  unfold ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
  rw [hLive, hOld]

/-- The rounded comparator gap retains the accepted integrability on the
original source law. -/
public theorem originalCalendarRoundedGap_integrable
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S) μ :=
  ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap_integrable
    rate rewards C_star C_h control0 S

/-- The actual first-invocation rounded comparator mean, retaining the exact
LIVE, OLD, and CURRENT floor losses as one explicit source-law term. -/
public theorem integral_originalCalendarRoundedGap_le_raw_add_floorLoss
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S z ∂μ) ≤
      (Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ)) +
        ∫ z : SourceInput p,
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
            rate rewards C_star C_h S z ∂μ := by
  have hRaw :=
    ReferenceFirstCollectionOriginalPrefixLearning.integral_firstInvocationRawGap_le
      rate rewards C_star C_h control0 S
  have hRawEq :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂μ) =
        ∫ z : SourceInput p,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z =>
      originalCalendarRawGap_eq_firstInvocationRawGap
        rate rewards C_star C_h S z)
  calc
    _ ≤
        (∫ z : SourceInput p,
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
            rate rewards C_star C_h S z ∂μ) +
          ∫ z : SourceInput p,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S z ∂μ :=
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.integral_originalCalendarRoundedGap_le_raw_add_floorLoss
        rate rewards C_star C_h control0 S
    _ =
        (∫ z : SourceInput p,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z ∂μ) +
          ∫ z : SourceInput p,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S z ∂μ := by
      rw [hRawEq]
    _ ≤ _ := add_le_add hRaw le_rfl

/-- The actual first-invocation rounded comparator mean has one log
normalizer and one horizon floor charge on the unchanged source law. -/
public theorem integral_originalCalendarRoundedGap_le_horizon
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S z ∂μ) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  have hExplicit :=
    integral_originalCalendarRoundedGap_le_raw_add_floorLoss
      rate rewards C_star C_h control0 S
  have hFloor :=
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.integral_originalCalendarFloorLoss_le_horizon
      rate rewards C_star C_h control0 S
  calc
    _ ≤ _ := hExplicit
    _ ≤ _ := add_le_add le_rfl hFloor

end Bandits.Support.ReferenceFirstCollectionOriginalPrefixRoundedLearning

end
