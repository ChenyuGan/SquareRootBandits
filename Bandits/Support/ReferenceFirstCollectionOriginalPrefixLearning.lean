/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionFirstInvocationRawPotential
public import Bandits.Support.ReferenceFirstCollectionOriginalWeightedArrivalBudget
public import Bandits.Support.ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin
public import Bandits.Support.ReferenceFirstCollectionOldOriginalComparatorRounding
public import Bandits.Support.ReferenceFirstLiveOriginalCalendarRoundedComparison

import Mathlib.Tactic

/-!
# Original-source learning bound through the first invocation

The raw comparator bound is integrated on the unchanged full source law. The
first-call cost uses the same actual call-cell backlog as the pre-call energy
join, and the weighted arrivals use the original calendar first-moment budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning

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

private theorem liveWeightedArrival_eq_firstWindow (z : SourceInput p) :
    (∑ t : Fin p.T,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
        rate rewards C_star C_h t z) =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationLiveWeightedArrival
        rate rewards C_star C_h z := by
  unfold ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
  rw [ReferenceFirstLiveOriginalCalendarArrivalMoments.sum_calendarWeightedArrival_eq_firstWindow
    rate rewards C_star C_h z]
  simp only [ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationLiveWeightedArrival,
    ReferenceFirstLiveRawPotentialBound.firstWindowMarginal,
    ReferenceFirstLiveRawPotentialBound.firstWindowAcceptedArrival,
    ReferenceFirstLiveRawPotentialBound.firstWindowQueue,
    ReferenceFirstLiveRawPotentialBound.firstWindowCells,
    ReferenceFirstLiveRawPotentialBound.firstWindowRun,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The first-invocation weighted arrival is the original LIVE/OLD/CURRENT
calendar sum on the same source input. -/
public theorem firstInvocationWeightedArrival_eq_calendar (z : SourceInput p) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z =
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
        rate rewards C_star C_h z := by
  have hLive := liveWeightedArrival_eq_firstWindow rate rewards C_star C_h z
  have hOld :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldWeightedArrival
          rate rewards C_star C_h z =
        ∑ t : Fin p.T,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
            rate rewards C_star C_h t z := by
    rfl
  have hCurrent :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCurrentWeightedArrival
          rate rewards C_star C_h z =
        ∑ t : Fin p.T, ∑ u : Fin p.T,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
            rate rewards C_star C_h u t z := by
    unfold ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCurrentWeightedArrival
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
    rw [Finset.sum_comm]
  calc
    _ =
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationLiveWeightedArrival
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldWeightedArrival
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCurrentWeightedArrival
            rate rewards C_star C_h z :=
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival_decomposition
        rate rewards C_star C_h z
    _ =
        (∑ t : Fin p.T,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
            rate rewards C_star C_h t z) +
          (∑ t : Fin p.T,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
              rate rewards C_star C_h t z) +
          ∑ t : Fin p.T, ∑ u : Fin p.T,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
              rate rewards C_star C_h u t z := by
      rw [← hLive, ← hOld, ← hCurrent]
    _ =
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
          rate rewards C_star C_h z := by
      unfold ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
      simp only [ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival,
        Finset.sum_add_distrib]
      ring

/-- The actual prefix weighted arrival is integrable on the original source. -/
public theorem firstInvocationWeightedArrival_integrable (control0 : TimeControl p) :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h) μ := by
  have h :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival_integrable
      rate rewards C_star C_h control0
  exact h.congr (Filter.Eventually.of_forall fun z =>
    (firstInvocationWeightedArrival_eq_calendar rate rewards C_star C_h z).symm)

/-- The actual prefix weighted arrival keeps the original `m*T` integral
budget. -/
public theorem firstInvocationWeightedArrival_integral_le (control0 : TimeControl p) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z ∂μ) ≤ (p.m : ℝ) * (p.T : ℝ) := by
  calc
    _ = ∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
          rate rewards C_star C_h z ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun z =>
        firstInvocationWeightedArrival_eq_calendar rate rewards C_star C_h z)
    _ ≤ (p.m : ℝ) * (p.T : ℝ) :=
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival_integral_le
        rate rewards C_star C_h control0

/-- The prefix cost is exactly the retained LIVE/OLD calendar cost plus the
actual first-call retained backlog observed by the energy join. -/
public theorem firstInvocationCost_eq_energyIntegrand (z : SourceInput p) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h z =
      (∑ t : Fin p.T,
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t z +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
            rate rewards C_star C_h t z)) +
        ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
          rate rewards C_star C_h z := by
  simp only [
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost,
    ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog,
    Finset.sum_add_distrib]

/-- The first-invocation cost is integrable on the same original source law. -/
public theorem firstInvocationCost_integrable (control0 : TimeControl p) :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h) μ := by
  have hPast : Integrable (fun z : SourceInput p =>
      ∑ t : Fin p.T,
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t z +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
            rate rewards C_star C_h t z)) μ := by
    apply integrable_finsetSum
    intro t ht
    exact (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hActual := hPast.add
    (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
      rate rewards C_star C_h control0)
  exact hActual.congr (Filter.Eventually.of_forall fun z =>
    (firstInvocationCost_eq_energyIntegrand rate rewards C_star C_h z).symm)

private theorem oldRawGap_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldRawGap
        rate rewards C_star C_h S) μ := by
  apply integrable_finsetSum
  intro t ht
  have hRaw :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_raw_integrable
      rate rewards C_star C_h control0 t S
  have hWeighted : Integrable
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
        rate rewards C_star C_h t) μ := by
    unfold ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
    apply integrable_finsetSum
    intro i hi
    exact ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
      rate rewards C_star C_h control0 t i
  have hStep : Integrable
      (fun z : SourceInput p =>
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
            rate rewards C_star C_h t S z -
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
            rate rewards C_star C_h t z) μ := hRaw.sub hWeighted
  have hEq (z : SourceInput p) :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldRawStepGap
          rate rewards C_star C_h t S z =
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
            rate rewards C_star C_h t S z -
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
            rate rewards C_star C_h t z := by
    rfl
  have hStep' := hStep.congr (Filter.Eventually.of_forall fun z => (hEq z).symm)
  exact hStep'

/-- The complete raw comparator gap on the actual prefix is integrable; each
component uses its accepted original-law integrability result. -/
public theorem firstInvocationRawGap_integrable (control0 : TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S) μ := by
  have hLive :=
    ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_firstWindowRawGap
      rate rewards C_star C_h S control0
  have hOld := oldRawGap_integrable rate rewards C_star C_h control0 S
  have hCurrent : Integrable (fun z : SourceInput p =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
          rate rewards C_star C_h u t S z) μ := by
    apply integrable_finsetSum
    intro u hu
    apply integrable_finsetSum
    intro t ht
    exact ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
      rate rewards C_star C_h control0 u t S
  have hParts : Integrable (fun z : SourceInput p =>
      (ReferenceFirstLiveRawPotentialBound.firstWindowRawGap
          rate rewards C_star C_h z S +
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationOldRawGap
          rate rewards C_star C_h S z) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
            rate rewards C_star C_h u t S z) μ :=
    (hLive.add hOld).add hCurrent
  exact hParts.congr (Filter.Eventually.of_forall fun z =>
    (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_decomposition
      rate rewards C_star C_h S z).symm)

private theorem firstInvocationRawGap_pointwise (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z +
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z) := by
  have hRaw := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_le
    rate rewards C_star C_h S z
  have hCorrection := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection_le
    rate rewards C_star C_h z
  calc
    _ ≤
        Real.log (Nat.choose p.K p.m : ℝ) /
            RecordedPotentialStep.potentialLambda Q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
          (p.m : ℝ) / (16 * rate.eta.val) +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection
            rate rewards C_star C_h z := hRaw
    _ ≤ _ := add_le_add le_rfl hCorrection

/-- The original-source expected raw gap has a cost-and-arrival form retaining
the actual potential normalizer and the single terminal queue charge. -/
public theorem integral_firstInvocationRawGap_le_cost_and_arrival
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ∂μ) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        8 * rate.eta.val *
          ((∫ z : SourceInput p,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z : SourceInput p,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z ∂μ) := by
  have hRaw := firstInvocationRawGap_integrable rate rewards C_star C_h control0 S
  have hCost := firstInvocationCost_integrable rate rewards C_star C_h control0
  have hArrival := firstInvocationWeightedArrival_integrable rate rewards C_star C_h control0
  let B : ℝ :=
    Real.log (Nat.choose p.K p.m : ℝ) /
        RecordedPotentialStep.potentialLambda Q +
      16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
      (p.m : ℝ) / (16 * rate.eta.val)
  have hMajorant : Integrable (fun z : SourceInput p =>
      B + 8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z)) μ := by
    exact (integrable_const B).add ((hCost.add hArrival).const_mul (8 * rate.eta.val))
  have hPoint (z : SourceInput p) :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S z ≤
        B + 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z +
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z) := by
    simpa only [B] using firstInvocationRawGap_pointwise rate rewards C_star C_h S z
  calc
    _ ≤ ∫ z : SourceInput p,
        B + 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z +
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z) ∂μ :=
      integral_mono hRaw hMajorant hPoint
    _ = (∫ _ : SourceInput p, B ∂μ) +
        ∫ z : SourceInput p,
          8 * rate.eta.val *
            (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z +
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z) ∂μ := by
      change (∫ z : SourceInput p,
          (fun _ : SourceInput p => B) z +
            (fun z => 8 * rate.eta.val *
              (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                  rate rewards C_star C_h z +
                ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                  rate rewards C_star C_h z)) z ∂μ) = _
      exact integral_add (integrable_const B)
        ((hCost.add hArrival).const_mul (8 * rate.eta.val))
    _ = B + 8 * rate.eta.val *
        ((∫ z : SourceInput p,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z ∂μ) +
          ∫ z : SourceInput p,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
              rate rewards C_star C_h z ∂μ) := by
      have hB : (∫ _ : SourceInput p, B ∂μ) = B := by
        rw [integral_const, probReal_univ, one_smul]
      rw [hB, integral_const_mul, integral_add hCost hArrival]

/-- The actual first-invocation raw comparator bound, including the no-call
horizon and exactly one normalizer cost. -/
public theorem integral_firstInvocationRawGap_le
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z ∂μ) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) := by
  have hPrecise := integral_firstInvocationRawGap_le_cost_and_arrival
    rate rewards C_star C_h control0 S
  have hArrival := firstInvocationWeightedArrival_integral_le
    rate rewards C_star C_h control0
  have hEnergy :
      (11 / 2 : ℝ) *
          (∫ z : SourceInput p,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z ∂μ) ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
    have hJoin :=
      ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.integral_preCall_firstCall_weighted_backlog_join
        rate rewards C_star C_h control0
    have hCostAE :
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h) =ᵐ[μ]
          (fun z =>
            (∑ t : Fin p.T,
              (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
                  rate rewards C_star C_h t z +
                ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
                  rate rewards C_star C_h t z)) +
              ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
                rate rewards C_star C_h z) :=
      Filter.Eventually.of_forall fun z =>
        firstInvocationCost_eq_energyIntegrand rate rewards C_star C_h z
    have hCostEq := integral_congr_ae hCostAE
    calc
      _ = (11 / 2 : ℝ) *
          (∫ z : SourceInput p,
            (∑ t : Fin p.T,
              (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
                  rate rewards C_star C_h t z +
                ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
                  rate rewards C_star C_h t z)) +
              ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
                rate rewards C_star C_h z ∂μ) := by rw [hCostEq]
      _ ≤ _ := hJoin
  have hCostMean :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
          rate rewards C_star C_h z ∂μ) ≤
        (2 / 11 : ℝ) *
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
    nlinarith only [hEnergy]
  have hCostArrival := add_le_add hCostMean hArrival
  have hEta := mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) rate.eta.property.le
  calc
    _ ≤ Real.log (Nat.choose p.K p.m : ℝ) /
            RecordedPotentialStep.potentialLambda Q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
          (p.m : ℝ) / (16 * rate.eta.val) +
          8 * rate.eta.val *
            ((∫ z : SourceInput p,
                ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                  rate rewards C_star C_h z ∂μ) +
              ∫ z : SourceInput p,
                ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                  rate rewards C_star C_h z ∂μ) := hPrecise
    _ ≤ Real.log (Nat.choose p.K p.m : ℝ) /
            RecordedPotentialStep.potentialLambda Q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
          (p.m : ℝ) / (16 * rate.eta.val) +
          8 * rate.eta.val *
            ((2 / 11 : ℝ) *
                (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
                (p.T : ℝ) +
              (p.m : ℝ) * (p.T : ℝ)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hCostArrival hEta)
    _ = _ := by ring

end Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning

end
