/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixLearning
public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixRoundedLearning
public import Bandits.Support.ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding
public import Bandits.Support.ReferenceFirstLiveFixedIDCalendarRoundedComparison

import Mathlib.Tactic

/-!
# Fixed-ID first-invocation rounded learning bound

The actual original-calendar rounded comparator is compared on the literal
fixed-ID source cylinder, then transported to its fixed-ID source law with one
atom cancellation and the shared horizon floor budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixRoundedLearning

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
local notation "Dset" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "ν" => ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
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

private theorem integrable_fixedID_of_integrable
    {f : SourceInput p → ℝ} (hf : Integrable f μ) : Integrable f ν := by
  have hRestricted : Integrable f ((sourceInputLaw p).restrict Dset) := hf.integrableOn
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection] at hRestricted
  have hAtom : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff
      (h := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top ids).ne)).mp
        (ne_of_gt (ReferenceFixedIDSourceSection.idArrayAtom_positive ids))
  have hAtomTop := (ReferenceFixedIDSourceSection.idArrayAtom_lt_top ids).ne
  exact (integrable_smul_measure hAtom hAtomTop).mp hRestricted

include control0

/-- The literal original-calendar rounded comparator is integrable under every
fixed-ID source law. -/
public theorem originalCalendarRoundedGap_integrable_fixedID :
    Integrable
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S) ν :=
  integrable_fixedID_of_integrable (ids := ids)
    (ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRoundedGap_integrable
      rate rewards C_star C_h control0 S)

/-- The literal original-calendar raw comparator is integrable under every
fixed-ID source law. -/
public theorem originalCalendarRawGap_integrable_fixedID :
    Integrable
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
        rate rewards C_star C_h S) ν :=
  integrable_fixedID_of_integrable (ids := ids)
    (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap_integrable
      rate rewards C_star C_h control0 S)

/-- The shared original-calendar floor loss is integrable under every
fixed-ID source law. -/
public theorem originalCalendarFloorLoss_integrable_fixedID :
    Integrable
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S) ν :=
  integrable_fixedID_of_integrable (ids := ids)
    (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss_integrable
      rate rewards C_star C_h control0 S)

/-- On the fixed-ID cylinder, the total literal calendar comparison sums the
accepted LIVE, OLD, and CURRENT signed estimates, retaining each actual call
event and its shared floor term. -/
public theorem integral_originalCalendarRoundedGap_fixedID_cylinder_le_raw_add_floor :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S z ∂μ) ≤
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂μ) +
      ∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S z ∂μ := by
  let liveRounded := fun t : Fin p.T =>
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRoundedGap
      rate rewards C_star C_h t S
  let liveRaw := fun t : Fin p.T =>
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarRawGap
      rate rewards C_star C_h t S
  let liveFloor := fun t : Fin p.T =>
    ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
      rate rewards C_star C_h t S
  let oldRounded := fun t : Fin p.T =>
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap
      rate rewards C_star C_h t S
  let oldRaw := fun t : Fin p.T =>
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap
      rate rewards C_star C_h t S
  let oldFloor := fun t : Fin p.T =>
    ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
      rate rewards C_star C_h t S
  let currentRounded := fun u t : Fin p.T =>
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
      rate rewards C_star C_h u t S
  let currentRaw := fun u t : Fin p.T =>
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
      rate rewards C_star C_h u t S
  let currentFloor := fun u t : Fin p.T =>
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
      rate rewards C_star C_h u t S

  have hLiveRounded (t : Fin p.T) : Integrable (liveRounded t) μ := by
    exact ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRoundedGap
      rate rewards C_star C_h t S control0
  have hLiveRaw (t : Fin p.T) : Integrable (liveRaw t) μ := by
    exact ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRawGap
      rate rewards C_star C_h t S control0
  have hLiveFloor (t : Fin p.T) : Integrable (liveFloor t) μ := by
    exact ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
      rate rewards C_star C_h t S control0
  have hOldRounded (t : Fin p.T) : Integrable (oldRounded t) μ := by
    exact ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap_integrable
      rate rewards C_star C_h control0 t S
  have hOldRaw (t : Fin p.T) : Integrable (oldRaw t) μ := by
    exact ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap_integrable
      rate rewards C_star C_h control0 t S
  have hOldFloor (t : Fin p.T) : Integrable (oldFloor t) μ := by
    exact ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 t S
  have hCurrentRounded (u t : Fin p.T) : Integrable (currentRounded u t) μ := by
    exact ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
      rate rewards C_star C_h control0 u t S
  have hCurrentRaw (u t : Fin p.T) : Integrable (currentRaw u t) μ := by
    exact ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
      rate rewards C_star C_h control0 u t S
  have hCurrentFloor (u t : Fin p.T) : Integrable (currentFloor u t) μ := by
    exact ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
      rate rewards C_star C_h control0 u t S

  have hLiveComparison :
      (∑ t : Fin p.T, ∫ z in Dset, liveRounded t z ∂μ) ≤
        (∑ t : Fin p.T, ∫ z in Dset, liveRaw t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, liveFloor t z ∂μ := by
    calc
      _ ≤ ∑ t : Fin p.T,
          ((∫ z in Dset, liveRaw t z ∂μ) + ∫ z in Dset, liveFloor t z ∂μ) :=
        Finset.sum_le_sum fun t _ =>
          ReferenceFirstLiveFixedIDCalendarRoundedComparison.integral_fixedID_calendarRoundedGap_le_raw_add_floor
            rate rewards C_star C_h control0 ids t S
      _ = _ := by rw [Finset.sum_add_distrib]
  have hOldComparison :
      (∑ t : Fin p.T, ∫ z in Dset, oldRounded t z ∂μ) ≤
        (∑ t : Fin p.T, ∫ z in Dset, oldRaw t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldFloor t z ∂μ := by
    calc
      _ ≤ ∑ t : Fin p.T,
          ((∫ z in Dset, oldRaw t z ∂μ) + ∫ z in Dset, oldFloor t z ∂μ) :=
        Finset.sum_le_sum fun t _ =>
          ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding.oldRoundedGap_setIntegral_fixedID_le
            rate rewards C_star C_h control0 ids t S
      _ = _ := by rw [Finset.sum_add_distrib]
  have hCurrentComparison :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRounded u t z ∂μ) ≤
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRaw u t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentFloor u t z ∂μ := by
    calc
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
          ((∫ z in Dset, currentRaw u t z ∂μ) +
            ∫ z in Dset, currentFloor u t z ∂μ) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t _ =>
          ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding.currentRoundedGap_setIntegral_fixedID_le
            rate rewards C_star C_h control0 ids u t S
      _ = _ := by simp_rw [Finset.sum_add_distrib]

  have hAggregateComparison :
      ((∑ t : Fin p.T, ∫ z in Dset, liveRounded t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldRounded t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRounded u t z ∂μ ≤
      ((∑ t : Fin p.T, ∫ z in Dset, liveRaw t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldRaw t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRaw u t z ∂μ +
      ((∑ t : Fin p.T, ∫ z in Dset, liveFloor t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldFloor t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentFloor u t z ∂μ := by
    linarith [hLiveComparison, hOldComparison, hCurrentComparison]

  have hLiveRoundedIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, liveRounded t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hLiveRounded t).integrableOn
  have hLiveRawIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, liveRaw t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hLiveRaw t).integrableOn
  have hLiveFloorIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, liveFloor t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hLiveFloor t).integrableOn
  have hOldRoundedIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, oldRounded t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hOldRounded t).integrableOn
  have hOldRawIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, oldRaw t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hOldRaw t).integrableOn
  have hOldFloorIntegrable :
      Integrable (fun z : SourceInput p => ∑ t : Fin p.T, oldFloor t z)
        ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun t _ => (hOldFloor t).integrableOn
  have hCurrentRoundedIntegrable :
      Integrable (fun z : SourceInput p => ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentRounded u t z) ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentRounded u t).integrableOn
  have hCurrentRawIntegrable :
      Integrable (fun z : SourceInput p => ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentRaw u t z) ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentRaw u t).integrableOn
  have hCurrentFloorIntegrable :
      Integrable (fun z : SourceInput p => ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentFloor u t z) ((sourceInputLaw p).restrict Dset) :=
    integrable_finsetSum Finset.univ fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentFloor u t).integrableOn

  have hLiveRoundedSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, liveRounded t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, liveRounded t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hLiveRounded t).integrableOn]
  have hLiveRawSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, liveRaw t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, liveRaw t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hLiveRaw t).integrableOn]
  have hLiveFloorSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, liveFloor t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, liveFloor t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hLiveFloor t).integrableOn]
  have hOldRoundedSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, oldRounded t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, oldRounded t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hOldRounded t).integrableOn]
  have hOldRawSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, oldRaw t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, oldRaw t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hOldRaw t).integrableOn]
  have hOldFloorSumExpansion :
      (∫ z in Dset, ∑ t : Fin p.T, oldFloor t z ∂μ) =
        ∑ t : Fin p.T, ∫ z in Dset, oldFloor t z ∂μ := by
    rw [integral_finsetSum Finset.univ fun t _ => (hOldFloor t).integrableOn]

  have hCurrentRoundedExpansion :
      (∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentRounded u t z ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRounded u t z ∂μ := by
    rw [integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentRounded u t).integrableOn)]
    apply Finset.sum_congr rfl
    intro u hu
    exact integral_finsetSum Finset.univ fun t _ => (hCurrentRounded u t).integrableOn
  have hCurrentRawExpansion :
      (∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentRaw u t z ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRaw u t z ∂μ := by
    rw [integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentRaw u t).integrableOn)]
    apply Finset.sum_congr rfl
    intro u hu
    exact integral_finsetSum Finset.univ fun t _ => (hCurrentRaw u t).integrableOn
  have hCurrentFloorExpansion :
      (∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
        currentFloor u t z ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentFloor u t z ∂μ := by
    rw [integral_finsetSum Finset.univ (fun u _ =>
      integrable_finsetSum Finset.univ fun t _ => (hCurrentFloor u t).integrableOn)]
    apply Finset.sum_congr rfl
    intro u hu
    exact integral_finsetSum Finset.univ fun t _ => (hCurrentFloor u t).integrableOn

  have hRoundedExpansion :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S z ∂μ) =
        ((∑ t : Fin p.T, ∫ z in Dset, liveRounded t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldRounded t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRounded u t z ∂μ := by
    calc
      _ = (∫ z in Dset,
          (∑ t : Fin p.T, liveRounded t z) +
            ∑ t : Fin p.T, oldRounded t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRounded u t z ∂μ :=
        integral_add (hLiveRoundedIntegrable.add hOldRoundedIntegrable)
          hCurrentRoundedIntegrable
      _ = ((∫ z in Dset, ∑ t : Fin p.T, liveRounded t z ∂μ) +
          ∫ z in Dset, ∑ t : Fin p.T, oldRounded t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRounded u t z ∂μ :=
        congrArg (fun x : ℝ => x +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRounded u t z ∂μ)
          (integral_add hLiveRoundedIntegrable hOldRoundedIntegrable)
      _ = _ := by
        rw [hLiveRoundedSumExpansion, hOldRoundedSumExpansion,
          hCurrentRoundedExpansion]
  have hRawExpansion :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂μ) =
        ((∑ t : Fin p.T, ∫ z in Dset, liveRaw t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldRaw t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentRaw u t z ∂μ := by
    calc
      _ = (∫ z in Dset,
          (∑ t : Fin p.T, liveRaw t z) +
            ∑ t : Fin p.T, oldRaw t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRaw u t z ∂μ :=
        integral_add (hLiveRawIntegrable.add hOldRawIntegrable)
          hCurrentRawIntegrable
      _ = ((∫ z in Dset, ∑ t : Fin p.T, liveRaw t z ∂μ) +
          ∫ z in Dset, ∑ t : Fin p.T, oldRaw t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRaw u t z ∂μ :=
        congrArg (fun x : ℝ => x +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentRaw u t z ∂μ)
          (integral_add hLiveRawIntegrable hOldRawIntegrable)
      _ = _ := by rw [hLiveRawSumExpansion, hOldRawSumExpansion, hCurrentRawExpansion]
  have hFloorExpansion :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S z ∂μ) =
        ((∑ t : Fin p.T, ∫ z in Dset, liveFloor t z ∂μ) +
          ∑ t : Fin p.T, ∫ z in Dset, oldFloor t z ∂μ) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in Dset, currentFloor u t z ∂μ := by
    calc
      _ = (∫ z in Dset,
          (∑ t : Fin p.T, liveFloor t z) +
            ∑ t : Fin p.T, oldFloor t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentFloor u t z ∂μ :=
        integral_add (hLiveFloorIntegrable.add hOldFloorIntegrable)
          hCurrentFloorIntegrable
      _ = ((∫ z in Dset, ∑ t : Fin p.T, liveFloor t z ∂μ) +
          ∫ z in Dset, ∑ t : Fin p.T, oldFloor t z ∂μ) +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentFloor u t z ∂μ :=
        congrArg (fun x : ℝ => x +
          ∫ z in Dset, ∑ u : Fin p.T, ∑ t : Fin p.T,
            currentFloor u t z ∂μ)
          (integral_add hLiveFloorIntegrable hOldFloorIntegrable)
      _ = _ := by rw [hLiveFloorSumExpansion, hOldFloorSumExpansion, hCurrentFloorExpansion]

  rw [hRoundedExpansion, hRawExpansion, hFloorExpansion]
  linarith [hAggregateComparison]

/-- The fixed-ID source-cylinder integral of the shared floor loss has one
horizon charge, with the literal ID atom as its sole measure factor. -/
public theorem integral_originalCalendarFloorLoss_fixedID_cylinder_le_horizon :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S z ∂μ) ≤
      Measure.real (CompletePublicTable.idArrayMeasure p) {ids} *
        (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) :=
  ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding.originalCalendarFloorLoss_setIntegral_fixedID_le_horizon
    rate rewards C_star C_h control0 ids S

/-- The actual rounded comparator mean on the fixed-ID source law is bounded
by the corresponding raw mean and the same literal floor-loss mean. -/
public theorem integral_originalCalendarRoundedGap_fixedID_le_raw_add_floor :
    (∫ z,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S z ∂ν) ≤
      (∫ z,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂ν) +
      ∫ z,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S z ∂ν := by
  have hLocal :=
    integral_originalCalendarRoundedGap_fixedID_cylinder_le_raw_add_floor
      rate rewards C_star C_h control0 ids S
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
      (p := p) ids
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S),
    ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
      (p := p) ids
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
        rate rewards C_star C_h S),
    ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
      (p := p) ids
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S)] at hLocal
  have hAtomPos : 0 < Measure.real (CompletePublicTable.idArrayMeasure p) {ids} :=
    ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply le_of_mul_le_mul_left _ hAtomPos
  calc
    _ ≤ Measure.real (CompletePublicTable.idArrayMeasure p) {ids} * (∫ z,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂ν) +
        Measure.real (CompletePublicTable.idArrayMeasure p) {ids} * (∫ z,
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
            rate rewards C_star C_h S z ∂ν) := hLocal
    _ = _ := by ring

/-- The shared horizon floor budget transports to the fixed-ID source law with
the same one normalizer. -/
public theorem integral_originalCalendarFloorLoss_fixedID_le_horizon :
    (∫ z,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S z ∂ν) ≤
      (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  have hLocal :=
    integral_originalCalendarFloorLoss_fixedID_cylinder_le_horizon
      rate rewards C_star C_h control0 ids S
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
    (p := p) ids
    (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
      rate rewards C_star C_h S)] at hLocal
  have hAtomPos : 0 < Measure.real (CompletePublicTable.idArrayMeasure p) {ids} :=
    ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply le_of_mul_le_mul_left _ hAtomPos
  calc
    _ ≤ Measure.real (CompletePublicTable.idArrayMeasure p) {ids} *
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := hLocal
    _ = _ := by ring

/-- The literal fixed-ID first-invocation rounded comparator mean retains one
potential normalizer and one original-calendar horizon floor charge. -/
public theorem integral_originalCalendarRoundedGap_fixedID_le_horizon :
    (∫ z,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S z ∂ν) ≤
      Real.log (Nat.choose p.K p.m : ℝ) / λ +
        16 * (p.m : ℝ) ^ 2 * λ * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) +
        (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  have hRoundedRawFloor :=
    integral_originalCalendarRoundedGap_fixedID_le_raw_add_floor
      rate rewards C_star C_h control0 ids S
  have hRawEq :
      (∫ z,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂ν) =
        ∫ z,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRawGap_eq_firstInvocationRawGap
        rate rewards C_star C_h S z)
  have hRaw :=
    ReferenceFirstCollectionFixedIDOriginalPrefixLearning.integral_firstInvocationRawGap_fixedID_le
      rate rewards C_star C_h control0 ids S
  have hFloor := integral_originalCalendarFloorLoss_fixedID_le_horizon
    rate rewards C_star C_h control0 ids S
  calc
    _ ≤
        (∫ z,
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
            rate rewards C_star C_h S z ∂ν) +
          ∫ z,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S z ∂ν := hRoundedRawFloor
    _ ≤ base + corr +
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
      rw [hRawEq]
      exact add_le_add hRaw hFloor
    _ = _ := by ring

end Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixRoundedLearning

end
