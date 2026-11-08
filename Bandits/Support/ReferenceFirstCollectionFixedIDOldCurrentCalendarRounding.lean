/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFixedIDWeightedArrivalBudget
public import Bandits.Support.ReferenceFirstCollectionOriginalCalendarRoundingJoin

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# Fixed-ID OLD and CURRENT signed calendar rounding

The OLD and CURRENT signed comparisons and the shared calendar floor budget
are integrated on the unchanged source law over the literal fixed-ID section.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding

open ConstructorDimensions (Parameters)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceActivePhysicalStep (RateInput)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

variable {p : Parameters} (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "μ" => sourceInputLaw p
local notation "Dset" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)
local notation "c" => (p.m : ℝ) / scale

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

include rate rewards C_star C_h

private theorem fixedID_predictable (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] Dset :=
  ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
    control0 ids t.val

private def oldWeightedRawAtDate (t : Fin p.T) (z : SourceInput p) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
      rate rewards C_star C_h t i z *
    (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
      (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
        rate rewards C_star C_h t i) z

private def oldWeightedRoundedAtDate (t : Fin p.T) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t).indicator (fun z =>
      ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z

private theorem oldRoundedGap_decomposition (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap
        rate rewards C_star C_h t S = fun z =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded
          rate rewards C_star C_h t S z - oldWeightedRoundedAtDate rate rewards C_star C_h t z := by
  funext z
  let G := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  by_cases hz : z ∈ G
  · simp [ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded,
      oldWeightedRoundedAtDate, G, hz]
  · simp [ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded,
      oldWeightedRoundedAtDate, G, hz]

private theorem oldRawGap_decomposition (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap
        rate rewards C_star C_h t S = fun z =>
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
          rate rewards C_star C_h t S z - oldWeightedRawAtDate rate rewards C_star C_h t z := rfl

include control0

private theorem oldWeightedRawAtDate_integrable (t : Fin p.T) :
    Integrable (oldWeightedRawAtDate rate rewards C_star C_h t) μ := by
  unfold oldWeightedRawAtDate
  exact integrable_finsetSum Finset.univ (fun i _ =>
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
      rate rewards C_star C_h control0 t i)

private theorem oldWeightedRoundedAtDate_integrable (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (oldWeightedRoundedAtDate rate rewards C_star C_h t) μ := by
  let comparator := ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded
    rate rewards C_star C_h t S
  let gap := ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap
    rate rewards C_star C_h t S
  have hcomp :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_rounded_integrable
      rate rewards C_star C_h control0 t S
  have hgap :=
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap_integrable
      rate rewards C_star C_h control0 t S
  have hEq : (fun z : SourceInput p => comparator z - gap z) =
      oldWeightedRoundedAtDate rate rewards C_star C_h t := by
    funext z
    have hz := congrFun
      (oldRoundedGap_decomposition rate rewards C_star C_h t S) z
    linarith
  rw [← hEq]
  exact hcomp.sub hgap

private theorem oldWeightedRawAtDate_setIntegral_le_rounded (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in Dset, oldWeightedRawAtDate rate rewards C_star C_h t z ∂μ) ≤
      ∫ z in Dset, oldWeightedRoundedAtDate rate rewards C_star C_h t z ∂μ := by
  let arm : Fin p.K → SourceInput p → ℝ := fun i z =>
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z
  let momentTerm : Fin p.K → SourceInput p → ℝ := fun i z =>
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hDpredictable : MeasurableSet[
      sourcePrefixFiltration control0 (t.val + 1)] Dset :=
    fixedID_predictable rate rewards C_star C_h control0 ids t
  have hD : MeasurableSet Dset := hFle Dset hDpredictable
  have hcond (i : Fin p.K) :
      μ[arm i | sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[μ] momentTerm i := by
    simpa only [arm, momentTerm] using
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_condExp
        rate rewards C_star C_h control0 t i)
  have hArmEq (i : Fin p.K) :
      (∫ z in Dset, arm i z ∂μ) = ∫ z in Dset, momentTerm i z ∂μ := by
    calc
      _ = ∫ z in Dset,
          μ[arm i | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ := by
        symm
        exact setIntegral_condExp hFle
          (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
            rate rewards C_star C_h control0 t i) hDpredictable
      _ = _ := setIntegral_congr_ae hD (by
        filter_upwards [hcond i] with z hz
        intro _
        exact hz)
  have hmomentInt (i : Fin p.K) : Integrable (momentTerm i) μ := by
    exact (integrable_condExp
      (f := arm i)).congr (hcond i)
  have hmomentSumInt : Integrable (fun z : SourceInput p =>
      ∑ i : Fin p.K, momentTerm i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hmomentInt i)
  have hroundedInt := oldWeightedRoundedAtDate_integrable
    rate rewards C_star C_h control0 t S
  have hpoint (z : SourceInput p) :
      (∑ i : Fin p.K, momentTerm i z) ≤
        oldWeightedRoundedAtDate rate rewards C_star C_h t z := by
    simp only [momentTerm]
    let G := ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t
    by_cases hz : z ∈ G
    · unfold oldWeightedRoundedAtDate
      rw [Set.indicator_of_mem hz]
      apply Finset.sum_le_sum
      intro i hi
      have htheta :=
        (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldIncomingTheta_predictable_bounds
          rate rewards C_star C_h control0 t i).2 z
      have hmoment :=
        (ReferenceFirstCollectionOldOriginalComparatorRounding.old_retained_moment_one_reward_bounds
          rate rewards C_star C_h t i z).2.1
      simpa [G, Set.indicator_of_mem hz] using
        (mul_le_mul_of_nonneg_left hmoment htheta.1)
    · unfold oldWeightedRoundedAtDate
      rw [Set.indicator_of_notMem hz]
      have hmomentZero (i : Fin p.K) :
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z = 0 := by
        have hb :=
          ReferenceFirstCollectionOldOriginalComparatorRounding.old_retained_moment_one_reward_bounds
            rate rewards C_star C_h t i z
        have hzero :
            (ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t).indicator (fun _ =>
                ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i) z = 0 :=
          Set.indicator_of_notMem hz _
        have hm0 :
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
              rate rewards C_star C_h t i z ≤ 0 := by
          calc
            _ ≤ _ := hb.2.1
            _ = 0 := hzero
        exact le_antisymm hm0 hb.1
      simp [hmomentZero]
  have hsumRaw :
      (∫ z in Dset, oldWeightedRawAtDate rate rewards C_star C_h t z ∂μ) =
        ∑ i : Fin p.K, ∫ z in Dset, arm i z ∂μ := by
    unfold oldWeightedRawAtDate
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldWeightedArrival_integrable
        rate rewards C_star C_h control0 t i).integrableOn)]
  have hsumMoment :
      (∑ i : Fin p.K, ∫ z in Dset, momentTerm i z ∂μ) =
        ∫ z in Dset, (∑ i : Fin p.K, momentTerm i z) ∂μ := by
    symm
    rw [integral_finsetSum Finset.univ (fun i _ => (hmomentInt i).integrableOn)]
  have hlocalPoint := setIntegral_mono_ae
    (hmomentSumInt.integrableOn (s := Dset))
    (hroundedInt.integrableOn (s := Dset)) (ae_of_all μ hpoint)
  calc
    _ = ∑ i : Fin p.K, ∫ z in Dset, arm i z ∂μ := hsumRaw
    _ = ∑ i : Fin p.K, ∫ z in Dset, momentTerm i z ∂μ := by
      exact Finset.sum_congr rfl (fun i _ => hArmEq i)
    _ = ∫ z in Dset, (∑ i : Fin p.K, momentTerm i z) ∂μ := hsumMoment
    _ ≤ _ := hlocalPoint

/-- The fixed-ID OLD signed comparison retains the exact OLD floor loss on the
same calendar date and source cylinder. -/
public theorem oldRoundedGap_setIntegral_fixedID_le
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap
        rate rewards C_star C_h t S z ∂μ) ≤
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap
          rate rewards C_star C_h t S z ∂μ) +
        ∫ z in Dset,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z ∂μ := by
  let compRaw := ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRaw
    rate rewards C_star C_h t S
  let compRounded := ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorRounded
    rate rewards C_star C_h t S
  let floor := ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
    rate rewards C_star C_h t S
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hDpredictable : MeasurableSet[
      sourcePrefixFiltration control0 (t.val + 1)] Dset :=
    fixedID_predictable rate rewards C_star C_h control0 ids t
  have hD : MeasurableSet Dset := hFle Dset hDpredictable
  have hcompRaw : Integrable compRaw μ :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_raw_integrable
      rate rewards C_star C_h control0 t S
  have hcompRounded : Integrable compRounded μ :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_rounded_integrable
      rate rewards C_star C_h control0 t S
  have hfloor : Integrable floor μ :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 t S
  have hweightedRaw := oldWeightedRawAtDate_integrable
    rate rewards C_star C_h control0 t
  have hweightedRounded := oldWeightedRoundedAtDate_integrable
    rate rewards C_star C_h control0 t S
  have hcompCond :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_cond_exp_rounded_sub_floor_le_raw
      rate rewards C_star C_h control0 t S
  have hcompMono := setIntegral_mono_ae
    ((hcompRounded.sub hfloor).integrableOn (s := Dset))
    ((integrable_condExp (f := compRaw)).integrableOn (s := Dset)) hcompCond
  have hcompLocal :
      (∫ z in Dset, compRounded z ∂μ) ≤
        (∫ z in Dset, compRaw z ∂μ) + ∫ z in Dset, floor z ∂μ := by
    change (∫ z in Dset, compRounded z - floor z ∂μ) ≤
      ∫ z in Dset,
        μ[compRaw | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ at hcompMono
    rw [integral_sub (hcompRounded.integrableOn (s := Dset))
      (hfloor.integrableOn (s := Dset))] at hcompMono
    rw [setIntegral_condExp hFle hcompRaw hDpredictable] at hcompMono
    linarith
  have hweightLocal := oldWeightedRawAtDate_setIntegral_le_rounded
    rate rewards C_star C_h control0 ids t S
  have hgapRoundedEq :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRoundedGap
          rate rewards C_star C_h t S z ∂μ) =
        (∫ z in Dset, compRounded z ∂μ) -
          ∫ z in Dset, oldWeightedRoundedAtDate rate rewards C_star C_h t z ∂μ := by
    rw [oldRoundedGap_decomposition rate rewards C_star C_h t S]
    exact integral_sub
      (hcompRounded.integrableOn (s := Dset))
      (hweightedRounded.integrableOn (s := Dset))
  have hgapRawEq :
      (∫ z in Dset,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.oldRawGap
          rate rewards C_star C_h t S z ∂μ) =
        (∫ z in Dset, compRaw z ∂μ) -
          ∫ z in Dset, oldWeightedRawAtDate rate rewards C_star C_h t z ∂μ := by
    rw [oldRawGap_decomposition rate rewards C_star C_h t S]
    exact integral_sub
      (hcompRaw.integrableOn (s := Dset))
      (hweightedRaw.integrableOn (s := Dset))
  have hfloorTerm : ∫ z in Dset, floor z ∂μ =
      ∫ z in Dset,
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ∂μ := rfl
  rw [hgapRoundedEq, hgapRawEq, hfloorTerm]
  linarith

/-- The CURRENT signed comparison holds after restriction to the same literal
fixed-ID cylinder, with its datewise floor term. -/
public theorem currentRoundedGap_setIntegral_fixedID_le
    (u t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in Dset,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
        rate rewards C_star C_h u t S z ∂μ) ≤
      (∫ z in Dset,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
          rate rewards C_star C_h u t S z ∂μ) +
        ∫ z in Dset,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ := by
  let rounded := ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap
    rate rewards C_star C_h u t S
  let raw := ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap
    rate rewards C_star C_h u t S
  let floor := ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
    rate rewards C_star C_h u t S
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hDpredictable : MeasurableSet[
      sourcePrefixFiltration control0 (t.val + 1)] Dset :=
    fixedID_predictable rate rewards C_star C_h control0 ids t
  have hrounded : Integrable rounded μ :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.roundedGap_integrable
      rate rewards C_star C_h control0 u t S
  have hraw : Integrable raw μ :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.rawGap_integrable
      rate rewards C_star C_h control0 u t S
  have hfloor : Integrable floor μ :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
      rate rewards C_star C_h control0 u t S
  have hcond :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.condExp_roundedGap_le_rawGap_add_floorLoss
      rate rewards C_star C_h control0 u t S
  have hmono := setIntegral_mono_ae
    ((integrable_condExp (f := rounded)).integrableOn (s := Dset))
    ((integrable_condExp (f := raw)).add hfloor).integrableOn (s := Dset) hcond
  calc
    _ = ∫ z in Dset,
        μ[rounded | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ := by
      symm
      exact setIntegral_condExp hFle hrounded hDpredictable
    _ ≤ ∫ z in Dset,
        (μ[raw | sourcePrefixFiltration control0 (t.val + 1)] z + floor z) ∂μ := hmono
    _ = (∫ z in Dset,
        μ[raw | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ) +
          ∫ z in Dset, floor z ∂μ := by
      exact integral_add
        ((integrable_condExp (f := raw)).integrableOn (s := Dset))
        (hfloor.integrableOn (s := Dset))
    _ = _ := by rw [setIntegral_condExp hFle hraw hDpredictable]

private theorem setIntegral_le_gate_mass
    {G : Set (SourceInput p)} {f : SourceInput p → ℝ}
    (gateMeasurable : MeasurableSet G) (hfun : Integrable f μ)
    (hc : 0 ≤ c)
    (hbound : ∀ z : SourceInput p, f z ≤ G.indicator (fun _ => c) z) :
    (∫ z in Dset, f z ∂μ) ≤ c * (μ).real (Dset ∩ G) := by
  have hupper : Integrable (G.indicator (fun _ : SourceInput p => c)) μ :=
    (integrable_const c).indicator gateMeasurable
  have hfunOn : IntegrableOn f Dset μ := hfun.integrableOn (s := Dset)
  have hupperOn : IntegrableOn (G.indicator (fun _ : SourceInput p => c)) Dset μ :=
    hupper.integrableOn (s := Dset)
  have hmono := setIntegral_mono_ae hfunOn hupperOn
    (ae_of_all μ hbound)
  calc
    _ ≤ ∫ z in Dset, G.indicator (fun _ => c) z ∂μ := hmono
    _ = ∫ z in Dset ∩ G, c ∂μ := by rw [setIntegral_indicator gateMeasurable]
    _ = _ := by rw [setIntegral_const, smul_eq_mul]; ring

private theorem sharedFloorSetIntegrals_le (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ((∫ z in Dset,
        ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
      ∫ z in Dset,
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
      ∑ u : Fin p.T, ∫ z in Dset,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z ∂μ ≤
      c * (CompletePublicTable.idArrayMeasure p).real {ids} := by
  let P234 := (ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3) ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4
  let liveGate := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  let oldGate := ReferenceFirstCollectionOldCalendarExponentialStep.G
    rate rewards C_star C_h t
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      sourceInputMeasurableSpace :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (mul_pos rate.eta.property
      (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))))
  have hliveGate : MeasurableSet liveGate :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.measurableSet_retainedEnabledEvent
      rate rewards C_star C_h t control0
  have holdGate : MeasurableSet oldGate :=
    hFle oldGate
      (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
        rate rewards C_star C_h control0 t)
  have hcurrentGate (u : Fin p.T) :
      MeasurableSet (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t) :=
    hFle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have hliveBound (z : SourceInput p) :
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h t S z ≤ liveGate.indicator (fun _ => c) z := by
    simpa [liveGate] using
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.calendarFloorLoss_le_actualGateConstant
        rate rewards C_star C_h t S z
  have hOldBound (z : SourceInput p) :
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
        rate rewards C_star C_h t S z ≤ oldGate.indicator (fun _ => c) z := by
    have hb :=
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_bounds
        rate rewards C_star C_h t S z
    by_cases hz : z ∈ oldGate
    · simpa [oldGate, Set.indicator_of_mem hz] using hb.2
    · have hzero :
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z = 0 := by
        apply le_antisymm
        · have hle := hb.2
          simpa [oldGate, hz] using hle
        · exact hb.1
      simp [oldGate, hz, hzero]
  have hcurrentBound (u : Fin p.T) (z : SourceInput p) :
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u t S z ≤
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t).indicator (fun _ => c) z := by
    let G := ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t
    by_cases hz : z ∈ G
    · have hb :=
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_le
          rate rewards C_star C_h u t S z
      simpa [G, Set.indicator_of_mem hz] using hb
    · simp [ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss, G, hz]
  have hLiveInt :=
    ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
      rate rewards C_star C_h t S control0
  have hOldInt :=
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 t S
  have hCurrentInt (u : Fin p.T) :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
      rate rewards C_star C_h control0 u t S
  have hLiveMass := setIntegral_le_gate_mass rate rewards C_star C_h control0 ids
    hliveGate hLiveInt hc hliveBound
  have hOldMass := setIntegral_le_gate_mass rate rewards C_star C_h control0 ids
    holdGate hOldInt hc hOldBound
  have hCurrentMass (u : Fin p.T) :=
    setIntegral_le_gate_mass rate rewards C_star C_h control0 ids
      (hcurrentGate u) (hCurrentInt u) hc (hcurrentBound u)
  have hliveSubset : Dset ∩ liveGate ⊆ Dset ∩ P234 := by
    intro z hz
    have heq :=
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
        rate rewards C_star C_h t control0
    change z ∈ Dset ∩ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t at hz
    rw [heq] at hz
    have hphase := hz.2.1
    rw [← Set.union_assoc] at hphase
    exact ⟨hz.1, hphase⟩
  have hLiveMassLocalized : (μ).real (Dset ∩ liveGate) ≤ (μ).real (Dset ∩ P234) :=
    measureReal_mono hliveSubset
  have hmass :=
    ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_local_gate_mass_le
      rate rewards C_star C_h control0 ids t
  have hshared :
      (∫ z in Dset,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z ∂μ) +
        ∫ z in Dset,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z ∂μ +
        ∑ u : Fin p.T, ∫ z in Dset,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ ≤
      c * ((μ).real (Dset ∩ P234) + (μ).real (Dset ∩ oldGate) +
        ∑ u : Fin p.T, (μ).real
          (Dset ∩ ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t)) := by
    calc
      _ ≤ (c * (μ).real (Dset ∩ liveGate) + c * (μ).real (Dset ∩ oldGate)) +
          ∑ u : Fin p.T, c * (μ).real
            (Dset ∩ ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u t) := by
        apply add_le_add
        · exact add_le_add hLiveMass hOldMass
        · exact Finset.sum_le_sum fun u _ => hCurrentMass u
      _ = c * ((μ).real (Dset ∩ liveGate) + (μ).real (Dset ∩ oldGate) +
          ∑ u : Fin p.T, (μ).real
            (Dset ∩ ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u t)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := by
        have hscaled := mul_le_mul_of_nonneg_left hLiveMassLocalized hc
        nlinarith [hscaled]
  calc
    _ ≤ c * ((μ).real (Dset ∩ P234) + (μ).real (Dset ∩ oldGate) +
        ∑ u : Fin p.T, (μ).real
          (Dset ∩ ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t)) := hshared
    _ ≤ c * (μ).real Dset := mul_le_mul_of_nonneg_left hmass hc
    _ = c * (CompletePublicTable.idArrayMeasure p).real {ids} := by
      rw [ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_source_mass_eq_idAtom
        ids]

/-- At one calendar date, the LIVE, OLD, and all CURRENT floors share the
actual fixed-ID gate-mass budget. -/
public theorem sharedCalendarFloor_setIntegral_fixedID_le
    (t : Fin p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    ((∫ z in Dset,
        ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
      ∫ z in Dset,
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ∂μ) +
      ∑ u : Fin p.T, ∫ z in Dset,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z ∂μ ≤
      (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ)) *
        (CompletePublicTable.idArrayMeasure p).real {ids} := by
  exact sharedFloorSetIntegrals_le rate rewards C_star C_h control0 ids t S

private def sharedFloorAtDate (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
    rate rewards C_star C_h t S z) +
  (ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
    rate rewards C_star C_h t S z) +
  ∑ u : Fin p.T,
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
      rate rewards C_star C_h u t S z

/-- The original-calendar floor sum has one sharp `m/scale` charge for every
date, weighted by the original, unnormalized fixed-ID atom. -/
public theorem originalCalendarFloorLoss_setIntegral_fixedID_le_horizon
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in Dset,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S z ∂μ) ≤
      (CompletePublicTable.idArrayMeasure p).real {ids} *
        (p.m : ℝ) * (p.T : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  let dateFloor := sharedFloorAtDate rate rewards C_star C_h
  let alpha := (CompletePublicTable.idArrayMeasure p).real {ids}
  have hfloorEq :
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S = fun z =>
        ∑ t : Fin p.T, dateFloor t S z := by
    funext z
    unfold dateFloor sharedFloorAtDate
    change
      ((∑ t : Fin p.T,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z) +
        (∑ t : Fin p.T,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) = _
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  have hdateBound (t : Fin p.T) :
      (∫ z in Dset, dateFloor t S z ∂μ) ≤
        c * alpha := by
    have hLive :=
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0
    have hOld :=
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S
    have hCurrent (u : Fin p.T) :=
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
        rate rewards C_star C_h control0 u t S
    have hCurrentSum : IntegrableOn
        (fun z : SourceInput p => ∑ u : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) Dset μ :=
      integrable_finsetSum Finset.univ (fun u _ => (hCurrent u).integrableOn)
    have hExpand :
        (∫ z in Dset, dateFloor t S z ∂μ) =
          (∫ z in Dset,
            ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
              rate rewards C_star C_h t S z ∂μ) +
          ∫ z in Dset,
            ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
              rate rewards C_star C_h t S z ∂μ +
          ∑ u : Fin p.T, ∫ z in Dset,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
              rate rewards C_star C_h u t S z ∂μ := by
      have hLiveOn : IntegrableOn
          (ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S) Dset μ := hLive.integrableOn
      have hOldOn : IntegrableOn
          (ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S) Dset μ := hOld.integrableOn
      have hLiveOldOn : IntegrableOn
          (fun z : SourceInput p =>
            ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h t S z +
              ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h t S z) Dset μ := hLiveOn.add hOldOn
      calc
        _ = (∫ z in Dset,
              ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h t S z ∂μ) +
            ∫ z in Dset,
              ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h t S z ∂μ +
            ∫ z in Dset, (∑ u : Fin p.T,
              ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                rate rewards C_star C_h u t S z) ∂μ := by
          change (∫ z, dateFloor t S z ∂((sourceInputLaw p).restrict Dset)) = _
          unfold dateFloor sharedFloorAtDate
          calc
            _ = (∫ z, (ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                    rate rewards C_star C_h t S z +
                  ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                    rate rewards C_star C_h t S z) ∂((sourceInputLaw p).restrict Dset)) +
                ∫ z, (∑ u : Fin p.T,
                  ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                    rate rewards C_star C_h u t S z) ∂((sourceInputLaw p).restrict Dset) :=
              integral_add hLiveOldOn hCurrentSum
            _ = _ := by
              rw [integral_add hLiveOn hOldOn]
        _ = _ := by
          rw [integral_finsetSum Finset.univ (fun u _ =>
            (hCurrent u).integrableOn (s := Dset))]
    calc
      _ = _ := hExpand
      _ ≤ _ := sharedCalendarFloor_setIntegral_fixedID_le
        rate rewards C_star C_h control0 ids t S
  have hdateIntegrable (t : Fin p.T) : IntegrableOn (dateFloor t S) Dset μ := by
    have hLive :=
      ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0
    have hOld :=
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S
    have hCurrent (u : Fin p.T) :=
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
        rate rewards C_star C_h control0 u t S
    have hCurrentSum : IntegrableOn
        (fun z : SourceInput p => ∑ u : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) Dset μ :=
      integrable_finsetSum Finset.univ (fun u _ => (hCurrent u).integrableOn)
    change IntegrableOn
      (fun z => ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S z +
        ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z +
        ∑ u : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) Dset μ
    exact hLive.integrableOn.add hOld.integrableOn |>.add hCurrentSum
  have hsumBound :
      (∫ z in Dset, (∑ t : Fin p.T, dateFloor t S z) ∂μ) ≤
        ∑ t : Fin p.T, c * alpha := by
    rw [integral_finsetSum Finset.univ (fun t _ => hdateIntegrable t)]
    exact Finset.sum_le_sum fun t _ => hdateBound t
  calc
    _ = ∫ z in Dset, (∑ t : Fin p.T, dateFloor t S z) ∂μ := by
      exact setIntegral_congr_fun
        (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
        (fun z _ => congrFun hfloorEq z)
    _ ≤ ∑ t : Fin p.T, c * alpha := hsumBound
    _ = alpha * (p.m : ℝ) * (p.T : ℝ) /
        (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [alpha]
      ring

end Bandits.Support.ReferenceFirstCollectionFixedIDOldCurrentCalendarRounding

end
