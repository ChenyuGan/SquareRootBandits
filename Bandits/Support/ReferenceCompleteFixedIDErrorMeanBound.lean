/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteErrorSelectedRowProbability
public import Bandits.Support.ReferenceCompleteInclusiveDecoderFixedIDBudget
public import Bandits.Support.ReferenceOriginalCalendarFixedIDOverflowBound
public import Bandits.Support.ActualReferenceInitializationCouplingProbability

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-ID bound for the complete reference error mean

The initialization term is transported from the actual original private
coordinates to the accepted complete-row flag integral. The other two terms
are the inclusive decoder union and physical first-overflow event under the
same fixed-ID source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ReferenceCompleteErrorSelectedRowProbability
open Bandits.Support.ReferenceCompleteInclusiveDecoderFixedIDBudget
open Bandits.Support.ReferenceOriginalCalendarFixedIDOverflowBound
open scoped ENNReal

namespace Bandits.Support.ReferenceCompleteFixedIDErrorMeanBound

abbrev Parameters := ConstructorDimensions.Parameters

/-- The literal fixed-ID source law is the original point-mass ID product
with the unchanged complete-row and private-coordinate factors. -/
private theorem fixedIDSourceLaw_eq_literalProduct
    {p : Parameters} (ids : CompletePublicTable.IDArray p) :
    ReferenceFixedIDSourceSection.fixedIDSourceLaw ids =
      ((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  rw [ReferenceFixedIDSourceSection.fixedIDSourceLaw_eq_fixedIDPublishedOutputProduct]
  rfl

/-- The mass of the actual source initialization event at a fixed ID equals
the accepted average actual-row initialization flag integral. -/
public theorem sourceInitializationFailureEvent_fixedIDSourceLaw_eq_eInitFlagIntegral
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p) :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
          rate rewards C_star C_h) =
      ∫ row : CompletePublicTable.CompleteRow p,
        InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta row
          ∂CompletePublicTable.completeRowMeasure p := by
  let E := ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
    rate rewards C_star C_h
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  let I : BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
    E.indicator (fun _ => (1 : ℝ))
  have hE : MeasurableSet E :=
    ReferenceCompleteErrorSelectedRowProbability.measurableSet_sourceInitializationFailureEvent
      rate rewards C_star C_h
  have hImeas : Measurable I := measurable_const.indicator hE
  have hIint : Integrable I ν := by
    apply Integrable.of_mem_Icc 0 1 hImeas.aemeasurable
    apply ae_of_all
    intro z
    by_cases hz : z ∈ E <;> simp [I, hz]
  let A : Set (CompletePublicTable.CompleteRows p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
    {w | w.2 ∈ InitializationRowObservables.actualInitializationFailureEvent
      p ids rewards C_star C_h rate.eta w.1}
  let J : CompletePublicTable.CompleteRows p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p → ℝ :=
    A.indicator (fun _ => (1 : ℝ))
  have hA : MeasurableSet A :=
    InitializationRowObservables.measurable_actualInitializationFailureEvent_pair
      p ids rewards C_star C_h rate.eta
  have hJmeas : Measurable J := measurable_const.indicator hA
  have hJint : Integrable J
      ((CompletePublicTable.completeRowsMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
    apply Integrable.of_mem_Icc 0 1 hJmeas.aemeasurable
    apply ae_of_all
    intro w
    by_cases hw : w ∈ A <;> simp [J, hw]
  have hIinsert :
      (fun w : CompletePublicTable.CompleteRows p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        I (ReferenceFixedIDSourceSection.fixedIDSourceInsertion ids w)) = J := by
    funext w
    rcases w with ⟨rows, e⟩
    rfl
  have hinner (rows : CompletePublicTable.CompleteRows p) :
      (∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
        J (rows, e) ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
            (rows j) := by
    have hsection :
        (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => J (rows, e)) =
          (InitializationRowObservables.actualInitializationFailureEvent
            p ids rewards C_star C_h rate.eta rows).indicator (fun _ => (1 : ℝ)) := by
      funext e
      rfl
    calc
      _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
          (InitializationRowObservables.actualInitializationFailureEvent
            p ids rewards C_star C_h rate.eta rows) := by
          rw [hsection]
          exact integral_indicator_one
            (InitializationRowObservables.measurable_actualInitializationFailureEvent
              p ids rewards C_star C_h rate.eta rows)
      _ = _ :=
        InitializationRowObservables.actual_initializationFailure_probability_eq_average
          p ids rewards C_star C_h rate.eta rows
  have hEventAverage :
      (∫ w : CompletePublicTable.CompleteRows p ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
        J w ∂(CompletePublicTable.completeRowsMeasure p).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) =
      ∫ rows : CompletePublicTable.CompleteRows p,
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
              (rows j) ∂CompletePublicTable.completeRowsMeasure p := by
    calc
      _ = ∫ rows : CompletePublicTable.CompleteRows p,
          ∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
            J (rows, e) ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
            ∂CompletePublicTable.completeRowsMeasure p := integral_prod _ hJint
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with rows
        exact hinner rows
  let S : Finset (Fin p.K) := Finset.Iio (⟨p.m, p.m_lt_K⟩ : Fin p.K)
  have hS : S.card = p.m := by simp [S]
  have hf := InitializationRowObservables.actual_observables_product_fubini
    p ids rewards C_star C_h rate.eta S hS
  have hfFlag := congrArg Prod.snd hf
  have hfInitFlag : Integrable
      (InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta)
      (CompletePublicTable.completeRowMeasure p) :=
    InitializationRowObservables.integrable_e_initFlag p ids rewards C_star C_h rate.eta
  have hrowTerms (j : Fin (ConstructorDimensions.M p)) : Integrable
      (fun rows : CompletePublicTable.CompleteRows p =>
        InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta (rows j))
      (CompletePublicTable.completeRowsMeasure p) :=
    (CompletePublicTable.measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
      hfInitFlag
  have hrowAverage :
      (∫ rows : CompletePublicTable.CompleteRows p,
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
              (rows j) ∂CompletePublicTable.completeRowsMeasure p) =
      ∫ row : CompletePublicTable.CompleteRow p,
        InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta row
          ∂CompletePublicTable.completeRowMeasure p := by
    calc
      _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            ∫ rows : CompletePublicTable.CompleteRows p,
              InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
                (rows j) ∂CompletePublicTable.completeRowsMeasure p := by
          rw [integral_const_mul, integral_finsetSum Finset.univ (fun j hj => hrowTerms j)]
      _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            ∫ row : CompletePublicTable.CompleteRow p,
              InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta row
                ∂CompletePublicTable.completeRowMeasure p := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hFae : AEStronglyMeasurable
              (InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta)
              ((CompletePublicTable.completeRowsMeasure p).map
                (fun rows : CompletePublicTable.CompleteRows p => rows j)) := by
            simpa only [CompletePublicTable.map_completeRowProjection] using
              hfInitFlag.aestronglyMeasurable
          rw [← integral_map
              (CompletePublicTable.measurable_completeRowProjection p j).aemeasurable hFae,
            CompletePublicTable.map_completeRowProjection]
      _ = ∫ row : CompletePublicTable.CompleteRow p,
          InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta row
            ∂CompletePublicTable.completeRowMeasure p := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hMpos : 0 < (ConstructorDimensions.M p : ℝ) :=
            Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
          field_simp [ne_of_gt hMpos]
  calc
    _ = ∫ z : BootstrapPrivateRoundStreams.SourceInput p, I z ∂ν :=
      (integral_indicator_one hE).symm
    _ = ∫ w : CompletePublicTable.CompleteRows p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
          I (ReferenceFixedIDSourceSection.fixedIDSourceInsertion ids w)
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) :=
      ReferenceFixedIDSourceSection.fixedIDSourceLaw_integral_eq_insertion ids I hIint
    _ = ∫ w : CompletePublicTable.CompleteRows p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
          J w ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by rw [hIinsert]
    _ = ∫ rows : CompletePublicTable.CompleteRows p,
          (1 / (ConstructorDimensions.M p : ℝ)) *
            ∑ j : Fin (ConstructorDimensions.M p),
              InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
                (rows j) ∂CompletePublicTable.completeRowsMeasure p := hEventAverage
    _ = ∫ w : CompletePublicTable.CompleteRows p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
          InitializationRowObservables.actualInitializationFailureIndicator
            p ids rewards C_star C_h rate.eta w.1 w.2
          ∂(CompletePublicTable.completeRowsMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := hfFlag.symm
    _ = ∫ rows : CompletePublicTable.CompleteRows p,
          (1 / (ConstructorDimensions.M p : ℝ)) *
            ∑ j : Fin (ConstructorDimensions.M p),
              InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta
                (rows j) ∂CompletePublicTable.completeRowsMeasure p := hfFlag
    _ = ∫ row : CompletePublicTable.CompleteRow p,
          InitializationRowObservables.e_initFlag p ids rewards C_star C_h rate.eta row
            ∂CompletePublicTable.completeRowMeasure p := hrowAverage

/-- The fixed-ID initialization source-event probability retains both
accepted initialization estimates under only the source good-ID and constant
premises. -/
public theorem sourceInitializationFailureEvent_fixedIDSourceLaw_bounds
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
          rate rewards C_star C_h) ≤
        5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ∧
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
          rate rewards C_star C_h) ≤
        5 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  rw [sourceInitializationFailureEvent_fixedIDSourceLaw_eq_eInitFlagIntegral]
  exact GeneratedInitializationFailureTail.e_initFlag_integral_bounds
    p ids rewards C_star C_h rate.eta hgood hC_h hCstar

/-- Under the literal complete-error union, the combined stopped decoder
failure is charged once and physical first overflow is charged once. -/
public theorem completeErrorEvent_fixedIDSourceLaw_le_init_add_two_over_N_sq
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
          rate rewards C_star C_h) ≤
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  have hLawProduct := fixedIDSourceLaw_eq_literalProduct ids
  have hDecoder : ν.real
      (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
        rate rewards C_star C_h) ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    change (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real _ ≤ _
    rw [hLawProduct]
    exact completeInclusiveDecoderFailureEvent_fixedID_measureReal_le
        rate rewards C_star C_h control0 ids
  have hOverflow :=
    physicalFirstOverflowEvent_fixedIDSourceLaw_le_inv_N_sq
      rate rewards C_star C_h control0 ids
  have hUnion :
      ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
          rate rewards C_star C_h =
        ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h ∪
          (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
              rate rewards C_star C_h ∪
            ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
              rate rewards C_star C_h) := by
    ext z
    simp [ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent,
      ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent,
      Set.union_assoc]
  calc
    _ = ν.real (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
          rate rewards C_star C_h ∪
        (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
            rate rewards C_star C_h ∪
          ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
            rate rewards C_star C_h)) := congrArg ν.real hUnion
    _ ≤ ν.real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        (ν.real
            (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
              rate rewards C_star C_h) +
          ν.real
            (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
              rate rewards C_star C_h)) := by
      calc
        _ ≤ ν.real
              (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
                rate rewards C_star C_h) +
            ν.real
              (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
                  rate rewards C_star C_h ∪
                ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
                  rate rewards C_star C_h) := MeasureTheory.measureReal_union_le _ _
        _ ≤ _ := add_le_add le_rfl (MeasureTheory.measureReal_union_le _ _)
    _ ≤ ν.real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        (1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
          1 / (ConstructorDimensions.N p : ℝ) ^ 2) :=
      add_le_add le_rfl (add_le_add hDecoder hOverflow)
    _ = ν.real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by ring

/-- The literal complete-error mean is nonnegative. -/
public theorem completeErrorMean_nonneg
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p) :
    0 ≤ ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
      rate rewards C_star C_h ids := by
  rw [ReferenceCompleteErrorSelectedRowProbability.completeErrorMean_eq_fixedID_sourceEvent_measure]
  exact MeasureTheory.measureReal_nonneg

/-- The literal complete-error mean is at most `13/(4 N^2)` for every
good identification array and the unrestricted original witnesses. -/
public theorem completeErrorMean_le_13_over_four_N_sq
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
      rate rewards C_star C_h ids ≤
        13 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  have hLawProduct := fixedIDSourceLaw_eq_literalProduct ids
  have hMeanLaw :
      ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
        rate rewards C_star C_h ids =
      ν.real (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
        rate rewards C_star C_h) := by
    calc
      _ = (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
            (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
              rate rewards C_star C_h) :=
        completeErrorMean_eq_fixedID_sourceEvent_measure rate rewards C_star C_h ids
      _ = _ := by rw [← hLawProduct]
  have hInit := sourceInitializationFailureEvent_fixedIDSourceLaw_bounds
    rate rewards C_star C_h ids hgood hC_h hCstar
  have hUnion := completeErrorEvent_fixedIDSourceLaw_le_init_add_two_over_N_sq
    rate rewards C_star C_h control0 ids
  have hN2pos : 0 < (ConstructorDimensions.N p : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)) 2
  calc
    _ = ν.real (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
          rate rewards C_star C_h) := hMeanLaw
    _ ≤ ν.real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := hUnion
    _ ≤ 5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := add_le_add hInit.1 le_rfl
    _ = 13 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
      field_simp [ne_of_gt hN2pos]
      ring

/-- The source-compatible coarser estimate keeps the initialization budget as
`5/N^2` and adds the two fixed-ID error budgets. -/
public theorem completeErrorMean_le_five_over_N_sq_add_two_over_N_sq
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
      rate rewards C_star C_h ids ≤
        5 / (ConstructorDimensions.N p : ℝ) ^ 2 +
          2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
  have hLawProduct := fixedIDSourceLaw_eq_literalProduct ids
  have hMeanLaw :
      ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
        rate rewards C_star C_h ids =
      ν.real (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
        rate rewards C_star C_h) := by
    calc
      _ = (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
            (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
              rate rewards C_star C_h) :=
        completeErrorMean_eq_fixedID_sourceEvent_measure rate rewards C_star C_h ids
      _ = _ := by rw [← hLawProduct]
  have hInit := sourceInitializationFailureEvent_fixedIDSourceLaw_bounds
    rate rewards C_star C_h ids hgood hC_h hCstar
  have hUnion := completeErrorEvent_fixedIDSourceLaw_le_init_add_two_over_N_sq
    rate rewards C_star C_h control0 ids
  calc
    _ = ν.real (ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
          rate rewards C_star C_h) := hMeanLaw
    _ ≤ ν.real
          (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
            rate rewards C_star C_h) +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := hUnion
    _ ≤ 5 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := add_le_add hInit.2 le_rfl

/-- The source-compatible complete-error mean estimate is `7/N^2`. -/
public theorem completeErrorMean_le_seven_over_N_sq
    {p : Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p)
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h) (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    ReferenceCompleteErrorSelectedRowProbability.completeErrorMean
      rate rewards C_star C_h ids ≤
        7 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  calc
    _ ≤ 5 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 :=
      completeErrorMean_le_five_over_N_sq_add_two_over_N_sq
        rate rewards C_star C_h control0 ids hgood hC_h hCstar
    _ = 7 / (ConstructorDimensions.N p : ℝ) ^ 2 := by ring

end Bandits.Support.ReferenceCompleteFixedIDErrorMeanBound

end
