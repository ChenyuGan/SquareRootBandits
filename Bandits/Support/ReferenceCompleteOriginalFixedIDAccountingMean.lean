/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalSignedAccounting
public import Bandits.Support.ReferenceCompleteFixedIDErrorMeanBound

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

/-!
# Physical regret mean from complete original-ID signed accounting

The complete physical reward is averaged under the same exhaustive terminal
law whose signed archive expectation remains explicit. Startup, signed stopped
transport, and the inclusive first-bad event are charged on the corresponding
literal original fixed-ID source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical ENNReal
open Bandits.Support
open ReferenceCompleteOriginalSignedAccounting
open ReferenceOriginalStartupFixedIDMean
open ReferenceOriginalStoppedTransportFixedIDMean
open ReferenceCompleteSignedFirstBadCalendar
open ReferenceCompleteInclusiveDecoderFixedIDBudget
open ReferenceOriginalCalendarFixedIDOverflowBound

namespace Bandits.Support.ReferenceCompleteOriginalFixedIDAccountingMean

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

private theorem fixedIDSourceLaw_eq_literalProduct
    (ids : CompletePublicTable.IDArray p) :
    ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids =
      ((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  rw [ReferenceFixedIDSourceSection.fixedIDSourceLaw_eq_fixedIDPublishedOutputProduct]
  rfl

private theorem measurable_generatedOutput_source :
    Measurable (fun z : SourceInput p =>
      ReferenceInitializationRun.output
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)) := by
  have hindex : Measurable (fun z : SourceInput p =>
      PrivateSourceStreams.coordinatorIndex p z.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hselected : Measurable (fun z : SourceInput p =>
      z.1.2 (PrivateSourceStreams.coordinatorIndex p z.2.1.2)) := by
    have heval : Measurable
        (fun w : Fin (ConstructorDimensions.M p) × SourceInput p => w.2.1.2 w.1) := by
      apply measurable_from_prod_countable_right
      intro j
      exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
    exact heval.comp (hindex.prodMk measurable_id)
  have hcoordinates : Measurable
      (fun z : SourceInput p =>
        (z.1.1, (z.1.2 (PrivateSourceStreams.coordinatorIndex p z.2.1.2), z.2)) :
        SourceInput p → ReferenceInitializationMeasurability.InputCoordinates p) := by
    exact (measurable_fst.comp measurable_fst).prodMk
      (hselected.prodMk measurable_snd)
  have hcoordinates_eq :
      (fun z : SourceInput p =>
        ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)) =
      (fun z : SourceInput p =>
        ReferenceInitializationRun.output
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h rate.eta
            rewards (z.1.1, (z.1.2
              (PrivateSourceStreams.coordinatorIndex p z.2.1.2), z.2)))) := by
    funext z
    rfl
  rw [hcoordinates_eq]
  exact (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h rate.eta rewards).comp hcoordinates

private theorem measurable_startupComparatorCharge
    (S : Finset (Fin p.K)) :
    Measurable (fun z : SourceInput p =>
      startupComparatorCharge rate z rewards C_star C_h S) := by
  exact (InitializationRowObservables.measurable_comparatorChargeAtBoundary
    p rewards S).comp (measurable_generatedOutput_source rate rewards C_star C_h)

private theorem badWithinHorizon_eq_indicator
    (z : SourceInput p) :
    SignedStoppedRegretAccounting.badWithinHorizon p.T
        (firstBadDate rate rewards C_star C_h z) =
      (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h ∪
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h).indicator (fun _ => (1 : ℝ)) z := by
  classical
  simp only [SignedStoppedRegretAccounting.badWithinHorizon, Set.indicator_apply]
  by_cases hb : firstBadDate rate rewards C_star C_h z ≤ p.T
  · have he := (firstBadDate_le_T_iff_event_union rate rewards C_star C_h z).mp hb
    rw [ite_eq_left hb, ite_eq_left he]
  · have he : z ∉
        (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
            rate rewards C_star C_h ∪
          ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
            rate rewards C_star C_h) := by
      intro hz
      exact hb ((firstBadDate_le_T_iff_event_union rate rewards C_star C_h z).mpr hz)
    rw [ite_eq_right hb, ite_eq_right he]

/-- The actual inclusive first-bad indicator has exactly the decoder/overflow
union as its event, and its fixed-ID expectation is at most `2/N^2`. The union
includes the first overflow update and excludes the distinct initialization
failure event. -/
public theorem fixedID_badWithinHorizon_integral_le_two_over_N_sq
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (∫ z : SourceInput p,
      SignedStoppedRegretAccounting.badWithinHorizon p.T
        (firstBadDate rate rewards C_star C_h z)
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  let E := ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
      rate rewards C_star C_h ∪
    ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
      rate rewards C_star C_h
  let I : SourceInput p → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hE : MeasurableSet E :=
    (ReferenceCompleteInclusivePhysicalDecoderErrors.measurableSet_completeInclusiveDecoderFailureEvent
      rate rewards C_star C_h).union
      (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_physicalFirstOverflowEvent
        rate rewards C_star C_h)
  have hImeas : Measurable I := measurable_const.indicator hE
  have hIint : Integrable I ν := by
    apply Integrable.of_mem_Icc 0 1 hImeas.aemeasurable
    apply ae_of_all
    intro z
    by_cases hz : z ∈ E <;> simp [I, hz]
  have hbadEq :
      (fun z : SourceInput p =>
        SignedStoppedRegretAccounting.badWithinHorizon p.T
          (firstBadDate rate rewards C_star C_h z)) = I := by
    funext z
    exact badWithinHorizon_eq_indicator rate rewards C_star C_h z
  have hbadIntegral :
      (∫ z : SourceInput p,
        SignedStoppedRegretAccounting.badWithinHorizon p.T
          (firstBadDate rate rewards C_star C_h z) ∂ν) = ν.real E := by
    rw [hbadEq]
    exact integral_indicator_one hE
  have hLaw := fixedIDSourceLaw_eq_literalProduct (p := p) ids
  have hdecoder : ν.real
      (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
        rate rewards C_star C_h) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    change (ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids).real _ ≤ _
    rw [hLaw]
    exact completeInclusiveDecoderFailureEvent_fixedID_measureReal_le
      rate rewards C_star C_h control0 ids
  have hoverflow :=
    physicalFirstOverflowEvent_fixedIDSourceLaw_le_inv_N_sq
      rate rewards C_star C_h control0 ids
  have hunion : ν.real E ≤
      ν.real (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h) +
        ν.real (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h) := by
    exact MeasureTheory.measureReal_union_le _ _
  have hsum :
      ν.real (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h) +
        ν.real (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h) ≤
        1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
          1 / (ConstructorDimensions.N p : ℝ) ^ 2 :=
    add_le_add hdecoder hoverflow
  have htwo :
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        1 / (ConstructorDimensions.N p : ℝ) ^ 2 =
        2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by ring
  rw [hbadIntegral]
  exact hunion.trans (hsum.trans_eq htwo)

/-- The same exhaustive original-ID terminal sample gives the physical mean
bound with its full signed auxiliary expectation still explicit. The strict
launch startup, signed stopped transport, and inclusive first-bad costs are
discharged using their accepted fixed-ID source-law estimates. -/
public theorem fixedID_physical_expected_regret_le_signedGap
    (ids : CompletePublicTable.IDArray p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∑ q : Fin p.T, ∑ a ∈ S0.val,
        ((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) -
        (∫ z : SourceInput p,
          ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids) ≤
      (∫ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h,
        ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S0
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
            rate rewards C_star C_h control0 w).2.2
        ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0 ids) +
      128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
        (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
        (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
          (4 * (ConstructorDimensions.b_N p : ℝ))) +
      (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2 +
      ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
        ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) +
      4 * (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids
  let μ := ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
    rate rewards C_star C_h control0 ids
  let compTotal : ℝ := ∑ q : Fin p.T, ∑ a ∈ S0.val,
    ((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ)
  let rewardSource : SourceInput p → ℝ := fun z =>
    ReferenceCompletePhysicalRewards.completeReward rate z rewards C_star C_h
  let startupSource : SourceInput p → ℝ := fun z =>
    startupComparatorCharge rate z rewards C_star C_h S0.val
  let badSource : SourceInput p → ℝ := fun z =>
    SignedStoppedRegretAccounting.badWithinHorizon p.T
      (firstBadDate rate rewards C_star C_h z)
  let rewardTerminal : _ → ℝ := fun w =>
    rewardSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
      rate rewards C_star C_h control0 w)
  let startupTerminal : _ → ℝ := fun w =>
    startupSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
      rate rewards C_star C_h control0 w)
  let jTerminal : _ → ℝ := fun w =>
    ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 w)
  let badTerminal : _ → ℝ := fun w =>
    badSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
      rate rewards C_star C_h control0 w)
  let gapTerminal : _ → ℝ := fun w =>
    ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S0
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
        rate rewards C_star C_h control0 w).2.2
  let leftTerminal : _ → ℝ := fun w => compTotal - rewardTerminal w
  let badWeight : ℝ := 2 * (p.m : ℝ) * (p.T : ℝ)
  let rightTerminal : _ → ℝ := fun w =>
    startupTerminal w + gapTerminal w + jTerminal w + badWeight * badTerminal w

  have hS : S0.val ∈ ProductSetLaw.support p.K p.m := S0.property
  have hRewardMeas : Measurable rewardSource :=
    ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h
  have hRewardInt : Integrable rewardSource ν := by
    have hbound (z : SourceInput p) : ‖rewardSource z‖ ≤ (p.m : ℝ) * (p.T : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (ReferenceCompletePhysicalRewards.completeReward_bounds rate z rewards C_star C_h).1]
      exact (ReferenceCompletePhysicalRewards.completeReward_bounds rate z rewards C_star C_h).2
    refine (integrable_const ((p.m : ℝ) * (p.T : ℝ))).mono'
      hRewardMeas.aestronglyMeasurable ?_
    exact ae_of_all _ hbound
  have hStartupMeas : Measurable startupSource :=
    measurable_startupComparatorCharge rate rewards C_star C_h S0.val
  have hStartupInt : Integrable startupSource ν :=
    integrable_startupComparatorCharge rate rewards C_star C_h S0.val ids hS
  have hJInt : Integrable
      (ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h) ν :=
    J_stop_integrable_fixedID rate rewards C_star C_h control0 ids
  have hBadEq : badSource = fun z =>
      (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h ∪
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h).indicator (fun _ => (1 : ℝ)) z := by
    funext z
    exact badWithinHorizon_eq_indicator rate rewards C_star C_h z
  have hBadMeas : Measurable badSource := by
    rw [hBadEq]
    exact measurable_const.indicator
      ((ReferenceCompleteInclusivePhysicalDecoderErrors.measurableSet_completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h).union
        (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_physicalFirstOverflowEvent
          rate rewards C_star C_h))
  have hBadInt : Integrable badSource ν := by
    let E := ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
        rate rewards C_star C_h ∪
      ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h
    let I : SourceInput p → ℝ := E.indicator (fun _ => (1 : ℝ))
    have hI : Integrable I ν := by
      apply Integrable.of_mem_Icc 0 1
        (measurable_const.indicator
          ((ReferenceCompleteInclusivePhysicalDecoderErrors.measurableSet_completeInclusiveDecoderFailureEvent
              rate rewards C_star C_h).union
            (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_physicalFirstOverflowEvent
              rate rewards C_star C_h))).aemeasurable
      apply ae_of_all
      intro z
      by_cases hz : z ∈ E <;> simp [E, hz]
    exact hI.congr (ae_of_all _ fun z => (congrFun hBadEq z).symm)

  have hRewardTerminalInt : Integrable rewardTerminal μ := by
    change Integrable
      (fun w => rewardSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 w))
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
        rate rewards C_star C_h control0 ids)
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_integrable_source_iff
      rate rewards C_star C_h control0 ids rewardSource hRewardMeas).2 hRewardInt
  have hStartupTerminalInt : Integrable startupTerminal μ := by
    change Integrable
      (fun w => startupSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 w))
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
        rate rewards C_star C_h control0 ids)
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_integrable_source_iff
      rate rewards C_star C_h control0 ids startupSource hStartupMeas).2 hStartupInt
  have hJMapInt : Integrable
      (ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h)
      ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
        rate rewards C_star C_h control0 ids).map
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
            rate rewards C_star C_h control0)) := by
    rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source
      rate rewards C_star C_h control0 ids]
    exact hJInt
  have hJTerminalInt : Integrable jTerminal μ := by
    change Integrable
      (fun w => ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
          rate rewards C_star C_h control0 w))
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
        rate rewards C_star C_h control0 ids)
    exact (integrable_map_measure hJMapInt.aestronglyMeasurable
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource
        rate rewards C_star C_h control0).aemeasurable).mp hJMapInt
  have hBadTerminalInt : Integrable badTerminal μ := by
    change Integrable
      (fun w => badSource (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 w))
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
        rate rewards C_star C_h control0 ids)
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_integrable_source_iff
      rate rewards C_star C_h control0 ids badSource hBadMeas).2 hBadInt
  have hGapTerminalInt : Integrable gapTerminal μ := by
    simpa [gapTerminal, μ, Option.elim] using
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.integrable_signedGap
        rate rewards C_star C_h control0 (some ids) S0).1

  have hConstInt : Integrable (fun _ :
      ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h => compTotal) μ :=
    integrable_const _
  have hleftInt : Integrable leftTerminal μ := hConstInt.sub hRewardTerminalInt
  have hWeightedBadInt : Integrable (fun w => badWeight * badTerminal w) μ :=
    hBadTerminalInt.const_mul badWeight
  have hrightInt : Integrable rightTerminal μ := by
    exact hStartupTerminalInt.add hGapTerminalInt |>.add hJTerminalInt |>.add hWeightedBadInt

  have haccount :=
    ReferenceCompleteOriginalSignedAccounting.ae_reference_accounting
      rate rewards C_star C_h control0 S0 (some ids)
  have hpoint : ∀ᵐ w ∂μ, leftTerminal w ≤ rightTerminal w := by
    filter_upwards [haccount] with w hw
    simpa only [leftTerminal, rightTerminal, compTotal, rewardTerminal, rewardSource,
      startupTerminal, startupSource, jTerminal, gapTerminal, badTerminal, badSource,
      badWeight, ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource] using hw

  have hmono := integral_mono_ae hleftInt hrightInt hpoint
  have hleftIntegral :
      (∫ w, leftTerminal w ∂μ) = compTotal - ∫ z, rewardSource z ∂ν := by
    change (∫ w, compTotal - rewardTerminal w ∂μ) = _
    rw [integral_sub hConstInt hRewardTerminalInt]
    have hcomp : (∫ w, compTotal ∂μ) = compTotal := by simp [compTotal]
    rw [hcomp]
    have hreward := ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_source_integral
      rate rewards C_star C_h control0 ids rewardSource hRewardMeas
    have hreward' :
        (∫ w, rewardTerminal w ∂μ) = ∫ z, rewardSource z ∂ν := by
      simpa only [rewardTerminal, rewardSource, μ, ν] using hreward
    exact congrArg (fun x : ℝ => compTotal - x) hreward'
  have hstartupIntegral :
      (∫ w, startupTerminal w ∂μ) = ∫ z, startupSource z ∂ν := by
    simpa only [startupTerminal, startupSource, μ, ν] using
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_source_integral
        rate rewards C_star C_h control0 ids startupSource hStartupMeas)
  have hJIntegralSource :
      (∫ w, ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
          rate rewards C_star C_h control0 w)
        ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0 ids) =
        ∫ z, ReferenceOriginalStoppedTransportFixedIDMean.J_stop
          rate rewards C_star C_h z
          ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw (p := p) ids := by
    rw [← ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source
      rate rewards C_star C_h control0 ids]
    exact (integral_map
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource
        rate rewards C_star C_h control0).aemeasurable
      hJMapInt.aestronglyMeasurable).symm
  have hJIntegral :
      (∫ w, jTerminal w ∂μ) =
        ∫ z, ReferenceOriginalStoppedTransportFixedIDMean.J_stop
          rate rewards C_star C_h z ∂ν := by
    simpa only [jTerminal, μ, ν] using hJIntegralSource
  have hbadIntegral :
      (∫ w, badTerminal w ∂μ) = ∫ z, badSource z ∂ν := by
    simpa only [badTerminal, badSource, μ, ν] using
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_source_integral
        rate rewards C_star C_h control0 ids badSource hBadMeas)
  have hbadBound : ∫ z, badSource z ∂ν ≤
      2 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    simpa only [badSource] using
      fixedID_badWithinHorizon_integral_le_two_over_N_sq
        rate rewards C_star C_h control0 ids

  have hstartupBound := fixedIDSourceLaw_integral_startupComparatorCharge_le
    rate rewards C_star C_h S0.val ids hS
  have hJBound := J_stop_fixedID_mean_le rate rewards C_star C_h control0 ids
  have hbadWeightNonneg : 0 ≤ badWeight := by positivity
  have hweightedBadBound :
      badWeight * (∫ z, badSource z ∂ν) ≤
        4 * (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    change (2 * (p.m : ℝ) * (p.T : ℝ)) *
      (∫ z, badSource z ∂ν) ≤ _
    have h := mul_le_mul_of_nonneg_left hbadBound (by positivity :
      0 ≤ 2 * (p.m : ℝ) * (p.T : ℝ))
    calc
      2 * (p.m : ℝ) * (p.T : ℝ) * (∫ z, badSource z ∂ν) ≤
          2 * (p.m : ℝ) * (p.T : ℝ) *
            (2 / (ConstructorDimensions.N p : ℝ) ^ 2) := h
      _ = 4 * (p.m : ℝ) * (p.T : ℝ) /
          (ConstructorDimensions.N p : ℝ) ^ 2 := by ring

  calc
    _ = ∫ w, leftTerminal w ∂μ := by
      exact hleftIntegral.symm
    _ ≤ ∫ w, rightTerminal w ∂μ := hmono
    _ = (∫ z, startupSource z ∂ν) + (∫ w, gapTerminal w ∂μ) +
        (∫ z, ReferenceOriginalStoppedTransportFixedIDMean.J_stop
          rate rewards C_star C_h z ∂ν) +
        badWeight * (∫ z, badSource z ∂ν) := by
      calc
        _ = (∫ w, startupTerminal w + gapTerminal w + jTerminal w ∂μ) +
              ∫ w, badWeight * badTerminal w ∂μ := by
          exact integral_add
            (hStartupTerminalInt.add hGapTerminalInt |>.add hJTerminalInt)
            hWeightedBadInt
        _ = (∫ w, startupTerminal w + gapTerminal w ∂μ) +
              (∫ w, jTerminal w ∂μ) +
              ∫ w, badWeight * badTerminal w ∂μ := by
          exact congrArg (fun x : ℝ => x + (∫ w, badWeight * badTerminal w ∂μ))
            (integral_add (hStartupTerminalInt.add hGapTerminalInt) hJTerminalInt)
        _ = (∫ w, startupTerminal w ∂μ) + (∫ w, gapTerminal w ∂μ) +
              (∫ w, jTerminal w ∂μ) +
              ∫ w, badWeight * badTerminal w ∂μ := by
          exact congrArg
            (fun x : ℝ => x + (∫ w, jTerminal w ∂μ) +
              (∫ w, badWeight * badTerminal w ∂μ))
            (integral_add hStartupTerminalInt hGapTerminalInt)
        _ = _ := by
          rw [integral_const_mul, hstartupIntegral, hJIntegral, hbadIntegral]
    _ ≤ _ := by
      calc
        _ = (∫ w, gapTerminal w ∂μ) + (∫ z, startupSource z ∂ν) +
            (∫ z, ReferenceOriginalStoppedTransportFixedIDMean.J_stop
              rate rewards C_star C_h z ∂ν) +
            badWeight * (∫ z, badSource z ∂ν) := by ring
        _ ≤ (∫ w, gapTerminal w ∂μ) +
            (128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
              (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
              (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
                (4 * (ConstructorDimensions.b_N p : ℝ))) +
              (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2) +
            (ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
              ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2)) +
            (4 * (p.m : ℝ) * (p.T : ℝ) /
              (ConstructorDimensions.N p : ℝ) ^ 2) := by
          have hstart :
              (∫ w, gapTerminal w ∂μ) + (∫ z, startupSource z ∂ν) ≤
                (∫ w, gapTerminal w ∂μ) +
                  (128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
                    (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
                    (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
                      (4 * (ConstructorDimensions.b_N p : ℝ))) +
                    (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2) :=
            add_le_add le_rfl hstartupBound
          have htransport :
              ((∫ w, gapTerminal w ∂μ) + (∫ z, startupSource z ∂ν)) +
                  (∫ z, ReferenceOriginalStoppedTransportFixedIDMean.J_stop
                    rate rewards C_star C_h z ∂ν) ≤
                ((∫ w, gapTerminal w ∂μ) +
                  (128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
                    (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
                    (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
                      (4 * (ConstructorDimensions.b_N p : ℝ))) +
                    (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2)) +
                  (ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
                    ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2)) :=
            add_le_add hstart hJBound
          exact add_le_add htransport hweightedBadBound
        _ = (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap
              rate rewards S0
              (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
                rate rewards C_star C_h control0 w).2.2
              ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
                rate rewards C_star C_h control0 ids) +
            128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
              (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) +
              (p.m : ℝ) * (p.K : ℝ) * (BootstrapDimensions.B_boot p : ℝ) *
                (4 * (ConstructorDimensions.b_N p : ℝ))) +
            (p.m : ℝ) * (p.T : ℝ) / (ConstructorDimensions.N p : ℝ) ^ 2 +
            ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
              ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) +
            4 * (p.m : ℝ) * (p.T : ℝ) /
              (ConstructorDimensions.N p : ℝ) ^ 2 := by
          simp only [gapTerminal, μ]
          ring_nf

end Bandits.Support.ReferenceCompleteOriginalFixedIDAccountingMean

end
