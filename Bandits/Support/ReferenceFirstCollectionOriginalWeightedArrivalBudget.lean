/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift
public import Bandits.Support.ReferenceFirstCollectionCurrentOriginalRoundedComparison
public import Bandits.Support.ReferenceFirstLiveOriginalCalendarArrivalMoments
public import Bandits.Support.ReferenceFirstCollectionPrecallFirstCallMassBudget

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Original-source first-invocation weighted arrival budget

The datewise calendar expression combines the original LIVE, OLD, and actual
first-invocation CURRENT accepted arrivals on the unchanged source law. The
OLD and CURRENT terms are integrated by their pre-choice conditional moments;
the LIVE term uses its existing calendar moment result. This module supplies
only the stochastic first-moment component, not a pathwise prefix identity or
a source-facing regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionOriginalWeightedArrivalBudget

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance readoutOptionMeasurableSpace : MeasurableSpace
    (Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K)) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

/-- The literal LIVE calendar contribution, using the existing actual
first-live score marginal and accepted arrival. -/
public def liveCalendarWeightedArrival (t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rate rewards C_star C_h t i z

/-- The literal OLD calendar contribution, using the existing predictable
incoming marginal and the actual OLD recorder gate. -/
public def oldCalendarWeightedArrival (t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) z

/-- The literal CURRENT contribution for one actual invocation tag. -/
public def currentCalendarWeightedArrival (u t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z

/-- The one-date LIVE plus OLD plus all actual CURRENT calendar contributions.
All branches retain their source-defined zero extensions and unnormalized law.
-/
public def calendarWeightedArrival (t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  liveCalendarWeightedArrival rate rewards C_star C_h t z +
    (oldCalendarWeightedArrival rate rewards C_star C_h t z +
      ∑ u : Fin p.T, currentCalendarWeightedArrival rate rewards C_star C_h u t z)

/-- The first invocation's complete calendar weighted-arrival expression. -/
public def firstInvocationCalendarWeightedArrival
    (z : SourceInput p) : ℝ :=
  ∑ t : Fin p.T, calendarWeightedArrival rate rewards C_star C_h t z

private theorem oldIncomingTheta_measurable (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hbase : Measurable[F]
      (fun z : S => ReferenceFirstCollectionCurrentQueueEnergy.thetaOfOptionalWeights
        ((ReferenceFirstCollectionCurrentQueueReadout.before?
          rate rewards C_star C_h t z).map
            ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout) i) := by
    have hoption : Measurable (fun r? : Option
        (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) =>
          ReferenceFirstCollectionCurrentQueueEnergy.thetaOfOptionalWeights
            (r?.map ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout) i) :=
      measurable_of_countable _
    exact hoption.comp
      (ReferenceFirstCollectionCurrentQueueReadout.before?_measurable
        rate rewards C_star C_h control0 t)
  have hE : MeasurableSet[F]
      (ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t) :=
    ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_E
      rate rewards C_star C_h control0 t
  change Measurable[F]
    ((ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t).indicator (fun z =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaOfOptionalWeights
          ((ReferenceFirstCollectionCurrentQueueReadout.before?
            rate rewards C_star C_h t z).map
              ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout) i))
  exact hbase.indicator hE

private theorem oldIncomingTheta_bounds (t : Fin p.T) (i : Fin p.K)
    (z : S) :
    0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z ∧
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z ≤ 1 := by
  by_cases hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t
  · rw [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta,
      Set.indicator_of_mem hz]
    cases hr : ReferenceFirstCollectionCurrentQueueReadout.before?
        rate rewards C_star C_h t z with
    | none => simp [ReferenceFirstCollectionCurrentQueueEnergy.thetaOfOptionalWeights]
    | some r =>
      have hw (j : Fin p.K) :
          0 < ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout r j := by
        unfold ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout
        positivity
      change 0 ≤ ProductSetLaw.theta p.m
          (ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout r) i ∧
        ProductSetLaw.theta p.m
          (ReferenceFirstCollectionCurrentQueueEnergy.weightVectorOfReadout r) i ≤ 1
      exact ⟨(ProductSetLaw.theta_pos _ _
          (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hw).le,
        (ProductSetLaw.theta_lt_one _ _ (ConstructorDimensions.m_pos p)
          p.m_lt_K hw).le⟩
  · simp only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta,
      Set.indicator_of_notMem hz]
    exact ⟨le_rfl, zero_le_one⟩

private theorem oldIncomingTheta_sum_on_E_internal (t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t) :
    (∑ i : Fin p.K,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z) = (p.m : ℝ) := by
  obtain ⟨L, _, hL, _, _, _⟩ :=
    ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
      rate rewards C_star C_h t z hz
  have hbefore : ReferenceFirstCollectionCurrentQueueReadout.before?
      rate rewards C_star C_h t z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) := by
    have h := ReferenceFirstCollectionOldCalendarExponentialStep.precallReadout_eq_prefixReadout_on_E rate rewards C_star C_h t z hz
    exact h.symm.trans (by
      simp only [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL,
        Option.map_some])
  have htheta (i : Fin p.K) :
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z =
        ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) i := by
    simp only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta,
      Set.indicator_of_mem hz, hbefore]
    rfl
  have hsum := ProductSetLaw.sum_theta_eq_card
    (RecordedQueueRun.scoreWeight
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L))
    (ConstructorDimensions.m_pos p) p.m_lt_K
    (fun i => RecordedMarginalGrowth.state_scoreWeight_pos
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) i)
  calc
    _ = ∑ i : Fin p.K, ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact htheta i
    _ = (p.m : ℝ) := hsum

private theorem oldWeightedArrival_integrable_internal (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    Integrable (fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) mu := by
  let A := (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t i)
  have hA := (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp rate rewards C_star C_h control0 t i).2.2.2.2.1
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace S) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hθM : Measurable (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta rate rewards C_star C_h t i) :=
    Measurable.mono (oldIncomingTheta_measurable rate rewards C_star C_h
      control0 t i) hFle le_rfl
  have hθB (z : S) : ‖ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta rate rewards C_star C_h t i z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (oldIncomingTheta_bounds rate rewards C_star C_h t i z).1]
    exact (oldIncomingTheta_bounds rate rewards C_star C_h t i z).2
  have h := hA.bdd_mul hθM.aestronglyMeasurable (ae_of_all mu hθB)
  simpa only [A, mul_comm] using h

/-- The actual OLD incoming marginal is predictable in the exact pre-choice
filtration and remains in `[0,1]` on the whole original source. -/
public theorem oldIncomingTheta_predictable_bounds (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
        (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i) ∧
      ∀ z : S, 0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z ∧
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z ≤ 1 := by
  exact ⟨oldIncomingTheta_measurable rate rewards C_star C_h control0 t i,
    oldIncomingTheta_bounds rate rewards C_star C_h t i⟩

/-- On the actual OLD event, the incoming marginals are the normalized
same-run inclusion vector and sum to `m`. -/
public theorem oldIncomingTheta_sum_on_E (t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t) :
    (∑ i : Fin p.K,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z) = (p.m : ℝ) :=
  oldIncomingTheta_sum_on_E_internal rate rewards C_star C_h t z hz

/-- The original OLD weighted accepted-arrival product is integrable. -/
public theorem oldWeightedArrival_integrable (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    Integrable (fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) mu :=
    oldWeightedArrival_integrable_internal rate rewards C_star C_h control0 t i

/-- Pulling the original predictable OLD marginal through conditional
expectation gives its actual retained first-moment coefficient. -/
public theorem oldWeightedArrival_condExp (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    mu[(fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[mu]
      (fun z =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let A := (ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h t i)
  have hA := (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp rate rewards C_star C_h control0 t i).2.2.2.2.1
  have hθM : Measurable[F]
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i) :=
    oldIncomingTheta_measurable rate rewards C_star C_h control0 t i
  have hθB (z : S) : ‖ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta rate rewards C_star C_h t i z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (oldIncomingTheta_bounds rate rewards C_star C_h t i z).1]
    exact (oldIncomingTheta_bounds rate rewards C_star C_h t i z).2
  have hprod := oldWeightedArrival_integrable_internal rate rewards C_star C_h control0 t i
  have hθsm := hθM.stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hθsm hprod hA
  have hfirst :=
    (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
      rate rewards C_star C_h control0 t i).1
  filter_upwards [hpull, hfirst] with z hpull hfirst
  change mu[(fun z =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z * A z) | F] z =
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z * mu[A | F] z at hpull
  have hmoment : mu[A | F] z =
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z := by
    change mu[(ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
        (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h t i) | F] z = _ at hfirst
    simpa only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne] using hfirst
  exact hpull.trans (congrArg (fun x : ℝ =>
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
      rate rewards C_star C_h t i z * x) hmoment)

private theorem currentWeightedArrival_integrable_internal (control0 : TimeControl p)
    (u t : Fin p.T) (i : Fin p.K) :
    Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z) mu :=
  ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus_mul_retainedRaw_integrable
    rate rewards C_star C_h control0 u t i

/-- The actual CURRENT incoming marginal times its retained raw arrival is
integrable under the original source law. -/
public theorem currentWeightedArrival_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (i : Fin p.K) :
    Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z) mu :=
  currentWeightedArrival_integrable_internal rate rewards C_star C_h control0 u t i

/-- The original CURRENT product has the exact retained first conditional
moment, with the incoming `thetaMinus` coefficient. -/
public theorem currentWeightedArrival_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (i : Fin p.K) :
    mu[(fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[mu]
      (fun z =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
          rate rewards C_star C_h u t i z) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hraw := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_integrable
    rate rewards C_star C_h control0 u t i
  have hprod := currentWeightedArrival_integrable_internal rate rewards C_star C_h
    control0 u t i
  have hθ := ReferenceFirstCollectionCurrentQueueEnergy.measurable_thetaMinus
    rate rewards C_star C_h control0 u t i
  have hpull := condExp_mul_of_stronglyMeasurable_left hθ.stronglyMeasurable hprod hraw
  have hfirst := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_condExp
    rate rewards C_star C_h control0 u t i
  filter_upwards [hpull, hfirst] with z hpull hfirst
  change mu[(fun z =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z) |
      sourcePrefixFiltration control0 (t.val + 1)] z =
    ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
      rate rewards C_star C_h u t i z *
    mu[ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
      rate rewards C_star C_h u t i | sourcePrefixFiltration control0 (t.val + 1)] z at hpull
  exact hpull.trans (congrArg (fun x : ℝ =>
    ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
      rate rewards C_star C_h u t i z * x) hfirst)

private theorem currentMomentOne_bound_on_G (u t : Fin p.T) (i : Fin p.K)
    (z : S) (hz : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t) :
    0 ≤ ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z ∧
      ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z ≤ 1 := by
  have hb := ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne_roundedReward_bounds
    rate rewards C_star C_h u t i z
  rw [Set.indicator_of_mem hz] at hb
  exact ⟨hb.1, hb.2.1.trans hb.2.2⟩

private theorem currentMomentOne_zero_outside_G (u t : Fin p.T) (i : Fin p.K)
    (z : S) (hz : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
      rate rewards C_star C_h u t i z = 0 := by
  by_cases hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
      rate rewards C_star C_h t
  · have hfirst : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t := by
      intro hfirst
      exact hz ⟨hfirst, hH⟩
    simp only [ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne,
      Set.indicator_of_mem hH]
    simp [ReferenceFirstCollectionCurrentRawMoments.currentMomentOne, hfirst]
  · simp [ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne, hH]

private theorem oldMomentOne_bound_on_G (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K)
    (z : S) (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t) :
    0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z ∧
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z ≤ 1 := by
  have hm := (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_retainedRaw_sq_condExp
    rate rewards C_star C_h control0 t i).2.2.1 z
  change 0 ≤ ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
      rate rewards C_star C_h t i z ∧
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
      rate rewards C_star C_h t i z ≤
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun _ : S => (1 : ℝ)) z at hm
  rw [Set.indicator_of_mem hz] at hm
  exact hm

private theorem oldMomentOne_zero_outside_G (t : Fin p.T) (i : Fin p.K)
    (z : S) (hz : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t) :
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
      rate rewards C_star C_h t i z = 0 := by
  simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne,
    hz]

private theorem oldMomentOne_sum_bound (control0 : TimeControl p) (t : Fin p.T)
    (z : S) :
    (∑ i : Fin p.K,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z) ≤
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator (fun _ : S => (p.m : ℝ)) z := by
  by_cases hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t
  · have hE := hz.1.1
    rw [Set.indicator_of_mem hz]
    calc
      _ ≤ ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (oldMomentOne_bound_on_G rate rewards C_star C_h control0 t i z hz).2
          (oldIncomingTheta_bounds rate rewards C_star C_h t i z).1
      _ = (p.m : ℝ) := by
        simp only [mul_one]
        exact oldIncomingTheta_sum_on_E_internal rate rewards C_star C_h t z hE
  · have hzero (i : Fin p.K) :=
      oldMomentOne_zero_outside_G rate rewards C_star C_h t i z hz
    simp [hzero, Set.indicator_of_notMem hz]

private theorem currentTheta_sum_on_G (u t : Fin p.T) (z : S)
    (hz : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t) :
    (∑ i : Fin p.K,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z) = (p.m : ℝ) := by
  have hsum := ReferenceFirstCollectionCurrentQueueEnergy.sum_thetaMinus
    rate rewards C_star C_h u t z
  rw [Set.indicator_of_mem hz.1] at hsum
  simpa using hsum

private theorem currentMomentOne_sum_bound (u t : Fin p.T) (z : S) :
    (∑ i : Fin p.K,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z) ≤
      (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t).indicator (fun _ : S => (p.m : ℝ)) z := by
  by_cases hz : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t
  · rw [Set.indicator_of_mem hz]
    calc
      _ ≤ ∑ i : Fin p.K,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (currentMomentOne_bound_on_G rate rewards C_star C_h u t i z hz).2
          (ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus_bounds
            rate rewards C_star C_h u t i z).1
      _ = (p.m : ℝ) := by
        simp only [mul_one]
        exact currentTheta_sum_on_G rate rewards C_star C_h u t z hz
  · have hzero (i : Fin p.K) :=
      currentMomentOne_zero_outside_G rate rewards C_star C_h u t i z hz
    simp [hzero, Set.indicator_of_notMem hz]

private theorem oldArmIntegral_eq_moment (control0 : TimeControl p)
    (t : Fin p.T) (i : Fin p.K) :
    (∫ z : S,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z ∂mu) =
    ∫ z : S,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
          rate rewards C_star C_h t i z ∂mu := by
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  calc
    _ = ∫ z : S, mu[(fun z : S =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
          sourcePrefixFiltration control0 (t.val + 1)] z ∂mu :=
      (integral_condExp (f := fun z : S =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) hle).symm
    _ = _ := integral_congr_ae
      (oldWeightedArrival_condExp rate rewards C_star C_h control0 t i)

private theorem currentArmIntegral_eq_moment (control0 : TimeControl p)
    (u t : Fin p.T) (i : Fin p.K) :
    (∫ z : S,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z ∂mu) =
    ∫ z : S,
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z ∂mu := by
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  calc
    _ = ∫ z : S, mu[(fun z : S =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z) |
          sourcePrefixFiltration control0 (t.val + 1)] z ∂mu :=
      (integral_condExp (f := fun z : S =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z) hle).symm
    _ = _ := integral_congr_ae
      (currentWeightedArrival_condExp rate rewards C_star C_h control0 u t i)

/-- The OLD calendar sum is original-source integrable. -/
public theorem oldCalendarWeightedArrival_integrable (control0 : TimeControl p)
    (t : Fin p.T) :
    Integrable (oldCalendarWeightedArrival rate rewards C_star C_h t) mu := by
  unfold oldCalendarWeightedArrival
  exact integrable_finsetSum Finset.univ fun i hi =>
    oldWeightedArrival_integrable_internal rate rewards C_star C_h control0 t i

/-- The integrated OLD sum is charged only to its actual calendar gate. -/
public theorem oldCalendarWeightedArrival_integral_le (control0 : TimeControl p)
    (t : Fin p.T) :
    (∫ z : S, oldCalendarWeightedArrival rate rewards C_star C_h t z ∂mu) ≤
      (p.m : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) := by
  have hfinite : IsFiniteMeasure (sourceInputLaw p) := by
    have hprob := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
    exact ⟨by
      calc
        sourceInputLaw p Set.univ = 1 := hprob.measure_univ
        _ < ⊤ := ENNReal.one_lt_top⟩
  have hconst : Integrable (fun _ : S => (p.m : ℝ)) (sourceInputLaw p) :=
    (integrable_const_iff (μ := sourceInputLaw p)).2 (Or.inr hfinite)
  have hsumInt := oldCalendarWeightedArrival_integrable rate rewards C_star C_h
    control0 t
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t) :=
    hFle _ (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)
  have htermInt : ∀ i : Fin p.K, Integrable (fun z : S =>
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
        rate rewards C_star C_h t i z *
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
        rate rewards C_star C_h t i z) mu := by
    intro i
    have hce := oldWeightedArrival_condExp rate rewards C_star C_h control0 t i
    have hceInt : Integrable (mu[(fun z : S =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z) |
        sourcePrefixFiltration control0 (t.val + 1)]) mu :=
      integrable_condExp (f := fun z : S =>
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z)
    exact hceInt.congr hce
  have hmomentInt := integrable_finsetSum Finset.univ fun i hi => htermInt i
  have hgateInt : Integrable ((ReferenceFirstCollectionOldCalendarExponentialStep.G
      rate rewards C_star C_h t).indicator (fun _ : S => (p.m : ℝ)))
      (sourceInputLaw p) :=
    hconst.indicator hG
  calc
    _ = ∑ i : Fin p.K, ∫ z : S,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator
            (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h t i) z ∂mu := by
      change (∫ z : S, ∑ i : Fin p.K,
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
          rate rewards C_star C_h t i z *
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionOldRecorderFoundation.oldRaw
            rate rewards C_star C_h t i) z ∂mu) = _
      exact integral_finsetSum Finset.univ fun i hi =>
        oldWeightedArrival_integrable_internal rate rewards C_star C_h
          control0 t i
    _ = ∑ i : Fin p.K, ∫ z : S,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      exact oldArmIntegral_eq_moment rate rewards C_star C_h control0 t i
    _ = ∫ z : S, ∑ i : Fin p.K,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.incomingTheta
            rate rewards C_star C_h t i z *
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.momentOne
            rate rewards C_star C_h t i z ∂mu := by
      symm
      exact integral_finsetSum Finset.univ fun i hi => htermInt i
    _ ≤ ∫ z : S,
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator (fun _ : S => (p.m : ℝ)) z ∂mu :=
      integral_mono hmomentInt hgateInt (oldMomentOne_sum_bound rate rewards C_star C_h
        control0 t)
    _ = (p.m : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) := by
      rw [integral_indicator_const (p.m : ℝ) hG, smul_eq_mul]
      ring

/-- The CURRENT sum for one actual invocation tag is integrable on the
original source space. -/
public theorem currentCalendarWeightedArrival_integrable
    (control0 : TimeControl p) (u t : Fin p.T) :
    Integrable (currentCalendarWeightedArrival rate rewards C_star C_h u t) mu := by
  unfold currentCalendarWeightedArrival
  exact integrable_finsetSum Finset.univ fun i hi =>
    currentWeightedArrival_integrable_internal rate rewards C_star C_h
      control0 u t i

/-- The integrated CURRENT sum uses its exact incoming marginal and charges
only its actual retained call gate. -/
public theorem currentCalendarWeightedArrival_integral_le
    (control0 : TimeControl p) (u t : Fin p.T) :
    (∫ z : S, currentCalendarWeightedArrival rate rewards C_star C_h u t z ∂mu) ≤
      (p.m : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t) := by
  have hfinite : IsFiniteMeasure (sourceInputLaw p) := by
    have hprob := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
    exact ⟨by
      calc
        sourceInputLaw p Set.univ = 1 := hprob.measure_univ
        _ < ⊤ := ENNReal.one_lt_top⟩
  have hconst : Integrable (fun _ : S => (p.m : ℝ)) (sourceInputLaw p) :=
    (integrable_const_iff (μ := sourceInputLaw p)).2 (Or.inr hfinite)
  have hFle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet
      (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t) :=
    hFle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have htermInt : ∀ i : Fin p.K, Integrable (fun z : S =>
      ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
        rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
        rate rewards C_star C_h u t i z) mu := by
    intro i
    have hce := currentWeightedArrival_condExp rate rewards C_star C_h
      control0 u t i
    have hceInt : Integrable (mu[(fun z : S =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z) |
        sourcePrefixFiltration control0 (t.val + 1)]) mu :=
      integrable_condExp (f := fun z : S =>
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z)
    exact hceInt.congr hce
  have hmomentInt := integrable_finsetSum Finset.univ fun i hi => htermInt i
  have hgateInt : Integrable ((ReferenceFirstCollectionCurrentRetainedGate.G
      rate rewards C_star C_h u t).indicator (fun _ : S => (p.m : ℝ)))
      (sourceInputLaw p) :=
    hconst.indicator hG
  calc
    _ = ∑ i : Fin p.K, ∫ z : S,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t i z ∂mu := by
      change (∫ z : S, ∑ i : Fin p.K,
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
          rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t i z ∂mu) = _
      exact integral_finsetSum Finset.univ fun i hi =>
        currentWeightedArrival_integrable_internal rate rewards C_star C_h
          control0 u t i
    _ = ∑ i : Fin p.K, ∫ z : S,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      exact currentArmIntegral_eq_moment rate rewards C_star C_h control0 u t i
    _ = ∫ z : S, ∑ i : Fin p.K,
          ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t i z *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedMomentOne
            rate rewards C_star C_h u t i z ∂mu := by
      symm
      exact integral_finsetSum Finset.univ fun i hi => htermInt i
    _ ≤ ∫ z : S,
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t).indicator (fun _ : S => (p.m : ℝ)) z ∂mu :=
      integral_mono hmomentInt hgateInt
        (currentMomentOne_sum_bound rate rewards C_star C_h u t)
    _ = (p.m : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t) := by
      rw [integral_indicator_const (p.m : ℝ) hG, smul_eq_mul]
      ring

private theorem liveCalendarWeightedArrival_integrable
    (control0 : TimeControl p) (t : Fin p.T) :
    Integrable (liveCalendarWeightedArrival rate rewards C_star C_h t) mu :=
  ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarWeightedArrival_moments
    rate rewards C_star C_h t control0 |>.1

private theorem liveCalendarWeightedArrival_integral_le_sourceCellMass
    (control0 : TimeControl p) (t : Fin p.T) :
    (∫ z : S, liveCalendarWeightedArrival rate rewards C_star C_h t z ∂mu) ≤
      (p.m : ℝ) *
        ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h t control0 := by
  have hmom := ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarWeightedArrival_moments rate rewards C_star C_h t control0
  have hsubset :
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
          rate rewards C_star C_h t ⊆
        ((ReferenceFirstLiveSourcePhasePartition.sourcePhase
            rate rewards C_star C_h t 2 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase
            rate rewards C_star C_h t 3) ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase
            rate rewards C_star C_h t 4) := by
    rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
      rate rewards C_star C_h t control0]
    intro z hz
    rcases hz.1 with h2 | h34
    · exact Or.inl (Or.inl h2)
    · rcases h34 with h3 | h4
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h4
  have hmass : (sourceInputLaw p).real
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t) ≤
      ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h t control0 := by
    rw [ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass_eq_sourcePhase234
      rate rewards C_star C_h t control0]
    exact MeasureTheory.measureReal_mono hsubset
  calc
    _ ≤ (p.m : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
          rate rewards C_star C_h t) := hmom.2
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg p.m)

/-- The complete original-source date expression is integrable. -/
public theorem calendarWeightedArrival_integrable (control0 : TimeControl p)
    (t : Fin p.T) :
    Integrable (calendarWeightedArrival rate rewards C_star C_h t) mu := by
  unfold calendarWeightedArrival
  exact (liveCalendarWeightedArrival_integrable rate rewards C_star C_h
      control0 t).add
    ((oldCalendarWeightedArrival_integrable rate rewards C_star C_h control0 t).add
      (integrable_finsetSum Finset.univ fun u hu =>
        currentCalendarWeightedArrival_integrable rate rewards C_star C_h
          control0 u t))

/-- The useful intermediate date budget, before combining the disjoint
source-cell, OLD, and CURRENT event masses. -/
public theorem calendarWeightedArrival_integral_le_sourceBudget
    (control0 : TimeControl p) (t : Fin p.T) :
    (∫ z : S, calendarWeightedArrival rate rewards C_star C_h t z ∂mu) ≤
      (p.m : ℝ) *
        (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
          (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u t)) := by
  have hLiveI := liveCalendarWeightedArrival_integrable rate rewards C_star C_h
    control0 t
  have hOldI := oldCalendarWeightedArrival_integrable rate rewards C_star C_h
    control0 t
  have hCurrentI := integrable_finsetSum Finset.univ fun u hu =>
    currentCalendarWeightedArrival_integrable rate rewards C_star C_h control0 u t
  have hCurrentLe :
      (∫ z : S, (∑ u : Fin p.T,
        currentCalendarWeightedArrival rate rewards C_star C_h u t z) ∂mu) ≤
        (p.m : ℝ) * ∑ u : Fin p.T, (sourceInputLaw p).real
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t) := by
    rw [integral_finsetSum Finset.univ (fun u hu =>
      currentCalendarWeightedArrival_integrable rate rewards C_star C_h control0 u t)]
    calc
      _ ≤ ∑ u : Fin p.T, (p.m : ℝ) * (sourceInputLaw p).real
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t) := by
        apply Finset.sum_le_sum
        intro u hu
        exact currentCalendarWeightedArrival_integral_le rate rewards C_star C_h
          control0 u t
      _ = _ := by rw [← Finset.mul_sum]
  calc
    _ = (∫ z : S, liveCalendarWeightedArrival rate rewards C_star C_h t z ∂mu) +
        (∫ z : S, oldCalendarWeightedArrival rate rewards C_star C_h t z ∂mu) +
        ∫ z : S, (∑ u : Fin p.T,
          currentCalendarWeightedArrival rate rewards C_star C_h u t z) ∂mu := by
      change (∫ z : S, liveCalendarWeightedArrival rate rewards C_star C_h t z +
          (oldCalendarWeightedArrival rate rewards C_star C_h t z +
            ∑ u : Fin p.T, currentCalendarWeightedArrival rate rewards C_star C_h u t z) ∂mu) = _
      calc
        _ = (∫ z : S, liveCalendarWeightedArrival rate rewards C_star C_h t z ∂mu) +
            ∫ z : S, (oldCalendarWeightedArrival rate rewards C_star C_h t z +
              ∑ u : Fin p.T, currentCalendarWeightedArrival rate rewards C_star C_h u t z) ∂mu :=
          integral_add hLiveI (hOldI.add hCurrentI)
        _ = _ := by
          rw [integral_add hOldI hCurrentI]
          ring
    _ ≤ (p.m : ℝ) *
          ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
        (p.m : ℝ) * (sourceInputLaw p).real
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
        (p.m : ℝ) * ∑ u : Fin p.T, (sourceInputLaw p).real
          (ReferenceFirstCollectionCurrentRetainedGate.G
            rate rewards C_star C_h u t) := by
      exact add_le_add (add_le_add
        (liveCalendarWeightedArrival_integral_le_sourceCellMass
          rate rewards C_star C_h control0 t)
        (oldCalendarWeightedArrival_integral_le rate rewards C_star C_h control0 t))
        hCurrentLe
    _ = _ := by ring

/-- The actual unnormalized first-invocation phase masses share one
probability budget, so each date costs at most `m`. -/
public theorem calendarWeightedArrival_integral_le (control0 : TimeControl p)
    (t : Fin p.T) :
    (∫ z : S, calendarWeightedArrival rate rewards C_star C_h t z ∂mu) ≤
      (p.m : ℝ) := by
  calc
    _ ≤ (p.m : ℝ) *
        (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h t control0 +
          (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G
              rate rewards C_star C_h u t)) :=
      calendarWeightedArrival_integral_le_sourceBudget rate rewards C_star C_h
        control0 t
    _ ≤ (p.m : ℝ) := by
      have hbudget :=
        ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass_oldG_currentRetainedGate_le_one
            rate rewards C_star C_h t control0
      calc
        _ ≤ (p.m : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg p.m)
        _ = (p.m : ℝ) := by ring

/-- The complete first-invocation calendar sum is integrable on the
original source law. -/
public theorem firstInvocationCalendarWeightedArrival_integrable
    (control0 : TimeControl p) :
    Integrable (firstInvocationCalendarWeightedArrival rate rewards C_star C_h) mu := by
  unfold firstInvocationCalendarWeightedArrival
  exact integrable_finsetSum Finset.univ fun t ht =>
    calendarWeightedArrival_integrable rate rewards C_star C_h control0 t

/-- The sharp shared datewise first-moment budget sums to `m*T` on the same
original source law. -/
public theorem firstInvocationCalendarWeightedArrival_integral_le
    (control0 : TimeControl p) :
    (∫ z : S,
      firstInvocationCalendarWeightedArrival rate rewards C_star C_h z ∂mu) ≤
      (p.m : ℝ) * (p.T : ℝ) := by
  have hsumI := firstInvocationCalendarWeightedArrival_integrable
    rate rewards C_star C_h control0
  calc
    _ = ∑ t : Fin p.T,
        ∫ z : S, calendarWeightedArrival rate rewards C_star C_h t z ∂mu := by
      change (∫ z : S, ∑ t : Fin p.T,
        calendarWeightedArrival rate rewards C_star C_h t z ∂mu) = _
      exact integral_finsetSum Finset.univ (fun t ht =>
        calendarWeightedArrival_integrable rate rewards C_star C_h control0 t)
    _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact calendarWeightedArrival_integral_le rate rewards C_star C_h control0 t
    _ = (p.m : ℝ) * (p.T : ℝ) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

end Bandits.Support.ReferenceFirstCollectionOriginalWeightedArrivalBudget

end
