/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original-source later-birth weighted-square drift

The potential and backlog below read the complete actual numerical prefix.
Birth success remains an event of the current assignment vector, and its
conditional mass is retained in the drift bound.

Source: ZIP4 `04_slow_fast_learner.tex:245-320,393-450` and
`06_interruptions.tex:355-426`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarLaterBirthWeightedDrift

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open RecordedQueueRun (RoundInput RunState run scoreWeight)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs)
open ReferenceFirstCollectionCurrentQueueReadout (QueueReadout)
open ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep
  (preSamplerSet sourceLaterMarker laterBirthPresenceMass)
open ReferenceFirstCollectionCurrentRawMoments (currentRaw)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The literal option-elimination of the original numerical prefix into its
current-score weighted-square potential. -/
def originalPrefixWeightedSquarePotential (n : ℕ) (z : SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h n z with
  | none => 0
  | some past => RecordedWeightedDrift.weightedSquarePotential p.m
      (queueParameters rate) (run (queueParameters rate) past)

/-- The source weighted backlog, using the same full current prefix as the
weighted-square potential. -/
def originalPrefixWeightedBacklog (n : ℕ) (z : SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h n z with
  | none => 0
  | some past => RecordedWeightedDrift.weightedBacklog p.m
      (queueParameters rate) (run (queueParameters rate) past)

/-- Current inclusion probabilities from the actual numerical prefix. -/
def originalPrefixTheta (n : ℕ) (z : SourceInput p) (a : Fin p.K) : ℝ :=
  match prefixInputs rate rewards C_star C_h n z with
  | none => 0
  | some past => ProductSetLaw.theta p.m
      (scoreWeight (queueParameters rate) (run (queueParameters rate) past)) a

/-- One coordinate of the normalized backlog observed in the original prefix. -/
def originalPrefixCoordinateBacklog (n : ℕ) (z : SourceInput p) (a : Fin p.K) : ℝ :=
  match prefixInputs rate rewards C_star C_h n z with
  | none => 0
  | some past => StoppedQueueBound.normalizedBacklog (queueParameters rate)
      (run (queueParameters rate) past) a

/-- The actual anchor-rate reciprocal sum. The absent calendar-parameter
branch has value zero and is masked from every retained-birth assertion. -/
def originalPrefixInverseRateSum (q : Fin p.T) (z : SourceInput p) : ℝ :=
  match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h q z with
  | none => 0
  | some theta =>
      match prefixInputs rate rewards C_star C_h q.val z with
      | none => 0
      | some past => ∑ a : Fin p.K,
          ProductSetLaw.theta p.m
            (scoreWeight (queueParameters rate) (run (queueParameters rate) past)) a /
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a

/-- The actual later-birth event retained by the incoming overflow gate. -/
def actualRetainedLaterBirthEvent (q : Fin p.T) : Set (SourceInput p) :=
  preSamplerSet rate rewards C_star C_h q ∩
    ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q ∩
    {z | (sourceLaterMarker rate rewards C_star C_h q z).isSome = true}

/-- Actual weighted-square increment across the same original prefix update. -/
def originalPrefixWeightedSquareDelta (q : Fin p.T) (z : SourceInput p) : ℝ :=
  originalPrefixWeightedSquarePotential rate rewards C_star C_h (q.val + 1) z -
    originalPrefixWeightedSquarePotential rate rewards C_star C_h q.val z

/-- Expected-cost integrand: the actual successful retained event multiplies
the current full-prefix weighted backlog. -/
def actualRetainedLaterBirthCost (q : Fin p.T) (z : SourceInput p) : ℝ :=
  (actualRetainedLaterBirthEvent rate rewards C_star C_h q).indicator
    (originalPrefixWeightedBacklog rate rewards C_star C_h q.val) z

/-- Retained weighted raw arrivals on the actual original-source birth. -/
def actualRetainedLaterBirthWeightedArrival (q : Fin p.T) (z : SourceInput p) : ℝ :=
  (actualRetainedLaterBirthEvent rate rewards C_star C_h q).indicator
    (fun z => ∑ a : Fin p.K,
      originalPrefixTheta rate rewards C_star C_h q.val z a *
        currentRaw rate rewards C_star C_h q a z) z

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private instance readoutSumMeasurableSingleton {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance readoutOptionMeasurableSingleton {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (Option A) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit A x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit A).injective.eq_iff]

private instance readoutRecordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hm := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private def readoutWeight (o : QueueReadout p.K) : Fin p.K → ℝ :=
  fun a => ScoreWeights.scoreWeight (1 + 1 / (ConstructorDimensions.D p : ℝ))
    (o.1 a).1

private def readoutWeightedSquarePotential (rate : RateInput p)
    (o : Option (QueueReadout p.K)) : ℝ :=
  match o with
  | none => 0
  | some r => ∑ a : Fin p.K,
      ProductSetLaw.theta p.m (readoutWeight r) a *
        (((r.1 a).2 : ℝ) / ((queueParameters rate).n : ℝ)) ^ 2

private def readoutWeightedBacklog (rate : RateInput p)
    (o : Option (QueueReadout p.K)) : ℝ :=
  match o with
  | none => 0
  | some r => ∑ a : Fin p.K,
      ProductSetLaw.theta p.m (readoutWeight r) a *
        (((r.1 a).2 : ℝ) / ((queueParameters rate).n : ℝ))

private def readoutCoordinateTheta (o : Option (QueueReadout p.K)) (a : Fin p.K) : ℝ :=
  match o with
  | none => 0
  | some r => ProductSetLaw.theta p.m (readoutWeight r) a

private def readoutCoordinateBacklog (rate : RateInput p)
    (o : Option (QueueReadout p.K)) (a : Fin p.K) : ℝ :=
  match o with
  | none => 0
  | some r => ((r.1 a).2 : ℝ) / ((queueParameters rate).n : ℝ)

private theorem prefixPotential_eq_readout (n : ℕ) (z : SourceInput p) :
    originalPrefixWeightedSquarePotential rate rewards C_star C_h n z =
      readoutWeightedSquarePotential rate
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z) := by
  classical
  cases h : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixWeightedSquarePotential,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h,
      readoutWeightedSquarePotential]
  | some past =>
      let state := RecordedQueueRun.run (queueParameters rate) past
      have hw : readoutWeight (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          state) = RecordedQueueRun.scoreWeight (queueParameters rate) state := by
        funext a
        simp [readoutWeight, RecordedQueueRun.scoreWeight,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
          ScoreWeights.scoreWeight, queueParameters]
      have heq : readoutWeightedSquarePotential rate
          (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state)) =
          RecordedWeightedDrift.weightedSquarePotential p.m (queueParameters rate) state := by
        rw [readoutWeightedSquarePotential, RecordedWeightedDrift.weightedSquarePotential]
        rw [← hw]
        simp [StoppedQueueBound.normalizedBacklog,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
      simpa [originalPrefixWeightedSquarePotential,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h, state] using heq.symm

private theorem prefixBacklog_eq_readout (n : ℕ) (z : SourceInput p) :
    originalPrefixWeightedBacklog rate rewards C_star C_h n z =
      readoutWeightedBacklog rate
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z) := by
  classical
  cases h : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixWeightedBacklog,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h,
      readoutWeightedBacklog]
  | some past =>
      let state := RecordedQueueRun.run (queueParameters rate) past
      have hw : readoutWeight (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          state) = RecordedQueueRun.scoreWeight (queueParameters rate) state := by
        funext a
        simp [readoutWeight, RecordedQueueRun.scoreWeight,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
          ScoreWeights.scoreWeight, queueParameters]
      have heq : readoutWeightedBacklog rate
          (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state)) =
          RecordedWeightedDrift.weightedBacklog p.m (queueParameters rate) state := by
        rw [readoutWeightedBacklog, RecordedWeightedDrift.weightedBacklog]
        rw [← hw]
        simp [StoppedQueueBound.normalizedBacklog,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
      simpa [originalPrefixWeightedBacklog,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h, state] using heq.symm

private theorem prefixTheta_eq_readout (n : ℕ) (z : SourceInput p) (a : Fin p.K) :
    originalPrefixTheta rate rewards C_star C_h n z a =
      readoutCoordinateTheta
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z) a := by
  classical
  cases h : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixTheta,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h,
      readoutCoordinateTheta]
  | some past =>
      let state := RecordedQueueRun.run (queueParameters rate) past
      have hw : readoutWeight (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          state) = RecordedQueueRun.scoreWeight (queueParameters rate) state := by
        funext j
        simp [readoutWeight, RecordedQueueRun.scoreWeight,
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
          ScoreWeights.scoreWeight, queueParameters]
      simp only [originalPrefixTheta, h,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        Option.map_some, readoutCoordinateTheta]
      change ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight
          (queueParameters rate) state) a =
        ProductSetLaw.theta p.m (readoutWeight
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state)) a
      exact congrArg (fun w => ProductSetLaw.theta p.m w a) hw.symm

private theorem prefixCoordinateBacklog_eq_readout (n : ℕ) (z : SourceInput p)
    (a : Fin p.K) :
    originalPrefixCoordinateBacklog rate rewards C_star C_h n z a =
      readoutCoordinateBacklog rate
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z) a := by
  classical
  cases h : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixCoordinateBacklog,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, h,
      readoutCoordinateBacklog]
  | some past =>
      let state := RecordedQueueRun.run (queueParameters rate) past
      simp only [originalPrefixCoordinateBacklog, h,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        Option.map_some, readoutCoordinateBacklog]
      change StoppedQueueBound.normalizedBacklog (queueParameters rate) state a =
        (((ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state).1 a).2 : ℝ) /
          ((queueParameters rate).n : ℝ)
      simp [StoppedQueueBound.normalizedBacklog,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]

private theorem readoutWeightedSquarePotential_measurable :
    Measurable (readoutWeightedSquarePotential rate) := measurable_of_countable _

private theorem readoutWeightedBacklog_measurable :
    Measurable (readoutWeightedBacklog rate) := measurable_of_countable _

private theorem readoutCoordinateTheta_measurable (a : Fin p.K) :
    Measurable (fun o => readoutCoordinateTheta o a) := measurable_of_countable _

private theorem readoutCoordinateBacklog_measurable (a : Fin p.K) :
    Measurable (fun o => readoutCoordinateBacklog rate o a) := measurable_of_countable _

private theorem originalPotential_measurable (control0 : TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (originalPrefixWeightedSquarePotential rate rewards C_star C_h q.val) := by
  rw [funext (prefixPotential_eq_readout rate rewards C_star C_h q.val)]
  exact (readoutWeightedSquarePotential_measurable rate).comp
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)

private theorem originalBacklog_measurable (control0 : TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (originalPrefixWeightedBacklog rate rewards C_star C_h q.val) := by
  rw [funext (prefixBacklog_eq_readout rate rewards C_star C_h q.val)]
  exact (readoutWeightedBacklog_measurable rate).comp
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)

private theorem successfulMarker_measurable (q : Fin p.T) :
    Measurable (fun z : SourceInput p =>
      ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator
        (sourceLaterMarker rate rewards C_star C_h q z).isSome) := by
  classical
  let S : Set (SourceInput p) :=
    {z | (sourceLaterMarker rate rewards C_star C_h q z).isSome = true}
  have hS : MeasurableSet S := by
    change MeasurableSet
      ((sourceLaterMarker rate rewards C_star C_h q) ⁻¹'
        {o : Option (Option (Fin p.K)) | o.isSome = true})
    exact (Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
      rate rewards C_star C_h q) (by
        simp)
  have heq : (fun z : SourceInput p =>
      ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator
        (sourceLaterMarker rate rewards C_star C_h q z).isSome) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext z
    cases hmark : sourceLaterMarker rate rewards C_star C_h q z <;>
      simp [S, hmark,
        ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator]
  rw [heq]
  exact measurable_const.indicator hS

/-- Conditional mass of the actual retained later-birth event. The incoming
pre-sampler and prior-clear gates remain visible, while success is integrated
as its actual whole-vector presence mass. -/
theorem actualRetainedLaterBirthEvent_condExp (control0 : TimeControl p)
    (q : Fin p.T) :
    (sourceInputLaw p)[(actualRetainedLaterBirthEvent rate rewards C_star C_h q).indicator
      (fun _ => (1 : ℝ)) | sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[sourceInputLaw p]
    (preSamplerSet rate rewards C_star C_h q ∩
      ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q).indicator
      (laterBirthPresenceMass rate rewards C_star C_h control0 q) := by
  classical
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0 (q.val + 1)
  let E := preSamplerSet rate rewards C_star C_h q
  let H := ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q
  let EH := E ∩ H
  let success := fun z : SourceInput p =>
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator
      (sourceLaterMarker rate rewards C_star C_h q z).isSome
  let f := E.indicator success
  have hE : MeasurableSet[F] E := by
    simpa only [F, E] using
      Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
        rate rewards C_star C_h control0 q
  have hH : MeasurableSet[F] H :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 q
  have hEH : MeasurableSet[F] EH := hE.inter hH
  have hEGlobal : @MeasurableSet (SourceInput p) (sourceInputMeasurableSpace p) E := by
    rcases hE with ⟨s, hs, hset⟩
    rw [← hset]
    exact (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
      control0 q.val) hs
  have hf : @Measurable (SourceInput p) ℝ (sourceInputMeasurableSpace p)
      Real.measurableSpace f :=
    (successfulMarker_measurable rate rewards C_star C_h q).indicator hEGlobal
  have hfBound : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ E
    · simp only [f, Set.indicator_of_mem hz]
      dsimp [success, Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator]
      cases (sourceLaterMarker rate rewards C_star C_h q z) <;> norm_num
    · simp only [f, Set.indicator_of_notMem hz]
      norm_num
  have hfInt : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hfBound)
  have hfun : (actualRetainedLaterBirthEvent rate rewards C_star C_h q).indicator
        (fun _ => (1 : ℝ)) = EH.indicator f := by
    funext z
    by_cases hz : z ∈ EH
    · rcases hz with ⟨hzE, hzH⟩
      by_cases hs : (sourceLaterMarker rate rewards C_star C_h q z).isSome = true
      · simp [actualRetainedLaterBirthEvent, E, H, EH, f, success, hzE, hzH, hs,
          ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator]
      · have hs' : (sourceLaterMarker rate rewards C_star C_h q z).isSome = false :=
          Bool.eq_false_iff.mpr hs
        simp [actualRetainedLaterBirthEvent, E, H, EH, f, success, hzE, hzH, hs',
          ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.presentIndicator]
    · simp [actualRetainedLaterBirthEvent, E, H, EH, f, success, hz]
  have hce := condExp_indicator (μ := μ) hfInt hEH
  have hpresence : μ[f | F] =ᵐ[μ]
      E.indicator (laterBirthPresenceMass rate rewards C_star C_h control0 q) := by
    simpa [f, E, success] using
      (Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthPresence_condExp
        rate rewards C_star C_h control0 q)
  rw [hfun]
  filter_upwards [hce, hpresence] with z hzCE hzPresence
  rw [hzCE]
  change EH.indicator (μ[f | F]) z =
    EH.indicator (laterBirthPresenceMass rate rewards C_star C_h control0 q) z
  by_cases hz : z ∈ EH
  · rcases hz with ⟨hzE, hzH⟩
    rw [Set.indicator_of_mem (show z ∈ EH from ⟨hzE, hzH⟩),
      Set.indicator_of_mem (show z ∈ EH from ⟨hzE, hzH⟩)]
    rw [hzPresence, Set.indicator_of_mem hzE]
  · simp [Set.indicator_of_notMem hz]

/-- Pathwise square drift on the actual retained successful later-birth event,
using the same original source prefix and its full current score vector. -/
theorem originalLaterBirth_weightedSquare_pointwise (q : Fin p.T)
    (z : SourceInput p) (hz : z ∈ actualRetainedLaterBirthEvent rate rewards C_star C_h q) :
    originalPrefixWeightedSquareDelta rate rewards C_star C_h q z ≤
      ∑ a : Fin p.K, originalPrefixTheta rate rewards C_star C_h q.val z a *
        ((2 * originalPrefixCoordinateBacklog rate rewards C_star C_h q.val z a + 1 / 2) *
            currentRaw rate rewards C_star C_h q a z +
          (currentRaw rate rewards C_star C_h q a z) ^ 2 +
          (-(15 / 2 : ℝ) * originalPrefixCoordinateBacklog
            rate rewards C_star C_h q.val z a + 16)) := by
  classical
  rcases hz with ⟨hzEH, hzS⟩
  rcases hzEH with ⟨hzE, hzH⟩
  obtain ⟨past, cell, hpre, hpost, hcell, henabled, hretained, hstep⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_prefix_energy_step
      rate rewards C_star C_h q z hzE hzS
  let Q := queueParameters rate
  let state := RecordedQueueRun.run Q past
  have hnot : state.overflow = false := hretained.mp hzH
  have hrun : RecordedQueueRun.run Q (past ++ [cell]) =
      RecordedQueueRun.step Q state cell := by
    rw [RecordedQueueRun.run, CanonicalQueueProcess.execute_append]
    rfl
  have hratePast : ∀ round ∈ past, ∀ a, 32 * Q.eta ≤ round.rate a :=
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
      rate rewards C_star C_h q.val z past hpre
  have hrateNext : ∀ a, 32 * Q.eta ≤ cell.rate a := by
    intro a
    have hbound := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixInputs_rate_bounds
      rate rewards C_star C_h (q.val + 1) z (past ++ [cell]) hpost cell (by simp) a
    simpa only [Q, queueParameters] using hbound
  have heta : Q.eta ≤ 1 / 64 := by
    apply RecordedWeightedDrift.eta_le_one_div_sixtyFour p Q
    simpa only [Q, queueParameters] using rate.sourceCap
  have hpotential : originalPrefixWeightedSquareDelta rate rewards C_star C_h q z =
      RecordedWeightedDrift.weightedSquarePotential p.m Q
        (RecordedQueueRun.step Q state cell) -
      RecordedWeightedDrift.weightedSquarePotential p.m Q state := by
    simp [originalPrefixWeightedSquareDelta, originalPrefixWeightedSquarePotential,
      hpre, hpost, hrun, Q, state]
  rw [hpotential]
  rw [RecordedWeightedDrift.weightedSquarePotential,
    RecordedWeightedDrift.weightedSquarePotential, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  let b := StoppedQueueBound.normalizedBacklog Q state a
  let r := currentRaw rate rewards C_star C_h q a z
  let bNext := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.step Q state cell) a
  let theta := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q state) a
  let thetaNext := ProductSetLaw.theta p.m
    (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell)) a
  have hback := hstep a hzH
  have hrec : bNext = QueueSquareDrift.queueNext b r := by
    dsimp only [b, r, bNext, Q] at *
    rw [← hrun]
    simpa only [QueueSquareDrift.queueNext, max_comm] using hback.1
  have hrawNonneg : 0 ≤ r := by
    obtain ⟨physicalRecord, physicalCell, _hr, _ht, _hrows, _hj, _hrewards,
      _hstrict, hphysicalCell, _hmarker, _hphysicalMarker, _howners, hquantized,
      _hunoccupied, _hsaved⟩ :=
      ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_physical
        rate rewards C_star C_h q z hzE hzS
    have hphysicalRaw : r =
        (RecordedQueueRun.quantizedArrival Q physicalCell.input a : ℝ) / (Q.n : ℝ) := by
      simp only [r, currentRaw, hphysicalCell, RecordedRoundMoments.normalizedQuantizedArrival, Q]
    rw [hphysicalRaw, hquantized a]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hb : 0 ≤ b := by
    dsimp only [b, Q, state, RecordedQueueRun.run, StoppedQueueBound.normalizedBacklog]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htheta : 0 ≤ theta := by
    dsimp only [theta]
    exact (RecordedMarginalGrowth.state_theta_pos Q state a
      (ConstructorDimensions.m_pos p) p.m_lt_K).le
  have hcap := RecordedWeightedDrift.successor_normalizedBacklog_le Q past hratePast
    cell hrateNext a
  have hsq := QueueSquareDrift.queueNext_sq_sub_le b r hb hrawNonneg
  have hcapQueue : QueueSquareDrift.queueNext b r ≤ 2 * (1 / (32 * Q.eta)) := by
    calc
      _ = bNext := hrec.symm
      _ ≤ 2 * (1 / (32 * Q.eta)) := by simpa only [bNext] using hcap
  have hcapSquare := QueueSquareDrift.queueNext_sq_le_cap_mul b r
    (1 / (32 * Q.eta)) hb hrawNonneg (by positivity [Q.eta_pos]) hcapQueue
  have hscaled0 := mul_le_mul_of_nonneg_left hcapSquare
    (show 0 ≤ 8 * Q.eta by positivity [Q.eta_pos])
  have hcoef := RecordedWeightedDrift.sixteen_eta_mul_backlogCap Q
  have hscaled : 8 * Q.eta * bNext ^ 2 ≤ (1 / 2 : ℝ) * (b + r) := by
    calc
      8 * Q.eta * bNext ^ 2 ≤
          8 * Q.eta * (2 * (1 / (32 * Q.eta)) * (b + r)) := by
        simpa only [hrec] using hscaled0
      _ = (1 / 2 : ℝ) * (b + r) := by
        calc
          _ = (16 * Q.eta * (1 / (32 * Q.eta))) * (b + r) := by ring
          _ = _ := by rw [hcoef]
  have hsq' : bNext ^ 2 - b ^ 2 ≤ 2 * b * (r - 4) + r ^ 2 + 16 := by
    rw [hrec]
    exact hsq
  have hinner : bNext ^ 2 - b ^ 2 + 8 * Q.eta * bNext ^ 2 ≤
      (2 * b + 1 / 2) * r + r ^ 2 + (-(15 / 2 : ℝ) * b + 16) := by
    nlinarith only [hsq', hscaled]
  have hgrowth := RecordedMarginalGrowth.step_theta_growth Q state cell a
    p.two_le_m p.m_lt_K heta
  have hcoord := (QueueSquareDrift.weighted_square_step thetaNext theta Q.eta bNext b
      htheta Q.eta_pos.le (hgrowth.1.trans hgrowth.2)).trans
    (mul_le_mul_of_nonneg_left hinner htheta)
  have hthetaEq : originalPrefixTheta rate rewards C_star C_h q.val z a = theta := by
    simp [originalPrefixTheta, hpre, theta, state, Q]
  have hbEq : originalPrefixCoordinateBacklog rate rewards C_star C_h q.val z a = b := by
    simp [originalPrefixCoordinateBacklog, hpre, b, state, Q]
  rw [hthetaEq, hbEq]
  simpa only [theta, thetaNext, bNext, b, r, Q, state,
    StoppedQueueBound.normalizedBacklog] using hcoord

variable (control0 : TimeControl p) (q : Fin p.T)

local notation "X" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (q.val + 1)
local notation "E" => preSamplerSet rate rewards C_star C_h q
local notation "H" => ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q
local notation "A" => actualRetainedLaterBirthEvent rate rewards C_star C_h q
local notation "α" => laterBirthPresenceMass rate rewards C_star C_h control0 q
local notation "θ" => originalPrefixTheta rate rewards C_star C_h q.val
local notation "b" => originalPrefixCoordinateBacklog rate rewards C_star C_h q.val
local notation "raw" => currentRaw rate rewards C_star C_h q
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "cap" => (2 * (1 / (32 * rate.eta.val)))

private theorem theta_measurable (a : Fin p.K) :
    Measurable[F] (fun z => θ z a) := by
  rw [funext (fun z => prefixTheta_eq_readout rate rewards C_star C_h q.val z a)]
  exact (readoutCoordinateTheta_measurable a).comp
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)

private theorem backlog_measurable (a : Fin p.K) :
    Measurable[F] (fun z => b z a) := by
  rw [funext (fun z => prefixCoordinateBacklog_eq_readout rate rewards C_star C_h q.val z a)]
  exact (readoutCoordinateBacklog_measurable rate a).comp
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
      rate rewards C_star C_h control0 q)

private theorem theta_bounds (n : ℕ) (z : X) (a : Fin p.K) :
    0 ≤ originalPrefixTheta rate rewards C_star C_h n z a ∧
      originalPrefixTheta rate rewards C_star C_h n z a ≤ 1 := by
  cases hp : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixTheta, hp]
  | some past =>
    simp only [originalPrefixTheta, hp]
    exact ⟨(RecordedMarginalGrowth.state_theta_pos _ _ a
      (ConstructorDimensions.m_pos p) p.m_lt_K).le,
      (ProductSetLaw.theta_lt_one _ a (ConstructorDimensions.m_pos p) p.m_lt_K
        (RecordedMarginalGrowth.state_scoreWeight_pos _ _)).le⟩

private theorem backlog_bounds (n : ℕ) (z : X) (a : Fin p.K) :
    0 ≤ originalPrefixCoordinateBacklog rate rewards C_star C_h n z a ∧
      originalPrefixCoordinateBacklog rate rewards C_star C_h n z a ≤ cap := by
  rw [prefixCoordinateBacklog_eq_readout]
  cases hp : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h n z with
  | none => simp [readoutCoordinateBacklog, le_of_lt rate.eta.property]
  | some o =>
    exact ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
      rate rewards C_star C_h n z o hp a

private theorem potential_integrable (n : ℕ) :
    Integrable (originalPrefixWeightedSquarePotential rate rewards C_star C_h n) μ := by
  classical
  have hm : Measurable (originalPrefixWeightedSquarePotential rate rewards C_star C_h n) := by
    rw [funext (prefixPotential_eq_readout rate rewards C_star C_h n)]
    let : MeasurableSpace (Option (QueueReadout p.K)) :=
      ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
    exact (measurable_of_countable (readoutWeightedSquarePotential rate)).comp
      (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
        rate rewards C_star C_h n)
  apply (integrable_const ((p.K : ℝ) * cap ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  have heq : originalPrefixWeightedSquarePotential rate rewards C_star C_h n z =
      ∑ a : Fin p.K, originalPrefixTheta rate rewards C_star C_h n z a *
        (originalPrefixCoordinateBacklog rate rewards C_star C_h n z a) ^ 2 := by
    cases hp : prefixInputs rate rewards C_star C_h n z <;>
      simp [originalPrefixWeightedSquarePotential, originalPrefixTheta,
        originalPrefixCoordinateBacklog, RecordedWeightedDrift.weightedSquarePotential, hp]
  rw [heq, Real.norm_of_nonneg (Finset.sum_nonneg (fun a _ =>
    mul_nonneg (theta_bounds rate rewards C_star C_h n z a).1 (sq_nonneg _)))]
  calc
    _ ≤ ∑ _a : Fin p.K, cap ^ 2 := Finset.sum_le_sum (fun a _ => by
      have ht := theta_bounds rate rewards C_star C_h n z a
      have hb := backlog_bounds rate rewards C_star C_h n z a
      exact (mul_le_mul_of_nonneg_right ht.2 (sq_nonneg _)).trans
        (by simpa only [one_mul] using pow_le_pow_left₀ hb.1 hb.2 2))
    _ = _ := by simp

include control0 in
private theorem event_measurable :
    MeasurableSet A := by
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hs : MeasurableSet {z : X |
      (sourceLaterMarker rate rewards C_star C_h q z).isSome = true} := by
    change MeasurableSet ((sourceLaterMarker rate rewards C_star C_h q) ⁻¹'
      {o : Option (Option (Fin p.K)) | o.isSome = true})
    exact (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
      rate rewards C_star C_h q) (by simp)
  exact ((hle _ (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
      rate rewards C_star C_h control0 q)).inter
    (hle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 q))).inter hs

private theorem raw_on_E_bounds (a : Fin p.K) (z : X) (hz : z ∈ E) :
    0 ≤ raw a z ∧ raw a z ≤ 1 / β := by
  rw [ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthRaw_factor
    rate rewards C_star C_h q a z hz]
  have ha := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.currentAmplitude_bounds
    rate rewards C_star C_h q a z
  split_ifs <;> simp_all [le_of_lt (CanonicalRecordingRates.beta_pos p rate.eta.property)]

include control0 in
private theorem maskedRaw_integrable
    (a : Fin p.K) (k : ℕ) : Integrable ((E).indicator (fun z => raw a z ^ k)) μ := by
  have hE := (sourcePrefixFiltration control0).le' (q.val + 1) _
    (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
      rate rewards C_star C_h control0 q)
  apply (integrable_const ((1 / β) ^ k)).mono'
    (((ReferenceFirstCollectionCurrentRawMoments.currentRaw_measurable
      rate rewards C_star C_h q a).pow_const k).indicator hE).aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z ∈ E
  · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (pow_nonneg (raw_on_E_bounds
      rate rewards C_star C_h q a z hz).1 k)]
    exact pow_le_pow_left₀ (raw_on_E_bounds rate rewards C_star C_h q a z hz).1
      (raw_on_E_bounds rate rewards C_star C_h q a z hz).2 k
  · rw [Set.indicator_of_notMem hz, norm_zero]
    positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]

private theorem success_raw (a : Fin p.K) (k : ℕ) (hk : 0 < k) :
    (A).indicator (fun z => raw a z ^ k) = (E ∩ H).indicator (fun z => raw a z ^ k) := by
  classical
  funext z
  by_cases he : z ∈ E ∩ H
  · rw [Set.indicator_of_mem he]
    by_cases hs : (sourceLaterMarker rate rewards C_star C_h q z).isSome = true
    · rw [Set.indicator_of_mem (show z ∈ A from ⟨he, hs⟩)]
    · have hm : sourceLaterMarker rate rewards C_star C_h q z = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp (Bool.eq_false_iff.mpr hs))
      rw [Set.indicator_of_notMem (show z ∉ A from fun h => hs h.2),
        ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthRaw_factor
          rate rewards C_star C_h q a z he.1]
      simp [hm, zero_pow (Nat.ne_of_gt hk)]
  · rw [Set.indicator_of_notMem he,
      Set.indicator_of_notMem (show z ∉ A from fun h => he h.1)]

private theorem bounded_predictable_product (f g : X → ℝ) (c : ℝ)
    (hf : Measurable[F] f) (hb : ∀ z, ‖f z‖ ≤ c) (hg : Integrable g μ) :
    Integrable (f * g) μ ∧ μ[f * g | F] =ᵐ[μ] f * μ[g | F] := by
  have hi : Integrable (f * g) μ := hg.bdd_mul
    (hf.mono ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  exact ⟨hi, condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable hi hg⟩

private theorem retained_moment (a : Fin p.K) (k : ℕ) (hk : 0 < k) :
    Integrable ((A).indicator (fun z => raw a z ^ k)) μ ∧
    μ[(A).indicator (fun z => raw a z ^ k) | F] =ᵐ[μ]
      (E ∩ H).indicator (μ[(E).indicator (fun z => raw a z ^ k) | F]) := by
  classical
  have hEH := (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
    rate rewards C_star C_h control0 q).inter
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H rate rewards C_star C_h control0 q)
  have heq : (A).indicator (fun z => raw a z ^ k) =
      (E ∩ H).indicator ((E).indicator (fun z => raw a z ^ k)) := by
    rw [success_raw rate rewards C_star C_h q a k hk]
    funext z
    by_cases hz : z ∈ E ∩ H
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz.1]
    · simp only [Set.indicator_of_notMem hz]
  rw [heq]
  have hi := maskedRaw_integrable rate rewards C_star C_h control0 q a k
  exact ⟨hi.indicator (((sourcePrefixFiltration control0).le' (q.val + 1)) _ hEH),
    condExp_indicator hi hEH⟩

include control0 in
private theorem mass_integrable : Integrable ((A).indicator (fun _ => (1 : ℝ))) μ :=
  (integrable_const _).indicator (event_measurable rate rewards C_star C_h control0 q)

private def driftCoordinate (q : Fin p.T) (a : Fin p.K) (z : X) : ℝ :=
  (actualRetainedLaterBirthEvent rate rewards C_star C_h q).indicator
    (fun z => originalPrefixTheta rate rewards C_star C_h q.val z a *
      ((2 * originalPrefixCoordinateBacklog rate rewards C_star C_h q.val z a + 1 / 2) *
        currentRaw rate rewards C_star C_h q a z +
        currentRaw rate rewards C_star C_h q a z ^ 2 +
        (-(15 / 2 : ℝ) * originalPrefixCoordinateBacklog rate rewards C_star C_h q.val z a + 16))) z

private theorem coordinate_transport (a : Fin p.K) :
    Integrable (driftCoordinate rate rewards C_star C_h q a) μ ∧
    μ[driftCoordinate rate rewards C_star C_h q a | F] =ᵐ[μ]
      (E ∩ H).indicator (fun z => θ z a *
        ((2 * b z a + 1 / 2) * μ[(E).indicator (raw a) | F] z +
          μ[(E).indicator (fun z => raw a z ^ 2) | F] z +
          (-(15 / 2 : ℝ) * b z a + 16) * α z)) := by
  classical
  let f : X → ℝ := fun z => θ z a * (2 * b z a + 1 / 2)
  let g : X → ℝ := fun z => θ z a * (-(15 / 2 : ℝ) * b z a + 16)
  let R1 := (A).indicator (fun z => raw a z ^ 1)
  let R2 := (A).indicator (fun z => raw a z ^ 2)
  let S := (A).indicator (fun _ => (1 : ℝ))
  have ht := theta_measurable rate rewards C_star C_h control0 q a
  have hb := backlog_measurable rate rewards C_star C_h control0 q a
  have hf : Measurable[F] f := ht.mul ((measurable_const.mul hb).add measurable_const)
  have hg : Measurable[F] g := ht.mul ((measurable_const.mul hb).add measurable_const)
  have htb (z : X) : ‖θ z a‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (theta_bounds rate rewards C_star C_h q.val z a).1]
    exact (theta_bounds rate rewards C_star C_h q.val z a).2
  have hbb (z : X) : ‖b z a‖ ≤ cap := by
    rw [Real.norm_of_nonneg (backlog_bounds rate rewards C_star C_h q.val z a).1]
    exact (backlog_bounds rate rewards C_star C_h q.val z a).2
  have hfb (z : X) : ‖f z‖ ≤ 2 * cap + 1 / 2 := by
    dsimp only [f]
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖2 * b z a + 1 / 2‖ := mul_le_mul_of_nonneg_right (htb z) (norm_nonneg _)
      _ ≤ 2 * cap + 1 / 2 := by
        have hx := norm_add_le (2 * b z a) (1 / 2 : ℝ)
        rw [norm_mul] at hx
        norm_num at hx
        have hbbz := hbb z
        simp only [Real.norm_eq_abs, one_mul] at hbbz ⊢
        linarith only [hx, hbbz]
  have hgb (z : X) : ‖g z‖ ≤ (15 / 2 : ℝ) * cap + 16 := by
    dsimp only [g]
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖-(15 / 2 : ℝ) * b z a + 16‖ :=
        mul_le_mul_of_nonneg_right (htb z) (norm_nonneg _)
      _ ≤ (15 / 2 : ℝ) * cap + 16 := by
        have hx := norm_add_le (-(15 / 2 : ℝ) * b z a) (16 : ℝ)
        rw [norm_mul] at hx
        norm_num at hx
        have hbbz := hbb z
        simp only [Real.norm_eq_abs, one_mul] at hbbz ⊢
        simp only [neg_mul] at ⊢
        linarith only [hx, hbbz]
  have h1 := retained_moment rate rewards C_star C_h control0 q a 1 (by norm_num)
  have h2 := retained_moment rate rewards C_star C_h control0 q a 2 (by norm_num)
  have hf1 := bounded_predictable_product control0 q f R1 _ hf hfb h1.1
  have ht2 := bounded_predictable_product control0 q (fun z => θ z a) R2 1 ht htb h2.1
  have hgs := bounded_predictable_product control0 q g S _ hg hgb
    (mass_integrable rate rewards C_star C_h control0 q)
  have heq : driftCoordinate rate rewards C_star C_h q a = f * R1 + (fun z => θ z a) * R2 + g * S := by
    funext z
    by_cases hz : z ∈ A
    · simp [driftCoordinate, R1, R2, S, f, g, Set.indicator_of_mem hz]
      ring
    · simp [driftCoordinate, R1, R2, S, Set.indicator_of_notMem hz]
  rw [heq]
  refine ⟨(hf1.1.add ht2.1).add hgs.1, ?_⟩
  filter_upwards [condExp_add (hf1.1.add ht2.1) hgs.1 F,
    condExp_add hf1.1 ht2.1 F, hf1.2, ht2.2, hgs.2, h1.2, h2.2,
    actualRetainedLaterBirthEvent_condExp rate rewards C_star C_h control0 q]
    with z hadd hadd' hp1 hp2 hps hr1 hr2 hs
  rw [hadd, Pi.add_apply, hadd', Pi.add_apply, hp1, hp2, hps]
  change f z * μ[R1 | F] z + θ z a * μ[R2 | F] z + g z * μ[S | F] z = _
  rw [hr1, hr2, hs]
  by_cases hz : z ∈ E ∩ H
  · simp only [Set.indicator_of_mem hz, pow_one]
    dsimp only [f, g]
    ring
  · simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]

private def inverseCoordinate (q : Fin p.T) (a : Fin p.K) (z : X) : ℝ :=
  match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h q z with
  | none => 0
  | some par => originalPrefixTheta rate rewards C_star C_h q.val z a /
      CanonicalRecordingRates.xi p rate.eta.val par.2 a

private theorem prefix_backlog_sum (z : X) :
    originalPrefixWeightedBacklog rate rewards C_star C_h q.val z =
      ∑ a : Fin p.K, θ z a * b z a := by
  cases hp : prefixInputs rate rewards C_star C_h q.val z <;>
    simp [originalPrefixWeightedBacklog, originalPrefixTheta,
      originalPrefixCoordinateBacklog, RecordedWeightedDrift.weightedBacklog, hp]

private theorem inverse_sum (z : X) :
    originalPrefixInverseRateSum rate rewards C_star C_h q z =
      ∑ a : Fin p.K, inverseCoordinate rate rewards C_star C_h q a z := by
  cases hp : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h q z with
  | none => simp [originalPrefixInverseRateSum, inverseCoordinate, hp]
  | some par =>
    cases hh : prefixInputs rate rewards C_star C_h q.val z <;>
      simp [originalPrefixInverseRateSum, inverseCoordinate, originalPrefixTheta, hp, hh]

private theorem sum_theta_le (n : ℕ) (z : X) :
    (∑ a : Fin p.K, originalPrefixTheta rate rewards C_star C_h n z a) ≤ (p.m : ℝ) := by
  cases hp : prefixInputs rate rewards C_star C_h n z with
  | none => simp [originalPrefixTheta, hp]
  | some past =>
    simp only [originalPrefixTheta, hp]
    exact (RecordedMarginalGrowth.state_sum_theta_eq_m _ _
      (ConstructorDimensions.m_pos p) p.m_lt_K).le

private theorem alpha_bounds (z : X) : 0 ≤ α z ∧ α z ≤ 1 :=
  ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthPresenceMassAtPrefix_bounds
    rate rewards C_star C_h control0 q _

private theorem reward_bounds (a : Fin p.K) :
    0 ≤ ((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ) ∧
      ((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ) ≤ 1 := by
  constructor
  · positivity
  · apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
    exact_mod_cast Nat.le_of_lt_succ (rewards q a).isLt

private theorem coordinate_bound (a : Fin p.K) :
    ∀ᵐ z ∂μ, μ[driftCoordinate rate rewards C_star C_h q a | F] z ≤
      (E ∩ H).indicator (fun z => α z *
        (-(11 / 2 : ℝ) * (θ z a * b z a) +
          inverseCoordinate rate rewards C_star C_h q a z + (33 / 2 : ℝ) * θ z a)) z := by
  filter_upwards [(coordinate_transport rate rewards C_star C_h control0 q a).2,
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_moments
      rate rewards C_star C_h control0 q a] with z hce hm
  rw [hce]
  by_cases hz : z ∈ E ∩ H
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    obtain ⟨par, hp⟩ := Option.isSome_iff_exists.mp hz.1
    have hmoment := hm par hp
    dsimp only at hmoment
    have hα := (alpha_bounds rate rewards C_star C_h control0 q z).1
    have hr := reward_bounds rewards q a
    have hfirst : μ[(E).indicator (raw a) | F] z ≤ α z :=
      hmoment.2.2.2.1.trans ((mul_le_mul_of_nonneg_left hr.2 hα).trans_eq (mul_one _))
    have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property par.2 a
    have hsecond : μ[(E).indicator (fun z => raw a z ^ 2) | F] z ≤
        α z / CanonicalRecordingRates.xi p rate.eta.val par.2 a := by
      calc
        _ ≤ α z * ((((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ^ 2 /
            CanonicalRecordingRates.xi p rate.eta.val par.2 a) := hmoment.2.2.2.2
        _ ≤ α z * (1 / CanonicalRecordingRates.xi p rate.eta.val par.2 a) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (by simpa using pow_le_pow_left₀ hr.1 hr.2 2) hxi.le) hα
        _ = _ := by ring
    have hc : 0 ≤ 2 * b z a + 1 / 2 := by
      positivity [(backlog_bounds rate rewards C_star C_h q.val z a).1]
    calc
      _ ≤ θ z a * ((2 * b z a + 1 / 2) * α z +
          α z / CanonicalRecordingRates.xi p rate.eta.val par.2 a +
          (-(15 / 2 : ℝ) * b z a + 16) * α z) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfirst hc) hsecond) le_rfl)
          (theta_bounds rate rewards C_star C_h q.val z a).1
      _ = _ := by simp only [inverseCoordinate, hp]; ring
  · simp only [Set.indicator_of_notMem hz, le_refl]

/-- Conditional weighted-square drift for the actual retained later birth.
The original whole-vector success mass multiplies every term, including the
negative backlog term. The inverse-rate sum uses the actual calendar anchor. -/
theorem originalLaterBirth_weightedSquare_condExp :
    ∀ᵐ z ∂μ, μ[(A).indicator
      (originalPrefixWeightedSquareDelta rate rewards C_star C_h q) | F] z ≤
      (E ∩ H).indicator (fun z => α z *
        (-(11 / 2 : ℝ) * originalPrefixWeightedBacklog rate rewards C_star C_h q.val z +
          originalPrefixInverseRateSum rate rewards C_star C_h q z + (33 / 2 : ℝ) * p.m)) z := by
  classical
  let D := (A).indicator (originalPrefixWeightedSquareDelta rate rewards C_star C_h q)
  let G := fun z => ∑ a : Fin p.K, driftCoordinate rate rewards C_star C_h q a z
  have hD : Integrable D μ :=
    ((potential_integrable rate rewards C_star C_h (q.val + 1)).sub
      (potential_integrable rate rewards C_star C_h q.val)).indicator
        (event_measurable rate rewards C_star C_h control0 q)
  have hcoord := fun a => (coordinate_transport rate rewards C_star C_h control0 q a).1
  have hG : Integrable G μ := integrable_finsetSum _ (fun a _ => hcoord a)
  have hle : D ≤ᵐ[μ] G := Filter.Eventually.of_forall (fun z => by
    by_cases hz : z ∈ A
    · simpa only [D, G, driftCoordinate, Set.indicator_of_mem hz] using
        originalLaterBirth_weightedSquare_pointwise rate rewards C_star C_h q z hz
    · simp only [D, G, driftCoordinate, Set.indicator_of_notMem hz, Finset.sum_const_zero, le_refl])
  have hsum : μ[G | F] =ᵐ[μ] fun z => ∑ a : Fin p.K,
      μ[driftCoordinate rate rewards C_star C_h q a | F] z :=
    by
      have heq : G = ∑ a : Fin p.K, driftCoordinate rate rewards C_star C_h q a := by
        funext z
        simp only [G, Finset.sum_apply]
      rw [heq]
      filter_upwards [condExp_finsetSum (s := Finset.univ) (fun a _ => hcoord a) F] with z hz
      simpa only [Finset.sum_apply] using hz
  filter_upwards [condExp_mono hD hG hle, hsum,
    Filter.eventually_all.mpr (fun a => coordinate_bound rate rewards C_star C_h control0 q a)]
    with z hmono hsumz hbounds
  refine (hmono.trans_eq hsumz).trans ((Finset.sum_le_sum (fun a _ => hbounds a)).trans ?_)
  by_cases hz : z ∈ E ∩ H
  · simp only [Set.indicator_of_mem hz]
    rw [prefix_backlog_sum rate rewards C_star C_h q z, inverse_sum rate rewards C_star C_h q z]
    calc
      _ = α z * (-(11 / 2 : ℝ) * (∑ a : Fin p.K, θ z a * b z a) +
          (∑ a : Fin p.K, inverseCoordinate rate rewards C_star C_h q a z) +
          (33 / 2 : ℝ) * (∑ a : Fin p.K, θ z a)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (sum_theta_le rate rewards C_star C_h q.val z)
            (show (0 : ℝ) ≤ 33 / 2 by norm_num)))
        (alpha_bounds rate rewards C_star C_h control0 q z).1
  · simp only [Set.indicator_of_notMem hz, Finset.sum_const_zero, le_refl]

include control0 in
private theorem inverse_integrable (a : Fin p.K) :
    Integrable (inverseCoordinate rate rewards C_star C_h q a) μ := by
  classical
  have hprod (S : Finset (Fin p.K)) :
      Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight v)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.theta p.m v a) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hprod S).div htotal
  have hf : Measurable (fun v : Fin p.K → ℝ => CanonicalRecordingRates.f p v a) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  have hxi : Measurable (fun par : AssignmentParameterFibreKernel.Theta p =>
      CanonicalRecordingRates.xi p rate.eta.val par.2 a) :=
    (AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
      (measurable_const.max hf)).comp measurable_snd
  let getXi := ReferenceCollectionOutcomeMeasurability.optionalElim (0 : ℝ)
    (fun par : AssignmentParameterFibreKernel.Theta p =>
      CanonicalRecordingRates.xi p rate.eta.val par.2 a)
  have hx : Measurable[F] (fun z => getXi
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h q z)) :=
    (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim 0 _ hxi).comp
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
        rate rewards C_star C_h control0 q)
  have heq : inverseCoordinate rate rewards C_star C_h q a = fun z => θ z a /
      getXi (ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h q z) := by
    funext z
    cases hp : ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h q z <;>
      simp [inverseCoordinate, getXi, ReferenceCollectionOutcomeMeasurability.optionalElim, hp]
  have hm : Measurable[F] (inverseCoordinate rate rewards C_star C_h q a) := by
    rw [heq]
    exact (theta_measurable rate rewards C_star C_h control0 q a).div hx
  apply (integrable_const (1 / β)).mono'
    (hm.mono ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl).aestronglyMeasurable
  filter_upwards [] with z
  cases hp : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h q z with
  | none => simp [inverseCoordinate, hp, (CanonicalRecordingRates.beta_pos p rate.eta.property).le]
  | some par =>
    simp only [inverseCoordinate, hp]
    have ht := theta_bounds rate rewards C_star C_h q.val z a
    have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property par.2 a
    rw [Real.norm_of_nonneg (div_nonneg ht.1 hxi.le)]
    exact (div_le_div_of_nonneg_right ht.2 hxi.le).trans
      (one_div_le_one_div_of_le (CanonicalRecordingRates.beta_pos p rate.eta.property)
        (CanonicalRecordingRates.beta_le_xi p rate.eta.property par.2 a))

private theorem goodTerm_integrable : Integrable ((E ∩ H).indicator (fun z =>
    α z * (originalPrefixInverseRateSum rate rewards C_star C_h q z + (33 / 2 : ℝ) * p.m))) μ := by
  have hI : Integrable (originalPrefixInverseRateSum rate rewards C_star C_h q) μ := by
    have heq : originalPrefixInverseRateSum rate rewards C_star C_h q =
        fun z => ∑ a : Fin p.K, inverseCoordinate rate rewards C_star C_h q a z :=
      funext (inverse_sum rate rewards C_star C_h q)
    rw [heq]
    exact integrable_finsetSum _ (fun a _ => inverse_integrable rate rewards C_star C_h control0 q a)
  have hα := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthPresenceMass_measurable_sourcePrefix
    rate rewards C_star C_h control0 q
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  exact ((hI.add (integrable_const _)).bdd_mul
    (hα.mono hle le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (alpha_bounds rate rewards C_star C_h control0 q z).1]
      exact (alpha_bounds rate rewards C_star C_h control0 q z).2))).indicator
        (hle _ ((ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
          rate rewards C_star C_h control0 q).inter
          (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H rate rewards C_star C_h control0 q)))

/-- The predictable backlog is weighted by the SAME actual success mass.
This identity retains the actual successful-event cost for integration. -/
theorem originalLaterBirth_cost_condExp :
    Integrable (actualRetainedLaterBirthCost rate rewards C_star C_h q) μ ∧
    μ[actualRetainedLaterBirthCost rate rewards C_star C_h q | F] =ᵐ[μ]
      (E ∩ H).indicator (fun z => α z *
        originalPrefixWeightedBacklog rate rewards C_star C_h q.val z) := by
  let C := originalPrefixWeightedBacklog rate rewards C_star C_h q.val
  let S := (A).indicator (fun _ => (1 : ℝ))
  have hb (z : X) : ‖C z‖ ≤ (p.K : ℝ) * cap := by
    rw [show C z = ∑ a : Fin p.K, θ z a * b z a from
      prefix_backlog_sum rate rewards C_star C_h q z]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun a _ =>
      mul_nonneg (theta_bounds rate rewards C_star C_h q.val z a).1
        (backlog_bounds rate rewards C_star C_h q.val z a).1))]
    calc
      _ ≤ ∑ _a : Fin p.K, cap := Finset.sum_le_sum (fun a _ => by
        have ht := theta_bounds rate rewards C_star C_h q.val z a
        have hback := backlog_bounds rate rewards C_star C_h q.val z a
        exact (mul_le_mul_of_nonneg_right ht.2 hback.1).trans (by simpa using hback.2))
      _ = _ := by simp
  have hp := bounded_predictable_product control0 q C S _
    (originalBacklog_measurable rate rewards C_star C_h control0 q) hb
    (mass_integrable rate rewards C_star C_h control0 q)
  have heq : actualRetainedLaterBirthCost rate rewards C_star C_h q = C * S := by
    funext z
    by_cases hz : z ∈ A <;> simp [actualRetainedLaterBirthCost, C, S, Set.indicator, hz]
  rw [heq]
  refine ⟨hp.1, ?_⟩
  filter_upwards [hp.2, actualRetainedLaterBirthEvent_condExp rate rewards C_star C_h control0 q]
    with z hpz hsz
  rw [hpz]
  change C z * μ[S | F] z = _
  rw [hsz]
  by_cases hz : z ∈ E ∩ H <;> simp [Set.indicator, hz, C, mul_comm]

/-- Integrated drift with the expected ACTUAL retained successful birth cost.
No predictable unmasked backlog is substituted for that cost. -/
theorem originalLaterBirth_weightedSquare_integral :
    (∫ z, (A).indicator (originalPrefixWeightedSquareDelta rate rewards C_star C_h q) z ∂μ) ≤
      -(11 / 2 : ℝ) * (∫ z, actualRetainedLaterBirthCost rate rewards C_star C_h q z ∂μ) +
      ∫ z, (E ∩ H).indicator (fun z => α z *
        (originalPrefixInverseRateSum rate rewards C_star C_h q z + (33 / 2 : ℝ) * p.m)) z ∂μ := by
  let good := (E ∩ H).indicator (fun z => α z *
    (originalPrefixInverseRateSum rate rewards C_star C_h q z + (33 / 2 : ℝ) * p.m))
  have hc := originalLaterBirth_cost_condExp rate rewards C_star C_h control0 q
  have hineq : μ[(A).indicator (originalPrefixWeightedSquareDelta rate rewards C_star C_h q) | F]
      ≤ᵐ[μ] fun z => -(11 / 2 : ℝ) * μ[actualRetainedLaterBirthCost rate rewards C_star C_h q | F] z + good z := by
    filter_upwards [originalLaterBirth_weightedSquare_condExp rate rewards C_star C_h control0 q, hc.2]
      with z hd hcost
    rw [hcost]
    refine hd.trans_eq ?_
    by_cases hz : z ∈ E ∩ H
    · simp only [good, Set.indicator_of_mem hz]
      ring
    · simp only [good, Set.indicator_of_notMem hz]
      ring
  have hDc : Integrable (μ[(A).indicator
      (originalPrefixWeightedSquareDelta rate rewards C_star C_h q) | F]) μ := integrable_condExp
  have hCc : Integrable (μ[actualRetainedLaterBirthCost rate rewards C_star C_h q | F]) μ :=
    integrable_condExp
  have hi := integral_mono_ae hDc
    ((hCc.const_mul (-(11 / 2 : ℝ))).add
      (goodTerm_integrable rate rewards C_star C_h control0 q)) hineq
  simp only [Pi.add_apply] at hi
  rw [integral_add (hCc.const_mul (-(11 / 2 : ℝ)))
    (goodTerm_integrable rate rewards C_star C_h control0 q), integral_const_mul] at hi
  simpa only [integral_condExp ((sourcePrefixFiltration control0).le' (q.val + 1))] using hi

private theorem arrival_coordinate (a : Fin p.K) :
    Integrable ((A).indicator (fun z => θ z a * raw a z)) μ ∧
    (∀ᵐ z ∂μ, μ[(A).indicator (fun z => θ z a * raw a z) | F] z ≤
      (E ∩ H).indicator (fun z => α z * θ z a) z) := by
  let R := (A).indicator (fun z => raw a z ^ 1)
  have hr := retained_moment rate rewards C_star C_h control0 q a 1 (by norm_num)
  have hp := bounded_predictable_product control0 q (fun z => θ z a) R 1
    (theta_measurable rate rewards C_star C_h control0 q a)
    (fun z => by
      rw [Real.norm_of_nonneg (theta_bounds rate rewards C_star C_h q.val z a).1]
      exact (theta_bounds rate rewards C_star C_h q.val z a).2) hr.1
  have heq : (A).indicator (fun z => θ z a * raw a z) = (fun z => θ z a) * R := by
    funext z
    by_cases hz : z ∈ A <;> simp [R, Set.indicator, hz]
  rw [heq]
  refine ⟨hp.1, ?_⟩
  filter_upwards [hp.2, hr.2,
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_moments
      rate rewards C_star C_h control0 q a] with z hpz hrz hm
  rw [hpz]
  change θ z a * μ[R | F] z ≤ _
  rw [hrz]
  simp only [pow_one]
  by_cases hz : z ∈ E ∩ H
  · simp only [Set.indicator_of_mem hz]
    obtain ⟨par, hpar⟩ := Option.isSome_iff_exists.mp hz.1
    have hmoment := hm par hpar
    have hfirst : μ[(E).indicator (raw a) | F] z ≤ α z :=
      hmoment.2.2.2.1.trans ((mul_le_mul_of_nonneg_left (reward_bounds rewards q a).2
        (alpha_bounds rate rewards C_star C_h control0 q z).1).trans_eq (mul_one _))
    exact (mul_le_mul_of_nonneg_left hfirst
      (theta_bounds rate rewards C_star C_h q.val z a).1).trans_eq (mul_comm _ _)
  · simp only [Set.indicator_of_notMem hz, mul_zero, le_refl]

/-- Retained weighted arrivals have first moment at most `m` times the
conditional mass of the ACTUAL successful retained birth. -/
theorem originalLaterBirth_weightedArrival_condExp :
    Integrable (actualRetainedLaterBirthWeightedArrival rate rewards C_star C_h q) μ ∧
    (∀ᵐ z ∂μ, μ[actualRetainedLaterBirthWeightedArrival rate rewards C_star C_h q | F] z ≤
      (p.m : ℝ) * μ[(A).indicator (fun _ => (1 : ℝ)) | F] z) := by
  classical
  let W := fun a : Fin p.K => (A).indicator (fun z => θ z a * raw a z)
  have hw := fun a => arrival_coordinate rate rewards C_star C_h control0 q a
  have heq : actualRetainedLaterBirthWeightedArrival rate rewards C_star C_h q = ∑ a : Fin p.K, W a := by
    funext z
    by_cases hz : z ∈ A <;>
      simp [actualRetainedLaterBirthWeightedArrival, W, Set.indicator, hz]
  rw [heq]
  refine ⟨integrable_finsetSum' _ (fun a _ => (hw a).1), ?_⟩
  filter_upwards [condExp_finsetSum (s := Finset.univ) (fun a _ => (hw a).1) F,
    Filter.eventually_all.mpr (fun a => (hw a).2),
    actualRetainedLaterBirthEvent_condExp rate rewards C_star C_h control0 q]
    with z hsum hbounds hmass
  rw [hsum, hmass]
  simp only [Finset.sum_apply]
  refine (Finset.sum_le_sum (fun a _ => hbounds a)).trans ?_
  by_cases hz : z ∈ E ∩ H
  · simp only [Set.indicator_of_mem hz, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_theta_le rate rewards C_star C_h q.val z)
      (alpha_bounds rate rewards C_star C_h control0 q z).1).trans_eq (mul_comm _ _)
  · simp only [Set.indicator_of_notMem hz, Finset.sum_const_zero, mul_zero, le_refl]

include control0 in
/-- Integrated arrival estimate with the mass of the actual successful event,
for the same original-source weighted-arrival consumer. -/
theorem originalLaterBirth_weightedArrival_integral :
    (∫ z, actualRetainedLaterBirthWeightedArrival rate rewards C_star C_h q z ∂μ) ≤
      (p.m : ℝ) * (∫ z, (A).indicator (fun _ => (1 : ℝ)) z ∂μ) := by
  have hw := originalLaterBirth_weightedArrival_condExp rate rewards C_star C_h control0 q
  have hWc : Integrable (μ[actualRetainedLaterBirthWeightedArrival rate rewards C_star C_h q | F]) μ :=
    integrable_condExp
  have hSc : Integrable (μ[(A).indicator (fun _ => (1 : ℝ)) | F]) μ := integrable_condExp
  have hi := integral_mono_ae hWc (hSc.const_mul (p.m : ℝ)) hw.2
  rw [integral_const_mul] at hi
  simpa only [integral_condExp ((sourcePrefixFiltration control0).le' (q.val + 1))] using hi

end Bandits.Support.ReferenceOriginalCalendarLaterBirthWeightedDrift

end
