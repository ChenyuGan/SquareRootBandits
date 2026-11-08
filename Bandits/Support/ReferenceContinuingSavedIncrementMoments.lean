/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingRecordingPhysicalReward
public import Bandits.Support.ReferenceContinuingRecordingFastLaw

/-!
# Fixed-prefix moments of one continuing saved increment

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-187,256-264`, and
`sources/zip4/manuscript/06_interruptions.tex:195-233,246-295`.

These are moments of the current physical saved emission for one actually
unoccupied follower under the original whole `TimeControl` law. The logging
and marker facts come from the continuing physical producers; this module
does not assert source-conditional freshness, recovery, queue truth, or
retained-round closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceContinuingDataCandidateLogging
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceContinuingRecordingFastPair
open Bandits.Support.ReferenceContinuingRecordingPhysicalReward
open Bandits.Support.ReferenceContinuingRecordingFastLaw
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RecordedRoundMoments
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.QuantizedRecordingMoments

namespace Bandits.Support.ReferenceContinuingSavedIncrementMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The normalized value of the current physical logging emission for one
follower's assignment. Older members of the carried buffer are not included. -/
def normalizedCurrentSavedContribution
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) : ℝ :=
  (ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
      record payload i : ℝ) /
    (rate.eta.val * (D p : ℝ))

/-- The current normalized saved contribution has the actual marker law and
the quantized first and second moments at one continuing fixed prefix.

All prefix, preparation, and ordinary-seed conditions are the explicit inputs
of the physical recording producers. The focal status condition refers to
the state in the actual prepared follower configuration through `ho`. -/
theorem actual_continuing_saved_increment_moments
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (seedMemory i))
    (hseedUnoccupied : ∀ i, (seed i).status = .unoccupied)
    (hseedValid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hseedPairwise : ∀ i, (seed i).buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q
        (candidateInput initial rows selected rewards start count hspan hmode).time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val
      (candidateInput initial rows selected rewards start count hspan hmode).time
      r.priorClock r.clockPending = .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time)
      (candidateInput initial rows selected rewards start count hspan hmode).row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time).payload
      d.startResult (candidateInput initial rows selected rewards start count hspan hmode).time
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time).complementWeights
      (candidateInput initial rows selected rewards start count hspan hmode).row)
    (hc : (ReferenceActivePhysicalStep.prepare
      (candidateInput initial rows selected rewards start count hspan hmode)).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare
      (candidateInput initial rows selected rewards start count hspan hmode)).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (henabled : (candidateInput initial rows selected rewards start count hspan hmode).time.val + 1 <
      d.startResult.clock.g)
    (i : Fin (p.m - 1))
    (hcurrentUnoccupied : (states i).status = .unoccupied) :
    let x := candidateInput initial rows selected rewards start count hspan hmode
    let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
    let pair := ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
      initial rows selected rewards start count hspan hmode r.payload true W
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
    let marker := fun u : ContinuousLearningRows.TimeControl p => (pair u).1
    let arm := r.payload.assignment.assigned (bufferFollowerIndex i)
    let xi := CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor arm
    let beta := CanonicalRecordingRates.beta p rate.eta.val
    let rho := ((rewards x.time arm).val : ℝ) / (D p : ℝ)
    let value := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
    let f := fun u : ContinuousLearningRows.TimeControl p =>
      normalizedCurrentSavedContribution
        (ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
          rewards start count hspan hmode u) r.payload i
    (0 < xi ∧ 0 < beta ∧ beta ≤ xi ∧ 0 ≤ rho ∧ rho ≤ 1) ∧
    (∀ u, f u = if marker u = some arm then value else 0) ∧
    Measurable f ∧
    Integrable f (ContinuousLearningRows.timeControlLaw p) ∧
    Integrable (fun u => f u ^ 2) (ContinuousLearningRows.timeControlLaw p) ∧
    (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) = xi * value ∧
    (∫ u, f u ^ 2 ∂ContinuousLearningRows.timeControlLaw p) = xi * value ^ 2 ∧
    rho - xi / (rate.eta.val * (D p : ℝ)) ≤
        ∫ u, f u ∂ContinuousLearningRows.timeControlLaw p ∧
    (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) ≤ rho ∧
    (∫ u, f u ^ 2 ∂ContinuousLearningRows.timeControlLaw p) ≤ rho ^ 2 / xi ∧
    (∫ u, f u ^ 2 ∂ContinuousLearningRows.timeControlLaw p) ≤ 1 / xi ∧
    (∀ u, 0 ≤ f u ∧ f u ≤ 1 / beta) := by
  classical
  let x := candidateInput initial rows selected rewards start count hspan hmode
  let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
  let pair := ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
    initial rows selected rewards start count hspan hmode r.payload true W
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
  let marker := fun u : ContinuousLearningRows.TimeControl p => (pair u).1
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap r.payload.anchor r.payload.anchor_pos
  let arm := r.payload.assignment.assigned (bufferFollowerIndex i)
  let xi := CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor arm
  let beta := CanonicalRecordingRates.beta p rate.eta.val
  let rho := ((rewards x.time arm).val : ℝ) / (D p : ℝ)
  let value := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
  let f : ContinuousLearningRows.TimeControl p → ℝ := fun u =>
    normalizedCurrentSavedContribution
      (ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
        rewards start count hspan hmode u) r.payload i
  let markerValue : Option (Fin p.K) → ℝ := fun outcome =>
    if outcome = some arm then value else 0

  have hphysical :=
    ReferenceContinuingRecordingPhysicalReward.prefix_continuing_recording_physical_reward
      initial rows selected rewards start count hspan hmode seed seedMemory hfirst hseed
      hseedUnoccupied hseedValid hseedPairwise hseedTime r q base d hs c a hc states memories
      ho henabled
  have hlaw :=
    ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
      initial rows selected rewards start count hspan hmode seed seedMemory hfirst hseed
      hseedUnoccupied hseedValid hseedPairwise hseedTime r q base d hs c a hc states memories
      ho henabled
  rcases hlaw with ⟨hpairMeas, _, _, hpairMarkerPMF, _, _, _, _, _⟩

  have hxi : 0 < xi :=
    CanonicalRecordingRates.xi_pos p rate.eta.property r.payload.anchor arm
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbetaLe : beta ≤ xi :=
    CanonicalRecordingRates.beta_le_xi p rate.eta.property r.payload.anchor arm
  have hDreal : 0 < (D p : ℝ) := by
    exact_mod_cast D_pos p
  have hgridNat : (rewards x.time arm).val ≤ D p :=
    Nat.le_of_lt_succ (rewards x.time arm).isLt
  have hgrid : ((rewards x.time arm).val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast hgridNat
  have hrho : rho ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [rho]
      exact div_nonneg (Nat.cast_nonneg _) hDreal.le
    · dsimp [rho]
      exact (div_le_one hDreal).2 hgrid
  have hvalueNonneg : 0 ≤ value :=
    QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val xi rho
      rate.eta.property
  have hvalueBound : value ≤ 1 / beta :=
    QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
      (D p) rate.eta.val xi rho beta (D_pos p) rate.eta.property hxi hrho hbeta hbetaLe
  have hrounding :=
    QuantizedRecordingMoments.quantizedValue_roundingError
      (D p) rate.eta.val xi rho (D_pos p) rate.eta.property hxi hrho
  have hfirstBound :=
    QuantizedRecordingMoments.quantizedValue_firstMoment_le
      (D p) rate.eta.val xi rho (D_pos p) rate.eta.property hxi hrho
  have hsecondBound :=
    QuantizedRecordingMoments.quantizedValue_secondMoment_le
      (D p) rate.eta.val xi rho (D_pos p) rate.eta.property hxi hrho
  have hrhoSq : rho ^ 2 ≤ 1 := by
    nlinarith [hrho.1, hrho.2]

  have hphysicalAt := hphysical.2
  have hpoint : ∀ u : ContinuousLearningRows.TimeControl p,
      f u = markerValue (marker u) := by
    intro u
    have hmarker : marker u =
        ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
          rewards start count hspan hmode r.payload true u := by
      rfl
    rcases hphysicalAt u with ⟨_, hfollowers⟩
    rcases hfollowers i hcurrentUnoccupied with ⟨_, _, _, _, hsaved⟩
    have hcontribution :
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
          (ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
            rewards start count hspan hmode u) r.payload i =
          if marker u = some arm then
            Nat.floor ((D p : ℝ) * rate.eta.val *
              (((rewards x.time arm).val : ℝ) / (D p : ℝ)) / xi)
          else 0 := by
      simpa [hmarker, arm] using hsaved
    change
      (ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
        (ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
          rewards start count hspan hmode u) r.payload i : ℝ) /
        (rate.eta.val * (D p : ℝ)) = markerValue (marker u)
    rw [hcontribution]
    by_cases hmarked : marker u = some arm
    · simp [markerValue, value, xi, rho, arm, hmarked,
        QuantizedRecordingMoments.quantizedValue,
        QuantizedRecordingMoments.quantizedIndex]
    · simp [markerValue, value, xi, rho, arm, hmarked,
        QuantizedRecordingMoments.quantizedValue,
        QuantizedRecordingMoments.quantizedIndex]

  have htargetSet : MeasurableSet {outcome : Option (Fin p.K) | outcome = some arm} := by
    have hset : {outcome : Option (Fin p.K) | outcome = some arm} = {some arm} := by
      ext outcome
      simp
    rw [hset]
    exact measurableSet_singleton _
  have hmarkerValueMeas : Measurable markerValue :=
    Measurable.ite htargetSet measurable_const measurable_const
  have hmarkerMeas : Measurable marker := measurable_fst.comp hpairMeas
  have hfMeas : Measurable f := by
    have hfun : f = fun u => markerValue (marker u) := funext hpoint
    rw [hfun]
    exact hmarkerValueMeas.comp hmarkerMeas

  have hpointRange : ∀ u : ContinuousLearningRows.TimeControl p,
      0 ≤ f u ∧ f u ≤ 1 / beta := by
    intro u
    rw [hpoint u]
    by_cases hmarked : marker u = some arm
    · simp [markerValue, hmarked]
      constructor
      · exact hvalueNonneg
      · simpa only [one_div] using hvalueBound
    · simp [markerValue, hmarked]
      exact hbeta.le

  have hnormBound : ∀ u : ContinuousLearningRows.TimeControl p, ‖f u‖ ≤ value := by
    intro u
    rw [hpoint u]
    by_cases hmarked : marker u = some arm
    · simp [markerValue, hmarked, abs_of_nonneg hvalueNonneg]
    · simp [markerValue, hmarked, hvalueNonneg]
  have hfIntegrable : Integrable f (ContinuousLearningRows.timeControlLaw p) := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable value
    exact Filter.Eventually.of_forall hnormBound

  have hvalueSqNonneg : 0 ≤ value ^ 2 := sq_nonneg value
  have hnormSqBound : ∀ u : ContinuousLearningRows.TimeControl p,
      ‖f u ^ 2‖ ≤ value ^ 2 := by
    intro u
    rw [hpoint u]
    by_cases hmarked : marker u = some arm
    · simp [markerValue, hmarked]
    · simp [markerValue, hmarked, hvalueSqNonneg]
  have hfSqMeas : Measurable (fun u : ContinuousLearningRows.TimeControl p => f u ^ 2) :=
    hfMeas.pow_const 2
  have hfSqIntegrable : Integrable (fun u : ContinuousLearningRows.TimeControl p => f u ^ 2)
      (ContinuousLearningRows.timeControlLaw p) := by
    apply Integrable.of_bound hfSqMeas.aestronglyMeasurable (value ^ 2)
    exact Filter.Eventually.of_forall hnormSqBound

  have hmarkerPush :
      (ContinuousLearningRows.timeControlLaw p).map marker =
        (RecordedRoundMoments.recordingOutcomePMF rates).toMeasure := by
    calc
      (ContinuousLearningRows.timeControlLaw p).map marker =
          ((ContinuousLearningRows.timeControlLaw p).map pair).map Prod.fst := by
        change (ContinuousLearningRows.timeControlLaw p).map (Prod.fst ∘ pair) = _
        symm
        exact Measure.map_map measurable_fst hpairMeas
      _ = (RecordedRoundMoments.recordingOutcomePMF rates).toMeasure := by
        simpa [pair, rates, SnapshotRecordingKernel.recordingRates] using hpairMarkerPMF

  have hrateArm : rates.rate arm = xi := by
    rfl
  have hfirstPMFRate :
      (∫ outcome, markerValue outcome ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) =
        rates.rate arm * value := by
    rw [PMF.integral_eq_sum]
    simp [markerValue, RecordedRoundMoments.recordingOutcomePMF,
      RecordedRoundMoments.outcomeMass, ENNReal.toReal_ofReal,
      RecordedRoundMoments.RecordingRates.rate_nonneg]
  have hfirstPMF :
      (∫ outcome, markerValue outcome ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) =
        xi * value := by
    simpa only [hrateArm] using hfirstPMFRate
  have hmarkerValueSqMeas : Measurable (fun outcome => markerValue outcome ^ 2) :=
    hmarkerValueMeas.pow_const 2
  have hsecondPMFRate :
      (∫ outcome, markerValue outcome ^ 2
        ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) = rates.rate arm * value ^ 2 := by
    rw [PMF.integral_eq_sum]
    simp [markerValue, RecordedRoundMoments.recordingOutcomePMF,
      RecordedRoundMoments.outcomeMass, ENNReal.toReal_ofReal,
      RecordedRoundMoments.RecordingRates.rate_nonneg]
  have hsecondPMF :
      (∫ outcome, markerValue outcome ^ 2
        ∂(RecordedRoundMoments.recordingOutcomePMF rates).toMeasure) = xi * value ^ 2 := by
    simpa only [hrateArm] using hsecondPMFRate

  have hmapFirst := MeasureTheory.integral_map
    (μ := ContinuousLearningRows.timeControlLaw p)
    hmarkerMeas.aemeasurable hmarkerValueMeas.aestronglyMeasurable
  have hfirstIntegral :
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) = xi * value := by
    calc
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) =
          ∫ u, markerValue (marker u) ∂ContinuousLearningRows.timeControlLaw p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = ∫ outcome, markerValue outcome ∂
          (ContinuousLearningRows.timeControlLaw p).map marker := hmapFirst.symm
      _ = ∫ outcome, markerValue outcome ∂
          (RecordedRoundMoments.recordingOutcomePMF rates).toMeasure := by
        rw [hmarkerPush]
      _ = xi * value := hfirstPMF

  have hmapSecond := MeasureTheory.integral_map
    (μ := ContinuousLearningRows.timeControlLaw p)
    hmarkerMeas.aemeasurable hmarkerValueSqMeas.aestronglyMeasurable
  have hsecondIntegral :
      (∫ u, f u ^ 2 ∂ContinuousLearningRows.timeControlLaw p) = xi * value ^ 2 := by
    calc
      (∫ u, f u ^ 2 ∂ContinuousLearningRows.timeControlLaw p) =
          ∫ u, markerValue (marker u) ^ 2 ∂ContinuousLearningRows.timeControlLaw p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => congrArg (fun z : ℝ => z ^ 2) (hpoint u))
      _ = ∫ outcome, markerValue outcome ^ 2 ∂
          (ContinuousLearningRows.timeControlLaw p).map marker := hmapSecond.symm
      _ = ∫ outcome, markerValue outcome ^ 2 ∂
          (RecordedRoundMoments.recordingOutcomePMF rates).toMeasure := by
        rw [hmarkerPush]
      _ = xi * value ^ 2 := hsecondPMF

  refine ⟨⟨hxi, hbeta, hbetaLe, hrho.1, hrho.2⟩, ?_, hfMeas, hfIntegrable,
    hfSqIntegrable, hfirstIntegral, hsecondIntegral, ?_, ?_, ?_, ?_, hpointRange⟩
  · intro u
    simpa [markerValue] using hpoint u
  · rw [hfirstIntegral]
    exact hrounding
  · rw [hfirstIntegral]
    exact hfirstBound
  · rw [hsecondIntegral]
    exact hsecondBound
  · rw [hsecondIntegral]
    exact hsecondBound.trans
      (div_le_div_of_nonneg_right hrhoSq hxi.le)

end Bandits.Support.ReferenceContinuingSavedIncrementMoments

end
