/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingRecordingFastPair

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
# The continuing-live physical recording and fast-arm law

This module consumes the actual continuing-live physical marker/fast pair on
the whole time-control space and on each fixed original affine-sample family.
It proves the concrete joint pushforward, its marker and fast marginals, the
marker atom masses, and the auxiliary one-round fast reward expectation.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-187,329-382`, and
`sources/zip4/manuscript/06_interruptions.tex:195-233,246-295`.

These are fixed computed-prefix laws under the visible continuing-live
operational telescope. They do not prove adaptive conditional freshness,
actual coordinator reward while confirmations are missing, or manuscript
closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceContinuingDataCandidateLogging
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceContinuingRecordingFastPair
open Bandits.Support.ReferenceOccupiedFieldHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.RecordedRoundMoments
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.MixedAuxiliaryReward
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceContinuingRecordingFastLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The actual whole-control pair law and its one-round consumers on one
computed prefix with an actual continuing-live preparation.

The initial ordinary follower seeds and their buffer conditions are genuine
prefix inputs. Current occupied fields and current candidate logs are produced
inside `prefix_physical_fast_pair_eq`; no current marker, pair law, or
measurability premise is accepted here. -/
theorem actual_continuing_live_joint_law
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
      d.startResult.clock.g) :
    let x := candidateInput initial rows selected rewards start count hspan hmode
    let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
    let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
      r q base x.time d states
    let actualPair :=
      ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
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
    let actualMeasure := (ContinuousLearningRows.timeControlLaw p).map actualPair
    Measurable actualPair ∧
    actualMeasure = FastRewardSliceLaw.liveRecordingFastPushforward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot ∧
    (∀ family : ContinuousLearningRows.AffineSamples p,
      Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
        actualPair (slice, family)) ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actualPair (slice, family)) =
        FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot) ∧
    actualMeasure.map Prod.fst =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
          rate.sourceCap r.payload.anchor r.payload.anchor_pos)).toMeasure ∧
    actualMeasure.map Prod.snd =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        r.payload.anchor W r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment)).toMeasure ∧
    (∀ j : Fin p.K,
      (actualMeasure.map Prod.fst) {some j} =
        ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor j)) ∧
    (actualMeasure.map Prod.fst) {none} =
      ENNReal.ofReal
        (1 - ∑ j : Fin p.K, CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor j) ∧
    Integrable
      (fun z : Option (Fin p.K) ×
          FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) =>
        MixedAuxiliaryReward.oneRoundAuxiliaryReward
          (fun j : Fin p.K =>
            ((rewards x.time j).val : ℝ) / (D p : ℝ))
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) z.2)
      actualMeasure ∧
    (∫ z : Option (Fin p.K) ×
        FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment),
      MixedAuxiliaryReward.oneRoundAuxiliaryReward
        (fun j : Fin p.K => ((rewards x.time j).val : ℝ) / (D p : ℝ))
        (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) z.2
      ∂ actualMeasure) =
      ∑ j : FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment),
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
          r.payload.anchor W r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) j *
          MixedAuxiliaryReward.oneRoundAuxiliaryReward
            (fun i : Fin p.K => ((rewards x.time i).val : ℝ) / (D p : ℝ))
            (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) j := by
  classical
  intro x W snapshot actualPair actualMeasure
  let canonicalPair := FastRewardSliceLaw.liveRecordingFastPair
    p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
    r.payload.anchor_pos
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    r.payload.assignment snapshot
  have hprefix := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    initial rows selected rewards start count hspan hmode seed seedMemory hfirst hseed
    hseedUnoccupied hseedValid hseedPairwise hseedTime r q base d hs c a hc states memories
    ho henabled
  have hpoint : ∀ u : ContinuousLearningRows.TimeControl p,
      actualPair u = canonicalPair u.1 := by
    intro u
    simpa only [actualPair, canonicalPair,
      FastRewardSliceLaw.liveRecordingFastPair] using hprefix u
  have hpairEq : actualPair = fun u : ContinuousLearningRows.TimeControl p =>
      canonicalPair u.1 := funext hpoint
  have hcanonicalMeasurable : Measurable canonicalPair :=
    FastRewardSliceLaw.measurable_liveRecordingFastPair p rate.eta.val rate.eta.property
      rate.sourceCap r.payload.anchor W r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot
  have hactualMeasurable : Measurable actualPair := by
    rw [hpairEq]
    exact hcanonicalMeasurable.comp measurable_fst
  have hpush : actualMeasure = FastRewardSliceLaw.liveRecordingFastPushforward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot := by
    dsimp only [actualMeasure]
    calc
      (ContinuousLearningRows.timeControlLaw p).map actualPair =
          (ContinuousLearningRows.timeControlLaw p).map
            (fun u : ContinuousLearningRows.TimeControl p => canonicalPair u.1) := by
        rw [hpairEq]
      _ = ((ContinuousLearningRows.timeControlLaw p).map Prod.fst).map canonicalPair := by
        symm
        exact Measure.map_map hcanonicalMeasurable measurable_fst
      _ = (ContinuousControlSlice.sliceLaw p.m p.K).map canonicalPair := by
        rw [ContinuousLearningRows.map_slice p]
      _ = FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot := rfl
  have hfixedFamilies : ∀ family : ContinuousLearningRows.AffineSamples p,
      Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
        actualPair (slice, family)) ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actualPair (slice, family)) =
        FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot := by
    intro family
    have hfixed :=
      ReferenceContinuingRecordingFastPair.fixedFamily_joint_pushforward_of_identity
        actualPair canonicalPair hcanonicalMeasurable hpoint family
    simpa only [FastRewardSliceLaw.liveRecordingFastPushforward] using hfixed
  have hfst : actualMeasure.map Prod.fst =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
          rate.sourceCap r.payload.anchor r.payload.anchor_pos)).toMeasure := by
    rw [hpush]
    exact FastRewardSliceLaw.liveRecordingFastPushforward_fst p rate.eta.val
      rate.eta.property rate.sourceCap r.payload.anchor W r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot
  have hsnd : actualMeasure.map Prod.snd =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        r.payload.anchor W r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment)).toMeasure := by
    rw [hpush]
    exact FastRewardSliceLaw.liveRecordingFastPushforward_snd p rate.eta.val
      rate.eta.property rate.sourceCap r.payload.anchor W r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot
  have hsome : ∀ j : Fin p.K,
      (actualMeasure.map Prod.fst) {some j} =
        ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor j) := by
    intro j
    rw [hfst, RecordedRoundMoments.recordingOutcomePMF_toMeasure_some]
    rfl
  have hnone : (actualMeasure.map Prod.fst) {none} =
      ENNReal.ofReal
        (1 - ∑ j : Fin p.K, CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor j) := by
    rw [hfst, RecordedRoundMoments.recordingOutcomePMF_toMeasure_none]
    rfl
  let auxiliaryReward : Fin p.K → ℝ := fun j =>
    ((rewards x.time j).val : ℝ) / (D p : ℝ)
  have hgridBounds : ∀ j : Fin p.K,
      0 ≤ auxiliaryReward j ∧ auxiliaryReward j ≤ 1 := by
    intro j
    have hDpos : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
    have hgrid : ((rewards x.time j).val : ℝ) ≤ (D p : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ (rewards x.time j).isLt
    dsimp [auxiliaryReward]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hDpos.le, (div_le_one hDpos).2 hgrid⟩
  have hinter : Integrable
      (fun z : Option (Fin p.K) ×
          FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) =>
        MixedAuxiliaryReward.oneRoundAuxiliaryReward auxiliaryReward
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) z.2)
      actualMeasure := by
    rw [hpush]
    exact FastRewardSliceLaw.integrable_liveRecordingFastPushforward_auxiliaryReward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      auxiliaryReward hgridBounds r.payload.assignment snapshot
  have hexpectation :
      (∫ z : Option (Fin p.K) ×
          FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment),
        MixedAuxiliaryReward.oneRoundAuxiliaryReward auxiliaryReward
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) z.2
        ∂ actualMeasure) =
      ∑ j : FastArm (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment),
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
          r.payload.anchor W r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) j *
          MixedAuxiliaryReward.oneRoundAuxiliaryReward auxiliaryReward
            (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment) j := by
    rw [hpush]
    exact FastRewardSliceLaw.liveRecordingFastPushforward_integral_auxiliaryReward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      auxiliaryReward r.payload.assignment snapshot
  exact ⟨hactualMeasurable, hpush, hfixedFamilies, hfst, hsnd, hsome, hnone,
    hinter, by simpa only [auxiliaryReward] using hexpectation⟩

/-- The actual source-launch specialization of the whole-control pair law.

It retains the selected original source row and every visible launch condition
from `actualLaunchedBoundary_physical_fast_pair_eq`. The nested continuing-live
conditions are the same operational telescope as the prefix theorem above. -/
theorem actual_launched_boundary_joint_pushforward
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated
      source rewards C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate) b h i)
    (hclean : ∀ i,
      ∀ hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate)
          b h).uninformed,
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i,
          hi⟩ (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T) :
    let initial := ReferenceContinuingDataCandidateLogging.actualLaunchState source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active := ReferenceContinuingDataCandidateLogging.actualLaunch_allActiveAtStart
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let x := candidateInput initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
    ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (henabled : x.time.val + 1 < d.startResult.clock.g),
    let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
    let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
      r q base x.time d states
    let actualPair :=
      ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
        initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start count span active r.payload true W
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
    let actualMeasure := (ContinuousLearningRows.timeControlLaw p).map actualPair
    Measurable actualPair ∧
    actualMeasure = FastRewardSliceLaw.liveRecordingFastPushforward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot ∧
    (∀ family : ContinuousLearningRows.AffineSamples p,
      Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
        actualPair (slice, family)) ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actualPair (slice, family)) =
        FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot) := by
  classical
  intro initial start active x r q base d hs c a hc states memories ho henabled
    W snapshot actualPair actualMeasure
  have hlaunchPair :=
    ReferenceContinuingRecordingFastPair.actualLaunchedBoundary_physical_fast_pair_eq
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched count span
  dsimp only at hlaunchPair
  have hprefix := hlaunchPair r q base d hs c a hc states memories ho henabled
  let canonicalPair := FastRewardSliceLaw.liveRecordingFastPair
    p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
    r.payload.anchor_pos
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid)
    r.payload.assignment snapshot
  have hpoint : ∀ u : ContinuousLearningRows.TimeControl p,
      actualPair u = canonicalPair u.1 := by
    intro u
    simpa only [actualPair, canonicalPair,
      FastRewardSliceLaw.liveRecordingFastPair] using hprefix u
  have hpairEq : actualPair = fun u : ContinuousLearningRows.TimeControl p =>
      canonicalPair u.1 := funext hpoint
  have hcanonicalMeasurable : Measurable canonicalPair :=
    FastRewardSliceLaw.measurable_liveRecordingFastPair p rate.eta.val rate.eta.property
      rate.sourceCap r.payload.anchor W r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot
  have hactualMeasurable : Measurable actualPair := by
    rw [hpairEq]
    exact hcanonicalMeasurable.comp measurable_fst
  have hpush : actualMeasure = FastRewardSliceLaw.liveRecordingFastPushforward
      p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      r.payload.assignment snapshot := by
    dsimp only [actualMeasure]
    calc
      (ContinuousLearningRows.timeControlLaw p).map actualPair =
          (ContinuousLearningRows.timeControlLaw p).map
            (fun u : ContinuousLearningRows.TimeControl p => canonicalPair u.1) := by
        rw [hpairEq]
      _ = ((ContinuousLearningRows.timeControlLaw p).map Prod.fst).map canonicalPair := by
        symm
        exact Measure.map_map hcanonicalMeasurable measurable_fst
      _ = (ContinuousControlSlice.sliceLaw p.m p.K).map canonicalPair := by
        rw [ContinuousLearningRows.map_slice p]
      _ = FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot := rfl
  have hfixedFamilies : ∀ family : ContinuousLearningRows.AffineSamples p,
      Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
        actualPair (slice, family)) ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actualPair (slice, family)) =
        FastRewardSliceLaw.liveRecordingFastPushforward
          p rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          r.payload.assignment snapshot := by
    intro family
    have hfixed :=
      ReferenceContinuingRecordingFastPair.fixedFamily_joint_pushforward_of_identity
        actualPair canonicalPair hcanonicalMeasurable hpoint family
    simpa only [FastRewardSliceLaw.liveRecordingFastPushforward] using hfixed
  exact ⟨hactualMeasurable, hpush, hfixedFamilies⟩

end Bandits.Support.ReferenceContinuingRecordingFastLaw

end
