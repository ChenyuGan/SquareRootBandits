/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchPreparationMeasurability
public import Bandits.Support.OrdinaryCoordinatorObservationMeasurability

/-!
# One actual mixed postlaunch step and its successor

The domain and both storage spaces are exactly those of
`ActualPostlaunchPreparationMeasurability`. The coordinator observes its own
entry of the actual simultaneous physical feedback. Every heterogeneous
follower observes its own entry, using its original source and retained
cursor state, including its own bootstrap or declared row and dagger branch.

The whole-step code retains the existing preparation/feedback code, the
ordinary coordinator's complete collection-tail observation code, and every
existing follower local code. Its successor readout only projects retained
coordinates. The reconstruction theorems identify all data fields of the
existing `RoundResult` and the entire next state; its other fields are proofs.
No dispatcher, preparation, observation or step is run by a storage decoder.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

The named consumers are actual mixed within-block iteration and an eventual
whole-history Borel construction using these same storage encodings. This is
one internal step only: boundary/launch transport, history laws, reference
coupling, source queue laws, probability and regret remain separate producers.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActualPostlaunchPhysicalStep

namespace Bandits.Support.ActualPostlaunchStepMeasurability

abbrev Parameters := ActualPostlaunchPhysicalStep.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}
  {block : Fin (n_boot p)} {cursor : Nat}

/-- The accepted ordinary observer at the original selected complete row,
actual coordinator storage/bank/time, and its own physical feedback entry. -/
def coordinatorObservationCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  OrdinaryCoordinatorObservationMeasurability.observeLocalCode
    (ActualPostlaunchPreparationMeasurability.coordinatorInput input,
      physicalFeedback (prepare input) (ActiveRoundActions.coordinator p.two_le_m))

theorem measurable_coordinatorObservationCode : Measurable
    (coordinatorObservationCode (p := p) (rate := rate)
      (block := block) (cursor := cursor)) := by
  exact OrdinaryCoordinatorObservationMeasurability.measurable_observeLocalCode.comp
    (ActualPostlaunchPreparationMeasurability.measurable_coordinatorInput.prodMk
      ((measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
        ActualPostlaunchPreparationMeasurability.measurable_physicalFeedback))

/-- The whole existing observation is encoded, including failure, recording,
the returned UP bank, and the full optional reception diagnostic. -/
theorem coordinatorObservationCode_eq_encode_step
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    coordinatorObservationCode input =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (step input).coordinatorObservation := by
  unfold coordinatorObservationCode
    OrdinaryCoordinatorObservationMeasurability.observeLocalCode
  rw [ActualPostlaunchPreparationMeasurability.coordinator_cut_eq_prepare]
  rfl

/-- Full observation equality, rather than only configuration/arm agreement. -/
theorem decode_coordinatorObservationCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      (coordinatorObservationCode input) = (step input).coordinatorObservation := by
  unfold coordinatorObservationCode
  rw [OrdinaryCoordinatorObservationMeasurability.decode_observeLocalCode,
    ActualPostlaunchPreparationMeasurability.coordinator_cut_eq_prepare]
  rfl

/-- This follower's original source, cursor-restricted state and actual own
feedback. No observer receives the preparation-only zero feedback coordinate. -/
def followerInput (i : Fin (p.m - 1))
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualPostlaunchFollowerMeasurability.LocalInput (rate := rate) block cursor :=
  (input.source,
    (ActualPostlaunchPreparationMeasurability.cursorFollower i input,
      physicalFeedback (prepare input)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)))

theorem measurable_followerInput (i : Fin (p.m - 1)) : Measurable
    (followerInput (p := p) (rate := rate) (block := block) (cursor := cursor) i) :=
  ActualPostlaunchPreparationMeasurability.measurable_inputSource.prodMk
    ((ActualPostlaunchPreparationMeasurability.measurable_cursorFollower i).prodMk
      ((measurable_pi_apply (PublicDiscreteDraws.followerPlayer p.two_le_m i)).comp
        ActualPostlaunchPreparationMeasurability.measurable_physicalFeedback))

/-- The existing complete local code, retaining preparation, raw observation
tags and the actual successor with all original saved-real coordinates. -/
def followerLocalCode (i : Fin (p.m - 1))
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualPostlaunchFollowerMeasurability.LocalCode (rate := rate) block :=
  ActualPostlaunchFollowerMeasurability.localCodeOnCursor input.cursor_lt i
    (followerInput i input)

/-- The accepted joint cursor theorem is composed with the actual original
source, cursor-follower and own physical feedback map proved measurable above. -/
theorem measurable_followerLocalCode (i : Fin (p.m - 1)) : Measurable
    (followerLocalCode (p := p) (rate := rate) (block := block) (cursor := cursor) i) := by
  by_cases hcursor : cursor < BootstrapObservedFollower.blockLength p block
  · change Measurable (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor i
        (followerInput i input))
    exact (ActualPostlaunchFollowerMeasurability.measurable_localCodeOnCursor
      (rate := rate) hcursor i).comp (measurable_followerInput i)
  · let : IsEmpty (PhysicalInput (p := p) (rate := rate) block cursor) :=
      ⟨fun input => hcursor input.cursor_lt⟩
    exact Subsingleton.measurable

/-- Only preparation is independent of feedback. The observation and successor
parts of this code still use the actual physical feedback. -/
theorem followerLocalCode_preparation
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    (followerLocalCode i input).1 =
      ActualPostlaunchPreparationMeasurability.followerPreparationCode i input :=
  (ActualPostlaunchPreparationMeasurability.followerPreparationCode_eq_at_feedback
    input i (physicalFeedback (prepare input)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))).symm

/-- The retained code decodes to the exact actual follower outcome, including
its entire prepared component and its entire heterogeneous next state. -/
theorem decode_followerLocalCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualPostlaunchFollowerMeasurability.decodeLocalCode input.source input.time i
      (followerLocalCode i input) = some ((step input).followers i) :=
  ActualPostlaunchFollowerMeasurability.decode_localCode_eq_actual_physical_outcome
    input i

/-- The literal observer consumes this same own physical feedback, and its
output is the follower outcome reconstructed by the retained code. -/
theorem follower_observation_eq_step
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.observeFollower rate block input.time input.source i
      ((step input).prepared.followers i)
      (physicalFeedback (step input).prepared
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      .ok ((step input).followers i) :=
  followerOutcome_eq_observe (prepare input) i

/-- Decode the successor coordinate of the SAME local code to the exact next
follower. This uses full outcome reconstruction, not an assumed queue law. -/
theorem followerLocalCode_next
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block
      (followerLocalCode i input).2.2 = ((step input).followers i).next := by
  have hdecode := decode_followerLocalCode input i
  have hprepared : ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
      (rate := rate) i input.source input.time (followerLocalCode i input).1 =
      some ((prepare input).followers i) := by
    rw [followerLocalCode_preparation]
    exact ActualPostlaunchPreparationMeasurability.decode_followerPreparationCode input i
  unfold ActualPostlaunchFollowerMeasurability.decodeLocalCode at hdecode
  rw [hprepared] at hdecode
  have houtcome :
      (⟨(prepare input).followers i,
        ActualInitializationRoundMeasurability.followerStateOfCode p rate block
          (followerLocalCode i input).2.2⟩ :
        ActualInitializationPhysicalStep.FollowerOutcome p rate block) =
        (step input).followers i := Option.some.inj hdecode
  exact congrArg ActualInitializationPhysicalStep.FollowerOutcome.next houtcome

/-- Re-encoding preserves the exact retained successor code. The admitted
codec identity covers both saved-real scalars at every buffer position. -/
theorem encode_nextFollower_eq
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      ((step input).followers i).next = (followerLocalCode i input).2.2 := by
  rw [← followerLocalCode_next input i]
  exact ActualInitializationCursorMeasurability.followerCodeOfState_decode _

/-- Existing code carriers only: full preparation/feedback, full coordinator
observation, and the finite family of full heterogeneous follower local codes. -/
abbrev StepCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualPostlaunchPreparationMeasurability.PreparationFeedbackCode p rate block ×
    (ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate ×
      (Fin (p.m - 1) → ActualPostlaunchFollowerMeasurability.LocalCode
        (rate := rate) block))

/-- This is the inherited product of the accepted code spaces. -/
@[instance_reducible] instance stepCodeMeasurableSpace :
    MeasurableSpace (StepCode p rate block) :=
  MeasurableSpace.prod
    ActualPostlaunchPreparationMeasurability.preparationFeedbackCodeMeasurableSpace
    (MeasurableSpace.prod
      (inferInstance : MeasurableSpace
        (ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate))
      (inferInstance : MeasurableSpace
        (Fin (p.m - 1) → ActualPostlaunchFollowerMeasurability.LocalCode
          (rate := rate) block)))

def stepCode (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    StepCode p rate block :=
  (ActualPostlaunchPreparationMeasurability.preparationFeedbackCode input,
    (coordinatorObservationCode input, fun i => followerLocalCode i input))

/-- Unconditional whole-step Borel composition on the original joint source,
whole reward table and existing storage, with only its original typing fields. -/
theorem measurable_stepCode : Measurable
    (stepCode (p := p) (rate := rate) (block := block) (cursor := cursor)) :=
  ActualPostlaunchPreparationMeasurability.measurable_preparationFeedbackCode.prodMk
    (measurable_coordinatorObservationCode.prodMk
      (measurable_pi_iff.mpr fun i => measurable_followerLocalCode i))

/-- Only retained configuration, returned bank and follower successor
coordinates are read. There is no operational call or raw-code normalization. -/
def successorCoordinates (code : StepCode p rate block) :
    ActualPostlaunchPreparationMeasurability.StateCoordinates p rate block :=
  (code.2.1.1, (code.2.1.2.1, fun i => (code.2.2 i).2.2))

theorem measurable_successorCoordinates :
    Measurable (successorCoordinates (p := p) (rate := rate) (block := block)) :=
  measurable_snd.fst.fst.prodMk
    (measurable_snd.fst.snd.fst.prodMk
      (measurable_pi_iff.mpr fun i =>
        ((measurable_pi_apply i).comp measurable_snd.snd).snd.snd))

/-- The coordinator coordinate is the SAME canonical real-valued code used
by the existing storage encoder. -/
theorem encode_nextState_coordinator
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator
      (step input).nextState.coordinator = (stepCode input).2.1.1 := by
  change ReferenceActivePhysicalStepMeasurability.encodeCoordinator
    (step input).coordinatorObservation.configuration =
      (coordinatorObservationCode input).1
  rw [coordinatorObservationCode_eq_encode_step]
  rfl

/-- The returned bank, including observation failure/rejection paths, is
exactly the bank read from the full ordinary observation code. -/
theorem nextState_bank
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    (step input).nextState.upDecoderBank = (stepCode input).2.1.2.1 := by
  change (step input).coordinatorObservation.upDecoderBank =
    (coordinatorObservationCode input).2.1
  rw [coordinatorObservationCode_eq_encode_step]
  rfl

/-- Every follower retains its own row/activation/bootstrap or dagger branch
in the original successor storage encoding. -/
theorem encode_nextState_follower
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      ((step input).nextState.followers i) = ((stepCode input).2.2 i).2.2 :=
  encode_nextFollower_eq input i

/-- Pointwise reconstruction of all successor storage coordinates. -/
theorem encode_nextState
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualPostlaunchPreparationMeasurability.encodeState (step input).nextState =
      successorCoordinates (stepCode input) :=
  Prod.ext (encode_nextState_coordinator input)
    (Prod.ext (nextState_bank input) (funext (encode_nextState_follower input)))

/-- Full next-state equality in the original indexed storage carrier. Image
membership supplies typing proofs only; the existing decoder reads the code. -/
theorem decode_successorCoordinates
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualPostlaunchPreparationMeasurability.decodeState
      ⟨successorCoordinates (stepCode input),
        ⟨(step input).nextState, encode_nextState input⟩⟩ =
      (step input).nextState := by
  have hcode :
      (⟨successorCoordinates (stepCode input),
        ⟨(step input).nextState, encode_nextState input⟩⟩ :
        Set.range (ActualPostlaunchPreparationMeasurability.encodeState
          (p := p) (rate := rate) (block := block) (cursor := cursor + 1))) =
      ⟨ActualPostlaunchPreparationMeasurability.encodeState (step input).nextState,
        ⟨(step input).nextState, rfl⟩⟩ :=
    Subtype.ext (encode_nextState input).symm
  rw [hcode, ActualPostlaunchPreparationMeasurability.decode_encodeState]

/-- The actual successor is Borel in P's SAME storage space at cursor + 1.
There is no common-row, success, clock-alignment or measurable-operation input. -/
theorem measurable_nextState : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (step input).nextState) := by
  apply measurable_comap_iff.mpr
  have heq :
      (ActualPostlaunchPreparationMeasurability.encodeState ∘
        (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
          (step input).nextState)) =
      successorCoordinates ∘ stepCode := funext encode_nextState
  rw [heq]
  exact measurable_successorCoordinates.comp measurable_stepCode

/-- All data fields of the existing dependent `RoundResult`, its simultaneous
actions/feedback and its full successor are reconstructed pointwise. The
remaining result/preparation fields are Prop witnesses, hence proof irrelevant.
No separate dependent operational decoder is introduced. -/
theorem stepCode_reconstructs
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode
        (ActualPostlaunchPreparationMeasurability.coordinatorInput input)
        (stepCode input).1.1.1.2 rfl = (step input).prepared.coordinator ∧
      (∀ i, ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
        (rate := rate) i input.source input.time ((stepCode input).1.1.2 i) =
        some ((step input).prepared.followers i)) ∧
      (stepCode input).1.2.1 = actionProfile (step input).prepared ∧
      (stepCode input).1.2.2 = physicalFeedback (step input).prepared ∧
      ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (stepCode input).2.1 = (step input).coordinatorObservation ∧
      (∀ i, ActualPostlaunchFollowerMeasurability.decodeLocalCode
        input.source input.time i ((stepCode input).2.2 i) =
        some ((step input).followers i)) ∧
      ActualPostlaunchPreparationMeasurability.decodeState
        ⟨successorCoordinates (stepCode input),
          ⟨(step input).nextState, encode_nextState input⟩⟩ =
        (step input).nextState :=
  ⟨ActualPostlaunchPreparationMeasurability.decode_coordinatorPreparationCode input,
    ActualPostlaunchPreparationMeasurability.decode_followerPreparationCode input,
    rfl, rfl, decode_coordinatorObservationCode input, decode_followerLocalCode input,
    decode_successorCoordinates input⟩

end Bandits.Support.ActualPostlaunchStepMeasurability

end
