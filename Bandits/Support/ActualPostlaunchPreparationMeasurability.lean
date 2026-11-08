/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchFollowerMeasurability
public import Bandits.Support.OrdinaryCoordinatorPreparationSelectionMeasurability
public import Bandits.Support.OrdinaryCoordinatorPreparationReconstruction

/-!
# Actual mixed postlaunch storage, preparation and physical feedback

The sole storage encoding below retains the existing coordinator, UP bank,
and every heterogeneous follower. The input encoding additionally retains the
original whole source and reward table. Its measurable spaces are pullbacks
of the inherited product Borel spaces. Image decoders restore only original
storage and typing proofs; they perform no local operation.

Preparation uses the ordinary coordinator's selected complete row and each
follower's own retained state. All actual arms are joined before physical
collision feedback is computed. This module constructs neither an observer
nor a whole-step/successor code. Its intended consumer is
`ActualPostlaunchStepMeasurability`.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
These are internal local measurability results, not manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActualPostlaunchPhysicalStep

namespace Bandits.Support.ActualPostlaunchPreparationMeasurability

abbrev Parameters := ActualPostlaunchPhysicalStep.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}
  {block : Fin (n_boot p)} {cursor : Nat}

/-- Literal storage coordinates, with all original saved-real follower fibres
and coordinator anchors retained by the admitted encoders. -/
abbrev StateCoordinates (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
    (CoordinatorUpReception.UpDecoderBank p ×
      (Fin (p.m - 1) → ActualInitializationRoundMeasurability.FollowerCode p rate block))

/-- No observer or transition is part of the storage encoding. -/
def encodeState (state : PostlaunchState (p := p) (rate := rate) block cursor) :
    StateCoordinates p rate block :=
  (ReferenceActivePhysicalStepMeasurability.encodeCoordinator state.coordinator,
    (state.upDecoderBank, fun i =>
      ActualInitializationRoundMeasurability.followerCodeOfState p rate block
        (state.followers i)))

/-- Decode on the actual image. The image certificate supplies only the
cursor invariant; every data field is decoded from its retained coordinate. -/
def decodeState (code : Set.range
    (encodeState (p := p) (rate := rate) (block := block) (cursor := cursor))) :
    PostlaunchState (p := p) (rate := rate) block cursor where
  coordinator := ReferenceActivePhysicalStepMeasurability.decodeCoordinator code.1.1
  upDecoderBank := code.1.2.1
  followers := fun i =>
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block (code.1.2.2 i)
  followers_at_cursor := by
    intro i
    obtain ⟨state, hstate⟩ := code.2
    have hi := congrArg (fun z : StateCoordinates p rate block => z.2.2 i) hstate
    rw [← hi]
    exact (ActualInitializationRoundMeasurability.followerStateOfCode_encode
      p rate block (state.followers i)) ▸ state.followers_at_cursor i

/-- Readiness proof fields are irrelevant to exact storage reconstruction. -/
theorem decode_encodeState
    (state : PostlaunchState (p := p) (rate := rate) block cursor) :
    decodeState ⟨encodeState state, ⟨state, rfl⟩⟩ = state := by
  have hf : (fun i => ActualInitializationRoundMeasurability.followerStateOfCode
      p rate block (ActualInitializationRoundMeasurability.followerCodeOfState
        p rate block (state.followers i))) = state.followers := by
    funext i
    exact ActualInitializationRoundMeasurability.followerStateOfCode_encode
      p rate block (state.followers i)
  cases state
  simp only [decodeState, encodeState,
    ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator, hf]

theorem encodeState_injective : Function.Injective
    (encodeState (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  intro a b hab
  have hcode : (⟨encodeState a, ⟨a, rfl⟩⟩ : Set.range
      (encodeState (p := p) (rate := rate) (block := block) (cursor := cursor))) =
      ⟨encodeState b, ⟨b, rfl⟩⟩ := Subtype.ext hab
  simpa only [decode_encodeState] using congrArg decodeState hcode

instance postlaunchStateMeasurableSpace :
    MeasurableSpace (PostlaunchState (p := p) (rate := rate) block cursor) :=
  MeasurableSpace.comap encodeState inferInstance

theorem measurable_encodeState : Measurable
    (encodeState (p := p) (rate := rate) (block := block) (cursor := cursor)) :=
  comap_measurable _

theorem measurable_stateCoordinatorCode : Measurable
    (fun state : PostlaunchState (p := p) (rate := rate) block cursor =>
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator state.coordinator) :=
  measurable_fst.comp measurable_encodeState

theorem measurable_stateBank : Measurable
    (fun state : PostlaunchState (p := p) (rate := rate) block cursor =>
      state.upDecoderBank) :=
  measurable_fst.comp (measurable_snd.comp measurable_encodeState)

theorem measurable_stateFollower (i : Fin (p.m - 1)) : Measurable
    (fun state : PostlaunchState (p := p) (rate := rate) block cursor =>
      state.followers i) := by
  apply measurable_comap_iff.mpr
  exact (measurable_pi_apply i).comp
    (measurable_snd.comp (measurable_snd.comp measurable_encodeState))

theorem measurable_decodeState : Measurable
    (decodeState (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  apply measurable_comap_iff.mpr
  have heq : (fun code : Set.range
      (encodeState (p := p) (rate := rate) (block := block) (cursor := cursor)) =>
      encodeState (decodeState code)) = Subtype.val := by
    funext code
    rcases code with ⟨raw, state, rfl⟩
    rw [decode_encodeState]
  rw [show encodeState ∘ decodeState = _ from heq]
  exact measurable_subtype_coe

/-- Whole original public/private source, whole rewards, and storage. -/
abbrev InputCoordinates (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualPostlaunchPhysicalStep.SourceInput p ×
    (ActualPostlaunchPhysicalStep.GridRewardTable p × StateCoordinates p rate block)

/-- Explicit inherited product instances keep typeclass search shallow. -/
@[instance_reducible] instance inputCoordinatesMeasurableSpace :
    MeasurableSpace (InputCoordinates p rate block) :=
  MeasurableSpace.prod
    (ActualInitializationRoundMeasurability.roundSourceMeasurableSpace p)
    (MeasurableSpace.prod
      (ActualInitializationRoundMeasurability.roundRewardMeasurableSpace p)
      (inferInstance : MeasurableSpace (StateCoordinates p rate block)))

def encodeInput (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    InputCoordinates p rate block :=
  (input.source, (input.rewards, encodeState input.state))

/-- Input decoding is restricted to the actual image and retains its cursor
bound. No arbitrary raw product is normalized or given fallback storage. -/
def decodeInput (code : Set.range
    (encodeInput (p := p) (rate := rate) (block := block) (cursor := cursor))) :
    PhysicalInput (p := p) (rate := rate) block cursor where
  source := code.1.1
  rewards := code.1.2.1
  state := decodeState ⟨code.1.2.2, by
    obtain ⟨input, hinput⟩ := code.2
    exact ⟨input.state, congrArg (fun z : InputCoordinates p rate block => z.2.2) hinput⟩⟩
  cursor_lt := by
    obtain ⟨input, _⟩ := code.2
    exact input.cursor_lt

theorem decode_encodeInput
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    decodeInput ⟨encodeInput input, ⟨input, rfl⟩⟩ = input := by
  cases input
  simp only [decodeInput, encodeInput, decode_encodeState]

theorem encodeInput_injective : Function.Injective
    (encodeInput (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  intro a b hab
  have hcode : (⟨encodeInput a, ⟨a, rfl⟩⟩ : Set.range
      (encodeInput (p := p) (rate := rate) (block := block) (cursor := cursor))) =
      ⟨encodeInput b, ⟨b, rfl⟩⟩ := Subtype.ext hab
  simpa only [decode_encodeInput] using congrArg decodeInput hcode

instance physicalInputMeasurableSpace :
    MeasurableSpace (PhysicalInput (p := p) (rate := rate) block cursor) :=
  MeasurableSpace.comap encodeInput inferInstance

theorem measurable_encodeInput : Measurable
    (encodeInput (p := p) (rate := rate) (block := block) (cursor := cursor)) :=
  comap_measurable _

theorem measurable_inputSource : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor => input.source) :=
  measurable_fst.comp measurable_encodeInput

theorem measurable_inputRewards : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor => input.rewards) :=
  measurable_fst.comp (measurable_snd.comp measurable_encodeInput)

theorem measurable_inputState : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor => input.state) := by
  apply measurable_comap_iff.mpr
  exact measurable_snd.comp (measurable_snd.comp measurable_encodeInput)

theorem measurable_decodeInput : Measurable
    (decodeInput (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  apply measurable_comap_iff.mpr
  have heq : (fun code : Set.range
      (encodeInput (p := p) (rate := rate) (block := block) (cursor := cursor)) =>
      encodeInput (decodeInput code)) = Subtype.val := by
    funext code
    rcases code with ⟨raw, input, rfl⟩
    rw [decode_encodeInput]
  rw [show encodeInput ∘ decodeInput = _ from heq]
  exact measurable_subtype_coe

/-- Time is fixed by the clipped block and cursor; its bound is supplied by
the input's own typing field. -/
theorem measurable_inputTime : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor => input.time) := by
  by_cases hcursor : cursor < BootstrapObservedFollower.blockLength p block
  · have heq : (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
        input.time) = fun _ => ActualInitializationRun.blockTime p block cursor hcursor := rfl
    rw [heq]
    exact measurable_const
  · let : IsEmpty (PhysicalInput (p := p) (rate := rate) block cursor) :=
      ⟨fun input => hcursor input.cursor_lt⟩
    exact Subsingleton.measurable

/-- Each original follower is mapped to the inherited cursor subtype. -/
def cursorFollower (i : Fin (p.m - 1))
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualPostlaunchFollowerMeasurability.CursorFollowerInput (rate := rate) block cursor :=
  ⟨input.state.followers i, input.state.followers_at_cursor i⟩

theorem measurable_cursorFollower (i : Fin (p.m - 1)) : Measurable
    (cursorFollower (p := p) (rate := rate) (block := block) (cursor := cursor) i) :=
  ((measurable_stateFollower i).comp measurable_inputState).subtype_mk

/-- The original coordinator product uses the selected COMPLETE row, the
actual encoded coordinator and bank, and the clipped-block calendar time. -/
def coordinatorInput (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    OrdinaryCoordinatorLocalMeasurability.LocalInput p rate :=
  (ReferenceActivePhysicalStepMeasurability.encodeCoordinator input.state.coordinator,
    (input.state.upDecoderBank,
      (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source),
        input.time)))

theorem measurable_coordinatorInput : Measurable
    (coordinatorInput (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  have hrows := (ActualBootstrapObservationCode.measurable_sourceRows p).comp
    (measurable_inputSource (rate := rate) (block := block) (cursor := cursor))
  have hindex := (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
    (measurable_inputSource (rate := rate) (block := block) (cursor := cursor))
  have hrow := (ActualPostlaunchFollowerMeasurability.measurable_evalCompleteRows_local p).comp
    (hrows.prodMk hindex)
  exact (measurable_stateCoordinatorCode.comp measurable_inputState).prodMk
    ((measurable_stateBank.comp measurable_inputState).prodMk
      (hrow.prodMk measurable_inputTime))

/-- The lossless coordinator decoder recovers the same actual preparation. -/
theorem coordinator_cut_eq_prepare
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    OrdinaryCoordinatorLocalMeasurability.cut (coordinatorInput input) =
      (prepare input).coordinator := by
  change OrdinaryCoordinatorPhysicalInterface.prepareLocal
      (ReferenceActivePhysicalStepMeasurability.decodeCoordinator
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator input.state.coordinator))
      input.state.upDecoderBank
      (input.source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.source))
      input.time = _
  rw [ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator]
  rfl

/-- This inherited countable coordinate contains clock/result data, never a
continuous weight or anchor. It is the same space used by the selection API. -/
local instance startRoundResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

theorem measurable_coordinatorArm : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (prepare input).coordinator.arm) := by
  have h : Measurable (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (OrdinaryCoordinatorLocalMeasurability.cut (coordinatorInput input)).arm) :=
    OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_prepareLocalArm.comp
      (measurable_coordinatorInput (rate := rate) (block := block) (cursor := cursor))
  have heq : (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (OrdinaryCoordinatorLocalMeasurability.cut (coordinatorInput input)).arm) =
      (fun input => (prepare input).coordinator.arm) := by
    funext input
    rw [coordinator_cut_eq_prepare]
    rfl
  rw [← heq]
  exact h

theorem measurable_coordinatorSelectionData : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData
        (prepare input).coordinator) := by
  have h : Measurable (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      OrdinaryCoordinatorPreparationSelectionMeasurability.prepareLocalSelectionData
        (coordinatorInput input)) :=
    OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_prepareLocalSelectionData.comp
      (measurable_coordinatorInput (rate := rate) (block := block) (cursor := cursor))
  have heq : (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      OrdinaryCoordinatorPreparationSelectionMeasurability.prepareLocalSelectionData
        (coordinatorInput input)) =
      (fun input => OrdinaryCoordinatorPreparationSelectionMeasurability.preparationSelectionData
        (prepare input).coordinator) := by
    funext input
    rw [OrdinaryCoordinatorPreparationSelectionMeasurability.prepareLocalSelectionData_eq_actualCut,
      coordinator_cut_eq_prepare]
    rfl
  rw [← heq]
  exact h

theorem measurable_coordinatorDownView : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (prepare input).coordinator.downView) := by
  have h : Measurable (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (OrdinaryCoordinatorLocalMeasurability.cut (coordinatorInput input)).downView) :=
    OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_prepareLocalDownView.comp
      (measurable_coordinatorInput (rate := rate) (block := block) (cursor := cursor))
  have heq : (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      (OrdinaryCoordinatorLocalMeasurability.cut (coordinatorInput input)).downView) =
      (fun input => (prepare input).coordinator.downView) := by
    funext input
    rw [coordinator_cut_eq_prepare]
    rfl
  rw [← heq]
  exact h

/-- Explicit preparation independence: changing the unused own-feedback slot
leaves the entire prepared code unchanged, on either heterogeneous branch. -/
theorem preparedCodeOnCursor_feedback_independent
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : ActualPostlaunchPhysicalStep.SourceInput p)
    (follower : ActualPostlaunchFollowerMeasurability.CursorFollowerInput
      (rate := rate) block cursor) (y y' : Fin (D p + 1)) :
    ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor i (source, (follower, y)) =
      ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor i
        (source, (follower, y')) := by
  rfl

/-- Only the PREPARE producer is projected at zero. No observer is evaluated
at that value; the physical feedback below comes from the full actual profile. -/
def followerPreparationCode (i : Fin (p.m - 1))
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block :=
  ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor input.cursor_lt i
    (input.source, (cursorFollower i input, 0))

theorem followerPreparationCode_eq_at_feedback
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) (ownY : Fin (D p + 1)) :
    followerPreparationCode i input =
      ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor input.cursor_lt i
        (input.source, (cursorFollower i input, ownY)) :=
  preparedCodeOnCursor_feedback_independent input.cursor_lt i input.source
    (cursorFollower i input) 0 ownY

theorem measurable_followerPreparationCode (i : Fin (p.m - 1)) : Measurable
    (followerPreparationCode (p := p) (rate := rate) (block := block) (cursor := cursor) i) := by
  by_cases hcursor : cursor < BootstrapObservedFollower.blockLength p block
  · exact (ActualPostlaunchFollowerMeasurability.measurable_preparedCodeOnCursor
      (rate := rate) hcursor i).comp
        (measurable_inputSource.prodMk ((measurable_cursorFollower i).prodMk measurable_const))
  · let : IsEmpty (PhysicalInput (p := p) (rate := rate) block cursor) :=
      ⟨fun input => hcursor input.cursor_lt⟩
    exact Subsingleton.measurable

/-- Decode the complete follower preparation at the SAME original source
and derived time. Readiness witnesses agree by proof irrelevance. -/
theorem decode_followerPreparationCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
      (rate := rate) i input.source input.time (followerPreparationCode i input) =
      some ((prepare input).followers i) := by
  have h := ActualPostlaunchFollowerMeasurability.decode_preparedCodeOnCursor
    (rate := rate) input.cursor_lt i input.source (input.state.followers i)
    (input.state.followers_at_cursor i) 0
  have heq := prepareFollowerValid_eq_of_follower_eq input.time input.source i
    (input.state.followers i) (input.state.followers i) rfl
    (ActualPostlaunchFollowerMeasurability.follower_ready_of_cursor
      input.cursor_lt (cursorFollower i input)) (follower_ready_at_time input i)
  exact h.trans (congrArg some heq)

/-- Conditional readout helper. Its sole logical input is the displayed
decoder equality; the actual producer discharges it in the theorem below. -/
theorem preparedFollowerCodeArm_eq_of_decode
    (i : Fin (p.m - 1)) (source : ActualPostlaunchPhysicalStep.SourceInput p)
    (time : Fin p.T)
    (code : ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block)
    (prepared : ActualInitializationPhysicalStep.PreparedFollower p rate block)
    (hdecode : ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
      (rate := rate) i source time code = some prepared) :
    ActualInitializationPreparationMeasurability.preparedFollowerCodeArm code =
      prepared.arm := by
  cases code with
  | inl fields =>
      rcases fields with ⟨state, arm⟩
      simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
        Option.some.injEq] at hdecode
      cases hdecode
      rfl
  | inr fields =>
      rcases fields with ⟨rowIndex, activation, arm, incoming⟩
      by_cases hvalid : activation.val ≤ time.val + 1
      · simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
          dite_eq_left hvalid, Option.some.injEq] at hdecode
        cases hdecode
        rfl
      · simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
          dite_eq_right hvalid] at hdecode
        cases hdecode

theorem followerPreparationCode_arm
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (i : Fin (p.m - 1)) :
    ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
      (followerPreparationCode i input) = ((prepare input).followers i).arm :=
  preparedFollowerCodeArm_eq_of_decode i input.source input.time
    (followerPreparationCode i input) ((prepare input).followers i)
    (decode_followerPreparationCode input i)

theorem measurable_followerArm (i : Fin (p.m - 1)) : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      ((prepare input).followers i).arm) := by
  have h := ActualInitializationPreparationMeasurability.measurable_preparedFollowerCodeArm.comp
    (measurable_followerPreparationCode (rate := rate) (block := block) (cursor := cursor) i)
  simpa only [Function.comp_def, followerPreparationCode_arm] using h

/-- Existing coordinator retained-preparation code and every existing
heterogeneous follower code. All raw coordinator outcome tags survive. -/
abbrev PreparationCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate ×
    (Fin (p.m - 1) →
      ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block)

/-- The coordinator code inherits exactly its existing input/observation
product. No space is assigned to the dependent preparation object itself. -/
@[instance_reducible] def coordinatorPreparationCodeMeasurableSpace :
    MeasurableSpace (OrdinaryCoordinatorLocalMeasurability.PreparationCode p rate) :=
  OrdinaryCoordinatorLocalMeasurability.preparationCodeMeasurableSpace

@[instance_reducible] instance preparationCodeMeasurableSpace :
    MeasurableSpace (PreparationCode p rate block) :=
  MeasurableSpace.prod coordinatorPreparationCodeMeasurableSpace
    (inferInstance : MeasurableSpace (Fin (p.m - 1) →
      ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block))

def prepareCode (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    PreparationCode p rate block :=
  (OrdinaryCoordinatorLocalMeasurability.prepareLocalCode (coordinatorInput input),
    fun i => followerPreparationCode i input)

theorem measurable_prepareCode : Measurable
    (prepareCode (p := p) (rate := rate) (block := block) (cursor := cursor)) := by
  have hc : @Measurable _ _
      (physicalInputMeasurableSpace (p := p) (rate := rate) (block := block) (cursor := cursor))
      (coordinatorPreparationCodeMeasurableSpace (p := p) (rate := rate))
      (fun input => OrdinaryCoordinatorLocalMeasurability.prepareLocalCode
        (coordinatorInput input)) :=
    OrdinaryCoordinatorLocalMeasurability.measurable_prepareLocalCode.comp
      (measurable_coordinatorInput (p := p) (rate := rate) (block := block) (cursor := cursor))
  exact hc.prodMk (measurable_pi_iff.mpr fun i => measurable_followerPreparationCode i)

/-- Restore the retained coordinator preparation, without rerunning dispatch
or StartRound in this decoder. -/
theorem decode_coordinatorPreparationCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode
      (coordinatorInput input) (prepareCode input).1.2 rfl =
      (prepare input).coordinator := by
  exact (OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode_exact
    (coordinatorInput input)).trans (coordinator_cut_eq_prepare input)

/-- Joint literal reconstruction identifies every retained local preparation
with `prepare input`, at the same original source and actual calendar time. -/
theorem prepareCode_reconstructs
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    OrdinaryCoordinatorPreparationReconstruction.decode_prepareLocalCode
        (coordinatorInput input) (prepareCode input).1.2 rfl =
        (prepare input).coordinator ∧
      ∀ i, ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
        (rate := rate) i input.source input.time ((prepareCode input).2 i) =
        some ((prepare input).followers i) :=
  ⟨decode_coordinatorPreparationCode input, decode_followerPreparationCode input⟩

theorem measurable_actionProfile : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      actionProfile (prepare input)) := by
  apply measurable_pi_iff.mpr
  intro player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hp | ⟨i, hp⟩
  · subst player
    simpa only [actionProfile_coordinator] using
      (measurable_coordinatorArm (rate := rate) (block := block) (cursor := cursor))
  · subst player
    change Measurable (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      actionProfile (prepare input) (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    have heq : (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
        actionProfile (prepare input) (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        (fun input => ((prepare input).followers i).arm) := by
      funext input
      exact actionProfile_follower (prepare input) i
    rw [heq]
    exact measurable_followerArm i

/-- Finite physical feedback coordinates use the WHOLE original reward table
and the ONE complete actual simultaneous action profile. -/
def feedbackCoordinates (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    ReferenceActivePhysicalStepMeasurability.FeedbackCoordinates p :=
  (input.rewards, (input.time, actionProfile (prepare input)))

theorem measurable_feedbackCoordinates : Measurable
    (feedbackCoordinates (p := p) (rate := rate) (block := block) (cursor := cursor)) :=
  measurable_inputRewards.prodMk (measurable_inputTime.prodMk measurable_actionProfile)

/-- The finite grid primitive agrees with the actual collision rule for
EVERY player, without collision-freeness or a supplied feedback hypothesis. -/
theorem gridFeedback_eq_physical
    (input : PhysicalInput (p := p) (rate := rate) block cursor) (player : Fin p.m) :
    ReferenceActivePhysicalStepMeasurability.gridFeedback (feedbackCoordinates input) player =
      ActualPostlaunchPhysicalStep.gridFeedback (prepare input) player := by
  rfl

/-- Whole-vector equality with the SAME retained physical preparation. -/
theorem feedbackCoordinates_reconstructs
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    (fun player => ReferenceActivePhysicalStepMeasurability.gridFeedback
      (feedbackCoordinates input) player) = physicalFeedback (prepare input) := by
  funext player
  exact gridFeedback_eq_physical input player

theorem measurable_physicalFeedback : Measurable
    (fun input : PhysicalInput (p := p) (rate := rate) block cursor =>
      physicalFeedback (prepare input)) := by
  have h := ReferenceActivePhysicalStepMeasurability.measurable_gridFeedback.comp
    (measurable_feedbackCoordinates (rate := rate) (block := block) (cursor := cursor))
  simpa only [Function.comp_def, feedbackCoordinates_reconstructs] using h

/-- Both the local preparation codes and the entire simultaneous action and
collision-filtered feedback vectors, on the unconditional actual input root. -/
abbrev PreparationFeedbackCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  PreparationCode p rate block ×
    ((Fin p.m → Fin p.K) × (Fin p.m → Fin (D p + 1)))

@[instance_reducible] instance preparationFeedbackCodeMeasurableSpace :
    MeasurableSpace (PreparationFeedbackCode p rate block) :=
  MeasurableSpace.prod preparationCodeMeasurableSpace
    (inferInstance : MeasurableSpace ((Fin p.m → Fin p.K) × (Fin p.m → Fin (D p + 1))))

def preparationFeedbackCode
    (input : PhysicalInput (p := p) (rate := rate) block cursor) :
    PreparationFeedbackCode p rate block :=
  (prepareCode input, (actionProfile (prepare input), physicalFeedback (prepare input)))

theorem measurable_preparationFeedbackCode : Measurable
    (preparationFeedbackCode (p := p) (rate := rate) (block := block) (cursor := cursor)) :=
  measurable_prepareCode.prodMk (measurable_actionProfile.prodMk measurable_physicalFeedback)

end Bandits.Support.ActualPostlaunchPreparationMeasurability

end
