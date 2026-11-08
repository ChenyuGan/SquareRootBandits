/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation

/-!
# First-collection current FAST insertion

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-390`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The insertion preserves the complete round code and successor, collection
calls/readouts, strict-past numerical cells, and the actual first-collection
domain through the inserted date. These are deterministic internal results.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput)
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
  (replaceSourceControl_private replaceSourceControl_id replaceSourceControl_forward)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
  (actualRecord incoming sourcePrefix sourcePrefix_sourcePrefix incoming_factor actualLaunchBy
    actualLaunchBy_factor sourcePrefix_preserves_actual_launch actualRecord_eq_none_of_not_launchBy)
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrderedTupleSampler

namespace Bandits.Support.ReferenceFirstCollectionFastErasure

open ReferenceCollectionPhaseHistory (cutoffChosen laterChosen collectionWindow)
open ReferenceFirstLiveConfirmationHistory (firstLiveWindow)

open ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open CompletePublicTable (CompleteRow)
open ReferencePrelaunchFollower (Activation)
open ReferenceActivePhysicalHorizon (RoundRecord RoundEvidence)
open FollowerObservationStageMeasurabilityRepair (CarriedState assembleObservationInput
  observationInputCarriedState reconstructCarriedState representativeState loggingInputOfFiber
  fiberValues fiberRow fiberTime fiberFeedbackIndex fiberPlayedArm observationInputRow
  observationInputTime observationInputFeedbackIndex observationInputPlayedArm
  observationInputRow_assemble observationInputTime_assemble observationInputFeedbackIndex_assemble
  observationInputCarriedState_assemble serviceInputOfFiber)
open ReferenceFollowerTailComposition (recordObservable occupiedCode unoccupiedRecord occupiedRecord
  downCall finishFollowerObservable ordinaryObservable finishRecordResult observeFollowerObservable
  canonicalFollowerInput)
open ReferenceFollowerLoggingMeasurability (checkedLoggingObservable unoccupiedLoggingInputs
  LoggingObservable)

open ReferenceSourcePrefixHistoryFiltration (actualRecord_on_launch)
open ReferenceLaterCollectionArrivalReadout (laterCollectionReadout laterCollectionReadout_call
  laterCollectionReadout_domain laterCollectionCall preparedFollowersUnoccupied)
open ReferenceLaterLiveNumericalReadout (laterLiveDomain laterLiveReadout laterLiveReadout_eq_none_iff)
open ReferenceActiveHorizonMeasurability (roundRecordCode)
open ReferenceActivePhysicalStepMeasurability (encodeState decodeState decodeState_encodeState)
open ReferenceActiveStepCompositionMeasurability (followerObservable followerObservable_reconstruct
  wholeStepCode)
open ReferenceFirstLiveCoordinatorStepMeasurability (physicalCode)
open ReferenceCollectionPhaseHistory (CollectionPhase)

open ReferenceActiveDispatchTemporal (dispatchData tailArgs cutData CollectionArgs LiveArgs)
open ReferenceDownReception (ChoiceTimeView)
open CoordinatorLocalArmChoice (coordinatorArmChoiceCore coordinatorArmChoice currentDownHash
  assignmentIsLive ChoiceInputsValid cutoffRound sourceRound)
open FollowerPrepareJointMeasurability (prepareOutputOnInput assemblePrepareInput
  prepareOutputConfiguration prepareRoundCodeOnInput IncomingConfiguration ActiveCalendarTime
  incomingOfLocalConfiguration)
open FollowerLifecycleMeasurability (prepareRoundCodeAt localConfigurationOfCode localConfigurationCode
  PreparedRoundCode)
open ActiveFollowerQueueOperation (checkedUpOffer selectedUpRound)
open ActiveFollowerArmChoice (followerArmChoice followerArmChoiceCore_eq_of_same_local_draws)
open DeclaredFollowerLocalRound (releaseAndFinish LocalConfiguration)

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}
variable (rewards : GridRewardTable p) (C_star C_h : ℝ)

-- These notations expand to the original records, inputs and source suffix.
local notation "Record" => RoundRecord (p := p) (rate := rate)
local notation "Input" => RoundInput p rate
local notation "sourceRecords" z:max =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "sourceStart" z:max =>
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "collectionRecords" z:max =>
  collectionWindow (sourceRecords z) (List.length (firstLiveWindow (sourceRecords z)))

/-- Replace the `fast` coordinate in a time control while retaining its other
slice coordinates and its full affine-sample vector. -/
def replaceFastScalar (control : TimeControl p) (f : Scalar) : TimeControl p :=
  (Function.update control.1 Label.fast f, control.2)

/-- Insert `f` into the original selected row at the current date, using the
accepted fixed-time source-control coupling. All other source data is copied
by that coupling. -/
def insertCurrentFastScalar (t : Fin p.T) (source : SourceInput p) (f : Scalar) : SourceInput p :=
  ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source
    (replaceFastScalar ((source.1.2 (selectedRowIndex p source)).2 t) f)

/-- The source insertion preserves the private arrays, identifiers, selected
row's forward array, and all other rows. -/
theorem insertCurrentFastScalar_source_frames (t : Fin p.T) (source : SourceInput p) (f : Scalar) :
    (insertCurrentFastScalar t source f).2 = source.2 ∧
    (insertCurrentFastScalar t source f).1.1 = source.1.1 ∧
    selectedRowIndex p (insertCurrentFastScalar t source f) = selectedRowIndex p source ∧
    ((insertCurrentFastScalar t source f).1.2 (selectedRowIndex p source)).1 =
    (source.1.2 (selectedRowIndex p source)).1 ∧ (∀ q, q ≠ selectedRowIndex p source →
    (insertCurrentFastScalar t source f).1.2 q = source.1.2 q) := by
  exact ⟨replaceSourceControl_private p t source _, replaceSourceControl_id p t source _, rfl,
    replaceSourceControl_forward p t source _, fun q hq => Function.update_of_ne hq _ _⟩

/-- At the inserted date, every scalar except `fast` and the entire affine
sample vector retain their original values. -/
theorem insertCurrentFastScalar_control_frames (t : Fin p.T) (source : SourceInput p) (f : Scalar) :
    let J := selectedRowIndex p source
    (∀ label, label ≠ Label.fast → (((insertCurrentFastScalar t source f).1.2 J).2 t).1 label =
    ((source.1.2 J).2 t).1 label) ∧ (((insertCurrentFastScalar t source f).1.2 J).2 t).1
    Label.fast = f ∧
    (((insertCurrentFastScalar t source f).1.2 J).2 t).2 = ((source.1.2 J).2 t).2 ∧ (∀ v, v ≠ t →
    ((insertCurrentFastScalar t source f).1.2 J).2 v = (source.1.2 J).2 v) := by
  dsimp only [insertCurrentFastScalar]
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    replaceFastScalar, Function.update_self]
  exact ⟨fun label hlabel => Function.update_of_ne hlabel _ _, True.intro, True.intro,
    fun v hv => Function.update_of_ne hv _ _⟩

/-- The insertion cannot change the source prefix strictly before `t`. This
is the prefix domain used to reconstruct the actual pre-choice state. -/
theorem sourcePrefix_strictPast_insert_eq (control0 : TimeControl p) (t : Fin p.T)
    (source : SourceInput p) (f : Scalar) : sourcePrefix control0 t.val
    (insertCurrentFastScalar t source f) = sourcePrefix control0 t.val source := by
  exact ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t source _

/-- Actual incoming states agree at `t`, including when the actual record is
absent. The proof uses the strict source prefix, with no future endpoint. -/
theorem insertCurrentFastScalar_incoming_eq (control0 : TimeControl p)
    (t : Fin p.T) (source : SourceInput p) (f : Scalar) (v : Fin p.T) (hvt : v.val ≤ t.val) :
    incoming rate rewards C_star C_h v source =
    incoming rate rewards C_star C_h v (insertCurrentFastScalar t source f) := by
  have hp : sourcePrefix control0 v.val (insertCurrentFastScalar t source f) =
      sourcePrefix control0 v.val source := by
    calc
      _ = sourcePrefix control0 v.val
          (sourcePrefix control0 t.val (insertCurrentFastScalar t source f)) :=
        (sourcePrefix_sourcePrefix control0 v.val t.val hvt _).symm
      _ = sourcePrefix control0 v.val (sourcePrefix control0 t.val source) := by
        rw [sourcePrefix_strictPast_insert_eq]
      _ = _ := sourcePrefix_sourcePrefix control0 v.val t.val hvt _
  rw [incoming_factor rate rewards C_star C_h control0 v source, incoming_factor rate rewards C_star
    C_h control0 v (insertCurrentFastScalar t source f), hp]

private theorem actualRecord_fields (t : Fin p.T) (z : SourceInput p) (r : Record)
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧ r.input.selected = selectedRowIndex p z ∧
    r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hrec := actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

/-! Local row consumers below retain every exceptional branch. -/

private def fastRow (row : CompleteRow p) (t : Fin p.T) (f : Scalar) : CompleteRow p :=
  (row.1, Function.update row.2 t (replaceFastScalar (row.2 t) f))

section RowDraws
variable (row : CompleteRow p) (t s : Fin p.T) (f : Scalar)

private theorem fastRow_scalar (label : Label p.m p.K) (hlabel : label ≠ Label.fast) :
    ((fastRow row t f).2 s).1 label = (row.2 s).1 label := by
  by_cases h : s = t
  · subst s
    simp only [fastRow, replaceFastScalar, Function.update_self]
    exact Function.update_of_ne hlabel _ _
  · simp only [fastRow, Function.update_of_ne h]

private theorem fastRow_affine : ((fastRow row t f).2 s).2 = (row.2 s).2 := by
  by_cases h : s = t
  · subst s
    simp only [fastRow, replaceFastScalar, Function.update_self]
  · simp only [fastRow, Function.update_of_ne h]

private theorem slot_row : slotDraw ((fastRow row t f).2 s).1 = slotDraw (row.2 s).1 := by
  unfold slotDraw coordinate
  rw [fastRow_scalar row t s f _ (by intro h; cases h)]

private theorem selected_row : selectedFollowerDraw p.two_le_m p.m_lt_K ((fastRow row t f).2 s).1 =
    selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 s).1 := by
  unfold selectedFollowerDraw coordinate
  rw [fastRow_scalar row t s f _ (by intro h; cases h)]

private theorem recorder_row : recorderSourceDraw p.two_le_m p.m_lt_K ((fastRow row t f).2 s).1 =
    recorderSourceDraw p.two_le_m p.m_lt_K (row.2 s).1 := by
  unfold recorderSourceDraw coordinate
  rw [fastRow_scalar row t s f _ (by intro h; cases h)]

private theorem pilot_row (i : Fin p.m) : pilotDraw (K_pos p) i ((fastRow row t f).2 s).1 =
    pilotDraw (K_pos p) i (row.2 s).1 := by
  unfold pilotDraw coordinate
  rw [fastRow_scalar row t s f _ (by intro h; cases h)]

private theorem tuple_row : OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((fastRow row t f).2 s).1 =
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 s).1 := by
  apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq
  intro i
  exact fastRow_scalar row t s f _ (by intro h; cases h)

end RowDraws

/-- At or after cutoff, the literal FAST replacement preserves the entire
coordinator arm-choice result, including the empty-pending collection branch. -/
theorem coordinatorArmChoice_eq_of_collection_fast_replace
    {eta : ReferencePrelaunchFollower.LearningRate} (payload : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m)) (cutoff : Option (Activation p))
    (t : Fin p.T) (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (row : CompleteRow p) (f : Scalar) (hcutoff : cutoffRound cutoff ≤ sourceRound t) :
    coordinatorArmChoiceCore payload pending cutoff t weights (row.2 t) =
    coordinatorArmChoiceCore payload pending cutoff t weights (replaceFastScalar (row.2 t) f) := by
  classical
  have hf : (fastRow row t f).2 t = replaceFastScalar (row.2 t) f := by
    simp only [fastRow, Function.update_self]
  rw [← hf]
  have hn : ¬ (assignmentIsLive payload cutoff t ∧ pending = ∅) :=
    fun h => Nat.not_lt_of_ge hcutoff h.1.2
  by_cases hv : ChoiceInputsValid payload cutoff t weights
  · simp only [coordinatorArmChoiceCore, dite_eq_left hv, ite_eq_right hn, slot_row, selected_row,
    pilot_row, tuple_row, currentDownHash, fastRow_affine]
  · simp only [coordinatorArmChoiceCore, dite_eq_right hv]

section RowOperations
variable (row : CompleteRow p) (t : Fin p.T) (f : Scalar)

private theorem proposal_row (eta : ℝ) :
    FollowerCutoffScan.completeRowProposalBit p eta (fastRow row t f) =
    FollowerCutoffScan.completeRowProposalBit p eta row := by
  funext s
  simp only [FollowerCutoffScan.completeRowProposalBit, CompletePublicTable.completeRowLearning]
  rw [fastRow_scalar row t s f _ (by intro h; cases h)]

private theorem checkedUpOffer_row (eta : ReferencePrelaunchFollower.LearningRate) (i : Fin (p.m - 1))
    (activation : Activation p) (s : Fin p.T) (state : ReferencePrelaunchFollower.State p eta) :
    checkedUpOffer eta i (fastRow row t f) activation s state =
    checkedUpOffer eta i row activation s state := by
  unfold checkedUpOffer selectedUpRound
  dsimp only
  rw [slot_row, selected_row]

private theorem followerArmChoice_row {eta : ReferencePrelaunchFollower.LearningRate}
    (state : ReferencePrelaunchFollower.State p eta) (s : Fin p.T) (i : Fin (p.m - 1))
    (offered : Option (OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p eta))) :
    followerArmChoice state (fastRow row t f) s i offered = followerArmChoice state row s i offered := by
  apply followerArmChoiceCore_eq_of_same_local_draws
  · exact slot_row row t s f
  · exact selected_row row t s f
  · exact tuple_row row t s f
  · exact pilot_row row t s f _
  · exact congrFun (fastRow_affine row t s f) _

private theorem prepare_follower_row (i : Fin (p.m - 1)) (activation : Activation p)
    (s : Fin p.T) (active : activation.val ≤ s.val + 1) (configuration : LocalConfiguration p rate) :
    DeclaredFollowerLocalRound.prepare rate i (fastRow row t f) activation s active configuration =
    { DeclaredFollowerLocalRound.prepare rate i row activation s active configuration with
    row := fastRow row t f } := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
    cases hs : ActiveFollowerLifecycle.startRound rate.eta s state memory with
    | error reason => simp only [DeclaredFollowerLocalRound.prepare, hs]
    | ok result =>
      rcases result with ⟨choiceState, choiceMemory⟩
      cases ho : checkedUpOffer rate.eta i row activation s choiceState with
      | failure => simp only [DeclaredFollowerLocalRound.prepare, hs, checkedUpOffer_row, ho]
      | noOffer =>
        cases hc : followerArmChoice choiceState row s i none <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs, checkedUpOffer_row, ho, followerArmChoice_row, hc]
      | offer offered =>
        cases hc : followerArmChoice choiceState row s i (some offered) <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs, checkedUpOffer_row, ho, followerArmChoice_row, hc]

private theorem thin_scalar (s : Fin p.T) : ((fastRow row t f).2 s).1 Label.thin =
    (row.2 s).1 Label.thin := fastRow_scalar row t s f _ (by intro h; cases h)

private theorem slot_scalar (s : Fin p.T) : ((fastRow row t f).2 s).1 Label.slot =
    (row.2 s).1 Label.slot := fastRow_scalar row t s f _ (by intro h; cases h)

private theorem rec_scalar (s : Fin p.T) : ((fastRow row t f).2 s).1 Label.rec = (row.2 s).1 Label.rec :=
    fastRow_scalar row t s f _ (by intro h; cases h)

private theorem down_row (view : Option (ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (s : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceDownReception.referenceDownCut p view i (fastRow row t f) s observation rate state =
    ReferenceDownReception.referenceDownCut p view i row s observation rate state := by
  have he : ReferenceDownReception.expectedDownFlatWord view i (fastRow row t f) s =
      ReferenceDownReception.expectedDownFlatWord view i row s := by
    cases view with
    | none => rfl
    | some view =>
      have hg : (coordinatorArmChoice view.payload view.pendingAtChoice
            view.cutoff s view.complementWeights (fastRow row t f) ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch view i
              (fastRow row t f) s) ↔
          (coordinatorArmChoice view.payload view.pendingAtChoice
            view.cutoff s view.complementWeights row ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch view i row s) := by
        simp only [ne_eq]
        rw [ReferenceAffineDispatchPairInvariance.coordinatorArmChoice_none_iff view.payload
          view.pendingAtChoice view.cutoff s view.complementWeights (fastRow row t f) row]
        simp only [ReferenceDownReception.selectedDownSenderBranch, slot_row, selected_row]
      by_cases h : coordinatorArmChoice view.payload view.pendingAtChoice
          view.cutoff s view.complementWeights row ≠ none ∧
          ReferenceDownReception.selectedDownSenderBranch view i row s
      · simp only [ReferenceDownReception.expectedDownFlatWord, ite_eq_left h, ite_eq_left (hg.mpr h)]
      · simp only [ReferenceDownReception.expectedDownFlatWord, ite_eq_right h, ite_eq_right (fun hv =>
        h (hg.mp hv))]
  have hd : ActiveFollowerDownAcceptance.currentDecodeStep p i (fastRow row t f)
      s observation rate state =
      ActiveFollowerDownAcceptance.currentDecodeStep p i row s observation rate state := by
    simp only [ActiveFollowerDownAcceptance.currentDecodeStep,
      ActiveFollowerDownAcceptance.currentRoundInput, fastRow_affine]
    rw [slot_row, selected_row]
  have hc (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (hstart : (ActiveFollowerDownAcceptance.downStart p rate message).val ≤ s.val) :
      ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message s hstart (fastRow row t f) =
        ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message s hstart row := by
    simp only [ActiveFollowerDownAcceptance.acceptedCutoffScan,
      FollowerCutoffScan.completeRowCutoffScan, proposal_row]
  have hsel : ActiveFollowerDownAcceptance.downSelected p i (fastRow row t f) s =
      ActiveFollowerDownAcceptance.downSelected p i row s := by
    unfold ActiveFollowerDownAcceptance.downSelected
    rw [slot_row, selected_row]
  simp only [ReferenceDownReception.referenceDownCut, he, hsel, hd, hc]
  rw [hsel]

private theorem public_row (s : Fin p.T) :
    ActiveFollowerLifecycle.publicRowOfCompleteRow (fastRow row t f) s =
    ActiveFollowerLifecycle.publicRowOfCompleteRow row s := by
  simp only [ActiveFollowerLifecycle.publicRowOfCompleteRow, slot_row, selected_row, tuple_row,
    pilot_row]

private theorem release_row (i : Fin (p.m - 1)) (s : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) :
    releaseAndFinish rate i (fastRow row t f) s observation state memory post =
    releaseAndFinish rate i row s observation state memory post := by
  simp only [releaseAndFinish, public_row, ActiveFollowerLifecycle.finishRound, proposal_row]

private theorem clock_finish_row (time : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (pending : Finset (Fin (p.m - 1))) :
    CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending (fastRow row t f) =
    CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending row := by
  simp only [CoordinatorPhaseClock.finishRound, proposal_row]

private theorem recorder_run_row
    (input : CoordinatorRecordingOperation.Input p) (hrow : input.row = row) :
    CoordinatorRecordingOperation.run { input with row := (fastRow row t f) } =
    CoordinatorRecordingOperation.run input := by
  have hi : CoordinatorRecordingOperation.InputsValid { input with row := (fastRow row t f) } ↔
      CoordinatorRecordingOperation.InputsValid input := by
    constructor <;> intro h <;>
      exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos, h.eta_source_cap,
        h.anchor_pos, h.current_pos, h.anchor_le_current, h.current_le_twice_anchor⟩
  by_cases hv : CoordinatorRecordingOperation.InputsValid input
  · simp only [CoordinatorRecordingOperation.run, dite_eq_left hv, dite_eq_left (hi.mpr hv)]
    have hslot : CoordinatorRecordingOperation.selectedSlot { input with row := (fastRow row t f) } =
        CoordinatorRecordingOperation.selectedSlot input := by
      simp only [CoordinatorRecordingOperation.selectedSlot, ContinuousLearningRows.sliceAt,
        coordinate, hrow, slot_scalar]
    have hrec : CoordinatorRecordingOperation.selectedRecorder { input with row := (fastRow row t f) } =
        CoordinatorRecordingOperation.selectedRecorder input := by
      simp only [CoordinatorRecordingOperation.selectedRecorder, ContinuousLearningRows.sliceAt,
        coordinate, hrow, rec_scalar]
    have hmask : CoordinatorRecordingOperation.ownMaskPasses { input with row := (fastRow row t f) } =
        CoordinatorRecordingOperation.ownMaskPasses input := by
      apply propext
      simp only [CoordinatorRecordingOperation.ownMaskPasses, CanonicalRecordingSlice.recordingMask,
        ContinuousLearningRows.sliceAt, hrow, pilot_row]
    have hraw : CoordinatorRecordingOperation.coordinatorRawGateMass
        { input with row := (fastRow row t f) } (hi.mpr hv) =
        CoordinatorRecordingOperation.coordinatorRawGateMass input hv := rfl
    have hthin : coordinate Label.thin (ContinuousLearningRows.sliceAt input.time (fastRow row t f).2) =
        coordinate Label.thin
          (ContinuousLearningRows.sliceAt input.time input.row.2) := by
      simp only [ContinuousLearningRows.sliceAt, coordinate, hrow, thin_scalar]
    have hfrozen : CoordinatorRecordingOperation.isFrozen { input with row := (fastRow row t f) } =
        CoordinatorRecordingOperation.isFrozen input := rfl
    have hfloor : CoordinatorRecordingOperation.floorArrival { input with row := (fastRow row t f) } =
        CoordinatorRecordingOperation.floorArrival input := rfl
    simp only [CoordinatorRecordingOperation.executeValid, hslot, hrec, hraw, hthin, hfloor]
    rw [hfrozen, hmask]
  · simp only [CoordinatorRecordingOperation.run, dite_eq_right hv, dite_eq_right (fun h => hv (hi.mp
    h))]

private theorem recorder_bridge_row (payload : Payload rate)
    (input : CoordinatorRecorderComplementBridge.Input payload) (hrow : input.row = row) :
    CoordinatorRecorderComplementBridge.run { input with row := (fastRow row t f) } =
    CoordinatorRecorderComplementBridge.run input := by
  change CoordinatorRecordingOperation.run { CoordinatorRecorderComplementBridge.recorderInput input with
        row := (fastRow row t f) } =
    CoordinatorRecordingOperation.run (CoordinatorRecorderComplementBridge.recorderInput input)
  exact recorder_run_row row t f (CoordinatorRecorderComplementBridge.recorderInput input) hrow

private theorem reception_input_row
    (inputs : ReferenceUpReception.ReceptionLocalInputs rate) (s : Fin p.T) :
    ReferenceUpReception.receptionInputAtRow rate (fastRow row t f) inputs s =
    ReferenceUpReception.receptionInputAtRow rate row inputs s := by
  simp only [ReferenceUpReception.receptionInputAtRow, CoordinatorUpMeasurability.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtControl,
    CoordinatorUpMeasurability.selectedChannelFollower,
    CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw, slot_row, selected_row, fastRow_affine]

end RowOperations

/-- A collection readout's selected cutoff is at or before this very round.
This is derived from the actual cutoff-clock equation or continuing core,
not an additional cutoff comparison. -/

private theorem selection_cutoff_of_collection_branch (record : Record)
    (hbranch : match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => True
      | _ => False) :
    ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      cutoffRound selected.view.cutoff ≤
        sourceRound record.input.time := by
  classical
  cases hc : record.output.preparation.coordinator with
  | first out => cases out <;> simp [hc] at hbranch
  | dagger => simp [hc] at hbranch
  | invalidCollectionCutoff => simp [hc] at hbranch
  | live r q base out =>
    cases out <;> simp [hc] at hbranch
    next dispatched hs ledger hi he hdomain hclock hp hn selected =>
      have hu : dispatched.startResult.clock.u = some record.input.time := by
        have h := congrArg CoordinatorPhaseClock.ClockRegisters.u hclock
        simpa only [liveInput, liveRegistersAt] using h
      simp only [DispatchCut.selection, selectionAt, dite_true]
      refine ⟨_, rfl, ?_⟩
      simp only [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hu, sourceRound,
        Option.elim_some]
      exact le_rfl
  | collection payload ledger clock cutoff out =>
    cases out <;> simp [hc] at hbranch
    next core snapshot boundary scores =>
      have hu : snapshot.clockStarted.clock.u = some cutoff := by
        rw [snapshot.clockStarted_frame.1]
        exact core.clock_cutoff_eq
      have ht := core.clock_start_time_valid
      change CoordinatorPhaseClock.startRoundTimeValid p record.input.time clock at ht
      unfold CoordinatorPhaseClock.startRoundTimeValid at ht
      have hsigma : clock.sigma = some payload.sigma := core.clock_sigma_eq
      have hcutoff : clock.u = some cutoff := core.clock_cutoff_eq
      rw [hsigma, hcutoff] at ht
      have ht' : payload.sigma.val < record.input.time.val ∧
          cutoff.val ≤ record.input.time.val := by simpa using ht
      refine ⟨_, rfl, ?_⟩
      change cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u) ≤ _
      rw [CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hu]
      dsimp only [sourceRound, Option.elim]
      omega

/-- The comparison is a consequence of the actual readout domain. -/
theorem collectionReadout_selection_cutoff (record : Record) (cell : RecordedQueueRun.RoundInput p.K)
    (hcell : laterCollectionReadout 0 record = some cell) : ∃ selected : Selection record.input,
    record.output.preparation.coordinator.selection = some selected ∧
    cutoffRound selected.view.cutoff ≤ sourceRound record.input.time := by
  apply selection_cutoff_of_collection_branch record
  have hd := ((laterCollectionReadout_domain 0 record).mp (by rw [hcell]; rfl)).2
  cases hc : record.output.preparation.coordinator <;> try (rename_i out; cases out)
  all_goals simp_all only

private theorem not_live_of_collection_phase (record : Record)
    (hphase : CollectionPhase record.input.state.coordinator)
    (hlater : laterChosen record.input = false) : ¬ laterLiveDomain 0 record := by
  classical
  have hprep : record.output.preparation.coordinator =
      dispatch record.input := by rw [record.output_eq]; rfl
  rintro ⟨selected, hs, hpositive, hlive, hord⟩
  rcases hphase with hdagger | ⟨payload, ledger, saved, hstate⟩
  · rw [hprep, dispatch_dagger record.input hdagger] at hs
    cases hs
  · by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger saved cutoff
      let input := collectionInput record.input payload ledger clock cutoff
      have hd : record.output.preparation.coordinator =
          .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection input) := by
        rw [hprep]
        simp only [dispatch, hstate, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
        rfl
      cases ho : CoordinatorRoundDispatch.dispatchCollection input <;>
        try { simp only [hd, ho, DispatchCut.selection] at hs; cases hs }
      next core snapshot boundary scores =>
        have hb : match record.output.preparation.coordinator with
            | .collection _ _ _ _ (.continuing _ _ _ _) => True
            | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => True
            | _ => False := by rw [hd, ho]; trivial
        obtain ⟨other, he, hbound⟩ := selection_cutoff_of_collection_branch record hb
        have heq := Option.some.inj (hs.symm.trans he)
        subst other
        exact Nat.not_lt_of_ge hbound hlive.2
      next core consistent started hstart instruction hi output hcons data installed arm =>
        have hl : (prepare record.input).coordinator =
            record.output.preparation.coordinator := by rw [record.output_eq]; rfl
        simp only [laterChosen, hl, hd, ho, Bool.true_eq_false] at hlater
    · rw [hprep, (dispatch_collection_invalid_cutoff record.input payload ledger saved hstate hcutoff).1]
      at hs
      cases hs

private theorem readout_next_collection_phase (record : Record) (cell : RecordedQueueRun.RoundInput p.K)
    (hcell : laterCollectionReadout 0 record = some cell) :
    CollectionPhase record.output.next.coordinator := by
  obtain ⟨payload, ledger, started, weights, out, _, hpost, _⟩ :=
    laterCollectionReadout_call 0 record cell hcell
  have hp := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    record.output.preparation payload ledger started weights
  rw [← hpost] at hp
  have hn : record.output.next.coordinator = record.coordinatorDiagnostics.configuration := by
    change record.output.next.coordinator = record.output.coordinator.configuration
    rw [record.output_eq]; rfl
  rw [hn]
  exact hp

private theorem collection_tail_readouts (records : List (Record)) (initial final : State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinitial : CollectionPhase initial.coordinator) (hphases : ∀ r ∈ records, laterLiveDomain 0 r ∨
    ∃ cell, laterCollectionReadout 0 r = some cell) :
    ∀ r ∈ records.takeWhile (fun r => !laterChosen r.input),
    ∃ cell, laterCollectionReadout 0 r = some cell := by
  induction records generalizing initial with
  | nil => simp only [List.takeWhile_nil, List.not_mem_nil, false_implies, implies_true]
  | cons head rest ih =>
    cases hl : laterChosen head.input with
    | true => simp only [hl, Bool.not_true, List.takeWhile, List.not_mem_nil, false_implies,
      implies_true]
    | false =>
      have hinput : CollectionPhase head.input.state.coordinator :=
        hchain.1 ▸ hinitial
      have hhead : ∃ cell, laterCollectionReadout 0 head = some cell := by
        rcases hphases head (by simp only [List.mem_cons, true_or]) with h | h
        · exact False.elim (not_live_of_collection_phase head hinput hl h)
        · exact h
      obtain ⟨cell, hcell⟩ := hhead
      have hnext := readout_next_collection_phase head cell hcell
      have hrest := ih head.output.next hchain.2 hnext
        (fun r hr => hphases r (List.mem_cons_of_mem head hr))
      intro r hr
      simp only [hl, Bool.not_false, List.takeWhile, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨cell, hcell⟩
      · exact hrest r hr

private theorem first_collection_readouts (records : List (Record)) (initial final : State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hphases : ∀ r ∈ records, laterLiveDomain 0 r ∨ ∃ cell, laterCollectionReadout 0 r = some cell) :
    ∀ r ∈ collectionWindow records (firstLiveWindow records).length,
    ∃ cell, laterCollectionReadout 0 r = some cell := by
  induction records generalizing initial with
  | nil => simp only [collectionWindow, List.drop_nil, List.take_nil, List.takeWhile_nil,
    List.append_nil, List.not_mem_nil, false_implies, implies_true]
  | cons head rest ih =>
    cases hcut : cutoffChosen head.input with
    | false =>
      have hrest := ih head.output.next hchain.2 (fun r hr => hphases r (List.mem_cons_of_mem head hr))
      simpa only [firstLiveWindow,
        List.takeWhile, hcut, Bool.not_false, List.length_cons,
        collectionWindow, List.drop_succ_cons,
        Nat.succ_eq_add_one, Nat.add_right_comm] using hrest
    | true =>
      have hb : match head.output.preparation.coordinator with
          | .collection _ _ _ _ (.continuing _ _ _ _) => True
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => True
          | _ => False := by
        have hp : (prepare head.input).coordinator =
            head.output.preparation.coordinator := by rw [head.output_eq]; rfl
        unfold cutoffChosen at hcut
        rw [hp] at hcut
        cases hc : head.output.preparation.coordinator <;> try (rename_i out; cases out)
        all_goals simp_all only [Bool.false_eq_true]
      have hhead : ∃ cell, laterCollectionReadout 0 head = some cell := by
        rcases hphases head (by simp only [List.mem_cons, true_or]) with hlive | h
        · obtain ⟨selected, hs, hbound⟩ := selection_cutoff_of_collection_branch head hb
          rcases hlive with ⟨other, ho, _, hlt, _⟩
          have he := Option.some.inj (ho.symm.trans hs)
          subst other
          exact False.elim (Nat.not_lt_of_ge hbound hlt.2)
        · exact h
      obtain ⟨cell, hcell⟩ := hhead
      have htail := collection_tail_readouts rest head.output.next final hchain.2
        (readout_next_collection_phase head cell hcell)
        (fun r hr => hphases r (List.mem_cons_of_mem head hr))
      intro r hr
      simp only [firstLiveWindow, List.takeWhile, hcut, Bool.not_true, List.length_nil,
        collectionWindow, List.drop_zero, List.take_succ_cons, List.take_zero, Nat.zero_add,
        List.drop_succ_cons, List.cons_append, List.nil_append, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨cell, hcell⟩
      · exact htail r hr

/-- Canonical first-collection membership itself supplies a present collection
readout. No future invocation or successful trace is assumed. -/
theorem firstCollection_actual_collectionReadout (source : SourceInput p) (record : Record)
    (hmem : record ∈ collectionRecords source) :
    ∃ cell, laterCollectionReadout 0 record = some cell := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h with
  | none =>
    simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl, dite_true, collectionWindow,
      List.drop_nil, List.take_nil, List.takeWhile_nil, List.append_nil, List.not_mem_nil] at hmem
  | some active =>
    have hc := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate source rewards C_star C_h active hl
    apply first_collection_readouts _ active _ hc _ record hmem
    intro r hr
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hr
    subst r
    exact (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h source ⟨k, hk⟩).2

private def fastInputAt (x : Input) (t : Fin p.T) (f : Scalar) : Input :=
  { x with rows := Function.update x.rows x.selected (fastRow x.row t f) }

private def fastInput (x : Input) (f : Scalar) : Input := fastInputAt x x.time f

private theorem fastInputAt_row (x : Input) (t : Fin p.T) (f : Scalar) :
    (fastInputAt x t f).row = fastRow x.row t f := by
  simp only [fastInputAt, ReferenceActivePhysicalStep.RoundInput.row, Function.update_self]

private theorem fastInput_row (x : Input) (f : Scalar) :
    (fastInput x f).row = fastRow x.row x.time f := fastInputAt_row x x.time f

private theorem fastInputAt_dispatch_tail (x : Input) (t : Fin p.T) (f : Scalar) : (dispatchData x).2 =
    (dispatchData (fastInputAt x t f)).2 := by
  apply ReferenceAffineDispatchPairInvariance.dispatch_tail_eq_of_assignment
  intro s
  change LaterAssignmentStartOperation.ownAssignmentVector x.row s =
    LaterAssignmentStartOperation.ownAssignmentVector (fastInputAt x t f).row s
  rw [fastInputAt_row]
  unfold LaterAssignmentStartOperation.ownAssignmentVector
  funext i
  exact (fastRow_scalar x.row t s f _ (by intro h; cases h)).symm

private theorem fastInput_dispatch_tail (x : Input) (f : Scalar) : (dispatchData x).2 =
      (dispatchData (fastInput x f)).2 :=
  fastInputAt_dispatch_tail x x.time f

private theorem dispatchTags_formula (x : Input) :
    (cutoffChosen x, laterChosen x) =
      match x.state.coordinator with
      | .live _ _ _ =>
          ((match tailArgs (dispatch x) with
            | .inr (.inr (.inr _)) => true | _ => false), false)
      | .collection _ _ _ =>
          (false, (match tailArgs (dispatch x) with
            | .inr (.inr (.inl _)) => true | _ => false))
      | _ => (false, false) := by
  classical
  unfold cutoffChosen laterChosen
  change (match dispatch x with | .live _ _ _ (.cutoffChosen ..) => true | _ => false,
    match dispatch x with | .collection _ _ _ _ (.laterChosen ..) => true | _ => false) = _
  cases hp : x.state.coordinator with
  | first => simp only [hp, dispatch, CoordinatorRoundDispatch.dispatch]; rfl
  | dagger => simp only [hp, dispatch]
  | live r q base =>
    have hd : dispatch x = .live r q base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
      simp only [dispatch, hp, CoordinatorRoundDispatch.dispatch]
      rfl
    rw [hd]
    cases CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
      simp [tailArgs, DispatchCut.selection, selectionAt]
  | collection payload ledger proposal =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger proposal cutoff
      have hd : dispatch x = .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff)) := by
        simp only [dispatch, hp, dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hd]
      cases CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff) with
      | laterChosen core consistent started hstart instruction hassignment output localEq clockData installation selection =>
        have ht := (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val x.time
          clock ledger.pending started instruction core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hassignment).1
        simp [tailArgs, DispatchCut.selection, selectionAt, ht]
      | _ => simp [tailArgs, DispatchCut.selection]
    · have hd : dispatch x = .invalidCollectionCutoff := by
        simp only [dispatch, hp, dite_eq_right hc]
      rw [hd]
      rfl

private theorem dispatchTags_eq_of_tail (x y : Input) (hs : x.state = y.state)
    (ht : tailArgs (dispatch x) = tailArgs (dispatch y)) : (cutoffChosen x, laterChosen x) =
    (cutoffChosen y, laterChosen y) := by
  rw [dispatchTags_formula, dispatchTags_formula, hs, ht]

private theorem roundInput_eq_of_fields {x y : Input} (hs : x.state = y.state) (hr : x.rows = y.rows)
    (hj : x.selected = y.selected) (ht : x.time = y.time) (hw : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  cases hs
  cases hr
  cases hj
  cases ht
  cases hw
  rfl

private theorem actualRecord_fastInputAt (t : Fin p.T) (source : SourceInput p) (f : Scalar)
    (v : Fin p.T) (hvt : v.val ≤ t.val) (record : Record)
    (hrecord : actualRecord rate rewards C_star C_h v source = some record) :
    ∃ inserted, actualRecord rate rewards C_star C_h v
    (insertCurrentFastScalar t source f) = some inserted ∧ inserted.input = fastInputAt record.input t f := by
  let control0 := record.input.row.2 record.input.time
  have hincoming := insertCurrentFastScalar_incoming_eq (rate := rate)
    rewards C_star C_h control0 t source f v hvt
  unfold incoming at hincoming
  rw [hrecord] at hincoming
  cases hi : actualRecord rate rewards C_star C_h v
      (insertCurrentFastScalar t source f) with
  | none => simp only [hi, Option.map_none, Option.map_some] at hincoming; cases hincoming
  | some inserted =>
    have hs := congrArg decodeState
      (Option.some.inj (by simpa only [hi, Option.map_some] using hincoming)).symm
    simp only [decodeState_encodeState] at hs
    obtain ⟨hir, hij, hit, hiw⟩ := actualRecord_fields rewards C_star C_h v _ inserted hi
    obtain ⟨hrr, hrj, hrt, hrw⟩ := actualRecord_fields rewards C_star C_h v source record hrecord
    refine ⟨inserted, rfl, roundInput_eq_of_fields hs ?_ ?_ ?_ ?_⟩
    · rw [hir]
      change (insertCurrentFastScalar t source f).1.2 =
        Function.update record.input.rows record.input.selected (fastRow record.input.row t f)
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hrr, hrj, insertCurrentFastScalar,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex, fastRow,
        replaceFastScalar]
    · exact hij.trans ((insertCurrentFastScalar_source_frames t source f).2.2.1.trans hrj.symm)
    · exact hit.trans hrt.symm
    · exact hiw.trans hrw.symm

private theorem actualRecord_fastInput (t : Fin p.T) (source : SourceInput p) (record : Record)
    (hrecord : actualRecord rate rewards C_star C_h t source = some record) (f : Scalar) :
    ∃ inserted, actualRecord rate rewards C_star C_h t (insertCurrentFastScalar t source f) = some inserted ∧
    inserted.input = fastInput record.input f := by
  obtain ⟨inserted, hi, hx⟩ := actualRecord_fastInputAt rewards C_star C_h t source f t le_rfl record hrecord
  have ht := (actualRecord_fields rewards C_star C_h t source record hrecord).2.2.1
  exact ⟨inserted, hi, by simpa only [fastInput, ht] using hx⟩

/-- Every actual search tag through the inserted date is preserved, including absent records. -/
theorem insertCurrentFastScalar_prefix_tags_eq (t : Fin p.T) (source : SourceInput p)
    (f : Scalar) (v : Fin p.T) (hvt : v.val ≤ t.val) :
    (actualRecord rate rewards C_star C_h v (insertCurrentFastScalar t source f)).map
    (fun r => (cutoffChosen r.input, laterChosen r.input)) =
    (actualRecord rate rewards C_star C_h v source).map
    (fun r => (cutoffChosen r.input, laterChosen r.input)) := by
  cases hr : actualRecord rate rewards C_star C_h v source with
  | none =>
    have hin := insertCurrentFastScalar_incoming_eq (rate := rate) rewards C_star C_h
      ((source.1.2 (selectedRowIndex p source)).2 t) t source f v hvt
    unfold incoming at hin
    cases hi : actualRecord rate rewards C_star C_h v (insertCurrentFastScalar t source f) <;>
      simp only [hr, hi, Option.map_none, Option.map_some] at hin ⊢
    cases hin
  | some r =>
    obtain ⟨inserted, hi, hx⟩ := actualRecord_fastInputAt rewards C_star C_h t source f v hvt r hr
    rw [hi, Option.map_some, Option.map_some]
    apply congrArg some
    rw [hx]
    exact dispatchTags_eq_of_tail _ _ rfl
      (congrArg Prod.snd (fastInputAt_dispatch_tail r.input t f)).symm

private def selectionCodeFromDispatchData (data : Fin p.K × (Option (ChoiceTimeView p rate.eta) ×
      (Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate))))) :
    Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :=
  match data.2.1, data.2.2 with
  | some view, Sum.inr (Sum.inr (Sum.inl args)) => some (view, (args.2.2.2, data.1))
  | some view, Sum.inr (Sum.inr (Sum.inr args)) => some (view, (args.2.2.1, data.1))
  | _, _ => none

private theorem selectionCode_eq_of_cutData {x : Input} (cut : DispatchCut x) :
    cut.selection.map (ReferenceLiveDispatchOutputMeasurability.encodeSelection) =
    selectionCodeFromDispatchData (cutData cut) := by
  classical
  cases cut <;> try (rename_i outcome; cases outcome)
  all_goals simp_all [selectionCodeFromDispatchData, cutData, tailArgs, DispatchCut.arm,
    DispatchCut.downView, DispatchCut.selection, selectionAt,
    ReferenceLiveDispatchOutputMeasurability.encodeSelection]
  all_goals split_ifs <;> simp_all

private theorem fastInput_arm (record : Record) (cell : RecordedQueueRun.RoundInput p.K)
    (hcell : laterCollectionReadout 0 record = some cell)
    (f : Scalar) : (dispatch record.input).arm = (dispatch (fastInput record.input f)).arm := by
  obtain ⟨selected, hs, hbound⟩ := collectionReadout_selection_cutoff record cell hcell
  have hselection : (dispatch record.input).selection = some selected := by
    have hp : record.output.preparation.coordinator = dispatch record.input := by
      rw [record.output_eq]; rfl
    rw [hp] at hs
    exact hs
  have hv := congrArg Prod.fst (fastInput_dispatch_tail record.input f)
  change (dispatch record.input).downView = (dispatch (fastInput record.input f)).downView at hv
  cases hy : (dispatch (fastInput record.input f)).selection with
  | none =>
    simp only [DispatchCut.downView, hselection, hy, Option.map_some, Option.map_none] at hv
    cases hv
  | some other =>
    have hviews : selected.view = other.view := Option.some.inj (by
      simpa only [DispatchCut.downView, hselection, hy, Option.map_some] using hv)
    have hc := coordinatorArmChoice_eq_of_collection_fast_replace selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff record.input.time
      selected.view.complementWeights record.input.row f hbound
    have ho := other.choice_eq
    rw [← hviews] at ho
    change coordinatorArmChoiceCore selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff record.input.time
      selected.view.complementWeights ((fastInput record.input f).row.2 record.input.time) =
        some other.arm at ho
    rw [fastInput_row] at ho
    simp only [fastRow, Function.update_self] at ho
    rw [← hc] at ho
    have harm : selected.arm = other.arm := Option.some.inj (selected.choice_eq.symm.trans ho)
    simp only [DispatchCut.arm, hselection, hy, harm]

private theorem fastInput_prepared_follower (x : Input) (f : Scalar) (i : Fin (p.m - 1)) :
    (prepare (fastInput x f)).followers.followers i = { (prepare x).followers.followers i with
    row := fastRow x.row x.time f } := by
  change DeclaredFollowerLocalRound.prepare rate i (fastInput x f).row _ _ _ _ = _
  rw [fastInput_row]
  exact prepare_follower_row x.row x.time f i _ _ _ _

private theorem fastInput_actions_feedback (x : Input) (f : Scalar) (harm : (dispatch x).arm =
    (dispatch (fastInput x f)).arm) :
    (prepare x).arms.actions = (prepare (fastInput x f)).arms.actions ∧ (prepare x).feedback.feedback =
    (prepare (fastInput x f)).feedback.feedback := by
  have ha : (prepare x).arms.actions = (prepare (fastInput x f)).arms.actions := by
    funext player
    rcases ActiveRoundActions.player_cases p.two_le_m player with h | ⟨i, h⟩
    · subst player
      rw [PreparedRound.action_coordinator, PreparedRound.action_coordinator]
      exact harm
    · subst player
      change Fin (p.m - 1) at i
      rw [(prepare x).action_follower i, (prepare (fastInput x f)).action_follower i]
      change (DeclaredFollowerLocalRound.prepare rate _ x.row _ _ _ _).arm =
        (DeclaredFollowerLocalRound.prepare rate _ (fastInput x f).row _ _ _ _).arm
      rw [fastInput_row, prepare_follower_row]
      rfl
  refine ⟨ha, ?_⟩
  funext player
  rw [PreparedRound.feedback_rule, PreparedRound.feedback_rule, ha]
  rfl

section FollowerCodes
variable (row : CompleteRow p) (t : Fin p.T) (f : Scalar)
variable (i : Fin (p.m - 1)) (activation : Activation p) (time : ActiveCalendarTime p activation)

private theorem prepareCode_row (incoming : IncomingConfiguration p rate) :
    (prepareOutputOnInput rate i activation (assemblePrepareInput incoming (fastRow row t f) time)).2 =
    (prepareOutputOnInput rate i activation (assemblePrepareInput incoming row time)).2 := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨⟨index, values⟩, memory⟩
    have hp := prepare_follower_row row t f i activation time.val time.property
      (localConfigurationOfCode rate
        (some (index.1, memory))
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values))
    have hcode := congrArg (fun prepared =>
      PreparedRoundCode.mk prepared.arm
        (localConfigurationCode prepared.configuration)) hp
    change prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 (fastRow row t f) time values =
      prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row time values at hcode
    simp only [prepareOutputOnInput, assemblePrepareInput, prepareRoundCodeOnInput,
      prepareOutputConfiguration, hcode]

private theorem recordCode_row (view : Option (ChoiceTimeView p rate.eta))
    (carry : CarriedState p rate) (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    recordObservable rate i activation (view, assembleObservationInput
    carry (fastRow row t f) time feedback arm) = recordObservable rate i activation
    (view, assembleObservationInput carry row time feedback arm) := by
  classical
  have hlog (hu hu') : checkedLoggingObservable rate i activation ⟨assembleObservationInput
          carry (fastRow row t f) time feedback arm, hu⟩ =
      checkedLoggingObservable rate i activation
        ⟨assembleObservationInput
          carry row time feedback arm, hu'⟩ := by
    let original := assembleObservationInput carry row time feedback arm
    let replaced := assembleObservationInput carry (fastRow row t f) time feedback arm
    have hg : FollowerLoggingDownMeasurability.loggingGateBit i (loggingInputOfFiber replaced.2) =
        FollowerLoggingDownMeasurability.loggingGateBit i (loggingInputOfFiber original.2) := by
      simp only [original, replaced, assembleObservationInput, loggingInputOfFiber, fiberRow,
        fiberTime, fiberFeedbackIndex, fiberPlayedArm, FollowerLoggingDownMeasurability.loggingGateBit,
        FollowerLoggingDownMeasurability.inputSliceAt, FollowerLoggingDownMeasurability.inputRow,
        FollowerLoggingDownMeasurability.inputTime, FollowerLoggingDownMeasurability.inputPlayedArm,
        ContinuousLearningRows.sliceAt, CompletePublicTable.completeRowLearning, slot_row,
        recorder_row, pilot_row]
      refine congrArg₂ Bool.and (congrArg₂ Bool.and ?_ ?_) ?_ <;>
        exact decide_eq_decide.mpr Iff.rfl
    have hk : FollowerLoggingDownMeasurability.currentKeyFresh (loggingInputOfFiber replaced.2) =
        FollowerLoggingDownMeasurability.currentKeyFresh (loggingInputOfFiber original.2) := rfl
    unfold checkedLoggingObservable
    dsimp only
    rw [hg, hk]
    simp only [observationInputCarriedState_assemble, observationInputTime_assemble,
      FollowerObservationStageMeasurabilityRepair.observationInputPlayedArm_assemble,
      observationInputFeedbackIndex_assemble, observationInputRow_assemble, thin_scalar]
    rfl
  have hoccupied : occupiedCode rate i activation (assembleObservationInput
        carry (fastRow row t f) time feedback arm) =
    occupiedCode rate i activation
      (assembleObservationInput
        carry row time feedback arm) := by
    unfold occupiedCode FollowerServiceMeasurability.occupiedRoundCodeAtJoint
    rw [FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor,
      FollowerServiceMeasurability.checkedServiceCodeAtJoint_eq_readFactor]
    congr 2
    dsimp only [assembleObservationInput]
    unfold FollowerServiceMeasurability.serviceReadForState
    cases (representativeState rate carry.1).lastDown with
    | none => rfl
    | some M =>
      simp only [FollowerServiceMeasurability.recorderReadForDownAt,
        FollowerServiceMeasurability.recorderGateBit, ActiveFollowerQueueOperation.recorderGate,
        FollowerDownJointMeasurability.jointRow, FollowerDownJointMeasurability.jointTime,
        FollowerDownJointMeasurability.jointRowTime, serviceInputOfFiber, fiberRow, fiberTime,
        CanonicalRecordingSlice.recordingMask, coordinate, slot_row, recorder_row, pilot_row,
        thin_scalar]
      congr 1
      exact decide_eq_decide.mpr Iff.rfl
  unfold recordObservable
  have huiff : (assembleObservationInput carry (fastRow row t f) time feedback arm ∈
        unoccupiedLoggingInputs rate activation) ↔
    (assembleObservationInput
      carry row time feedback arm ∈
        unoccupiedLoggingInputs rate activation) := Iff.rfl
  by_cases hu : assembleObservationInput
      carry row time feedback arm ∈ unoccupiedLoggingInputs rate activation
  · rw [dite_eq_left hu, dite_eq_left (huiff.mpr hu)]
    unfold unoccupiedRecord
    rw [hlog _ hu]
    cases checkedLoggingObservable rate i activation _ with
    | inl reason => rfl
    | inr logged =>
      simp only [downCall, observationInputRow_assemble, observationInputTime_assemble,
        observationInputFeedbackIndex_assemble, down_row]
  · rw [dite_eq_right hu, dite_eq_right (fun h => hu (huiff.mp h))]
    simp only [occupiedRecord, hoccupied, observationInputCarriedState_assemble]

private theorem finishCode_row (view : Option (ChoiceTimeView p rate.eta))
    (incoming : IncomingConfiguration p rate) (feedback : Fin (D p + 1)) (arm : Fin p.K) :
    finishFollowerObservable rate i activation
    (view, ((fastRow row t f, time), (arm, incoming)), feedback) =
    finishFollowerObservable rate i activation (view, ((row, time), (arm, incoming)), feedback) := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨carry, memory⟩
    unfold finishFollowerObservable ordinaryObservable
    dsimp only
    rw [recordCode_row]
    generalize (recordObservable rate i activation
      (view, assembleObservationInput carry row time feedback arm)).1 = result
    cases result with
    | inl reason => rfl
    | inr postRecord =>
      simp only [finishRecordResult, observationInputCarriedState_assemble,
        observationInputRow_assemble, observationInputTime_assemble,
        observationInputFeedbackIndex_assemble,
        FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents,
        FollowerLifecycleMeasurability.releaseAndFinishResultCodeAt, release_row]

end FollowerCodes

private theorem fastInput_followerCode (x : Input) (f : Scalar)
    (harm : (dispatch x).arm = (dispatch (fastInput x f)).arm) (i : Fin (p.m - 1)) :
    followerObservable (fastInput x f) i = followerObservable x i := by
  have hv := congrArg Prod.fst (fastInput_dispatch_tail x f)
  change (dispatch x).downView = (dispatch (fastInput x f)).downView at hv
  have hf := congrFun (fastInput_actions_feedback x f harm).2 (followerPlayer p.two_le_m i)
  let activation := x.state.activations i
  let time : ActiveCalendarTime p activation := ⟨x.time, x.active i⟩
  let incoming := incomingOfLocalConfiguration rate (x.state.followers i)
  let prepared (row : CompleteRow p) :=
    prepareOutputOnInput rate i activation
      (assemblePrepareInput incoming row time)
  have hrepr (row : CompleteRow p) : prepared row = ((row, time), (prepared row).2) := by
    dsimp only [prepared, prepareOutputOnInput]
    cases incoming <;> rfl
  unfold followerObservable observeFollowerObservable canonicalFollowerInput
  change finishFollowerObservable rate i activation
      ((dispatch (fastInput x f)).downView, prepared (fastInput x f).row,
        (prepare (fastInput x f)).feedback.feedback (followerPlayer p.two_le_m i)) =
    finishFollowerObservable rate i activation
      ((dispatch x).downView, prepared x.row,
        (prepare x).feedback.feedback (followerPlayer p.two_le_m i))
  rw [fastInput_row, hrepr (fastRow x.row x.time f), hrepr x.row, ← hv, ← hf]
  rw [show (prepared (fastRow x.row x.time f)).2 = (prepared x.row).2 from prepareCode_row x.row x.time f i activation time incoming]
  exact finishCode_row x.row x.time f i activation time _ _ _ _

private theorem fastInput_followers (x : Input) (f : Scalar)
    (harm : (dispatch x).arm = (dispatch (fastInput x f)).arm) :
    (prepare x).observeFollower = (prepare (fastInput x f)).observeFollower := by
  funext i
  rw [← followerObservable_reconstruct x i, ← followerObservable_reconstruct (fastInput x f) i,
    fastInput_followerCode x f harm i]

private theorem fastInput_receive_up (x : Input) (f : Scalar) (harm : (dispatch x).arm =
    (dispatch (fastInput x f)).arm) (ledger : Ledger rate) :
    receiveUp (prepare (fastInput x f)) ledger = receiveUp (prepare x) ledger := by
  have ho : (prepare (fastInput x f)).coordinatorObservation = (prepare x).coordinatorObservation :=
    congrFun (fastInput_actions_feedback x f harm).2.symm (ActiveRoundActions.coordinator p.two_le_m)
  have ht : (fastInput x f).time = x.time := rfl
  have hs : (fastInput x f).state = x.state := rfl
  have hi : upSenderIndex (fastInput x f) = upSenderIndex x := by
    simp only [upSenderIndex, fastInput_row, CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
      ht, selected_row]
    rfl
  simp only [receiveUp, upInputs, upExpected, hi, fastInput_prepared_follower, fastInput_row,
    ReferenceUpReception.receiveUpFilteredAtRow,
    ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow, reception_input_row,
    ReferenceUpReception.currentOfferWord, checkedUpOffer_row, ho, hs, ht]
  simp only [((prepare x).follower_alignment _).1]

private theorem fastInput_collection_postChoice (x : Input) (f : Scalar) (harm : (dispatch x).arm =
    (dispatch (fastInput x f)).arm) (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) : collectionPostChoice (prepare x)
    payload ledger started weights = collectionPostChoice (prepare (fastInput x f))
    payload ledger started weights := by
  have ho : (prepare x).coordinatorObservation = (prepare (fastInput x f)).coordinatorObservation :=
    congrFun (fastInput_actions_feedback x f harm).2 (ActiveRoundActions.coordinator p.two_le_m)
  let input := collectionRecordingInput (prepare x) payload started weights
  have hr : CoordinatorRecorderComplementBridge.run input = CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput
          (prepare (fastInput x f)) payload started weights) := by
    have h := recorder_bridge_row x.row x.time f payload input rfl
    dsimp only [input, collectionRecordingInput] at h ⊢
    rw [fastInput_row]
    change CoordinatorRecorderComplementBridge.run _ = CoordinatorRecorderComplementBridge.run
      { currentWeights := weights, time := x.time, gridBoundary := started.clock.g,
        row := fastRow x.row x.time f,
        ownArm := (dispatch (fastInput x f)).arm,
        observation := (prepare (fastInput x f)).coordinatorObservation,
        mode := .collection }
    rw [← harm, ← ho]
    exact h.symm
  have hf (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut =
        ReferenceActivePhysicalStep.collectionFinish (x := fastInput x f) payload started recording cut := by
    simp only [ReferenceActivePhysicalStep.collectionFinish, fastInput_row, clock_finish_row (rate :=
      rate) x.row x.time f]
    rfl
  dsimp only [input] at hr
  simp only [collectionPostChoice, hr, fastInput_receive_up x f harm, ← hf]
  rfl

private theorem collection_call_tailArgs (record : Record) (args : CollectionArgs p rate)
    (hcall : laterCollectionCall 0 record = some args) :
    tailArgs record.output.preparation.coordinator = .inr (.inr (.inr args)) := by
  classical
  unfold laterCollectionCall at hcall
  split at hcall
  next hf =>
    cases hc : record.output.preparation.coordinator with
    | first out => cases out <;> simp only [hc] at hcall <;> cases hcall
    | dagger => simp only [hc] at hcall; cases hcall
    | invalidCollectionCutoff => simp only [hc] at hcall; cases hcall
    | live r q base out =>
      cases out <;> simp only [hc] at hcall <;> try { cases hcall }
      next dispatched hs ledger hi he hdomain hclock hp hn selected =>
        split at hcall
        next hpositive =>
          rw [← Option.some.inj hcall]
          simp [tailArgs, DispatchCut.selection, selectionAt]
        next => cases hcall
    | collection payload ledger clock cutoff out =>
      cases out <;> simp only [hc] at hcall <;> try { cases hcall }
      next core snapshot boundary scores =>
        rw [← Option.some.inj hcall]
        simp [tailArgs, DispatchCut.selection]
  next => cases hcall

private theorem observeCoordinator_tail_formula {x : Input} (prepared : PreparedRound x) :
    prepared.observeCoordinator = match tailArgs prepared.coordinator with
      | .inl _ => ⟨.dagger, x.state.upDecoderBank, none, none, none⟩
      | .inr (.inl _) => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
      | .inr (.inr (.inl args)) =>
          livePostChoice prepared args.1 args.2.1 args.2.2.1 args.2.2.2
      | .inr (.inr (.inr args)) =>
          collectionPostChoice prepared args.1 args.2.1 args.2.2.1 args.2.2.2 := by
  classical
  cases hc : prepared.coordinator <;> try (rename_i outcome; cases outcome)
  all_goals simp only [PreparedRound.observeCoordinator, hc, tailArgs]
  all_goals split_ifs <;> rfl

private theorem fastInput_collection_coordinator (record : Record)
    (cell : RecordedQueueRun.RoundInput p.K) (hcell : laterCollectionReadout 0 record = some cell)
    (f : Scalar) : (prepare record.input).observeCoordinator =
    (prepare (fastInput record.input f)).observeCoordinator := by
  obtain ⟨payload, ledger, started, weights, out, hcall, hpost, _⟩ :=
    laterCollectionReadout_call 0 record cell hcell
  have ht := collection_call_tailArgs record ⟨payload, ledger, started, weights⟩ hcall
  rw [record.output_eq] at ht
  change tailArgs (prepare record.input).coordinator = _ at ht
  have ht' := (congrArg Prod.snd (fastInput_dispatch_tail record.input f)).symm.trans ht
  change tailArgs (prepare (fastInput record.input f)).coordinator = _ at ht'
  rw [observeCoordinator_tail_formula, observeCoordinator_tail_formula, ht, ht']
  exact fastInput_collection_postChoice record.input f (fastInput_arm record cell hcell f)
    payload ledger started weights

private theorem numericalCoordinates_injective : Function.Injective
    (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (p := p)) := by
  intro a b h
  cases a
  cases b
  simp only [ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private def recordTags (r : Record) : Bool × Bool :=
  (cutoffChosen r.input, laterChosen r.input)

private theorem takeWhile_position_congr {α : Type*} (test : α → Bool) (R S : List α) (n : ℕ)
    (h : (R.take (n + 1)).map test = (S.take (n + 1)).map test) :
    n < (R.takeWhile test).length ↔ n < (S.takeWhile test).length := by
  induction n generalizing R S with
  | zero =>
    cases R <;> cases S <;> simp_all [List.takeWhile]
    split <;> simp_all
  | succ n ih =>
    cases R with
    | nil => cases S <;> simp_all
    | cons r R =>
      cases S with
      | nil => simp at h
      | cons s S =>
        have hh := List.cons.inj (by simpa only [List.take_succ_cons, List.map_cons] using h)
        cases hr : test r <;> simp [hr, ← hh.1, ih R S hh.2]

private theorem collection_position_transfer (R S : List (Record))
    (n : ℕ) (hR : n < R.length) (hS : n < S.length)
    (htags : (R.take (n + 1)).map recordTags = (S.take (n + 1)).map recordTags)
    (hin : (firstLiveWindow R).length ≤ n ∧
    n < (firstLiveWindow R).length + (collectionWindow R (firstLiveWindow R).length).length) :
    (firstLiveWindow R).length = (firstLiveWindow S).length ∧ (firstLiveWindow S).length ≤ n ∧
    n < (firstLiveWindow S).length + (collectionWindow S (firstLiveWindow S).length).length := by
  induction n generalizing R S with
  | zero =>
    cases R with
    | nil => simp at hR
    | cons r R =>
      cases S with
      | nil => simp at hS
      | cons s S =>
        have he := congrArg (fun L => L.head?) htags
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.head?_cons,
          Option.some.injEq] at he
        have hc := congrArg Prod.fst he
        cases hr : cutoffChosen r.input <;>
          simp_all [firstLiveWindow, List.takeWhile, recordTags, collectionWindow]
  | succ n ih =>
    cases R with
    | nil => simp at hR
    | cons r R =>
      cases S with
      | nil => simp at hS
      | cons s S =>
        have he := List.cons.inj (by simpa only [List.take_succ_cons, List.map_cons] using htags)
        have hc : cutoffChosen r.input = cutoffChosen s.input := congrArg Prod.fst he.1
        cases hr : cutoffChosen r.input with
        | false =>
          have hs : cutoffChosen s.input = false := hc.symm.trans hr
          have hrest : (firstLiveWindow R).length ≤ n ∧
              n < (firstLiveWindow R).length + (collectionWindow R (firstLiveWindow R).length).length := by
            simp [firstLiveWindow, List.takeWhile, hr, collectionWindow, Nat.add_assoc] at hin ⊢
            omega
          have h := ih R S (by simpa using hR) (by simpa using hS) he.2 hrest
          simp [firstLiveWindow, List.takeWhile, hr, hs, collectionWindow, Nat.add_assoc] at h ⊢
          omega
        | true =>
          have hs : cutoffChosen s.input = true := hc.symm.trans hr
          have hm := congrArg (List.map Prod.snd) he.2
          simp only [List.map_map, Function.comp_def, recordTags] at hm
          have hmNot : (R.take (n + 1)).map (fun r => !laterChosen r.input) =
              (S.take (n + 1)).map (fun r => !laterChosen r.input) := by
            simpa only [List.map_map, Function.comp_def] using congrArg (List.map Bool.not) hm
          have hi := (takeWhile_position_congr (fun (r : Record) =>
              !laterChosen r.input) R S n hmNot).mp
          have hn : n < (R.takeWhile (fun r => !laterChosen r.input)).length := by
            simpa [firstLiveWindow, List.takeWhile, hr, collectionWindow] using hin.2
          simpa [firstLiveWindow, List.takeWhile, hr, hs, collectionWindow] using
            (show 0 = 0 ∧ 0 ≤ n + 1 ∧ n < (S.takeWhile (fun r => !laterChosen r.input)).length from
              ⟨rfl, Nat.zero_le _, hi hn⟩)

private theorem collectionWindow_lookup (R : List (Record))
    (w j : ℕ) (hj : j < (collectionWindow R w).length) :
    R[w + j]? = some ((collectionWindow R w)[j]) := by
  have hp : collectionWindow R w <+: R.drop w := by
    refine ⟨(R.drop (w + 1)).dropWhile (fun r => !laterChosen r.input), ?_⟩
    rw [collectionWindow, List.append_assoc, List.takeWhile_append_dropWhile]
    simp
  have h := hp.getElem hj
  rw [List.getElem_drop] at h
  rw [List.getElem?_eq_getElem (by have hb := hp.length_le; simp only [List.length_drop] at hb; omega)]
  exact congrArg some h.symm

private theorem record_date (z : SourceInput p) (j : ℕ) (r : Record)
    (hr : (sourceRecords z)[j]? = some r) : r.input.time.val = sourceStart z + j := by
  have hj := (List.getElem?_eq_some_iff.mp hr).1
  have hb : j < p.T - sourceStart z := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hj
  have h := congrArg (fun L : List ℕ => L[j]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h)
  simp only [List.getElem?_map, hr, Option.map_some, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range' hb, Nat.one_mul] at h
  exact Option.some.inj h

/-- The actual first-collection domain is stable through the current date.
Only prefix tags through `t` enter the comparison; no future endpoint is supplied. -/
theorem firstCollection_currentFast_domain (t : Fin p.T) (source : SourceInput p)
    (v : Fin p.T) (hvt : v.val ≤ t.val) (record : Record)
    (hrecord : actualRecord rate rewards C_star C_h v source = some record)
    (hmem : record ∈ collectionRecords source) (f : Scalar) :
    ∃ inserted, actualRecord rate rewards C_star C_h v (insertCurrentFastScalar t source f) = some inserted ∧
    inserted ∈ collectionRecords (insertCurrentFastScalar t source f) ∧
    (firstLiveWindow (sourceRecords (insertCurrentFastScalar t source f))).length =
    (firstLiveWindow (sourceRecords source)).length := by
  let z' := insertCurrentFastScalar t source f
  let R := sourceRecords source
  let S := sourceRecords z'
  let start := sourceStart source
  let n := v.val - start
  let control0 := record.input.row.2 t
  obtain ⟨inserted, hi, _⟩ := actualRecord_fastInputAt rewards C_star C_h t source f v hvt record hrecord
  have hby : actualLaunchBy rate rewards C_star C_h v.val source := by
    by_contra hn
    rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h v source hn] at hrecord
    cases hrecord
  have hp := sourcePrefix_strictPast_insert_eq control0 t source f
  have hby' : actualLaunchBy rate rewards C_star C_h v.val z' := by
    by_contra hn
    rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h v z' hn] at hi
    cases hi
  have hs : sourceStart z' = start := by
    have ha := (sourcePrefix_preserves_actual_launch rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) source ⟨hby.1, hby.2.trans hvt⟩).1
    have hb := (sourcePrefix_preserves_actual_launch rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) z' ⟨hby'.1, hby'.2.trans hvt⟩).1
    rw [hp] at hb
    exact hb.trans ha.symm
  have hr : R[n]? = some record := by
    simpa only [actualRecord, ite_eq_left hby.2] using hrecord
  have hsi : S[n]? = some inserted := by
    have h := hi
    change actualRecord rate rewards C_star C_h v z' = some inserted at h
    rw [actualRecord, ite_eq_left hby'.2, hs] at h
    exact h
  have hR := (List.getElem?_eq_some_iff.mp hr).1
  have hS := (List.getElem?_eq_some_iff.mp hsi).1
  have htags : (R.take (n + 1)).map recordTags = (S.take (n + 1)).map recordTags := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.succ_le_iff.mpr hR),
      Nat.min_eq_left (Nat.succ_le_iff.mpr hS)]
    · intro j hj hj'
      have hjn : j < n + 1 := by
        simpa only [List.length_map, List.length_take, Nat.min_eq_left (Nat.succ_le_iff.mpr hR)] using hj
      have hjR : j < R.length := by omega
      have hjS : j < S.length := by omega
      let q : Fin p.T := ⟨start + j, by have ht := v.isLt; have hb := hby.2; dsimp [n, start] at *; omega⟩
      have hv : q.val ≤ v.val := by have hb := hby.2; dsimp [q, n, start] at *; omega
      have hrj : actualRecord rate rewards C_star C_h q source = some (R[j]) := by
        rw [actualRecord, ite_eq_left (by dsimp [q]; omega)]
        change R[(start + j) - start]? = _
        rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hjR]
      have hsj : actualRecord rate rewards C_star C_h q z' = some (S[j]) := by
        rw [actualRecord, ite_eq_left (by rw [hs]; dsimp [q]; omega), hs]
        change S[(start + j) - start]? = _
        rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hjS]
      have ht := insertCurrentFastScalar_prefix_tags_eq (rate := rate) rewards C_star C_h t source f q (hv.trans hvt)
      rw [hrj, hsj] at ht
      simpa only [List.getElem_map, List.getElem_take, recordTags] using (Option.some.inj ht).symm
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hmem
  change j < (collectionWindow R (firstLiveWindow R).length).length at hj
  have hl := collectionWindow_lookup R (firstLiveWindow R).length j hj
  rw [he] at hl
  have hd := record_date rewards C_star C_h source _ record hl
  have ht := (actualRecord_fields rewards C_star C_h v source record hrecord).2.2.1
  have hn : (firstLiveWindow R).length + j = n := by
    rw [ht] at hd
    change v.val = start + ((firstLiveWindow R).length + j) at hd
    dsimp only [n]
    omega
  obtain ⟨hw, hlow, hupp⟩ := collection_position_transfer R S n hR hS htags (by omega)
  let k := n - (firstLiveWindow S).length
  have hk : k < (collectionWindow S (firstLiveWindow S).length).length := by dsimp [k]; omega
  have hl' := collectionWindow_lookup S (firstLiveWindow S).length k hk
  have hnk : (firstLiveWindow S).length + k = n := by dsimp [k]; omega
  rw [hnk, hsi] at hl'
  refine ⟨inserted, hi, ?_, hw.symm⟩
  rw [Option.some.inj hl']
  exact List.getElem_mem hk

private theorem collectionReadout_not_live (r : Record) (cell : RecordedQueueRun.RoundInput p.K)
    (hc : laterCollectionReadout 0 r = some cell) : ¬ laterLiveDomain 0 r := by
  obtain ⟨selected, hs, hb⟩ := collectionReadout_selection_cutoff r cell hc
  rintro ⟨other, ho, _, hlive, _⟩
  have he := Option.some.inj (ho.symm.trans hs)
  subst other
  exact Nat.not_lt_of_ge hb hlive.2

/-- Actual complete physical observations and successor under only the current
selected-row FAST insertion. The raw input rows are intentionally different. -/
theorem firstCollection_currentFast_recordCode_eq (t : Fin p.T) (source : SourceInput p)
    (record : Record) (hrecord : actualRecord rate rewards C_star C_h t source = some record)
    (hmem : record ∈ collectionRecords source) (f : Scalar) :
    ∃ inserted, actualRecord rate rewards C_star C_h t
    (insertCurrentFastScalar t source f) = some inserted ∧
    roundRecordCode inserted = roundRecordCode record ∧ inserted.output.next = record.output.next ∧
    inserted.evidence = record.evidence ∧
    laterCollectionCall 0 inserted = laterCollectionCall 0 record ∧
    laterCollectionReadout 0 inserted = laterCollectionReadout 0 record ∧
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate inserted =
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record := by
  obtain ⟨cell, hcell⟩ := firstCollection_actual_collectionReadout rewards C_star C_h source record hmem
  obtain ⟨inserted, hi, hx⟩ := actualRecord_fastInput rewards C_star C_h t source record hrecord f
  have ha := fastInput_arm record cell hcell f
  obtain ⟨hactions, hfeedback⟩ := fastInput_actions_feedback record.input f ha
  have hcoordinator := fastInput_collection_coordinator record cell hcell f
  have hfollowers := fastInput_followers record.input f ha
  have he : (step record.input).ownEntries = (step (fastInput record.input f)).ownEntries := by
    funext player
    rw [step_own_entry, step_own_entry, hactions, hfeedback]
  have hn := congrArg₂ (fun (c : CoordinatorObservation p rate)
      (fs : Fin (p.m - 1) → FollowerObservation p rate) =>
      State.mk c.configuration c.upDecoderBank
        record.input.state.activations (fun i => (fs i).configuration))
      hcoordinator.symm hfollowers.symm
  have hevidence : inserted.evidence = record.evidence := by
    unfold RoundRecord.evidence RoundRecord.actions RoundRecord.gridFeedback RoundRecord.ownEntries
      RoundRecord.coordinatorDiagnostics RoundRecord.followerDiagnostics
    rw [inserted.output_eq, record.output_eq, hx]
    congr 1 <;> first
      | exact hactions.symm
      | exact hfeedback.symm
      | exact he.symm
      | exact hcoordinator.symm
      | exact hfollowers.symm
  obtain ⟨same, hs, hmem', _⟩ := firstCollection_currentFast_domain
    rewards C_star C_h t source t le_rfl record hrecord hmem f
  have heq : same = inserted := Option.some.inj (hs.symm.trans hi)
  subst same
  obtain ⟨newCell, hnewCell⟩ := firstCollection_actual_collectionReadout
    rewards C_star C_h (insertCurrentFastScalar t source f) inserted hmem'
  have hdataFull := Prod.ext (fastInput_arm record cell hcell f) (fastInput_dispatch_tail record.input f)
  have hselection := congrArg selectionCodeFromDispatchData hdataFull
  unfold dispatchData at hselection
  rw [← selectionCode_eq_of_cutData, ← selectionCode_eq_of_cutData] at hselection
  have hphysical : physicalCode record.input = physicalCode (fastInput record.input f) := by
    unfold physicalCode
    rw [hselection, hactions, hfeedback, hcoordinator]
    exact congrArg (fun view => (_, view, _, _, _)) (congrArg Prod.fst (fastInput_dispatch_tail record.input f))
  have hcode : roundRecordCode inserted = roundRecordCode record := by
    unfold roundRecordCode
    rw [hx]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    unfold wholeStepCode
    refine Prod.ext hphysical.symm (Prod.ext (funext (fastInput_followerCode record.input f
      (fastInput_arm record cell hcell f))) ?_)
    exact congrArg encodeState hn
  obtain ⟨payload, ledger, started, weights, out, hcall, _⟩ :=
    laterCollectionReadout_call 0 record cell hcell
  obtain ⟨payload', ledger', started', weights', out', hcall', _⟩ :=
    laterCollectionReadout_call 0 inserted newCell hnewCell
  have htail : tailArgs record.output.preparation.coordinator =
      tailArgs inserted.output.preparation.coordinator := by
    rw [record.output_eq, inserted.output_eq, hx]
    exact congrArg Prod.snd (fastInput_dispatch_tail record.input f)
  have hargs := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
    ((collection_call_tailArgs record _ hcall).symm.trans
      (htail.trans (collection_call_tailArgs inserted _ hcall')))))
  have hcalls := hcall'.trans ((congrArg some hargs.symm).trans hcall.symm)
  have hread : laterCollectionReadout 0 inserted = laterCollectionReadout 0 record := by
    apply Option.map_injective numericalCoordinates_injective
    rw [ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization,
      ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization]
    simp only [hnewCell, hcell, Option.isSome_some, ite_true, hcode]
    rw [hx]
    rfl
  refine ⟨inserted, hi, hcode, congrArg RoundEvidence.after hevidence, hevidence, hcalls, hread, ?_⟩
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, (laterLiveReadout_eq_none_iff 0
    inserted).mpr (collectionReadout_not_live inserted newCell hnewCell), (laterLiveReadout_eq_none_iff
    0 record).mpr (collectionReadout_not_live record cell hcell), Option.none_or, hread]

open Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate (cell0 pastSlots pastCells?)

private theorem cell0_coordinates (r : Record) :
    (cell0 rate r).map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
    (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ = (laterLiveReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ = (laterCollectionReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hr
  rw [← hl, ← hr]
  cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some value => cases value <;> rfl

private theorem slotCoordinates_eq_datePrefix (t : Fin p.T) (z : SourceInput p) :
    (pastSlots rate rewards C_star C_h t z).map
    (Option.map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates) =
    (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
    (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z)).map (fun e => e.2.2.map (Sum.elim id id)) := by
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take rate rewards C_star C_h t.val
    (Nat.le_of_lt t.isLt)]
  simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.map_take, List.map_map,
    Function.comp_def]
  let R := sourceRecords z
  let n := t.val - sourceStart z
  have hn : n ≤ R.length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact Nat.sub_le_sub_right (Nat.le_of_lt t.isLt) _
  apply List.ext_getElem
  · simp only [pastSlots, List.length_map, List.length_range, List.length_take]
    exact (Nat.min_eq_left hn).symm
  · intro k hk hk'
    have hkR : k < R.length := by
      have hkn : k < n := by
        have h := hk'
        simp only [List.length_map, List.length_take] at h
        exact lt_of_lt_of_le h (Nat.min_le_left _ _)
      omega
    simp only [pastSlots, List.getElem_map, List.getElem_range, List.getElem_take]
    change (R[k]?.bind (cell0 rate)).map _ = _
    rw [List.getElem?_eq_getElem hkR, Option.bind_some]
    exact cell0_coordinates _

/-- Every strict-past numerical cell is preserved under the current insertion,
including all absent-launch and absent-cell cases. -/
theorem insertCurrentFastScalar_pastCells_eq (control0 : TimeControl p) (t : Fin p.T)
    (source : SourceInput p) (f : Scalar) :
    pastCells? rate rewards C_star C_h t (insertCurrentFastScalar t source f) =
    pastCells? rate rewards C_star C_h t source := by
  have hp := sourcePrefix_strictPast_insert_eq control0 t source f
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val (insertCurrentFastScalar t source f) ↔
      actualLaunchBy rate rewards C_star C_h t.val source := by
    have hi := actualLaunchBy_factor
      rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) (insertCurrentFastScalar t source f)
    have hs := actualLaunchBy_factor rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) source
    rw [hp] at hi
    exact hi.trans hs.symm
  unfold pastCells?
  by_cases hl : actualLaunchBy rate rewards C_star C_h t.val source
  · rw [ite_eq_left hl, ite_eq_left (hlaunch.mpr hl)]
    have he := ReferenceCompleteObservationPrefixInformation.datePrefix_factor
      rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) source
    have he' := ReferenceCompleteObservationPrefixInformation.datePrefix_factor
      rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) (insertCurrentFastScalar t source f)
    rw [hp] at he'
    have hcoords := congrArg (fun L => L.map (fun e => e.2.2.map (Sum.elim id id))) (he'.trans he.symm)
    rw [← slotCoordinates_eq_datePrefix, ← slotCoordinates_eq_datePrefix] at hcoords
    have hslots := List.map_injective_iff.mpr (Option.map_injective numericalCoordinates_injective) hcoords
    rw [hslots]
  · rw [ite_eq_right hl, ite_eq_right (fun h => hl (hlaunch.mp h))]

end Bandits.Support.ReferenceFirstCollectionFastErasure

end
