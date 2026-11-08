/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

import Lean.Elab.Tactic.Omega

/-!
# Partial numerical readout for later collection rounds

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`,
`sources/zip4/manuscript/08_main_theorem.tex:26-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.

This module reads only actual later collection and later cutoff-choice
constructors. Missing branches remain absent from the partial calendar. Its
numerical input is computed from the actual selection, current complement
weights, complete row, and collection recorder map. Next consumers are
collection numerical replay after actual ready domains, and
`ReferenceCompleteCalendarArrivalCells` after missing total branch coverage.
No global queue truth, physical overflow, recording law, or manuscript closure
is established here.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceLaterCollectionArrivalReadout

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev RewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
variable {p : Parameters} {rate : RateInput p}
abbrev RoundRecord := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- Whether every actual follower PREPARE configuration is ordinary and its
actual state is unoccupied. Dagger is deliberately outside this domain. -/
def preparedFollowersUnoccupied (record : RoundRecord (p := p) (rate := rate)) : Prop :=
  ∀ i, match (record.output.preparation.followers.followers i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False

/-- Each admitted follower configuration determines its own state and
memory; the unoccupied-domain proof excludes dagger. -/
theorem actualFollowerParts_exists
    (record : RoundRecord (p := p) (rate := rate))
    (hunoccupied : preparedFollowersUnoccupied record)
    (i : Fin (p.m - 1)) :
    ∃ pair : ReferencePrelaunchFollower.State p rate.eta ×
      ActiveFollowerLifecycle.LocalMemory p,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary pair.1 pair.2 ∧ pair.1.status = .unoccupied := by
  cases hconfig : (record.output.preparation.followers.followers i).configuration with
  | dagger =>
      have hfalse : False := by
        have hi := hunoccupied i
        rw [hconfig] at hi
        exact hi
      exact False.elim hfalse
  | ordinary state memory =>
      exact ⟨(state, memory), by simp,
        by simpa [preparedFollowersUnoccupied, hconfig] using hunoccupied i⟩

/-- The state and memory exposed by each actual ordinary PREPARE constructor. -/
def actualFollowerParts
    (record : RoundRecord (p := p) (rate := rate))
    (hunoccupied : preparedFollowersUnoccupied record)
    (i : Fin (p.m - 1)) :
    ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p :=
  match h : (record.output.preparation.followers.followers i).configuration with
  | .ordinary state memory => (state, memory)
  | .dagger => False.elim (by
      have hi := hunoccupied i
      rw [h] at hi
      exact hi)

/-- The extracted pair reproduces the actual ordinary configuration and its
actual unoccupied status. -/
theorem actualFollowerParts_spec
    (record : RoundRecord (p := p) (rate := rate))
    (hunoccupied : preparedFollowersUnoccupied record)
    (i : Fin (p.m - 1)) :
    (record.output.preparation.followers.followers i).configuration =
        .ordinary (actualFollowerParts record hunoccupied i).1
          (actualFollowerParts record hunoccupied i).2 ∧
      (actualFollowerParts record hunoccupied i).1.status = .unoccupied := by
  unfold actualFollowerParts
  split
  next state memory h =>
    exact ⟨h, by simpa only [preparedFollowersUnoccupied, h] using hunoccupied i⟩
  next h =>
    have hi := hunoccupied i
    rw [h] at hi
    exact False.elim hi

/-- On collection mode, the whole recorder map is exactly the existing
coordinator-source projection. This equality includes the `none` cases. -/
theorem collectionRecordingMap_eq_projection
    (payload : Payload rate)
    (input : CoordinatorRecorderComplementBridge.Input payload)
    (valid : CoordinatorRecordingOperation.InputsValid
      (CoordinatorRecorderComplementBridge.recorderInput input))
    (enabled : Bool) :
    SnapshotRecordingKernel.recordingMap p .collection enabled
      (CoordinatorRecorderComplementBridge.recorderInput input).eta
      valid.eta_pos valid.eta_source_cap
      (CoordinatorRecorderComplementBridge.recorderInput input).anchor
      (CoordinatorRecorderComplementBridge.recorderInput input).currentWeights
      valid.anchor_pos valid.current_pos valid.anchor_le_current
      valid.current_le_twice_anchor
      (ContinuousLearningRows.sliceAt
        (CoordinatorRecorderComplementBridge.recorderInput input).time
        (CoordinatorRecorderComplementBridge.recorderInput input).row.2) =
    CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
      (CoordinatorRecorderComplementBridge.recorderInput input) valid enabled := by
  unfold CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
  by_cases hsource : CoordinatorRecordingOperation.selectedRecorder
      (CoordinatorRecorderComplementBridge.recorderInput input) =
        ActiveRoundActions.coordinator p.two_le_m
  · simp [hsource]
  · have hmap : SnapshotRecordingKernel.recordingMap p .collection enabled
        (CoordinatorRecorderComplementBridge.recorderInput input).eta
        valid.eta_pos valid.eta_source_cap
        (CoordinatorRecorderComplementBridge.recorderInput input).anchor
        (CoordinatorRecorderComplementBridge.recorderInput input).currentWeights
        valid.anchor_pos valid.current_pos valid.anchor_le_current
        valid.current_le_twice_anchor
        (ContinuousLearningRows.sliceAt
          (CoordinatorRecorderComplementBridge.recorderInput input).time
          (CoordinatorRecorderComplementBridge.recorderInput input).row.2) = none := by
      let slice := ContinuousLearningRows.sliceAt
        (CoordinatorRecorderComplementBridge.recorderInput input).time
        (CoordinatorRecorderComplementBridge.recorderInput input).row.2
      change SnapshotRecordingKernel.recordingMap p .collection enabled
        (CoordinatorRecorderComplementBridge.recorderInput input).eta
        valid.eta_pos valid.eta_source_cap
        (CoordinatorRecorderComplementBridge.recorderInput input).anchor
        (CoordinatorRecorderComplementBridge.recorderInput input).currentWeights
        valid.anchor_pos valid.current_pos valid.anchor_le_current
        valid.current_le_twice_anchor slice = none
      cases hrecord : SnapshotRecordingKernel.recordingMap p .collection enabled
          (CoordinatorRecorderComplementBridge.recorderInput input).eta
          valid.eta_pos valid.eta_source_cap
          (CoordinatorRecorderComplementBridge.recorderInput input).anchor
          (CoordinatorRecorderComplementBridge.recorderInput input).currentWeights
          valid.anchor_pos valid.current_pos valid.anchor_le_current
          valid.current_le_twice_anchor slice with
      | none => rfl
      | some arm =>
          have henabled : enabled = true := by
            by_contra hne
            simp [SnapshotRecordingKernel.recordingMap, hne] at hrecord
          have htests := (SnapshotRecordingKernel.recordingMap_some_iff p .collection
            (CoordinatorRecorderComplementBridge.recorderInput input).eta
            valid.eta_pos valid.eta_source_cap
            (CoordinatorRecorderComplementBridge.recorderInput input).anchor
            (CoordinatorRecorderComplementBridge.recorderInput input).currentWeights
            valid.anchor_pos valid.current_pos valid.anchor_le_current
            valid.current_le_twice_anchor slice arm).mp (by
              simpa [henabled] using hrecord)
          rcases htests with ⟨_, _, howns, _, _⟩
          have hrecorder : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec slice) =
              ActiveRoundActions.coordinator p.two_le_m := by
            simpa [SnapshotRecordingKernel.owns] using howns
          exact False.elim (hsource (by
            simpa [CoordinatorRecordingOperation.selectedRecorder, slice] using hrecorder))
    simpa [hsource] using hmap

/-- Apply the continuing-collection identification theorem to the actual
record's continuing constructor and its actual ordinary, unoccupied PREPARE
configurations. -/
theorem continuingCollectionRecorderOutput
    (record : RoundRecord (p := p) (rate := rate)) (_s : Nat)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) = true)
    (hbranch : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores))
    (hunoccupied : preparedFollowersUnoccupied record) :
    let source := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
    let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
    let input := ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare record.input) payload snapshot.clockStarted weights
    let operationInput := CoordinatorRecorderComplementBridge.recorderInput input
    let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨boundary, fun j => ⟨snapshot.inputsValid.choice_valid.anchor_le_current j,
        snapshot.inputsValid.choice_valid.current_le_twice_anchor j⟩⟩
    let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen operationInput)
    let E := CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
      operationInput valid enabled
    (∃ out, CoordinatorRecorderComplementBridge.run input = some out ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = E ∧
      out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
        payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (record.input.rewards record.input.time j)) E) ∧
      enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time := by
  classical
  let states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => (actualFollowerParts record hunoccupied i).1
  let memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun i => (actualFollowerParts record hunoccupied i).2
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
    rw [← hprepared]
    exact hbranch
  have hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    have hparts := (actualFollowerParts_spec record hunoccupied i).1
    rw [hprepared] at hparts
    exact hparts
  have hstatus : ∀ i, (states i).status = .unoccupied := by
    intro i
    exact (actualFollowerParts_spec record hunoccupied i).2
  have hidentified := ReferenceCoordinatorCollectionRecording.continuing_collection_recording_identification
    (x := record.input) payload ledger clock cutoff core snapshot boundary scores hcut states memories
    hordinary hstatus
  dsimp only at hidentified ⊢
  rcases hidentified with ⟨⟨out, hrun, hstep, hgate, hraw⟩, henabled⟩
  refine ⟨⟨out, hrun, ?_, hgate, hraw⟩, henabled⟩
  unfold ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics
  rw [record.output_eq]
  exact hstep

/-- Apply the cutoff-recording identification to the literal later-cutoff
constructor. The first-cutoff caller remains outside this readout; this branch
requires the actual payload's strict later-cutoff time test. -/
theorem laterCutoffCollectionRecorderOutput
    (record : RoundRecord (p := p) (rate := rate)) (s : Nat)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).clockPending =
        .ok dispatched.startResult)
    (newLedger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time))
    (hinit : dispatched.collectionInitialization = .success (some newLedger))
    (hcand : newLedger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base record.input.time)
    (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base record.input.time)
    (hclock : dispatched.startResult.clock =
      { (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).priorClock with
        u := some (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).time })
    (hpending : dispatched.startResult.pending = Finset.univ)
    (hnone : dispatched.startResult.assignmentStart = none)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
      record.input.row)
    (hbranch : record.output.preparation.coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selected))
    (hunoccupied : preparedFollowersUnoccupied record)
    (_hlater : s < registers.payload.sigma.val) :
    let weights := (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
    let input := ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare record.input) registers.payload dispatched.startResult weights
    let operationInput := CoordinatorRecorderComplementBridge.recorderInput input
    let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨selected.recorderBoundaryValid, fun j =>
        ⟨selected.choiceInputsValid.anchor_le_current j,
          selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
    let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen operationInput)
    let E := CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
      operationInput valid enabled
    (∃ out, CoordinatorRecorderComplementBridge.run input = some out ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = E ∧
      out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
        registers.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (record.input.rewards record.input.time j)) E) ∧
      enabled = ReferenceActivePhysicalStep.collectionEnabled
        (ReferenceActivePhysicalStep.sharedLedger newLedger) record.input.time := by
  classical
  let states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => (actualFollowerParts record hunoccupied i).1
  let memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun i => (actualFollowerParts record hunoccupied i).2
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selected) := by
    rw [← hprepared]
    exact hbranch
  have hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    have hparts := (actualFollowerParts_spec record hunoccupied i).1
    rw [hprepared] at hparts
    exact hparts
  have hstatus : ∀ i, (states i).status = .unoccupied := by
    intro i
    exact (actualFollowerParts_spec record hunoccupied i).2
  have hidentified := ReferenceCoordinatorCollectionRecording.cutoff_recording_identification
    (x := record.input) registers owned base dispatched hstart newLedger hinit hcand hdomain
    hclock hpending hnone selected hcut states memories hordinary hstatus
  dsimp only at hidentified ⊢
  rcases hidentified with ⟨⟨out, hrun, hstep, hgate, hraw⟩, henabled⟩
  refine ⟨⟨out, hrun, ?_, hgate, hraw⟩, henabled⟩
  unfold ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics
  rw [record.output_eq]
  exact hstep

/-- The checked stage-one attempt made from one retained recorder output.
The option-to-raw conversion preserves `some (arm, 0)` distinctly from `none`.
-/
def stageOneAttempt
    (ledger : Ledger rate) (time : Fin p.T) (enabled : Bool)
    (out : CoordinatorRecordingOperation.Output p) :=
  CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)

/-- The literal result of stage one is invalid, rejected, or successful. On
success the returned ledger is exactly the source candidate, not a later
receive or finish result. -/
theorem stageOneAttempt_cases
    (ledger : Ledger rate) (time : Fin p.T) (enabled : Bool)
    (out : CoordinatorRecordingOperation.Output p) :
    stageOneAttempt ledger time enabled out = .invalid ∨
      (∃ rejected, stageOneAttempt ledger time enabled out = .rejected rejected) ∨
      ∃ started, stageOneAttempt ledger time enabled out = .success started ∧
        started = CoordinatorCollectionLedger.startRoundCandidate ledger time enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) := by
  classical
  cases hresult : stageOneAttempt ledger time enabled out with
  | invalid => exact Or.inl rfl
  | rejected rejected => exact Or.inr (Or.inl ⟨rejected, rfl⟩)
  | success started =>
      have hstart : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) =
            .success started := by
        simpa [stageOneAttempt] using hresult
      have hcand := CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
        ledger (time.val + 1) (by omega) (by omega) enabled
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) started hstart
      exact Or.inr (Or.inr ⟨started, rfl, by simpa [stageOneAttempt] using hcand⟩)

/-- A known queue in the actual stage-one candidate receives the exact
capacity-`4*n` queue transition on the routed local arrival and service flag.
-/
theorem stageOneCandidate_known_transition
    (ledger : Ledger rate) (time : Fin p.T) (enabled : Bool)
    (out : CoordinatorRecordingOperation.Output p) (a : Fin p.K)
    (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : ledger.currentRegisters a = some current) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)).currentRegisters a =
      some ⟨(QueueReplay.transition (4 * rate.n) (0, current.queue)
          (CoordinatorCollectionLedger.localQueueRecord ledger time enabled
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)).2,
        (QueueReplay.transition (4 * rate.n) (0, current.queue)
          (CoordinatorCollectionLedger.localQueueRecord ledger time enabled
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)).1⟩ := by
  exact CoordinatorCollectionLedger.startRoundCandidate_known_transition ledger time enabled
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a current hknown

/-- Unknown queues accrue zero local service at stage one. -/
theorem stageOneCandidate_unknown_zero
    (ledger : Ledger rate) (time : Fin p.T) (enabled : Bool)
    (out : CoordinatorRecordingOperation.Output p) (a : Fin p.K)
    (hunknown : ledger.currentRegisters a = none) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)).gammaLoc a = 0 :=
  CoordinatorCollectionLedger.startRoundCandidate_unknown_zero ledger time enabled
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a hunknown

/-- Only a genuine positive raw arrival to a pre-freeze unknown arm is
inserted in that arm's current source-calendar cell. -/
theorem stageOneCandidate_unknown_positive_buffer
    (ledger : Ledger rate) (time : Fin p.T) (enabled : Bool)
    (out : CoordinatorRecordingOperation.Output p) (a : Fin p.K) (amount : ℕ)
    (hraw : CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out =
      some (a, amount)) (hunknown : ledger.currentRegisters a = none)
    (hpositive : 0 < amount)
    (hbefore : CoordinatorCollectionLedger.sourceRound time < ledger.freezeAt) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)).rawBuffer a time =
      some amount := by
  rw [hraw]
  exact CoordinatorCollectionLedger.startRoundCandidate_rawBuffer_positive
    ledger time enabled a amount hunknown hpositive hbefore

/-- The recorder's option output routes exactly the canonical numerical
arrival on every arm. `some arm` is preserved even when its floor is zero. -/
theorem rawInput_localArrival_eq_quantizedArrival
    (payload : Payload rate) (round : RecordedQueueRun.RoundInput p.K)
    (out : CoordinatorRecordingOperation.Output p) (E : Option (Fin p.K))
    (reward : Fin p.K → ℝ)
    (hgate : out.gateArm = round.recordedArm)
    (hmap : round.recordedArm = E)
    (hreward : round.reward = reward)
    (hrate : ∀ a, round.rate a = payload.rate a)
    (hraw : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
      payload.anchor reward E) :
    ∀ a, CoordinatorCollectionLedger.localArrival
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) round a := by
  classical
  intro a
  cases hselected : out.gateArm with
  | none =>
      have hrecorded : round.recordedArm = none := by
        simpa [hselected] using hgate.symm
      simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        CoordinatorCollectionLedger.localArrival, RecordedQueueRun.quantizedArrival,
        hselected, hrecorded]
  | some arm =>
      have hrecorded : round.recordedArm = some arm := by
        simpa [hselected] using hgate.symm
      have hE : E = some arm := hmap.symm.trans hrecorded
      have hrawFloor : out.rawArrival =
          Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n *
            round.reward arm / round.rate arm) := by
        calc
          out.rawArrival = Nat.floor
              ((D p : ℝ) * rate.eta.val * round.reward arm / round.rate arm) := by
            rw [hraw, hE, SnapshotRecordingKernel.recordedIncrement]
            rw [← congrFun hreward arm, ← payload.rate_eq_canonical arm, ← hrate arm]
          _ = Nat.floor
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n *
                round.reward arm / round.rate arm) := by
            congr 1
            rw [(ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D]
            simp only [ReferenceFirstLaunchNumericalCell.queueParameters]
            ring
      by_cases hsame : arm = a
      · subst a
        have hlocal : CoordinatorCollectionLedger.localArrival
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
              out.rawArrival := by
          simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
            CoordinatorCollectionLedger.localArrival, hselected]
        rw [hlocal, hrawFloor]
        exact (RecordedQueueRun.quantizedArrival_eq_floor
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) round arm hrecorded).symm
      · have hlocal : CoordinatorCollectionLedger.localArrival
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a = 0 := by
          simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
            CoordinatorCollectionLedger.localArrival, hselected, hsame]
        rw [hlocal]
        exact (RecordedQueueRun.quantizedArrival_eq_zero
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) round a (by
            intro heq
            exact hsame (Option.some.inj (hrecorded.symm.trans heq)))).symm

/-- Construct the canonical whole-arm numerical input on an actual continuing
collection constructor. -/
def continuingCollectionInput
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) :
    RecordedQueueRun.RoundInput p.K := by
  classical
  let x := record.input
  let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  let complement := CoordinatorCollectionInteractive.PreObservationInputs.weights source
    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
  let choice := snapshot.inputsValid.choice_valid
  let u := some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)
  let W := ReferenceFirstWindowNumericalStream.sourceWeights payload complement
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation payload snapshot.clockStarted complement
  let recorderInput := CoordinatorRecorderComplementBridge.recorderInput recordingInput
  let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen recorderInput)
  exact {
    enabled := enabled
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection enabled
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor W
      payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos payload complement u x.time
        (by simpa [source, u, complement,
          ReferenceActivePhysicalStep.collectionInput,
          CoordinatorCollectionInteractive.PreObservationInputs.weights,
          CoordinatorCollectionUpRoundStep.Inputs.weights] using choice))
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower payload complement u x.time
        (by simpa [source, u, complement,
          ReferenceActivePhysicalStep.collectionInput,
          CoordinatorCollectionInteractive.PreObservationInputs.weights,
          CoordinatorCollectionUpRoundStep.Inputs.weights] using choice))
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper payload complement u x.time
        (by simpa [source, u, complement,
          ReferenceActivePhysicalStep.collectionInput,
          CoordinatorCollectionInteractive.PreObservationInputs.weights,
          CoordinatorCollectionUpRoundStep.Inputs.weights] using choice))
      (ContinuousLearningRows.sliceAt x.time x.row.2)
    reward := fun a => ((x.rewards x.time a).val : ℝ) / (D p : ℝ)
    rate := payload.rate
    reward_nonneg := by
      intro a
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro a
      have hvalue : (x.rewards x.time a).val ≤ D p :=
        Nat.le_of_lt_succ (x.rewards x.time a).isLt
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast hvalue
    rate_pos := by
      intro a
      exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
        (AssignmentStartPayload.Input.beta_le_rate payload a) }

/-- Construct the same canonical whole-arm numerical input on an actual later
cutoff choice. -/
def laterCutoffCollectionInput
    (record : RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
      base)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
      record.input.row) : RecordedQueueRun.RoundInput p.K := by
  classical
  let x := record.input
  let complement := (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
  let choice := selected.choiceInputsValid
  let u := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
  let W := ReferenceFirstWindowNumericalStream.sourceWeights registers.payload complement
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation registers.payload dispatched.startResult complement
  let recorderInput := CoordinatorRecorderComplementBridge.recorderInput recordingInput
  let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen recorderInput)
  exact {
    enabled := enabled
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection enabled
      rate.eta.val rate.eta.property rate.sourceCap registers.payload.anchor W
      registers.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos registers.payload complement u x.time choice)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower registers.payload complement u x.time choice)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper registers.payload complement u x.time choice)
      (ContinuousLearningRows.sliceAt x.time x.row.2)
    reward := fun a => ((x.rewards x.time a).val : ℝ) / (D p : ℝ)
    rate := registers.payload.rate
    reward_nonneg := by
      intro a
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro a
      have hvalue : (x.rewards x.time a).val ≤ D p :=
        Nat.le_of_lt_succ (x.rewards x.time a).isLt
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast hvalue
    rate_pos := by
      intro a
      exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
        (AssignmentStartPayload.Input.beta_le_rate registers.payload a) }

/-- On a genuine continuing collection constructor, the checked stage-one
service bit is exactly the strict comparison with that call's started clock. -/
theorem continuingCollectionEnabled_eq_started_clock
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) :
    ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time =
      decide (record.input.time.val + 1 < snapshot.clockStarted.clock.g) := by
  have hledgerSigma : ledger.sigma =
      CoordinatorRecorderComplementBridge.sourceStart payload := core.ledger_sigma_eq
  have hsigma : 0 < ledger.sigma := by
    rw [hledgerSigma]
    simp [CoordinatorRecorderComplementBridge.sourceStart]
  have htimeValid := core.clock_start_time_valid
  change CoordinatorPhaseClock.startRoundTimeValid p record.input.time clock at htimeValid
  unfold CoordinatorPhaseClock.startRoundTimeValid at htimeValid
  have hclockSigma : clock.sigma = some payload.sigma := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_sigma_eq
  have hclockCutoff : clock.u = some cutoff := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_cutoff_eq
  rw [hclockSigma, hclockCutoff] at htimeValid
  have htimeParts : payload.sigma.val < record.input.time.val ∧
      cutoff.val ≤ record.input.time.val := by
    simpa using htimeValid
  have hledgerCutoff : ledger.cutoff =
      CoordinatorCollectionUpRoundStep.sourceCutoff cutoff := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.ledger_cutoff_eq
  have hcutoff : ledger.cutoff ≤ record.input.time.val + 1 := by
    rw [hledgerCutoff]
    simp [CoordinatorCollectionUpRoundStep.sourceCutoff]
    omega
  have hledgerFreeze : ledger.freezeAt = clock.g := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.ledger_freeze_eq
  have hfreeze : ledger.freezeAt = snapshot.clockStarted.clock.g := by
    calc
      ledger.freezeAt = clock.g := hledgerFreeze
      _ = snapshot.clockStarted.clock.g := by
        exact (congrArg CoordinatorPhaseClock.ClockRegisters.g
          snapshot.clockStarted_frame.1).symm
  simp [ReferenceActivePhysicalStep.collectionEnabled, hsigma, hcutoff, hfreeze]

/-- On an accepted later cutoff choice, the initialized shared ledger records
the source clock boundary and cutoff used by stage one. -/
theorem laterCutoffCollectionEnabled_eq_started_clock
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned time) base)
    (newLedger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers time))
    (hcand : newLedger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned time) base time)
    (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (ReferenceActivePhysicalStep.liveRegistersAt registers time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned time) base time)
    (hclock : dispatched.startResult.clock =
      {(ReferenceActivePhysicalStep.liveRegistersAt registers time).priorClock with
        u := some (ReferenceActivePhysicalStep.liveRegistersAt registers time).time}) :
    ReferenceActivePhysicalStep.collectionEnabled
        (ReferenceActivePhysicalStep.sharedLedger newLedger) time =
      decide (time.val + 1 < dispatched.startResult.clock.g) := by
  let live := ReferenceActivePhysicalStep.liveRegistersAt registers time
  have hfields := ReferenceActivePhysicalStep.sharedLedger_fields newLedger
  have hsigma : 0 < (ReferenceActivePhysicalStep.sharedLedger newLedger).sigma := by
    rw [hfields.2.1, hcand]
    simp [CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      ReferenceActivePhysicalStep.liveRegistersAt]
  have hcutoff : (ReferenceActivePhysicalStep.sharedLedger newLedger).cutoff =
      time.val + 1 := by
    rw [hfields.2.2.1, hcand]
    rfl
  have hfreeze : (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt =
      dispatched.startResult.clock.g := by
    rw [hfields.2.2.2.1, hcand]
    calc
      live.gridBoundary = live.priorClock.g := hdomain.2.1
      _ = dispatched.startResult.clock.g := by
        simpa [live, ReferenceActivePhysicalStep.liveRegistersAt] using
          (congrArg CoordinatorPhaseClock.ClockRegisters.g hclock).symm
  simp [ReferenceActivePhysicalStep.collectionEnabled, hsigma, hcutoff, hfreeze]

/-- The numerical input's full collection map equals the actual
coordinator-source projection on a continuing collection constructor. -/
theorem continuingCollectionInput_map_eq_projection
    (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1) :
    let source := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
    let complement := CoordinatorCollectionInteractive.PreObservationInputs.weights source
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
    let input := ReferenceActivePhysicalStep.collectionRecordingInput
      record.output.preparation payload snapshot.clockStarted complement
    let operationInput := CoordinatorRecorderComplementBridge.recorderInput input
    let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨boundary, fun j => ⟨snapshot.inputsValid.choice_valid.anchor_le_current j,
        snapshot.inputsValid.choice_valid.current_le_twice_anchor j⟩⟩
    let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen operationInput)
    (continuingCollectionInput record payload ledger clock cutoff snapshot).recordedArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
        operationInput valid enabled := by
  classical
  dsimp only
  let source := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
  let complement := CoordinatorCollectionInteractive.PreObservationInputs.weights source
    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
  let input := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation payload snapshot.clockStarted complement
  let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
    ⟨boundary, fun j => ⟨snapshot.inputsValid.choice_valid.anchor_le_current j,
      snapshot.inputsValid.choice_valid.current_le_twice_anchor j⟩⟩
  let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
  let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen
    (CoordinatorRecorderComplementBridge.recorderInput input))
  exact collectionRecordingMap_eq_projection payload input valid enabled

/-- The later-cutoff numerical input's whole collection map equals the actual
coordinator-source projection. The valid rate envelope comes from the exact
selected payload and complement-choice constructor. -/
theorem laterCutoffCollectionInput_map_eq_projection
    (record : RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
      record.input.row) :
    let weights := (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
    let input := ReferenceActivePhysicalStep.collectionRecordingInput
      record.output.preparation registers.payload dispatched.startResult weights
    let operationInput := CoordinatorRecorderComplementBridge.recorderInput input
    let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨selected.recorderBoundaryValid, fun j =>
        ⟨selected.choiceInputsValid.anchor_le_current j,
          selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
    let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen operationInput)
    (laterCutoffCollectionInput record registers owned base dispatched selected).recordedArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart
        operationInput valid enabled := by
  classical
  dsimp only
  let weights := (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
  let input := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation registers.payload dispatched.startResult weights
  let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid input :=
    ⟨selected.recorderBoundaryValid, fun j =>
      ⟨selected.choiceInputsValid.anchor_le_current j,
        selected.choiceInputsValid.current_le_twice_anchor j⟩⟩
  let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
  let enabled := decide (¬ CoordinatorRecordingOperation.isFrozen
    (CoordinatorRecorderComplementBridge.recorderInput input))
  exact collectionRecordingMap_eq_projection registers.payload input valid enabled

/-- The deterministic partial readout. The selected payload and current
complement weights are read from the actual prepared coordinator branch.
Only later cutoff choices are admitted; the first cutoff owner is preserved. -/
def laterCollectionReadout (s : Nat)
    (record : RoundRecord (p := p) (rate := rate)) : Option (RecordedQueueRun.RoundInput p.K) := by
  classical
  if hfollowers : preparedFollowersUnoccupied record then
    match record.output.preparation.coordinator with
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        exact some (continuingCollectionInput record payload ledger clock cutoff snapshot)
    | .live registers owned base
        (.cutoffChosen dispatched _ _ _ _ _ _ _ _ selected) =>
        if s < registers.payload.sigma.val then
          exact some (laterCutoffCollectionInput record registers owned base dispatched selected)
        else
          exact none
    | _ => exact none
  else
    exact none

/-- The exact structural domain of the readout; no missing branch is assigned
a numerical default. -/
theorem laterCollectionReadout_domain
    (s : Nat) (record : RoundRecord (p := p) (rate := rate)) :
    (laterCollectionReadout s record).isSome = true ↔
      preparedFollowersUnoccupied record ∧
        (match record.output.preparation.coordinator with
        | .collection _ _ _ _ (.continuing _ _ _ _) => True
        | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            s < registers.payload.sigma.val
        | _ => False) := by
  classical
  by_cases hfollowers : preparedFollowersUnoccupied record
  · cases hcoord : record.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [laterCollectionReadout, hfollowers, hcoord]
    | live registers owned base outcome =>
        cases outcome <;> simp [laterCollectionReadout, hfollowers, hcoord]
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp [laterCollectionReadout, hfollowers, hcoord]
    | invalidCollectionCutoff => simp [laterCollectionReadout, hfollowers, hcoord]
    | dagger => simp [laterCollectionReadout, hfollowers, hcoord]
  · simp [laterCollectionReadout, hfollowers]

/-- Literal call arguments of the admitted collection tail, read from the
actual constructors. This is an option-valued diagnostic, not a new state. -/
def laterCollectionCall (s : Nat) (record : RoundRecord (p := p) (rate := rate)) :
    Option (Σ payload : Payload rate, Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
      (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) :=
  if preparedFollowersUnoccupied record then
    match record.output.preparation.coordinator with
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        some ⟨payload, ledger, snapshot.clockStarted,
          CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩
    | .live registers _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        if s < registers.payload.sigma.val then
          some ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights⟩
        else none
    | _ => none
  else none

/-- The readout discharges all constructor and ordinary/unoccupied inputs of
the two collection producers. It identifies the same physical recorder and
actual post-choice call, including every subsequent failure. -/
theorem laterCollectionReadout_call (s : Nat)
    (record : RoundRecord (p := p) (rate := rate)) (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : laterCollectionReadout s record = some c) :
    ∃ (payload : Payload rate) (ledger : Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      laterCollectionCall s record = some ⟨payload, ledger, started, weights⟩ ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation payload ledger started weights ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          payload started weights) = some out ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
      c.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      c.rate = payload.rate ∧
      c.reward = (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  classical
  have hsome : (laterCollectionReadout s record).isSome = true := by
    rw [hreadout]
    rfl
  have hdomain := (laterCollectionReadout_domain s record).mp hsome
  rcases hdomain with ⟨hunoccupied, hbranchDomain⟩
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      simp [hcoord] at hbranchDomain
  | invalidCollectionCutoff =>
      simp [hcoord] at hbranchDomain
  | dagger =>
      simp [hcoord] at hbranchDomain
  | collection payload ledger clock cutoff outcome =>
      cases outcome
      case continuing core snapshot boundary scores =>
          have hinput : continuingCollectionInput record payload ledger clock cutoff snapshot = c := by
            simpa [laterCollectionReadout, hunoccupied, hcoord] using hreadout
          subst c
          have hidentified := continuingCollectionRecorderOutput record s payload ledger clock cutoff
            core snapshot boundary scores hcoord hunoccupied
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hmap := continuingCollectionInput_map_eq_projection record payload ledger clock cutoff
            snapshot boundary
          rw [hprepared] at hmap
          dsimp only at hidentified hmap ⊢
          rcases hidentified with ⟨⟨out, hrun, hdiag, hgate, hraw⟩, henabled⟩
          have hgateReadout : out.gateArm =
              (continuingCollectionInput record payload ledger clock cutoff snapshot).recordedArm :=
            hgate.trans hmap.symm
          have hreward : (continuingCollectionInput record payload ledger clock cutoff snapshot).reward =
              (fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                (record.input.rewards record.input.time a)) := by
            rfl
          have hrate : ∀ a, (continuingCollectionInput record payload ledger clock cutoff snapshot).rate a =
              payload.rate a := by
            intro a
            rfl
          refine ⟨payload, ledger, snapshot.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, out, ?_, ?_, ?_,
            henabled, henabled.trans (continuingCollectionEnabled_eq_started_clock
              record payload ledger clock cutoff core snapshot), rfl, rfl,
            hdiag, hgateReadout, ?_⟩
          · simp [laterCollectionCall, hunoccupied, hcoord]
          · unfold ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics
            rw [record.output_eq]
            change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator = _
            rw [ReferenceActivePhysicalStep.observeCoordinator_collection_equation _ _ _ _ _ _
              (by simpa only [← hprepared] using hcoord)]
            simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
              Option.some_ne_none, ite_false]
            rfl
          · simpa only [hprepared] using hrun
          · exact rawInput_localArrival_eq_quantizedArrival payload
              (continuingCollectionInput record payload ledger clock cutoff snapshot) out _ _
              hgateReadout hmap hreward hrate hraw

      all_goals simp [hcoord] at hbranchDomain
  | live registers owned base outcome =>
      cases outcome
      case cutoffChosen dispatched hstart newLedger hinit hcand hdomainCut hclock hpending hnone selected =>
          have hlater : s < ↑registers.payload.sigma := by
            simpa [hcoord] using hbranchDomain
          have hinput : laterCutoffCollectionInput record registers owned base dispatched selected = c := by
            simpa [laterCollectionReadout, hunoccupied, hcoord, hlater] using hreadout
          subst c
          have hidentified := laterCutoffCollectionRecorderOutput record s registers owned base
            dispatched hstart newLedger hinit hcand hdomainCut hclock hpending hnone selected
            hcoord hunoccupied hlater
          have hprepared : record.output.preparation =
              ReferenceActivePhysicalStep.prepare record.input := by
            rw [record.output_eq]
            rfl
          have hmap := laterCutoffCollectionInput_map_eq_projection record registers owned base
            dispatched selected
          rw [hprepared] at hmap
          dsimp only at hidentified hmap ⊢
          rcases hidentified with ⟨⟨out, hrun, hdiag, hgate, hraw⟩, henabled⟩
          have hgateReadout : out.gateArm =
              (laterCutoffCollectionInput record registers owned base dispatched selected).recordedArm :=
            hgate.trans hmap.symm
          have hreward : (laterCutoffCollectionInput record registers owned base dispatched selected).reward =
              (fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                (record.input.rewards record.input.time a)) := by
            rfl
          have hrate : ∀ a, (laterCutoffCollectionInput record registers owned base dispatched selected).rate a =
              registers.payload.rate a := by
            intro a
            rfl
          refine ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger newLedger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights,
            out, ?_, ?_, ?_, henabled,
            henabled.trans (laterCutoffCollectionEnabled_eq_started_clock registers owned base
              record.input.time dispatched newLedger hcand hdomainCut hclock), rfl, rfl,
            hdiag, hgateReadout, ?_⟩
          · simp [laterCollectionCall, hunoccupied, hcoord, hlater]
          · unfold ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics
            rw [record.output_eq]
            change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator = _
            rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation _ _ _ _ _
              (by simpa only [← hprepared] using hcoord)]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
            rfl
          · simpa only [hprepared] using hrun
          · exact rawInput_localArrival_eq_quantizedArrival registers.payload
              (laterCutoffCollectionInput record registers owned base dispatched selected) out _ _
              hgateReadout hmap hreward hrate hraw

      all_goals simp [hcoord] at hbranchDomain

/-- Exhaustive literal collection recorder output. A passed gate may have
zero floor; every failed DATA/source/freeze/mask/thinning test returns the
successful no-gate output. No observation positivity is required. -/
theorem collectionRecorder_output_cases (input : CoordinatorRecordingOperation.Input p)
    (hmode : input.mode = .collection) (out : CoordinatorRecordingOperation.Output p)
    (hrun : CoordinatorRecordingOperation.run input = some out) :
    ∃ valid : CoordinatorRecordingOperation.InputsValid input,
      out = if CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot ∧
          CoordinatorRecordingOperation.selectedRecorder input = ActiveRoundActions.coordinator p.two_le_m ∧
          ¬ CoordinatorRecordingOperation.isFrozen input ∧
          CoordinatorRecordingOperation.ownMaskPasses input ∧
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
            (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
              CoordinatorRecordingOperation.coordinatorThreshold input valid then
        ⟨some input.ownArm, CoordinatorRecordingOperation.floorArrival input,
          CoordinatorRecordingOperation.floorArrival_le_D input valid⟩
      else CoordinatorRecordingOperation.zeroOutput p := by
  classical
  have valid : CoordinatorRecordingOperation.InputsValid input := by
    by_contra h
    rw [CoordinatorRecordingOperation.run_none_of_invalid input h] at hrun
    contradiction
  have howned : CoordinatorRecordingOperation.ownsArm input.mode input.ownArm := by
    simp [hmode, CoordinatorRecordingOperation.ownsArm]
  have hden := (CoordinatorRecordingOperation.rawGateMass_feasible input valid howned).1
  have hparameter := CoordinatorRecordingOperation.coordinatorThreshold_mem_Icc_of_owned
    input valid howned
  have hbound := CoordinatorRecordingOperation.floorArrival_le_D input valid
  refine ⟨valid, ?_⟩
  have hex : CoordinatorRecordingOperation.executeValid input valid = some out := by
    simpa only [CoordinatorRecordingOperation.run, dite_eq_left valid] using hrun
  by_cases hd : CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot
  <;> by_cases hs : CoordinatorRecordingOperation.selectedRecorder input =
      ActiveRoundActions.coordinator p.two_le_m
  <;> by_cases hf : CoordinatorRecordingOperation.isFrozen input
  <;> by_cases hm : CoordinatorRecordingOperation.ownMaskPasses input
  <;> by_cases ht : (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
      (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
        CoordinatorRecordingOperation.coordinatorThreshold input valid
  <;> simp only [CoordinatorRecordingOperation.coordinatorThreshold] at ht hparameter ⊢
  <;> simp only [CoordinatorRecordingOperation.executeValid, hd, hs, hf, howned, hm,
      hden, hparameter, hbound, ht, and_true, and_false, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
      dite_true, dite_false, Option.some.injEq] at hex ⊢
  all_goals exact hex.symm

/-- A gated collection recorder uses the actual coordinator action and exact
grid feedback. Ordinary unoccupied followers take their own DATA pilots, so
the actual mask proves physical collision freedom. -/
theorem collectionRecorder_gated_feedback
    (record : RoundRecord (p := p) (rate := rate))
    (hunoccupied : preparedFollowersUnoccupied record)
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (out : CoordinatorRecordingOperation.Output p) (a : Fin p.K)
    (hrun : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        payload started weights) = some out) (hgate : out.gateArm = some a) :
    let input := CoordinatorRecorderComplementBridge.recorderInput
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        payload started weights)
    ∃ valid : CoordinatorRecordingOperation.InputsValid input,
      CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot ∧
      CoordinatorRecordingOperation.selectedRecorder input = ActiveRoundActions.coordinator p.two_le_m ∧
      ¬ CoordinatorRecordingOperation.isFrozen input ∧
      SnapshotRecordingKernel.owns p .collection (ActiveRoundActions.coordinator p.two_le_m) a ∧
      record.actions (ActiveRoundActions.coordinator p.two_le_m) = a ∧
      CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) a
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2)).val ≤
          CoordinatorRecordingOperation.coordinatorThreshold input valid ∧
      record.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) =
        record.input.rewards record.input.time a ∧
      out.rawArrival = Nat.floor ((D p : ℝ) * rate.eta.val *
        (((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ)) / payload.rate a) := by
  classical
  dsimp only
  let input := CoordinatorRecorderComplementBridge.recorderInput
    (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation payload started weights)
  obtain ⟨valid, hout⟩ := collectionRecorder_output_cases input rfl out hrun
  split at hout
  next htests =>
    rcases htests with ⟨hd, hs, hf, hm, ht⟩
    have harm : input.ownArm = a := Option.some.inj (by simpa only [hout] using hgate)
    have haction : record.actions (ActiveRoundActions.coordinator p.two_le_m) = a :=
      record.output.preparation.action_coordinator.trans harm
    have hdata : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.dataSlot := hd
    have hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) a
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) := by
      change CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) input.ownArm
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) at hm
      simpa only [harm] using hm
    have hprepared : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    have hfree : FiniteBanditModel.collisionFreeFor record.actions
        (ActiveRoundActions.coordinator p.two_le_m) := by
      intro player hne
      let i := ActiveRoundActions.followerIndex p.two_le_m player hne
      have hparts := actualFollowerParts_spec record hunoccupied i
      have hordinary := hparts.1
      rw [hprepared] at hordinary
      have hpilot := ReferenceActiveDataOwnership.ordinary_data_arm payload i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) _ _ hordinary
        (fun h => False.elim (h hparts.2)) hdata
      have hplayer := ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hne
      have hactual : record.actions player = PublicDiscreteDraws.pilotDraw (K_pos p) player
          (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) := by
        rw [← hplayer]
        exact record.output.preparation.action_follower i |>.trans
          (by simpa only [hparts.2, ite_true, i, ContinuousLearningRows.sliceAt] using hpilot)
      rw [haction, hactual]
      exact hmask player hne
    have hfeedback : record.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) =
        record.input.rewards record.input.time a := by
      rw [record.gridFeedback_formula, ite_eq_left hfree, haction]
    refine ⟨valid, hd, hs, hf, rfl, haction, hmask, ht, hfeedback, ?_⟩
    rw [hout]
    change CoordinatorRecordingOperation.floorArrival input = _
    rw [CoordinatorRecordingOperation.floorArrival_eq_literal, payload.rate_eq_canonical a]
    change Nat.floor ((D p : ℝ) * rate.eta.val *
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.gridFeedback (ActiveRoundActions.coordinator p.two_le_m)) /
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor input.ownArm) = _
    rw [hfeedback, harm]
    rfl
  next hfailed =>
    rw [hout] at hgate
    cases hgate

/-- The partial source calendar retains every original suffix record and its
option-valued later-collection readout in the same order. -/
def partialCalendar (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p) :
    List (Fin p.T × Option (RecordedQueueRun.RoundInput p.K)) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
    (fun record =>
      (record.input.time,
        laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          record))

/-- Every finite index of the partial calendar is paired with that exact
physical record time and its unfiltered option-valued readout. -/
theorem partialCalendar_get (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (partialCalendar rate rewards C_star C_h source).get
        ⟨k.val, by simp [partialCalendar]⟩ =
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).input.time,
        laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k)) := by
  simp [partialCalendar]

/-- The partial calendar has one entry per actual suffix round, including
NONE-valued readouts. -/
theorem partialCalendar_length (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p) :
    (partialCalendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp [partialCalendar,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length]

/-- The first coordinates are exactly the physical interval from the actual
launch through `T`, with no filtering of unsupported branches. -/
theorem partialCalendar_times (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p) :
    (partialCalendar rate rewards C_star C_h source).map (fun item => item.1.val) =
      List.range'
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        1 := by
  unfold partialCalendar
  rw [List.map_map]
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
      (fun record => record.input.time.val) = _
  simpa [ReferenceActivePhysicalHorizon.calendar] using
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h)

/-- The launch boundary never exceeds `T`, so the partial calendar length is
at most `T`. -/
theorem partialCalendar_length_le_T (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p) :
    (partialCalendar rate rewards C_star C_h source).length ≤ p.T := by
  rw [partialCalendar_length]
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  omega

/-- Split the original source construction at its actual corrected launch.
The absent launch gives the real empty suffix and terminal start. A present
launch is identified with its actual payload, and its seed facts come from
the existing first-live constructor while the suffix remains the original
physical horizon run. -/
theorem source_launch_split (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p) :
    (ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = none ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = [] ∧
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = p.T) ∨
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      ∃ hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some active,
      ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h =
          (ReferenceActivePhysicalHorizon.run active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (by
              have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate source rewards C_star C_h
              omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate source rewards C_star C_h active hlaunch)).records ∧
      ∃ hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true,
        active = ReferenceFirstLaunchNumericalCell.launchState
          rate source rewards C_star C_h hc ∧
        ∃ seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h),
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc).coordinator =
            .first ∧
          (∀ i, (seed.followers i).status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid (seed.followers i) ∧
            ActiveFollowerLifecycle.localBufferValid (seed.followers i) ∧
            (seed.followers i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            ActiveFollowerLifecycle.downDecoderStateValid (seed.followers i)) ∧
          (∀ i saved, saved ∈ (seed.followers i).buffer →
            saved.calendarRound <
              ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + 1) := by
  classical
  by_cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · exact Or.inl ⟨hlaunch, by simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch],
      ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate source rewards C_star C_h hlaunch⟩
  · have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h).isSome = true := by
      exact Option.ne_none_iff_isSome.mp hlaunch
    have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mp hsome
    let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate source rewards C_star C_h hlaunch
    have hactive : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some active :=
      ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
        rate source rewards C_star C_h hlaunch
    have hstate : active = ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc :=
      Option.some.inj (hactive.symm.trans
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc))
    subst active
    have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate source rewards C_star C_h
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc)
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    refine Or.inr ⟨_, ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc, ?_,
      ⟨hc, rfl, ⟨seed, ?_, ?_, ?_⟩⟩⟩
    · exact hrecords
    · exact seed.coordinatorFirst
    · intro i
      exact ⟨seed.unoccupied i, seed.localStateDomain i, seed.bufferValid i,
        seed.chronologicalBuffer i, seed.decoderValid i⟩
    · intro i saved hsaved
      have hstamp := seed.bufferStamps i saved hsaved
      change saved.calendarRound ≤
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h at hstamp
      omega

section Source

variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ) (source : SourceInput p)
variable (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h).length)

/-- The indexed record retains the whole original row family, selected index
(including the original J scalar), and reward matrix. Launch splitting uses
the same corrected seed and original horizon run, including the empty case. -/
theorem sourceIndexedReadout_inputs :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    record.input.rows = source.1.2 ∧
      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      record.input.rewards = rewards := by
  dsimp only
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
  rcases source_launch_split rate rewards C_star C_h source with hnone | ⟨active, hlaunch, hrecords, _⟩
  · have hlength := congrArg List.length hnone.2.1
    exact False.elim (Nat.not_lt_zero k.val (k.isLt.trans_eq hlength))
  · apply ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
      (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h; omega)
      (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch) record
    rw [← hrecords]
    exact List.get_mem records k

/-- On SOME, the same physical recorder supplies all numerical arrivals.
For every gated arm, the actual coordinator owns and plays that arm, passes
the mask/thinning tests, and receives its original grid reward, including zero. -/
theorem laterCollectionReadout_physical (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    let delta := RecordedQueueRun.quantizedArrival (K := p.K) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ∃ (payload : Payload rate) (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      laterCollectionCall
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        record = some ⟨payload, ledger, started, weights⟩ ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation payload started weights) = some out ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a = delta c a) ∧
      c.rate = payload.rate ∧ c.reward = (fun a => ((rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
      ∀ a, c.recordedArm = some a →
        let input := CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation payload started weights)
        ∃ valid : CoordinatorRecordingOperation.InputsValid input,
          CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot ∧
          CoordinatorRecordingOperation.selectedRecorder input = ActiveRoundActions.coordinator p.two_le_m ∧
          ¬ CoordinatorRecordingOperation.isFrozen input ∧
          SnapshotRecordingKernel.owns p .collection (ActiveRoundActions.coordinator p.two_le_m) a ∧
          record.actions (ActiveRoundActions.coordinator p.two_le_m) = a ∧
          CanonicalRecordingSlice.recordingMask (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) a
            (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) ∧
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
            (ContinuousLearningRows.sliceAt record.input.time record.input.row.2)).val ≤
              CoordinatorRecordingOperation.coordinatorThreshold input valid ∧
          record.gridFeedback (ActiveRoundActions.coordinator p.two_le_m) = rewards record.input.time a ∧
          out.rawArrival = Nat.floor ((D p : ℝ) * rate.eta.val *
            (((rewards record.input.time a).val : ℝ) / (D p : ℝ)) / payload.rate a) := by
  dsimp only
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
  obtain ⟨payload, ledger, started, weights, out, hcall, _, hrun, _, _, hrate, hreward, hdiag, hgate, harr⟩ :=
    laterCollectionReadout_call start record c hreadout
  have hinput : record.input.rewards = rewards :=
    (sourceIndexedReadout_inputs rate rewards C_star C_h source k).2.2
  refine ⟨payload, ledger, started, weights, out, hcall, hrun, hdiag, hgate, harr, hrate,
    hreward.trans (by rw [hinput]), ?_⟩
  intro a ha
  have hfollowers := ((laterCollectionReadout_domain start record).mp (by rw [hreadout]; rfl)).1
  have hphysical := collectionRecorder_gated_feedback record hfollowers payload started weights out a
    hrun (hgate.trans ha)
  rw [hinput] at hphysical
  exact hphysical

/-- The actual attempted stage-one candidate has the canonical per-arm queue
transition, zero unknown-arm service, and exactly the positive unknown/pre-freeze
buffer insertion. Other cells persist. START is exposed by cases; no START,
receive, FINISH, global score, or complete-calendar coverage is assumed. -/
theorem laterCollectionReadout_stageOne (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    let delta := RecordedQueueRun.quantizedArrival (K := p.K) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ∃ (payload : Payload rate) (ledger : Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      laterCollectionCall (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record = some ⟨payload, ledger, started, weights⟩ ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation payload ledger started weights ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation payload started weights) = some out ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
      c.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      (let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
       let l1 := CoordinatorCollectionLedger.startRoundCandidate ledger record.input.time c.enabled raw
       (∀ a current, ledger.currentRegisters a = some current →
         l1.currentRegisters a = some ⟨(QueueReplay.transition (4 * rate.n) (0, current.queue)
           (c.enabled, delta c a)).2, (QueueReplay.transition (4 * rate.n) (0, current.queue) (c.enabled, delta c a)).1⟩ ∧
         l1.gammaLoc a = (QueueReplay.transition (4 * rate.n) (0, current.queue) (c.enabled, delta c a)).1) ∧
       (∀ a, ledger.currentRegisters a = none → l1.gammaLoc a = 0) ∧
       (∀ a time, l1.rawBuffer a time =
         if c.recordedArm = some a ∧ ledger.currentRegisters a = none ∧ 0 < delta c a ∧
             CoordinatorCollectionLedger.sourceRound record.input.time < ledger.freezeAt ∧ time = record.input.time
         then some (delta c a) else ledger.rawBuffer a time) ∧
       (stageOneAttempt ledger record.input.time c.enabled out = .invalid ∨
         (∃ rejected, stageOneAttempt ledger record.input.time c.enabled out = .rejected rejected) ∨
         ∃ result, stageOneAttempt ledger record.input.time c.enabled out = .success result ∧ result = l1)) := by
  classical
  dsimp only
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
  let delta := RecordedQueueRun.quantizedArrival (K := p.K) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
  obtain ⟨payload, ledger, started, weights, out, hcall, htail, hrun, henabled, hclock,
    _, _, hdiag, hgate, harr⟩ := laterCollectionReadout_call start record c hreadout
  refine ⟨payload, ledger, started, weights, out, hcall, htail, hrun, hdiag, hgate,
    henabled, hclock, ?_, ?_, ?_, stageOneAttempt_cases ledger record.input.time c.enabled out⟩
  · intro a current hknown
    have htransition : QueueReplay.transition (4 * rate.n) (0, current.queue)
        (CoordinatorCollectionLedger.localQueueRecord ledger record.input.time c.enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a) =
        QueueReplay.transition (4 * rate.n) (0, current.queue) (c.enabled, delta c a) := by
      cases he : c.enabled with
      | false => simp [CoordinatorCollectionLedger.localQueueRecord, QueueReplay.transition]
      | true =>
          have hbefore := (of_decide_eq_true (henabled.symm.trans he)).2.2
          simp only [CoordinatorCollectionLedger.localQueueRecord,
            CoordinatorCollectionLedger.sourceRound, hbefore, decide_true, Bool.and_self, ite_true, harr a]
          rfl
    constructor
    · rw [stageOneCandidate_known_transition ledger record.input.time c.enabled out a current hknown, htransition]
    · simp only [CoordinatorCollectionLedger.startRoundCandidate, hknown]
      exact congrArg Prod.fst htransition
  · exact stageOneCandidate_unknown_zero ledger record.input.time c.enabled out
  · intro a time
    cases ho : out.gateArm with
    | none =>
        simp [CoordinatorCollectionLedger.startRoundCandidate,
          CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, ho, ← hgate]
    | some arm =>
        have hdelta : delta c arm = out.rawArrival := by
          simpa [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, ho,
            CoordinatorCollectionLedger.localArrival] using (harr arm).symm
        dsimp only [delta] at hdelta
        by_cases ha : a = arm
        · subst a
          simp only [CoordinatorCollectionLedger.startRoundCandidate,
            CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, ho, Option.map_some, ← hgate,
            hdelta]
          split <;> simp_all [CoordinatorCollectionLedger.putRaw]
        · simp only [CoordinatorCollectionLedger.startRoundCandidate,
            CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, ho, Option.map_some, ← hgate,
            Option.some.injEq, Ne.symm ha, false_and, ite_false]
          split <;> simp_all [CoordinatorCollectionLedger.putRaw]

/-- The original recorder-and-all-arrivals projection of the complete physical
export, with no successful-round or positive-reward premise. -/
theorem sourceIndexedReadout_recorder_and_arrivals (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    ∃ out : CoordinatorRecordingOperation.Output p,
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
      ∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  obtain ⟨_, _, _, _, out, _, _, _, _, _, _, _, hdiag, hgate, harr⟩ :=
    laterCollectionReadout_call _ _ c hreadout
  exact ⟨out, hdiag, hgate, harr⟩

/-- Every canonical arrival is the literal source floor on its gated arm and
zero otherwise. This preserves gated zero and does not fill absent readouts. -/
theorem sourceIndexedReadout_arrival_formula (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    ∀ a, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
      if c.recordedArm = some a then Nat.floor ((D p : ℝ) * rate.eta.val *
        (((rewards record.input.time a).val : ℝ) / (D p : ℝ)) / c.rate a) else 0 := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hreward, _, _, _⟩ :=
    laterCollectionReadout_call _ _ c hreadout
  have hinput := (sourceIndexedReadout_inputs rate rewards C_star C_h source k).2.2
  intro a
  unfold RecordedQueueRun.quantizedArrival
  split_ifs
  · congr 1
    rw [(ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D, hreward, hinput]
    change rate.eta.val * (D p : ℝ) * _ / _ = (D p : ℝ) * rate.eta.val * _ / _
    ring
  · rfl

/-- The exact physical time at each original index is launch plus that index.
In particular the last suffix record, when present, is the source round T. -/
theorem sourceIndexedReadout_time :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[k.val]?) htimes
  have hi : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using k.isLt
  have hsome := List.getElem?_range' (s := ReferenceCompletePhysicalHistory.physicalStart
    rate source rewards C_star C_h) (step := 1) hi
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem k.isLt, hsome] using hget

end Source

end Bandits.Support.ReferenceLaterCollectionArrivalReadout

end
