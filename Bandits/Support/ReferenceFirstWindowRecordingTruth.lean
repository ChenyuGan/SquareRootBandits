/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual first-live-window coordinator recording

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`, and
`sources/zip4/manuscript/06_interruptions.tex:246-295,391-397`.

The branch adapters below consume the actual first or continuing-live
dispatcher constructor and ordinary follower choices produced by
`ReferenceFirstLiveFollowerSafety`. They identify the existing coordinator
recording output and retain the original arm-indexed raw diagnostic, including
the distinction between no call and a successful no-gate output. They do not
assert a law, a global queue trace, or source totality.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstWindowRecordingTruth

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open ConstructorDimensions
open CanonicalRecordingSlice
open PublicDiscreteDraws
open ActiveRoundActions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCoordinatorRecorderCallTrace
open ReferenceCoordinatorRecorderCallCorrespondence
open ReferenceActiveHorizonMeasurability
open ReferenceCoordinatorLiveRecording
open CoordinatorRecorderComplementBridge
open CoordinatorRecordingOperation
open CoordinatorLiveChoiceRecorderStep
open CoordinatorLiveServiceFinish
open CoordinatorRoundDispatch
open CoordinatorPhaseClock
open CoordinatorLocalArmChoice

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_preparation_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
  simpa only [ReferenceActivePhysicalStep.step] using
    congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input => output.preparation)
      record.output_eq

/-- On an actual installed-first record, consume the literal first recording
identity and identify the lossless arm-indexed projection of the retained
recorder output. All follower ordinary configurations and occupied fields are
explicit inputs; the first-live theorem is the producer of those inputs. -/
theorem first_branch_recording_truth
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput record.input)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights record.input.row)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed arm))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (installed.registers.payload.downRecord i)) :
    ∃ htime : installed.registers.time = record.input.time,
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input installed.registers.payload installed.startRoundResult
        installed.registers.time installed.registers.complementWeights arm
        htime ∧
      ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
        CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input) installed.registers
            installed.startRoundResult) ∧
      (∀ i, (states i).status ≠ .unoccupied →
        (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
      ∃ out,
        record.output.coordinator.recording = some out ∧
        (let I := ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input) installed.registers installed.startRoundResult
         let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
            (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
              record.output.preparation installed.registers installed.startRoundResult
              installed.registers.time arm)
         let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
            (CoordinatorRecorderComplementBridge.recorderInput I) v
            installed.registers.payload.assignment
            { missing := installed.startRoundResult.pending
              status := fun i => (states i).status }
            (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
         CoordinatorRecorderComplementBridge.run I = some out ∧
          out.gateArm = E ∧
          out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
            installed.registers.payload.anchor
            (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              (record.input.rewards record.input.time j)) E ∧
          ∀ j : Fin p.K,
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
              some (if out.gateArm = some j then out.rawArrival else 0)) := by
  classical
  have hprep := record_preparation_eq record
  have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .first (.chosen installed arm) := by
    have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
    exact h.symm.trans hbranch
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  rw [hbranch] at hframes
  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    record.input installed.registers.payload installed.startRoundResult
    installed.registers.time installed.registers.complementWeights arm hframes.1
  have hselectedAt :
      ReferenceActivePhysicalStep.selectionAt record.input installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights arm =
        some selected := by
    simpa only [selected] using
      ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
        installed.registers.payload installed.startRoundResult installed.registers.time
        installed.registers.complementWeights arm hframes.1
  have hselectedPrep : record.output.preparation.coordinator.selection = some selected := by
    rw [hbranch]
    exact hselectedAt
  have hselectedDispatch : (ReferenceActivePhysicalStep.dispatch record.input).selection =
      some selected := by
    have hprepCoord : record.output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch record.input := by
      have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
      simpa only [ReferenceActivePhysicalStep.prepare] using h
    rw [← hprepCoord]
    exact hselectedPrep
  have hidentity := ReferenceCoordinatorLiveRecording.first_recording_identification
    record.input installed arm hcut states memories (by
      intro i
      rw [← hprep]
      exact hordinary i) hfields hframes.2.1
  obtain ⟨out, hrun, hrecording, hgate, hraw⟩ := hidentity
  have hrecording' : record.output.coordinator.recording = some out := by
    rw [record.output_eq]
    exact hrecording
  have hin := ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
    record installed.registers installed.startRoundResult installed.registers.time arm
    hframes.1 hselectedPrep hframes.2.1
  have hin' : ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.liveRecordingInput
          (ReferenceActivePhysicalStep.prepare record.input) installed.registers
          installed.startRoundResult) := by
    calc
      ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
        CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            record.output.preparation installed.registers installed.startRoundResult) := hin
      _ = CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input) installed.registers
            installed.startRoundResult) :=
        congrArg (fun prepared => CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput prepared installed.registers
            installed.startRoundResult)) hprep
  have hdiag := ReferenceCoordinatorRecorderCallCorrespondence.coordinatorRaw_eq_run_of_selected
    record selected hselectedDispatch
  refine ⟨hframes.1, selected, hselectedPrep, rfl, hin', ?_, out, hrecording', ?_⟩
  · intro i hi
    exact hfields i hi
  dsimp only
  refine ⟨hrun, hgate, hraw, ?_⟩
  intro j
  rw [hdiag j, hin']
  change (CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) installed.registers
        installed.startRoundResult)).map
      (fun output => if output.gateArm = some j then output.rawArrival else 0) = _
  rw [hrun]
  simp

/-- On an actual continuing-live record, consume the literal continuation
recording identity and identify the lossless arm-indexed projection of its
retained output. The phase frame is derived from the actual dispatcher. -/
theorem continuing_branch_recording_truth
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
      r.priorClock (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).clockPending =
        .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time) record.input.row)
    (arm : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult
      record.input.time (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
      record.input.row)
    (hbranch : record.output.preparation.coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation arm))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i)) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).payload
        dispatched.startResult record.input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights arm rfl ∧
      ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
        CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input)
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            dispatched.startResult) ∧
      (∀ i, (states i).status ≠ .unoccupied →
        (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
      ∃ out,
        record.output.coordinator.recording = some out ∧
        (let I := ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input)
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            dispatched.startResult
         let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
            (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
              record.output.preparation
              (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
              dispatched.startResult record.input.time arm)
         let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
            (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
            { missing := dispatched.startResult.pending
              status := fun i => (states i).status }
            (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
         CoordinatorRecorderComplementBridge.run I = some out ∧
          out.gateArm = E ∧
          out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
            (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              (record.input.rewards record.input.time j)) E ∧
          ∀ j : Fin p.K,
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
              some (if out.gateArm = some j then out.rawArrival else 0)) := by
  classical
  have hprep := record_preparation_eq record
  have hcut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation arm) := by
    have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
    exact h.symm.trans hbranch
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  rw [hbranch] at hframes
  let registers := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    record.input registers.payload dispatched.startResult record.input.time registers.complementWeights arm rfl
  have hselectedAt :
      ReferenceActivePhysicalStep.selectionAt record.input registers.payload dispatched.startResult
        record.input.time registers.complementWeights arm = some selected := by
    simpa only [selected] using
      ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input registers.payload
        dispatched.startResult record.input.time registers.complementWeights arm rfl
  have hselectedPrep : record.output.preparation.coordinator.selection = some selected := by
    rw [hbranch]
    exact hselectedAt
  have hselectedDispatch : (ReferenceActivePhysicalStep.dispatch record.input).selection =
      some selected := by
    have hprepCoord : record.output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch record.input := by
      have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
      simpa only [ReferenceActivePhysicalStep.prepare] using h
    rw [← hprepCoord]
    exact hselectedPrep
  have hidentity := ReferenceCoordinatorLiveRecording.continuing_recording_identification
    record.input r q base dispatched hstart continuation arm hcut states memories (by
      intro i
      rw [← hprep]
      exact hordinary i) hfields hframes.1
  obtain ⟨out, hrun, hrecording, hgate, hraw⟩ := hidentity
  have hrecording' : record.output.coordinator.recording = some out := by
    rw [record.output_eq]
    exact hrecording
  have hin := ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
    record registers dispatched.startResult record.input.time arm rfl hselectedPrep hframes.1
  have hin' : ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.liveRecordingInput
          (ReferenceActivePhysicalStep.prepare record.input) registers dispatched.startResult) := by
    calc
      ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
        CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            record.output.preparation registers dispatched.startResult) := hin
      _ = CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare record.input) registers dispatched.startResult) :=
        congrArg (fun prepared => CoordinatorRecorderComplementBridge.recorderInput
          (ReferenceActivePhysicalStep.liveRecordingInput prepared registers dispatched.startResult)) hprep
  have hdiag := ReferenceCoordinatorRecorderCallCorrespondence.coordinatorRaw_eq_run_of_selected
    record selected hselectedDispatch
  refine ⟨selected, hselectedPrep, rfl, hin', ?_, out, hrecording', ?_⟩
  · intro i hi
    simpa only [selected, registers, ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hfields i hi
  dsimp only
  refine ⟨hrun, hgate, hraw, ?_⟩
  intro j
  rw [hdiag j, hin']
  change (CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) registers dispatched.startResult)).map
      (fun output => if output.gateArm = some j then output.rawArrival else 0) = _
  rw [hrun]
  simp only [Option.map_some]

/-- DATA actions and owned grid feedback on an actual finite-horizon record.
The action is derived for every ordinary follower. Reward equality is exposed
only when that follower is occupied and its actual canonical slice satisfies
the recording mask; zero rewards remain included without a positivity premise.
The original run membership aligns the feedback entry with the supplied grid.
-/
def actual_window_follower_data_claim
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) : Prop :=
    ∀ i : Fin (p.m - 1), slotDraw (record.input.row.2 record.input.time).1 = dataSlot →
      (record.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
        if (states i).status = .unoccupied then
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
            (record.input.row.2 record.input.time).1
        else selected.view.payload.assignment.assigned i) ∧
      ((states i).status ≠ .unoccupied →
        ∀ hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
          (followerPlayer p.two_le_m i) (selected.view.payload.assignment.assigned i)
          (record.input.row.2 record.input.time).1,
          record.gridFeedback (followerPlayer p.two_le_m i) =
            rewards record.input.time (selected.view.payload.assignment.assigned i) ∧
          ReferenceActivePhysicalHorizon.observationValue
            (record.ownEntries (followerPlayer p.two_le_m i)).2 =
            ((rewards record.input.time (selected.view.payload.assignment.assigned i)).val : ℝ) /
              (D p : ℝ))

theorem actual_window_follower_data_truth
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active).records)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time) :
    actual_window_follower_data_claim record selected states rewards := by
  classical
  intro i hdata
  have hOrdDecl :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).configuration = .ordinary (states i) (memories i) := by
    have h := hordinary i
    rw [record.output.preparation.followers.followers_eq i] at h
    simpa [ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActivePhysicalStep.RoundInput.row] using h
  have hArm := ReferenceActiveDataOwnership.ordinary_data_arm selected.view.payload i
    record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i) (record.input.state.followers i) (states i) (memories i)
    hOrdDecl (hfields i) hdata
  have haction : record.output.preparation.arms.actions (followerPlayer p.two_le_m i) =
      if (states i).status = .unoccupied then
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1
      else selected.view.payload.assignment.assigned i := by
    rw [ReferenceActivePhysicalStep.PreparedRound.action_follower]
    exact hArm
  constructor
  · exact haction
  · intro hi hmask
    have hactionAssigned : record.output.preparation.arms.actions
        (followerPlayer p.two_le_m i) = selected.view.payload.assignment.assigned i := by
      simpa [hi] using haction
    have hactionPrepared : (ReferenceActivePhysicalStep.prepare record.input).arms.actions
        (followerPlayer p.two_le_m i) = selected.view.payload.assignment.assigned i := by
      rw [← record_preparation_eq record]
      exact hactionAssigned
    have hselectedPrep :
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
      rw [← record_preparation_eq record]
      exact hselected
    have howns : SnapshotRecordingKernel.owns p
        (.live selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot selected states))
        (followerPlayer p.two_le_m i) (selected.view.payload.assignment.assigned i) := by
      simp only [SnapshotRecordingKernel.owns,
        dite_eq_right (followerPlayer_ne_coordinator p.two_le_m i),
        followerIndex_followerPlayer p.two_le_m i
          (followerPlayer_ne_coordinator p.two_le_m i)]
    have hfeedback := ReferenceActiveDataOwnership.run_record_owner_feedback
      initial rows J rewards start count hspan active record hrecord selected hselectedPrep
      states memories (by
        intro j
        rw [← record_preparation_eq record]
        exact hordinary j) hfields hlive hdata (followerPlayer p.two_le_m i)
      (selected.view.payload.assignment.assigned i) hactionPrepared howns hmask
    exact hfeedback

private theorem actual_first_or_continuing_record_branch
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcarried : ReferenceFirstLiveConfirmationHistory.FirstLiveState record.input.state)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false)
    (hhasChoice : (ReferenceActivePhysicalStep.dispatch record.input).selection ≠ none) :
    (∃ installed arm,
      record.output.preparation.coordinator = .first (.chosen installed arm)) ∨
    (∃ r q base dispatched hstart continuation arm,
      record.output.preparation.coordinator =
        .live r q base (.continuingChosen dispatched hstart continuation arm)) := by
  have hprep := record_preparation_eq record
  have hprepCoord : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    have h := congrArg ReferenceActivePhysicalStep.PreparedRound.coordinator hprep
    simpa only [ReferenceActivePhysicalStep.prepare] using h
  cases hstate : record.input.state.coordinator with
  | first =>
      cases hd : CoordinatorRoundDispatch.dispatch
          (.first (ReferenceActivePhysicalStep.firstInput record.input)) with
      | first outcome =>
          have hactual : record.output.preparation.coordinator = .first outcome := by
            have hdispatch : ReferenceActivePhysicalStep.dispatch record.input = .first outcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate, hd]
              rfl
            exact hprepCoord.trans hdispatch
          cases outcome with
          | choiceDomainFailure installed =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | recorderBoundaryFailure installed =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | choiceRejected installed =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | chosen installed arm => exact Or.inl ⟨installed, arm, hactual⟩
  | live r q base =>
      cases hd : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput record.input r q base)) with
      | live outcome =>
          have hactual : record.output.preparation.coordinator = .live r q base outcome := by
            have hdispatch : ReferenceActivePhysicalStep.dispatch record.input = .live r q base outcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate, hd]
              rfl
            exact hprepCoord.trans hdispatch
          cases outcome with
          | clockFailure failure =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | initializerFailure dispatched hstart checked hchecked =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | localFailure dispatched hstart reason =>
              have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
                rw [← hprepCoord, hactual]
                rfl
              exact False.elim (hhasChoice hnone)
          | cutoffChosen dispatched hstart ledger hinitial hledger hdomains hclock hpending hno arm =>
              have hcutoffTrue : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
                unfold ReferenceCollectionPhaseHistory.cutoffChosen
                rw [← hprep, hactual]
              rw [hcutoff] at hcutoffTrue
              cases hcutoffTrue
          | continuingChosen dispatched hstart continuation arm =>
              exact Or.inr ⟨r, q, base, dispatched, hstart, continuation, arm, hactual⟩
  | collection payload ledger saved =>
      simp [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hstate] at hcarried
  | dagger =>
      have hnone : (ReferenceActivePhysicalStep.dispatch record.input).selection = none := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate,
          ReferenceActivePhysicalStep.DispatchCut.selection]
      exact False.elim (hhasChoice hnone)

private theorem mem_of_mem_takeWhile {α : Type} (predicate : α → Bool)
    {items : List α} {item : α}
    (hitem : item ∈ items.takeWhile predicate) : item ∈ items := by
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
      by_cases hpredicate : predicate head
      · have hmem : item ∈ head :: tail.takeWhile predicate := by
          simpa [List.takeWhile_cons, hpredicate] using hitem
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst item
          simp
        · exact List.mem_cons_of_mem head (ih htail)
      · simp [List.takeWhile_cons, hpredicate] at hitem

/- Finite chronological raw-recorder truth on the actual first-live window.
Every retained record carries an actual first or continuing-live choice,
ordinary CHOICE states and memories, the current-payload occupied-field
agreement, the actual recorder output and its exact source-map/raw-increment
identity, plus the arm-indexed retained diagnostic. The original whole rows,
private index, reward table, run interval, and every initial-boundary premise
remain explicit. Empty windows and their terminal endpoint are included. -/
/-- Result type for the exact finite first-live-window recording theorem.
It is parameterized by the original run inputs so the actual-launched adapter
can preserve the same record identities without introducing another trace. -/
def actual_first_live_window_recording_claim
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : Prop :=
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length,
      let record := W[k.val]
      (record.input.rows = rows ∧ record.input.selected = J ∧
        record.input.rewards = rewards ∧
        record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar start count) ∧
      record.output.coordinator.failure = none ∧
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∃ hordinary : ∀ i,
          (record.output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i),
        ((∃ installed arm,
            ∃ hbranch : record.output.preparation.coordinator = .first (.chosen installed arm),
            ∃ hfields : ∀ i, (states i).status ≠ .unoccupied →
              (states i).lastDown = some (installed.registers.payload.downRecord i),
            ∃ htime : installed.registers.time = record.input.time,
            ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
              record.output.preparation.coordinator.selection = some selected ∧
              selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
                record.input installed.registers.payload installed.startRoundResult
                installed.registers.time installed.registers.complementWeights arm htime ∧
              ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                  (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
                CoordinatorRecorderComplementBridge.recorderInput
                  (ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input) installed.registers
                    installed.startRoundResult) ∧
              (∀ i, (states i).status ≠ .unoccupied →
                (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
              ∃ out,
                record.output.coordinator.recording = some out ∧
                (let I := ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input) installed.registers installed.startRoundResult
                 let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
                    (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
                      record.output.preparation installed.registers installed.startRoundResult
                      installed.registers.time arm)
                 let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
                    (CoordinatorRecorderComplementBridge.recorderInput I) v
                    installed.registers.payload.assignment
                    { missing := installed.startRoundResult.pending
                      status := fun i => (states i).status }
                    (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
                 CoordinatorRecorderComplementBridge.run I = some out ∧
                  out.gateArm = E ∧
                  out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                    installed.registers.payload.anchor
                    (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                      (record.input.rewards record.input.time j)) E ∧
                  ∀ j : Fin p.K,
                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                      (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
                    some (if out.gateArm = some j then out.rawArrival else 0)) ∧
                 CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                   selected.view.cutoff record.input.time ∧
                 actual_window_follower_data_claim record selected states rewards) ∨
         (∃ r q base dispatched hstart continuation arm,
            ∃ hbranch : record.output.preparation.coordinator =
              .live r q base (.continuingChosen dispatched hstart continuation arm),
            ∃ hfields : ∀ i, (states i).status ≠ .unoccupied →
              (states i).lastDown = some (r.payload.downRecord i),
            ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
              record.output.preparation.coordinator.selection = some selected ∧
              selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
                record.input (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).payload
                dispatched.startResult record.input.time
                (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights arm rfl ∧
              ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                  (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
                CoordinatorRecorderComplementBridge.recorderInput
                  (ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input)
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    dispatched.startResult) ∧
              (∀ i, (states i).status ≠ .unoccupied →
                (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
              ∃ out,
                record.output.coordinator.recording = some out ∧
                (let I := ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input)
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    dispatched.startResult
                 let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
                    (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
                      record.output.preparation
                      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                      dispatched.startResult record.input.time arm)
                 let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
                    (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
                    { missing := dispatched.startResult.pending
                      status := fun i => (states i).status }
                    (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
                 CoordinatorRecorderComplementBridge.run I = some out ∧
                  out.gateArm = E ∧
                  out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
                    (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                      (record.input.rewards record.input.time j)) E ∧
                  ∀ j : Fin p.K,
                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                      (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
                    some (if out.gateArm = some j then out.rawArrival else 0)) ∧
                 CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                   selected.view.cutoff record.input.time ∧
                 actual_window_follower_data_claim record selected states rewards))

theorem run_first_live_window_recording_truth
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0) (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length,
      let record := W[k.val]
      (record.input.rows = rows ∧ record.input.selected = J ∧
        record.input.rewards = rewards ∧
        record.input.time.val ∈ ReferenceActivePhysicalHorizon.calendar start count) ∧
      record.output.coordinator.failure = none ∧
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∃ hordinary : ∀ i,
          (record.output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i),
        ((∃ installed arm,
            ∃ hbranch : record.output.preparation.coordinator = .first (.chosen installed arm),
            ∃ hfields : ∀ i, (states i).status ≠ .unoccupied →
              (states i).lastDown = some (installed.registers.payload.downRecord i),
            ∃ htime : installed.registers.time = record.input.time,
            ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
              record.output.preparation.coordinator.selection = some selected ∧
              selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
                record.input installed.registers.payload installed.startRoundResult
                installed.registers.time installed.registers.complementWeights arm htime ∧
              ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                  (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
                CoordinatorRecorderComplementBridge.recorderInput
                  (ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input) installed.registers
                    installed.startRoundResult) ∧
              (∀ i, (states i).status ≠ .unoccupied →
                (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
              ∃ out,
                record.output.coordinator.recording = some out ∧
                (let I := ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input) installed.registers installed.startRoundResult
                 let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
                    (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
                      record.output.preparation installed.registers installed.startRoundResult
                      installed.registers.time arm)
                 let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
                    (CoordinatorRecorderComplementBridge.recorderInput I) v
                    installed.registers.payload.assignment
                    { missing := installed.startRoundResult.pending
                      status := fun i => (states i).status }
                    (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
                 CoordinatorRecorderComplementBridge.run I = some out ∧
                  out.gateArm = E ∧
                  out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
                    installed.registers.payload.anchor
                    (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                      (record.input.rewards record.input.time j)) E ∧
                  ∀ j : Fin p.K,
                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                      (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
                    some (if out.gateArm = some j then out.rawArrival else 0)) ∧
                 CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                   selected.view.cutoff record.input.time ∧
                 actual_window_follower_data_claim record selected states rewards) ∨
         (∃ r q base dispatched hstart continuation arm,
            ∃ hbranch : record.output.preparation.coordinator =
              .live r q base (.continuingChosen dispatched hstart continuation arm),
            ∃ hfields : ∀ i, (states i).status ≠ .unoccupied →
              (states i).lastDown = some (r.payload.downRecord i),
            ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
              record.output.preparation.coordinator.selection = some selected ∧
              selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
                record.input (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).payload
                dispatched.startResult record.input.time
                (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights arm rfl ∧
              ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
                  (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
                CoordinatorRecorderComplementBridge.recorderInput
                  (ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input)
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    dispatched.startResult) ∧
              (∀ i, (states i).status ≠ .unoccupied →
                (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
              ∃ out,
                record.output.coordinator.recording = some out ∧
                (let I := ReferenceActivePhysicalStep.liveRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input)
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    dispatched.startResult
                 let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
                    (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
                      record.output.preparation
                      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                      dispatched.startResult record.input.time arm)
                 let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
                    (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
                    { missing := dispatched.startResult.pending
                      status := fun i => (states i).status }
                    (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
                 CoordinatorRecorderComplementBridge.run I = some out ∧
                  out.gateArm = E ∧
                  out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
                    (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                      (record.input.rewards record.input.time j)) E ∧
                  ∀ j : Fin p.K,
                    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                      (ReferenceActiveHorizonMeasurability.roundRecordCode record) j =
                    some (if out.gateArm = some j then out.rawArrival else 0)) ∧
                 CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                   selected.view.cutoff record.input.time ∧
                 actual_window_follower_data_claim record selected states rewards)) := by
  classical
  intro E W k
  have hFollower := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  dsimp only [E, W] at hFollower
  have hCoordinator := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  dsimp only [E, W] at hCoordinator
  have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro i state localMemory hstate
    rw [hseed i] at hstate
    cases hstate
    exact ⟨hunoccupied i, hnone i⟩
  have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
    initial rows J rewards start count hspan active hfirst hinitial
  dsimp only [E, W] at hcarried
  let record := W[k.val]
  have hdata : ∀ i, ∃ state localMemory,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary state localMemory ∧
      ∀ selected : ReferenceActivePhysicalStep.Selection record.input,
        record.output.preparation.coordinator.selection = some selected →
        (state.status ≠ .unoccupied →
          state.lastDown = some (selected.view.payload.downRecord i)) := by
    intro i
    obtain ⟨state, localMemory, next, nextMemory, hchoice, hnext, hfailure, hfields⟩ :=
      hFollower.2 k i
    exact ⟨state, localMemory, hchoice, hfields⟩
  let states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => Classical.choose (hdata i)
  let memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun i => Classical.choose ((hdata i).choose_spec)
  have hordinary : ∀ i,
      (record.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    exact ((hdata i).choose_spec.choose_spec).1
  have hstateFields : ∀ i selected,
      record.output.preparation.coordinator.selection = some selected →
      ((states i).status ≠ .unoccupied →
        (states i).lastDown = some (selected.view.payload.downRecord i)) := by
    intro i selected hselected hi
    exact ((hdata i).choose_spec.choose_spec).2 selected hselected hi
  have hcall := hCoordinator.1 k
  obtain ⟨hfailure, recorded, hrecorded, nextRegisters, nextOwned, nextBase, _⟩ := hcall
  have htrace : ReferenceCoordinatorRecorderCallTrace.recording
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) = some recorded := by
    rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
    change record.output.coordinator.recording = some recorded
    exact hrecorded
  have hhasChoice : (ReferenceActivePhysicalStep.dispatch record.input).selection ≠ none := by
    intro hno
    rw [ReferenceCoordinatorRecorderCallCorrespondence.recording_eq_none_of_no_selection record hno]
      at htrace
    cases htrace
  have hmember : record ∈ W := by
    dsimp [record]
    exact List.getElem_mem k.isLt
  have hrecordRun : record ∈ E.records := by
    have htake := hmember
    dsimp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at htake
    exact mem_of_mem_takeWhile _ htake
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs initial rows J rewards
    start count hspan active record hrecordRun
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards
    start count hspan active
  have htimeMember : record.input.time.val ∈
      ReferenceActivePhysicalHorizon.calendar start count := by
    rw [← htimes]
    exact List.mem_map.mpr ⟨record, hrecordRun, rfl⟩
  have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    have htake := List.mem_takeWhile_imp hmember
    change (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true at htake
    cases hc : ReferenceCollectionPhaseHistory.cutoffChosen record.input with
    | false => rfl
    | true => simp [hc] at htake
  rcases actual_first_or_continuing_record_branch record (hcarried k) hcutoff hhasChoice with
    hfirstBranch | hcontinuingBranch
  · obtain ⟨installed, arm, hbranch⟩ := hfirstBranch
    have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
    rw [hbranch] at hframes
    let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
      record.input installed.registers.payload installed.startRoundResult
      installed.registers.time installed.registers.complementWeights arm hframes.1
    have hselectedAt := ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      record.input installed.registers.payload installed.startRoundResult installed.registers.time
      installed.registers.complementWeights arm hframes.1
    have hselectedPrep : record.output.preparation.coordinator.selection = some selected := by
      rw [hbranch]
      simpa only [selected, ReferenceActivePhysicalStep.DispatchCut.selection] using hselectedAt
    have hfields : ∀ i, (states i).status ≠ .unoccupied →
        (states i).lastDown = some (installed.registers.payload.downRecord i) := by
      intro i hi
      have hf := hstateFields i selected hselectedPrep hi
      exact hf
    have htruth := first_branch_recording_truth record installed arm hbranch states memories
      hordinary hfields
    rcases htruth with ⟨htime, selected, hselected, hselectionEq, hinputSelection, hselectedFields,
      out, hrecording, hidentity⟩
    have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff record.input.time := by
      rw [hselectionEq]
      simpa only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.firstInput] using hframes.2.1
    have hdataTruth := actual_window_follower_data_truth initial rows J rewards start count
      hspan active record hrecordRun selected hselected states memories hordinary
      hselectedFields hlive
    exact ⟨⟨hinputs.1, hinputs.2.1, hinputs.2.2, htimeMember⟩, hfailure,
      ⟨states, memories, hordinary,
      Or.inl ⟨installed, arm, hbranch, hfields, htime, selected, hselected, hselectionEq,
        hinputSelection, hselectedFields, out, hrecording, ⟨hidentity, hlive, hdataTruth⟩⟩⟩⟩
  · obtain ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch⟩ := hcontinuingBranch
    have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
    rw [hbranch] at hframes
    let registers := ReferenceActivePhysicalStep.liveRegistersAt r record.input.time
    let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
      record.input registers.payload dispatched.startResult record.input.time registers.complementWeights arm rfl
    have hselectedAt := ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      record.input registers.payload dispatched.startResult record.input.time registers.complementWeights arm rfl
    have hselectedPrep : record.output.preparation.coordinator.selection = some selected := by
      rw [hbranch]
      exact hselectedAt
    have hfields : ∀ i, (states i).status ≠ .unoccupied →
        (states i).lastDown = some (r.payload.downRecord i) := by
      intro i hi
      have hf := hstateFields i selected hselectedPrep hi
      simpa only [selected, registers, ReferenceActivePhysicalStep.liveRegistersAt,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hf
    have htruth := continuing_branch_recording_truth record r q base dispatched hstart
      continuation arm hbranch states memories hordinary hfields
    rcases htruth with ⟨selected, hselected, hselectionEq, hinputSelection, hselectedFields,
      out, hrecording, hidentity⟩
    have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff record.input.time := by
      rw [hselectionEq]
      simpa only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.liveRegistersAt] using hframes.1
    have hdataTruth := actual_window_follower_data_truth initial rows J rewards start count
      hspan active record hrecordRun selected hselected states memories hordinary
      hselectedFields hlive
    exact ⟨⟨hinputs.1, hinputs.2.1, hinputs.2.2, htimeMember⟩, hfailure,
      ⟨states, memories, hordinary,
      Or.inr ⟨r, q, base, dispatched, hstart, continuation, arm, hbranch, hfields,
        selected, hselected, hselectionEq, hinputSelection, hselectedFields, out, hrecording,
        ⟨hidentity, hlive, hdataTruth⟩⟩⟩⟩

def actual_first_live_window_terminal_claim
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : Prop :=
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∃ hprefix : start + W.length ≤ p.T,
      (∀ i : Fin (p.m - 1), ∃ state memory,
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start W.length hprefix active).finalState.followers i =
          .ordinary state memory ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        state.S + state.backlog ≤ W.length * D p) ∧
      ((W.length = 0 →
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start 0
            (by omega) active).finalState.coordinator = .first) ∧
       (0 < W.length → ∃ registers owned base,
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start W.length hprefix active).finalState.coordinator =
            .live registers owned base)) ∧
      (W.length < count → ∃ hidx : W.length < E.records.length,
        let boundary := E.records[W.length]'hidx
        ReferenceCollectionPhaseHistory.cutoffChosen boundary.input = true ∧
          boundary ∉ W)

/-- Preserve the zero-prefix and terminal endpoints for the same takeWhile
window. The follower endpoint is produced by F, the coordinator endpoint and
the first excluded cutoff record by N. -/
theorem run_first_live_window_terminal_endpoint
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0) (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) :
    actual_first_live_window_terminal_claim initial rows J rewards start count hspan active := by
  classical
  dsimp only [actual_first_live_window_terminal_claim]
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hFollower := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  dsimp only [E, W] at hFollower
  have hCoordinator := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  dsimp only [E, W] at hCoordinator
  obtain ⟨hprefix, hstates⟩ := hFollower.1 W.length (Nat.le_refl _)
  have hcoordinatorEnd := hCoordinator.2.1 W.length (Nat.le_refl _)
  refine ⟨hprefix, ?_, ⟨?_, ?_⟩, hCoordinator.2.2⟩
  · intro i
    obtain ⟨state, memory, hconfiguration, hdomain, hmass, _, _, _, _⟩ := hstates i
    exact ⟨state, memory, hconfiguration, hdomain, hmass⟩
  · intro hzero
    exact (hCoordinator.2.1 0 (Nat.zero_le _)).1 rfl
  · intro hpositive
    obtain ⟨registers, owned, base, hstate⟩ := hcoordinatorEnd.2 hpositive
    exact ⟨registers, owned, base, hstate⟩

private theorem launched_ordinary_decoder
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : ActiveRoundActions.Follower p.m) :
    ActiveFollowerLifecycle.downDecoderStateValid (ReferenceInitializationRun.ordinary x b i) := by
  classical
  have hinitial : ActiveFollowerLifecycle.downDecoderStateValid
      (ReferencePrelaunchFollower.initial p x.eta) :=
    ⟨AffineBatchDecoder.quota_pos p, by
      simp [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial]⟩
  unfold ReferenceInitializationRun.ordinary
  split
  · exact hinitial
  · split
    · exact hinitial
    · rename_i activation _
      have h := ReferencePrelaunchFollower.replay_batch_spec x.eta
        (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row activation
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (ReferenceInitializationRun.elapsed_le_T p b.completed)
      exact ⟨h.1, h.2.1⟩

/-- The original launched-boundary theorem with its complete initialization
relation and prelaunch conditions. This specializes the same recordwise
finite-window result at `blockStop`; the result remains finite and assumes no
source totality. -/
theorem actual_launched_first_live_window_recording_truth
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := fun i =>
      ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    actual_first_live_window_recording_claim initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active ∧
    actual_first_live_window_terminal_claim initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active := by
  classical
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
  let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := fun i =>
    ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  have hfirst : initial.coordinator = .first :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate C_star C_h
      b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hseeds : ∀ i : Fin (p.m - 1), ∃ seed memory,
      initial.followers i = .ordinary seed memory ∧
      seed.S = 0 ∧ seed.delta = 0 ∧ seed.backlog = 0 ∧ seed.lastDown = none ∧
      seed.status = .unoccupied ∧ ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ seed.buffer, saved.calendarRound ≤ start) ∧
      ActiveFollowerLifecycle.downDecoderStateValid seed := by
    intro i
    obtain ⟨seed, memory, hseed, hS, hdelta, hbacklog, hunoccupied, hnone,
      hvalid, hpair, htime⟩ :=
      ReferenceFirstFollowerMassBudget.actual_launched_follower_seed source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    obtain ⟨state, mem, hconfig, hstate, _⟩ :=
      ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    have hsame : seed = state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hseed.symm.trans hconfig)).1
    have hdecoder : ActiveFollowerLifecycle.downDecoderStateValid seed := by
      rw [hsame, hstate]
      exact launched_ordinary_decoder _ _ _
    exact ⟨seed, memory, hseed, hS, hdelta, hbacklog, hnone, hunoccupied,
      hvalid, hpair, htime, hdecoder⟩
  choose seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch using hseeds
  have hrecording := run_first_live_window_recording_truth initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active hfirst
    seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch
  have hterminal := run_first_live_window_terminal_endpoint initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active hfirst
    seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch
  exact ⟨hrecording, hterminal⟩

end Bandits.Support.ReferenceFirstWindowRecordingTruth

end
