/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveDataOwnership

/-!
# Local collection recording in the reference coordinator

This module relates the checked coordinator recorder to its computed local
collection branch and to the recording retained by the complete physical
round. Local ordinary and unoccupied conditions are explicit inputs; they are
not claimed as run-wide invariants.

Sources: sources/zip4/manuscript/05_binary_transport.tex:354-396,408-423,
sources/zip4/manuscript/06_interruptions.tex:246-269,277-294,391-397, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCoordinatorCollectionRecording

open Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.SnapshotRecordingKernel


variable {p : Bandits.Support.ConstructorDimensions.Parameters}
  {rate : Bandits.Support.ReferenceActivePhysicalStep.RateInput p}

private theorem collectionFinish_recording (x : Bandits.Support.ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Bandits.Support.ReferenceActivePhysicalStep.Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : Bandits.Support.CoordinatorRecordingOperation.Output p) (cut : Bandits.Support.ReferenceActivePhysicalStep.UpCut p rate) :
    (Bandits.Support.ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).recording = some recording := by
  classical
  cases hresult : cut.result with
  | invalid => simp [Bandits.Support.ReferenceActivePhysicalStep.collectionFinish, hresult,
      Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
  | success result =>
      simp only [Bandits.Support.ReferenceActivePhysicalStep.collectionFinish, hresult]
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected ledger => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock ledger.pending x.row <;>
            simp [hclock, Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
  | rejected result =>
      simp only [Bandits.Support.ReferenceActivePhysicalStep.collectionFinish, hresult]
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected ledger => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock ledger.pending x.row <;>
            simp [hclock, Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]

/-- The complete collection tail keeps the checked recorder's result in its
diagnostic field for every start, receive, ledger-finish, and clock-finish
outcome, including rejected and invalid outcomes. -/
theorem collectionPostChoice_recording_eq_run {x : Bandits.Support.ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : Bandits.Support.ReferenceActivePhysicalStep.PreparedRound x) (payload : Bandits.Support.ReferenceActivePhysicalStep.Payload rate)
    (ledger : Bandits.Support.ReferenceActivePhysicalStep.Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : FastArm payload.slowSet → ℝ) :
    (Bandits.Support.ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).recording =
      Bandits.Support.CoordinatorRecorderComplementBridge.run (Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) := by
  classical
  cases hrecord : Bandits.Support.CoordinatorRecorderComplementBridge.run (Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp [Bandits.Support.ReferenceActivePhysicalStep.collectionPostChoice, hrecord, Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      simp only [Bandits.Support.ReferenceActivePhysicalStep.collectionPostChoice, hrecord]
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [Bandits.Support.ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerStarted =>
          exact collectionFinish_recording x payload started recording
            (Bandits.Support.ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)

private theorem collectionSourceMap_none_of_rejected_test
    {payload : Bandits.Support.ReferenceActivePhysicalStep.Payload rate} (input : Bandits.Support.CoordinatorRecorderComplementBridge.Input payload)
    (hcollection : input.mode = Bandits.Support.CoordinatorRecorderComplementBridge.LocalMode.collection)
    (hvalidLocal : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input) (enabled : Bool)
    (hsource : Bandits.Support.CoordinatorRecordingOperation.selectedRecorder (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input) = coordinator p.two_le_m)
    (hpilotArm : input.ownArm = pilotDraw (K_pos p) (coordinator p.two_le_m)
      (sliceAt input.time input.row.2))
    (hrejected : Bandits.Support.CoordinatorRecordingOperation.selectedSlot (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input) ≠ dataSlot ∨
      enabled = false ∨
      ¬ Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input) ∨
      ¬ Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤
        Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hvalidLocal) :
    Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input)
      (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hvalidLocal) enabled = none := by
  classical
  let a := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input
  let hv := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hvalidLocal
  have hmode : a.mode = Bandits.Support.CoordinatorRecordingOperation.LocalMode.collection := by
    simp [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, hcollection]
  by_cases henabled : enabled = true
  · cases hm : Bandits.Support.SnapshotRecordingKernel.recordingMap p .collection enabled a.eta hv.eta_pos
        hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos hv.current_pos
        hv.anchor_le_current hv.current_le_twice_anchor
        (sliceAt a.time a.row.2) with
    | none =>
        simpa [Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart,
          a, hv, hsource, henabled] using hm
    | some arm =>
        have hm' : Bandits.Support.SnapshotRecordingKernel.recordingMap p .collection true a.eta hv.eta_pos
            hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos hv.current_pos
            hv.anchor_le_current hv.current_le_twice_anchor
            (sliceAt a.time a.row.2) = some arm := by
          simpa [henabled] using hm
        have htests := (Bandits.Support.SnapshotRecordingKernel.recordingMap_some_iff p .collection a.eta hv.eta_pos
          hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos hv.current_pos
          hv.anchor_le_current hv.current_le_twice_anchor
          (sliceAt a.time a.row.2) arm).mp hm'
        have hselected : recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec (sliceAt input.time input.row.2)) = coordinator p.two_le_m := by
          simpa [Bandits.Support.CoordinatorRecordingOperation.selectedRecorder,
            a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
            Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights] using hsource
        have harm : arm = input.ownArm := by
          have haction : pilotDraw (K_pos p) (coordinator p.two_le_m)
              (sliceAt input.time input.row.2) = arm := by
            simpa [Bandits.Support.SnapshotRecordingKernel.dataAction, hselected,
              a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights] using htests.2.1
          exact haction.symm.trans (by
            simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights] using
                hpilotArm.symm)
        rcases hrejected with hslot | henabledFalse | hmask | hthin
        · exact False.elim (hslot (by simpa [Bandits.Support.CoordinatorRecordingOperation.selectedSlot] using htests.1))
        · exact False.elim (by
            have hfalse : true = false := henabled.symm.trans henabledFalse
            cases hfalse)
        · have hmaskOp : Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses a := by
            simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
              Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses, harm, hselected] using
              htests.2.2.2.1
          exact False.elim (hmask (by
            simpa [Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses,
              a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights] using hmaskOp))
        · have hthreshold := Bandits.Support.CoordinatorRecordingOperation.collectionThreshold_eq_snapshot a hv hmode
          have hthinOp : (coordinate Label.thin (sliceAt a.time a.row.2)).val ≤
              Bandits.Support.CoordinatorRecordingOperation.coordinatorThreshold a hv := by
            rw [hthreshold]
            simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
              hselected, harm] using htests.2.2.2.2
          have hthin' : Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤
              Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hvalidLocal := by
            simpa [a, hv, Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar,
              Bandits.Support.CoordinatorRecorderComplementBridge.threshold,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
              Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
              Bandits.Support.CoordinatorRecorderComplementBridge.operationMode] using hthinOp
          exact False.elim (hthin hthin')
  · simp [Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart, hsource, Bandits.Support.SnapshotRecordingKernel.recordingMap,
      henabled]

private theorem collectionRun_recording_identification
    (x : Bandits.Support.ReferenceActivePhysicalStep.RoundInput p rate) (payload : Bandits.Support.ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : FastArm payload.slowSet → ℝ)
    (hchoice : Bandits.Support.CoordinatorLocalArmChoice.ChoiceInputsValid payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights)
    (hnotLive : ¬ Bandits.Support.CoordinatorLocalArmChoice.assignmentIsLive payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time)
    (hboundary : started.clock.g ≤ p.T + 1)
    (hchoiceArm : Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice payload started.pending
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights x.row =
        some (Bandits.Support.ReferenceActivePhysicalStep.prepare x).coordinator.arm)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((Bandits.Support.ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hunoccupied : ∀ i, (states i).status = .unoccupied) :
    let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
    let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
    let localValid : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨hboundary, fun j => ⟨hchoice.anchor_le_current j,
        hchoice.current_le_twice_anchor j⟩⟩
    let a := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input
    let hv := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a)
    let reward (j : Fin p.K) :=
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)
    let E := Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv enabled
    ∃ out, Bandits.Support.CoordinatorRecorderComplementBridge.run input = some out ∧ out.gateArm = E ∧
      out.rawArrival = Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor reward E := by
  classical
  dsimp only
  let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
  let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
  have hlocal : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
    ⟨hboundary, fun j => ⟨hchoice.anchor_le_current j,
      hchoice.current_le_twice_anchor j⟩⟩
  let a := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input
  let hv := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hlocal
  let enabled := decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a)
  let E := Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv enabled
  let reward : ActiveRoundActions.RewardRow p.K :=
    ⟨fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (x.rewards x.time j),
      fun j => RealRewardGridCount.realRewardGridValue_mem_Icc
        (D p) (D_pos p) (x.rewards x.time j)⟩
  let runInput := Bandits.Support.CoordinatorRecorderComplementBridge.run input
  have hsourceInput : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = Bandits.Support.CoordinatorRecordingOperation.selectedRecorder a := rfl
  have hdataInput : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = Bandits.Support.CoordinatorRecordingOperation.selectedSlot a := rfl
  have hmap_none (hsource : Bandits.Support.CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m)
      (hdata : Bandits.Support.CoordinatorRecordingOperation.selectedSlot a = dataSlot)
      (hrejected : enabled = false ∨ ¬ Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses a ∨
      ¬ Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤
        Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal) : E = none := by
    have hpilotArm : input.ownArm = pilotDraw (K_pos p) (coordinator p.two_le_m)
        (sliceAt input.time input.row.2) := by
      have hdataRow : slotDraw (sliceAt x.time x.row.2) = dataSlot := by
        simpa [Bandits.Support.CoordinatorRecordingOperation.selectedSlot, a,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          Bandits.Support.CoordinatorRecorderComplementBridge.operationMode,
          Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input,
          sliceAt] using hdata
      have hchoiceData := Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
        payload started.pending
        (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time weights (x.row.2 x.time) hchoice
        (by intro hfast; exact hnotLive hfast.1) hdataRow
      have hchoiceData' : Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice payload
          started.pending (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time weights x.row =
            some (pilotDraw (K_pos p) (coordinator p.two_le_m) (sliceAt x.time x.row.2)) := by
        simpa [Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice, sliceAt] using hchoiceData
      have harm := Option.some.inj (hchoiceArm.symm.trans hchoiceData')
      simpa [input, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput,
        sliceAt] using harm
    have hsourceBridge : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m := by
      rw [hsourceInput]
      exact hsource
    have hcollection : input.mode = Bandits.Support.CoordinatorRecorderComplementBridge.LocalMode.collection := rfl
    exact collectionSourceMap_none_of_rejected_test input hcollection hlocal
      enabled hsourceBridge hpilotArm (Or.inr (by simpa [a, hv] using hrejected))
  have hrun_zero_not_data (hdata : Bandits.Support.CoordinatorRecordingOperation.selectedSlot a ≠ dataSlot) :
      runInput = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p) := by
    change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p)
    apply Bandits.Support.CoordinatorRecorderComplementBridge.run_zero_of_not_data input hlocal
    intro h
    apply hdata
    exact hdataInput.symm.trans h
  have hrun_zero_other_source (hdata : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot)
      (hsource : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input ≠ coordinator p.two_le_m) :
      runInput = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p) := by
    change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p)
    exact Bandits.Support.CoordinatorRecorderComplementBridge.run_zero_of_other_source input hlocal hdata hsource
  have hrun_zero_frozen (hdata : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot)
      (hsource : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m)
      (hfrozen : Bandits.Support.CoordinatorRecordingOperation.isFrozen a) : runInput = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p) := by
    change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p)
    exact Bandits.Support.CoordinatorRecorderComplementBridge.run_zero_of_frozen input hlocal hdata hsource
      (by simpa [Bandits.Support.CoordinatorRecorderComplementBridge.isFrozen] using hfrozen)
  have hrun_zero_mask (hdata : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot)
      (hsource : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m)
      (hnotFrozen : ¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a) (hmask : ¬ Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses input) :
      runInput = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p) := by
    change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p)
    have howned : Bandits.Support.CoordinatorRecorderComplementBridge.ownsArm input := by
      simp [Bandits.Support.CoordinatorRecorderComplementBridge.ownsArm,
        Bandits.Support.CoordinatorRecordingOperation.ownsArm,
        Bandits.Support.CoordinatorRecorderComplementBridge.operationMode,
        Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input]
    exact Bandits.Support.CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected input hlocal hdata hsource
      (by simpa [Bandits.Support.CoordinatorRecorderComplementBridge.isFrozen] using hnotFrozen)
      howned hmask
  have hrun_zero_thin (hdata : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot)
      (hsource : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m)
      (hnotFrozen : ¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a) (hmask : Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses input)
      (hthin : ¬ Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤ Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal) :
      runInput = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p) := by
    change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p)
    have howned : Bandits.Support.CoordinatorRecorderComplementBridge.ownsArm input := by
      simp [Bandits.Support.CoordinatorRecorderComplementBridge.ownsArm,
        Bandits.Support.CoordinatorRecordingOperation.ownsArm,
        Bandits.Support.CoordinatorRecorderComplementBridge.operationMode,
        Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input]
    exact Bandits.Support.CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected input hlocal hdata hsource
      (by simpa [Bandits.Support.CoordinatorRecorderComplementBridge.isFrozen] using hnotFrozen)
      howned hmask hthin
  have hrun_success (hdata : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot)
      (hsource : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m)
      (hnotFrozen : ¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a) (hmask : Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses input)
      (hthin : Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤ Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal) :
      ∃ out, runInput = some out ∧ out.gateArm = E ∧
        out.rawArrival = Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (x.rewards x.time j)) E := by
    have hdata' : slotDraw (x.row.2 x.time).1 = dataSlot := by
      simpa [Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, Bandits.Support.CoordinatorRecordingOperation.selectedSlot, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, a, sliceAt] using hdata
    have hsource' : Bandits.Support.CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m := by
      exact hsourceInput.symm.trans hsource
    have hmask' : Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses a := hmask
    have hthreshold := Bandits.Support.CoordinatorRecordingOperation.collectionThreshold_eq_snapshot a hv (by
      simp [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights, Bandits.Support.CoordinatorRecorderComplementBridge.operationMode,
        Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input])
    have hthin' : (coordinate Label.thin (sliceAt x.time x.row.2)).val ≤
        Bandits.Support.CoordinatorRecordingOperation.coordinatorThreshold a hv := by
      change Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤ Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal at hthin
      simpa [Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar, Bandits.Support.CoordinatorRecorderComplementBridge.threshold, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, a, hv,
        Bandits.Support.CoordinatorRecordingOperation.coordinatorThreshold, hthreshold] using hthin
    have hchoiceData := Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data payload started.pending
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights (x.row.2 x.time)
      hchoice (by
        intro hfast
        exact hnotLive hfast.1) hdata'
    have hcoordinatorArm : prepared.coordinator.arm =
      pilotDraw (K_pos p) (coordinator p.two_le_m) (x.row.2 x.time).1 := by
      apply Option.some.inj
      exact hchoiceArm.symm.trans (by
        simpa [Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice, sliceAt] using hchoiceData)
    have hpilotActions : ∀ player : Fin p.m,
        prepared.arms.actions player = pilotDraw (K_pos p) player
          (sliceAt x.time x.row.2) := by
      intro player
      by_cases hc : player = coordinator p.two_le_m
      · subst player
        simpa [sliceAt] using prepared.action_coordinator.trans hcoordinatorArm
      · let i := followerIndex p.two_le_m player hc
        have harm := Bandits.Support.ReferenceActiveDataOwnership.ordinary_data_arm payload i x.row (x.state.activations i)
          x.time (x.active i) (x.state.followers i) (states i) (memories i)
          (hordinary i) (fun h => False.elim (h (hunoccupied i))) hdata'
        have hplayer := followerPlayer_followerIndex p.two_le_m player hc
        calc
          prepared.arms.actions player = prepared.arms.actions
              (followerPlayer p.two_le_m i) := by rw [hplayer]
          _ = (DeclaredFollowerLocalRound.prepare rate i x.row
              (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm :=
            prepared.action_follower i
          _ = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
              (sliceAt x.time x.row.2) := by simpa [hunoccupied i, sliceAt] using harm
          _ = pilotDraw (K_pos p) player (sliceAt x.time x.row.2) := by
            rw [hplayer]
    have hmaskPilot : ∀ player : Fin p.m,
        player ≠ coordinator p.two_le_m →
        pilotDraw (K_pos p) player (sliceAt x.time x.row.2) ≠
          pilotDraw (K_pos p) (coordinator p.two_le_m) (sliceAt x.time x.row.2) := by
      intro player hne
      have hm := hmask' player hne
      have hm' : pilotDraw (K_pos p) player (sliceAt x.time x.row.2) ≠ prepared.coordinator.arm := by
        simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, sliceAt] using hm
      have harm' : prepared.coordinator.arm =
          pilotDraw (K_pos p) (coordinator p.two_le_m) (sliceAt x.time x.row.2) := by
        simpa [sliceAt] using hcoordinatorArm
      intro heq
      exact hm' (heq.trans harm'.symm)
    have hfree : FiniteBanditModel.collisionFreeFor
        (fun player => pilotDraw (K_pos p) player (sliceAt x.time x.row.2))
        (coordinator p.two_le_m) := by
      intro player hne
      exact hmaskPilot player hne
    have hactualFree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
        (coordinator p.two_le_m) := by
      intro player hne
      rw [hpilotActions player, hpilotActions (coordinator p.two_le_m)]
      exact hmaskPilot player hne
    have hfeedbackGrid : prepared.feedback.feedback (coordinator p.two_le_m) =
        x.rewards x.time (pilotDraw (K_pos p) (coordinator p.two_le_m)
          (sliceAt x.time x.row.2)) := by
      rw [prepared.feedback_rule, ite_eq_left hactualFree, hpilotActions]
    have hfeedback : Bandits.Support.CoordinatorRecordingOperation.observationValue a =
        FiniteBanditModel.playerFeedback
          (fun player => pilotDraw (K_pos p) player (sliceAt x.time x.row.2))
          reward.val (coordinator p.two_le_m) := by
      have hobs : Bandits.Support.CoordinatorRecordingOperation.observationValue a =
          reward.val (pilotDraw (K_pos p) (coordinator p.two_le_m)
            (sliceAt x.time x.row.2)) := by
        simp [Bandits.Support.CoordinatorRecordingOperation.observationValue, a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, Bandits.Support.ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation,
          input, reward, hfeedbackGrid]
      rw [hobs, FiniteBanditModel.playerFeedback, ite_eq_left hfree]
    obtain ⟨out, hrun, hgate, hpart, hraw⟩ :=
      Bandits.Support.CoordinatorRecordingOperation.collection_coordinator_recording_agrees a hv reward rfl
        (by simpa [Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, Bandits.Support.CoordinatorRecordingOperation.selectedSlot, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, a] using hdata)
        hsource' hnotFrozen
        (by simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, sliceAt] using hcoordinatorArm)
        hmask' hthin' hfeedback
    have hrunBridge : runInput = some out := by
      change Bandits.Support.CoordinatorRecorderComplementBridge.run input = some out
      rw [Bandits.Support.CoordinatorRecorderComplementBridge.run_eq_accepted input, hrun]
    have hpartE : E = some a.ownArm := by
      simpa [E, enabled, hnotFrozen] using hpart
    have hrawE : out.rawArrival =
        Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (x.rewards x.time j)) E := by
      have hrecordingMap : Bandits.Support.SnapshotRecordingKernel.recordingMap p .collection true a.eta hv.eta_pos
          hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos hv.current_pos
          hv.anchor_le_current hv.current_le_twice_anchor (sliceAt a.time a.row.2) =
            some a.ownArm := by
        simpa [Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart, hsource'] using hpart
      have hfloor := Bandits.Support.SnapshotRecordingKernel.collectionPhysicalIncrement_eq_floor p a.eta hv.eta_pos
        hv.eta_source_cap a.anchor a.currentWeights hv.anchor_pos hv.current_pos
        hv.anchor_le_current hv.current_le_twice_anchor (sliceAt a.time a.row.2)
        reward a.ownArm hrecordingMap
      rw [hraw]
      simp only [Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceIncrement,
        hsource', hpartE, Bandits.Support.SnapshotRecordingKernel.recordedIncrement]
      simpa [a, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
        Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, reward] using hfloor
    exact ⟨out, hrunBridge, by simpa [hpartE] using hgate, hrawE⟩
  have hzero_raw (hE : E = none) :
      (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p).rawArrival =
        Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (x.rewards x.time j)) E := by
    simp [Bandits.Support.CoordinatorRecordingOperation.zeroOutput,
      Bandits.Support.SnapshotRecordingKernel.recordedIncrement, hE]
  have hzero_gate (hE : E = none) :
      (Bandits.Support.CoordinatorRecordingOperation.zeroOutput p).gateArm = E := by
    simpa [Bandits.Support.CoordinatorRecordingOperation.zeroOutput] using hE.symm
  by_cases hdata : Bandits.Support.CoordinatorRecordingOperation.selectedSlot a = dataSlot
  · have hdataBridge : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input = dataSlot := hdataInput.trans hdata
    by_cases hsource : Bandits.Support.CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m
    · have hsourceBridge : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input = coordinator p.two_le_m :=
        hsourceInput.trans hsource
      by_cases hfrozen : Bandits.Support.CoordinatorRecordingOperation.isFrozen a
      · have henabled : enabled = false := by simp [enabled, hfrozen]
        have hrun := hrun_zero_frozen hdataBridge hsourceBridge hfrozen
        have hE := hmap_none hsource hdata (Or.inl henabled)
        exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
          hzero_raw hE⟩
      · by_cases hmask : Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses input
        · by_cases hthin : Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤ Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal
          · simpa [runInput, E, enabled, a, hv, input, prepared] using
              hrun_success hdataBridge hsourceBridge hfrozen hmask hthin
          · have hnotThin : ¬ Bandits.Support.CoordinatorRecorderComplementBridge.thinScalar input ≤
                Bandits.Support.CoordinatorRecorderComplementBridge.threshold input hlocal := hthin
            have hrun := hrun_zero_thin hdataBridge hsourceBridge hfrozen hmask hthin
            have hE := hmap_none hsource hdata (Or.inr (Or.inr hnotThin))
            exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
              hzero_raw hE⟩
        · have hmaskO : ¬ Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses a := by
            simpa [Bandits.Support.CoordinatorRecorderComplementBridge.ownMaskPasses, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput, Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
              Bandits.Support.CoordinatorRecorderComplementBridge.operationMode, Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input, a, Bandits.Support.CoordinatorRecordingOperation.ownMaskPasses] using hmask
          have hrun := hrun_zero_mask hdataBridge hsourceBridge hfrozen hmask
          have hE := hmap_none hsource hdata (Or.inr (Or.inl hmaskO))
          exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
            hzero_raw hE⟩
    · have hsourceBridge : Bandits.Support.CoordinatorRecorderComplementBridge.selectedRecorder input ≠ coordinator p.two_le_m := by
        intro heq
        apply hsource
        exact hsourceInput.symm.trans heq
      have hrun := hrun_zero_other_source hdataBridge hsourceBridge
      have hE : E = none := by
        simp [E, Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart, hsource]
      exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
        hzero_raw hE⟩
  · have hdataBridge : Bandits.Support.CoordinatorRecorderComplementBridge.selectedSlot input ≠ dataSlot := by
      intro hd
      apply hdata
      exact hdataInput.symm.trans hd
    have hrun := hrun_zero_not_data hdata
    by_cases hsource : Bandits.Support.CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m
    · have hE : E = none := by
        simp only [E, Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart, hsource]
        have hslot : slotDraw (sliceAt a.time a.row.2) ≠ dataSlot := by
          simpa [Bandits.Support.CoordinatorRecordingOperation.selectedSlot,
            Bandits.Support.PublicDiscreteDraws.slotDraw,
            Bandits.Support.CanonicalRecordingSlice.slotFromScalar] using hdata
        by_cases henabled : enabled = true
        · simp [Bandits.Support.SnapshotRecordingKernel.recordingMap, henabled, hslot]
        · simp [Bandits.Support.SnapshotRecordingKernel.recordingMap, henabled]
      exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
        hzero_raw hE⟩
    · have hE : E = none := by
        simp [E, Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart, hsource]
      exact ⟨Bandits.Support.CoordinatorRecordingOperation.zeroOutput p, hrun, hzero_gate hE,
        hzero_raw hE⟩

/-- Recording on the first computed cutoff uses the original StartRound,
initialized ledger, payload, complement registers, and follower PREPARE
configurations. The returned physical recording is the exact checked local
run, with its cutoff-derived collection enable bit and integer increment. -/
theorem cutoff_recording_identification {x : Bandits.Support.ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time) (Bandits.Support.ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending = .ok dispatched.startResult)
    (newLedger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time))
    (hinit : dispatched.collectionInitialization = .success (some newLedger))
    (hcand : newLedger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time) (Bandits.Support.ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)
    (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time) (Bandits.Support.ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)
    (hclock : dispatched.startResult.clock =
      { (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock with
        u := some (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).time })
    (hpending : dispatched.startResult.pending = Finset.univ)
    (hnone : dispatched.startResult.assignmentStart = none)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult
      x.time (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hcut : (Bandits.Support.ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base
      (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selection))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((Bandits.Support.ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hunoccupied : ∀ i, (states i).status = .unoccupied) :
    let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
    let payload := r.payload
    let started := dispatched.startResult
    let weights := (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
    let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
    let localValid : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨selection.recorderBoundaryValid, fun j =>
        ⟨selection.choiceInputsValid.anchor_le_current j,
          selection.choiceInputsValid.current_le_twice_anchor j⟩⟩
    let a := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input
    let hv := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a)
    let reward (j : Fin p.K) :=
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)
    let E := Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv enabled
    (∃ out, Bandits.Support.CoordinatorRecorderComplementBridge.run input = some out ∧ (Bandits.Support.ReferenceActivePhysicalStep.step x).coordinator.recording = some out ∧
      out.gateArm = E ∧
      out.rawArrival = Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor reward E) ∧
      enabled = Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger) x.time := by
  classical
  dsimp only
  let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
  let started := dispatched.startResult
  let weights : FastArm r.payload.slowSet → ℝ :=
    (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
  let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared r.payload started weights
  have hcutoffRound :
      Bandits.Support.CoordinatorLocalArmChoice.cutoffRound (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) = x.time.val + 1 := by
    rw [Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock]
    simp [started, hclock, Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt]
  have hnotLive : ¬ Bandits.Support.CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time := by
    intro hlive
    rcases hlive with ⟨_, hlive⟩
    rw [hcutoffRound] at hlive
    exact (Nat.lt_irrefl (x.time.val + 1)) hlive
  have hchoice : Bandits.Support.CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights := by
    simpa [started, weights, Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt] using selection.choiceInputsValid
  have hphysicalArm : prepared.coordinator.arm = selection.arm := by
    rw [hcut]
    simpa using Bandits.Support.ReferenceActivePhysicalStep.live_arm_equation r q base
      (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selection)
  have hchoiceArm : Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice r.payload started.pending
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights x.row =
        some prepared.coordinator.arm := by
    rw [hphysicalArm]
    simpa [started, weights] using selection.armChoice_eq
  have hboundary : started.clock.g ≤ p.T + 1 := by
    simpa [started, Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt] using selection.recorderBoundaryValid
  have hlocal : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
    ⟨hboundary, fun j => ⟨hchoice.anchor_le_current j,
      hchoice.current_le_twice_anchor j⟩⟩
  obtain ⟨out, hrun, hgate, hraw⟩ := collectionRun_recording_identification
    x r.payload started weights hchoice hnotLive hboundary hchoiceArm
    states memories hordinary hunoccupied
  have hpost : prepared.observeCoordinator =
      Bandits.Support.ReferenceActivePhysicalStep.collectionPostChoice prepared r.payload
        (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger) started weights := by
    have hselected : (Bandits.Support.ReferenceActivePhysicalStep.DispatchCut.live r q base
        (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selection)).selection ≠ none := by
      simp [Bandits.Support.ReferenceActivePhysicalStep.DispatchCut.selection,
        Bandits.Support.ReferenceActivePhysicalStep.selectionAt]
    have heq := Bandits.Support.ReferenceActivePhysicalStep.observeCoordinator_live_equation prepared r q base
      (.cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selection)
      hcut
    rw [heq, ite_eq_right hselected]
    rfl
  have hstep : (Bandits.Support.ReferenceActivePhysicalStep.step x).coordinator.recording = some out := by
    change prepared.observeCoordinator.recording = some out
    rw [hpost]
    exact (@collectionPostChoice_recording_eq_run p rate x prepared r.payload
      (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger) started weights).trans hrun
  have hfields := Bandits.Support.ReferenceActivePhysicalStep.sharedLedger_fields newLedger
  have hgridEq : (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary =
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.g := hdomain.2.1
  have hsigma : 0 < (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger).sigma := by
    rw [hfields.2.1, hcand]
    simp [CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt]
  have hcutoffEq : (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger).cutoff = x.time.val + 1 := by
    rw [hfields.2.2.1, hcand]
    rfl
  have hfreezeEq : (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt =
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary := by
    rw [hfields.2.2.2.1, hcand]
    rfl
  have hboundaryEq : (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary = started.clock.g := by
    calc
      _ = (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.g := hgridEq
      _ = started.clock.g := by
        symm
        simpa [started, Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt] using
          congrArg CoordinatorPhaseClock.ClockRegisters.g hclock
  have hsigmaLedger : 0 < newLedger.sigma := by
    rw [← hfields.2.1]
    exact hsigma
  have hcutoffLedger : newLedger.cutoff = x.time.val + 1 := by
    rw [← hfields.2.2.1]
    exact hcutoffEq
  have hfreezeLedger : newLedger.freezeAt =
      (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary := by
    rw [← hfields.2.2.2.1]
    exact hfreezeEq
  have hleftEnabled : decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen
      (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input)) =
      decide (x.time.val + 1 <
        (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary) := by
    simp [Bandits.Support.CoordinatorRecordingOperation.isFrozen,
      Bandits.Support.CoordinatorRecordingOperation.sourceCalendarRound,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      Bandits.Support.CoordinatorRecorderComplementBridge.sourceStart,
      Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input,
      hboundaryEq]
  have hrightEnabled : Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled
      (Bandits.Support.ReferenceActivePhysicalStep.sharedLedger newLedger) x.time =
      decide (x.time.val + 1 <
        (Bandits.Support.ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary) := by
    simp [Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled,
      Bandits.Support.ReferenceActivePhysicalStep.sharedLedger,
      hsigmaLedger, hcutoffLedger, hfreezeLedger]
  have henabled := hleftEnabled.trans hrightEnabled.symm
  exact ⟨⟨out, hrun, hstep, hgate, hraw⟩, henabled⟩

/-- Recording during a continuing collection round uses the retained
collection snapshot, exact complement weights, clock result, and actual
follower PREPARE configurations. The recorder output is retained by the full
physical step, and its increment is the accepted source floor. -/
theorem continuing_collection_recording_identification {x : Bandits.Support.ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : Bandits.Support.ReferenceActivePhysicalStep.Payload rate) (ledger : Bandits.Support.ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (Bandits.Support.ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (Bandits.Support.ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (Bandits.Support.ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) = true)
    (hcut : (Bandits.Support.ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((Bandits.Support.ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hunoccupied : ∀ i, (states i).status = .unoccupied) :
    let source := Bandits.Support.ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
    let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
    let started := snapshot.clockStarted
    let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
    let localValid : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
      ⟨boundary, fun j => ⟨snapshot.inputsValid.choice_valid.anchor_le_current j,
        snapshot.inputsValid.choice_valid.current_le_twice_anchor j⟩⟩
    let a := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input
    let hv := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput_inputsValid input localValid
    let enabled := decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen a)
    let reward (j : Fin p.K) :=
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)
    let E := Bandits.Support.CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv enabled
    (∃ out, Bandits.Support.CoordinatorRecorderComplementBridge.run input = some out ∧ (Bandits.Support.ReferenceActivePhysicalStep.step x).coordinator.recording = some out ∧
      out.gateArm = E ∧
      out.rawArrival = Bandits.Support.SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor reward E) ∧
      enabled = Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled ledger x.time := by
  classical
  dsimp only
  let source := Bandits.Support.ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  let weights : FastArm payload.slowSet → ℝ := by
    simpa [source, Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using
      (CoordinatorCollectionInteractive.PreObservationInputs.weights source
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
  let prepared := Bandits.Support.ReferenceActivePhysicalStep.prepare x
  let started := snapshot.clockStarted
  let input := Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
  have hcutoff : Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
      some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
    rw [snapshot.clockStarted_frame.1, core.clock_cutoff_eq]
    rfl
  have htimeValid := core.clock_start_time_valid
  have htime : cutoff.val ≤ x.time.val := by
    have hsigmaFrame : clock.sigma = some payload.sigma := by
      simpa [Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using core.clock_sigma_eq
    have hcutoffFrame : clock.u = some cutoff := by
      simpa [Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using core.clock_cutoff_eq
    have htimeParts : (payload.sigma.val < x.time.val) ∧ cutoff.val ≤ x.time.val := by
      change CoordinatorPhaseClock.startRoundTimeValid p x.time clock at htimeValid
      unfold CoordinatorPhaseClock.startRoundTimeValid at htimeValid
      rw [hsigmaFrame, hcutoffFrame] at htimeValid
      simpa [Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using htimeValid
    exact htimeParts.2
  have hnotLive : ¬ Bandits.Support.CoordinatorLocalArmChoice.assignmentIsLive payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time := by
    intro hlive
    have hcutoffRound : Bandits.Support.CoordinatorLocalArmChoice.cutoffRound
        (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) = cutoff.val + 1 := by
      rw [hcutoff]
      simp [Bandits.Support.CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorCollectionUpRoundStep.localCutoff,
        CoordinatorCollectionUpRoundStep.sourceCutoff]
    have hge : Bandits.Support.CoordinatorLocalArmChoice.cutoffRound
        (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) ≤
        Bandits.Support.CoordinatorLocalArmChoice.sourceRound x.time := by
      rw [hcutoffRound]
      simp only [Bandits.Support.CoordinatorLocalArmChoice.sourceRound]
      omega
    exact (not_lt_of_ge hge) hlive.2
  have hchoice : Bandits.Support.CoordinatorLocalArmChoice.ChoiceInputsValid payload
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights := by
    simpa [hcutoff, weights, source,
      Bandits.Support.ReferenceActivePhysicalStep.collectionInput,
      CoordinatorCollectionInteractive.PreObservationInputs.weights,
      CoordinatorCollectionUpRoundStep.Inputs.weights] using
        snapshot.inputsValid.choice_valid
  have hphysicalArm : prepared.coordinator.arm = snapshot.arm := by
    have harm := Bandits.Support.ReferenceActivePhysicalStep.collection_arm_equation payload ledger clock cutoff
      (.continuing core snapshot boundary scores)
    rw [hcut]
    simpa using harm
  have hchoiceArm : Bandits.Support.CoordinatorLocalArmChoice.coordinatorArmChoice payload started.pending
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time weights x.row =
        some prepared.coordinator.arm := by
    rw [hcutoff, hphysicalArm]
    simpa [weights, source, Bandits.Support.ReferenceActivePhysicalStep.collectionInput,
      CoordinatorCollectionInteractive.PreObservationInputs.weights,
      CoordinatorCollectionUpRoundStep.Inputs.weights] using snapshot.armChoice_eq
  have hboundary : started.clock.g ≤ p.T + 1 := by
    simpa [started] using boundary
  have hlocal : Bandits.Support.CoordinatorRecorderComplementBridge.LocalInputsValid input :=
    ⟨hboundary, fun j => ⟨hchoice.anchor_le_current j,
      hchoice.current_le_twice_anchor j⟩⟩
  obtain ⟨out, hrun, hgate, hraw⟩ := collectionRun_recording_identification
    x payload started weights hchoice hnotLive hboundary hchoiceArm
    states memories hordinary hunoccupied
  have hselected : (Bandits.Support.ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
      (.continuing core snapshot boundary scores)).selection ≠ none := by
    simp [Bandits.Support.ReferenceActivePhysicalStep.DispatchCut.selection]
  have hpost : prepared.observeCoordinator =
      Bandits.Support.ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights := by
    have heq := Bandits.Support.ReferenceActivePhysicalStep.observeCoordinator_collection_equation prepared payload ledger
      clock cutoff (.continuing core snapshot boundary scores) hcut
    simpa [Bandits.Support.ReferenceActivePhysicalStep.DispatchCut.selection,
      Bandits.Support.ReferenceActivePhysicalStep.selectionAt, hselected, started, weights,
      source, Bandits.Support.ReferenceActivePhysicalStep.collectionInput,
      CoordinatorCollectionInteractive.PreObservationInputs.weights,
      CoordinatorCollectionUpRoundStep.Inputs.weights] using heq
  have hstep : (Bandits.Support.ReferenceActivePhysicalStep.step x).coordinator.recording = some out := by
    change prepared.observeCoordinator.recording = some out
    rw [hpost]
    exact (@collectionPostChoice_recording_eq_run p rate x prepared payload ledger started weights).trans hrun
  have hledgerCutoff : ledger.cutoff = CoordinatorCollectionUpRoundStep.sourceCutoff cutoff := by
    simpa [Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using core.ledger_cutoff_eq
  have hcutoffLe : ledger.cutoff ≤ x.time.val + 1 := by
    rw [hledgerCutoff]
    simp [CoordinatorCollectionUpRoundStep.sourceCutoff]
    omega
  have hledgerSigma : ledger.sigma =
      Bandits.Support.CoordinatorRecorderComplementBridge.sourceStart payload := by
    simpa [Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using core.ledger_sigma_eq
  have hsigma : 0 < ledger.sigma := by
    rw [hledgerSigma]
    simp [Bandits.Support.CoordinatorRecorderComplementBridge.sourceStart]
  have hfreeze : ledger.freezeAt = started.clock.g := by
    calc
      ledger.freezeAt = clock.g := core.ledger_freeze_eq
      _ = started.clock.g := by
        have hclockFrame : started.clock = clock := by
          simpa [started, source, Bandits.Support.ReferenceActivePhysicalStep.collectionInput] using
            snapshot.clockStarted_frame.1
        rw [hclockFrame]
  have hleftEnabled : decide (¬ Bandits.Support.CoordinatorRecordingOperation.isFrozen
      (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput input)) =
      decide (x.time.val + 1 < ledger.freezeAt) := by
    simp [Bandits.Support.CoordinatorRecordingOperation.isFrozen,
      Bandits.Support.CoordinatorRecordingOperation.sourceCalendarRound,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      Bandits.Support.CoordinatorRecorderComplementBridge.sourceStart,
      Bandits.Support.ReferenceActivePhysicalStep.collectionRecordingInput, input,
      hfreeze]
  have hrightEnabled : Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled ledger x.time =
      decide (x.time.val + 1 < ledger.freezeAt) := by
    simp [Bandits.Support.ReferenceActivePhysicalStep.collectionEnabled,
      hsigma, hcutoffLe]
  have henabled := hleftEnabled.trans hrightEnabled.symm
  exact ⟨⟨out, hrun, hstep, hgate, hraw⟩, henabled⟩

end Bandits.Support.ReferenceCoordinatorCollectionRecording

end
