/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffNumericalSource
public import Bandits.Support.ReferenceLaterCollectionArrivalReadout
public import Bandits.Support.ReferenceGeneratedFirstCollectionFollowerPrefix

import Lean.Elab.Tactic.Omega

/-!
# Canonical numerical arrivals on the actual first collection window

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,391-402`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.

This module joins the original physical records of the actual first collection
window to the numerical cell made by their actual recorder. Missing choices
remain missing. The result is conditional on the visible first-cutoff scenario
selectors and proves no total calendar coverage, queue truth, score splice,
recording law, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceGeneratedFirstCutoffSurvival
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RecordedQueueRun

namespace Bandits.Support.ReferenceFirstCollectionCanonicalArrivalSource

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : RateInput p}

private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
        start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hspan' : start + (count + 1) ≤ p.T := by omega
      have hprefixSpan : start + count ≤ p.T := by omega
      have hprefixLength :
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
            hprefixSpan active).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start count
          hprefixSpan active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows selected rewards start count hspan' active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = count := by omega
        subst index
        simp [hprefixLength]

private theorem getElem_takeWhile_eq {α : Type}
    (predicate : α → Bool) (xs : List α) (index : ℕ)
    (hindex : index < (xs.takeWhile predicate).length) :
    (xs.takeWhile predicate)[index]'hindex =
      xs[index]'(by
        exact Nat.lt_of_lt_of_le hindex (List.takeWhile_prefix predicate).length_le) :=
  (List.takeWhile_prefix predicate).getElem hindex

private theorem collection_choice_continuing
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hstate : record.input.state.coordinator = .collection payload ledger proposal)
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some call) :
    ∃ clock cutoff core snapshot boundary scores,
      record.output.preparation.coordinator =
        .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) ∧
      call = ⟨payload, ledger, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩ := by
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hchoiceCut :
      ReferenceCollectionSegmentExtraction.choiceOfCut
        (ReferenceActivePhysicalStep.dispatch record.input) = some call := by
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    have hselection :
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
      intro hnone
      simp [hnone] at hchoice
    have hselectionD : (ReferenceActivePhysicalStep.dispatch record.input).selection ≠ none := by
      simpa only [ReferenceActivePhysicalStep.PreparedRound.coordinator_eq] using hselection
    change (if (ReferenceActivePhysicalStep.dispatch record.input).selection = none then none
      else ReferenceCollectionSegmentExtraction.choiceOfCut
        (ReferenceActivePhysicalStep.dispatch record.input)) = some call at hchoice
    rw [ite_eq_right hselectionD] at hchoice
    exact hchoice
  have hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.dispatch, hstate, hbad]
    rw [hdispatch] at hchoiceCut
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoiceCut
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
  have hdispatch :
      ReferenceActivePhysicalStep.dispatch record.input =
        .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection
            (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) := by
    unfold ReferenceActivePhysicalStep.dispatch
    rw [hstate]
    simp only [dite_eq_left hcutoff]
    rfl
  rw [hdispatch] at hchoiceCut
  cases hresult : CoordinatorRoundDispatch.dispatchCollection
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) with
  | continuing core snapshot boundary scores =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
      have hcall := (Option.some.inj hchoiceCut).symm
      refine ⟨clock, cutoff, core, snapshot, boundary, scores, ?_, hcall⟩
      rw [hprepared]
      simp [ReferenceActivePhysicalStep.prepare, hdispatch, hresult]
  | clockFailure failure hstart =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | localFailure started hstart hcore reason =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | coreFailure core started hstart reason =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | laterChoiceFailure core consistent started hstart instruction hinstruction output localEq
      clockData installation reason =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut
  | laterChosen core consistent started hstart instruction hinstruction output localEq
      clockData installation selection =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hresult] at hchoiceCut

/-- Conditional continuing-record calculation. The source-root theorem below
supplies the actual continuing constructor, whole reward identity and ordinary
unoccupied PREPARE configurations; none is a new root premise. -/
private theorem continuing_canonical_arrivals
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (s : ℕ) (rewards : RewardTable p)
    (hrewards : record.input.rewards = rewards)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (movingLedger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload movingLedger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload movingLedger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload movingLedger clock cutoff) = true)
    (hbranch : record.output.preparation.coordinator =
      .collection payload movingLedger clock cutoff (.continuing core snapshot boundary scores))
    (hunoccupied : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record) :
    let actualWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
      (ReferenceActivePhysicalStep.collectionInput record.input payload movingLedger clock cutoff)
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
    let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
      record.output.preparation payload snapshot.clockStarted actualWeights
    ∃ localValid : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput,
      let a := CoordinatorRecorderComplementBridge.recorderInput recordingInput
      let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
        recordingInput localValid
      let enabled := ReferenceActivePhysicalStep.collectionEnabled
        movingLedger record.input.time
      ∃ c : RecordedQueueRun.RoundInput p.K,
        c.enabled = enabled ∧
        c.enabled = decide (record.input.time.val + 1 < snapshot.clockStarted.clock.g) ∧
        c.recordedArm = SnapshotRecordingKernel.recordingMap p .collection enabled
          a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
          hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
          (record.input.row.2 record.input.time).1 ∧
        c.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) ∧
        c.rate = payload.rate ∧
        (∃ out : CoordinatorRecordingOperation.Output p,
          CoordinatorRecorderComplementBridge.run recordingInput = some out ∧
          record.coordinatorDiagnostics.recording = some out ∧
          out.gateArm = c.recordedArm ∧
          ReferenceCollectionRawBufferHistory.rawDiagnostic record =
            out.gateArm.map (fun arm => (arm, out.rawArrival)) ∧
          (∀ arm, CoordinatorCollectionLedger.localArrival
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm) ∧
          (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord
            movingLedger arm record =
              (c.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm)) ∧
          (∀ arm, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm =
            if c.recordedArm = some arm then
              Nat.floor ((D p : ℝ) * rate.eta.val *
                (((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
                  payload.rate arm)
            else 0) ∧
          (c.recordedArm = none → out.rawArrival = 0) ∧
          (∀ arm, c.recordedArm = some arm → c.reward arm = 0 →
            ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0))) ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some c := by
  classical
  dsimp only
  let actualWeights :=
    CoordinatorCollectionInteractive.PreObservationInputs.weights
      (ReferenceActivePhysicalStep.collectionInput record.input payload
        movingLedger clock cutoff)
      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
  let cell := ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
    record payload movingLedger clock cutoff snapshot
  have hreadout :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        record = some cell := by
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
      cell, hunoccupied, hbranch]
  have hcallExpected :
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall s record =
        some ⟨payload, movingLedger, snapshot.clockStarted, actualWeights⟩ := by
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
      actualWeights, hunoccupied, hbranch]
  rcases ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
      s record cell hreadout with
    ⟨payload', ledger', started', weights', out, hcallReadout, hpostChoice,
      hrun, hEnabled, hclock, hRate, hReward, hdiag, hgate, harrivals⟩
  have htuple :
      (⟨payload', ledger', started', weights'⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate ×
            CoordinatorPhaseClock.StartRoundResult p ×
              (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
        ⟨payload, movingLedger, snapshot.clockStarted, actualWeights⟩ :=
    (Option.some.inj (hcallExpected.symm.trans hcallReadout)).symm
  cases htuple
  let localValid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        payload snapshot.clockStarted actualWeights) :=
    ⟨boundary, fun i =>
      ⟨snapshot.inputsValid.choice_valid.anchor_le_current i,
        snapshot.inputsValid.choice_valid.current_le_twice_anchor i⟩⟩
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    record.output.preparation payload snapshot.clockStarted actualWeights
  let a := CoordinatorRecorderComplementBridge.recorderInput recordingInput
  let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    recordingInput localValid
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hidentified :=
    ReferenceLaterCollectionArrivalReadout.continuingCollectionRecorderOutput
      record s payload movingLedger clock cutoff core snapshot boundary
      scores hbranch hunoccupied
  dsimp only at hidentified
  rcases hidentified with
    ⟨⟨rawOut, hrunRaw, hdiagRaw, hgateRaw, hrawRaw⟩, henabledRaw⟩
  have hrunRaw' : CoordinatorRecorderComplementBridge.run recordingInput =
      some rawOut := by
    simpa [recordingInput, hprepared] using hrunRaw
  have hrunReadout : CoordinatorRecorderComplementBridge.run recordingInput =
      some out := by
    simpa [recordingInput] using hrun
  have hout : out = rawOut :=
    Option.some.inj (hrunReadout.symm.trans hrunRaw')
  have hmapPart :=
    ReferenceLaterCollectionArrivalReadout.continuingCollectionInput_map_eq_projection
      record payload movingLedger clock cutoff snapshot boundary
  dsimp only at hmapPart
  have hcellEnabled : cell.enabled =
      !decide (CoordinatorRecordingOperation.isFrozen a) := by
    change decide (¬ CoordinatorRecordingOperation.isFrozen a) =
      !decide (CoordinatorRecordingOperation.isFrozen a)
    simp
  have hcellMapPart : cell.recordedArm =
      CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv cell.enabled := by
    rw [hcellEnabled]
    exact hmapPart
  have hmapRecording :=
    ReferenceLaterCollectionArrivalReadout.collectionRecordingMap_eq_projection
      payload recordingInput hv cell.enabled
  have hcellMapRecorder : cell.recordedArm =
      SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
        hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (ContinuousLearningRows.sliceAt a.time a.row.2) :=
    hcellMapPart.trans hmapRecording.symm
  have hcellMap : cell.recordedArm =
      SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
        hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (record.input.row.2 record.input.time).1 := by
    change cell.recordedArm = SnapshotRecordingKernel.recordingMap p .collection cell.enabled
      a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
      hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
      (record.input.row.2 record.input.time).1 at hcellMapRecorder
    exact hcellMapRecorder
  have hcellMapEnabled : cell.recordedArm =
      SnapshotRecordingKernel.recordingMap p .collection
        (ReferenceActivePhysicalStep.collectionEnabled movingLedger record.input.time)
        a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
        hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
        (record.input.row.2 record.input.time).1 := by
    rw [← hEnabled]
    exact hcellMap
  have hdiagOutput : record.output.coordinator.recording = some rawOut := by
    simpa only [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics] using hdiagRaw
  have hrawDiagnostic : ReferenceCollectionRawBufferHistory.rawDiagnostic record =
      rawOut.gateArm.map (fun arm => (arm, rawOut.rawArrival)) := by
    change (record.output.coordinator.recording.bind fun output =>
      output.gateArm.map fun arm => (arm, output.rawArrival)) = _
    rw [hdiagOutput]
    rfl
  have hrawRaw' : rawOut.rawArrival =
      SnapshotRecordingKernel.recordedIncrement p rate.eta.val payload.anchor
        (fun arm => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (record.input.rewards record.input.time arm))
        (CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv cell.enabled) := by
    rw [← hgateRaw] at hrawRaw
    have hgateCell : rawOut.gateArm = cell.recordedArm :=
      hgateRaw.trans hcellMapPart.symm
    rw [← hcellMapPart, ← hgateCell]
    exact hrawRaw
  have harrivalsRaw : ∀ arm,
      CoordinatorCollectionLedger.localArrival
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder rawOut) arm =
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm := by
    intro arm
    simpa [hout] using harrivals arm
  have hqueueArrival : ∀ arm,
      CoordinatorCollectionLedger.localArrival
          (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm =
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm := by
    intro arm
    rw [hrawDiagnostic]
    simpa [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder] using
      harrivalsRaw arm
  have hrawNone : cell.recordedArm = none → rawOut.rawArrival = 0 := by
    intro hnone
    have hmapNone :
        CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv cell.enabled = none :=
      hcellMapPart.symm.trans hnone
    simpa [SnapshotRecordingKernel.recordedIncrement, hmapNone] using hrawRaw'
  have hzeroDiagnostic : ∀ arm, cell.recordedArm = some arm → cell.reward arm = 0 →
      ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0) := by
    intro arm hrecorded hzero
    have hgridZero : RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time arm) = 0 := by
      rw [hReward] at hzero
      simpa [RealRewardGridCount.realRewardGridValue] using hzero
    have hmapSome :
        CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart a hv cell.enabled =
          some arm := hcellMapPart.symm.trans hrecorded
    have hrawZero : rawOut.rawArrival = 0 := by
      simpa [SnapshotRecordingKernel.recordedIncrement, hmapSome, hgridZero] using hrawRaw'
    rw [hrawDiagnostic, hgateRaw.trans hcellMapPart.symm, hrecorded, hrawZero]
    rfl
  have hphysical : ∀ arm,
      ReferenceCollectionRawBufferHistory.physicalQueueRecord movingLedger arm record =
        (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) := by
    intro arm
    by_cases hbefore : record.input.time.val + 1 < movingLedger.freezeAt
    · simp [ReferenceCollectionRawBufferHistory.physicalQueueRecord, hbefore,
        hEnabled, hqueueArrival arm]
    · have hdisabled :
          ReferenceActivePhysicalStep.collectionEnabled movingLedger record.input.time = false := by
        simp [ReferenceActivePhysicalStep.collectionEnabled, hbefore]
      have hrecordedNone : cell.recordedArm = none := by
        rw [hcellMapEnabled, hdisabled]
        simp [SnapshotRecordingKernel.recordingMap]
      have hquantizedZero :
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm = 0 :=
        RecordedQueueRun.quantizedArrival_eq_zero
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm (by
            intro hsome
            rw [hrecordedNone] at hsome
            cases hsome)
      simp [ReferenceCollectionRawBufferHistory.physicalQueueRecord, hbefore,
        hdisabled, hEnabled, hquantizedZero]
  have hRewardTarget : cell.reward =
      (fun arm => ((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) := by
    simpa only [hrewards] using hReward
  refine ⟨localValid, cell, hEnabled, hclock, ?_, hRewardTarget, hRate,
    ?_, hreadout⟩
  · simpa only [actualWeights] using hcellMapEnabled
  · refine ⟨rawOut, hrunRaw', hdiagRaw, hgateRaw.trans hcellMapPart.symm,
      hrawDiagnostic, harrivalsRaw, hphysical, ?_, hrawNone, hzeroDiagnostic⟩
    · intro arm
      by_cases hrecorded : cell.recordedArm = some arm
      · have hfloorArgument :
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).n * cell.reward arm /
                cell.rate arm =
              (D p : ℝ) * rate.eta.val *
                (((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
                  payload.rate arm := by
          rw [hRewardTarget, hRate]
          rw [(ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D]
          simp [ReferenceFirstLaunchNumericalCell.queueParameters]
          ring
        rw [RecordedQueueRun.quantizedArrival_eq_floor
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm hrecorded,
          hrecorded, hfloorArgument]
        simp only [ite_true]
      · rw [RecordedQueueRun.quantizedArrival_eq_zero
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm hrecorded]
        simp [hrecorded]

/-- Every actual selected record in the computed first collection window is
joined to the same canonical numerical cell that its collection recorder
produced. The cutoff cell comes from the original first-cutoff source theorem;
continuing cells use the literal prepared collection snapshot. Missing choices
remain absent. -/
theorem actual_first_collection_canonical_arrival_source
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T)
    (hshort : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length < count)
    (j : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length).length)) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let w := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length
    let b := w + 1
    let W := (E.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    let C := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (headCell : RecordedQueueRun.RoundInput p.K),
      cut = E.records[w]'(by
        have hw : w < count := by simpa [w] using hshort
        have hlen : E.records.length = count := by
          simpa [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
            ReferenceActivePhysicalHorizon.run_record_count
              (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
              source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards s count hspan
              (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                rate source rewards C_star C_h hc).activeAtStart
        exact hw.trans_eq hlen.symm) ∧
      E.records = ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan ++ cut :: suffix ∧
      cut.input.rows = source.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      cut.input.rewards = rewards ∧
      cut.input.time.val = s + w ∧
      (∃ r q base,
        cut.input.state.coordinator = .live r q base ∧ P = r.payload) ∧
      C = [cut] ++ W ∧
      (∀ q : Fin (W.length + 1),
        let boundary := ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (b + q.val) (by
            have hlen : E.records.length = count := by
              simpa [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
                ReferenceActivePhysicalHorizon.run_record_count
                  (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
                  source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards s count hspan
                  (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                    rate source rewards C_star C_h hc).activeAtStart
            have hdrop : (E.records.drop b).length = count - b := by
              simp [List.length_drop, hlen]
            have hprefix : W <+: E.records.drop b := List.takeWhile_prefix _
            have htail : W.length ≤ count - b := by
              simpa [hdrop] using hprefix.length_le
            omega)
          (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
            rate source rewards C_star C_h hc s rfl)
        (boundary.finalState.coordinator = .dagger ∨
          ∃ ledger saved, boundary.finalState.coordinator = .collection P ledger saved) ∧
        ∀ i : Fin (p.m - 1),
          ∃ state memory,
            boundary.finalState.followers i = .ordinary state memory ∧
            state.status = .unoccupied) ∧
      let record := C.get j
      record.input.rows = source.1.2 ∧
      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      record.input.rewards = rewards ∧
      record.input.time.val = s + w + j.val ∧
      (ReferenceCollectionSegmentExtraction.choice record.input = none → 0 < j.val) ∧
      ∀ call : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice record.input = some call →
          call.payload = P ∧
          (j.val = 0 → call.initializer.isSome = true) ∧
          (0 < j.val → call.initializer = none) ∧
          let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
            record.output.preparation call.payload call.started call.weights
          ∃ localValid : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput,
            let a := CoordinatorRecorderComplementBridge.recorderInput recordingInput
            let hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
              recordingInput localValid
            let enabled := ReferenceActivePhysicalStep.collectionEnabled
              call.preLedger record.input.time
            ∃ c : RecordedQueueRun.RoundInput p.K,
              c.enabled = enabled ∧
              c.enabled = decide (record.input.time.val + 1 < call.started.clock.g) ∧
              c.recordedArm = SnapshotRecordingKernel.recordingMap p .collection enabled
                a.eta hv.eta_pos hv.eta_source_cap a.anchor a.currentWeights
                hv.anchor_pos hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor
                (record.input.row.2 record.input.time).1 ∧
              c.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) ∧
              c.rate = call.payload.rate ∧ call.payload.rate = P.rate ∧
              (∃ out : CoordinatorRecordingOperation.Output p,
                CoordinatorRecorderComplementBridge.run recordingInput = some out ∧
                record.coordinatorDiagnostics.recording = some out ∧
                out.gateArm = c.recordedArm ∧
                ReferenceCollectionRawBufferHistory.rawDiagnostic record =
                  out.gateArm.map (fun arm => (arm, out.rawArrival)) ∧
                (∀ arm, CoordinatorCollectionLedger.localArrival
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) arm =
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm) ∧
                (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  call.preLedger arm record =
                    (c.enabled, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm)) ∧
                (∀ arm, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm =
                  if c.recordedArm = some arm then
                    Nat.floor ((D p : ℝ) * rate.eta.val *
                      (((rewards record.input.time arm).val : ℝ) / (D p : ℝ)) /
                        call.payload.rate arm)
                  else 0) ∧
                (c.recordedArm = none → out.rawArrival = 0) ∧
                (∀ arm, c.recordedArm = some arm → c.reward arm = 0 →
                  ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, 0))) ∧
              ((j.val = 0 ∧ c = headCell) ∨
                (0 < j.val ∧
                  ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some c)) := by
  classical
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let execution := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let w := window.length
  let b := w + 1
  let tail := (execution.records.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let active := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let commonElapsed := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  have hrunCount : execution.records.length = count := by
    simpa [execution, ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
        count hspan active.activeAtStart
  have htailBound : b + tail.length ≤ count := by
    have hprefix : tail <+: execution.records.drop b := List.takeWhile_prefix _
    have hlength := hprefix.length_le
    have htail : tail.length ≤ execution.records.length - b := by
      simpa [List.length_drop] using hlength
    have hb : b ≤ execution.records.length := by
      have hw : w < count := by simpa [window, w] using hshort
      rw [hrunCount]
      dsimp [b, w]
      exact Nat.succ_le_of_lt hw
    calc
      b + tail.length ≤ b + (execution.records.length - b) :=
        Nat.add_le_add_left htail b
      _ = execution.records.length := Nat.add_sub_cancel' hb
      _ = count := hrunCount
  have hN := ReferenceFirstCutoffNumericalSource.actual_first_cutoff_numerical_source
    rate source rewards C_star C_h hc count hspan hshort
  dsimp only at hN
  rcases hN with ⟨cut, suffix, r, q, base, hcut, hNrest⟩
  rcases hNrest with
    ⟨hrecords, htime, hrows, hselected, hrewards, hstate, hsigma, hqzero, hdispatch⟩
  rcases hdispatch with
    ⟨dispatched, hstart, ledger, hinit, hcand, hdomain, hclock, hpending,
      hnoAssignment, selected, hcutBranch, hNtail⟩
  rcases hNtail with
    ⟨hu, huBound, huGrid, hledgerSigma, hledgerCut, hfollowers, hkpos,
      hstartRound, holdReplay, hpayloads, hNnumeric⟩
  rcases hNnumeric with
    ⟨hNenabled, hNrecorded, hNmapArm, hNreward, hNrate, hNweights, hNthreshold,
      hNout, hNclock, hNboundary, hNstrict, hNfailed, hNzero, hNactions,
      hNfeedback, hNphysical, hNdisabled, hNlength⟩
  rcases hNout with
    ⟨headOut, hNrun, hNdiag, hNgate, hNraw, hNnone, hNrawDiagnostic, hNarrivals⟩
  have hcutIndex : cut = execution.records[w]'(by omega) := by
    simpa [execution, window, w] using hcut
  have htimeCut : cut.input.time.val = commonElapsed + w := by
    simpa [window, w, commonElapsed] using htime
  have hwindow : window.length = w := rfl
  have hdropHead : execution.records.drop w = cut :: suffix := by
    rw [hrecords, ← hwindow, List.drop_append_length]
  have hdropTail : execution.records.drop (w + 1) = suffix := by
    rw [hrecords, ← hwindow, List.drop_append]
    simp [window]
  have hcollection :
      ReferenceCollectionPhaseHistory.collectionWindow execution.records w =
        [cut] ++ tail := by
    simp [ReferenceCollectionPhaseHistory.collectionWindow, tail, b,
      hdropHead, hdropTail]
  have headLocalValid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
        r.payload dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights) :=
    ⟨selected.recorderBoundaryValid, fun i =>
      ⟨selected.choiceInputsValid.anchor_le_current i,
        selected.choiceInputsValid.current_le_twice_anchor i⟩⟩
  let headRecordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    cut.output.preparation r.payload dispatched.startResult
    (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights
  let headA := CoordinatorRecorderComplementBridge.recorderInput headRecordingInput
  let headHv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    headRecordingInput headLocalValid
  let headEnabled := ReferenceActivePhysicalStep.collectionEnabled
    (ReferenceActivePhysicalStep.sharedLedger ledger) cut.input.time
  let headCell : RecordedQueueRun.RoundInput p.K := {
    enabled := headEnabled
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection headEnabled
      headA.eta headHv.eta_pos headHv.eta_source_cap headA.anchor headA.currentWeights
      headHv.anchor_pos headHv.current_pos headHv.anchor_le_current
      headHv.current_le_twice_anchor (cut.input.row.2 cut.input.time).1
    reward := fun arm => ((rewards cut.input.time arm).val : ℝ) / D p
    rate := r.payload.rate
    reward_nonneg := by intro arm; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro arm
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast (Nat.le_of_lt_succ (rewards cut.input.time arm).isLt)
    rate_pos := by
      intro arm
      exact (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
        (r.payload.beta_le_rate arm) }
  let headCall : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time)⟩
  have hheadChoice : ReferenceCollectionSegmentExtraction.choice cut.input = some headCall := by
    have hprepared : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input := by
      rw [cut.output_eq]
      rfl
    unfold ReferenceCollectionSegmentExtraction.choice
    have hselection :
        (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection ≠ none := by
      rw [← hprepared, hcutBranch]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt]
    rw [ite_eq_right hselection]
    rw [← hprepared, hcutBranch]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut]
    rfl
  have hFs := ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
    rate source rewards C_star C_h hc commonElapsed rfl count
    (by simpa [commonElapsed] using hspan)
    (by simpa [execution, window, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      commonElapsed] using hshort)
  have hgeneratedRun :
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc commonElapsed rfl count
        (by simpa [commonElapsed] using hspan) = execution := by
    rfl
  dsimp only at hFs
  rcases hFs with
    ⟨rF, qF, baseF, hFlive, hFsigma, hFqzero,
      dispatchedF, hFstart, ledgerF, hFinit, hFledger, hFdomain,
      hFclock, hFpending, hFnoAssignment, selectedF, hFcutBranch, hFtail⟩
  rcases hFtail with
    ⟨_, _, _, _, _, _, _, _, hFboundaries, hFsteps⟩
  have hcutF :
      cut = execution.records[w]'(by omega) := hcutIndex
  have hFwindowBound :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hc commonElapsed rfl count
          (by simpa [commonElapsed] using hspan)).records).length <
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hc commonElapsed rfl count
          (by simpa [commonElapsed] using hspan)).records.length := by
    rw [hgeneratedRun, hrunCount]
    simpa [window, execution,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hshort
  have hFrecord :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc commonElapsed rfl count
        (by simpa [commonElapsed] using hspan)).records[
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hc commonElapsed rfl count
              (by simpa [commonElapsed] using hspan)).records).length]'hFwindowBound = cut := by
    simpa [hgeneratedRun, window, w, execution,
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hcutIndex.symm
  have hFstate :
      ((ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hc commonElapsed rfl count
        (by simpa [commonElapsed] using hspan)).records[
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hc commonElapsed rfl count
              (by simpa [commonElapsed] using hspan)).records).length]'hFwindowBound).input.state.coordinator =
        cut.input.state.coordinator :=
    congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      record.input.state.coordinator) hFrecord
  have hrootEq :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.live rF qF baseF :=
    hstate.symm.trans (hFstate.symm.trans hFlive)
  cases hrootEq
  have hboundary :
      ∀ q : Fin (tail.length + 1),
        let boundary := ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
          (b + q.val) (by omega) active.activeAtStart
        (boundary.finalState.coordinator = .dagger ∨
          ∃ ledger saved, boundary.finalState.coordinator = .collection r.payload ledger saved) ∧
        ∀ i : Fin (p.m - 1),
          ∃ state memory,
            boundary.finalState.followers i = .ordinary state memory ∧
            state.status = .unoccupied := by
    intro q
    have hq : q.val ≤ tail.length := Nat.le_of_lt_succ q.isLt
    let generatedExecution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hc commonElapsed rfl count
      (by simpa [commonElapsed] using hspan)
    let generatedWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      generatedExecution.records
    let generatedTail := (generatedExecution.records.drop (generatedWindow.length + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hqF : q.val ≤ generatedTail.length := by
      simpa [generatedTail, generatedWindow, generatedExecution, hgeneratedRun,
        tail, execution, window, w, b,
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
        ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hq
    have hf := hFboundaries q.val hqF
    rcases hf with ⟨hcoord, hfollowers⟩
    constructor
    · simpa [generatedTail, generatedWindow, generatedExecution, hgeneratedRun,
        tail, execution, window, w, b, active,
        ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
        ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
        ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive] using hcoord
    · intro i
      obtain ⟨state, memory, hord, hstatus, _⟩ := hfollowers i
      exact ⟨state, memory, by
        simpa [generatedTail, generatedWindow, generatedExecution, hgeneratedRun,
          tail, execution, window, w, b, active,
          ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
          ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
          ReferenceFirstWindowNumericalStream.actualFirstLiveSeed,
          ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive] using hord,
        hstatus⟩
  refine ⟨cut, suffix, r.payload, headCell, hcutIndex, ?_, hrows, hselected,
    hrewards, ?_, ⟨r, q, base, hstate, rfl⟩, ?_, hboundary, ?_⟩
  · simpa [execution, window] using hrecords
  · simpa [commonElapsed, w, window] using htimeCut
  · simpa [tail, execution, window, w, b] using hcollection
  · have hj : j.val <
        (ReferenceCollectionPhaseHistory.collectionWindow execution.records w).length := by
      simp [execution, window, w]
    have hjR : j.val < ([cut] ++ tail).length := by
      rw [← hcollection]
      exact hj
    have hgetOpt :
        (ReferenceCollectionPhaseHistory.collectionWindow execution.records w)[j.val]? =
          ([cut] ++ tail)[j.val]? := congrArg
            (fun xs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
              xs[j.val]?) hcollection
    have hleft := List.getElem?_eq_getElem hj
    have hright := List.getElem?_eq_getElem hjR
    have hget :
        (ReferenceCollectionPhaseHistory.collectionWindow execution.records w).get j =
          ([cut] ++ tail)[j.val]'hjR := by
      rw [hleft, hright] at hgetOpt
      exact Option.some.inj hgetOpt
    by_cases hzero : j.val = 0
    · have hheadGet : ([cut] ++ tail)[j.val]'hjR = cut := by
        simp [hzero]
      rw [hget, hheadGet]
      refine ⟨hrows, hselected, hrewards, ?_, ?_, ?_⟩
      · simpa [commonElapsed, w, window, hzero] using htimeCut
      · intro hnone
        rw [hheadChoice] at hnone
        cases hnone
      · intro call hchoice
        have hcallEq : call = headCall :=
          (Option.some.inj (hheadChoice.symm.trans hchoice)).symm
        subst call
        refine ⟨rfl, ?_, ?_, ?_⟩
        · intro _
          simp [headCall]
        · intro hj
          omega
        · refine ⟨headLocalValid, headCell, rfl, ?_, rfl, rfl, rfl, rfl, ?_,
            Or.inl ⟨hzero, rfl⟩⟩
          · exact ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionEnabled_eq_started_clock
              r q base cut.input.time dispatched ledger hcand hdomain hclock
          · have hsourceMap :=
              ReferenceLaterCollectionArrivalReadout.collectionRecordingMap_eq_projection
                r.payload headRecordingInput headHv headEnabled
            refine ⟨headOut, hNrun, ?_, hNgate.trans hsourceMap.symm,
              hNrawDiagnostic, hNarrivals, ?_, ?_, hNnone, ?_⟩
            · exact hNdiag
            · intro arm
              have h := (hNphysical arm).2
              simpa [headCall, headCell, headEnabled] using h
            · intro arm
              by_cases hrecorded : headCell.recordedArm = some arm
              · rw [RecordedQueueRun.quantizedArrival_eq_floor
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) headCell arm hrecorded,
                  hrecorded]
                rw [(ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D]
                simp [headCell, headCall,
                  ReferenceFirstLaunchNumericalCell.queueParameters]
                ring_nf
              · rw [RecordedQueueRun.quantizedArrival_eq_zero
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) headCell arm hrecorded]
                simp [hrecorded]
            · simpa [headCell] using hNzero
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hzero
      let k : ℕ := j.val - 1
      have hk : k < tail.length := by
        dsimp [k]
        have hlen : ([cut] ++ tail).length = tail.length + 1 := by simp
        omega
      let tailPredicate :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) → Bool :=
        fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input
      have hdropIndex : k < (execution.records.drop b).length :=
        Nat.lt_of_lt_of_le hk (List.takeWhile_prefix tailPredicate).length_le
      have htailAt : tail[k] = execution.records[b + k] := by
        calc
          tail[k] = (execution.records.drop b)[k]'hdropIndex := by
            exact (List.takeWhile_prefix tailPredicate).getElem hk
          _ = execution.records[b + k] := by
            simp only [List.getElem_drop]
      have hindex : b + k < count := by
        have h := htailBound
        omega
      have hrecordBound : b + k < execution.records.length := by
        rw [hrunCount]
        exact hindex
      have hactual : execution.records[b + k]'hrecordBound =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
            (b + k) (by omega) active.activeAtStart := by
        have hgetActual := run_records_getElem?_actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
          count hspan active.activeAtStart (b + k) hindex
        change execution.records[b + k]? =
          some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
            (b + k) (by omega) active.activeAtStart) at hgetActual
        have hthis : execution.records[b + k]? = some (execution.records[b + k]'hrecordBound) :=
          List.getElem?_eq_getElem hrecordBound
        rw [hthis] at hgetActual
        exact Option.some.inj hgetActual
      have htailRows : (tail[k]).input.rows = source.1.2 := by
        rw [htailAt, hactual]
        rfl
      have htailSelected :
          (tail[k]).input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source := by
        rw [htailAt, hactual]
        rfl
      have htailRewards : (tail[k]).input.rewards = rewards := by
        rw [htailAt, hactual]
        rfl
      have htailTime : (tail[k]).input.time.val = commonElapsed + w + j.val := by
        rw [htailAt, hactual]
        simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt, b, k]
        omega
      have hrecordState : (tail[k]).input.state.coordinator =
          (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
            (b + k) (by omega) active.activeAtStart).finalState.coordinator := by
        rw [htailAt, hactual]
        rfl
      have htailGet : ([cut] ++ tail)[j.val]'hjR = tail[k]'hk := by
        rw [List.getElem_append_right (by
          simp only [List.length_singleton]
          omega)]
        simp [k]
      rw [hget, htailGet]
      refine ⟨htailRows, htailSelected, htailRewards, ?_, ?_, ?_⟩
      · simpa [commonElapsed, w, window] using htailTime
      · intro _
        exact hjpos
      · intro call hchoice
        have hstepAt := hFsteps k hk
        have hunoccupied :
            ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied (tail[k]) := by
          unfold ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
          intro i
          rcases hstepAt i with
            ⟨incoming, memory, _, hstatus, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
              hlast, hstartRound, hprep, _⟩
          have hprepTail :
              ((tail[k]).output.preparation.followers.followers i).configuration =
                .ordinary incoming memory := by
            rw [htailAt]
            exact hprep
          rw [hprepTail]
          exact hstatus
        let qindex : Fin (tail.length + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
        have hboundaryK := hboundary qindex
        have hcoordRun :
            (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
              (b + k) (by omega) active.activeAtStart).finalState.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              (ReferenceActivePhysicalHorizon.run initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards commonElapsed
                (b + k) (by omega) active.activeAtStart).finalState.coordinator =
                  .collection r.payload movingLedger movingSaved := by
          simpa [qindex] using hboundaryK.1
        have hcoordRecord : (tail[k]).input.state.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              (tail[k]).input.state.coordinator =
                .collection r.payload movingLedger movingSaved := by
          rcases hcoordRun with hdagger | ⟨movingLedger, movingSaved, hmoving⟩
          · exact Or.inl (hrecordState.trans hdagger)
          · exact Or.inr ⟨movingLedger, movingSaved, hrecordState.trans hmoving⟩
        rcases hcoordRecord with hdagger | ⟨movingLedger, movingSaved, hcollectionState⟩
        · unfold ReferenceCollectionSegmentExtraction.choice at hchoice
          have hpreparedDagger :
              (ReferenceActivePhysicalStep.prepare (tail[k]).input).coordinator = .dagger := by
            simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
              hdagger]
          have hselection :
              (ReferenceActivePhysicalStep.prepare (tail[k]).input).coordinator.selection = none := by
            simp [hpreparedDagger, ReferenceActivePhysicalStep.DispatchCut.selection]
          rw [ite_eq_left hselection] at hchoice
          cases hchoice
        · have hcontinuing := collection_choice_continuing (tail[k]) r.payload movingLedger
            movingSaved call hcollectionState hchoice
          rcases hcontinuing with
            ⟨clock, cutoff, core, snapshot, boundary, scores, hbranch, hcall⟩
          subst call
          refine ⟨rfl, ?_, ?_, ?_⟩
          · intro hzero
            omega
          · intro _
            rfl
          · have hcanonical := continuing_canonical_arrivals (tail[k]) commonElapsed
              rewards htailRewards r.payload movingLedger clock cutoff core snapshot boundary
              scores hbranch hunoccupied
            dsimp only at hcanonical
            rcases hcanonical with
              ⟨localValid, cell, hEnabled, hclock, hmap, hReward, hRate, hout, hreadout⟩
            exact ⟨localValid, cell, hEnabled, hclock, hmap, hReward, hRate, rfl,
              hout, Or.inr ⟨hjpos, hreadout⟩⟩

end Bandits.Support.ReferenceFirstCollectionCanonicalArrivalSource

end
