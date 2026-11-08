/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAcceptedReception
public import Bandits.Support.ReferenceContinuingCollectionAcceptedFinishDomains

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection accepted admission and physical FINISH

This module composes the first locally admitted UP reception on the original
generated run with the continuing-collection checked FINISH. The exhaustion
case retains its original prefix endpoint and terminal boundary. The accepted
case retains the actual source record, original sender and receiver evidence,
the full FINISH producer result, and the exact adjacent `H.run` boundaries.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
164-177,246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceGeneratedFirstCollectionAdmission

abbrev Parameters := ReferenceGeneratedFirstCollectionAcceptedReception.Parameters
abbrev RateInput := ReferenceGeneratedFirstCollectionAcceptedReception.RateInput
abbrev SourceInput := ReferenceGeneratedFirstCollectionAcceptedReception.SourceInput
abbrev RewardTable := ReferenceGeneratedFirstCollectionAcceptedReception.RewardTable

variable {p : Parameters} {rate : RateInput p}

abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev State (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.State p rate
abbrev Ledger (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate
abbrev Payload (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev UpRecord (p : Parameters) (rate : RateInput p) :=
  OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val)

/-- The FINISH producer's own witnesses, retained so the receiving admission
can identify them with the same R witnesses. -/
structure AcceptedFinishEvidence
    (record : Record p rate) (payload : Payload p rate) (ledger : Ledger p rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      record.input payload ledger saved)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (recording : CoordinatorRecordingOperation.Output p)
    (started : Ledger p rate) (message : UpRecord p rate)
    (rootCutoff : Fin p.T)
    (rootCutoffEq : rootCutoff.val + 1 = ledger.cutoff)
    (rootCore : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff))
    (rootSnapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff))
    (rootClockBound : rootSnapshot.clockStarted.clock.g ≤ p.T + 1)
    (rootScoreCheck : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff) = true)
    (rootDispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing rootCore rootSnapshot rootClockBound rootScoreCheck)) : Type where
  /-- The complete public F result is retained, including its accepted replay,
  checked FINISH, clock FINISH, step fields, follower outputs, and either the
  next ready input or the terminal ready boundary (or its empty-pending
  alternative). -/
  finish_domain_output : _ :=
    ReferenceContinuingCollectionAcceptedFinishDomains.continuing_collection_accepted_finish_domains
      record.input payload ledger saved hReady
  cutoff : Fin p.T
  cutoff_eq : cutoff.val + 1 = ledger.cutoff
  core : CoordinatorRoundDispatch.CollectionCoreValid
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)
  snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)
  clock_bound : snapshot.clockStarted.clock.g ≤ p.T + 1
  score_check : CoordinatorRoundDispatch.collectionCurrentScoresCheck
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff) = true
  dispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
    ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
      cutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing core snapshot clock_bound score_check)
  dispatch_eq_root :
    ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing rootCore rootSnapshot rootClockBound rootScoreCheck) =
      ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
        cutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing core snapshot clock_bound score_check)
  snapshot_start_matches : choice.started = snapshot.clockStarted
  recorder : CoordinatorRecordingOperation.Output p
  recorder_eq : recorder = recording
  recorder_run : CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare record.input) payload snapshot.clockStarted
      (CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)) = some recorder
  startedAfter : Ledger p rate
  started_eq : startedAfter = started
  start_success : CoordinatorCollectionLedger.startRound ledger
    (record.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recorder) =
      .success startedAfter
  past : List (Bool × ℕ)
  currentRecord : Bool × ℕ
  decodedLedger : Ledger p rate
  advancedBank : CoordinatorUpReception.UpDecoderBank p
  acceptedCandidate : decodedLedger = CoordinatorCollectionLedger.acceptUpCandidate
    startedAfter (ReferenceActivePhysicalStep.upSenderIndex record.input) message past currentRecord
  decoderValid : CoordinatorCollectionLedger.validLedgerCheck decodedLedger = true
  decodeSuccess : CoordinatorCollectionLedger.decodeUp startedAfter
    (ReferenceActivePhysicalStep.upSenderIndex record.input) (some message) =
      .success decodedLedger
  receiveSuccess : (ReferenceActivePhysicalStep.receiveUp
    (ReferenceActivePhysicalStep.prepare record.input) startedAfter).result =
      .success (decodedLedger, advancedBank)

/-- Produced evidence for the accepted alternative. The record keeps R's actual
sender and receiver, and `finish` joins F's checked decode and receive result
to that same receiver. -/
structure AcceptedAdmissionOutput
    (sourceInput : SourceInput p) (wholeRewards : RewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).crossing.isSome = true)
    (start : ℕ)
    (hsElapsed : start = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : start + count ≤ p.T)
    (execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState
        rate sourceInput wholeRewards C_star C_h hcross))
    (window : List (Record p rate)) (payload : Payload p rate) (ledger : Ledger p rate)
    (saved : Option (Fin p.T × Bool)) (w qLength k : ℕ) : Type where
  execution_eq : execution = ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate sourceInput wholeRewards C_star C_h hcross start hsElapsed count hspan
  hspanActual : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).completed +
      count ≤ p.T := by simpa only [hsElapsed] using hspan
  actualRun : ReferenceActivePhysicalHorizon.Run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
  actualRun_eq_execution : actualRun = execution
  actualRun_is_original : actualRun = ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate sourceInput wholeRewards C_star C_h hcross count hspanActual
  actualMode : ReferenceActivePhysicalHorizon.allActiveAtStart
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).completed) :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate sourceInput wholeRewards C_star C_h hcross).1
  k_before_end : k < count
  record : Record p rate
  record_index_lt : k < execution.records.length
  record_index : record = execution.records[k]'record_index_lt
  record_output_eq_step : record.output = ReferenceActivePhysicalStep.step record.input
  hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
    record.input payload ledger saved
  windowIndex : Fin window.length
  window_index_value : windowIndex.val = qLength + 1
  window_index_offset : windowIndex.val = k - w
  window_record : window[windowIndex.val] = record
  choice : ReferenceCollectionSegmentExtraction.Choice rate
  choice_eq : ReferenceCollectionSegmentExtraction.choice record.input = some choice
  recording : CoordinatorRecordingOperation.Output p
  recording_eq : CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare record.input) choice.payload choice.started
      choice.weights) = some recording
  started : Ledger p rate
  start_eq : CoordinatorCollectionLedger.startRound choice.preLedger
    (record.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled choice.preLedger record.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
      .success started
  started_valid : CoordinatorCollectionLedger.validLedgerCheck started = true
  raw_diagnostic :
    CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording =
      ReferenceCollectionRawBufferHistory.rawDiagnostic record
  choice_payload : choice.payload = payload
  choice_ledger : choice.preLedger = ledger
  choice_initializer : choice.initializer = none
  rootCutoff : Fin p.T
  root_cutoff_eq : rootCutoff.val + 1 = ledger.cutoff
  rootCore : CoordinatorRoundDispatch.CollectionCoreValid
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff) rootCutoff)
  rootSnapshot : CoordinatorCollectionInteractive.PreparedSnapshot
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff) rootCutoff)
  root_clock_bound : rootSnapshot.clockStarted.clock.g ≤ p.T + 1
  root_score_check : CoordinatorRoundDispatch.collectionCurrentScoresCheck
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff) rootCutoff) = true
  root_dispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
    .collection payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
      rootCutoff (.continuing rootCore rootSnapshot root_clock_bound root_score_check)
  choice_started : choice.started = rootSnapshot.clockStarted
  message : UpRecord p rate
  message_parse : ReferenceCollectionSegmentExtraction.effectiveParse record.input started =
    some message
  message_accepted : CoordinatorCollectionLedger.acceptUpCheck started
    (ReferenceActivePhysicalStep.upSenderIndex record.input) message = true
  source : ReferenceGeneratedFirstCollectionAcceptedReception.ParsedUpSourceEvidence
    execution.records window record choice message ledger started start w windowIndex.val
  receiver : ReferenceGeneratedFirstCollectionAcceptedReception.AcceptedReceiverOutput
    record payload ledger saved hReady started message
  finish : Nonempty (Σ' evidence : AcceptedFinishEvidence record payload ledger saved hReady
      choice recording started message rootCutoff root_cutoff_eq rootCore rootSnapshot root_clock_bound
      root_score_check root_dispatch,
    evidence.decodedLedger = receiver.l2 ∧ evidence.advancedBank = receiver.bank)
  round_time : record.input.time.val = start + k
  actualPrefix : ReferenceActivePhysicalHorizon.Run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
  actualPrefix_eq : actualPrefix = ReferenceActivePhysicalHorizon.run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
    sourceInput.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceInput)
    wholeRewards (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).completed)
    k (by omega) actualMode
  actualPrefixNext : ReferenceActivePhysicalHorizon.Run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
  actualPrefixNext_eq : actualPrefixNext = ReferenceActivePhysicalHorizon.run
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate sourceInput wholeRewards C_star C_h hcross)
    sourceInput.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p sourceInput)
    wholeRewards (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput sourceInput wholeRewards C_star C_h rate)).completed)
    (k + 1) (by omega) actualMode
  record_step_next_eq_actual_boundary :
    (ReferenceActivePhysicalStep.step record.input).next = actualPrefixNext.finalState
  record_input_state_eq_prefix : record.input.state = actualPrefix.finalState
  record_output_next_eq_prefix_next : record.output.next = actualPrefixNext.finalState
  prefix_next_eq_execution_of_last : k + 1 = count →
    actualPrefixNext.finalState = execution.finalState

private theorem run_record_endpoints
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[j]'(by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).input.state =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
          (by omega) active).finalState ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records[j]'(by
          rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).output.next := by
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
    rewards start j (by omega) active
  have hsuccessorRecords := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  have hsuccessorFinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    initial rows selected rewards start j (by omega) active
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (j + 1) (count - (j + 1)) (by omega) active
  have hprefixCount :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
          (by omega) active).records ++ suffix := by
    simpa [Nat.add_sub_of_le (by omega : j + 1 ≤ count)] using hprefix
  have hjFull : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjSuccessor : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (j + 1) (by omega) active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hprefixAt := List.getElem_of_eq hprefixCount hjFull
  have hsuccessorAt := List.getElem_of_eq hsuccessorRecords hjSuccessor
  have hprefixAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩ =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ := by
    simpa [List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using hprefixAt
  have hsuccessorAt' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).records.get ⟨j, hjSuccessor⟩ = actual := by
    simpa [actual, List.getElem_append, ReferenceActivePhysicalHorizon.run_record_count] using
      hsuccessorAt
  have hactual :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩ = actual :=
    hprefixAt'.trans hsuccessorAt'
  constructor
  · change ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩).input.state = _
    rw [hactual]
    rfl
  · change (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (j + 1)
        (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.get ⟨j, hjFull⟩).output.next
    rw [hactual]
    exact hsuccessorFinal

private theorem run_record_time
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[j]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).input.time.val =
      start + j := by
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan active
  have hjtimes : j <
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan active).records.map (fun record => record.input.time.val)).length := by
    rw [List.length_map, ReferenceActivePhysicalHorizon.run_record_count]
    exact hj
  have hjcalendar : j < (ReferenceActivePhysicalHorizon.calendar start count).length := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hj
  have hmap := List.getElem_of_eq htimes hjtimes
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem_map,
    List.getElem_range'_1] using hmap

private theorem run_finalState_eq_of_index
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index + 1 = count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (index + 1) (by omega) active).finalState =
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      count hspan active).finalState := by
  subst count
  rfl

private theorem accepted_finish_of_actual_reception
    (record : Record p rate) (payload : Payload p rate) (ledger : Ledger p rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      record.input payload ledger saved)
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (recording : CoordinatorRecordingOperation.Output p) (started : Ledger p rate)
    (message : UpRecord p rate)
    (rootCutoff : Fin p.T)
    (rootCore : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff))
    (rootSnapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff))
    (rootClockBound : rootSnapshot.clockStarted.clock.g ≤ p.T + 1)
    (rootScoreCheck : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff) = true)
    (rootDispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .collection payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
        rootCutoff (.continuing rootCore rootSnapshot rootClockBound rootScoreCheck))
    (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some choice)
    (hrecorded : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) choice.payload choice.started
        choice.weights) = some recording)
    (hstarted : CoordinatorCollectionLedger.startRound choice.preLedger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled choice.preLedger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started)
    (hrootStarted : choice.started = rootSnapshot.clockStarted)
    (hrootCutoff : rootCutoff.val + 1 = ledger.cutoff)
    (hparse : ReferenceCollectionSegmentExtraction.effectiveParse record.input started =
      some message)
    (haccepted : CoordinatorCollectionLedger.acceptUpCheck started
      (ReferenceActivePhysicalStep.upSenderIndex record.input) message = true)
    (hjoint : message.val.S + message.val.q ≤
      (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p)
    (hscore : message.val.S ≤ (4 * rate.n) * (ledger.cutoff - ledger.sigma))
    (receiver : ReferenceGeneratedFirstCollectionAcceptedReception.AcceptedReceiverOutput
      record payload ledger saved hReady started message) :
    Nonempty (Σ' evidence : AcceptedFinishEvidence record payload ledger saved hReady
      choice recording started message rootCutoff hrootCutoff rootCore rootSnapshot rootClockBound
      rootScoreCheck rootDispatch,
      evidence.decodedLedger = receiver.l2 ∧ evidence.advancedBank = receiver.bank) := by
  classical
  let rootClock := ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff
  let rootInput := ReferenceActivePhysicalStep.collectionInput record.input payload ledger
    rootClock rootCutoff
  let rootWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights rootInput
    rootSnapshot.inputsValid.ledger_valid rootSnapshot.inputsValid.assignment_eq
  let expectedChoice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, ledger, rootSnapshot.clockStarted, rootWeights, none⟩
  have hchoiceExpected : ReferenceCollectionSegmentExtraction.choice record.input =
      some expectedChoice := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [rootDispatch]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection, expectedChoice,
      rootWeights, rootInput, rootClock]
  have hchoiceEq : choice = expectedChoice :=
    Option.some.inj (hchoice.symm.trans hchoiceExpected)
  have hfinish :=
    ReferenceContinuingCollectionAcceptedFinishDomains.continuing_collection_accepted_finish_domains
      record.input payload ledger saved hReady
  have hfinishCopy := hfinish
  rcases hfinishCopy with
    ⟨cutoff, hcutoff, core, snapshot, clockBound, scoreCheck, dispatch,
      hafterDispatch⟩
  rcases hafterDispatch with
    ⟨_, _, _, recorder, startedAfter, hrecordFinish, hafterRecord⟩
  rcases hafterRecord with
    ⟨hstartFinish, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hmessages⟩
  have hdispatchEq :
      ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved rootCutoff)
          rootCutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing rootCore rootSnapshot rootClockBound rootScoreCheck) =
        ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
          cutoff (CoordinatorRoundDispatch.CollectionOutcome.continuing core snapshot clockBound scoreCheck) :=
    rootDispatch.symm.trans dispatch
  have hcutoffEq : cutoff = rootCutoff := by
    cases hdispatchEq
    rfl
  have hclockStartedEq : rootSnapshot.clockStarted = snapshot.clockStarted := by
    have h := hdispatchEq
    cases h
    rfl
  have hchoiceStartedFinish : choice.started = snapshot.clockStarted := by
    calc
      choice.started = rootSnapshot.clockStarted := hrootStarted
      _ = snapshot.clockStarted := hclockStartedEq
  have hrecordedExpected : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) expectedChoice.payload
        expectedChoice.started expectedChoice.weights) = some recording := by
    rw [← hchoiceEq]
    exact hrecorded
  have hfinishWeights :
      CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput record.input payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq = rootWeights := by
    cases hcutoffEq
    have hsnapshotEq : snapshot = rootSnapshot := by
      cases hdispatchEq
      rfl
    cases hsnapshotEq
    rfl
  have hrecordFinishRoot : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare record.input) payload rootSnapshot.clockStarted rootWeights) =
        some recorder := by
    simpa [ReferenceActivePhysicalStep.collectionRecordingInput, hfinishWeights,
      hclockStartedEq] using hrecordFinish
  have hrecordFinishEq : recorder = recording :=
    Option.some.inj (hrecordFinishRoot.symm.trans hrecordedExpected)
  have hstartExpected : CoordinatorCollectionLedger.startRound ledger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started := by
    rw [hchoiceEq] at hstarted
    simpa [expectedChoice] using hstarted
  have hstartFinishRoot : CoordinatorCollectionLedger.startRound ledger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success startedAfter := by
    simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
      hrecordFinishEq] using hstartFinish
  have hstartedEq : startedAfter = started :=
    CoordinatorCollectionLedger.Checked.success.inj
      (hstartFinishRoot.symm.trans hstartExpected)
  have hparseFinish : ReferenceCollectionSegmentExtraction.effectiveParse
      record.input startedAfter = some message := by
    rw [hstartedEq]
    exact hparse
  have hacceptedFinish : CoordinatorCollectionLedger.acceptUpCheck startedAfter
      (ReferenceActivePhysicalStep.upSenderIndex record.input) message = true := by
    rw [hstartedEq]
    exact haccepted
  have hquery := hmessages.2 message hparseFinish hacceptedFinish hjoint hscore
  rcases hquery with
    ⟨past, currentRecord, _, _, _, _, _, _, _, _, _, _, _, _, _,
      decodedLedger, advancedBank, acceptedCandidate, decoderValid, decodeSuccess,
      receiveSuccess, _⟩
  have hstartFinishFinal : CoordinatorCollectionLedger.startRound ledger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success startedAfter := hstartFinishRoot
  have hstartFinishRecorder : CoordinatorCollectionLedger.startRound ledger
      (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recorder) =
        .success startedAfter := by
    rw [hrecordFinishEq]
    exact hstartFinishFinal
  have hreceiveSuccess : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) startedAfter).result =
        .success (decodedLedger, advancedBank) := by
    simpa only [hstartedEq] using receiveSuccess
  let evidence : AcceptedFinishEvidence record payload ledger saved hReady choice
      recording started message rootCutoff hrootCutoff rootCore rootSnapshot rootClockBound rootScoreCheck
      rootDispatch := {
    finish_domain_output := hfinish
    cutoff := cutoff
    cutoff_eq := hcutoff
    core := core
    snapshot := snapshot
    clock_bound := clockBound
    score_check := scoreCheck
    dispatch := dispatch
    dispatch_eq_root := hdispatchEq
    snapshot_start_matches := hchoiceStartedFinish
    recorder := recorder
    recorder_eq := hrecordFinishEq
    recorder_run := by
      simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
        hrecordFinishEq] using hrecordFinish
    startedAfter := startedAfter
    started_eq := hstartedEq
    start_success := hstartFinishRecorder
    past := past
    currentRecord := currentRecord
    decodedLedger := decodedLedger
    advancedBank := advancedBank
    acceptedCandidate := acceptedCandidate
    decoderValid := decoderValid
    decodeSuccess := by simpa only [hstartedEq] using decodeSuccess
    receiveSuccess := hreceiveSuccess }
  have hreceiveR := receiver.received
  have hreceiveBoth : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) startedAfter).result =
        .success (receiver.l2, receiver.bank) := by
    rw [hstartedEq]
    exact hreceiveR
  have hsuccessEq := hreceiveSuccess.symm.trans hreceiveBoth
  have hpairEq : decodedLedger = receiver.l2 ∧ advancedBank = receiver.bank := by
    have hpair := CoordinatorCollectionLedger.Checked.success.inj hsuccessEq
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  exact ⟨⟨evidence, hpairEq⟩⟩

/-- The first locally admissible admission is either exhausted at the actual
original prefix endpoint or is an actual accepted record whose same UP message
also produces the continuing checked FINISH. The theorem keeps the original
source telescope and has no readiness, acceptance, queue, budget, or FINISH
premise beyond the initialization crossing, elapsed equality, horizon span,
and first-window shortness used by R.

The FINISH result is still conditional on the two explicit sender budget
fields carried by its produced `source`; they are applied in the proof below,
never supplied at this root.
-/
theorem actual_generated_first_collection_accepted_admission
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s hsElapsed count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let b := w + 1
    let Q := (execution.records.drop b).takeWhile
      (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
    let hcount : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
            rate source rewards C_star C_h hcross s hsElapsed)
    let htail : b + Q.length ≤ count := by
      have hw : w < count := by simpa [execution, firstWindow, w] using hshort
      have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
      have hlen := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      omega
    let k := b + Q.length
    let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
      ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
        (by omega)
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∃ cut payload saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, firstWindow, w] using hshort
        simpa [execution, firstWindow, w] using Nat.lt_of_lt_of_eq hw hcount.symm) ∧
      (∃ ledger,
        (prefixAt Q.length (by omega)).finalState.coordinator =
          .collection payload ledger saved ∧
        ledger.pending = Finset.univ ∧ ledger.sigma = s + 1 ∧ ledger.cutoff = s + b ∧
        ((k = count ∧
          (prefixAt Q.length (by omega)).finalState = execution.finalState ∧
          (∀ htime : s + k < p.T,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
                  rate source rewards C_star C_h hcross s hsElapsed)
                (prefixAt Q.length (by omega)) ⟨s + k, by omega, htime⟩)
              payload ledger saved) ∧
          (s + k = p.T →
            ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
              (prefixAt Q.length (by omega)).finalState payload ledger saved)) ∨
         (∃ hendpoint : k < count,
          ∃ output : AcceptedAdmissionOutput source rewards C_star C_h hcross s hsElapsed
            count hspan execution B payload ledger saved w Q.length k,
            output.k_before_end = hendpoint))) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hcross
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross s hsElapsed count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let b := w + 1
  let Q := (execution.records.drop b).takeWhile
    (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
  have hcount : execution.records.length = count := by
    simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
  have htail : b + Q.length ≤ count := by
    have hw : w < count := by simpa [execution, firstWindow, w] using hshort
    have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
    have hlen := hprefix.length_le
    have hdrop : (execution.records.drop b).length = count - b := by
      simp [List.length_drop, hcount]
    omega
  let k := b + Q.length
  let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
    ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
      (by omega)
      (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
        rate source rewards C_star C_h hcross s hsElapsed)
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  have hR :=
    ReferenceGeneratedFirstCollectionAcceptedReception.actual_generated_first_collection_accepted_reception
      rate source rewards C_star C_h hcross s hsElapsed count hspan hshort
  dsimp only at hR
  rcases hR with ⟨cut, payload, saved, hcut, hrest⟩
  rcases hrest with ⟨ledger, hcoordinator, hpending, hsigma, hcutoff, hbranch⟩
  refine ⟨cut, payload, saved, hcut, ledger, hcoordinator, hpending, hsigma, hcutoff, ?_⟩
  rcases hbranch with hExhausted | haccepted
  · exact Or.inl hExhausted
  · rcases haccepted with
      ⟨hendpoint, record, hrecord, hReady, windowIndex, hwindowValue, hwindowOffset,
        hwindowRecord, choice, recording, started, hchoice, hrecorded, hstarted,
        message, hparse, haccepted, hstartedValid, hrawDiagnostic, hchoicePayload,
        hchoiceLedger, hchoiceInitializer, hrootPackage, hreceiverPackage⟩
    rcases hrootPackage with
      ⟨rootCutoff, rootCutoffEq, rootCore, rootSnapshot, rootClockBound,
        rootScoreCheck, rootDispatch, hrootStarted⟩
    obtain ⟨sender, receiver⟩ := hreceiverPackage
    let hspanActual : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T := by simpa only [hsElapsed] using hspan
    have hactualRunEq :=
      ReferenceGeneratedFirstCollectionAcceptedReception.actual_first_collection_run_eq_generated
        rate source rewards C_star C_h hcross s hsElapsed count hspan hspanActual
    let actualRun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspanActual
    have hactualRecords : actualRun.records = execution.records :=
      congrArg (fun run => run.records) hactualRunEq
    have hrecordIndex : k < execution.records.length := by rw [hcount]; exact hendpoint
    have hactualIndex : k < actualRun.records.length := by rw [hactualRecords]; exact hrecordIndex
    have hgetActual : execution.records[k]'hrecordIndex = actualRun.records[k]'hactualIndex := by
      exact List.getElem_of_eq hactualRecords.symm hrecordIndex
    have hrecordActual : record = actualRun.records[k]'hactualIndex :=
      hrecord.trans hgetActual
    let actualInitial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    have hactualModeElapsed :=
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
    let originalPrefix := ReferenceActivePhysicalHorizon.run actualInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      k (by omega) hactualModeElapsed
    let originalPrefixNext := ReferenceActivePhysicalHorizon.run actualInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      (k + 1) (by omega) hactualModeElapsed
    have hboundaries := run_record_endpoints actualInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count hspanActual hactualModeElapsed k hendpoint
    have hstateBoundary : record.input.state = originalPrefix.finalState := by
      calc
        record.input.state = (actualRun.records[k]'hactualIndex).input.state := by
          rw [hrecordActual]
        _ = originalPrefix.finalState := by
          simpa [actualRun, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
            actualInitial, originalPrefix, hsElapsed] using hboundaries.1
    have hnextBoundary : record.output.next = originalPrefixNext.finalState := by
      calc
        record.output.next = (actualRun.records[k]'hactualIndex).output.next := by
          rw [hrecordActual]
        _ = originalPrefixNext.finalState := by
          change (ReferenceActivePhysicalHorizon.run actualInitial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
            count hspanActual hactualModeElapsed).records[k].output.next = originalPrefixNext.finalState
          exact hboundaries.2.symm
    have htimeActual := run_record_time actualInitial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count hspanActual hactualModeElapsed k hendpoint
    have htime : record.input.time.val = s + k := by
      rw [hrecordActual]
      change (ReferenceActivePhysicalHorizon.run actualInitial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        count hspanActual hactualModeElapsed).records[k].input.time.val = s + k
      omega
    have hlastPrefix : k + 1 = count →
        originalPrefixNext.finalState = execution.finalState := by
      intro hlast
      calc
        originalPrefixNext.finalState = actualRun.finalState := by
          exact run_finalState_eq_of_index actualInitial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
            count hspanActual hactualModeElapsed k hlast
        _ = execution.finalState := congrArg (fun run => run.finalState) hactualRunEq
    let finishedEvidence := accepted_finish_of_actual_reception record payload ledger saved
      hReady choice recording started message rootCutoff rootCore rootSnapshot rootClockBound
      rootScoreCheck rootDispatch hchoice hrecorded hstarted hrootStarted rootCutoffEq
      hparse haccepted sender.joint_budget sender.score_budget receiver
    let output : AcceptedAdmissionOutput source rewards C_star C_h hcross s hsElapsed
        count hspan execution B payload ledger saved w Q.length k := {
      execution_eq := by rfl
      hspanActual := hspanActual
      actualRun := actualRun
      actualRun_eq_execution := hactualRunEq
      actualRun_is_original := rfl
      actualMode := hactualModeElapsed
      k_before_end := hendpoint
      record := record
      record_index_lt := hrecordIndex
      record_index := hrecord
      record_output_eq_step := record.output_eq
      hReady := hReady
      windowIndex := windowIndex
      window_index_value := hwindowValue
      window_index_offset := hwindowOffset
      window_record := hwindowRecord
      choice := choice
      choice_eq := hchoice
      recording := recording
      recording_eq := hrecorded
      started := started
      start_eq := hstarted
      started_valid := hstartedValid
      raw_diagnostic := hrawDiagnostic
      choice_payload := hchoicePayload
      choice_ledger := hchoiceLedger
      choice_initializer := hchoiceInitializer
      rootCutoff := rootCutoff
      root_cutoff_eq := rootCutoffEq
      rootCore := rootCore
      rootSnapshot := rootSnapshot
      root_clock_bound := rootClockBound
      root_score_check := rootScoreCheck
      root_dispatch := rootDispatch
      choice_started := hrootStarted
      message := message
      message_parse := hparse
      message_accepted := haccepted
      source := sender
      receiver := receiver
      finish := finishedEvidence
      round_time := htime
      actualPrefix := originalPrefix
      actualPrefix_eq := rfl
      actualPrefixNext := originalPrefixNext
      actualPrefixNext_eq := rfl
      record_step_next_eq_actual_boundary := by
        rw [← record.output_eq]
        exact hnextBoundary
      record_input_state_eq_prefix := hstateBoundary
      record_output_next_eq_prefix_next := hnextBoundary
      prefix_next_eq_execution_of_last := hlastPrefix }
    exact Or.inr ⟨hendpoint, output, rfl⟩

end Bandits.Support.ReferenceGeneratedFirstCollectionAdmission

end
