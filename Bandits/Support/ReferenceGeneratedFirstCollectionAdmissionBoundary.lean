/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmission

import Lean.Elab.Tactic.Omega

/-!
# Finished first-collection admission at the original prefix boundary

This module opens the accepted-admission FINISH producer at the actual message,
matches its checked receive to the receiver already produced at that record,
and exports concrete ready-ledger and original-run boundary facts. The
exhausted rejected-prefix case is kept intact.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
164-177,246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

abbrev Parameters := ReferenceGeneratedFirstCollectionAdmission.Parameters
abbrev RateInput := ReferenceGeneratedFirstCollectionAdmission.RateInput
abbrev SourceInput := ReferenceGeneratedFirstCollectionAdmission.SourceInput
abbrev RewardTable := ReferenceGeneratedFirstCollectionAdmission.RewardTable
abbrev Record := ReferenceGeneratedFirstCollectionAdmission.Record
abbrev State := ReferenceGeneratedFirstCollectionAdmission.State
abbrev Ledger := ReferenceGeneratedFirstCollectionAdmission.Ledger
abbrev Payload := ReferenceGeneratedFirstCollectionAdmission.Payload

variable {p : Parameters} {rate : RateInput p}

/-- In a canonical run, the input state of record `j` is the length-`j`
prefix endpoint, and its output is the length-`j+1` prefix endpoint. -/
private theorem run_record_endpoints
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[j]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hj)).input.state =
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
  have hmap := List.getElem_of_eq htimes hjtimes
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem_map,
    List.getElem_range'_1] using hmap

private theorem round_input_ext {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  cases hstate
  cases hrows
  cases hselected
  cases htime
  cases hrewards
  rfl

/-- Concrete FINISH, clock, register, and original-run facts for the accepted
record supplied by the admitted first-reception producer. Every ledger in this
record refers to that receiver's decoded ledger. -/
structure AcceptedBoundaryOutput
    {source : SourceInput p} {wholeRewards : RewardTable p}
    {C_star C_h : ℝ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).crossing.isSome = true}
    {s : ℕ}
    {hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed}
    {count : ℕ} {hspan : s + count ≤ p.T}
    {execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate source wholeRewards C_star C_h hcross)}
    {window : List (Record p rate)} {payload : Payload p rate} {ledger : Ledger p rate}
    {saved : Option (Fin p.T × Bool)} {w qLength k : ℕ}
    (admission : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
      source wholeRewards C_star C_h hcross s hsElapsed count hspan execution window
      payload ledger saved w qLength k) : Type where
  finished : Ledger p rate
  clockFinished : CoordinatorPhaseClock.FinishRoundResult p
  finish_success : CoordinatorCollectionLedger.finishRound admission.receiver.l2 =
    .success finished
  finish_candidate : finished = CoordinatorCollectionLedger.finishRoundCandidate
    admission.receiver.l2
  finish_valid : CoordinatorCollectionLedger.validLedgerCheck finished = true
  phase_ready : finished.phase = CoordinatorCollectionLedger.Phase.ready
  cursor_finished : finished.cursor = s + k + 2
  pending_finished : finished.pending =
    ledger.pending.erase (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)
  sigma_finished : finished.sigma = ledger.sigma
  cutoff_finished : finished.cutoff = ledger.cutoff
  freeze_finished : finished.freezeAt = ledger.freezeAt
  assignment_finished : finished.assignment = ledger.assignment
  base_score_finished : finished.baseScore = ledger.baseScore
  current_registers_finished : finished.currentRegisters = admission.receiver.l2.currentRegisters
  cutoff_registers_finished : finished.cutoffRegisters = admission.receiver.l2.cutoffRegisters
  raw_buffer_finished : finished.rawBuffer = admission.receiver.l2.rawBuffer
  enabled_history_finished : finished.enabledHistory = admission.receiver.l2.enabledHistory
  recovered_local_service :
    let a := admission.started.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)
    finished.increment a =
      (QueueReplay.replay (4 * rate.n) (0, admission.message.val.q)
        (admission.receiver.past ++ [admission.receiver.currentRecord])).1
  recovered_local_gamma_zero :
    admission.receiver.l2.gammaLoc
      (admission.started.assignment.arm
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)) = 0
  other_known_local_service :
    ∀ b, b ≠ admission.started.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) →
      finished.increment b = admission.started.increment b + admission.started.gammaLoc b
  gamma_zero_after_finish : ∀ b, finished.gammaLoc b = 0
  register_pending_characterization :
    ∀ b,
      (finished.currentRegisters b = none ↔ CoordinatorCollectionLedger.armPending finished b) ∧
      (finished.cutoffRegisters b = none ↔ CoordinatorCollectionLedger.armPending finished b)
  cutoff_mass_bound :
    ∀ b c, finished.cutoffRegisters b = some c →
      c.score + c.queue ≤ (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p
  joint_mass_and_service_span :
    ∀ b c q, finished.cutoffRegisters b = some c →
      finished.currentRegisters b = some q →
      c.score + finished.increment b + q.queue ≤ (s + k + 2 - ledger.sigma) * ConstructorDimensions.D p ∧
      c.score + finished.increment b ≤
        (4 * rate.n) * (min (s + k + 2) ledger.freezeAt - ledger.sigma)
  raw_support_bound :
    ∀ b r amount, finished.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ ConstructorDimensions.D p ∧
      ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound r ∧
      CoordinatorCollectionLedger.sourceRound r < min finished.cursor finished.freezeAt ∧
      CoordinatorCollectionLedger.armPending finished b
  enabled_calendar_inclusive_current :
    ∀ r, finished.enabledHistory r =
      if ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound r ∧
        CoordinatorCollectionLedger.sourceRound r < finished.cursor then
        some (decide (CoordinatorCollectionLedger.sourceRound r < ledger.freezeAt)) else none
  clock_finish_success :
    CoordinatorPhaseClock.finishRound p rate.eta.val admission.record.input.time
      admission.rootSnapshot.clockStarted.clock finished.pending admission.record.input.row =
        .ok clockFinished
  clock_registers_preserved :
    clockFinished.clock = admission.rootSnapshot.clockStarted.clock
  clock_pending_matches : clockFinished.pending = finished.pending
  clock_command_at_record :
    clockFinished.ledgerCommand =
      some (.accumulateLocalServiceAt admission.record.input.time)
  saved_proposal_preserved : clockFinished.clock.lastProposal = saved
  coordinator_finish_has_no_failure : admission.record.output.coordinator.failure = none
  coordinator_next_is_finished_collection :
    admission.record.output.next.coordinator = .collection payload finished saved
  decoder_bank_next_is_receiver_bank :
    admission.record.output.next.upDecoderBank = admission.receiver.bank
  record_input_is_original_prefix_boundary :
    admission.record.input.state = admission.actualPrefix.finalState
  record_output_is_original_next_prefix_boundary :
    admission.record.output.next = admission.actualPrefixNext.finalState
  prefix_next_is_execution_final_when_last :
    k + 1 = count → admission.actualPrefixNext.finalState = execution.finalState
  actual_activations_preserved :
    admission.record.output.next.activations = admission.record.input.state.activations
  actual_follower_outputs :
    ∀ j, admission.record.output.followers j =
      (ReferenceActivePhysicalStep.prepare admission.record.input).observeFollower j
  next_ready_input :
    (ledger.pending.erase
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty →
    s + k + 1 < p.T →
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = admission.actualPrefixNext.finalState ∧
      next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = wholeRewards ∧
      next.time.val = s + k + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next payload finished saved ∧
      ∀ (hnext : k + 1 < count),
        next = (admission.actualRun.records[k + 1]'(by
          have hcount : admission.actualRun.records.length = count := by
            rw [admission.actualRun_is_original]
            simpa [ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
              ReferenceActivePhysicalHorizon.run_record_count
                (ReferenceFirstCollectionEpochAlignment.actualLaunchState
                  rate source wholeRewards C_star C_h hcross)
                source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                wholeRewards
                (ReferenceInitializationRun.elapsed p
                  (ReferenceInitializationRun.output
                    (ActualReferenceInitializationBlock.referenceInput
                      source wholeRewards C_star C_h rate)).completed)
                count admission.hspanActual admission.actualMode
          rw [hcount]
          exact hnext)).input
  terminal_ready_state_boundary :
    (ledger.pending.erase
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty →
    s + k + 1 = p.T →
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      admission.record.output.next payload finished saved
  all_known_registers_when_pending_empty :
    ledger.pending.erase (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) = ∅ →
    ∀ b, ∃ q, finished.currentRegisters b = some q ∧
      ∃ c, finished.cutoffRegisters b = some c


/-- The accepted output's retained run is the literal original finite
physical run, with one record for each calendar index in the requested span. -/
theorem admission_actual_run_record_count
    {source : SourceInput p} {wholeRewards : RewardTable p}
    {C_star C_h : ℝ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).crossing.isSome = true}
    {s : ℕ}
    {hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed}
    {count : ℕ} {hspan : s + count ≤ p.T}
    {execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate source wholeRewards C_star C_h hcross)}
    {window : List (Record p rate)} {payload : Payload p rate} {ledger : Ledger p rate}
    {saved : Option (Fin p.T × Bool)} {w qLength k : ℕ}
    (admission : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
      source wholeRewards C_star C_h hcross s hsElapsed count hspan execution window
      payload ledger saved w qLength k) :
    admission.actualRun.records.length = count := by
  rw [admission.actualRun_is_original]
  simpa [ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
    ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source wholeRewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode

private theorem accepted_boundary_of_output
    {source : SourceInput p} {wholeRewards : RewardTable p}
    {C_star C_h : ℝ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).crossing.isSome = true}
    {s : ℕ}
    {hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source wholeRewards C_star C_h rate)).completed}
    {count : ℕ} {hspan : s + count ≤ p.T}
    {execution : ReferenceActivePhysicalHorizon.Run
      (ReferenceFirstLaunchNumericalCell.launchState rate source wholeRewards C_star C_h hcross)}
    {window : List (Record p rate)} {payload : Payload p rate} {ledger : Ledger p rate}
    {saved : Option (Fin p.T × Bool)} {w qLength k : ℕ}
    (admission : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
      source wholeRewards C_star C_h hcross s hsElapsed count hspan execution window
      payload ledger saved w qLength k) : Nonempty (AcceptedBoundaryOutput admission) := by
  classical
  rcases admission.finish with ⟨⟨finishEvidence, hreceiverMatch⟩⟩
  rcases finishEvidence with ⟨finishDomainOutput, finishEvidenceCutoff,
    finishEvidenceCutoffEquation, finishEvidenceCore, finishEvidenceSnapshot,
    finishEvidenceClockBound, finishEvidenceScoreCheck, finishEvidenceDispatch,
    finishEvidenceDispatchEqRoot, finishEvidenceSnapshotStartMatches,
    finishEvidenceRecorder, finishEvidenceRecorderEq, finishEvidenceRecorderRun,
    finishEvidenceStartedAfter, finishEvidenceStartedEq, finishEvidenceStartSuccess,
    finishEvidencePast, finishEvidenceCurrentRecord, finishEvidenceDecodedLedger,
    finishEvidenceAdvancedBank, finishEvidenceAcceptedCandidate,
    finishEvidenceDecoderValid, finishEvidenceDecodeSuccess,
    finishEvidenceReceiveSuccess⟩
  have hfinish := finishDomainOutput
  rcases hfinish with
    ⟨finishCutoff, hfinishCutoff, finishCore, finishSnapshot, finishClockBound,
      finishScoreCheck, hafterDispatch⟩
  rcases hafterDispatch with
    ⟨hfinishDispatch, _, _, _, finishRecorder, finishStarted,
      hfinishRecorded, hafterRecorded⟩
  rcases hafterRecorded with
    ⟨hfinishStart, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hmessages⟩
  let rootClock := ReferenceActivePhysicalStep.collectionClock payload ledger saved
    admission.rootCutoff
  let rootInput := ReferenceActivePhysicalStep.collectionInput admission.record.input
    payload ledger rootClock admission.rootCutoff
  let rootWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights rootInput
    admission.rootSnapshot.inputsValid.ledger_valid
    admission.rootSnapshot.inputsValid.assignment_eq
  have hrootDispatchFinish :
      ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved admission.rootCutoff)
          admission.rootCutoff
          (CoordinatorRoundDispatch.CollectionOutcome.continuing admission.rootCore
            admission.rootSnapshot admission.root_clock_bound admission.root_score_check) =
        ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved finishCutoff)
          finishCutoff
          (CoordinatorRoundDispatch.CollectionOutcome.continuing finishCore finishSnapshot
            finishClockBound finishScoreCheck) :=
    admission.root_dispatch.symm.trans hfinishDispatch
  have hfinishCutoffEq : finishCutoff = admission.rootCutoff := by
    injection hrootDispatchFinish with hpayload hledger hclock hcutoff houtcome
    exact hcutoff.symm
  have hfinishSnapshotEq : HEq finishSnapshot admission.rootSnapshot := by
    injection hrootDispatchFinish with hpayload hledger hclock hcutoff houtcome
    cases hcutoff
    cases hclock
    have houtcomeEq := eq_of_heq houtcome
    injection houtcomeEq with hsnapshot
    exact heq_of_eq hsnapshot.symm
  have hfinishEvidenceCutoffEq : finishEvidenceCutoff = admission.rootCutoff := by
    injection finishEvidenceDispatchEqRoot with hpayload hledger hclock hcutoff houtcome
    exact hcutoff.symm
  have hfinishEvidenceSnapshotEq : HEq finishEvidenceSnapshot admission.rootSnapshot := by
    injection finishEvidenceDispatchEqRoot with hpayload hledger hclock hcutoff houtcome
    cases hcutoff
    cases hclock
    have houtcomeEq := eq_of_heq houtcome
    injection houtcomeEq with hsnapshot
    exact heq_of_eq hsnapshot.symm
  have hfinishClockStartedEq : finishSnapshot.clockStarted =
      admission.rootSnapshot.clockStarted := by
    cases hfinishCutoffEq
    have hsnapshotEq := eq_of_heq hfinishSnapshotEq
    exact congrArg CoordinatorCollectionInteractive.PreparedSnapshot.clockStarted hsnapshotEq
  have hfinishWeights :
      CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput admission.record.input payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved finishCutoff)
          finishCutoff)
        finishSnapshot.inputsValid.ledger_valid finishSnapshot.inputsValid.assignment_eq =
      rootWeights := by
    cases hfinishCutoffEq
    have hsnapshotEq := eq_of_heq hfinishSnapshotEq
    cases hsnapshotEq
    rfl
  have hfinishRecordedRoot : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare admission.record.input) payload
        admission.rootSnapshot.clockStarted rootWeights) = some finishRecorder := by
    simpa [ReferenceActivePhysicalStep.collectionRecordingInput,
      hfinishWeights, hfinishClockStartedEq] using hfinishRecorded
  have hfinishRecordedEvidence : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare admission.record.input) payload
        admission.rootSnapshot.clockStarted rootWeights) = some finishEvidenceRecorder := by
    cases hfinishEvidenceCutoffEq
    have hsnapshotEq := eq_of_heq hfinishEvidenceSnapshotEq
    simpa [ReferenceActivePhysicalStep.collectionRecordingInput, hsnapshotEq] using
      finishEvidenceRecorderRun
  have hfinishRecorderEq : finishRecorder = finishEvidenceRecorder :=
    Option.some.inj (hfinishRecordedRoot.symm.trans hfinishRecordedEvidence)
  have hfinishRecorderActual : finishRecorder = admission.recording :=
    hfinishRecorderEq.trans finishEvidenceRecorderEq
  have hfinishStartRoot : CoordinatorCollectionLedger.startRound ledger
      (admission.record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger admission.record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder admission.recording) =
        .success finishStarted := by
    simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
      hfinishRecorderActual] using hfinishStart
  have hfinishStartEvidence : CoordinatorCollectionLedger.startRound ledger
      (admission.record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger admission.record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder admission.recording) =
        .success finishEvidenceStartedAfter := by
    simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
      finishEvidenceRecorderEq] using
        finishEvidenceStartSuccess
  have hfinishStartedEq : finishStarted = finishEvidenceStartedAfter :=
    CoordinatorCollectionLedger.Checked.success.inj
      (hfinishStartRoot.symm.trans hfinishStartEvidence)
  have hfinishStartedActual : finishStarted = admission.started :=
    hfinishStartedEq.trans finishEvidenceStartedEq
  have hparseFinish : ReferenceCollectionSegmentExtraction.effectiveParse
      admission.record.input finishStarted = some admission.message := by
    rw [hfinishStartedActual]
    exact admission.message_parse
  have hacceptedFinish : CoordinatorCollectionLedger.acceptUpCheck finishStarted
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) admission.message = true := by
    rw [hfinishStartedActual]
    exact admission.message_accepted
  have hquery := hmessages.2 admission.message hparseFinish hacceptedFinish
    admission.source.joint_budget admission.source.score_budget
  rcases hquery with
    ⟨past, currentRecord,
      _hcurrentNone, _hcutoffNone, _hreplayPast, _hreplayCurrent, _hpastMap,
      _hcurrentRecord, _hrecordsLength, _hrecordBound, _hserviceBound,
      _hreplayPrefix, _hcalendar, _hreplayOutputDomains, _hreplayScoreBound,
      finishDecoded, finishBank, _hacceptedCandidate, _hdecodedValid,
      _hdecodeSuccess, hfinishReceive, _hbankEquation, _htransitionExpected,
      _hparsedMessage, _hdiagnostic, _hl2Phase, _hl2Pending, _hl2Sigma,
      _hl2Cutoff, _hl2Cursor, _hl2Freeze, _hl2Assignment, _hl2Base,
      _hl2CutoffRegister, _hl2CurrentRegister, _hl2Increment, _hl2Gamma,
      _hl2GammaAll, _hl2Raw, _hl2OtherArms, _hl2RegisterPending,
      _hl2PendingZero, _hl2CutoffMass, _hl2JointMass, _hl2RawSupport,
      _hl2History, _hbankWellFormed, _hquota, _hbankPending, _hcompletedBatch,
      _hdecoderTransition, _hotherBank, _hpendingBanks,
      finishLedger, hfinishSuccess, hfinishCandidate, hfinishValid,
      hfinishIncrement, _hfinishGammaFunction, hfinishCursor, hfinishPhase,
      hfinishPending, hfinishSigma, hfinishCutoff, hfinishFreeze,
      hfinishAssignment, hfinishBase, hfinishCutoffRegisters,
      hfinishCurrentRegisters, hfinishRaw, hfinishHistory,
      hfinishIncrementAtArm, hfinishOtherIncrement, hfinishGammaZero,
      hfinishRegisterPending, hfinishCutoffMass, hfinishJointMass,
      hfinishRawSupport, hfinishHistoryEq, hclockFinished, hclockFinish,
      hclockEq, hclockPending, hproposalSaved,
      _hfinishOutputEquation, hfinishObservation, hstepObserve,
      hstepCoordinator, hstepBank, hstepActivations, hstepFollowers,
      _hownEntries, hbranches, hknownRegisters⟩
  have hlastProposalEq : finishSnapshot.clockStarted.clock.lastProposal = saved := by
    simpa using hproposalSaved
  have hfinishReceiveAtEvidence :
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare admission.record.input)
        finishStarted).result = .success (finishEvidenceDecodedLedger,
          finishEvidenceAdvancedBank) := by
    rw [hfinishStartedEq]
    exact finishEvidenceReceiveSuccess
  have hpairsFinishEvidence := CoordinatorCollectionLedger.Checked.success.inj
    (hfinishReceive.symm.trans hfinishReceiveAtEvidence)
  have hdecodedPair : finishDecoded = admission.receiver.l2 ∧
      finishBank = admission.receiver.bank := by
    exact ⟨(congrArg Prod.fst hpairsFinishEvidence).trans hreceiverMatch.1,
      (congrArg Prod.snd hpairsFinishEvidence).trans hreceiverMatch.2⟩
  rcases hdecodedPair with ⟨hdecoded, hbank⟩
  have hfinishSuccessReceiver : CoordinatorCollectionLedger.finishRound
      admission.receiver.l2 = .success finishLedger := by
    rw [← hdecoded]
    exact hfinishSuccess
  have hfinishCandidateReceiver : finishLedger =
      CoordinatorCollectionLedger.finishRoundCandidate admission.receiver.l2 := by
    calc
      finishLedger = CoordinatorCollectionLedger.finishRoundCandidate finishDecoded :=
        hfinishCandidate
      _ = CoordinatorCollectionLedger.finishRoundCandidate admission.receiver.l2 := by
        rw [hdecoded]
  have hfinishRecoveredArm :
      finishLedger.increment (admission.started.assignment.arm
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)) =
      (QueueReplay.replay (4 * rate.n) (0, admission.message.val.q)
        (admission.receiver.past ++ [admission.receiver.currentRecord])).1 := by
    let a := admission.started.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)
    have hgamma := admission.receiver.selected_gamma_zero
    have hincrement := admission.receiver.selected_increment
    have hfinishInc : finishLedger.increment a = admission.receiver.l2.increment a := by
      have h := congrArg (fun f => f a) hfinishIncrement
      simpa [a, hdecoded, hgamma] using h
    exact hfinishInc.trans (by simpa [a] using hincrement)
  have hfinishOtherArms : ∀ b, b ≠ admission.started.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) →
      finishLedger.increment b = admission.started.increment b + admission.started.gammaLoc b := by
    intro b hba
    have h := hfinishOtherIncrement b (by simpa [hfinishStartedActual] using hba)
    simpa [hdecoded, hfinishStartedActual] using h
  have hstepFailure :
      (ReferenceActivePhysicalStep.step admission.record.input).coordinator.failure = none := by
    rw [hstepObserve, _hfinishOutputEquation]
  have hstepNextCoordinator :
      (ReferenceActivePhysicalStep.step admission.record.input).next.coordinator =
        .collection payload finishLedger saved := by
    simpa [hlastProposalEq] using hstepCoordinator
  have hnextReadyFields :
      (ledger.pending.erase
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty →
      s + k + 1 < p.T →
      ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
        next.state = admission.actualPrefixNext.finalState ∧
        next.rows = source.1.2 ∧
        next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        next.rewards = wholeRewards ∧
        next.time.val = s + k + 1 ∧
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          next payload finishLedger saved ∧
        (∀ (hnext : k + 1 < count),
          next = (admission.actualRun.records[k + 1]'(by
            rw [admission_actual_run_record_count admission]
            exact hnext)).input) := by
    intro hremaining hbeforeTerminal
    have hremainingF : (ledger.pending.erase
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty := hremaining
    have htimeF : admission.record.input.time.val + 1 < p.T := by
      rw [admission.round_time]
      omega
    rcases hbranches hremainingF with ⟨hnextAtTime, _⟩
    rcases hnextAtTime htimeF with
      ⟨next, hnextState, hnextRows, hnextSelected, hnextRewards, hnextTime, hready⟩
    have hreadySaved :
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          next payload finishLedger saved := by
      simpa [hlastProposalEq] using hready
    have hnextStatePrefix : next.state = admission.actualPrefixNext.finalState := by
      calc
        next.state = (ReferenceActivePhysicalStep.step admission.record.input).next := hnextState
        _ = admission.record.output.next := by rw [admission.record_output_eq_step]
        _ = admission.actualPrefixNext.finalState := admission.record_output_next_eq_prefix_next
    have hrecordMemExecution : admission.record ∈ execution.records := by
      rw [admission.record_index]
      exact List.getElem_mem admission.record_index_lt
    have hrecordMem : admission.record ∈ admission.actualRun.records := by
      rw [admission.actualRun_eq_execution]
      exact hrecordMemExecution
    have hrecordMemOriginal : admission.record ∈
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source wholeRewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          wholeRewards
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput
                source wholeRewards C_star C_h rate)).completed)
          count admission.hspanActual admission.actualMode).records := by
      rw [admission.actualRun_is_original] at hrecordMem
      simpa [ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hrecordMem
    have hrecordOriginalInputs := ReferenceActivePhysicalHorizon.run_record_inputs
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source wholeRewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode admission.record hrecordMemOriginal
    have hnextRows' : next.rows = source.1.2 := hnextRows.trans hrecordOriginalInputs.1
    have hnextSelected' : next.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p source :=
      hnextSelected.trans hrecordOriginalInputs.2.1
    have hnextRewards' : next.rewards = wholeRewards :=
      hnextRewards.trans hrecordOriginalInputs.2.2
    have hnextTime' : next.time.val = s + k + 1 := by
      simpa [admission.round_time, Nat.add_assoc] using hnextTime
    refine ⟨next, hnextStatePrefix, hnextRows', hnextSelected', hnextRewards',
      hnextTime', hreadySaved, ?_⟩
    intro hnextCount
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source wholeRewards C_star C_h hcross
    let originalRun := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode
    have hnextIndex : k + 1 < admission.actualRun.records.length := by
      rw [admission_actual_run_record_count admission]
      exact hnextCount
    have hrecordsEq : originalRun.records = admission.actualRun.records := by
      have hactualRecords := congrArg
        (fun run : ReferenceActivePhysicalHorizon.Run
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source wholeRewards C_star C_h hcross) => run.records)
        admission.actualRun_is_original
      have horiginalRecords : originalRun.records =
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source wholeRewards C_star C_h hcross count admission.hspanActual).records := by
        rfl
      exact horiginalRecords.trans hactualRecords.symm
    have hnextOriginalIndex : k + 1 < originalRun.records.length := by
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact hnextCount
    have hrecordAtEq :
        originalRun.records[k + 1]'hnextOriginalIndex =
          admission.actualRun.records[k + 1]'hnextIndex :=
      List.getElem_of_eq hrecordsEq hnextOriginalIndex
    have hnextMemOriginal : (admission.actualRun.records[k + 1]'hnextIndex) ∈
        originalRun.records := by
      rw [← hrecordAtEq]
      exact List.getElem_mem hnextOriginalIndex
    have hnextOriginalInputs := ReferenceActivePhysicalHorizon.run_record_inputs
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode
      (admission.actualRun.records[k + 1]'hnextIndex) hnextMemOriginal
    have hnextOriginalBoundary := run_record_endpoints initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode (k + 1) hnextCount
    have hnextOriginalTime := run_record_time initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) wholeRewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source wholeRewards C_star C_h rate)).completed)
      count admission.hspanActual admission.actualMode (k + 1) hnextCount
    have hnextStateEqual : next.state =
        (admission.actualRun.records[k + 1]'hnextIndex).input.state := by
      let nextRun := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) wholeRewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source wholeRewards C_star C_h rate)).completed)
        (k + 1) (by omega) admission.actualMode
      have hactualNextFinal : admission.actualPrefixNext.finalState = nextRun.finalState := by
        simpa [nextRun, initial] using
          congrArg (fun run : ReferenceActivePhysicalHorizon.Run initial => run.finalState)
            admission.actualPrefixNext_eq
      calc
        next.state = admission.actualPrefixNext.finalState := hnextStatePrefix
        _ = (originalRun.records[k + 1]'hnextOriginalIndex).input.state := by
          calc
            admission.actualPrefixNext.finalState = nextRun.finalState := hactualNextFinal
            _ = (originalRun.records[k + 1]'hnextOriginalIndex).input.state := by
              simpa [nextRun, originalRun] using hnextOriginalBoundary.1.symm
        _ = (admission.actualRun.records[k + 1]'hnextIndex).input.state := by
          rw [hrecordAtEq]
    have hnextActualRows : next.rows =
        (admission.actualRun.records[k + 1]'hnextIndex).input.rows :=
      hnextRows'.trans hnextOriginalInputs.1.symm
    have hnextActualSelected : next.selected =
        (admission.actualRun.records[k + 1]'hnextIndex).input.selected :=
      hnextSelected'.trans hnextOriginalInputs.2.1.symm
    have hnextActualRewards : next.rewards =
        (admission.actualRun.records[k + 1]'hnextIndex).input.rewards :=
      hnextRewards'.trans hnextOriginalInputs.2.2.symm
    have hnextActualTime : next.time =
        (admission.actualRun.records[k + 1]'hnextIndex).input.time := by
      apply Fin.ext
      have htimeActual :
          (admission.actualRun.records[k + 1]'hnextIndex).input.time.val =
            ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput
                  source wholeRewards C_star C_h rate)).completed + (k + 1) := by
        rw [← hrecordAtEq]
        exact hnextOriginalTime
      have htime' :
          (admission.actualRun.records[k + 1]'hnextIndex).input.time.val = s + k + 1 := by
        calc
          _ = ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput
                  source wholeRewards C_star C_h rate)).completed + (k + 1) := htimeActual
          _ = s + k + 1 := by omega
      exact hnextTime'.trans htime'.symm
    exact round_input_ext hnextStateEqual hnextActualRows hnextActualSelected
      hnextActualTime hnextActualRewards
  have hterminalBoundary :
      (ledger.pending.erase
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty →
      s + k + 1 = p.T →
      ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
        admission.record.output.next payload finishLedger saved := by
    intro hremaining hterminal
    have hterminalF : admission.record.input.time.val + 1 = p.T := by
      rw [admission.round_time]
      exact hterminal
    have hbranchesF : (ledger.pending.erase
        (ReferenceActivePhysicalStep.upSenderIndex admission.record.input)).Nonempty := hremaining
    have hterminalResult := (hbranches hbranchesF).2 hterminalF
    simpa [admission.record_output_eq_step, hlastProposalEq] using hterminalResult
  have hknownOutput :
      ledger.pending.erase (ReferenceActivePhysicalStep.upSenderIndex admission.record.input) = ∅ →
      ∀ b, ∃ q, finishLedger.currentRegisters b = some q ∧
        ∃ c, finishLedger.cutoffRegisters b = some c := by
    intro hempty b
    exact hknownRegisters hempty b
  refine ⟨{
    finished := finishLedger
    clockFinished := {
      clock := finishSnapshot.clockStarted.clock
      pending := finishLedger.pending
      ledgerCommand := some (.accumulateLocalServiceAt admission.record.input.time) }
    finish_success := hfinishSuccessReceiver
    finish_candidate := hfinishCandidateReceiver
    finish_valid := hfinishValid
    phase_ready := hfinishPhase
    cursor_finished := by
      simpa [admission.round_time, Nat.add_assoc] using hfinishCursor
    pending_finished := hfinishPending
    sigma_finished := hfinishSigma
    cutoff_finished := hfinishCutoff
    freeze_finished := hfinishFreeze
    assignment_finished := hfinishAssignment
    base_score_finished := hfinishBase
    current_registers_finished := by simpa [hdecoded] using hfinishCurrentRegisters
    cutoff_registers_finished := by simpa [hdecoded] using hfinishCutoffRegisters
    raw_buffer_finished := by simpa [hdecoded] using hfinishRaw
    enabled_history_finished := by simpa [hdecoded] using hfinishHistory
    recovered_local_service := hfinishRecoveredArm
    recovered_local_gamma_zero := admission.receiver.selected_gamma_zero
    other_known_local_service := hfinishOtherArms
    gamma_zero_after_finish := hfinishGammaZero
    register_pending_characterization := hfinishRegisterPending
    cutoff_mass_bound := hfinishCutoffMass
    joint_mass_and_service_span := by
      intro b c q hc hq
      have h := hfinishJointMass b c q hc hq
      simpa [admission.round_time, Nat.add_assoc] using h
    raw_support_bound := hfinishRawSupport
    enabled_calendar_inclusive_current := by
      intro r
      have h := hfinishHistoryEq r
      rw [hfinishFreeze] at h
      change finishLedger.enabledHistory r =
        if ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound r ∧
          CoordinatorCollectionLedger.sourceRound r < finishLedger.cursor then
          some (decide (CoordinatorCollectionLedger.sourceRound r < ledger.freezeAt))
        else none at h
      exact h
    clock_finish_success := by
      simpa [hfinishClockStartedEq] using hclockFinished
    clock_registers_preserved := by simp [hfinishClockStartedEq]
    clock_pending_matches := hclockEq
    clock_command_at_record := hclockPending
    saved_proposal_preserved := hproposalSaved
    coordinator_finish_has_no_failure := by
      simpa [admission.record_output_eq_step] using hstepFailure
    coordinator_next_is_finished_collection := by
      simpa [admission.record_output_eq_step] using hstepNextCoordinator
    decoder_bank_next_is_receiver_bank := by
      simpa [admission.record_output_eq_step, hbank] using hstepBank
    record_input_is_original_prefix_boundary := admission.record_input_state_eq_prefix
    record_output_is_original_next_prefix_boundary :=
      admission.record_output_next_eq_prefix_next
    prefix_next_is_execution_final_when_last := admission.prefix_next_eq_execution_of_last
    actual_activations_preserved := by
      simpa [admission.record_output_eq_step] using hstepActivations
    actual_follower_outputs := by
      intro j
      simpa [admission.record_output_eq_step] using hstepFollowers j
    next_ready_input := hnextReadyFields
    terminal_ready_state_boundary := hterminalBoundary
    all_known_registers_when_pending_empty := hknownOutput
  }⟩

/-- At the unchanged original source telescope, the first admissible attempt is
either the same honest rejected-prefix exhaustion boundary or an actual
accepted record with its matched receiver FINISH, clock FINISH, and original
prefix continuation facts. The accepted output's query is instantiated with
its own parsed message and the two budgets already produced by its sender. -/
theorem actual_generated_first_collection_admission_boundary
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
          ∃ output : ReferenceGeneratedFirstCollectionAdmission.AcceptedAdmissionOutput
            source rewards C_star C_h hcross s hsElapsed count hspan execution B payload ledger
            saved w Q.length k,
            output.k_before_end = hendpoint ∧
            Nonempty (AcceptedBoundaryOutput output)))) := by
  classical
  have hAdmission :=
    ReferenceGeneratedFirstCollectionAdmission.actual_generated_first_collection_accepted_admission
      rate source rewards C_star C_h hcross s hsElapsed count hspan hshort
  dsimp only at hAdmission
  rcases hAdmission with ⟨cut, payload, saved, hcut, hrest⟩
  rcases hrest with ⟨ledger, hcoordinator, hpending, hsigma, hcutoff, hbranch⟩
  refine ⟨cut, payload, saved, hcut, ledger, hcoordinator, hpending, hsigma,
    hcutoff, ?_⟩
  rcases hbranch with hexhausted | haccepted
  · exact Or.inl hexhausted
  · rcases haccepted with ⟨hendpoint, output, houtput⟩
    refine Or.inr ⟨hendpoint, output, houtput, ?_⟩
    exact accepted_boundary_of_output output

end Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

end
