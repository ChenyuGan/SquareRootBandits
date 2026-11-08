/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAcceptedReadyStep
public import Bandits.Support.ReferenceFirstCollectionRejectedReadyStep
public import Bandits.Support.ReferenceFirstCollectionStoredServiceStep
public import Bandits.Support.ReferenceFirstCutoffStoredServiceBounds

import Lean.Elab.Tactic.Omega

/-!
# Initialized finite first-collection ready and service stream

This module composes the actual checked cutoff with the actual accepted and
rejected continuing FINISH branches.  Its output stops at the first output
whose actual pending set is empty, or at exhaustion of the finite actual
collection window.  It does not assert delivery, eventual admission, physical
queue truth, a sampler law, or regret closure.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-70`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionReadyStream

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

/-- Elapsed time of the actual initialization output on the whole inputs. -/
abbrev startTime (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ) : ℕ :=
  ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed

/-- The actual reference run selected by the initialization crossing and the
same finite interval witnesses used by every producer in this module. -/
def actualEpoch (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T) :=
  ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan

/-- The original finite first-collection window, with its actual cutoff
record retained at its head. -/
def actualWindow (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T) :=
  let epoch := actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan
  ReferenceCollectionPhaseHistory.collectionWindow epoch.records
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length

/-- The generated cutoff initializer and the admitted actual epoch use the
same launch state and original physical run on the same unrestricted inputs. -/
theorem generatedFirstCutoffRun_records_eq (source : SourceInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T) :
    (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards C_star C_h
      hcross (startTime (rate := rate) source rewards C_star C_h)
      rfl count hspan).records =
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records := by
  rfl

/-- The branch certificate records the output of the actual checked FINISH
producer.  Accepted data comes from A after its real parse and acceptance
tests; rejected data comes from R after the complementary literal branch. -/
inductive ContinuingBranchOutput
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords : List (Record p rate)) (j count start : ℕ)
    (r : Record p rate) (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (recording : CoordinatorRecordingOperation.Output p)
    (started : Ledger rate) : Type where
  | accepted {M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)}
      (hparse : ReferenceCollectionSegmentExtraction.effectiveParse r.input started = some M)
      (haccept : CoordinatorCollectionLedger.acceptUpCheck started
        (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true)
      (result : ReferenceFirstCollectionAcceptedReadyStep.AcceptedFinishOutput
        source rewards epochRecords j count start r payload ledger saved
        choice recording started M) : ContinuingBranchOutput source rewards epochRecords
          j count start r payload ledger saved choice recording started
  | rejected (hrejected : ReferenceFirstCollectionRejectedReadyStep.actualRejectedBranch
      r.input started)
      (result : ReferenceFirstCollectionRejectedReadyStep.ActualRejectedFinishOutput
        r r.input payload ledger saved choice recording started source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        epochRecords count j) : ContinuingBranchOutput source rewards epochRecords
          j count start r payload ledger saved choice recording started

/-- The common FINISH ledger selected by either actual branch certificate. -/
def ContinuingBranchOutput.finished
    {source : SourceInput p} {rewards : RewardTable p}
    {epochRecords : List (Record p rate)} {j count start : ℕ}
    {r : Record p rate} {payload : Payload rate} {ledger : Ledger rate}
    {saved : Option (Fin p.T × Bool)}
    {choice : ReferenceCollectionSegmentExtraction.Choice rate}
    {recording : CoordinatorRecordingOperation.Output p}
    {started : Ledger rate}
    (branch : ContinuingBranchOutput source rewards epochRecords j count start r
      payload ledger saved choice recording started) : Ledger rate := by
  cases branch with
  | accepted _ _ result => exact result.finished
  | rejected _ result => exact result.finished

/-- One noninitial actual collection record, including its checked branch
output and the separately produced stored-service bounds on that same ledger.
This is evidence over the existing physical record and ledger types. -/
structure ContinuingStreamCell
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords : List (Record p rate)) (j count start : ℕ)
    (r : Record p rate) (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool)) where
  readyInput : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
    r.input payload ledger saved
  choice : ReferenceCollectionSegmentExtraction.Choice rate
  recording : CoordinatorRecordingOperation.Output p
  started : Ledger rate
  actualChoice : ReferenceCollectionSegmentExtraction.choice r.input = some choice
  actualRecording : CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare r.input) choice.payload choice.started choice.weights) =
      some recording
  choicePayload : choice.payload = payload
  choiceLedger : choice.preLedger = ledger
  noInitializer : choice.initializer = none
  actualStart : CoordinatorCollectionLedger.startRound ledger (r.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
      .success started
  startedIsCandidate : started = CoordinatorCollectionLedger.startRoundCandidate
    choice.preLedger r.input.time
    (ReferenceActivePhysicalStep.collectionEnabled choice.preLedger r.input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic r)
  branch : ContinuingBranchOutput source rewards epochRecords j count start r
    payload ledger saved choice recording started
  serviceLedger : Ledger rate
  serviceNextCoordinator : r.output.next.coordinator = .collection payload serviceLedger saved
  serviceLedgerIsBranch : serviceLedger = branch.finished
  context : serviceLedger.sigma = ledger.sigma ∧ serviceLedger.cutoff = ledger.cutoff ∧
    serviceLedger.freezeAt = ledger.freezeAt ∧ serviceLedger.assignment = ledger.assignment ∧
    serviceLedger.baseScore = ledger.baseScore
  cutoffLastServiceBounds : ∀ a c, serviceLedger.cutoffRegisters a = some c →
    c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n
  incrementGrowthBound : ∀ a, serviceLedger.increment a ≤
    4 * rate.n * (min serviceLedger.cursor serviceLedger.freezeAt - serviceLedger.cutoff)

/-- Apply the accepted producer, the rejected producer on the complementary
actual branch, and the stored-service producer at one continuing record. -/
private theorem continuingStreamCell_exists
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (actualWindow (rate := rate) source rewards C_star C_h hcross count hspan).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (actualWindow (rate := rate) source rewards C_star C_h hcross count hspan)[n.val].input
      payload ledger saved)
    (hCut : ∀ a c, ledger.cutoffRegisters a = some c →
      c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n)
    (hInc : ∀ a, ledger.increment a ≤
      4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff)) :
    Nonempty (ContinuingStreamCell source rewards
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + n.val)
      count
      (startTime (rate := rate) source rewards C_star C_h)
      (actualWindow (rate := rate) source rewards C_star C_h hcross count hspan)[n.val]
      payload ledger saved) := by
  classical
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let start := startTime (rate := rate) source rewards C_star C_h
  let r := window[n.val]
  have hAcceptedRoot :=
    ReferenceFirstCollectionAcceptedReadyStep.actual_first_collection_accepted_finish_ready_step
      rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
  dsimp only at hAcceptedRoot
  rcases hAcceptedRoot with ⟨hstep, htime, choice, recording, started,
    hchoice, hrecording, hchoicePayload, hchoiceLedger, hchoiceInitializer,
    hstart, hcandidate, hregisters, hacceptedQuery⟩
  have hServiceRoot :=
    ReferenceFirstCollectionStoredServiceStep.actual_first_collection_stored_service_step
      rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved
      hReady hCut hInc
  dsimp only at hServiceRoot
  rcases hServiceRoot with ⟨serviceLedger, hserviceNext, hserviceSigma,
    _hserviceCursor, hserviceCutoff, hserviceFreeze, hserviceAssignment,
    hserviceBase, _hnoAcceptedMap, _hacceptedMap, hcutService, hincService⟩
  let x := r.input
  let j := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length + n.val
  have rejectedCell (hbranch : ReferenceFirstCollectionRejectedReadyStep.actualRejectedBranch x started) :
      Nonempty (ContinuingStreamCell source rewards epoch.records j count start r payload ledger saved) := by
    let hRejectedRoot :=
      ReferenceFirstCollectionRejectedReadyStep.actual_collection_window_rejected_ready_finish
        rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
    dsimp only at hRejectedRoot
    rcases hRejectedRoot with ⟨_hstepR, _htimeR, _cutoff, _hcutoff,
      _core, _snap, _hb, _hs, _hcoord, choiceR, recordingR, startedR,
      hchoiceR, hrecordingR, _hpayloadR, _hledgerR, _hstartedR,
      _hinitR, hstartR, _hcandidateR, _hregistersR, hrejectedQuery⟩
    have hchoiceEq : choiceR = choice := Option.some.inj (hchoiceR.symm.trans hchoice)
    have hrecordingRunEq := congrArg
      (fun c : ReferenceCollectionSegmentExtraction.Choice rate =>
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights)) hchoiceEq
    have hrecordingEq : recordingR = recording := by
      apply Option.some.inj
      exact (hrecordingR.symm.trans hrecordingRunEq).trans hrecording
    rw [hrecordingEq] at hstartR
    change CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success startedR at hstartR
    have hstartAtR := hstartR
    have hstartedEq : startedR = started :=
      CoordinatorCollectionLedger.Checked.success.inj (hstartAtR.symm.trans hstart)
    subst choiceR
    subst recordingR
    subst startedR
    let result := Classical.choice (hrejectedQuery (by simpa [r, x] using hbranch))
    have hbranchNext : r.output.next.coordinator =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.actualLastProposal := by
      calc
        r.output.next.coordinator = (ReferenceActivePhysicalStep.step r.input).next.coordinator :=
          congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput r.input => out.next.coordinator) r.output_eq
        _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.actualLastProposal :=
          result.step_next_coordinator_eq
    have hproposal : result.actualLastProposal = saved := result.actualLastProposal_eq
    have hsame : serviceLedger = result.finished := by
      have hcoordinator :
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload serviceLedger saved =
            ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.actualLastProposal := by
        calc
          ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload serviceLedger saved = r.output.next.coordinator := hserviceNext.symm
          _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.actualLastProposal := hbranchNext
      rw [hproposal] at hcoordinator
      injection hcoordinator with _ hledger _
    refine ⟨{
      readyInput := hReady
      choice := choice
      recording := recording
      started := started
      actualChoice := hchoice
      actualRecording := hrecording
      choicePayload := hchoicePayload
      choiceLedger := hchoiceLedger
      noInitializer := hchoiceInitializer
      actualStart := hstart
      startedIsCandidate := hcandidate
      branch := .rejected (by simpa [r, x] using hbranch) result
      serviceLedger := serviceLedger
      serviceNextCoordinator := hserviceNext
      serviceLedgerIsBranch := by simp [ContinuingBranchOutput.finished, hsame]
      context := ⟨hserviceSigma, hserviceCutoff, hserviceFreeze, hserviceAssignment, hserviceBase⟩
      cutoffLastServiceBounds := hcutService
      incrementGrowthBound := hincService
    }⟩
  cases hparse : ReferenceCollectionSegmentExtraction.effectiveParse x started with
  | none => exact rejectedCell (Or.inl hparse)
  | some M =>
      by_cases haccept : CoordinatorCollectionLedger.acceptUpCheck started
          (ReferenceActivePhysicalStep.upSenderIndex x) M = true
      · let result := Classical.choice (hacceptedQuery M hparse haccept)
        have hsame : serviceLedger = result.finished := by
          have hcoordinator :
              ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload serviceLedger saved =
                ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.lastProposal := by
            calc
              ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload serviceLedger saved = r.output.next.coordinator := hserviceNext.symm
              _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection payload result.finished result.lastProposal := result.actualNextCoordinator
          rw [result.lastProposalIsSaved] at hcoordinator
          injection hcoordinator with _ hledger _
        refine ⟨{
          readyInput := hReady
          choice := choice
          recording := recording
          started := started
          actualChoice := hchoice
          actualRecording := hrecording
          choicePayload := hchoicePayload
          choiceLedger := hchoiceLedger
          noInitializer := hchoiceInitializer
          actualStart := hstart
          startedIsCandidate := hcandidate
          branch := .accepted hparse haccept result
          serviceLedger := serviceLedger
          serviceNextCoordinator := hserviceNext
          serviceLedgerIsBranch := by simp [ContinuingBranchOutput.finished, hsame]
          context := ⟨hserviceSigma, hserviceCutoff, hserviceFreeze, hserviceAssignment, hserviceBase⟩
          cutoffLastServiceBounds := hcutService
          incrementGrowthBound := hincService
        }⟩

      · exact rejectedCell (Or.inr ⟨M, hparse, Bool.eq_false_iff.mpr haccept⟩)

section CellConsequences

variable {source : SourceInput p} {rewards : RewardTable p}
  {epochRecords : List (Record p rate)} {j count start : ℕ}
  {r : Record p rate} {payload : Payload rate} {ledger : Ledger rate}
  {saved : Option (Fin p.T × Bool)}

/-- Common valid/ready facts on the branch's same stored-service ledger.
The branch field additionally exposes its full joint mass, service, raw,
calendar and bank bounds, with checked receiver and FINISH evidence. -/
theorem ContinuingStreamCell.output_properties
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved) :
    r.output.coordinator.failure = none ∧
    CoordinatorCollectionLedger.validLedgerCheck cell.serviceLedger = true ∧
    cell.serviceLedger.phase = CoordinatorCollectionLedger.Phase.ready ∧
    cell.serviceLedger.cursor = r.input.time.val + 2 ∧
    cell.serviceLedger.gammaLoc = (fun _ => 0) ∧
    ∀ a, (cell.serviceLedger.currentRegisters a = none ↔
        CoordinatorCollectionLedger.armPending cell.serviceLedger a) ∧
      (cell.serviceLedger.cutoffRegisters a = none ↔
        CoordinatorCollectionLedger.armPending cell.serviceLedger a) := by
  have hsame := cell.serviceLedgerIsBranch
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      rw [hbranch] at hsame
      change cell.serviceLedger = result.finished at hsame
      rw [hsame]
      exact ⟨result.actualCoordinatorFailureNone, result.finishedValid, result.finishedReady,
        result.finishedCursor, result.finishedGammaZero, result.registerPendingEquivalence⟩
  | rejected hreject result =>
      rw [hbranch] at hsame
      change cell.serviceLedger = result.finished at hsame
      rw [hsame]
      exact ⟨result.actual_record_failure_none, result.finished_valid, result.finished_phase,
        result.finished_cursor, result.finished_gammaLoc,
        fun a => ⟨(result.finished_register_pending a).1, (result.finished_register_pending a).2.1⟩⟩

theorem cell_pending_recurrence
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved) :
    cell.serviceLedger.pending = ReferenceCollectionPhaseHistory.eraseEvent ledger.pending
      (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      rw [hsame]
      exact result.eraseEventExact
  | rejected hreject result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      rw [hsame]
      exact result.eraseEvent_recurrence

theorem cell_sender_pending
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved) :
    ReferenceCollectionPhaseHistory.acceptedLabel r.input =
      some (ReferenceActivePhysicalStep.upSenderIndex r.input) →
    ReferenceActivePhysicalStep.upSenderIndex r.input ∈ ledger.pending := by
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      intro _
      exact result.senderWasPending
  | rejected hreject result =>
      intro hlabel
      have hnone := result.acceptedLabel_none
      rw [hnone] at hlabel
      cases hlabel

theorem cell_next_ready
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved)
    (hpending : cell.serviceLedger.pending.Nonempty)
    (hnextTime : r.input.time.val + 1 < p.T) :
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = r.output.next ∧ next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = rewards ∧ next.time.val = r.input.time.val + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next payload cell.serviceLedger saved ∧
      ∀ hnext : j + 1 < epochRecords.length,
        next = (epochRecords[j + 1]'hnext).input := by
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      have hpending' : result.finished.pending.Nonempty := by
        rw [← hsame]
        exact hpending
      rcases result.nextReadyOnOriginalPrefix hpending' hnextTime with
        ⟨next, hstate, hrows, hselected, hrewards, htime, hready, hretain⟩
      rw [← hsame, result.lastProposalIsSaved] at hready
      exact ⟨next, hstate, hrows, hselected, hrewards, htime, hready, hretain⟩
  | rejected hreject result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      rcases result.next_ready_prefix hnextTime with
        ⟨next, hstate, hrows, hselected, hrewards, htime, hready, hretain⟩
      rw [← hsame, result.actualLastProposal_eq] at hready
      have hstate' : next.state = r.output.next := by
        rw [r.output_eq]
        exact hstate
      exact ⟨next, hstate', hrows, hselected, hrewards, htime, hready, hretain⟩

theorem cell_terminal_ready
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved)
    (hpending : cell.serviceLedger.pending.Nonempty)
    (hterminal : r.input.time.val + 1 = p.T) :
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      r.output.next payload cell.serviceLedger saved := by
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      have hpending' : result.finished.pending.Nonempty := by
        rw [← hsame]
        exact hpending
      have hready := result.terminalReadyBoundary hpending' hterminal
      rw [← hsame, result.lastProposalIsSaved] at hready
      exact hready
  | rejected hreject result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      have hready := result.boundary_ready hterminal
      rw [← hsame, result.actualLastProposal_eq] at hready
      simpa [r.output_eq] using hready

theorem cell_all_known_when_empty
    (cell : ContinuingStreamCell source rewards epochRecords j count start r payload ledger saved)
    (hempty : cell.serviceLedger.pending = ∅) :
    ∀ a, (∃ q, cell.serviceLedger.currentRegisters a = some q) ∧
      (∃ c, cell.serviceLedger.cutoffRegisters a = some c) := by
  cases hbranch : cell.branch with
  | accepted hparse haccept result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      have hempty' : result.finished.pending = ∅ := by
        rw [← hsame]
        exact hempty
      simpa [hsame] using result.allKnownWhenPendingEmpty hempty'
  | rejected hreject result =>
      have hsame : cell.serviceLedger = result.finished := by
        have hsame' := cell.serviceLedgerIsBranch
        rw [hbranch] at hsame'
        simpa [ContinuingBranchOutput.finished] using hsame'
      have hnonempty := result.finished_pending_nonempty
      rw [← hsame] at hnonempty
      exfalso
      exact (Finset.nonempty_iff_ne_empty.mp hnonempty) hempty

end CellConsequences

/-- A continuing input at an index of the original finite window. Its local
ready domain and stored-service bounds are carried as output evidence, never
as premises of the exported initialized construction. -/
structure ActualTailInput
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords window : List (Record p rate))
    (count start w : ℕ) (payload : Payload rate)
    (saved : Option (Fin p.T × Bool)) (offset : ℕ) where
  index_lt : offset < window.length
  ledger : Ledger rate
  ready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
    (window[offset]'index_lt).input payload ledger saved
  cutoffBounds : ∀ a c, ledger.cutoffRegisters a = some c →
    c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n
  incrementBound : ∀ a, ledger.increment a ≤
    4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff)

/-- The actual ready/service cells from offset one onward, ending at the first
empty pending ledger or at the actual finite window boundary. The recursive
case stores the producer's same-prefix readiness and retained-record equality. -/
inductive ActualTailTrace
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords window : List (Record p rate))
    (count start w : ℕ) (payload : Payload rate)
    (saved : Option (Fin p.T × Bool)) :
    (offset : ℕ) → ActualTailInput source rewards epochRecords window
      count start w payload saved offset → List (Ledger rate) → Type where
  | firstEmpty {offset : ℕ}
      (input : ActualTailInput source rewards epochRecords window count start w payload saved offset)
      (cell : ContinuingStreamCell source rewards epochRecords (w + offset) count start
        (window[offset]'input.index_lt) payload input.ledger saved)
      (hempty : cell.serviceLedger.pending = ∅) :
      ActualTailTrace source rewards epochRecords window count start w payload saved
        offset input [cell.serviceLedger]
  | windowExhausted {offset : ℕ}
      (input : ActualTailInput source rewards epochRecords window count start w payload saved offset)
      (cell : ContinuingStreamCell source rewards epochRecords (w + offset) count start
        (window[offset]'input.index_lt) payload input.ledger saved)
      (hpending : cell.serviceLedger.pending.Nonempty)
      (hend : offset + 1 = window.length) :
      ActualTailTrace source rewards epochRecords window count start w payload saved
        offset input [cell.serviceLedger]
  | nextRecord {offset : ℕ}
      (input : ActualTailInput source rewards epochRecords window count start w payload saved offset)
      (cell : ContinuingStreamCell source rewards epochRecords (w + offset) count start
        (window[offset]'input.index_lt) payload input.ledger saved)
      (hpending : cell.serviceLedger.pending.Nonempty)
      (hnextIndex : offset + 1 < window.length)
      (next : ReferenceActivePhysicalStep.RoundInput p rate)
      (hstate : next.state = (window[offset]'input.index_lt).output.next)
      (hrows : next.rows = source.1.2)
      (hselected : next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source)
      (hrewards : next.rewards = rewards)
      (htime : next.time.val = (window[offset]'input.index_lt).input.time.val + 1)
      (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next payload cell.serviceLedger saved)
      (hretain : ∀ hnext : w + offset + 1 < epochRecords.length,
        next = (epochRecords[w + offset + 1]'hnext).input)
      (hnextRecord : next = (window[offset + 1]'hnextIndex).input)
      (tailLedgers : List (Ledger rate))
      (tail : ActualTailTrace source rewards epochRecords window count start w payload saved
        (offset + 1)
        ⟨hnextIndex, cell.serviceLedger,
          (by simpa [hnextRecord] using hready),
          cell.cutoffLastServiceBounds, cell.incrementGrowthBound⟩ tailLedgers) :
      ActualTailTrace source rewards epochRecords window count start w payload saved
        offset input (cell.serviceLedger :: tailLedgers)

private theorem actualTailTrace_exists
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (payload : Payload rate) (saved : Option (Fin p.T × Bool))
    (offset : ℕ)
    (input : ActualTailInput source rewards
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
      (actualWindow (rate := rate) source rewards C_star C_h hcross count hspan)
      count
      (startTime (rate := rate) source rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length
      payload saved offset) :
    Nonempty (Σ ledgers : List (Ledger rate), ActualTailTrace source rewards
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
      (actualWindow (rate := rate) source rewards C_star C_h hcross count hspan)
      count
      (startTime (rate := rate) source rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length
      payload saved offset input ledgers) := by
  classical
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let start := startTime (rate := rate) source rewards C_star C_h
  have hwindowTime := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hwindowTime
  have hrec : ∀ rem offset, rem = window.length - offset →
      ∀ input : ActualTailInput source rewards epoch.records window count start w payload saved offset,
        Nonempty (Σ ledgers : List (Ledger rate),
          ActualTailTrace source rewards epoch.records window count start w payload saved
            offset input ledgers) := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | h rem ih =>
      intro offset hrem input
      let n : Fin window.length := ⟨offset, input.index_lt⟩
      let cell := Classical.choice
        (continuingStreamCell_exists source rewards C_star C_h count hcross hspan hshort
          n payload input.ledger saved input.ready input.cutoffBounds input.incrementBound)
      by_cases hempty : cell.serviceLedger.pending = ∅
      · exact ⟨⟨[cell.serviceLedger], .firstEmpty input cell hempty⟩⟩
      · have hpending : cell.serviceLedger.pending.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hempty
        by_cases hend : offset + 1 = window.length
        · exact ⟨⟨[cell.serviceLedger], .windowExhausted input cell hpending hend⟩⟩
        · have hindex := input.index_lt
          have hnextIndex : offset + 1 < window.length := by omega
          let nextIndex : Fin window.length := ⟨offset + 1, hnextIndex⟩
          have hcurrentTime : (window[offset]'input.index_lt).input.time.val + 1 =
              start + w + 1 + offset := by
            simpa [n] using (hwindowTime n).2
          have hnextRecordLookup := (hwindowTime nextIndex).1
          have hnextTime : (window[offset]'input.index_lt).input.time.val + 1 < p.T := by
            have hnextFin := (window[offset + 1]'hnextIndex).input.time.isLt
            have hnextTime' : (window[offset + 1]'hnextIndex).input.time.val + 1 =
                start + w + 1 + (offset + 1) := by
              simpa [nextIndex] using (hwindowTime nextIndex).2
            omega
          obtain ⟨next, hstate, hrows, hselected, hrewards, htime, hready, hretain⟩ :=
            cell_next_ready cell hpending hnextTime
          have hnextRecordLookup' : epoch.records[w + offset + 1]? =
              some (window[offset + 1]'hnextIndex) := by
            simpa [nextIndex, Nat.add_assoc] using hnextRecordLookup
          have hrecordIndex : w + offset + 1 < epoch.records.length := by
            by_contra hnot
            have hnone := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hnot)
            rw [hnone] at hnextRecordLookup'
            cases hnextRecordLookup'
          have hget := List.getElem?_eq_getElem
            (l := epoch.records) (i := w + offset + 1) hrecordIndex
          have hrecordEq : epoch.records[w + offset + 1]'hrecordIndex =
              window[offset + 1]'hnextIndex :=
            Option.some.inj (hget.symm.trans hnextRecordLookup')
          have hnextRecord : next = (window[offset + 1]'hnextIndex).input := by
            calc
              next = (epoch.records[w + offset + 1]'hrecordIndex).input := hretain hrecordIndex
              _ = (window[offset + 1]'hnextIndex).input := congrArg
                ReferenceActivePhysicalHorizon.RoundRecord.input hrecordEq
          have hremNext : rem - 1 = window.length - (offset + 1) := by omega
          let nextInput : ActualTailInput source rewards epoch.records window count start w payload saved
              (offset + 1) := ⟨hnextIndex, cell.serviceLedger,
                by simpa [hnextRecord] using hready,
                cell.cutoffLastServiceBounds, cell.incrementGrowthBound⟩
          obtain ⟨⟨tailLedgers, htail⟩⟩ :=
            ih (rem - 1) (by omega) (offset + 1) hremNext nextInput
          exact ⟨⟨cell.serviceLedger :: tailLedgers,
            .nextRecord input cell hpending hnextIndex next hstate hrows hselected hrewards
              htime hready hretain hnextRecord tailLedgers htail⟩⟩
  exact hrec (window.length - offset) offset rfl input

/-- The actual cutoff record and its C-produced FINISH output at the head of
the original collection window. The conditional stored-service facts come
from C at exactly this returned ledger. -/
structure ActualCutoffData
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) where
  cut : Record p rate
  payload : Payload rate
  saved : Option (Fin p.T × Bool)
  ledger : Ledger rate
  cutIndex : (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records[
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length]? = some cut
  cutTime : cut.input.time.val =
    startTime (rate := rate) source rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length
  outputCoordinator : cut.output.next.coordinator =
    .collection payload ledger saved
  ledgerCutoff : ledger.cutoff =
    startTime (rate := rate) source rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1
  ledgerCursor : ledger.cursor =
    startTime (rate := rate) source rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 2
  cutoffRegisterBounds : ∀ a c, ledger.cutoffRegisters a = some c →
    c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n
  incrementGrowthBound : ∀ a, ledger.increment a ≤
    4 * rate.n * (min ledger.cursor ledger.freezeAt - ledger.cutoff)

private theorem actual_cutoff_data_exists
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) :
    Nonempty (ActualCutoffData source rewards C_star C_h count hcross hspan hshort) := by
  classical
  have hcutoff :=
    ReferenceFirstCutoffStoredServiceBounds.actual_first_cutoff_stored_service_bounds
      rate source rewards C_star C_h hcross count hspan hshort
  dsimp only at hcutoff
  rcases hcutoff with ⟨cut, suffix, hsplit, hcutIndex, htime, hrows, hselected,
    hrewards, r, q, base, hstate, dispatched, hstart, startLedger, hinit,
    hledger, hdomain, hclock, hpending, hnoAssignment, selected, hpreparation,
    l0, initializer, choice, hl0, hinitializer, hchoice, hchoiceInitializer,
    hchecked, hl0cursor, hl0cutoff, hl0freeze, hfreezeBound, hcutoffBounds,
    hl0increment, recording, ledgerStarted, input, decoded, bank, ledger,
    hrecording, hstarted, hinput, hdecoded, hreceive, hfinish, hnext,
    hfinishedCutoff, hfinishedCursor, hfinishedFreeze, hfinishedRegisters,
    hfinishedBounds, hincrement⟩
  refine ⟨{
    cut := cut
    payload := r.payload
    saved := dispatched.startResult.clock.lastProposal
    ledger := ledger
    cutIndex := ?_
    cutTime := ?_
    outputCoordinator := ?_
    ledgerCutoff := hfinishedCutoff
    ledgerCursor := hfinishedCursor
    cutoffRegisterBounds := hfinishedBounds
    incrementGrowthBound := hincrement
  }⟩
  · rw [hcutIndex]
    exact List.getElem?_eq_getElem _
  · exact htime
  · exact hnext

/-- Generated-run shortness is derived from the actual-run selector using the
exact public run equality above. -/
theorem generatedFirstCutoffRun_short (source : SourceInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards C_star C_h
        hcross (startTime (rate := rate) source rewards C_star C_h)
        rfl count hspan).records).length < count := by
  rw [generatedFirstCutoffRun_records_eq]
  exact hshort

section TailConsequences

variable {source : SourceInput p} {rewards : RewardTable p}
  {records window : List (Record p rate)} {count start w offset : ℕ}
  {payload : Payload rate} {saved : Option (Fin p.T × Bool)}
  {input : ActualTailInput source rewards records window count start w payload saved offset}
  {ledgers : List (Ledger rate)}

private theorem actualTailTrace_length_bounds
    (trace : ActualTailTrace source rewards records window count start w payload saved
      offset input ledgers) :
    1 ≤ ledgers.length ∧ ledgers.length ≤ window.length - offset := by
  induction trace with
  | firstEmpty input cell hempty =>
      simp only [List.length_cons, List.length_nil]
      constructor
      · omega
      · have hi := input.index_lt
        omega
  | windowExhausted input cell hpending hend =>
      simp only [List.length_cons, List.length_nil]
      constructor
      · omega
      · omega
  | nextRecord input cell hpending hnextIndex next hstate hrows hselected hrewards htime
      hready hretain hnextRecord tailLedgers tail ih =>
      simp only [List.length_cons]
      omega

/-- Recover any produced continuing cell and its literal predecessor ledger.
The optional lookup avoids transporting dependent list indices. -/
theorem ActualTailTrace.cell_at
    (trace : ActualTailTrace source rewards records window count start w payload saved offset input ledgers)
    (k : ℕ) (hk : k < ledgers.length) :
    ∃ j r incoming, ∃ cell : ContinuingStreamCell source rewards records j count start r payload incoming saved,
      j = w + offset + k ∧ window[offset + k]? = some r ∧
      cell.serviceLedger = ledgers[k] ∧
      (k = 0 → incoming = input.ledger) ∧
      (∀ hpos : 0 < k, incoming = ledgers[k - 1]'(by omega)) := by
  induction trace generalizing k with
  | firstEmpty input cell hempty | windowExhausted input cell hpending hend =>
      have hk0 : k = 0 := by
        simp only [List.length_cons, List.length_nil] at hk
        omega
      subst k
      exact ⟨_, _, _, cell, by omega, by simp, rfl, fun _ => rfl, by omega⟩
  | nextRecord input cell hpending hnextIndex next hstate hrows hselected hrewards htime
      hready hretain hnextRecord tailLedgers tail ih =>
      cases k with
      | zero => exact ⟨_, _, _, cell, by omega, by simp, rfl, fun _ => rfl, by omega⟩
      | succ k =>
          obtain ⟨j, r, incoming, later, hj, hr, hout, hfirst, hprev⟩ := ih k (by simpa using hk)
          refine ⟨j, r, incoming, later, by omega, ?_, ?_, by omega, ?_⟩
          · simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hr
          · simpa only [List.getElem_cons_succ] using hout
          · intro _
            cases k with
            | zero => simpa using hfirst rfl
            | succ k => simpa only [Nat.add_sub_cancel, List.getElem_cons_succ] using hprev (by omega)

/-- Every output before the last produced output still has pending replies. -/
theorem ActualTailTrace.pending_before_last
    (trace : ActualTailTrace source rewards records window count start w payload saved offset input ledgers)
    (k : ℕ) (hk : k < ledgers.length) (hbefore : k + 1 < ledgers.length) :
    (ledgers[k]'hk).pending.Nonempty := by
  induction trace generalizing k with
  | firstEmpty input cell hempty | windowExhausted input cell hpending hend =>
      simp only [List.length_cons, List.length_nil] at hbefore
      omega
  | nextRecord input cell hpending hnextIndex next hstate hrows hselected hrewards htime
      hready hretain hnextRecord tailLedgers tail ih =>
      cases k with
      | zero => exact hpending
      | succ k => exact ih k (by simpa using hk) (by simpa using hbefore)

/-- A produced tail ending strictly inside the available window ends empty. -/
theorem ActualTailTrace.last_empty_of_not_exhausted
    (trace : ActualTailTrace source rewards records window count start w payload saved offset input ledgers)
    (k : ℕ) (hk : k < ledgers.length) (hlast : k + 1 = ledgers.length)
    (hshort : offset + ledgers.length < window.length) :
    (ledgers[k]'hk).pending = ∅ := by
  induction trace generalizing k with
  | firstEmpty input cell hempty =>
      have hk0 : k = 0 := by
        simp only [List.length_cons, List.length_nil] at hk
        omega
      subst k
      exact hempty
  | windowExhausted input cell hpending hend =>
      simp only [List.length_cons, List.length_nil] at hshort
      omega
  | nextRecord input cell hpending hnextIndex next hstate hrows hselected hrewards htime
      hready hretain hnextRecord tailLedgers tail ih =>
      cases k with
      | zero =>
          have hpos := (actualTailTrace_length_bounds tail).1
          simp only [List.length_cons] at hlast
          omega
      | succ k =>
          exact ih k (by simpa using hk) (by simpa using hlast) (by simp only [List.length_cons] at hshort; omega)

end TailConsequences

/-- The tail is absent only when the actual cutoff is the complete one-record
window. Otherwise it carries the starting ready input and full producer trace. -/
inductive ActualTailOutput
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords window : List (Record p rate))
    (count start w : ℕ) (payload : Payload rate)
    (saved : Option (Fin p.T × Bool)) (initial : Ledger rate) : List (Ledger rate) → Type where
  | noNext (hwindow : window.length = 1) :
      ActualTailOutput source rewards epochRecords window count start w payload saved initial []
  | continuing {ledgers : List (Ledger rate)}
      (input : ActualTailInput source rewards epochRecords window count start w payload saved 1)
      (initialLedger : input.ledger = initial)
      (trace : ActualTailTrace source rewards epochRecords window count start w payload saved
        1 input ledgers) :
      ActualTailOutput source rewards epochRecords window count start w payload saved initial ledgers

section TailOutputConsequences

variable {source : SourceInput p} {rewards : RewardTable p}
  {records window : List (Record p rate)} {count start w : ℕ}
  {payload : Payload rate} {saved : Option (Fin p.T × Bool)}
  {initial : Ledger rate} {ledgers : List (Ledger rate)}

private theorem tail_cell_at
    (tail : ActualTailOutput source rewards records window count start w payload saved initial ledgers)
    (k : ℕ) (hk : k < ledgers.length) :
    ∃ j r incoming, ∃ cell : ContinuingStreamCell source rewards records j count start r payload incoming saved,
      j = w + 1 + k ∧ window[1 + k]? = some r ∧ cell.serviceLedger = ledgers[k] ∧
      (k = 0 → incoming = initial) ∧
      (∀ hpos : 0 < k, incoming = ledgers[k - 1]'(by omega)) := by
  cases tail with
  | noNext hend => simp only [List.length_nil] at hk; omega
  | continuing input hinit trace =>
      obtain ⟨j, r, incoming, cell, hj, hr, hf, hfirst, hprev⟩ := trace.cell_at k hk
      exact ⟨j, r, incoming, cell, hj, hr, hf, fun hz => (hfirst hz).trans hinit, hprev⟩

private theorem tail_pending_before_last
    (tail : ActualTailOutput source rewards records window count start w payload saved initial ledgers)
    (k : ℕ) (hk : k < ledgers.length) (hbefore : k + 1 < ledgers.length) :
    (ledgers[k]'hk).pending.Nonempty := by
  cases tail with
  | noNext hend => simp only [List.length_nil] at hk; omega
  | continuing input hinit trace => exact trace.pending_before_last k hk hbefore

private theorem tail_last_empty
    (tail : ActualTailOutput source rewards records window count start w payload saved initial ledgers)
    (hshort : ledgers.length + 1 < window.length) :
    ∃ k, ∃ hk : k < ledgers.length, k + 1 = ledgers.length ∧ (ledgers[k]'hk).pending = ∅ := by
  cases tail with
  | noNext hend => simp only [List.length_nil] at hshort; omega
  | continuing input hinit trace =>
      have hpos := (actualTailTrace_length_bounds trace).1
      refine ⟨ledgers.length - 1, by omega, by omega, ?_⟩
      exact trace.last_empty_of_not_exhausted _ (by omega) (by omega) (by omega)

end TailOutputConsequences

/-- The cutoff's real checked initializer, START, rejected receive and FINISH.
All witnesses refer to the original cutoff record and its same output ledger. -/
structure CutoffExecution (cut : Record p rate) (payload : Payload rate)
    (finished : Ledger rate) where
  live : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta
  owned : CoordinatorLiveServiceFinish.OwnedRegisters live
  base : Fin (p.m - 1) → ℕ
  actualLive : cut.input.state.coordinator = .live live owned base
  payloadIsLive : payload = live.payload
  initializer : ReferenceCollectionSegmentExtraction.Initializer p
  literalInitializer : initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
    (ReferenceActivePhysicalStep.liveInput cut.input live owned base).registers
    (ReferenceActivePhysicalStep.liveInput cut.input live owned base).ownedRegisters base cut.input.time
  initial : Ledger rate
  checkedInitialization : initializer.checkedStart rate = .success initial
  recording : CoordinatorRecordingOperation.Output p
  started : Ledger rate
  startSuccess : CoordinatorCollectionLedger.startRound initial (cut.input.time.val + 1)
    (ReferenceActivePhysicalStep.collectionEnabled initial cut.input.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started
  actualRecording : cut.output.coordinator.recording = some recording
  decoded : Ledger rate
  bank : CoordinatorUpReception.UpDecoderBank p
  receiveRejected : (ReferenceActivePhysicalStep.receiveUp cut.output.preparation started).result =
    .rejected (decoded, bank)
  finishSuccess : CoordinatorCollectionLedger.finishRound decoded = .success finished

/-- Alternatives at an actual selected FINISH. The next input is the original
prefix input, even beyond a shortened requested count; at `T` only a state
boundary is supplied. This certificate is produced, never a root premise. -/
structure Boundary (source : SourceInput p) (rewards : RewardTable p)
    (records : List (Record p rate)) (j : ℕ) (r : Record p rate)
    (payload : Payload rate) (finished : Ledger rate) (saved : Option (Fin p.T × Bool)) : Prop where
  allKnownWhenEmpty : finished.pending = ∅ →
    ∀ a, (∃ q, finished.currentRegisters a = some q) ∧ (∃ c, finished.cutoffRegisters a = some c)
  nextReady : finished.pending.Nonempty → r.input.time.val + 1 < p.T →
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = r.output.next ∧ next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = rewards ∧ next.time.val = r.input.time.val + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain next payload finished saved ∧
      ∀ hi : j + 1 < records.length, next = (records[j + 1]'hi).input
  terminalReady : finished.pending.Nonempty → r.input.time.val + 1 = p.T →
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      r.output.next payload finished saved

/-- Produced initialized stream data. `cutoffExecution` contains the actual checked
initializer and operations; `cutoff` is C's same indexed cutoff and FINISH. The tail is an initial segment of the original window, with the
producer's same-prefix readiness and retained-record equality carried at its
first continuation. The public `ledgers` map begins with the actual cutoff. -/
structure ActualInitializedStreamOutput
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) where
  window : List (Record p rate)
  windowIsActual : window = actualWindow (rate := rate) source rewards C_star C_h hcross count hspan
  windowNonempty : 0 < window.length
  alignment : ∀ n : Fin window.length,
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records[
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + n.val]? =
      some window[n.val] ∧
    window[n.val].input.time.val + 1 = startTime (rate := rate) source rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1 + n.val
  originalInputs : ∀ n : Fin window.length,
    window[n.val].input.rows = source.1.2 ∧
    window[n.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    window[n.val].input.rewards = rewards
  cutoff : ActualCutoffData source rewards C_star C_h count hcross hspan hshort
  payload : Payload rate
  saved : Option (Fin p.T × Bool)
  initialLedger : Ledger rate
  payloadMatchesCutoff : payload = cutoff.payload
  savedMatchesCutoff : saved = cutoff.saved
  ledgerMatchesCutoff : initialLedger = cutoff.ledger
  cutoffIsHead : window[0]'(by omega) = cutoff.cut
  cutoffFailureNone : cutoff.cut.output.coordinator.failure = none
  cutoffPendingUniv : cutoff.ledger.pending = Finset.univ
  cutoffPendingNonempty : cutoff.ledger.pending.Nonempty
  cutoffContext : cutoff.ledger.sigma = startTime (rate := rate) source rewards C_star C_h + 1 ∧
    cutoff.payload.sigma.val = startTime (rate := rate) source rewards C_star C_h ∧
    cutoff.ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val cutoff.payload.sigma ∧
    cutoff.ledger.assignment.arm = cutoff.payload.assignment.assigned ∧
    cutoff.ledger.baseScore = (fun _ => 0)
  cutoffExecution : Nonempty (CutoffExecution cutoff.cut cutoff.payload cutoff.ledger)
  cutoffValid : CoordinatorCollectionLedger.validLedgerCheck cutoff.ledger = true
  cutoffPhase : cutoff.ledger.phase = CoordinatorCollectionLedger.Phase.ready
  cutoffGamma : ∀ a, cutoff.ledger.gammaLoc a = 0
  cutoffNextReady : cutoff.cut.input.time.val + 1 < p.T →
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = cutoff.cut.output.next ∧ next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = rewards ∧ next.time.val = cutoff.cut.input.time.val + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next cutoff.payload cutoff.ledger cutoff.saved ∧
      ∀ hi : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1 <
          (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records.length,
        next = ((actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records[
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + 1]'hi).input
  cutoffTerminalReady : cutoff.cut.input.time.val + 1 = p.T →
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      cutoff.cut.output.next cutoff.payload cutoff.ledger cutoff.saved
  tailLedgers : List (Ledger rate)
  tail : ActualTailOutput source rewards
    (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
    window count
    (startTime (rate := rate) source rewards C_star C_h)
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length
    payload saved cutoff.ledger tailLedgers
  ell : ℕ
  ellEq : ell = tailLedgers.length + 1
  positiveLength : 1 ≤ ell
  withinWindow : ell ≤ window.length
  ledgers : Fin ell → Ledger rate
  ledgers_are_outputs : ∀ n : Fin ell,
    ledgers n = (cutoff.ledger :: tailLedgers)[n.val]'(by rw [List.length_cons, ← ellEq]; exact n.isLt)

/-- Produce the actual nonempty initial segment of the real collection window.
Its first ledger is C's checked cutoff FINISH. Each later ledger is obtained
from the same actual record by the accepted or rejected FINISH producer and
stored-service producer, and recursion stops at first empty pending or window
exhaustion. -/
theorem actual_initialized_first_collection_ready_stream
    (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count) :
    Nonempty (ActualInitializedStreamOutput source rewards C_star C_h count hcross hspan hshort) := by
  classical
  let epoch := actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let start := startTime (rate := rate) source rewards C_star C_h
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  have hshortActual :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count := by
    simpa [actualEpoch] using hshort
  let cutoff := Classical.choice
    (actual_cutoff_data_exists source rewards C_star C_h count hcross hspan hshortActual)
  have hcount : epoch.records.length = count := by
    simpa [epoch, actualEpoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hw : w < epoch.records.length := by
    rw [hcount]
    simpa [w, epoch] using hshort
  have hdrop : epoch.records.drop w ≠ [] := by
    intro hd
    have hdropLength : (epoch.records.drop w).length = epoch.records.length - w := by simp
    rw [hd] at hdropLength
    simp at hdropLength
    omega
  have hwindowNe : window ≠ [] := by
    have htake : (epoch.records.drop w).take 1 ≠ [] := by
      intro hnil
      cases h : epoch.records.drop w with
      | nil => exact hdrop h
      | cons head tail => simp [h] at hnil
    intro hnil
    dsimp [window, ReferenceCollectionPhaseHistory.collectionWindow] at hnil
    cases hfirst : (epoch.records.drop w).take 1 with
    | nil => exact htake hfirst
    | cons head tail => simp [hfirst] at hnil
  have hwindowPos : 0 < window.length := List.length_pos_of_ne_nil hwindowNe
  have hwindowTime := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshortActual
  dsimp only at hwindowTime
  have hwindowIndex (j : ℕ) (hj : j < window.length) :
      epoch.records[w + j]? = some (window[j]'hj) := by
    let n : Fin window.length := ⟨j, hj⟩
    simpa [n, epoch, w, window, actualEpoch] using (hwindowTime n).1
  have hwindowHead : window[0]'(by omega) = cutoff.cut := by
    have hlookup : epoch.records[w]? = some (window[0]'(by omega)) := by
      simpa only [Nat.add_zero] using hwindowIndex 0 (by omega)
    exact Option.some.inj (hlookup.symm.trans cutoff.cutIndex)
  have hgeneratedRun :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
        C_star C_h hcross start rfl count hspan).records = epoch.records :=
    generatedFirstCutoffRun_records_eq source rewards C_star C_h hcross count hspan
  have hgeneratedShort := generatedFirstCutoffRun_short source rewards C_star C_h
    hcross count hspan hshort
  have hreadyInit :=
    ReferenceFirstCollectionReadyInitialization.actual_first_collection_ready_initialization
      rate source rewards C_star C_h hcross start rfl count hspan hgeneratedShort
  dsimp only at hreadyInit
  rcases hreadyInit with ⟨_hsT, cutReady, suffixReady, _hsplitReady, hindexReady,
    _htimeReady, _hstateReady, _hrowsReady, _hselectedReady, _hrewardsReady,
    rReady, _qReady, _baseReady, _hreadyLive, _hsigmaReady, dispatchedReady,
    _hstartReady, _ledgerReady, _hinitReady, _hledgerReady, _hdomainReady,
    _hclockReady, _hpendingReady, _hnoAssignmentReady, _selectedReady,
    _hbranchReady, _huReady, _huTReady, _hugReady, _hsigmaLedgerReady,
    _hcutoffLedgerReady, _recordingReady, _hactualInputReady, _htraceReady,
    _hrecordingDiagnosticReady, _hrecordingRunReady, _ledgerStartedReady,
    _hstartSuccessReady, _hstartCandidateReady, _inputReady, _decodedReady,
    _bankReady, _diagnosticReady, finishedReady, _hinputReady,
    _hinputDomainReady, _hinputCheckReady, _htransitionReady, _hquotaReady,
    _hdecodedReady, _hreceiveReady, _hbankReady, _hbankUpdateReady, _hbankFrameReady,
    _hrawParsedReady, _hreceiveDiagnosticReady, _hdiagnosticInputReady,
    _hdiagnosticExpectedReady, _hdiagnosticAfterReady, _hdiagnosticRawReady,
    _hdiagnosticParsedReady, _hdiagnosticAcceptedReady, _hdiagnosticWrongReady,
    _hfinishReady, hreadyTail⟩
  rcases hreadyTail with ⟨_hvalidFinishedReady, _hclockFinishReady,
    _hconfigurationReady, hfailureReady, _hbankOutputReady, _hrecordOutputReady,
    _hupOutputReady, hnextCoordinatorReady, _hnextBankReady, _hsuccessorReady,
    _hsuccessorCoordinatorReady, _hsuccessorBankReady, hreadyFinalTail⟩
  rcases hreadyFinalTail with ⟨_hphaseFinishedReady, _hsigmaFinishedReady,
    _hcutoffFinishedReady, _hcursorFinishedReady, _hfreezeFinishedReady,
    _hfreezeBoundFinishedReady, _hassignmentFinishedReady, hreadyFinalRest⟩
  rcases hreadyFinalRest with ⟨_hbaseScoreReady, _hanchorReady, _hpayloadRateReady,
    hpendingUnivReady, _hpendingNonemptyReady, _hsigmaPositiveReady, _hsigmaBoundReady,
    _hsigmaCutoffReady, _hsigmaPayloadReady, _hcutoffPositiveReady, _hcutoffBoundReady,
    _hcutoffFreezeReady, _hcutoffCursorReady, _hcursorBoundReady, _hregistersReady,
    _hgammaReady, _hcutoffMassReady, _hcurrentJointReady, _hcurrentServiceReady,
    _hrawBoundsReady, _henabledExactReady, _henabledAtCutoffReady,
    _henabledOtherReady, _hrawOtherReady, _hrawFutureReady, _hbankBoundsReady,
    _hterminalCursorReady, hnextBoundaryReady⟩
  have hgeneratedWindowLength :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
          C_star C_h hcross start rfl count hspan).records).length = w := by
    simpa [w, epoch, actualEpoch] using
      congrArg (fun rs : List (Record p rate) =>
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow rs).length) hgeneratedRun
  have hreadyCut : cutReady = epoch.records[w]'hw := by
    simpa only [hgeneratedRun] using hindexReady
  have hsameCut : cutReady = cutoff.cut := by
    have hget := List.getElem?_eq_getElem (l := epoch.records) (i := w) hw
    exact hreadyCut.trans (Option.some.inj (hget.symm.trans cutoff.cutIndex))
  have hcoordinator :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          cutoff.payload cutoff.ledger cutoff.saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          rReady.payload finishedReady dispatchedReady.startResult.clock.lastProposal := by
    calc
      _ = cutoff.cut.output.next.coordinator := cutoff.outputCoordinator.symm
      _ = cutReady.output.next.coordinator := by
        exact congrArg (fun rec : Record p rate => rec.output.next.coordinator) hsameCut.symm
      _ = _ := hnextCoordinatorReady
  injection hcoordinator with hpayloadReady hledgerReady hsavedReady
  have hnextStateReady : cutReady.output.next = cutoff.cut.output.next :=
    congrArg (fun rec : Record p rate => rec.output.next) hsameCut
  have hreadyFailure : cutoff.cut.output.coordinator.failure = none := by
    rw [hsameCut] at hfailureReady
    exact hfailureReady
  have hreadyPending : cutoff.ledger.pending = Finset.univ := by
    simpa [hledgerReady] using hpendingUnivReady
  let initializer := ReferenceCollectionSegmentExtraction.cutoffInitializer
    (ReferenceActivePhysicalStep.liveInput cutReady.input rReady _qReady _baseReady).registers
    (ReferenceActivePhysicalStep.liveInput cutReady.input rReady _qReady _baseReady).ownedRegisters
    _baseReady cutReady.input.time
  have hchecked : initializer.checkedStart rate =
      .success (ReferenceActivePhysicalStep.sharedLedger _ledgerReady) := by
    rw [_hledgerReady]
    exact ReferenceCollectionSegmentExtraction.shared_initializer _ _
      (CoordinatorStartRoundCutoffDispatch.startCollectionChecked_success_of_domains
        _ _ _ _ _hdomainReady)
  have hcheckOutput : Nonempty (CutoffExecution cutReady rReady.payload finishedReady) :=
    ⟨{ live := rReady
       owned := _qReady
       base := _baseReady
       actualLive := _hreadyLive
       payloadIsLive := rfl
       initializer := initializer
       literalInitializer := rfl
       initial := ReferenceActivePhysicalStep.sharedLedger _ledgerReady
       checkedInitialization := hchecked
       recording := _recordingReady
       started := _ledgerStartedReady
       startSuccess := _hstartSuccessReady
       actualRecording := _hrecordOutputReady
       decoded := _decodedReady
       bank := _bankReady
       receiveRejected := _hreceiveReady
       finishSuccess := _hfinishReady }⟩
  have hcutoffExecution : Nonempty (CutoffExecution cutoff.cut cutoff.payload cutoff.ledger) := by
    simpa only [hsameCut, ← hpayloadReady, ← hledgerReady] using hcheckOutput
  have hcutTime : cutReady.input.time.val = start + w := by
    simpa only [hgeneratedRun] using _htimeReady
  have hprefixReady (ht : cutReady.input.time.val + 1 < p.T) :
      ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
        next.state = cutReady.output.next ∧ next.rows = source.1.2 ∧
        next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        next.rewards = rewards ∧ next.time.val = cutReady.input.time.val + 1 ∧
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          next rReady.payload finishedReady dispatchedReady.startResult.clock.lastProposal ∧
        ∀ hi : w + 1 < epoch.records.length, next = (epoch.records[w + 1]'hi).input := by
    rcases hnextBoundaryReady (by simpa only [hgeneratedWindowLength] using
      (show start + w + 1 < p.T by omega)) with ⟨hready, hretain⟩
    refine ⟨_, _hsuccessorReady, rfl, rfl, rfl, ?_, hready, ?_⟩
    · simpa only [ReferenceActivePhysicalHorizon.roundInputAt, hgeneratedWindowLength] using
        congrArg (fun t => t + 1) hcutTime.symm
    · intro hi
      have hmore : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
          C_star C_h hcross start rfl count hspan).records).length + 1 < count := by
        rw [hgeneratedWindowLength, ← hcount]
        exact hi
      simpa only [hgeneratedRun] using hretain hmore
  have hterminalReady (ht : cutReady.input.time.val + 1 = p.T) :
      ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
        cutReady.output.next rReady.payload finishedReady dispatchedReady.startResult.clock.lastProposal := by
    have hc : finishedReady.cursor = p.T + 1 := by
      have hcur := _hcursorFinishedReady
      rw [hgeneratedWindowLength] at hcur
      omega
    exact ⟨hnextCoordinatorReady, _hphaseFinishedReady, _hsigmaPositiveReady, _hsigmaBoundReady,
      _hsigmaCutoffReady, _hsigmaPayloadReady, _hcutoffPositiveReady, _hcutoffBoundReady,
      _hcutoffFreezeReady, _hfreezeBoundFinishedReady, _hfreezeFinishedReady, hc,
      _hcutoffCursorReady, _hcursorBoundReady, _hassignmentFinishedReady, _hbaseScoreReady,
      _hanchorReady, _hpayloadRateReady, _hpendingNonemptyReady, _hregistersReady, _hgammaReady,
      _hcutoffMassReady, _hcurrentJointReady, _hcurrentServiceReady, _hrawBoundsReady,
      _henabledExactReady, by simpa only [_hnextBankReady] using _hbankBoundsReady⟩
  have htail : Nonempty (Σ ls : List (Ledger rate),
      ActualTailOutput source rewards epoch.records window count start w
        cutoff.payload cutoff.saved cutoff.ledger ls) := by
    by_cases hwindowOne : window.length = 1
    · exact ⟨⟨[], .noNext hwindowOne⟩⟩
    · have hnextIndex : 1 < window.length := by omega
      let n1 : Fin window.length := ⟨1, hnextIndex⟩
      have hlookup1 := hwindowIndex 1 hnextIndex
      have hrecordIndex : w + 1 < epoch.records.length := by
        by_contra hnot
        have hnone := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hnot)
        rw [hnone] at hlookup1
        cases hlookup1
      have hrecordGet := List.getElem?_eq_getElem
        (l := epoch.records) (i := w + 1) hrecordIndex
      have hrecordEq : epoch.records[w + 1]'hrecordIndex = window[1]'hnextIndex :=
        Option.some.inj (hrecordGet.symm.trans hlookup1)
      have hnextTime : (window[1]'hnextIndex).input.time.val + 1 = start + w + 2 := by
        simpa [n1, epoch, w, window, actualEpoch] using (hwindowTime n1).2
      have hu : cutReady.input.time.val + 1 < p.T := by
        have ht := (window[1]'hnextIndex).input.time.isLt
        omega
      obtain ⟨next, _hs, _hr, _hi, _hy, _ht, hreadyNext, hretainNext⟩ := hprefixReady hu
      rw [hretainNext hrecordIndex, hrecordEq] at hreadyNext
      have hreadyOnWindow :
          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
            (window[1]'hnextIndex).input cutoff.payload cutoff.ledger cutoff.saved := by
        simpa only [← hpayloadReady, ← hledgerReady, ← hsavedReady] using hreadyNext
      let tailInput : ActualTailInput source rewards epoch.records window count start w
          cutoff.payload cutoff.saved 1 :=
        ⟨hnextIndex, cutoff.ledger,
          hreadyOnWindow,
          cutoff.cutoffRegisterBounds, cutoff.incrementGrowthBound⟩
      let tailWitness := Classical.choice
        (actualTailTrace_exists source rewards C_star C_h count hcross hspan hshortActual
          cutoff.payload cutoff.saved 1 tailInput)
      let tailLedgers := tailWitness.1
      let tail : ActualTailOutput source rewards epoch.records window count start w
          cutoff.payload cutoff.saved cutoff.ledger tailLedgers := .continuing tailInput rfl tailWitness.2
      exact ⟨⟨tailLedgers, tail⟩⟩
  obtain ⟨⟨tailLedgers, tail⟩⟩ := htail
  have htailBounds : tailLedgers.length + 1 ≤ window.length := by
    cases tail with
    | noNext hend => simp only [List.length_nil]; omega
    | continuing input hinit trace =>
        have hlen := (actualTailTrace_length_bounds trace).2
        omega
  refine ⟨{
    window := window
    windowIsActual := rfl
    windowNonempty := hwindowPos
    alignment := hwindowTime
    originalInputs := by
      intro n
      exact ReferenceActivePhysicalHorizon.run_record_inputs
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        _ (List.mem_of_getElem? (hwindowIndex n.val n.isLt))
    cutoff := cutoff
    payload := cutoff.payload
    saved := cutoff.saved
    initialLedger := cutoff.ledger
    payloadMatchesCutoff := rfl
    savedMatchesCutoff := rfl
    ledgerMatchesCutoff := rfl
    cutoffIsHead := hwindowHead
    cutoffFailureNone := hreadyFailure
    cutoffPendingUniv := hreadyPending
    cutoffPendingNonempty := by simpa [hledgerReady] using _hpendingNonemptyReady
    cutoffContext := by
      rw [hledgerReady, hpayloadReady]
      exact ⟨_hsigmaFinishedReady, _hsigmaReady, _hfreezeFinishedReady,
        _hassignmentFinishedReady, _hbaseScoreReady⟩
    cutoffExecution := hcutoffExecution
    cutoffValid := by simpa only [hledgerReady] using _hvalidFinishedReady
    cutoffPhase := by simpa only [hledgerReady] using _hphaseFinishedReady
    cutoffGamma := by intro a; simpa only [hledgerReady] using (_hgammaReady a).1
    cutoffNextReady := by
      simpa only [hsameCut, hnextStateReady, ← hpayloadReady, ← hledgerReady, ← hsavedReady] using hprefixReady
    cutoffTerminalReady := by
      simpa only [hsameCut, hnextStateReady, ← hpayloadReady, ← hledgerReady, ← hsavedReady] using hterminalReady
    tailLedgers := tailLedgers
    tail := tail
    ell := tailLedgers.length + 1
    ellEq := rfl
    positiveLength := by simp
    withinWindow := htailBounds
    ledgers := fun n => (cutoff.ledger :: tailLedgers)[n.val]'(by
      simpa using n.isLt)
    ledgers_are_outputs := by intro n; rfl
  }⟩

section OutputConsequences

variable {source : SourceInput p} {rewards : RewardTable p} {C_star C_h : ℝ} {count : ℕ}
  {hcross hspan hshort}
  (out : ActualInitializedStreamOutput (rate := rate) source rewards C_star C_h count hcross hspan hshort)

/-- Every noninitial selected output is the branch/service output at that
actual window record, with the preceding selected output as its input ledger. -/
theorem ActualInitializedStreamOutput.cell_at
    (n : Fin out.ell) (hpos : 0 < n.val) :
    ∃ j r incoming, ∃ cell : ContinuingStreamCell source rewards
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
      j count (startTime (rate := rate) source rewards C_star C_h) r out.payload incoming out.saved,
      j = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + n.val ∧
      out.window[n.val]? = some r ∧ cell.serviceLedger = out.ledgers n ∧
      incoming = out.ledgers ⟨n.val - 1, by omega⟩ := by
  have hn : n.val < out.tailLedgers.length + 1 := lt_of_lt_of_eq n.isLt out.ellEq
  obtain ⟨j, r, incoming, cell, hj, hr, hf, hfirst, hprev⟩ :=
    tail_cell_at out.tail (n.val - 1) (by omega)
  refine ⟨j, r, incoming, cell, by omega, ?_, ?_, ?_⟩
  · have he : n.val = 1 + (n.val - 1) := by omega
    rw [he]
    exact hr
  · rw [out.ledgers_are_outputs]
    simpa only [List.getElem_cons, Nat.ne_of_gt hpos, dite_false] using hf
  · rw [out.ledgers_are_outputs]
    by_cases hone : n.val = 1
    · simpa only [Fin.val_mk, hone, Nat.sub_self, List.getElem_cons_zero] using hfirst (by omega)
    · have hp : 0 < n.val - 1 := by omega
      simpa only [Fin.val_mk, List.getElem_cons, Nat.ne_of_gt hp, dite_false] using hprev hp

/-- No selected output before the last has emptied pending. -/
theorem ActualInitializedStreamOutput.pending_before_last
    (n : Fin out.ell) (hbefore : n.val + 1 < out.ell) :
    (out.ledgers n).pending.Nonempty := by
  rw [out.ledgers_are_outputs]
  by_cases hz : n.val = 0
  · simpa only [hz, List.getElem_cons_zero] using out.cutoffPendingNonempty
  · have hn : n.val < out.tailLedgers.length + 1 := lt_of_lt_of_eq n.isLt out.ellEq
    have hb : n.val + 1 < out.tailLedgers.length + 1 := lt_of_lt_of_eq hbefore out.ellEq
    have hp : 0 < n.val := by omega
    simpa only [List.getElem_cons, Nat.ne_of_gt hp, dite_false] using
      tail_pending_before_last out.tail (n.val - 1) (by omega) (by omega)

/-- Ending strictly before the finite window is exactly an empty boundary;
no delivery or eventual empty-pending claim is made. -/
theorem ActualInitializedStreamOutput.last_empty_of_not_exhausted
    (hshorter : out.ell < out.window.length) :
    (out.ledgers ⟨out.ell - 1, by have h := out.positiveLength; omega⟩).pending = ∅ := by
  rw [out.ledgers_are_outputs]
  have he := out.ellEq
  obtain ⟨k, hk, hlast, hempty⟩ := tail_last_empty out.tail (by omega)
  have hi : out.ell - 1 = k + 1 := by omega
  simp only [hi, List.getElem_cons_succ]
  exact hempty

/-- The original context is preserved through the same actual output ledgers. -/
theorem ActualInitializedStreamOutput.context
    (n : Fin out.ell) :
    (out.ledgers n).sigma = out.cutoff.ledger.sigma ∧
    (out.ledgers n).cutoff = out.cutoff.ledger.cutoff ∧
    (out.ledgers n).freezeAt = out.cutoff.ledger.freezeAt ∧
    (out.ledgers n).assignment = out.cutoff.ledger.assignment ∧
    (out.ledgers n).baseScore = out.cutoff.ledger.baseScore := by
  have hrec : ∀ k hk, (out.ledgers ⟨k, hk⟩).sigma = out.cutoff.ledger.sigma ∧
      (out.ledgers ⟨k, hk⟩).cutoff = out.cutoff.ledger.cutoff ∧
      (out.ledgers ⟨k, hk⟩).freezeAt = out.cutoff.ledger.freezeAt ∧
      (out.ledgers ⟨k, hk⟩).assignment = out.cutoff.ledger.assignment ∧
      (out.ledgers ⟨k, hk⟩).baseScore = out.cutoff.ledger.baseScore := by
    intro k
    induction k with
    | zero => intro hk; rw [out.ledgers_are_outputs]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨j, r, incoming, cell, _hj, _hr, hf, hi⟩ := out.cell_at ⟨k + 1, hk⟩ (by simp)
        have hc := cell.context
        rw [hf, hi] at hc
        obtain ⟨hs, hu, hg, ha, hb⟩ := ih (by omega)
        exact ⟨hc.1.trans hs, hc.2.1.trans hu, hc.2.2.1.trans hg,
          hc.2.2.2.1.trans ha, hc.2.2.2.2.trans hb⟩
  exact hrec n.val n.isLt

/-- Every selected ledger belongs to its actual no-failure FINISH, is valid
and ready, and has both stronger stored-service bounds on that same ledger. -/
theorem ActualInitializedStreamOutput.output_properties
    (n : Fin out.ell) :
    ∃ r, out.window[n.val]? = some r ∧ r.output.coordinator.failure = none ∧
      r.output.next.coordinator = .collection out.payload (out.ledgers n) out.saved ∧
      CoordinatorCollectionLedger.validLedgerCheck (out.ledgers n) = true ∧
      (out.ledgers n).phase = CoordinatorCollectionLedger.Phase.ready ∧
      (out.ledgers n).cursor = r.input.time.val + 2 ∧
      (∀ a, (out.ledgers n).gammaLoc a = 0) ∧
      (∀ a c, (out.ledgers n).cutoffRegisters a = some c →
        c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) ∧
      (∀ a, (out.ledgers n).increment a ≤
        4 * rate.n * (min (out.ledgers n).cursor (out.ledgers n).freezeAt - (out.ledgers n).cutoff)) := by
  by_cases hz : n.val = 0
  · have hf : out.ledgers n = out.cutoff.ledger := by
      rw [out.ledgers_are_outputs]
      simp only [hz, List.getElem_cons_zero]
    refine ⟨out.cutoff.cut, ?_, out.cutoffFailureNone, ?_⟩
    · rw [hz]
      exact (List.getElem?_eq_getElem (by have h := out.windowNonempty; omega)).trans
        (congrArg some out.cutoffIsHead)
    · rw [hf, out.payloadMatchesCutoff, out.savedMatchesCutoff]
      exact ⟨out.cutoff.outputCoordinator, out.cutoffValid, out.cutoffPhase,
        by rw [out.cutoff.cutTime, out.cutoff.ledgerCursor], out.cutoffGamma,
        out.cutoff.cutoffRegisterBounds, out.cutoff.incrementGrowthBound⟩
  · obtain ⟨j, r, incoming, cell, _hj, hr, hf, _hi⟩ := out.cell_at n (by omega)
    obtain ⟨hfail, hvalid, hphase, hcursor, hgamma, _hregisters⟩ := cell.output_properties
    refine ⟨r, hr, hfail, ?_⟩
    rw [← hf]
    exact ⟨cell.serviceNextCoordinator, hvalid, hphase, hcursor,
      fun a => congrFun hgamma a, cell.cutoffLastServiceBounds, cell.incrementGrowthBound⟩


/-- Apply at the final selected index for the required empty, original-prefix,
or terminal boundary, with Cut/Inc on the same ledger from `output_properties`. -/
theorem ActualInitializedStreamOutput.boundary_at (n : Fin out.ell) :
    ∃ r, out.window[n.val]? = some r ∧ Boundary source rewards
      (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) source rewards C_star C_h hcross count hspan).records).length + n.val)
      r out.payload (out.ledgers n) out.saved := by
  by_cases hz : n.val = 0
  · have hf : out.ledgers n = out.cutoff.ledger := by
      rw [out.ledgers_are_outputs]
      simp only [hz, List.getElem_cons_zero]
    refine ⟨out.cutoff.cut, ?_, ?_⟩
    · rw [hz]
      exact (List.getElem?_eq_getElem (by have h := out.windowNonempty; omega)).trans
        (congrArg some out.cutoffIsHead)
    · simp only [hf, hz, Nat.add_zero, out.payloadMatchesCutoff, out.savedMatchesCutoff]
      refine ⟨?_, fun _ => out.cutoffNextReady, fun _ => out.cutoffTerminalReady⟩
      intro hempty
      exact ((Finset.nonempty_iff_ne_empty.mp out.cutoffPendingNonempty) hempty).elim
  · obtain ⟨j, r, incoming, cell, hj, hr, hf, _hi⟩ := out.cell_at n (by omega)
    refine ⟨r, hr, ?_⟩
    rw [← hj, ← hf]
    exact ⟨cell_all_known_when_empty cell, cell_next_ready cell, cell_terminal_ready cell⟩


end OutputConsequences

end Bandits.Support.ReferenceFirstCollectionReadyStream

end
