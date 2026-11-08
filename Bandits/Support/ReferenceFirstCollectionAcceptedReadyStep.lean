/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionReadyStep

import Lean.Elab.Tactic.Omega

/-!
# One actual accepted first-collection FINISH step

This module takes the accepted-UP branch at an arbitrary record in the actual
first collection window. It obtains dispatch, recorder, and checked START data
from the admitted ready-step module, derives both offered-message budgets at
that same record, and applies the accepted FINISH query. Its only induction
input is the existing literal ready predicate at the current actual input.
The numeric outputs serve that ready predicate; stronger cutoff last-service
and increment-growth invariants remain with their separate owners.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-70`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionAcceptedReadyStep

abbrev Parameters := ReferenceFirstCollectionReadyStep.Parameters
abbrev RateInput := ReferenceFirstCollectionReadyStep.RateInput
abbrev SourceInput := ReferenceFirstCollectionReadyStep.SourceInput
abbrev RewardTable := ReferenceFirstCollectionReadyStep.RewardTable
abbrev Record := ReferenceFirstCollectionReadyStep.Record
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceFirstCollectionReadyStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceFirstCollectionReadyStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem round_input_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
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

private theorem register_domains_of_valid
    (l : Ledger rate) (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true) :
    (∀ b q, l.currentRegisters b = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p) ∧
    (∀ b c, l.cutoffRegisters b = some c →
      c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p) ∧
    (∀ k, l.baseScore k ≤ p.T * D p) ∧
    (∀ b, l.increment b ≤ p.T * D p) := by
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hvalid
  have hregisters := hvalid.1.2
  simp only [CoordinatorCollectionLedger.registerDomainsCheck, Bool.and_eq_true] at hregisters
  rcases hregisters with ⟨⟨⟨⟨hcurrent, hcutoff⟩, hbase⟩, hincrement⟩, _hgamma⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b q hq
    have hcheck := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hcurrent b
    simpa only [hq, Bool.and_eq_true, decide_eq_true_eq] using hcheck
  · intro b c hc
    have hcheck := (ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hcutoff b
    simp only [hc, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩
  · intro k
    exact of_decide_eq_true
      ((ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hbase k)
  · intro b
    exact of_decide_eq_true
      ((ReferenceFirstCutoffRecordedService.allFin_eq_true_iff _).mp hincrement b)

/-- Concrete values and proof fields produced by the actual accepted receiver,
ledger FINISH, and clock FINISH for one accepted effective parse. This is an
output witness over the existing ledger and round input types, not a new
protocol state representation. -/
structure AcceptedFinishOutput
    (source : SourceInput p) (rewards : RewardTable p)
    (epochRecords : List (Record p rate)) (j count start : ℕ)
    (r : Record p rate) (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (recording : CoordinatorRecordingOperation.Output p)
    (started : Ledger rate)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) where
  jointBudget : M.val.S + M.val.q ≤
    (ledger.cutoff - ledger.sigma) * D p
  scoreBudget : M.val.S ≤ (4 * rate.n) * (ledger.cutoff - ledger.sigma)
  senderWasPending :
    ReferenceActivePhysicalStep.upSenderIndex r.input ∈ ledger.pending
  recordIsStep : r.output = ReferenceActivePhysicalStep.step r.input
  effectiveParse :
    ReferenceCollectionSegmentExtraction.effectiveParse r.input started = some M
  acceptedCheck :
    CoordinatorCollectionLedger.acceptUpCheck started
      (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true
  startedAssignment : started.assignment = ledger.assignment
  knownQueueService : ∀ b q, ledger.currentRegisters b = some q →
    let row := CoordinatorCollectionLedger.localQueueRecord ledger r.input.time
      (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic r) b
    let next := QueueReplay.transition (4 * rate.n) (0, q.queue) row
    started.currentRegisters b = some ⟨next.2, next.1⟩ ∧ started.gammaLoc b = next.1
  knownEnabledZeroService : ∀ b q, ledger.currentRegisters b = some q →
    ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time = true →
    CoordinatorCollectionLedger.sourceRound r.input.time < ledger.freezeAt →
    CoordinatorCollectionLedger.localArrival
      (ReferenceCollectionRawBufferHistory.rawDiagnostic r) b = 0 →
    started.currentRegisters b =
      some ⟨q.queue - min (4 * rate.n) q.queue, min (4 * rate.n) q.queue⟩ ∧
    started.gammaLoc b = min (4 * rate.n) q.queue
  knownDisabledService : ∀ b q, ledger.currentRegisters b = some q →
    (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time = false ∨
      ledger.freezeAt ≤ CoordinatorCollectionLedger.sourceRound r.input.time) →
    started.currentRegisters b = some ⟨q.queue, 0⟩ ∧ started.gammaLoc b = 0
  past : List (Bool × ℕ)
  currentRecord : Bool × ℕ
  currentRecordIsActual : currentRecord =
    (decide (CoordinatorCollectionLedger.sourceRound r.input.time < ledger.freezeAt),
      CoordinatorCollectionLedger.bufferedArrival started
        (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input))
        r.input.time)
  replayRecordsLength : (past ++ [currentRecord]).length =
    (r.input.time.val + 1 - ledger.cutoff) + 1
  replayArrivalsBound : ∀ row ∈ past ++ [currentRecord], row.2 ≤ D p
  replayCalendarBits : ∀ k : Fin (past ++ [currentRecord]).length,
    ((past ++ [currentRecord])[k.val]'(by simpa using k.isLt)).1 =
      decide (ledger.cutoff + k.val < ledger.freezeAt)
  replayPrefixBounds : ∀ h, h ≤ (past ++ [currentRecord]).length →
    let R := QueueReplay.replay (4 * rate.n) (0, M.val.q)
      ((past ++ [currentRecord]).take h)
    M.val.S + R.1 + R.2 ≤ (ledger.cutoff - ledger.sigma + h) * D p ∧
    R.1 ≤ p.T * D p ∧ R.2 ≤ p.T * D p
  replayDomains :
    CoordinatorCollectionLedger.replayOutputDomainsCheck (p := p) (4 * rate.n)
      M.val.q (past ++ [currentRecord]) = true
  inclusiveReplayScore :
    let R := QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])
    M.val.S + R.1 ≤
      (4 * rate.n) * (min (r.input.time.val + 2) ledger.freezeAt - ledger.sigma)
  inclusiveReplayTransition :
    let prior := QueueReplay.replay (4 * rate.n) (0, M.val.q) past
    QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
      QueueReplay.transition (4 * rate.n) prior currentRecord
  enabledZeroArrivalReplay : currentRecord = (true, 0) →
    let prior := QueueReplay.replay (4 * rate.n) (0, M.val.q) past
    QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
      (prior.1 + min (4 * rate.n) prior.2, prior.2 - min (4 * rate.n) prior.2)
  disabledReplayPreserves : currentRecord.1 = false →
    QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
      QueueReplay.replay (4 * rate.n) (0, M.val.q) past
  frozenReplayPreserves : ledger.freezeAt ≤ CoordinatorCollectionLedger.sourceRound r.input.time →
    QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
      QueueReplay.replay (4 * rate.n) (0, M.val.q) past
  decoded : Ledger rate
  bank : CoordinatorUpReception.UpDecoderBank p
  receiveInputDomain : CoordinatorUpReception.receptionInputDomain
    (ReferenceUpReception.receptionInputAtRow rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time)
  receiveInputCheck : CoordinatorUpReception.receptionInputCheck
    (ReferenceUpReception.receptionInputAtRow rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time) = true
  receiveInputBank :
    (ReferenceUpReception.receptionInputAtRow rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time).upDecoderBank =
      r.input.state.upDecoderBank
  decodeSuccess : CoordinatorCollectionLedger.decodeUp started
    (ReferenceActivePhysicalStep.upSenderIndex r.input) (some M) = .success decoded
  receiveSuccess :
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare r.input) started).result =
        .success (decoded, bank)
  bankAfter : bank = CoordinatorUpReception.decoderBankAfter
    (ReferenceUpReception.receptionInputAtRow rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time)
  rawMatchesExpected :
    (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time)).2 =
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input)
  parserReturnsMessage :
    CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate r.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare r.input) started) r.input.time)).2 = some M
  decodedValid : CoordinatorCollectionLedger.validLedgerCheck decoded = true
  decodedPhase : decoded.phase = CoordinatorCollectionLedger.Phase.decoded
  decodedPending : decoded.pending = ledger.pending.erase
    (ReferenceActivePhysicalStep.upSenderIndex r.input)
  decodedCursor : decoded.cursor = r.input.time.val + 1
  decodedContext : decoded.sigma = ledger.sigma ∧ decoded.cutoff = ledger.cutoff ∧
    decoded.freezeAt = ledger.freezeAt ∧ decoded.assignment = ledger.assignment ∧
    decoded.baseScore = ledger.baseScore
  decodedSelectedRegisters :
    let a := started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)
    let R := QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])
    decoded.cutoffRegisters a = some ⟨M.val.S, M.val.q, M.val.delta⟩ ∧
    decoded.currentRegisters a = some ⟨R.2,
      R.1 - (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((past ++ [currentRecord]).take ((past ++ [currentRecord]).length - 1))).1⟩ ∧
    decoded.increment a = R.1 ∧ decoded.gammaLoc a = 0
  decodedOtherGamma : ∀ b, b ≠
      started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input) →
        decoded.gammaLoc b = started.gammaLoc b
  decodedSelectedRawCleared :
    decoded.rawBuffer
      (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) =
        fun _ => none
  decoderBankWellFormed : CoordinatorUpReception.decoderBankWellFormed p bank
  decoderSenderQuota :
    (r.input.state.upDecoderBank (ReferenceActivePhysicalStep.upSenderIndex r.input)).pending.length + 1 =
      AffineBatchDecoder.quota p
  decoderSenderPendingEmpty :
    (bank (ReferenceActivePhysicalStep.upSenderIndex r.input)).pending = []
  decoderSenderCompletedBatch : ∃ batch,
    batch ∈ (bank (ReferenceActivePhysicalStep.upSenderIndex r.input)).completed ∧
      batch.length = AffineBatchDecoder.quota p
  decoderOtherBanks : ∀ k, k ≠ ReferenceActivePhysicalStep.upSenderIndex r.input →
    bank k = r.input.state.upDecoderBank k
  finished : Ledger rate
  finishSuccess : CoordinatorCollectionLedger.finishRound decoded = .success finished
  finishCandidate : finished = CoordinatorCollectionLedger.finishRoundCandidate decoded
  finishedValid : CoordinatorCollectionLedger.validLedgerCheck finished = true
  finishedIncrement : finished.increment = fun b => decoded.increment b + decoded.gammaLoc b
  finishedGammaZero : finished.gammaLoc = fun _ => 0
  finishedCursor : finished.cursor = r.input.time.val + 2
  finishedReady : finished.phase = CoordinatorCollectionLedger.Phase.ready
  finishedPending : finished.pending = ledger.pending.erase
    (ReferenceActivePhysicalStep.upSenderIndex r.input)
  finishedContext : finished.sigma = ledger.sigma ∧ finished.cutoff = ledger.cutoff ∧
    finished.freezeAt = ledger.freezeAt ∧ finished.assignment = ledger.assignment ∧
    finished.baseScore = ledger.baseScore
  finishedRegistersPreserved :
    finished.cutoffRegisters = decoded.cutoffRegisters ∧
    finished.currentRegisters = decoded.currentRegisters ∧
    finished.rawBuffer = decoded.rawBuffer ∧ finished.enabledHistory = decoded.enabledHistory
  finishedSelectedIncrement :
    finished.increment
      (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) =
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])).1
  finishedSelectedGammaZero : finished.gammaLoc
    (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) = 0
  finishedOtherIncrement : ∀ b, b ≠
      started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input) →
        finished.increment b = started.increment b + started.gammaLoc b
  finishedAllGammaZero : ∀ b, finished.gammaLoc b = 0
  currentRegisterDomains : ∀ b q, finished.currentRegisters b = some q →
    q.queue ≤ p.T * D p ∧ q.lastService ≤ D p
  cutoffRegisterDomains : ∀ b c, finished.cutoffRegisters b = some c →
    c.score ≤ p.T * D p ∧ c.queue ≤ p.T * D p ∧ c.lastService ≤ D p
  baseScoreDomain : ∀ k, finished.baseScore k ≤ p.T * D p
  incrementDomain : ∀ b, finished.increment b ≤ p.T * D p
  registerPendingEquivalence : ∀ b,
    (finished.currentRegisters b = none ↔ CoordinatorCollectionLedger.armPending finished b) ∧
    (finished.cutoffRegisters b = none ↔ CoordinatorCollectionLedger.armPending finished b)
  pendingArmIncrementZero : ∀ b, CoordinatorCollectionLedger.armPending finished b →
    finished.increment b = 0 ∧ finished.gammaLoc b = 0
  cutoffMassBounds : ∀ b c, finished.cutoffRegisters b = some c →
    c.score + c.queue ≤ (ledger.cutoff - ledger.sigma) * D p
  currentMassBounds : ∀ b c q, finished.cutoffRegisters b = some c →
    finished.currentRegisters b = some q →
    c.score + finished.increment b + q.queue ≤ (r.input.time.val + 2 - ledger.sigma) * D p
  currentServiceSpanBound : ∀ b c q, finished.cutoffRegisters b = some c →
    finished.currentRegisters b = some q →
    c.score + finished.increment b ≤
      (4 * rate.n) * (min (r.input.time.val + 2) ledger.freezeAt - ledger.sigma)
  rawBufferBounds : ∀ b t amount, finished.rawBuffer b t = some amount →
    0 < amount ∧ amount ≤ D p ∧ ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound t ∧
    CoordinatorCollectionLedger.sourceRound t < min finished.cursor finished.freezeAt ∧
    CoordinatorCollectionLedger.armPending finished b
  enabledHistoryExact : ∀ t, finished.enabledHistory t =
    if ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound t ∧
        CoordinatorCollectionLedger.sourceRound t < finished.cursor then
      some (decide (CoordinatorCollectionLedger.sourceRound t < finished.freezeAt))
    else none
  bankOutsidePendingEmpty : ∀ k, k ∉ finished.pending → (bank k).pending = []
  clockFinishSuccess :
    let clockFinished : CoordinatorPhaseClock.FinishRoundResult p :=
      { clock := choice.started.clock
        pending := finished.pending
        ledgerCommand := some (.accumulateLocalServiceAt r.input.time) }
    CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time
      choice.started.clock finished.pending r.input.row = .ok clockFinished
  clockFinishPreservesContext :
    let clockFinished : CoordinatorPhaseClock.FinishRoundResult p :=
      { clock := choice.started.clock
        pending := finished.pending
        ledgerCommand := some (.accumulateLocalServiceAt r.input.time) }
    clockFinished.clock = choice.started.clock ∧
    clockFinished.pending = finished.pending ∧
    clockFinished.ledgerCommand = some (.accumulateLocalServiceAt r.input.time) ∧
    clockFinished.clock.lastProposal = saved
  lastProposal : Option (Fin p.T × Bool)
  lastProposalIsSaved : lastProposal = saved
  actualCollectionFinish :
    ReferenceActivePhysicalStep.collectionFinish (x := r.input) payload
      choice.started recording (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) started) =
    { configuration := .collection payload finished lastProposal
      upDecoderBank := bank
      failure := none
      recording := some recording
      up := (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) started).diagnostic }
  actualCoordinatorFailureNone : r.output.coordinator.failure = none
  actualCoordinatorRecording : r.output.coordinator.recording = some recording
  actualCoordinatorUp : r.output.coordinator.up =
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare r.input) started).diagnostic
  actualNextCoordinator : r.output.next.coordinator = .collection payload finished lastProposal
  actualNextBank : r.output.next.upDecoderBank = bank
  actualNextActivations : r.output.next.activations = r.input.state.activations
  acceptedLabel : ReferenceCollectionPhaseHistory.acceptedLabel r.input =
    some (ReferenceActivePhysicalStep.upSenderIndex r.input)
  eraseEventExact : finished.pending =
    ReferenceCollectionPhaseHistory.eraseEvent ledger.pending
      (ReferenceCollectionPhaseHistory.acceptedLabel r.input)
  nextReadyOnOriginalPrefix : finished.pending.Nonempty → r.input.time.val + 1 < p.T →
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = r.output.next ∧ next.rows = source.1.2 ∧
      next.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      next.rewards = rewards ∧ next.time.val = r.input.time.val + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next payload finished lastProposal ∧
      ∀ hnext : j + 1 < epochRecords.length,
        next = (epochRecords[j + 1]'hnext).input
  terminalReadyBoundary : finished.pending.Nonempty → r.input.time.val + 1 = p.T →
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      r.output.next payload finished lastProposal
  allKnownWhenPendingEmpty : finished.pending = ∅ →
    ∀ b, (∃ q, finished.currentRegisters b = some q) ∧
      (∃ c, finished.cutoffRegisters b = some c)

/-! The telescope below is deliberately the actual run, complete private
source, whole reward table, and unrestricted common constants. -/

/-- Preserve the existing ready domain along one actual accepted-UP record.
The dispatch, recorder, and START witnesses are produced at the arbitrary
original window index. Each effective parsed message passing the local UP
check receives both budgets from the actual parsed-message producer and then
the concrete accepted FINISH output. The continuing alternative uses the
same original prefix, whole rows, selected private index, and whole rewards.

This is the accepted one-record input for the subsequent initialized finite
first-collection ready/numerical stream construction. The current ready
domain and the two explicit accepted-message tests delimit this internal
result. Source ranges are listed in the module docstring. -/
theorem actual_first_collection_accepted_finish_ready_step
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (payload : ReferenceFirstCollectionReadyStep.Payload rate)
    (ledger : ReferenceFirstCollectionReadyStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved) :
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    let r := window[n.val]
    let x := r.input
    let j := w + n.val
    r.output = ReferenceActivePhysicalStep.step x ∧
    x.time.val + 1 =
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        w + 1 + n.val ∧
    ∃ (choice : ReferenceCollectionSegmentExtraction.Choice rate)
      (recording : CoordinatorRecordingOperation.Output p) (started : Ledger rate),
      ReferenceCollectionSegmentExtraction.choice x = some choice ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) choice.payload choice.started choice.weights) =
        some recording ∧
      choice.payload = payload ∧ choice.preLedger = ledger ∧
      choice.initializer = none ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      started = CoordinatorCollectionLedger.startRoundCandidate choice.preLedger x.time
        (ReferenceActivePhysicalStep.collectionEnabled choice.preLedger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r) ∧
      (∀ a, (started.currentRegisters a = none ↔
          CoordinatorCollectionLedger.armPending started a) ∧
        (started.cutoffRegisters a = none ↔
          CoordinatorCollectionLedger.armPending started a)) ∧
      ∀ M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val),
        ReferenceCollectionSegmentExtraction.effectiveParse x started = some M →
        CoordinatorCollectionLedger.acceptUpCheck started
          (ReferenceActivePhysicalStep.upSenderIndex x) M = true →
        Nonempty (AcceptedFinishOutput source rewards epoch.records j count
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          r payload ledger saved choice recording started M) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let r := window[n.val]
  let x := r.input
  let j := w + n.val
  let i := ReferenceActivePhysicalStep.upSenderIndex x

  have hReadyStep :=
    ReferenceFirstCollectionReadyStep.actual_collection_window_ready_start
      rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
  rcases hReadyStep with
    ⟨hstep, htime, cutoff, hcutoff, core, snap, hb, hs, hcoord,
      choice, recording, started, hchoice, hrecording, hchoicePayload,
      hchoiceLedger, hchoiceStarted, hchoiceInitializer, hstart,
      hcandidate, hregisters⟩
  have hstepActual : r.output = ReferenceActivePhysicalStep.step x := by
    simpa [r, x, window, epoch] using hstep
  have htimeActual : x.time.val + 1 = start + w + 1 + n.val := by
    simpa [x, window, epoch, w, start] using htime

  have hFinishDomains :=
    ReferenceContinuingCollectionAcceptedFinishDomains.continuing_collection_accepted_finish_domains
      x payload ledger saved hReady
  rcases hFinishDomains with
    ⟨cutoffF, hcutoffF, coreF, snapF, hbF, hsF, hcoordF, harmF,
      hlocalF, hrecordInputsF, recordingF, l1, hrecordF, hstartF,
      hl1Candidate, hvalidF, hphaseF, hcursorF, hsigmaF, hcutF,
      hfreezeF, hpendingF, hassignmentF, hbaseF, hcutRegistersF,
      hincrementF, hregistersF, hobserveF, hrecordingObserveF,
      hdiagnosticF, hdomainF, hinputCheckF, hbankInputF, hmessages⟩

  let inputF := ReferenceActivePhysicalStep.collectionInput x payload ledger
    (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoffF) cutoffF
  let weightsF := CoordinatorCollectionInteractive.PreObservationInputs.weights inputF
    snapF.inputsValid.ledger_valid snapF.inputsValid.assignment_eq
  let choiceF : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, ledger, snapF.clockStarted, weightsF, none⟩
  have hchoiceF : ReferenceCollectionSegmentExtraction.choice x = some choiceF := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [hcoordF]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection, choiceF, weightsF, inputF]
  have hchoiceEq : choice = choiceF := Option.some.inj (hchoice.symm.trans hchoiceF)
  have hrecordingAtFInput :
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) payload snapF.clockStarted weightsF) =
        some recording := by
    have hinputEq := congrArg
      (fun c : ReferenceCollectionSegmentExtraction.Choice rate =>
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights)) hchoiceEq
    calc
      CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) payload snapF.clockStarted weightsF) =
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput
              (ReferenceActivePhysicalStep.prepare x) choice.payload choice.started choice.weights) := by
        simpa [choiceF, weightsF, inputF] using hinputEq.symm
      _ = some recording := hrecording
  have hrecordingEq : recording = recordingF :=
    Option.some.inj (hrecordingAtFInput.symm.trans hrecordF)
  have hstartAtRInput :
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success l1 := by
    simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
      ← hrecordingEq] using hstartF
  rw [hstart] at hstartAtRInput
  have hstartedEq : l1 = started :=
    CoordinatorCollectionLedger.Checked.success.inj hstartAtRInput.symm
  have hstartedAssignment : started.assignment = ledger.assignment := by
    simpa [hstartedEq] using hassignmentF
  refine ⟨hstepActual, htimeActual, choice, recording, started, hchoice, hrecording,
    hchoicePayload, hchoiceLedger, hchoiceInitializer, hstart, hcandidate,
    hregisters, ?_⟩
  intro M hparse haccept

  let lplus := CoordinatorCollectionLedger.startRoundCandidate choice.preLedger x.time
    (ReferenceActivePhysicalStep.collectionEnabled choice.preLedger x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic r)
  have hcandidateEq : started = lplus := by simpa [lplus] using hcandidate
  have hparseCandidate :
      ReferenceCollectionSegmentExtraction.effectiveParse x lplus = some M := by
    rw [← hcandidateEq]
    exact hparse
  have hacceptCandidate : CoordinatorCollectionLedger.acceptUpCheck lplus i M = true := by
    rw [← hcandidateEq]
    exact haccept
  have hBudgetProducer :=
    ReferenceFirstCollectionParsedUpBudgets.actual_first_collection_parsed_up_budget_calendar_replay_join
      rate source rewards C_star C_h count hcross hspan hshort
  have hBudgetJoin := hBudgetProducer n choice hchoice M hparseCandidate hacceptCandidate
  simp only [Fin.getElem_fin] at hBudgetJoin
  rcases hBudgetJoin with
    ⟨P0, birth, state, memory, offered, downIndex, message,
      _hinitializer, _hledgerSigma, _hledgerCutoff, _hledgerAssignment,
      _hvalidLedger, hSenderPending, _hcurrentUnknown, _hcutoffUnknown,
      _hlplusSigma, _hlplusCutoff, _hP0Sigma, _hP0Queues, _hbirthMem,
      _hbirth, _hbirthTime, _hconfiguration, _hcheckedOffer, _hOfferEq,
      _hword, _hlastDown, _hjBound, _hjRange, _hretained, _hmessageP0,
      _hmessageSigma, _hmessageQ, _hmessageMSigma, _hMScore, _hMQueue,
      _hMDelta, _hfirstReply, hbudgetJoint, hbudgetScore, _hbudgetDelta,
      _hbudgetCap, _hcalendarEnd, _hindices, _hindexLength, _hreplayPrior,
      _hrowsBound, _hlonger, _hlongerLength, _hreplayCandidate,
      _hcandidateRowsBound⟩
  have hcutoffPlus : lplus.cutoff = ledger.cutoff := by
    simp [lplus, hchoiceLedger, CoordinatorCollectionLedger.startRoundCandidate]
  have hsigmaPlus : lplus.sigma = ledger.sigma := by
    simp [lplus, hchoiceLedger, CoordinatorCollectionLedger.startRoundCandidate]
  have hBudgetJoint : M.val.S + M.val.q ≤ (ledger.cutoff - ledger.sigma) * D p := by
    change M.val.S + M.val.q ≤ (lplus.cutoff - lplus.sigma) * D p at hbudgetJoint
    rw [hcutoffPlus, hsigmaPlus] at hbudgetJoint
    exact hbudgetJoint
  have hBudgetScore : M.val.S ≤ (4 * rate.n) * (ledger.cutoff - ledger.sigma) := by
    change M.val.S ≤ (4 * rate.n) * (lplus.cutoff - lplus.sigma) at hbudgetScore
    rw [hcutoffPlus, hsigmaPlus] at hbudgetScore
    exact hbudgetScore
  have hSenderPendingLedger : i ∈ ledger.pending := by
    simpa [hchoiceLedger] using hSenderPending

  have hparseF : ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M := by
    simpa [hstartedEq] using hparse
  have hacceptF : CoordinatorCollectionLedger.acceptUpCheck l1 i M = true := by
    simpa [hstartedEq] using haccept
  have hmessageResult := hmessages M hparseF hacceptF hBudgetJoint hBudgetScore
  rcases hmessageResult with
    ⟨past, currentRecord, hcurrentNone, hcutoffNone, hPastSome,
      hCurrentSome, hpastMap, hcurrentEq, hrecordsLength, harrivals,
      hfourN, hprefix, hbits, hreplayCheck, hendpointScore, decoded,
      bank, hacceptedCandidate, hdecodedValid, hdecoded, hreceiveResult,
      hbankAfter, hrawEq, hparseActual, _hdiagnosticM, hphaseAfter,
      hpendingAfter, hσAfter, hcutAfter, hcursorAfter, hfreezeAfter,
      hassignmentAfter, hbaseAfter, hcutRecovered, hcurrentRecovered,
      hincrementRecovered, hgammaRecovered, hgammaFrame, hrawCleared,
      hframe, hregistersAfter, hzeroPendingAfter, hcutoffMassAfter,
      hknownMassAfter, hrawSupportAfter, hhistoryAfter, hbankWellFormed,
      hquota, hselectedClear, hselectedBatch, _htransitionSelected,
      hbankUnselected, hbankEmptyOutside, finished, hfinish,
      hfinishedCandidate, hfinishedValid, hfinishedIncrement,
      hfinishedGamma, hfinishedCursor, hfinishedPhase, hfinishedPending,
      hfinishedSigma, hfinishedCutoff, hfinishedFreeze, hfinishedAssignment,
      hfinishedBase, hfinishedCutoffRegisters, hfinishedCurrentRegisters,
      hfinishedRaw, hfinishedHistory, hfinishedAtArm, hfinishedOtherIncrement,
      hfinishedGammaZero, hfinishedRegisters,
      hfinishedCutoffMass, hfinishedMass, hfinishedRawSupport,
      hfinishedHistory2, hclockFinish, hclockClock,
      hclockPending, hclockCommand, hlastProposal,
      hcollectionFinish, hobserveCoordinator, hstepCoordinator,
      hstepNextCoordinator, hstepNextBank, hstepNextActivations,
      _hfollowerFrame, _hownEntries, htail⟩
  rcases htail with ⟨hnextBranch, hallKnown⟩
  have hchoiceStarted : choice.started = snapF.clockStarted := by
    have h := congrArg
      (fun c : ReferenceCollectionSegmentExtraction.Choice rate => c.started) hchoiceEq
    simpa [choiceF] using h
  let actualLastProposal := snapF.clockStarted.clock.lastProposal

  have hFinishedPending : finished.pending = ledger.pending.erase i := by
    simpa [hstartedEq] using hfinishedPending
  have hreceiveStarted :
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, bank) := by
    simpa [hstartedEq] using hreceiveResult
  have hAcceptedLabel : ReferenceCollectionPhaseHistory.acceptedLabel x = some i := by
    let tail : ReferenceCollectionPhaseHistory.Tail x :=
      ⟨payload, ledger, snapF.clockStarted, weightsF⟩
    have htail : ReferenceCollectionPhaseHistory.executedTail x = some tail := by
      simp [ReferenceCollectionPhaseHistory.executedTail, hcoordF,
        ReferenceActivePhysicalStep.DispatchCut.selection, tail, inputF, weightsF]
    have htailReception : tail.reception =
        some (started, ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started) := by
      simp [ReferenceCollectionPhaseHistory.Tail.reception, tail,
        inputF, weightsF,
        hrecordF, hstartF, hstartedEq]
    unfold ReferenceCollectionPhaseHistory.acceptedLabel
    rw [htail]
    simp only [Option.bind_some]
    rw [htailReception]
    simp [hreceiveStarted, i]
  have hEraseEventExact : finished.pending =
      ReferenceCollectionPhaseHistory.eraseEvent ledger.pending
        (ReferenceCollectionPhaseHistory.acceptedLabel x) := by
    rw [hFinishedPending, hAcceptedLabel]
    rfl

  have hactualCoordinatorEq : r.output.coordinator =
      { configuration := .collection payload finished actualLastProposal
        upDecoderBank := bank
        failure := none
        recording := some recording
        up := (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started).diagnostic } := by
    calc
      r.output.coordinator = (ReferenceActivePhysicalStep.step x).coordinator := by
        rw [hstepActual]
      _ = ReferenceActivePhysicalStep.collectionFinish (x := x) payload
          choice.started recording (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started) := by
          simpa [hchoiceStarted, hrecordingEq, hstartedEq] using hstepCoordinator
      _ = _ := by
        simpa [hchoiceStarted, hstartedEq, hrecordingEq, actualLastProposal] using
          hcollectionFinish

  have hlookup :=
    ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
      rate source rewards C_star C_h count hcross hspan hshort n
  have hrecordLookup : epoch.records[j]? = some r := by
    simpa [epoch, w, window, r, j] using hlookup.1
  have hindex : j < epoch.records.length :=
    (List.getElem?_eq_some_iff.mp hrecordLookup).1
  have hrecord : epoch.records[j]'hindex = r := by
    exact Option.some.inj ((List.getElem?_eq_getElem hindex).symm.trans hrecordLookup)
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hactive :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have hrunInputs := ReferenceActivePhysicalHorizon.run_record_inputs initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hactive
  have hrMemEpoch : r ∈ epoch.records := by
    rw [← hrecord]
    exact List.getElem_mem hindex
  have hrMem : r ∈
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hactive).records := by
    simpa [epoch, initial, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      hrMemEpoch
  have hinputData : r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.rewards = rewards := by
    exact hrunInputs r hrMem

  have hCurrentRecordActual : currentRecord =
      (decide (CoordinatorCollectionLedger.sourceRound x.time < ledger.freezeAt),
        CoordinatorCollectionLedger.bufferedArrival started (started.assignment.arm i) x.time) := by
    refine hcurrentEq.trans ?_
    apply Prod.ext
    · exact decide_eq_decide.mpr Iff.rfl
    · change CoordinatorCollectionLedger.bufferedArrival l1 (l1.assignment.arm i) x.time = _
      rw [hstartedEq]
  have hReplayTransition :
      QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
        QueueReplay.transition (4 * rate.n)
          (QueueReplay.replay (4 * rate.n) (0, M.val.q) past) currentRecord := by
    rw [QueueReplay.replay_append]
    rfl
  have hDisabledReplay (hdisabled : currentRecord.1 = false) :
      QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord]) =
        QueueReplay.replay (4 * rate.n) (0, M.val.q) past := by
    rw [hReplayTransition]
    simp only [QueueReplay.transition, hdisabled, Bool.false_eq_true, ite_false]
  obtain ⟨hCurrentDomains, hCutoffDomains, hBaseDomain, hIncrementDomain⟩ :=
    register_domains_of_valid finished hfinishedValid
  have hStartedCandidate : started = CoordinatorCollectionLedger.startRoundCandidate
      ledger x.time (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := by
    simpa only [hchoiceLedger] using hcandidate
  have hKnownService (b : Fin p.K) (q : CoordinatorCollectionLedger.CurrentRegister)
      (hq : ledger.currentRegisters b = some q) :
      let row := CoordinatorCollectionLedger.localQueueRecord ledger x.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r) b
      let next := QueueReplay.transition (4 * rate.n) (0, q.queue) row
      started.currentRegisters b = some ⟨next.2, next.1⟩ ∧ started.gammaLoc b = next.1 := by
    rw [hStartedCandidate]
    constructor
    · exact CoordinatorCollectionLedger.startRoundCandidate_known_transition
        ledger x.time _ _ b q hq
    · simp only [CoordinatorCollectionLedger.startRoundCandidate, hq]

  refine ⟨{
    jointBudget := hBudgetJoint
    scoreBudget := hBudgetScore
    senderWasPending := hSenderPendingLedger
    recordIsStep := hstepActual
    effectiveParse := hparse
    acceptedCheck := haccept
    startedAssignment := hstartedAssignment
    knownQueueService := hKnownService
    knownEnabledZeroService := by
      intro b q hq henabled hbefore hzero
      change ReferenceActivePhysicalStep.collectionEnabled ledger x.time = true at henabled
      change CoordinatorCollectionLedger.sourceRound x.time < ledger.freezeAt at hbefore
      change CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r) b = 0 at hzero
      have hknown := hKnownService b q hq
      simpa only [CoordinatorCollectionLedger.localQueueRecord, henabled, hbefore,
        decide_true, Bool.and_self, ite_true, hzero,
        QueueReplay.transition_enabled_zero_arrival, Nat.zero_add] using hknown
    knownDisabledService := by
      intro b q hq hdisabled
      change ReferenceActivePhysicalStep.collectionEnabled ledger x.time = false ∨
        ledger.freezeAt ≤ CoordinatorCollectionLedger.sourceRound x.time at hdisabled
      have hknown := hKnownService b q hq
      rcases hdisabled with hdisabled | hfrozen
      · simpa only [CoordinatorCollectionLedger.localQueueRecord, hdisabled,
          Bool.false_and, Bool.false_eq_true, ite_false, QueueReplay.transition,
          Prod.fst, Prod.snd] using hknown
      · have hnotBefore : ¬CoordinatorCollectionLedger.sourceRound x.time < ledger.freezeAt :=
          Nat.not_lt.mpr hfrozen
        simpa only [CoordinatorCollectionLedger.localQueueRecord, hnotBefore,
          decide_false, Bool.and_false, Bool.false_eq_true, ite_false,
          QueueReplay.transition, Prod.fst, Prod.snd] using hknown
    past := past
    currentRecord := currentRecord
    currentRecordIsActual := hCurrentRecordActual
    replayRecordsLength := by
      simpa [Nat.add_assoc] using hrecordsLength
    replayArrivalsBound := harrivals
    replayCalendarBits := by
      intro k
      simpa [List.get_eq_getElem,
        ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound] using hbits k
    replayPrefixBounds := by
      intro h hh
      have hp := hprefix h hh
      exact ⟨hp.1, hp.2.2.1, hp.2.2.2.1⟩
    replayDomains := hreplayCheck
    inclusiveReplayScore := by
      have hv : x.time.val + 1 + 1 = x.time.val + 2 := by omega
      simpa [hv] using hendpointScore
    inclusiveReplayTransition := hReplayTransition
    enabledZeroArrivalReplay := by
      intro hzero
      rw [hReplayTransition, hzero]
      exact QueueReplay.transition_enabled_zero_arrival _ _ _
    disabledReplayPreserves := hDisabledReplay
    frozenReplayPreserves := by
      intro hfrozen
      apply hDisabledReplay
      rw [hCurrentRecordActual]
      exact decide_eq_false (Nat.not_lt.mpr hfrozen)
    decoded := decoded
    bank := bank
    receiveInputDomain := by simpa [hstartedEq] using hdomainF
    receiveInputCheck := by simpa [hstartedEq] using hinputCheckF
    receiveInputBank := by simpa [hstartedEq] using hbankInputF
    decodeSuccess := by simpa [hstartedEq] using hdecoded
    receiveSuccess := by simpa [hstartedEq] using hreceiveResult
    bankAfter := by simpa [hstartedEq] using hbankAfter
    rawMatchesExpected := by simpa [hstartedEq] using hrawEq
    parserReturnsMessage := by simpa [hstartedEq] using hparseActual
    decodedValid := hdecodedValid
    decodedPhase := hphaseAfter
    decodedPending := by simpa [hstartedEq] using hpendingAfter
    decodedCursor := by simpa [hstartedEq] using hcursorAfter
    decodedContext := by
      exact ⟨hσAfter, hcutAfter, hfreezeAfter, hassignmentAfter, hbaseAfter⟩
    decodedSelectedRegisters := by
      have htake :
          (past ++ [currentRecord]).take ((past ++ [currentRecord]).length - 1) = past := by
        have hlen : (past ++ [currentRecord]).length - 1 = past.length := by simp
        rw [hlen]
        simp
      rw [htake] at hcurrentRecovered
      have hcutRecovered' : decoded.cutoffRegisters
          (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) =
          some ⟨M.val.S, M.val.q, M.val.delta⟩ := by
        simpa [x, hstartedEq] using hcutRecovered
      have hcurrentRecovered' : decoded.currentRegisters
          (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) =
          some ⟨(QueueReplay.replay (4 * rate.n) (0, M.val.q)
            (past ++ [currentRecord])).2,
            (QueueReplay.replay (4 * rate.n) (0, M.val.q)
              (past ++ [currentRecord])).1 -
              (QueueReplay.replay (4 * rate.n) (0, M.val.q) past).1⟩ := by
        simpa [x, hstartedEq] using hcurrentRecovered
      have hincrementRecovered' : decoded.increment
          (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) =
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            (past ++ [currentRecord])).1 := by
        simpa [x, hstartedEq] using hincrementRecovered
      have hgammaRecovered' : decoded.gammaLoc
          (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input)) = 0 := by
        simpa [x, hstartedEq] using hgammaRecovered
      dsimp only
      rw [htake]
      exact ⟨hcutRecovered', hcurrentRecovered', hincrementRecovered', hgammaRecovered'⟩
    decodedOtherGamma := by
      intro b _
      simpa [hstartedEq, r, x] using hgammaFrame b
    decodedSelectedRawCleared := by simpa [hstartedEq] using hrawCleared
    decoderBankWellFormed := hbankWellFormed
    decoderSenderQuota := hquota
    decoderSenderPendingEmpty := hselectedClear
    decoderSenderCompletedBatch := hselectedBatch
    decoderOtherBanks := hbankUnselected
    finished := finished
    finishSuccess := hfinish
    finishCandidate := hfinishedCandidate
    finishedValid := hfinishedValid
    finishedIncrement := hfinishedIncrement
    finishedGammaZero := hfinishedGamma
    finishedCursor := by
      have hv : x.time.val + 1 + 1 = x.time.val + 2 := by omega
      simpa [hv] using hfinishedCursor
    finishedReady := hfinishedPhase
    finishedPending := hFinishedPending
    finishedContext := ⟨hfinishedSigma, hfinishedCutoff, hfinishedFreeze,
      hfinishedAssignment, hfinishedBase⟩
    finishedRegistersPreserved := ⟨hfinishedCutoffRegisters,
      hfinishedCurrentRegisters, hfinishedRaw, hfinishedHistory⟩
    finishedSelectedIncrement := by simpa [hstartedEq] using hfinishedAtArm
    finishedSelectedGammaZero := by
      simpa [r, x] using hfinishedGammaZero
        (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex r.input))
    finishedOtherIncrement := by simpa [hstartedEq] using hfinishedOtherIncrement
    finishedAllGammaZero := hfinishedGammaZero
    currentRegisterDomains := hCurrentDomains
    cutoffRegisterDomains := hCutoffDomains
    baseScoreDomain := hBaseDomain
    incrementDomain := hIncrementDomain
    registerPendingEquivalence := hfinishedRegisters
    pendingArmIncrementZero := by
      intro b hb
      have hPendingEq : finished.pending = decoded.pending := by
        calc
          finished.pending = ledger.pending.erase i := hFinishedPending
          _ = decoded.pending := by simpa [i] using hpendingAfter.symm
      have hAssignmentEq : finished.assignment = decoded.assignment :=
        hfinishedAssignment.trans hassignmentAfter.symm
      have hArm : CoordinatorCollectionLedger.armPending decoded b := by
        simpa [CoordinatorCollectionLedger.armPending, hPendingEq, hAssignmentEq] using hb
      have hz := hzeroPendingAfter b hArm
      constructor
      · simp [hfinishedIncrement, hz.1, hz.2]
      · exact hfinishedGammaZero b
    cutoffMassBounds := hfinishedCutoffMass
    currentMassBounds := by
      intro b c q hc hq
      have hv : x.time.val + 1 + 1 = x.time.val + 2 := by omega
      simpa [hv] using (hfinishedMass b c q hc hq).1
    currentServiceSpanBound := by
      intro b c q hc hq
      have hv : x.time.val + 1 + 1 = x.time.val + 2 := by omega
      simpa [hv] using (hfinishedMass b c q hc hq).2
    rawBufferBounds := hfinishedRawSupport
    enabledHistoryExact := hfinishedHistory2
    bankOutsidePendingEmpty := by
      intro k hk
      have hk' : k ∉ decoded.pending := by simpa [hFinishedPending, hpendingAfter] using hk
      exact hbankEmptyOutside k hk'
    clockFinishSuccess := by simpa [hchoiceStarted] using hclockFinish
    clockFinishPreservesContext := by
      refine ⟨rfl, rfl, rfl, ?_⟩
      simpa [hchoiceStarted] using hlastProposal
    lastProposal := actualLastProposal
    lastProposalIsSaved := by simpa [actualLastProposal] using hlastProposal
    actualCollectionFinish := by
      simpa [hchoiceStarted, hstartedEq, hrecordingEq, actualLastProposal] using
        hcollectionFinish
    actualCoordinatorFailureNone := by rw [hactualCoordinatorEq]
    actualCoordinatorRecording := by rw [hactualCoordinatorEq]
    actualCoordinatorUp := by rw [hactualCoordinatorEq]
    actualNextCoordinator := by
      change r.output.next.coordinator = .collection payload finished actualLastProposal
      rw [hstepActual]
      simpa [actualLastProposal] using hstepNextCoordinator
    actualNextBank := by
      change r.output.next.upDecoderBank = bank
      rw [hstepActual]
      exact hstepNextBank
    actualNextActivations := by
      change r.output.next.activations = r.input.state.activations
      rw [hstepActual]
      simpa [r, x] using hstepNextActivations
    acceptedLabel := hAcceptedLabel
    eraseEventExact := hEraseEventExact
    nextReadyOnOriginalPrefix := by
      intro hremaining hbefore
      have hremaining' : (ledger.pending.erase i).Nonempty := by
        simpa [hFinishedPending] using hremaining
      have hnextResults := hnextBranch hremaining'
      have hreadyResult := hnextResults.1 hbefore
      rcases hreadyResult with
        ⟨xNext, hxstate, hxrows, hxselected, hxrewards, hxtime, hxready⟩
      have hNextPrefix :=
        ReferenceFirstCollectionReadyStep.actual_collection_window_next_prefix_input
          rate source rewards C_star C_h count hcross hspan hshort n
          (by simpa [x] using hbefore)
      rcases hNextPrefix with
        ⟨next, hnextstate, hnextrows, hnextselected, hnextrewards,
          hnexttime, hnextRecord⟩
      have hnextVal : next.time.val = x.time.val + 1 := by
        calc
          next.time.val = start + j + 1 := hnexttime
          _ = start + (w + n.val) + 1 := by rfl
          _ = start + w + 1 + n.val := by
            calc
              start + (w + n.val) + 1 = (start + w) + n.val + 1 := by
                simp only [Nat.add_assoc]
              _ = (start + w) + 1 + n.val := by
                exact Nat.add_right_comm (start + w) n.val 1
          _ = x.time.val + 1 := htimeActual.symm
      have hnextStates : xNext.state = next.state := by
        calc
          xNext.state = (ReferenceActivePhysicalStep.step x).next := hxstate
          _ = r.output.next := by rw [← hstepActual]
          _ = next.state := hnextstate.symm
      have hnextRows : xNext.rows = next.rows := by
        calc
          xNext.rows = x.rows := hxrows
          _ = source.1.2 := hinputData.1
          _ = next.rows := hnextrows.symm
      have hnextSelected : xNext.selected = next.selected := by
        calc
          xNext.selected = x.selected := hxselected
          _ = ActualInitializationPhysicalStep.selectedRowIndex p source := hinputData.2.1
          _ = next.selected := hnextselected.symm
      have hnextRewards : xNext.rewards = next.rewards := by
        calc
          xNext.rewards = x.rewards := hxrewards
          _ = rewards := hinputData.2.2
          _ = next.rewards := hnextrewards.symm
      have hnextTimeVal : xNext.time.val = next.time.val := by
        rw [hxtime, hnextVal]
      have hnextTimeEq : xNext.time = next.time := Fin.ext hnextTimeVal
      have hNextEq : xNext = next :=
        round_input_ext hnextStates hnextRows hnextSelected hnextTimeEq hnextRewards
      refine ⟨next, hnextstate, hnextrows, hnextselected, hnextrewards,
        hnextVal, ?_, ?_⟩
      · rw [← hNextEq]
        simpa [actualLastProposal] using hxready
      · intro hnext
        have hcount : epoch.records.length = count := by
          simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
            initial] using
            ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              start count hspan hactive
        have hnextCount : j + 1 < count := by rw [← hcount]; exact hnext
        simpa [epoch, w, window, r, j, hcount] using hnextRecord hnextCount
    terminalReadyBoundary := by
      intro hremaining hterminal
      have hremaining' : (ledger.pending.erase i).Nonempty := by
        simpa [hFinishedPending] using hremaining
      have hboundary := (hnextBranch hremaining').2 hterminal
      rw [hstepActual]
      simpa [actualLastProposal] using hboundary
    allKnownWhenPendingEmpty := by
      intro hempty b
      have hempty' : ledger.pending.erase i = ∅ := by
        simpa [hFinishedPending] using hempty
      rcases hallKnown hempty' b with ⟨q, hq, c, hc⟩
      exact ⟨⟨q, hq⟩, ⟨c, hc⟩⟩
  }⟩

end Bandits.Support.ReferenceFirstCollectionAcceptedReadyStep

end
