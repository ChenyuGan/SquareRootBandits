/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionReadyStep

import Lean.Elab.Tactic.Omega

/-!
# One actual rejected UP finish in the first collection

At an arbitrary record of the actual first collection, this module composes
the existing ready-to-START producer with the actual filtered rejected
receiver and FINISH domain.  The only induction input is the existing local
ready predicate at that record.  The branch is selected by the literal
effective parse and receiver check; no sender success or history is supplied.

Mathematical source ranges: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-299`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-70`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRejectedReadyStep

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

/-- The literal rejected branch at the actual filtered parser and actual UP
acceptance check.  A raw parser result is deliberately not used here. -/
def actualRejectedBranch
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (started : Ledger rate) : Prop :=
  ReferenceCollectionSegmentExtraction.effectiveParse x started = none ∨
    ∃ M, ReferenceCollectionSegmentExtraction.effectiveParse x started = some M ∧
      CoordinatorCollectionLedger.acceptUpCheck started
        (ReferenceActivePhysicalStep.upSenderIndex x) M = false

/-- Concrete data and proof fields produced by the rejected FINISH query for
one actual physical input.  This records the existing ledger and physical
outputs; it introduces no alternate state carrier. -/
structure ActualRejectedFinishOutput
    (r : ReferenceFirstCollectionReadyStep.Record (p := p) rate)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (o : CoordinatorRecordingOperation.Output p)
    (started : Ledger rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : RewardTable p)
    (records : List (ReferenceFirstCollectionReadyStep.Record (p := p) rate))
    (count j : ℕ) where
  filteredParse_alignment :
    CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs
                (ReferenceActivePhysicalStep.prepare x) started) x.time)).2
          (ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare x))) =
      ReferenceCollectionSegmentExtraction.effectiveParse x started
  started_valid : CoordinatorCollectionLedger.validLedgerCheck started = true
  started_phase : started.phase = CoordinatorCollectionLedger.Phase.started
  started_cursor : started.cursor =
    ReferenceContinuingCollectionStartDomains.sourceRound x.time
  started_sigma : started.sigma = ledger.sigma
  started_cutoff : started.cutoff = ledger.cutoff
  started_freezeAt : started.freezeAt = ledger.freezeAt
  started_pending : started.pending = ledger.pending
  started_assignment : started.assignment = ledger.assignment
  started_baseScore : started.baseScore = ledger.baseScore
  started_cutoffRegisters : started.cutoffRegisters = ledger.cutoffRegisters
  started_increment : started.increment = ledger.increment
  started_register_pending : ∀ a,
    (started.currentRegisters a = none ↔
      CoordinatorCollectionLedger.armPending started a) ∧
    (started.cutoffRegisters a = none ↔
      CoordinatorCollectionLedger.armPending started a) ∧
    (ledger.currentRegisters a = none →
      started.currentRegisters a = none ∧ started.gammaLoc a = 0)
  started_joint_and_span : ∀ a c0 q,
    ledger.cutoffRegisters a = some c0 → started.currentRegisters a = some q →
      c0.score + ledger.increment a + started.gammaLoc a + q.queue ≤
          (ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1 -
            ledger.sigma) * D p ∧
      c0.score + ledger.increment a + started.gammaLoc a ≤
          4 * rate.n *
            (min (ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1)
              ledger.freezeAt - ledger.sigma) ∧
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p
  started_current_register_domain : ∀ a q,
    started.currentRegisters a = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p
  started_cutoff_register_domain : ∀ a c0,
    started.cutoffRegisters a = some c0 →
      c0.score ≤ p.T * D p ∧ c0.queue ≤ p.T * D p ∧ c0.lastService ≤ D p
  started_pending_zero : ∀ a,
    CoordinatorCollectionLedger.armPending started a →
      started.increment a = 0 ∧ started.gammaLoc a = 0
  started_service_bounds : ∀ a,
    started.gammaLoc a ≤ 4 * rate.n ∧ started.gammaLoc a ≤ D p ∧
      started.increment a + started.gammaLoc a ≤ p.T * D p
  started_raw_entries : ∀ a r amount,
    started.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧
      ledger.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
      ReferenceContinuingCollectionStartDomains.sourceRound r <
        min (ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1)
          ledger.freezeAt ∧
      CoordinatorCollectionLedger.armPending started a
  started_enabled_history : ∀ r,
    started.enabledHistory r =
      if ledger.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
          ReferenceContinuingCollectionStartDomains.sourceRound r ≤
            ReferenceContinuingCollectionStartDomains.sourceRound x.time then
        some (decide
          (ReferenceContinuingCollectionStartDomains.sourceRound r < ledger.freezeAt))
      else none
  decoded : Ledger rate
  bank : CoordinatorUpReception.UpDecoderBank p
  receiver_rejected :
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).result = .rejected (decoded, bank)
  decoded_phase : decoded =
    {started with phase := CoordinatorCollectionLedger.Phase.decoded}
  reception_input_domain :
    CoordinatorUpReception.receptionInputDomain
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare x) started) x.time)
  reception_input_check :
    CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare x) started) x.time) = true
  receiver_diagnostic :
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).diagnostic =
      some {
        input := ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) started) x.time
        expected := ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare x)
        decoderAfter := (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time)).1
        raw := (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time)).2
        parsed := ReferenceUpReception.rawParsedOutput rate
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time)
        locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time)
        rawMatches := decide ((CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time)).2 =
            ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare x))
        wrongUniqueAccepted :=
          ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time
            ((ReferenceActivePhysicalStep.prepare x).followers.followers
              (ReferenceActivePhysicalStep.upSenderIndex x))
            ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
            ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
            ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl }
  finished : Ledger rate
  finish_success :
    CoordinatorCollectionLedger.finishRound decoded = .success finished
  finish_candidate : finished = CoordinatorCollectionLedger.finishRoundCandidate decoded
  finished_increment : finished.increment =
    (fun a => ledger.increment a + started.gammaLoc a)
  finished_gammaLoc : finished.gammaLoc = fun _ => 0
  finished_cursor :
    finished.cursor = ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1
  finished_phase : finished.phase = CoordinatorCollectionLedger.Phase.ready
  finished_pending : finished.pending = ledger.pending
  finished_pending_nonempty : finished.pending.Nonempty
  finished_assignment : finished.assignment = ledger.assignment
  finished_baseScore : finished.baseScore = ledger.baseScore
  finished_sigma : finished.sigma = ledger.sigma
  finished_cutoff : finished.cutoff = ledger.cutoff
  finished_freezeAt : finished.freezeAt = ledger.freezeAt
  finished_cutoffRegisters : finished.cutoffRegisters = ledger.cutoffRegisters
  finished_currentRegisters : finished.currentRegisters = started.currentRegisters
  finished_rawBuffer : finished.rawBuffer = started.rawBuffer
  finished_enabledHistory : finished.enabledHistory = started.enabledHistory
  finished_register_pending : ∀ a,
    (finished.currentRegisters a = none ↔
      CoordinatorCollectionLedger.armPending finished a) ∧
    (finished.cutoffRegisters a = none ↔
      CoordinatorCollectionLedger.armPending finished a) ∧
    (CoordinatorCollectionLedger.armPending finished a → finished.increment a = 0)
  finished_cutoff_domain : ∀ a c0,
    finished.cutoffRegisters a = some c0 →
      c0.score ≤ p.T * D p ∧ c0.queue ≤ p.T * D p ∧ c0.lastService ≤ D p ∧
      c0.score + c0.queue ≤ (finished.cutoff - finished.sigma) * D p
  finished_current_joint_and_span : ∀ a c0 q,
    ledger.cutoffRegisters a = some c0 → started.currentRegisters a = some q →
      c0.score + finished.increment a + q.queue ≤
        (ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1 -
          ledger.sigma) * D p ∧
      c0.score + finished.increment a ≤
        4 * rate.n *
          (min (ReferenceContinuingCollectionStartDomains.sourceRound x.time + 1)
            ledger.freezeAt - ledger.sigma)
  finished_raw_entries : ∀ a r amount,
    finished.rawBuffer a r = some amount →
      0 < amount ∧ amount ≤ D p ∧
      ledger.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
      ReferenceContinuingCollectionStartDomains.sourceRound r <
        min finished.cursor finished.freezeAt ∧
      CoordinatorCollectionLedger.armPending finished a
  finished_enabled_history : ∀ r,
    finished.enabledHistory r =
      if ledger.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
          ReferenceContinuingCollectionStartDomains.sourceRound r < finished.cursor then
        some (decide
          (ReferenceContinuingCollectionStartDomains.sourceRound r < finished.freezeAt))
      else none
  finished_valid : CoordinatorCollectionLedger.validLedgerCheck finished = true
  clockFinished : CoordinatorPhaseClock.FinishRoundResult p
  clock_finish_success :
    CoordinatorPhaseClock.finishRound p rate.eta.val x.time c.started.clock
      finished.pending x.row = .ok clockFinished
  clock_same : clockFinished.clock = c.started.clock
  clock_pending : clockFinished.pending = finished.pending
  clock_command :
    clockFinished.ledgerCommand =
      some (.accumulateLocalServiceAt x.time)
  actualLastProposal : Option (Fin p.T × Bool)
  actualLastProposal_eq : actualLastProposal = saved
  collection_finish_eq :
    ReferenceActivePhysicalStep.collectionFinish (x := x) payload c.started o
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started) =
      { configuration := .collection payload finished actualLastProposal
        upDecoderBank := bank
        failure := none
        recording := some o
        up := (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started).diagnostic }
  observe_coordinator_eq :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload c.started o
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started)
  step_coordinator_eq :
    (ReferenceActivePhysicalStep.step x).coordinator =
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator
  step_next_coordinator_eq :
    (ReferenceActivePhysicalStep.step x).next.coordinator =
      .collection payload finished actualLastProposal
  step_next_bank_eq :
    (ReferenceActivePhysicalStep.step x).next.upDecoderBank = bank
  step_next_activations_eq :
    (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations
  step_followers_eq : ∀ i,
    (ReferenceActivePhysicalStep.step x).followers i =
      (ReferenceActivePhysicalStep.prepare x).observeFollower i
  step_ownEntries_eq :
    (ReferenceActivePhysicalStep.step x).ownEntries =
      (ReferenceActivePhysicalStep.prepare x).feedback.ownEntries
  actual_record_failure_none :
    r.output.coordinator.failure = none
  acceptedLabel_none : ReferenceCollectionPhaseHistory.acceptedLabel x = none
  eraseEvent_recurrence :
    finished.pending = ReferenceCollectionPhaseHistory.eraseEvent ledger.pending
      (ReferenceCollectionPhaseHistory.acceptedLabel x)
  next_ready_prefix : ∀ (_ : x.time.val + 1 < p.T),
    ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
      next.state = (ReferenceActivePhysicalStep.step x).next ∧
      next.rows = rows ∧
      next.selected = selected ∧
      next.rewards = rewards ∧
      next.time.val = x.time.val + 1 ∧
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        next payload finished actualLastProposal ∧
      ∀ hnext : j + 1 < records.length,
        next = (records[j + 1]'hnext).input
  boundary_ready : x.time.val + 1 = p.T →
    ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      (ReferenceActivePhysicalStep.step x).next payload finished actualLastProposal

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

/-- At every index of the actual first-collection window, the existing local
ready predicate produces the real START witnesses.  Whenever their actual
filtered parse is rejected, the instantiated receiver and checked FINISH
produce the same ready ledger on the next original prefix input, or the
terminal ready boundary at `T`. -/
theorem actual_collection_window_rejected_ready_finish
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
    (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved) :
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
    window[n.val].output = ReferenceActivePhysicalStep.step x ∧
    x.time.val + 1 = start + w + 1 + n.val ∧
    ∃ cutoff : Fin p.T, cutoff.val + 1 = ledger.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1)
      (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff (.continuing core snap hb hs) ∧
      ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
        (o : CoordinatorRecordingOperation.Output p) (started : Ledger rate),
        ReferenceCollectionSegmentExtraction.choice x = some c ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o ∧
        c.payload = payload ∧ c.preLedger = ledger ∧
        c.started = snap.clockStarted ∧ c.initializer = none ∧
        CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
            .success started ∧
        started = CoordinatorCollectionLedger.startRoundCandidate c.preLedger x.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic r) ∧
        (∀ a, (started.currentRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a) ∧
          (started.cutoffRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a)) ∧
        (∀ _ : actualRejectedBranch x started,
          Nonempty (ActualRejectedFinishOutput r x payload ledger saved c o started
            source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards epoch.records count j)) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let r := window[n.val]
  let x := r.input
  let j := w + n.val
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hR := ReferenceFirstCollectionReadyStep.actual_collection_window_ready_start
    rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved hReady
  rcases hR with ⟨hstep, htime, cutoff, hcutoff, core, snap, hb, hs, hcoord,
    c, o, started, hchoice, hrecording, hcpayload, hcpre, hcstarted, hcinit,
    hstart, hcandidate, hregisters⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  have hF :=
    ReferenceContinuingCollectionRejectedFinishDomains.continuing_collection_rejected_finish_domains
      x payload ledger saved hReady
  rcases hF with ⟨cutoffF, hcutoffF, coreF, snapF, hbF, hsF, hcoordF,
    harmF, hlocalF, hrecordInputsF, oF, l1, hrecordF, hstartF, hcandidateF,
    hvalidF, hphaseF, hcursorF, hσF, hcutF, hfreezeF, hpendingF,
    hassignmentF, hbaseF, hcutregsF, hincrementF, hregistersF, hmassF,
    hcurrentF, hcutDomainF, hzeroF, hgammaF, hrawF, hhistoryF, hmessagesF⟩
  let weightsF := CoordinatorCollectionInteractive.PreObservationInputs.weights
    (ReferenceActivePhysicalStep.collectionInput x payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoffF) cutoffF)
    snapF.inputsValid.ledger_valid snapF.inputsValid.assignment_eq
  let cF : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, ledger, snapF.clockStarted, weightsF, none⟩
  have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    split at hchoice
    · contradiction
    · assumption
  have hchoiceF : ReferenceCollectionSegmentExtraction.choice x = some cF := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [ite_eq_right hselected, hcoordF]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      cF, weightsF]
  have hcEq : c = cF := Option.some.inj (hchoice.symm.trans hchoiceF)
  have hcPayload : c.payload = payload := by
    simpa [cF] using congrArg (fun ch : ReferenceCollectionSegmentExtraction.Choice rate => ch.payload) hcEq
  have hcPreLedger : c.preLedger = ledger := by
    simpa [cF] using congrArg (fun ch : ReferenceCollectionSegmentExtraction.Choice rate => ch.preLedger) hcEq
  have hcStartedF : c.started = snapF.clockStarted := by
    simpa [cF] using congrArg (fun ch : ReferenceCollectionSegmentExtraction.Choice rate => ch.started) hcEq
  have hrecordF' : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some oF := by
    calc
      CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) =
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) cF.payload cF.started cF.weights) :=
          congrArg (fun ch : ReferenceCollectionSegmentExtraction.Choice rate =>
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare x) ch.payload ch.started ch.weights)) hcEq
      _ = some oF := by simpa [cF] using hrecordF
  have hoEq : o = oF := Option.some.inj (hrecording.symm.trans hrecordF')
  have hstartF' : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 := by
    simpa [ReferenceContinuingCollectionRejectedFinishDomains.sourceRound, hoEq] using hstartF
  have hl1Eq : l1 = started := by
    have hsuccessEq : CoordinatorCollectionLedger.Checked.success l1 =
        CoordinatorCollectionLedger.Checked.success started := hstartF'.symm.trans hstart
    injection hsuccessEq with hEq
  have hStartedSigma : started.sigma = ledger.sigma := by
    simpa [hl1Eq] using hσF
  have hStartedCutoff : started.cutoff = ledger.cutoff := by
    simpa [hl1Eq] using hcutF
  have hStartedFreeze : started.freezeAt = ledger.freezeAt := by
    simpa [hl1Eq] using hfreezeF
  have hStartedCutRegisters : started.cutoffRegisters = ledger.cutoffRegisters := by
    simpa [hl1Eq] using hcutregsF
  have hfilteredEq :
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs
                (ReferenceActivePhysicalStep.prepare x) l1) x.time)).2
          (ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare x))) =
        ReferenceCollectionSegmentExtraction.effectiveParse x started := by
    change ReferenceCollectionSegmentExtraction.effectiveParse x l1 =
      ReferenceCollectionSegmentExtraction.effectiveParse x started
    rw [hl1Eq]
  have hOutput : ∀ hbranch : actualRejectedBranch x started,
      Nonempty (ActualRejectedFinishOutput r x payload ledger saved c o started
        source.1.2 selected rewards epoch.records count j) := by
    intro hbranch
    have hbranchF :
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (ReferenceUpReception.filterRawByExpected
            (CoordinatorUpReception.decoderTransition
              (ReferenceUpReception.receptionInputAtRow rate x.row
                (ReferenceActivePhysicalStep.upInputs
                  (ReferenceActivePhysicalStep.prepare x) l1) x.time)).2
            (ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare x))) = none ∨
          ∃ M,
            CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
              (ReferenceUpReception.filterRawByExpected
                (CoordinatorUpReception.decoderTransition
                  (ReferenceUpReception.receptionInputAtRow rate x.row
                    (ReferenceActivePhysicalStep.upInputs
                      (ReferenceActivePhysicalStep.prepare x) l1) x.time)).2
                (ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare x))) = some M ∧
            CoordinatorCollectionLedger.acceptUpCheck l1
              (ReferenceActivePhysicalStep.upSenderIndex x) M = false := by
      rcases hbranch with hnone | ⟨M, hparsed, haccept⟩
      · exact Or.inl (hfilteredEq.trans hnone)
      · refine Or.inr ⟨M, hfilteredEq.trans hparsed, ?_⟩
        simpa [hl1Eq] using haccept
    have hfinishF := hmessagesF hbranchF
    rcases hfinishF with ⟨decoded, bank, hreceiver, hdecodedPhase, hdomain,
      hcheck, hdiagnostic, finished, hfinish, hfinishCandidate, hfinishIncrement,
      hfinishGamma, hfinishCursor, hfinishPhase, hfinishPending,
      hfinishAssignment, hfinishBase, hfinishCutoffRegisters,
      hfinishCurrentRegisters, hfinishRaw, hfinishHistory, hfinishJoint,
      hfinishRawEntries, hfinishEnabledHistory, hfinishValid, clockFinished,
      hclockFinish, hclockSame, hclockPending, hclockCommand,
      hlastProposal, hcollectionFinish, hobserve, hstepCoordinator,
      hstepNextCoordinator, hstepNextBank, hstepNextActivations,
      hstepFollowers, hstepOwnEntries, hnextReady, hboundaryReady⟩
    let actualLastProposal := clockFinished.clock.lastProposal
    rcases hReady with ⟨hstateReady, hphaseReady, hσposReady, hσTReady, hσcutReady,
      hσpayloadReady, hcutPosReady, hcutTReady, hcutFreezeReady, hfreezeTReady,
      hgridReady, hcursorReady, hcutCursorReady, hcursorTReady, hassignmentReady,
      hbaseReady, hanchorReady, hnReady, hReadyPending, hregisterReady, hgammaReady,
      hReadyCut, hpairedReady, hcapReady, hrawReady, hhistoryReady, hbankReady⟩
    have hFinishedSigma : finished.sigma = ledger.sigma := by
      calc
        finished.sigma = decoded.sigma := by
          rw [hfinishCandidate]
          rfl
        _ = started.sigma := by simp [hdecodedPhase, hl1Eq]
        _ = ledger.sigma := hStartedSigma
    have hFinishedCutoff : finished.cutoff = ledger.cutoff := by
      calc
        finished.cutoff = decoded.cutoff := by
          rw [hfinishCandidate]
          rfl
        _ = started.cutoff := by simp [hdecodedPhase, hl1Eq]
        _ = ledger.cutoff := hStartedCutoff
    have hFinishedFreeze : finished.freezeAt = ledger.freezeAt := by
      calc
        finished.freezeAt = decoded.freezeAt := by
          rw [hfinishCandidate]
          rfl
        _ = started.freezeAt := by simp [hdecodedPhase, hl1Eq]
        _ = ledger.freezeAt := hStartedFreeze
    have hFinishedRegisterPending : ∀ a,
        (finished.currentRegisters a = none ↔
          CoordinatorCollectionLedger.armPending finished a) ∧
        (finished.cutoffRegisters a = none ↔
          CoordinatorCollectionLedger.armPending finished a) ∧
        (CoordinatorCollectionLedger.armPending finished a → finished.increment a = 0) := by
      intro a
      have hStartedPending : started.pending = ledger.pending := by
        simpa [hl1Eq] using hpendingF
      have hStartedAssignment : started.assignment = ledger.assignment := by
        simpa [hl1Eq] using hassignmentF
      have hArmStarted :
          CoordinatorCollectionLedger.armPending started a ↔
            CoordinatorCollectionLedger.armPending ledger a := by
        simp [CoordinatorCollectionLedger.armPending, hStartedPending,
          hStartedAssignment]
      have hArmFinished :
          CoordinatorCollectionLedger.armPending finished a ↔
            CoordinatorCollectionLedger.armPending ledger a := by
        simp [CoordinatorCollectionLedger.armPending, hfinishPending,
          hfinishAssignment]
      have hreg' : (started.currentRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a) ∧
          (started.cutoffRegisters a = none ↔
            CoordinatorCollectionLedger.armPending started a) := by
        exact ⟨by simpa [hl1Eq] using (hregistersF a).1,
          by simpa [hl1Eq] using (hregistersF a).2.1⟩
      have hFinishedCurrentRegisters : finished.currentRegisters = started.currentRegisters := by
        simpa [hl1Eq] using hfinishCurrentRegisters
      have hFinishedCutoffRegisters : finished.cutoffRegisters = started.cutoffRegisters := by
        calc
          finished.cutoffRegisters = ledger.cutoffRegisters := hfinishCutoffRegisters
          _ = started.cutoffRegisters := hStartedCutRegisters.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hFinishedCurrentRegisters]
        exact hreg'.1.trans (hArmStarted.trans hArmFinished.symm)
      · rw [hFinishedCutoffRegisters]
        exact hreg'.2.trans (hArmStarted.trans hArmFinished.symm)
      · intro hpending
        have hpendingLedger := hArmFinished.mp hpending
        have hpendingStarted := hArmStarted.mpr hpendingLedger
        have hzero := hzeroF a (by simpa [hl1Eq] using hpendingStarted)
        have hfinishInc : finished.increment = fun b => ledger.increment b + started.gammaLoc b := by
          simpa [hl1Eq] using hfinishIncrement
        have hincZero : ledger.increment a = 0 := by
          exact (congrArg (fun f => f a) hincrementF).symm.trans hzero.1
        have hgammaZero : started.gammaLoc a = 0 := by
          simpa [hl1Eq] using hzero.2
        rw [hfinishInc]
        change ledger.increment a + started.gammaLoc a = 0
        rw [hincZero, hgammaZero]
    have hFinishedCutoffDomain : ∀ a c0,
        finished.cutoffRegisters a = some c0 →
        c0.score ≤ p.T * D p ∧ c0.queue ≤ p.T * D p ∧
          c0.lastService ≤ D p ∧
          c0.score + c0.queue ≤ (finished.cutoff - finished.sigma) * D p := by
      intro a c0 hc0
      have hcLedger : ledger.cutoffRegisters a = some c0 := by
        rw [hfinishCutoffRegisters] at hc0
        exact hc0
      have hStartedCutRegister : started.cutoffRegisters a = some c0 := by
        simpa [hStartedCutRegisters] using hcLedger
      have hdomain0 := hcutDomainF a c0 (by simpa [hl1Eq] using hStartedCutRegister)
      have hmass0 := hReadyCut a c0 hcLedger
      exact ⟨hdomain0.1, hdomain0.2.1, hdomain0.2.2,
        by simpa [hFinishedCutoff, hFinishedSigma] using hmass0.1⟩
    have hacceptedLabel : ReferenceCollectionPhaseHistory.acceptedLabel x = none := by
      let inputR := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
      let weightsR := CoordinatorCollectionInteractive.PreObservationInputs.weights inputR
        snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
      let cR : ReferenceCollectionSegmentExtraction.Choice rate :=
        ⟨payload, ledger, snap.clockStarted, weightsR, none⟩
      have hcRChoice : ReferenceCollectionSegmentExtraction.choice x = some cR := by
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [ite_eq_right hselected, hcoord]
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
          cR, inputR, weightsR, clock]
      have hcR : c = cR := Option.some.inj (hchoice.symm.trans hcRChoice)
      let tail : ReferenceCollectionPhaseHistory.Tail x :=
        ⟨payload, ledger, snap.clockStarted, weightsR⟩
      have htail : ReferenceCollectionPhaseHistory.executedTail x = some tail := by
        unfold ReferenceCollectionPhaseHistory.executedTail
        rw [ite_eq_right hselected, hcoord]
      have hrecordingR : CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) payload snap.clockStarted weightsR) = some o := by
        calc
          CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare x) payload snap.clockStarted weightsR) =
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) :=
                (congrArg (fun ch : ReferenceCollectionSegmentExtraction.Choice rate =>
                  CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.collectionRecordingInput
                      (ReferenceActivePhysicalStep.prepare x) ch.payload ch.started ch.weights)) hcR).symm
          _ = some o := hrecording
      have htailReception : tail.reception =
          some (started, ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started) := by
        simp [ReferenceCollectionPhaseHistory.Tail.reception, tail, x, r, window, epoch,
          w, hrecordingR, hstart]
      have hreceiverR : (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started).result = .rejected (decoded, bank) := by
        simpa [hl1Eq] using hreceiver
      unfold ReferenceCollectionPhaseHistory.acceptedLabel
      simp only [htail, Option.bind_some, htailReception]
      simp [hreceiverR]
    have herase : finished.pending = ReferenceCollectionPhaseHistory.eraseEvent
        ledger.pending (ReferenceCollectionPhaseHistory.acceptedLabel x) := by
      simpa [hacceptedLabel, ReferenceCollectionPhaseHistory.eraseEvent] using hfinishPending
    have hrecordCount : epoch.records.length = count := by
      simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        initial, selected, start, active] using
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 selected rewards
          start count hspan active
    have hlookup := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
      rate source rewards C_star C_h count hcross hspan hshort n
    have hrecordIndex : j < epoch.records.length :=
      (List.getElem?_eq_some_iff.mp (by
        simpa [epoch, w, window, j] using hlookup.1)).1
    have hrecordEq : epoch.records[j]'hrecordIndex = r := by
      have hget := List.getElem?_eq_getElem (l := epoch.records) hrecordIndex
      have hlookup' : epoch.records[j]? = some r := by
        simpa [epoch, w, window, j] using hlookup.1
      exact Option.some.inj (hget.symm.trans hlookup')
    have hrecordMem : r ∈ epoch.records := by
      rw [← hrecordEq]
      exact List.getElem_mem hrecordIndex
    have hinputFields :=
      ReferenceActivePhysicalHorizon.run_record_inputs initial source.1.2 selected rewards
        start count hspan active r hrecordMem
    have hinputRows : x.rows = source.1.2 := by
      simpa [x, r, epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        initial, selected, start, active] using hinputFields.1
    have hinputSelected : x.selected = selected := by
      simpa [x, r, epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        initial, selected, start, active] using hinputFields.2.1
    have hinputRewards : x.rewards = rewards := by
      simpa [x, r, epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
        initial, selected, start, active] using hinputFields.2.2
    have hcollectionFinishR :
        ReferenceActivePhysicalStep.collectionFinish (x := x) payload c.started o
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started) =
        { configuration := .collection payload finished actualLastProposal
          upDecoderBank := bank
          failure := none
          recording := some o
          up := (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started).diagnostic } := by
      simpa [hcStartedF, hoEq, hl1Eq] using hcollectionFinish
    have hobserveR :
        (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
          ReferenceActivePhysicalStep.collectionFinish (x := x) payload c.started o
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) started) := by
      simpa [hcStartedF, hoEq, hl1Eq] using hobserve
    have hfailure : r.output.coordinator.failure = none := by
      rw [hstep, hstepCoordinator, hobserveR, hcollectionFinishR]
    have hnextReadyPrefix : ∀ (hbefore : x.time.val + 1 < p.T),
        ∃ next : ReferenceActivePhysicalStep.RoundInput p rate,
          next.state = (ReferenceActivePhysicalStep.step x).next ∧
          next.rows = source.1.2 ∧ next.selected = selected ∧ next.rewards = rewards ∧
          next.time.val = x.time.val + 1 ∧
          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
            next payload finished actualLastProposal ∧
          ∀ hnext : j + 1 < epoch.records.length,
            next = (epoch.records[j + 1]'hnext).input := by
      intro hbefore
      have hprefix :=
        ReferenceFirstCollectionReadyStep.actual_collection_window_next_prefix_input
          rate source rewards C_star C_h count hcross hspan hshort n hbefore
      rcases hprefix with ⟨next, hnextState, hnextRows, hnextSelected, hnextRewards,
        hnextTime, hnextRecord⟩
      have hnextF := hnextReady (by
        change x.time.val + 1 < p.T
        simpa [ReferenceContinuingCollectionStartDomains.sourceRound] using hbefore)
      rcases hnextF with ⟨xNext, hxstate, hxrows, hxselected, hxrewards, hxtime, hxready⟩
      have hrowsEq : next.rows = xNext.rows := by
        calc
          next.rows = source.1.2 := hnextRows
          _ = x.rows := hinputRows.symm
          _ = xNext.rows := hxrows.symm
      have hselectedEq : next.selected = xNext.selected := by
        calc
          next.selected = selected := hnextSelected
          _ = x.selected := hinputSelected.symm
          _ = xNext.selected := hxselected.symm
      have hrewardsEq : next.rewards = xNext.rewards := by
        calc
          next.rewards = rewards := hnextRewards
          _ = x.rewards := hinputRewards.symm
          _ = xNext.rewards := hxrewards.symm
      have hstateEq : next.state = xNext.state := by
        calc
          next.state = r.output.next := hnextState
          _ = (ReferenceActivePhysicalStep.step x).next := by rw [hstep]
          _ = xNext.state := hxstate.symm
      have hnextLocalTime : next.time.val = x.time.val + 1 := by
        calc
          next.time.val = start + j + 1 := hnextTime
          _ = start + w + 1 + n.val := by dsimp [j]; omega
          _ = x.time.val + 1 := htime.symm
      have htimeEq : next.time = xNext.time :=
        Fin.ext (hnextLocalTime.trans hxtime.symm)
      have hnextEq := round_input_ext hstateEq hrowsEq hselectedEq htimeEq hrewardsEq
      have hnextState' : next.state = (ReferenceActivePhysicalStep.step x).next := by
        calc
          next.state = r.output.next := hnextState
          _ = (ReferenceActivePhysicalStep.step x).next := by rw [hstep]
      refine ⟨next, hnextState', hnextRows, hnextSelected, hnextRewards, hnextLocalTime,
        ?_, ?_⟩
      · rw [hnextEq]
        exact hxready
      · intro hnext
        have hnextCount : j + 1 < count := by
          rw [← hrecordCount]
          exact hnext
        have hmatch := hnextRecord hnextCount
        simpa [epoch, w, window, j, hrecordCount] using hmatch
    have hboundary : x.time.val + 1 = p.T →
        ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
          (ReferenceActivePhysicalStep.step x).next payload finished actualLastProposal := by
      intro htimeT
      apply hboundaryReady
      simpa [ReferenceContinuingCollectionStartDomains.sourceRound] using htimeT
    have hFinishedPendingNonempty : finished.pending.Nonempty := by
      simpa [hfinishPending] using hReadyPending
    have hFinishedRegisterPending' := hFinishedRegisterPending
    refine ⟨?_⟩
    refine {
      filteredParse_alignment := rfl
      started_valid := by simpa [hl1Eq] using hvalidF
      started_phase := by simpa [hl1Eq] using hphaseF
      started_cursor := by simpa [hl1Eq] using hcursorF
      started_sigma := by simpa [hl1Eq] using hσF
      started_cutoff := by simpa [hl1Eq] using hcutF
      started_freezeAt := by simpa [hl1Eq] using hfreezeF
      started_pending := by simpa [hl1Eq] using hpendingF
      started_assignment := by simpa [hl1Eq] using hassignmentF
      started_baseScore := by simpa [hl1Eq] using hbaseF
      started_cutoffRegisters := by simpa [hl1Eq] using hcutregsF
      started_increment := by simpa [hl1Eq] using hincrementF
      started_register_pending := by simpa [hl1Eq] using hregistersF
      started_joint_and_span := by simpa [hl1Eq] using hmassF
      started_current_register_domain := by simpa [hl1Eq] using hcurrentF
      started_cutoff_register_domain := by simpa [hl1Eq] using hcutDomainF
      started_pending_zero := by simpa [hl1Eq] using hzeroF
      started_service_bounds := by simpa [hl1Eq] using hgammaF
      started_raw_entries := by simpa [hl1Eq] using hrawF
      started_enabled_history := by simpa [hl1Eq] using hhistoryF
      decoded := decoded
      bank := bank
      receiver_rejected := by simpa [hl1Eq] using hreceiver
      decoded_phase := by simpa [hl1Eq] using hdecodedPhase
      reception_input_domain := by simpa [hl1Eq] using hdomain
      reception_input_check := by simpa [hl1Eq] using hcheck
      receiver_diagnostic := by simpa [hl1Eq] using hdiagnostic
      finished := finished
      finish_success := by simpa [hl1Eq] using hfinish
      finish_candidate := by simpa [hl1Eq] using hfinishCandidate
      finished_increment := by simpa [hl1Eq] using hfinishIncrement
      finished_gammaLoc := hfinishGamma
      finished_cursor := hfinishCursor
      finished_phase := hfinishPhase
      finished_pending := hfinishPending
      finished_pending_nonempty := hFinishedPendingNonempty
      finished_assignment := hfinishAssignment
      finished_baseScore := hfinishBase
      finished_sigma := hFinishedSigma
      finished_cutoff := hFinishedCutoff
      finished_freezeAt := hFinishedFreeze
      finished_cutoffRegisters := hfinishCutoffRegisters
      finished_currentRegisters := by simpa [hl1Eq] using hfinishCurrentRegisters
      finished_rawBuffer := by simpa [hl1Eq] using hfinishRaw
      finished_enabledHistory := by simpa [hl1Eq] using hfinishHistory
      finished_register_pending := hFinishedRegisterPending'
      finished_cutoff_domain := hFinishedCutoffDomain
      finished_current_joint_and_span := by simpa [hl1Eq] using hfinishJoint
      finished_raw_entries := hfinishRawEntries
      finished_enabled_history := hfinishEnabledHistory
      finished_valid := hfinishValid
      clockFinished := clockFinished
      clock_finish_success := by simpa [hcStartedF] using hclockFinish
      clock_same := by simpa [hcStartedF] using hclockSame
      clock_pending := hclockPending
      clock_command := hclockCommand
      actualLastProposal := actualLastProposal
      actualLastProposal_eq := hlastProposal
      collection_finish_eq := hcollectionFinishR
      observe_coordinator_eq := hobserveR
      step_coordinator_eq := hstepCoordinator
      step_next_coordinator_eq := hstepNextCoordinator
      step_next_bank_eq := hstepNextBank
      step_next_activations_eq := hstepNextActivations
      step_followers_eq := hstepFollowers
      step_ownEntries_eq := hstepOwnEntries
      actual_record_failure_none := hfailure
      acceptedLabel_none := hacceptedLabel
      eraseEvent_recurrence := herase
      next_ready_prefix := hnextReadyPrefix
      boundary_ready := hboundary }
  refine ⟨hstep, htime, cutoff, hcutoff, core, snap, hb, hs, hcoord,
    c, o, started, hchoice, hrecording, hcpayload, hcpre, hcstarted, hcinit,
    hstart, hcandidate, hregisters, hOutput⟩

end Bandits.Support.ReferenceFirstCollectionRejectedReadyStep

end
