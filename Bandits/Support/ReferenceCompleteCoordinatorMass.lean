/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteAcceptedUpReplayBounds

import Lean.Elab.Tactic.Omega

/-!
# Coordinator numerical mass on the original complete suffix

Sources: `sources/zip4/manuscript/06_interruptions.tex:164-177,246-299,303-348,355-390`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

The public result follows the actual complete physical suffix and bounds the
coordinator's real incoming state and successor. The accepted-UP corollary
retains the decoder's actual replay list and its same-calendar endpoint.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCoordinatorMass

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open CoordinatorCollectionLedger
open ReferenceCollectionPhaseHistory
open ReferenceCollectionSegmentExtraction
open CollectionKnownQueueContinuation
open ReferenceAssignmentCollectionMassSteps

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal joint numerical invariant for an actual incoming coordinator
state. First has no installed numeric registers; its real dispatcher seed is
proved zero below. Dagger is deliberately not asserted to survive any test. -/
def coordinatorInputMass (x : RoundInput p rate) : Prop :=
  match x.state.coordinator with
  | .first => True
  | .live r q _ =>
      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        r.complementScores j + q.queue j ≤ x.time.val * D p) ∧
      q.previousServiceDomainValid
  | .collection _ l _ =>
      ∀ (a : Fin p.K) (cut : CutoffRegister) (current : CurrentRegister),
        l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
        cut.score + l.increment a + current.queue ≤ x.time.val * D p ∧
          cut.score + cut.queue ≤ (l.cutoff - 1) * D p ∧
          cut.lastService ≤ D p ∧ current.lastService ≤ D p
  | .dagger => True

/-- The literal joint numerical invariant for an actual coordinator successor
at calendar endpoint `e`. A first state is impossible after an actual round;
dagger remains an explicit branch with no survival assertion. -/
def coordinatorSuccessorMass (e : ℕ)
    (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Prop :=
  match configuration with
  | .first => False
  | .live r q _ =>
      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        r.complementScores j + q.queue j ≤ e * D p) ∧
      q.previousServiceDomainValid
  | .collection _ l _ =>
      ∀ (a : Fin p.K) (cut : CutoffRegister) (current : CurrentRegister),
        l.cutoffRegisters a = some cut → l.currentRegisters a = some current →
        cut.score + l.increment a + current.queue ≤ e * D p ∧
          cut.score + cut.queue ≤ (l.cutoff - 1) * D p ∧
          cut.lastService ≤ D p ∧ current.lastService ≤ D p
  | .dagger => True

private theorem choice_executedTail
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    unfold ReferenceCollectionPhaseHistory.executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction

/-- The successful filtered receiver branch is the physical accepted-UP event
consumed by the historical replay producer. -/
private theorem local_decode_accepted_up
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (recording : CoordinatorRecordingOperation.Output p)
    (started decoded : Ledger rate)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) = some recording)
    (hstart : startRound c.preLedger (x.time.val + 1)
      (collectionEnabled c.preLedger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started)
    (hreception : (receiveUp (prepare x) started).result ≠ .invalid)
    (U : UpRecord p rate)
    (hparsed : ReferenceCollectionSegmentExtraction.effectiveParse x started = some U)
    (hdecode : decodeUp started (upSenderIndex x) (some U) = .success decoded) :
    AcceptedUp x (upSenderIndex x) U := by
  refine ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩, recording, started, decoded,
    CoordinatorUpReception.decoderBankAfter
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (upInputs (prepare x) started) x.time),
    choice_executedTail x c hchoice, hrecord, hstart, ?_, hparsed, rfl⟩
  rw [ReferenceCollectionSegmentExtraction.receiveUp_filtered x started
    (ReferenceCollectionSegmentExtraction.receiveUp_input_check x started hreception),
    hparsed, hdecode]
  rfl

/-- The actual accepted-UP event supplies the frozen reply credit through the
one admitted public replay-prefix theorem, with no separate base or cutoff
assumption. -/
private theorem accepted_up_reply_credit_of_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : UpRecord p rate)
    (haccepted : AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
      U.val.delta ≤ D p := by
  obtain ⟨_b, _j, _F, _memory, _order, _pastIndex, _birth, _base, _retained,
    _input, _lastDown, _sigma, _ledgerSigma, _served, _delta, _queue, _followerMass,
    _followerDelta, hreply, hmessageDelta, _replay⟩ :=
    ReferenceCompleteAcceptedUpReplayBounds.complete_accepted_up_replay_prefix_credit
      rewards C_star C_h source k c hchoice i U haccepted
  exact ⟨hreply, hmessageDelta⟩

private theorem live_tail_mass
    (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j + owned.queue j ≤ x.time.val * D p) :
    match (livePostChoice (prepare x) r owned base started).configuration with
    | .live next queues _ =>
        (∀ j : CanonicalFastSampling.FastArm next.payload.slowSet,
          next.complementScores j + queues.queue j ≤ (x.time.val + 1) * D p) ∧
        queues.previousServiceDomainValid
    | .dagger => True
    | _ => False := by
  unfold livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (liveRecordingInput (prepare x) r started) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hservice : CoordinatorLiveServiceFinish.servicePass r owned recording with
      | error reason => trivial
      | ok serviced =>
          dsimp only
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (prepare x).coordinatorObservation with
          | none => trivial
          | some pending =>
              dsimp only
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => trivial
              | ok finished =>
                  dsimp only
                  exact ⟨live_service_mass r owned serviced x.time.val hcredit,
                    serviced.previousServiceDomain⟩

private theorem checked_round_cutoff
    (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw =
      .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished) : finished.cutoff = l.cutoff := by
  have hs := CollectionCheckedExecution.startRound_success_candidate l started
    (sourceRound input.round) input.enabled input.raw hstart
  have hf := CollectionCheckedExecution.finishRound_success_candidate decoded finished hfinish
  have hd : decoded.cutoff = started.cutoff := by
    rcases hdecode with hsuccess | hrejected
    · cases hp : input.parsed with
      | none =>
          simp only [hp, decodeUp] at hsuccess
          split at hsuccess
          · split at hsuccess <;> contradiction
          · contradiction
      | some U =>
          rw [hp] at hsuccess
          obtain ⟨_bound, _last, _source, _past, _current, _hpast, _hcurrent,
            _unknown, hcandidate⟩ :=
            CollectionCheckedExecution.decodeUp_success_candidate
              started decoded input.selectedFollower U hsuccess
          rw [hcandidate]
          rfl
    · rw [CollectionKnownQueueContinuation.decodeUp_rejected_candidate
        started decoded input.selectedFollower input.parsed hrejected]
  rw [hf]
  change decoded.cutoff = l.cutoff
  rw [hd, hs]
  rfl

/-- Every checked collection tail preserves the joint mass for all present
pairs. Its actual reply event is decoded from the filtered reception and is
then consumed by the public accepted-UP replay-prefix theorem. -/
private theorem collection_tail_mass
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hcredit : ∀ (a : Fin p.K) (cutoff : CutoffRegister) (current : CurrentRegister),
      c.preLedger.cutoffRegisters a = some cutoff →
      c.preLedger.currentRegisters a = some current →
      cutoff.score + c.preLedger.increment a + current.queue ≤ x.time.val * D p ∧
        cutoff.score + cutoff.queue ≤ (c.preLedger.cutoff - 1) * D p ∧
        cutoff.lastService ≤ D p)
    (hreply : ∀ (i : Fin (p.m - 1)) (U : UpRecord p rate),
      AcceptedUp x i U →
      c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
        U.val.delta ≤ D p) :
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection _ final _ =>
        ∀ (a : Fin p.K) (cutoff : CutoffRegister) (current : CurrentRegister),
          final.cutoffRegisters a = some cutoff → final.currentRegisters a = some current →
          cutoff.score + final.increment a + current.queue ≤ (x.time.val + 1) * D p ∧
            cutoff.score + cutoff.queue ≤ (final.cutoff - 1) * D p ∧
            cutoff.lastService ≤ D p ∧ current.lastService ≤ D p
    | .dagger => True
    | _ => False := by
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecode := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecode ⊢
              cases hfinish : finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hd : decodeUp started input.selectedFollower input.parsed =
                          .success decoded ∨
                          decodeUp started input.selectedFollower input.parsed =
                            .rejected decoded := by
                        first | exact Or.inl hdecode | exact Or.inr hdecode
                      have hcutoff := checked_round_cutoff c.preLedger started decoded finished
                        input hstart hd hfinish
                      rw [hcutoff]
                      apply collection_round_mass c.preLedger started decoded finished input
                        hcredit ?_ hstart hd hfinish
                      intro U hparsed hsuccess
                      apply hreply (upSenderIndex x) U
                      exact local_decode_accepted_up x c hchoice recording started decoded
                        hrecord hstart (by rw [hreceive]; intro h; cases h) U
                        (by
                          simpa only [input, ReferenceCollectionSegmentExtraction.inputOf]
                            using hparsed)
                        hsuccess

private theorem coordinator_round_mass
    (x : RoundInput p rate)
    (hlive : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
      x.state.coordinator = .live r q base →
      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        r.complementScores j + q.queue j ≤ x.time.val * D p) ∧
      q.previousServiceDomainValid)
    (hcollection : ∀ (P : Payload rate) (l : Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved →
      ∀ (a : Fin p.K) (cutoff : CutoffRegister) (current : CurrentRegister),
        l.cutoffRegisters a = some cutoff → l.currentRegisters a = some current →
        cutoff.score + l.increment a + current.queue ≤ x.time.val * D p ∧
          cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
          cutoff.lastService ≤ D p ∧ current.lastService ≤ D p)
    (hreply : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice x = some c →
      ∀ (i : Fin (p.m - 1)) (U : UpRecord p rate),
        AcceptedUp x i U →
        c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
          U.val.delta ≤ D p) :
    coordinatorSuccessorMass (x.time.val + 1)
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration := by
  classical
  unfold coordinatorSuccessorMass
  by_cases hselected : (prepare x).coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases (prepare x).coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : (prepare x).coordinator = dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
        | choiceDomainFailure installed => trivial
        | recorderBoundaryFailure installed => trivial
        | choiceRejected installed => trivial
        | chosen installed selected =>
            obtain ⟨hscores, hqueues, _hprevious, _hbase⟩ :=
              dispatchFirst_zero_seed x installed selected ho
            have ht := live_tail_mass x installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult (by
                intro j
                rw [hscores j, hqueues j, Nat.zero_add]
                exact Nat.zero_le _)
            split at ht <;> simp_all only [implies_true, and_true]
    | live r q base =>
        have hcut : (prepare x).coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        obtain ⟨hmass, hprevious⟩ := hlive r q base hconfiguration
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have ht := live_tail_mass x (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
            base dispatched.startResult hmass
          split at ht <;> simp_all only [implies_true, and_true]
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨r.payload, sharedLedger ledger, dispatched.startResult,
              (liveRegistersAt r x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [ite_eq_right hselected, hcut, ho]
            rfl
          have hcredit := collection_start_mass (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base x.time hmass hprevious
          have hledger : c.preLedger = sharedLedger
              (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time) := by
            dsimp only [c]
            rw [hcandidate]
            rfl
          have ht := collection_tail_mass x c hchoice (by
            intro a cutoff current hc hq
            rw [hledger] at hc hq ⊢
            obtain ⟨hcurrent, hfrozen, hlast, _hprevious⟩ := hcredit a cutoff current hc hq
            exact ⟨hcurrent, hfrozen, hlast⟩) (hreply c hchoice)
          split at ht <;> simp_all only [c, implies_true, true_and]
          intro a cut current hc hq
          exact (ht a cut current hc hq).2
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : (prepare x).coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_left hcutoff,
              CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (collectionInput x old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            let c : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨old, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (collectionInput x old ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
              unfold ReferenceCollectionSegmentExtraction.choice
              rw [ite_eq_right hselected, hcut, ho]
              rfl
            have ht := collection_tail_mass x c hchoice (by
              intro a cut current hc hq
              obtain ⟨hmass, hfrozen, hlast, _hprevious⟩ :=
                hcollection old ledger saved hconfiguration a cut current hc hq
              exact ⟨hmass, hfrozen, hlast⟩) (hreply c hchoice)
            split at ht <;> simp_all only [c, implies_true, true_and]
            intro a cut current hc hq
            exact (ht a cut current hc hq).2
          case laterChosen core consistent started hstart instruction hinstruction output
              hlocal clockData installed selected =>
            have hprovenance :=
              ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
            rw [← hactual, hcut, ho] at hprovenance
            obtain ⟨hinstalled, _payload, _sigma, _down⟩ := hprovenance
            have fields := CoordinatorRoundDispatch.collectionOperationLedger_fields
              (collectionInput x old ledger clock cutoff) core.payload_n_eq
            obtain ⟨_assignment, _startSigma, _cut, _freeze, _base, _pending,
              hcutoffRegisters, hcurrentRegisters, hincrement, _other⟩ := fields
            have htime := later_instruction_time x old ledger clock cutoff core
              started instruction hstart hinstruction
            have hoperation : ∀ (a : Fin p.K) (c : CutoffRegister)
                (q : CurrentRegister),
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).cutoffRegisters a =
                    some c →
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).currentRegisters a =
                    some q →
                c.score + (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).increment a +
                    q.queue ≤ instruction.time.val * D p := by
              intro a c q hc hq
              rw [hcutoffRegisters] at hc
              rw [hcurrentRegisters] at hq
              rw [hincrement, htime]
              exact (hcollection old ledger saved hconfiguration a c q hc hq).1
            obtain ⟨_queues, hmass, _followers, _downCredit⟩ :=
              later_installation_mass output clockData hoperation
            subst installed
            have hsigma : (CoordinatorAssignmentRegisterInstall.installLater
                output clockData).registers.payload.sigma.val = x.time.val := by
              change output.payload.sigma.val = x.time.val
              rw [output.payload_start, htime]
            have ht := live_tail_mass x
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore
              started (by
                intro j
                exact (hmass j).trans_eq
                  (congrArg (fun n : ℕ => n * D p) hsigma))
            split at ht <;> simp_all only [implies_true, and_true]
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (h : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (h : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at h; omega
          | cons next tail => exact hconnected.2.1
      | succ n =>
          exact ih hconnected.2 n (by simp only [List.length_cons] at h; omega)

/-- Every original-source suffix record satisfies the actual incoming joint
mass, and its computed coordinator successor satisfies the corresponding
joint mass at the next calendar endpoint. The first dispatch is established
from its zero seed; dagger remains explicit in both matches. -/
theorem complete_coordinator_input_output_mass
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ k : Fin R.length,
      coordinatorInputMass (R[k.val]'k.isLt).input ∧
      coordinatorSuccessorMass ((R[k.val]'k.isLt).input.time.val + 1)
        (R[k.val]'k.isLt).output.next.coordinator := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  intro k
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hconnected :=
        ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate source rewards C_star C_h initial hcanonical
      have hfold : ∀ n (hn : n < R.length),
          coordinatorInputMass R[n].input ∧
          coordinatorSuccessorMass (R[n].input.time.val + 1)
            R[n].output.next.coordinator := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            refine ⟨?_, ?_⟩
            · unfold coordinatorInputMass
              rw [hstate, seed.coordinatorFirst]
              trivial
            · have hlive : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                  (base : Fin (p.m - 1) → ℕ),
                  R[0].input.state.coordinator = .live r q base →
                  (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                    r.complementScores j + q.queue j ≤ R[0].input.time.val * D p) ∧
                    q.previousServiceDomainValid := by
                intro r q base hconfiguration
                rw [hstate, seed.coordinatorFirst] at hconfiguration
                cases hconfiguration
              have hcollection : ∀ (P : Payload rate) (l : Ledger rate)
                  (saved : Option (Fin p.T × Bool)),
                  R[0].input.state.coordinator = .collection P l saved →
                  ∀ (a : Fin p.K) (cutoff : CutoffRegister)
                    (current : CurrentRegister),
                    l.cutoffRegisters a = some cutoff →
                    l.currentRegisters a = some current →
                    cutoff.score + l.increment a + current.queue ≤ R[0].input.time.val * D p ∧
                      cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
                      cutoff.lastService ≤ D p ∧ current.lastService ≤ D p := by
                intro P l saved hconfiguration
                rw [hstate, seed.coordinatorFirst] at hconfiguration
                cases hconfiguration
              have hreply : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
                  ReferenceCollectionSegmentExtraction.choice R[0].input = some c →
                  ∀ (i : Fin (p.m - 1)) (U : UpRecord p rate),
                    AcceptedUp R[0].input i U →
                    c.preLedger.baseScore i + U.val.S + U.val.q ≤
                        (c.preLedger.cutoff - 1) * D p ∧ U.val.delta ≤ D p := by
                intro c hchoice i U haccepted
                exact accepted_up_reply_credit_of_replay rate rewards C_star C_h source
                  ⟨0, by omega⟩ c hchoice i U haccepted
              have hstep := coordinator_round_mass R[0].input hlive hcollection hreply
              have houtput : coordinatorSuccessorMass (R[0].input.time.val + 1)
                  R[0].output.next.coordinator =
                    coordinatorSuccessorMass (R[0].input.time.val + 1)
                      (prepare R[0].input).observeCoordinator.configuration := by
                rw [R[0].output_eq]
                rfl
              rw [houtput]
              exact hstep
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            let prior : Fin R.length := ⟨n, hnprev⟩
            have htime : R[n + 1].input.time.val = R[n].input.time.val + 1 := by
              have hprev := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source prior
              have hnext := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n + 1, hn⟩
              change R[n].input.time.val = _ + n at hprev
              change R[n + 1].input.time.val = _ + (n + 1) at hnext
              omega
            obtain ⟨hinput, _houtput⟩ := ih hnprev
            have hlive : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                (base : Fin (p.m - 1) → ℕ),
                R[n].input.state.coordinator = .live r q base →
                (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                  r.complementScores j + q.queue j ≤ R[n].input.time.val * D p) ∧
                q.previousServiceDomainValid := by
              intro r q base hconfiguration
              have h := hinput
              unfold coordinatorInputMass at h
              rw [hconfiguration] at h
              exact h
            have hcollection : ∀ (P : Payload rate) (l : Ledger rate)
                (saved : Option (Fin p.T × Bool)),
                R[n].input.state.coordinator = .collection P l saved →
                ∀ (a : Fin p.K) (cutoff : CutoffRegister)
                  (current : CurrentRegister),
                  l.cutoffRegisters a = some cutoff → l.currentRegisters a = some current →
                  cutoff.score + l.increment a + current.queue ≤ R[n].input.time.val * D p ∧
                    cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
                    cutoff.lastService ≤ D p ∧ current.lastService ≤ D p := by
              intro P l saved hconfiguration
              have h := hinput
              unfold coordinatorInputMass at h
              rw [hconfiguration] at h
              exact h
            have hreply : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
                ReferenceCollectionSegmentExtraction.choice R[n].input = some c →
                ∀ (i : Fin (p.m - 1)) (U : UpRecord p rate),
                  AcceptedUp R[n].input i U →
                  c.preLedger.baseScore i + U.val.S + U.val.q ≤
                      (c.preLedger.cutoff - 1) * D p ∧ U.val.delta ≤ D p := by
              intro c hchoice i U haccepted
              exact accepted_up_reply_credit_of_replay rate rewards C_star C_h source prior
                c hchoice i U haccepted
            have hstep := coordinator_round_mass R[n].input hlive hcollection hreply
            have houtput : coordinatorSuccessorMass (R[n].input.time.val + 1)
                R[n].output.next.coordinator =
                  coordinatorSuccessorMass (R[n].input.time.val + 1)
                    (prepare R[n].input).observeCoordinator.configuration := by
              rw [R[n].output_eq]
              rfl
            rw [← houtput] at hstep
            have hstate := connected_succ_input hconnected n hn
            have hnextInput : coordinatorInputMass R[n + 1].input := by
              unfold coordinatorInputMass
              rw [hstate, htime]
              cases hconfiguration : R[n].output.next.coordinator with
              | first => trivial
              | live r q base =>
                  simpa only [coordinatorSuccessorMass, hconfiguration] using hstep
              | collection payload ledger saved =>
                  simpa only [coordinatorSuccessorMass, hconfiguration] using hstep
              | dagger => trivial
            let next : Fin R.length := ⟨n + 1, hn⟩
            have hliveNext : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                (base : Fin (p.m - 1) → ℕ),
                R[n + 1].input.state.coordinator = .live r q base →
                (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                  r.complementScores j + q.queue j ≤
                    R[n + 1].input.time.val * D p) ∧ q.previousServiceDomainValid := by
              intro r q base hconfiguration
              have h := hnextInput
              unfold coordinatorInputMass at h
              rw [hconfiguration] at h
              exact h
            have hcollectionNext : ∀ (P : Payload rate) (l : Ledger rate)
                (saved : Option (Fin p.T × Bool)),
                R[n + 1].input.state.coordinator = .collection P l saved →
                ∀ (a : Fin p.K) (cutoff : CutoffRegister)
                  (current : CurrentRegister),
                  l.cutoffRegisters a = some cutoff →
                  l.currentRegisters a = some current →
                  cutoff.score + l.increment a + current.queue ≤
                      R[n + 1].input.time.val * D p ∧
                    cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
                    cutoff.lastService ≤ D p ∧ current.lastService ≤ D p := by
              intro P l saved hconfiguration
              have h := hnextInput
              unfold coordinatorInputMass at h
              rw [hconfiguration] at h
              exact h
            have hreplyNext : ∀ (choice : ReferenceCollectionSegmentExtraction.Choice rate),
                ReferenceCollectionSegmentExtraction.choice R[n + 1].input = some choice →
                ∀ (i : Fin (p.m - 1)) (U : UpRecord p rate),
                  AcceptedUp R[n + 1].input i U →
                  choice.preLedger.baseScore i + U.val.S + U.val.q ≤
                      (choice.preLedger.cutoff - 1) * D p ∧ U.val.delta ≤ D p := by
              intro choice hchoice i U haccepted
              exact accepted_up_reply_credit_of_replay rate rewards C_star C_h source next
                choice hchoice i U haccepted
            have hstepNext := coordinator_round_mass R[n + 1].input
              hliveNext hcollectionNext hreplyNext
            have houtputNext :
                coordinatorSuccessorMass (R[n + 1].input.time.val + 1)
                    R[n + 1].output.next.coordinator =
                  coordinatorSuccessorMass (R[n + 1].input.time.val + 1)
                    (prepare R[n + 1].input).observeCoordinator.configuration := by
              rw [R[n + 1].output_eq]
              rfl
            rw [houtputNext]
            exact ⟨hnextInput, hstepNext⟩
      exact hfold k.val k.isLt

/-- On an actual accepted-UP branch, expose the exact checked decoder's past
list, current record, decoded registers, and first update. These are the same
witnesses as the admitted replay theorem; no independent candidate or queue
trace is introduced. -/
theorem complete_accepted_up_decoded_numerical_mass
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : UpRecord p rate)
    (haccepted : AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let x := (R[k.val]'k.isLt).input
    ∃ (started decoded : Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
      (hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T)
      (lastIndex : Fin p.T) (past : List (Bool × ℕ)) (currentRecord : Bool × ℕ)
      (cutoff : CutoffRegister) (current : CurrentRegister),
      (receiveUp (prepare x) started).result = .success (decoded, bank) ∧
      filteredParsed x started = some U ∧ effectiveParse x started = some U ∧
      decodeUp started i (some U) = .success decoded ∧
      started.assignment = c.preLedger.assignment ∧
      started.baseScore = c.preLedger.baseScore ∧
      started.cutoff = c.preLedger.cutoff ∧ started.cursor = x.time.val + 1 ∧
      lastIndex = x.time ∧
      replayRecords? started (started.assignment.arm i)
        (calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound) = some past ∧
      replayRecords? started (started.assignment.arm i) [lastIndex] =
        some [currentRecord] ∧
      (∀ record ∈ past ++ [currentRecord], record.2 ≤ D p) ∧
      (past ++ [currentRecord]).length =
        x.time.val + 1 - c.preLedger.cutoff + 1 ∧
      decoded.cutoffRegisters (started.assignment.arm i) = some cutoff ∧
      decoded.currentRegisters (started.assignment.arm i) = some current ∧
      decoded.increment (started.assignment.arm i) =
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          (past ++ [currentRecord])).1 ∧
      cutoff.score + decoded.increment (started.assignment.arm i) + current.queue ≤
        (x.time.val + 1) * D p ∧
      cutoff.score + cutoff.queue ≤ (c.preLedger.cutoff - 1) * D p ∧
      cutoff.lastService ≤ D p ∧ current.lastService ≤ D p ∧
      started.gammaLoc (started.assignment.arm i) = 0 := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := (R[k.val]'k.isLt).input
  obtain ⟨_b, _j, _F, _memory, _order, _pastIndex, _birth, _base, _retained,
    _input, _lastDown, _sigma, _ledgerSigma, _served, _delta, _queue, _followerMass,
    _followerDelta, _reply, _messageDelta,
    htailData⟩ :=
    ReferenceCompleteAcceptedUpReplayBounds.complete_accepted_up_replay_prefix_credit
      rewards C_star C_h source k c hchoice i U haccepted
  rcases htailData with
    ⟨tail, recording, started, decoded, bank, _executed, _tailEq, _recording,
      _start, hstartedAssignment, hstartedBase, hreceive, hfiltered, heffective,
      hdecode, hdata⟩
  rcases hdata with
    ⟨hbound, hcutoff, hcursor, _cutoffPositive, _cutoffCurrent, _endpoint,
      hindexData⟩
  rcases hindexData with ⟨lastIndex, hindexData⟩
  rcases hindexData with ⟨hlastIndex, hrecordsData⟩
  rcases hrecordsData with
    ⟨past, currentRecord, hpast, hcurrentRecord, hcaps, hlength,
      _emptyQueue, _emptyLast, _baseBound, _queueBound, _deltaBound, _prefix,
      hdecodedCurrent, hdecodedIncrement, hdecodedCutoff, _pending,
      _startedCurrent, _startedCutoff, hgamma, hjoint, hcutBudget, hcurrentService⟩
  let arm := started.assignment.arm i
  let cutoff : CutoffRegister := ⟨c.preLedger.baseScore i + U.val.S,
    U.val.q, U.val.delta⟩
  let current : CurrentRegister := ⟨
    (QueueReplay.replay (4 * rate.n) (0, U.val.q) (past ++ [currentRecord])).2,
    (QueueReplay.replay (4 * rate.n) (0, U.val.q) (past ++ [currentRecord])).1 -
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) past).1⟩
  have hcutoffRegisters : decoded.cutoffRegisters arm = some cutoff := by
    simpa only [arm, cutoff] using hdecodedCutoff
  have hcurrentRegisters : decoded.currentRegisters arm = some current := by
    simpa only [arm, current] using hdecodedCurrent
  have hdecodedIncrement' : decoded.increment arm =
      (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        (past ++ [currentRecord])).1 := by
    simpa only [arm] using hdecodedIncrement
  have hmass : cutoff.score + decoded.increment arm + current.queue ≤
      (x.time.val + 1) * D p := by
    calc
      cutoff.score + decoded.increment arm + current.queue =
          c.preLedger.baseScore i + U.val.S + decoded.increment arm +
            (QueueReplay.replay (4 * rate.n) (0, U.val.q)
              (past ++ [currentRecord])).2 := rfl
      _ ≤ started.cursor * D p := hjoint
      _ = (x.time.val + 1) * D p := by rw [hcursor]
  have hcutBudget' : cutoff.score + cutoff.queue ≤
      (c.preLedger.cutoff - 1) * D p := by
    simpa only [cutoff, CutoffRegister.score, CutoffRegister.queue] using hcutBudget
  have hcutLast : cutoff.lastService ≤ D p := by
    simpa only [cutoff, CutoffRegister.lastService] using _deltaBound
  have hcurrentLast : current.lastService ≤ D p := by
    simpa only [current, CurrentRegister.lastService] using hcurrentService
  exact ⟨started, decoded, bank, hbound, lastIndex, past, currentRecord, cutoff, current,
    hreceive, hfiltered, heffective, hdecode, hstartedAssignment, hstartedBase,
    hcutoff, hcursor, hlastIndex, hpast,
    hcurrentRecord, hcaps, hlength, hcutoffRegisters, hcurrentRegisters,
    hdecodedIncrement', hmass, hcutBudget', hcutLast, hcurrentLast, hgamma⟩

end Bandits.Support.ReferenceCompleteCoordinatorMass

end
