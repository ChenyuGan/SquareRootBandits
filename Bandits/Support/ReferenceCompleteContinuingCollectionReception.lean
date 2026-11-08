/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionUpDecodeDomains
public import Bandits.Support.ReferenceCompleteContinuingCollectionStart

import Lean.Elab.Tactic.Omega

/-!
# Actual continuing collection reception and FINISH

This module composes one actual continuing-collection choice on the complete
physical suffix with its checked recorder, ledger START, filtered UP
reception, ledger FINISH, and original phase-clock FINISH. Replay and candidate
checks are derived from the same START and local acceptance; no successful
receiver result, truthful physical message, score law, or queue law is an input.

Mathematical source: `sources/zip4/manuscript/06_interruptions.tex:64-100,164-177,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-177`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteContinuingCollectionReception

open ConstructorDimensions
open ReferenceActivePhysicalStep
open CoordinatorCollectionLedger
open ReferenceCollectionSegmentExtraction
open CoordinatorPhaseClock

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro hall i
    exact hall (test i) (by simp)
  · intro hall value hvalue
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hvalue
    subst value
    exact hall i

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem validLedger_pending_register_checks
    (l : Ledger rate) (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true) :
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.currentRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true ∧
    CoordinatorCollectionLedger.allFin p.K (fun a =>
      (l.cutoffRegisters a).isNone == CoordinatorCollectionLedger.armPendingCheck l a) = true := by
  have hparts := hvalid
  simp [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hparts
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, _⟩
  rcases hparts with ⟨hparts, hcutoffPending⟩
  rcases hparts with ⟨_, hcurrentPending⟩
  exact ⟨hcurrentPending, hcutoffPending⟩

private theorem actual_choice_continuing_snapshot
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (c : Choice rate)
    (hstate : x.state.coordinator = .collection P l saved)
    (hchoice : choice x = some c) :
    ∃ (cutoff : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
      (core : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff))
      (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff))
      (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
        (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) = true),
      CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) =
        .continuing core snapshot boundary scores ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection P l clock cutoff (.continuing core snapshot boundary scores) ∧
      c = ⟨P, l, snapshot.clockStarted,
        CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff)
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
        none⟩ ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator.arm = snapshot.arm := by
  classical
  have hcutoffDomain : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    by_contra hbad
    have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hbad,
        ReferenceActivePhysicalStep.DispatchCut.selection]
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    simp [hcut] at hchoice
  let cutoff : Fin p.T := ⟨l.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock P l saved cutoff
  have hchoiceCut :
      ReferenceCollectionSegmentExtraction.choiceOfCut
        (ReferenceActivePhysicalStep.prepare x).coordinator = some c := by
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    by_cases hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
    · simp [hselection] at hchoice
    · simpa [hselection] using hchoice
  have hpreparedDispatch : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection P l clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff)) := by
    simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      CoordinatorRoundDispatch.dispatch, hstate, hcutoffDomain, cutoff, clock]
    rfl
  rw [hpreparedDispatch] at hchoiceCut
  cases houtcome : CoordinatorRoundDispatch.dispatchCollection
      (ReferenceActivePhysicalStep.collectionInput x P l clock cutoff) with
  | continuing core snapshot boundary scores =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, houtcome] at hchoiceCut
      have hchoiceEq := Option.some.inj hchoiceCut
      have hpreparedContinue : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .collection P l clock cutoff (.continuing core snapshot boundary scores) := by
        rw [hpreparedDispatch, houtcome]
      have harm : (ReferenceActivePhysicalStep.prepare x).coordinator.arm = snapshot.arm := by
        rw [hpreparedContinue]
        simp [ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.selection]
      exact ⟨cutoff, clock, core, snapshot, boundary, scores,
        houtcome, hpreparedContinue, hchoiceEq.symm, harm⟩
  | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, houtcome] at hchoiceCut

private theorem actual_filtered_receive_noninvalid
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (_hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection P l saved)
    (c : Choice rate)
    (hchoice : choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (o : CoordinatorRecordingOperation.Output p)
    (started : Ledger rate)
    (hstart : CoordinatorCollectionLedger.startRound c.preLedger
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt |>.input).time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt |>.input).time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success started)
    (hinput : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt |>.input).row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt |>.input)) started)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt |>.input).time) = true) :
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
    let prepared := ReferenceActivePhysicalStep.prepare x
    let input := ReferenceUpReception.receptionInputAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared started) x.time
    ∃ decoded,
      (ReferenceActivePhysicalStep.receiveUp prepared started).result =
        .success (decoded, CoordinatorUpReception.decoderBankAfter input) ∨
      (ReferenceActivePhysicalStep.receiveUp prepared started).result =
        .rejected (decoded, CoordinatorUpReception.decoderBankAfter input) := by
  classical
  dsimp only
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  have hxInput : x = ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input := rfl
  let prepared := ReferenceActivePhysicalStep.prepare x
  let input := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs prepared started) x.time
  let parsed := ReferenceCollectionSegmentExtraction.effectiveParse x started
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  have hreceivePacked := ReferenceCollectionSegmentExtraction.receiveUp_filtered
    x started (by simpa [x, prepared] using hinput)
  have hdomain : CoordinatorUpReception.receptionInputDomain input :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hinput
  have hledger : input.ledger = started := rfl
  have hselected : input.selectedFollower = i := rfl
  obtain ⟨hvalid, _hsigma, hphase, hcut, hcutCursor, hcursorT, _htime, _hbank⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts input hdomain
  have hdecodeInput : CoordinatorCollectionLedger.validLedgerCheck started = true ∧
      started.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧ started.cursor ≤ p.T :=
    ⟨by simpa [hledger] using hvalid, by simpa [hledger] using hphase,
      by simpa [hledger] using hcut, by simpa [hledger] using hcutCursor,
      by simpa [hledger] using hcursorT⟩
  cases hparsed : parsed with
  | none =>
      have hparsedEffective : ReferenceCollectionSegmentExtraction.effectiveParse x started = none := by
        simpa [parsed] using hparsed
      have hdecode := CoordinatorUpReception.decodeUp_none_rejected input hdomain
      have hdecodeStarted : CoordinatorCollectionLedger.decodeUp started
          (ReferenceActivePhysicalStep.upSenderIndex x) none =
          .rejected {started with phase := CoordinatorCollectionLedger.Phase.decoded} := by
        simpa [hledger, hselected, i] using hdecode
      refine ⟨{started with phase := CoordinatorCollectionLedger.Phase.decoded}, ?_⟩
      right
      rw [hreceivePacked, hparsedEffective]
      simp [CoordinatorUpReception.packDecodeResult, hdecodeStarted, x]
  | some U =>
      cases haccept : CoordinatorCollectionLedger.acceptUpCheck started i U with
      | false =>
          have hparsedEffective : ReferenceCollectionSegmentExtraction.effectiveParse x started = some U := by
            simpa [parsed] using hparsed
          have hnot : ¬ CoordinatorCollectionLedger.acceptUpCheck started i U := by
            simp [haccept]
          have hdecode := CoordinatorUpReception.decodeUp_unaccepted_rejected
            input hdomain U hnot
          have hdecodeStarted : CoordinatorCollectionLedger.decodeUp started
              (ReferenceActivePhysicalStep.upSenderIndex x) (some U) =
              .rejected {started with phase := CoordinatorCollectionLedger.Phase.decoded} := by
            simpa [hledger, hselected, i] using hdecode
          refine ⟨{started with phase := CoordinatorCollectionLedger.Phase.decoded}, ?_⟩
          right
          rw [hreceivePacked, hparsedEffective]
          simp [CoordinatorUpReception.packDecodeResult, hdecodeStarted, x]
      | true =>
          have hdomains :=
            ReferenceCompleteCollectionUpDecodeDomains.complete_filtered_up_decode_domains
              rate rewards C_star C_h source k c hchoice o started hstart U hparsed haccept
          dsimp only at hdomains
          rcases hdomains with ⟨hs, hc, past, current, hpast, hcurrent, hlength,
            houtputDomains, hcandidateValid, _hmass, _hdifference, _hcapacity⟩
          rw [← hxInput] at hpast hcurrent hcandidateValid
          let iActual := ReferenceActivePhysicalStep.upSenderIndex x
          let arm := started.assignment.arm iActual
          have hacceptParts := haccept
          simp only [CoordinatorCollectionLedger.acceptUpCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hacceptParts
          rcases hacceptParts with ⟨_hcutoffLeCursor, hpending, _hsigma⟩
          have hpendingArm : CoordinatorCollectionLedger.armPending started arm :=
            ⟨iActual, hpending, rfl⟩
          have hregisters := validLedger_pending_register_checks started hvalid
          have hcurrentBool :=
            (allFin_eq_true_iff _).1 hregisters.1 arm
          have hcutoffBool :=
            (allFin_eq_true_iff _).1 hregisters.2 arm
          have hcurrentRel : (started.currentRegisters arm).isNone =
              CoordinatorCollectionLedger.armPendingCheck started arm := by
            simpa only [beq_iff_eq] using hcurrentBool
          have hcutoffRel : (started.cutoffRegisters arm).isNone =
              CoordinatorCollectionLedger.armPendingCheck started arm := by
            simpa only [beq_iff_eq] using hcutoffBool
          have hpendingCheck :=
            (armPendingCheck_eq_true_iff started arm).2 hpendingArm
          have hcurrentNone : started.currentRegisters arm = none := by
            have hnone : (started.currentRegisters arm).isNone = true :=
              hcurrentRel.trans hpendingCheck
            cases hreg : started.currentRegisters arm with
            | none => rfl
            | some value => simp [hreg] at hnone
          have hcutoffNone : started.cutoffRegisters arm = none := by
            have hnone : (started.cutoffRegisters arm).isNone = true :=
              hcutoffRel.trans hpendingCheck
            cases hreg : started.cutoffRegisters arm with
            | none => rfl
            | some value => simp [hreg] at hnone
          have hdecode : CoordinatorCollectionLedger.decodeUp started
              (ReferenceActivePhysicalStep.upSenderIndex x)
              (some U) = .success
                (CoordinatorCollectionLedger.acceptUpCandidate started
                  (ReferenceActivePhysicalStep.upSenderIndex x) U past current) := by
            unfold CoordinatorCollectionLedger.decodeUp
            rw [dite_eq_left hdecodeInput]
            have hacceptRaw : CoordinatorCollectionLedger.acceptUpCheck started
                (ReferenceActivePhysicalStep.upSenderIndex x) U = true := by
              simpa [i] using haccept
            have hunknownRaw : started.currentRegisters
                (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) = none ∧
                started.cutoffRegisters
                (started.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x)) = none := by
              simpa [arm, iActual] using ⟨hcurrentNone, hcutoffNone⟩
            simp only [hacceptRaw, hunknownRaw]
            simp [hpast, hcurrent, houtputDomains, hcandidateValid]
          refine ⟨CoordinatorCollectionLedger.acceptUpCandidate started
            (ReferenceActivePhysicalStep.upSenderIndex x) U past current, ?_⟩
          left
          rw [hreceivePacked]
          have hparsedEffective : ReferenceCollectionSegmentExtraction.effectiveParse x started = some U := by
            simpa [parsed] using hparsed
          rw [hparsedEffective]
          simp [CoordinatorUpReception.packDecodeResult, hdecode, x]

/-- One actual continuing-collection reception and both FINISH operations on
one record of the complete physical suffix. All local inputs are produced in
this proof from the same successful choice and PREPARE. The returned bank is
exactly the same-row decoder transition, and the final observation preserves
its complete diagnostic and all ledger/clock output fields.
-/
theorem actual_continuing_collection_reception_finish
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
    ∀ (P : Payload rate) (l : Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved →
      ∀ (c : Choice rate), choice x = some c →
      ∃ (o : CoordinatorRecordingOperation.Output p) (started decoded : Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p)
        (finished : Ledger rate)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        c.payload = P ∧ c.preLedger = l ∧ c.initializer = none ∧
        CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o ∧
        CoordinatorCollectionLedger.rawSlotFreshCheck l x.time
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = true ∧
        CoordinatorCollectionLedger.startRound l (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled l x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
            .success started ∧
        CoordinatorCollectionLedger.validLedgerCheck started = true ∧
        started.phase = CoordinatorCollectionLedger.Phase.started ∧
        started.cursor = x.time.val + 1 ∧
        1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
        started.cursor ≤ p.T ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time) = true ∧
        ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, bank) ∨
         (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) started).result = .rejected (decoded, bank)) ∧
        bank = CoordinatorUpReception.decoderBankAfter
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare x) started) x.time) ∧
        CoordinatorUpReception.decoderBankWellFormed p bank ∧
        CoordinatorUpReception.decoderBankCheck p bank = true ∧
        (∀ follower, follower ≠ ReferenceActivePhysicalStep.upSenderIndex x →
          bank follower = x.state.upDecoderBank follower) ∧
        CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
        finished = CoordinatorCollectionLedger.finishRoundCandidate decoded ∧
        CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
        finished.phase = CoordinatorCollectionLedger.Phase.ready ∧
        finished.cursor = x.time.val + 2 ∧
        (∀ a, finished.increment a = decoded.increment a + decoded.gammaLoc a ∧
          finished.gammaLoc a = 0) ∧
        finished.assignment = decoded.assignment ∧ finished.sigma = decoded.sigma ∧
        finished.cutoff = decoded.cutoff ∧ finished.freezeAt = decoded.freezeAt ∧
        finished.baseScore = decoded.baseScore ∧ finished.pending = decoded.pending ∧
        finished.cutoffRegisters = decoded.cutoffRegisters ∧
        finished.currentRegisters = decoded.currentRegisters ∧
        finished.rawBuffer = decoded.rawBuffer ∧
        finished.enabledHistory = decoded.enabledHistory ∧
        CoordinatorPhaseClock.clockRegistersValid p rate.eta.val c.started.clock ∧
        c.started.clock.sigma = some P.sigma ∧
        ∃ cutoff : Fin p.T, c.started.clock.u = some cutoff ∧
          cutoff.val ≤ x.time.val ∧
          CoordinatorPhaseClock.startRoundTimeValid p x.time c.started.clock ∧
          CoordinatorPhaseClock.finishRoundTimeValid x.time c.started.clock ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val x.time c.started.clock
            finished.pending x.row = .ok clockFinished ∧
        (ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights =
            ⟨.collection P finished clockFinished.clock.lastProposal, bank, none,
              some o, (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) started).diagnostic⟩) ∧
        (ReferenceActivePhysicalStep.collectionFinish
          (x := x) P c.started o
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started) =
            ⟨.collection P finished clockFinished.clock.lastProposal, bank, none,
              some o, (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) started).diagnostic⟩) ∧
        ((ReferenceActivePhysicalStep.prepare x).observeCoordinator =
            ⟨.collection P finished clockFinished.clock.lastProposal, bank, none,
              some o, (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) started).diagnostic⟩) ∧
        ((ReferenceActivePhysicalStep.receiveUp
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
            wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
              rate x.row (ReferenceActivePhysicalStep.upInputs
                (ReferenceActivePhysicalStep.prepare x) started) x.time
              ((ReferenceActivePhysicalStep.prepare x).followers.followers
                (ReferenceActivePhysicalStep.upSenderIndex x))
              ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                (ReferenceActivePhysicalStep.upSenderIndex x)).1
              (by simpa only [ReferenceUpReception.receptionInputAtRow_selectedFollower,
                ReferenceActivePhysicalStep.upSenderIndex] using
                ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                  (ReferenceActivePhysicalStep.upSenderIndex x)).2.1)
              ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                (ReferenceActivePhysicalStep.upSenderIndex x)).2.2.1 rfl }) ∧
        (∀ _hrawMismatch :
          (CoordinatorUpReception.decoderTransition
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs
                (ReferenceActivePhysicalStep.prepare x) started) x.time)).2 ≠
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x),
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) started).result =
            .rejected ({started with phase := CoordinatorCollectionLedger.Phase.decoded},
              CoordinatorUpReception.decoderBankAfter
                (ReferenceUpReception.receptionInputAtRow rate x.row
                  (ReferenceActivePhysicalStep.upInputs
                    (ReferenceActivePhysicalStep.prepare x) started) x.time))) := by
  classical
  dsimp only
  intro P l saved hstate c hchoice
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  obtain ⟨cutoff, clock, core, snapshot, boundary, scores,
    hdispatch, hprepared, hchoiceEq, harm⟩ :=
      actual_choice_continuing_snapshot x P l saved c hstate hchoice
  have hpayload : c.payload = P := by
    exact congrArg Choice.payload hchoiceEq
  have hpre : c.preLedger = l := by
    exact congrArg Choice.preLedger hchoiceEq
  have hstartedClock : c.started = snapshot.clockStarted :=
    congrArg Choice.started hchoiceEq
  have hlocalSnapshot := snapshot.inputsValid
  have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val c.started.clock := by
    rw [hstartedClock, snapshot.clockStarted_frame.1]
    exact hlocalSnapshot.clock_registers_valid
  have hclockSigma : clock.sigma = some P.sigma := hlocalSnapshot.clock_sigma_eq
  have hclockCutoff : clock.u = some cutoff := hlocalSnapshot.clock_cutoff_eq
  have hclockSigmaStarted : c.started.clock.sigma = some P.sigma := by
    rw [hstartedClock, snapshot.clockStarted_frame.1]
    exact hclockSigma
  have hclockCutoffStarted : c.started.clock.u = some cutoff := by
    rw [hstartedClock, snapshot.clockStarted_frame.1]
    exact hclockCutoff
  have htimeSource : CoordinatorPhaseClock.startRoundTimeValid p x.time clock :=
    hlocalSnapshot.clock_start_time_valid
  have htimeSourceParts : P.sigma.val < x.time.val ∧ cutoff.val ≤ x.time.val := by
    simpa [CoordinatorPhaseClock.startRoundTimeValid, hclockSigma, hclockCutoff]
      using htimeSource
  have hcutoffReached : cutoff.val ≤ x.time.val := by
    exact htimeSourceParts.2
  have hphaseTimes := CoordinatorPhaseClock.collection_timeValid p rate.eta.val
    c.started.clock P.sigma cutoff x.time hclock hclockSigmaStarted
    hclockCutoffStarted hcutoffReached
  have hstartClockTime : CoordinatorPhaseClock.startRoundTimeValid p x.time c.started.clock :=
    hphaseTimes.1
  have hfinishClockTime : CoordinatorPhaseClock.finishRoundTimeValid x.time c.started.clock :=
    hphaseTimes.2
  have hstartRoot :=
    ReferenceCompleteContinuingCollectionStart.actual_continuing_collection_recorder_start
      rate rewards C_star C_h source k
  dsimp only at hstartRoot
  rcases (hstartRoot P l saved hstate c hchoice) with
    ⟨o, started, hrootPayload, hrootPre, hinitializer, hlocal, hrecord,
      hfresh, hstart, hstartCandidate, hvalid, hphase, hcursor, hinput⟩
  have hstartL : CoordinatorCollectionLedger.startRound l (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled l x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
        .success started := by
    simpa [hpre] using hstart
  have hstartC : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
        .success started := by
    cases hpre
    exact hstart
  have hreceiver := actual_filtered_receive_noninvalid rate rewards C_star C_h source k
    P l saved hstate c hchoice o started hstartC hinput
  dsimp only at hreceiver
  rcases hreceiver with ⟨decoded, hreceive⟩
  let hinputValue :=
    ReferenceUpReception.receptionInputAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time
  have hinputValueCheck : CoordinatorUpReception.receptionInputCheck hinputValue = true := by
    simpa [hinputValue] using hinput
  have hinputValueCheckAtRow : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare x) started) x.time) = true := by
    simpa [hinputValue, ReferenceActivePhysicalStep.upInputs] using hinputValueCheck
  have hdomain : CoordinatorUpReception.receptionInputDomain hinputValue :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff hinputValue).mp hinputValueCheck
  have hbankWellFormed :=
    CoordinatorUpReception.decoderBankAfter_wellFormed hinputValue hdomain
  let hbank : CoordinatorUpReception.UpDecoderBank p :=
    CoordinatorUpReception.decoderBankAfter hinputValue
  have hbankCheck : CoordinatorUpReception.decoderBankCheck p hbank = true :=
    (CoordinatorUpReception.decoderBankCheck_eq_true_iff p hbank).2 (by
      simpa [hbank] using hbankWellFormed)
  have hreceiveBank :
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, hbank) ∨
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).result = .rejected (decoded, hbank) := by
    simpa [hbank, hinputValue] using hreceive
  have hfinishRoot :=
    ReferenceCompleteContinuingCollectionFinish.actual_continuing_collection_finish
      rate rewards C_star C_h source k P l saved hstate c hchoice o hrecord started hstartC
      decoded hbank hreceiveBank
  rcases hfinishRoot with
    ⟨finished, hfinish, hfinishCandidate, hfinishValid, hfinishPhase, hfinishCursor,
      hincrement, hassignment, hsigma, hcutoffOut, hfreeze, hbase, hpending,
      hcutoffRegisters, hcurrentRegisters, hrawBuffer, henabledHistory, haccepted⟩
  let clockFinished : CoordinatorPhaseClock.FinishRoundResult p := {
    clock := c.started.clock
    pending := finished.pending
    ledgerCommand := some (.accumulateLocalServiceAt x.time) }
  have hclockFinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
      c.started.clock finished.pending x.row = .ok clockFinished := by
    simpa [clockFinished] using
      CoordinatorPhaseClock.finishRound_collection p rate.eta.val x.time P.sigma cutoff
        c.started.clock finished.pending x.row hclock hclockSigmaStarted
        hclockCutoffStarted hcutoffReached
  let output : ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
    ⟨.collection P finished clockFinished.clock.lastProposal, hbank, none,
      some o, (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).diagnostic⟩
  have hpostChoice := ReferenceCollectionSegmentExtraction.choice_tail x c hchoice
  have hcollectionPost :=
    ReferenceActivePhysicalStep.collectionPostChoice_after_start
      (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger
      c.started c.weights o started hrecord hstartC
  have hcollectionFinish :=
    ReferenceActivePhysicalStep.collectionFinish_success (x := x) c.payload c.started o
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started) decoded finished hbank clockFinished
      hreceiveBank hfinish hclockFinish
  have hobservation : (ReferenceActivePhysicalStep.prepare x).observeCoordinator = output := by
    calc
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
          ReferenceActivePhysicalStep.collectionPostChoice
            (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights :=
              hpostChoice
      _ = ReferenceActivePhysicalStep.collectionFinish (x := x) P c.started o
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) started) := by
                simpa [hpayload] using hcollectionPost
      _ = output := by simpa [output, hpayload] using hcollectionFinish
  have hcollectionPostFinal :
      ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) c.payload c.preLedger c.started c.weights =
        output := by
    calc
      _ = ReferenceActivePhysicalStep.collectionFinish (x := x) P c.started o
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) started) := by
                simpa [hpayload] using hcollectionPost
      _ = output := by simpa [output, hpayload] using hcollectionFinish
  have hbankUnselected : ∀ follower,
      follower ≠ ReferenceActivePhysicalStep.upSenderIndex x →
        hbank follower = x.state.upDecoderBank follower := by
    intro follower hne
    have hneInput : follower ≠ hinputValue.selectedFollower := by
      simpa [hinputValue, ReferenceActivePhysicalStep.upSenderIndex] using hne
    exact CoordinatorUpReception.decoderBankAfter_unselected hinputValue follower hneInput
  have hmismatch :
      (CoordinatorUpReception.decoderTransition hinputValue).2 ≠
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) →
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) started).result =
          .rejected ({started with phase := CoordinatorCollectionLedger.Phase.decoded}, hbank) := by
    intro hrawMismatch
    have hrawMismatchInput : (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) started) x.time)).2 ≠
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) := by
      simpa [hinputValue] using hrawMismatch
    exact ReferenceActivePhysicalStep.receiveUp_mismatch
      (ReferenceActivePhysicalStep.prepare x) started hinput hrawMismatchInput
  have hdiagnostic : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).diagnostic =
      some {
        input := hinputValue
        expected := ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)
        decoderAfter := (CoordinatorUpReception.decoderTransition hinputValue).1
        raw := (CoordinatorUpReception.decoderTransition hinputValue).2
        parsed := ReferenceUpReception.rawParsedOutput rate hinputValue
        locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate hinputValue
        rawMatches := decide ((CoordinatorUpReception.decoderTransition hinputValue).2 =
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x))
        wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
          rate x.row (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) started) x.time
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x))
          ((ReferenceActivePhysicalStep.prepare x).follower_alignment
            (ReferenceActivePhysicalStep.upSenderIndex x)).1
              (by simpa only [ReferenceUpReception.receptionInputAtRow_selectedFollower,
                ReferenceActivePhysicalStep.upSenderIndex] using
                ((ReferenceActivePhysicalStep.prepare x).follower_alignment
                  (ReferenceActivePhysicalStep.upSenderIndex x)).2.1)
          ((ReferenceActivePhysicalStep.prepare x).follower_alignment
            (ReferenceActivePhysicalStep.upSenderIndex x)).2.2.1 rfl } := by
    have hdiagCheckRaw : CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) started) x.time) = true :=
      hinputValueCheckAtRow
    have hdiagCheckTuple : CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (started, x.state.upDecoderBank, x.time,
            (ReferenceActivePhysicalStep.prepare x).coordinatorObservation) x.time) = true := by
      simpa [ReferenceActivePhysicalStep.upInputs] using hdiagCheckRaw
    dsimp only [ReferenceActivePhysicalStep.receiveUp,
      ReferenceActivePhysicalStep.upInputs]
    by_cases hcheck : CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (started, x.state.upDecoderBank, x.time,
            (ReferenceActivePhysicalStep.prepare x).coordinatorObservation) x.time) = true
    · simp [hcheck, hinputValue, ReferenceActivePhysicalStep.upInputs]
      all_goals rfl
    · simp [hcheck] at hdiagCheckTuple
  refine ⟨o, started, decoded, hbank, finished, clockFinished,
    hrootPayload, hrootPre, hinitializer, hlocal, hrecord, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hpre] using hfresh
  · exact hstartL
  · exact hvalid
  · exact hphase
  · exact hcursor
  · obtain ⟨hvalidInput, _hsigmaInput, _hphaseInput, hcutInput,
      hcutCursorInput, hcursorTInput, _htimeInput, _hbankInput⟩ :=
        CoordinatorUpReception.receptionInputDomain_parts hinputValue hdomain
    exact hcutInput
  · obtain ⟨_, _, _, hcutInput, hcutCursorInput, hcursorTInput, _, _⟩ :=
        CoordinatorUpReception.receptionInputDomain_parts hinputValue hdomain
    exact hcutCursorInput
  · obtain ⟨_, _, _, _, _, hcursorTInput, _, _⟩ :=
        CoordinatorUpReception.receptionInputDomain_parts hinputValue hdomain
    exact hcursorTInput
  · exact hinputValueCheck
  · exact hreceiveBank
  · exact rfl
  · exact hbankWellFormed
  · exact hbankCheck
  · exact hbankUnselected
  · exact hfinish
  · exact hfinishCandidate
  · exact hfinishValid
  · exact hfinishPhase
  · exact hfinishCursor
  · exact hincrement
  · exact hassignment
  · exact hsigma
  · exact hcutoffOut
  · exact hfreeze
  · exact hbase
  · exact hpending
  · exact hcutoffRegisters
  · exact hcurrentRegisters
  · exact hrawBuffer
  · exact henabledHistory
  · exact hclock
  · exact hclockSigmaStarted
  · exact cutoff
  · exact hclockCutoffStarted
  · exact hcutoffReached
  · exact hstartClockTime
  · exact hfinishClockTime
  · refine ⟨hclockFinish, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [output] using hcollectionPostFinal
    · refine ⟨?_, ?_⟩
      · simpa [hpayload, output] using hcollectionFinish
      · refine ⟨hobservation, ?_⟩
        exact ⟨hdiagnostic, hmismatch⟩

end Bandits.Support.ReferenceCompleteContinuingCollectionReception

end
