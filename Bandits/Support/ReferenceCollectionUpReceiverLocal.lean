/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCutoffUpReplyInterval
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

/-!
# Actual local collection UP receiver

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-88,105-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,164-177,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module exposes one actual continuing-collection receiver call and its
same-round retained diagnostic. The call keeps its real success, rejection,
and invalid branches. A separate conditional result identifies the locally
accepted encoded word at this same call; it is not a trajectory or delivery
theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionUpReceiverLocal

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem prepared_observation_eq_executed_collection
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (htail : ReferenceCollectionPhaseHistory.executedTail x = some tail) :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
        tail.started tail.weights := by
  classical
  have hshape :
      (ReferenceActivePhysicalStep.prepare x).coordinator = .invalidCollectionCutoff ∨
        ∃ clock cutoff outcome,
          (ReferenceActivePhysicalStep.prepare x).coordinator =
            .collection payload ledger clock cutoff outcome := by
    change ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff ∨
      ∃ clock cutoff outcome,
        ReferenceActivePhysicalStep.dispatch x = .collection payload ledger clock cutoff outcome
    unfold ReferenceActivePhysicalStep.dispatch
    rw [hstate]
    by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      cases hrun : CoordinatorRoundDispatch.dispatch
          (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
      | collection outcome =>
          refine Or.inr ⟨clock, cutoff, outcome, ?_⟩
          simp only [hcut, cutoff, clock, hrun]
          cases outcome <;> rfl
    · simp [hcut]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      rcases hshape with hbad | ⟨clock, cutoff, outcome, hgood⟩
      · rw [hcoord] at hbad
        cases hbad
      · rw [hcoord] at hgood
        cases hgood
  | live registers owned base outcome =>
      rcases hshape with hbad | ⟨clock, cutoff, outcome, hgood⟩
      · rw [hcoord] at hbad
        cases hbad
      · rw [hcoord] at hgood
        cases hgood
  | collection actualPayload actualLedger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hselected :
              (ReferenceActivePhysicalStep.DispatchCut.collection actualPayload
                actualLedger clock cutoff (.continuing core snapshot boundary scores)).selection ≠
                none := by
            intro hnone
            have : (ReferenceCollectionPhaseHistory.executedTail x) = none := by
              simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hnone]
            rw [htail] at this
            cases this
          have htailEq : tail =
              ⟨actualPayload, actualLedger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (ReferenceActivePhysicalStep.collectionInput x actualPayload actualLedger
                    clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ := by
            have hs : some
                (⟨actualPayload, actualLedger, snapshot.clockStarted,
                  CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (ReferenceActivePhysicalStep.collectionInput x actualPayload actualLedger
                      clock cutoff)
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ :
                    ReferenceCollectionPhaseHistory.Tail x) = some tail := by
              simpa [ReferenceCollectionPhaseHistory.executedTail, hcoord, hselected] using htail
            exact (Option.some.inj hs).symm
          subst tail
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            hcoord, hselected]
      | _ =>
          simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
  | invalidCollectionCutoff =>
      simp [ReferenceCollectionPhaseHistory.executedTail, hcoord] at htail
  | dagger =>
      rcases hshape with hbad | ⟨clock, cutoff, outcome, hgood⟩
      · rw [hcoord] at hbad
        cases hbad
      · rw [hcoord] at hgood
        cases hgood

private theorem collectionPostChoice_actual_receiver
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hordinary :
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration ≠
        .dagger) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) payload started weights) = some recording ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success ledgerStarted ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare x) ledgerStarted).result ≠ .invalid ∧
      ∃ (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p)
        (finished : ReferenceActivePhysicalStep.Ledger rate)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        ((ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) ledgerStarted).result =
              .success (receivedLedger, bank) ∨
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) ledgerStarted).result =
              .rejected (receivedLedger, bank)) ∧
        CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
          finished.pending x.row = .ok clockFinished := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare x) payload started weights)
  cases hrecording : recordingInput with
  | none =>
      have hdagger :
          (ReferenceActivePhysicalStep.collectionPostChoice
            (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration =
            .dagger := by
        simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput, hrecording,
          ReferenceActivePhysicalStep.coordinatorFailure]
      exact (hordinary hdagger).elim
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          have hdagger :
              (ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration =
                .dagger := by
            simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
              hrecording, hstart, ReferenceActivePhysicalStep.coordinatorFailure]
          exact (hordinary hdagger).elim
      | rejected rejectedLedger =>
          have hdagger :
              (ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).configuration =
                .dagger := by
            simp [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
              hrecording, hstart, ReferenceActivePhysicalStep.coordinatorFailure]
          exact (hordinary hdagger).elim
      | success ledgerStarted =>
          have hfinishOrdinary :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration ≠ .dagger := by
            intro hdagger
            apply hordinary
            have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
              (ReferenceActivePhysicalStep.prepare x) payload ledger started weights recording
              ledgerStarted (by simpa [recordingInput] using hrecording) hstart
            exact (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost).trans
              hdagger
          have hnotInvalid :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).result ≠ .invalid := by
            intro hinvalid
            apply hfinishOrdinary
            simp [ReferenceActivePhysicalStep.collectionFinish, hinvalid,
              ReferenceActivePhysicalStep.coordinatorFailure]
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) ledgerStarted).result with
          | invalid => exact (hnotInvalid hreceive).elim
          | success pair =>
              rcases pair with ⟨receivedLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound receivedLedger with
              | invalid =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                        recording (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact (hfinishOrdinary hdagger).elim
              | rejected rejectedLedger =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                        recording (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact (hfinishOrdinary hdagger).elim
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason =>
                      have hdagger :
                          (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                            recording (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration =
                            .dagger := by
                        simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                          hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                      exact (hfinishOrdinary hdagger).elim
                  | ok clockFinished =>
                      exact ⟨recording, ledgerStarted, by simpa [recordingInput] using hrecording,
                        hstart, hnotInvalid, receivedLedger, bank, finished, clockFinished,
                        Or.inl hreceive, hfinish, hclock⟩
          | rejected pair =>
              rcases pair with ⟨receivedLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound receivedLedger with
              | invalid =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                        recording (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact (hfinishOrdinary hdagger).elim
              | rejected rejectedLedger =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                        recording (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact (hfinishOrdinary hdagger).elim
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason =>
                      have hdagger :
                          (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started
                            recording (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare x) ledgerStarted)).configuration =
                            .dagger := by
                        simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                          hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                      exact (hfinishOrdinary hdagger).elim
                  | ok clockFinished =>
                      exact ⟨recording, ledgerStarted, by simpa [recordingInput] using hrecording,
                        hstart, hnotInvalid, receivedLedger, bank, finished, clockFinished,
                        Or.inr hreceive, hfinish, hclock⟩

/-- One actual continuing-collection receiver execution with its literal
recording, started ledger, site ledger, and retained UP diagnostic. The result
keeps ordinary UP rejection intact. The endpoint excludes invalid reception
and proves the actual finish and clock calls succeeded. -/
theorem actual_collection_up_receiver
    (r : Record p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hordinary : r.output.next.coordinator ≠ .dagger) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
            some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      r.output.coordinator.up = some d ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L).result ≠
        .invalid ∧
      ∃ (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p)
        (finished : ReferenceActivePhysicalStep.Ledger rate)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        (((ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) L).result =
              .success (receivedLedger, bank)) ∨
          ((ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) L).result =
              .rejected (receivedLedger, bank))) ∧
        CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time tail.started.clock
          finished.pending r.input.row = .ok clockFinished ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.rawMatches = decide (d.raw = d.expected) ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      d.input.affineSample =
        ((r.input.rows r.input.selected).2 r.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time)) ∧
      d.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input))
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl := by
  have hobs : (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator =
      ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights :=
    prepared_observation_eq_executed_collection payload ledger saved tail hstate htail
  have hout : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  have hnext : r.output.next.coordinator =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration := by
    rw [r.output_eq]
    exact (ReferenceActivePhysicalStep.step_next_fields r.input).1
  have hpostOrdinary :
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights).configuration ≠ .dagger := by
    intro hdagger
    apply hordinary
    rw [hnext]
    exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hobs |>.trans hdagger
  obtain ⟨recording, L, hrecording, hstart, hnotInvalid, hfinishData⟩ :=
    collectionPostChoice_actual_receiver tail.payload tail.ledger tail.started tail.weights
      hpostOrdinary
  let input := ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L
  let d : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
    input := input
    expected := ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input)
    decoderAfter := (CoordinatorUpReception.decoderTransition input).1
    raw := (CoordinatorUpReception.decoderTransition input).2
    parsed := ReferenceUpReception.rawParsedOutput rate input
    locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate input
    rawMatches := decide ((CoordinatorUpReception.decoderTransition input).2 =
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input))
    wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate
      r.input.row (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r.input))
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl }
  have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
    cases hvalue : CoordinatorUpReception.receptionInputCheck input with
    | true => rfl
    | false =>
        let inputs := ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) L
        let sender := (ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input)
        have hfalse : CoordinatorUpReception.receptionInputCheck
            (ReferenceUpReception.receptionInputAtRow rate r.input.row inputs r.input.time) =
              false := by
          simpa [inputs, input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
            ReferenceActivePhysicalStep.upInputs,
            ReferenceUpReception.receptionInputAtRow,
            CoordinatorUpMeasurability.receptionInputAtRow,
            CoordinatorUpMeasurability.receptionInputAtControl] using hvalue
        have hfiltered := ReferenceUpReception.receiveUpFilteredAtRow_input_invalid
          rate r.input.row inputs r.input.time sender
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl hfalse
        have hinvalid :
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result = .invalid := by
          change ReferenceUpReception.receiveUpFilteredAtRow rate r.input.row inputs
            r.input.time sender ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
            ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
            ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl = .invalid
          exact hfiltered.1
        exact (hnotInvalid hinvalid).elim
  have hdiagActual :
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights).up = some d ∧
      d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input))
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl := by
    have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
      (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger tail.started
      tail.weights recording L hrecording hstart
    have hfields := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up hpost
    rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hfields
    have hcheckControl : CoordinatorUpReception.receptionInputCheck
        (CoordinatorUpMeasurability.receptionInputAtControl
          (r.input.row.2 r.input.time)
          (L, r.input.state.upDecoderBank, r.input.time,
            (ReferenceActivePhysicalStep.prepare r.input).coordinatorObservation)) = true := by
      simpa [input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
        ReferenceActivePhysicalStep.upInputs,
        ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl] using hcheck
    have hdiagnostic :
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).diagnostic = some d := by
      simp [d, input, ReferenceActivePhysicalStep.receiveUp,
        ReferenceActivePhysicalStep.upInputs,
        ReferenceCoordinatorUpPhysicalCall.actualUpInput,
        ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow, hcheckControl]
      ; rfl
    have hwrongField : d.wrongUniqueAccepted =
        ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
          rate r.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex r.input))
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
          ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl := by
      have hwrongOption := congrArg
        (Option.map (fun diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate =>
          diagnostic.wrongUniqueAccepted)) hdiagnostic
      have hwrongEquality :
          some (ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate r.input.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
            ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
              (ReferenceActivePhysicalStep.upSenderIndex r.input))
            ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
            ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
            ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl) =
          some d.wrongUniqueAccepted := by
        simpa [ReferenceActivePhysicalStep.receiveUp,
          ReferenceActivePhysicalStep.upInputs,
          ReferenceUpReception.receptionInputAtRow,
          CoordinatorUpMeasurability.receptionInputAtRow,
          ReferenceActivePhysicalStep.upExpected,
          ReferenceActivePhysicalStep.upSenderIndex, hcheckControl] using hwrongOption
      exact (Option.some.inj hwrongEquality).symm
    exact ⟨hfields.trans hdiagnostic, hwrongField⟩
  rcases hdiagActual with ⟨hdiagActual, hwrongField⟩
  have hdiagnostic : r.output.coordinator.up = some d := by
    calc
      r.output.coordinator.up =
          (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := hout
      _ = (ReferenceActivePhysicalStep.collectionPostChoice
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
          tail.started tail.weights).up :=
            congrArg ReferenceActivePhysicalStep.CoordinatorObservation.up hobs
      _ = some d := hdiagActual
  obtain ⟨siteLedger, hsite, hsiteCheck, hinput, hdecoderAfter⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d hdiagnostic
  have hledgerEq : siteLedger = L := by
    have hinputs : input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input siteLedger := by
      exact (show input = d.input from rfl).trans hinput
    have hprojection := congrArg CoordinatorUpReception.ReceptionInput.ledger hinputs
    simpa [input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hprojection.symm
  subst siteLedger
  have htailReception : tail.reception = some (L,
      ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) := by
    simp [ReferenceCollectionPhaseHistory.Tail.reception, hrecording, hstart]
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
    r d hdiagnostic
  rcases hfields with ⟨_, _, _, hbank, htime, hobservation, _, hsample, _, _, _, _, _, _⟩
  obtain ⟨receivedLedger, bank, finished, clockFinished, hreceived, hfinished, hclock⟩ :=
    hfinishData
  have hdecoderAfter' : d.decoderAfter =
      (CoordinatorUpReception.decoderTransition d.input).1 := by
    simp [d, input, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow]
  refine ⟨recording, L, d, ?_⟩
  refine ⟨hrecording, ?_⟩
  refine ⟨hstart, ?_⟩
  refine ⟨hsite, ?_⟩
  refine ⟨hsiteCheck, ?_⟩
  refine ⟨hdiagnostic, ?_⟩
  refine ⟨hinput, ?_⟩
  refine ⟨htailReception, ?_⟩
  refine ⟨hnotInvalid, ?_⟩
  refine ⟨receivedLedger, bank, finished, clockFinished, ?_⟩
  refine ⟨hreceived, ?_⟩
  refine ⟨hfinished, ?_⟩
  refine ⟨hclock, ?_⟩
  refine ⟨hdecoderAfter', ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨hbank, ?_⟩
  refine ⟨htime, ?_⟩
  refine ⟨hsample, ?_⟩
  refine ⟨hobservation, ?_⟩
  exact hwrongField

/-- The actual continuing-collection receiver's local matching-word
implication. The decoder word and local acceptance test remain explicit
conditions at this same produced ledger and diagnostic; no queue, replay, or
truthful-score property is assumed.
-/
theorem actual_collection_up_receiver_matching_word
    (r : Record p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hordinary : r.output.next.coordinator ≠ .dagger) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
            some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      r.output.coordinator.up = some d ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
      (∃ (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p)
        (finished : ReferenceActivePhysicalStep.Ledger rate)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        (((ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) L).result =
              .success (receivedLedger, bank)) ∨
          ((ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) L).result =
              .rejected (receivedLedger, bank))) ∧
        CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time tail.started.clock
          finished.pending r.input.row = .ok clockFinished) ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.rawMatches = decide (d.raw = d.expected) ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      d.input.affineSample =
        ((r.input.rows r.input.selected).2 r.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time)) ∧
      d.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
        rate r.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input))
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
        ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl ∧
      ∀ (M : ReferenceCollectionPhaseHistory.UpRecord p rate),
        d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) →
        d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) →
        CoordinatorCollectionLedger.acceptUpCheck L
          (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true →
        ReferenceCollectionPhaseHistory.filteredParsed r.input L = some M ∧
        d.parsed = some M ∧
        d.locallyAccepted = true ∧
        d.rawMatches = true ∧
        d.wrongUniqueAccepted = false ∧
        (∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
          (bank : CoordinatorUpReception.UpDecoderBank p),
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare r.input) L).result = .success (decoded, bank) ∧
          ReferenceCollectionPhaseHistory.AcceptedUp r.input
            (ReferenceActivePhysicalStep.upSenderIndex r.input) M) := by
  obtain ⟨recording, L, d, hrecording, hstart, hsite, hsiteCheck,
      hdiagnostic, hinput, htailReception, hnotInvalid,
      receivedLedger, receivedBank, finished, clockFinished,
      hreceived, hfinished, hclock, hdecoderAfter, hrawDiagnostic,
      hparsedDiagnostic, hlocalDiagnostic, hexpectedDiagnostic,
      hrawMatchesDiagnostic, hbank, htime, hsample, hobservation,
      hwrongDiagnostic⟩ :=
    actual_collection_up_receiver r payload ledger saved tail hstate htail hordinary
  refine ⟨recording, L, d, hrecording, hstart, hsite, hsiteCheck,
    hdiagnostic, hinput, htailReception, hnotInvalid,
    ⟨receivedLedger, receivedBank, finished, clockFinished,
      hreceived, hfinished, hclock⟩, hdecoderAfter, hrawDiagnostic,
    hparsedDiagnostic, hlocalDiagnostic, hexpectedDiagnostic,
    hrawMatchesDiagnostic, hbank, htime, hsample, hobservation,
    hwrongDiagnostic, ?_⟩
  intro M hrawWord hExpectedWord haccept
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let inputs := ReferenceActivePhysicalStep.upInputs prepared L
  let receiverInput := ReferenceUpReception.receptionInputAtRow rate r.input.row
    inputs r.input.time
  let sender := prepared.followers.followers
    (ReferenceActivePhysicalStep.upSenderIndex r.input)
  have hrawAtDiagnostic :
      (CoordinatorUpReception.decoderTransition d.input).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) :=
    hrawDiagnostic.symm.trans hrawWord
  have hrawAtRow :
      (CoordinatorUpReception.decoderTransition receiverInput).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    simpa [receiverInput, inputs, prepared, hinput,
      ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hrawAtDiagnostic
  have hexpectedAtPrepared :
      ReferenceActivePhysicalStep.upExpected prepared =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) :=
    hexpectedDiagnostic.symm.trans hExpectedWord
  have hcurrentWord :
      ReferenceUpReception.currentOfferWord rate r.input.row
        receiverInput.selectedFollower receiverInput.time sender
        (prepared.follower_alignment _).1
        (prepared.follower_alignment _).2.1
        (prepared.follower_alignment _).2.2.1 =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    change ReferenceActivePhysicalStep.upExpected prepared =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta M)
    exact hexpectedAtPrepared
  have hflatWord : ActiveFollowerArmChoice.offeredUpWord rate.eta M =
      OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) M) := by
    unfold ActiveFollowerArmChoice.offeredUpWord
    have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
    cases hcodec
    rfl
  have hparsedWord :
      CoordinatorUpReception.parseDecoderOutput
        (some (ActiveFollowerArmChoice.offeredUpWord rate.eta M)) = some M := by
    rw [CoordinatorUpReception.parseDecoderOutput, hflatWord]
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) M)))) = some M
    rw [Equiv.symm_apply_apply]
    exact OrdinaryMessageCodec.parseUp_encode
      (CoordinatorCollectionLedger.codecParams p rate.eta.val) M
  have hparsedAtDiagnostic :
      ReferenceUpReception.rawParsedOutput rate d.input = some M := by
    change CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition d.input).2 = some M
    rw [hrawAtDiagnostic]
    exact hparsedWord
  have hparsedResult : d.parsed = some M :=
    hparsedDiagnostic.trans hparsedAtDiagnostic
  have hlocalRaw : ReferenceUpReception.rawParsedLocalAcceptance rate d.input = true := by
    rw [ReferenceUpReception.rawParsedLocalAcceptance, hparsedAtDiagnostic]
    rw [hinput]
    change CoordinatorCollectionLedger.acceptUpCheck L
      (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true
    exact haccept
  have hlocalResult : d.locallyAccepted = true := hlocalDiagnostic.trans hlocalRaw
  have hrawEqExpected : d.raw = d.expected := hrawWord.trans hExpectedWord.symm
  have hrawMatchesResult : d.rawMatches = true := by
    rw [hrawMatchesDiagnostic]
    simp [hrawEqExpected]
  have hfiltered : ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition receiverInput).2
      (ReferenceActivePhysicalStep.upExpected prepared) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    rw [hrawAtRow, hexpectedAtPrepared]
    exact ReferenceUpReception.filterRawByExpected_eq_raw_of_eq _ _ rfl
  have hfilteredParsed : ReferenceCollectionPhaseHistory.filteredParsed r.input L = some M := by
    change CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition receiverInput).2
        (ReferenceActivePhysicalStep.upExpected prepared)) = some M
    rw [hfiltered]
    exact hparsedWord
  let wrong := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate r.input.row
    inputs r.input.time sender
    (prepared.follower_alignment _).1
    (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1 rfl
  have hwrongFalse : wrong = false := by
    cases hwrongValue : wrong with
    | false => rfl
    | true =>
        obtain ⟨word, parsed, hrawWrong, hparsedWrong, hacceptWrong, hwrongWord⟩ :=
          (ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
            rate r.input.row inputs r.input.time sender
            (prepared.follower_alignment _).1
            (prepared.follower_alignment _).2.1
            (prepared.follower_alignment _).2.2.1 rfl).mp hwrongValue
        have hwordEq : word = ActiveFollowerArmChoice.offeredUpWord rate.eta M :=
          Option.some.inj (hrawWrong.symm.trans hrawAtRow)
        subst word
        exact (hwrongWord hcurrentWord.symm).elim
  have hwrongResult : d.wrongUniqueAccepted = false :=
    hwrongDiagnostic.trans hwrongFalse
  have hreceiverCheck : CoordinatorUpReception.receptionInputCheck receiverInput = true := by
    simpa [receiverInput, inputs, prepared,
      ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hsiteCheck
  have hdomain : CoordinatorUpReception.receptionInputDomain receiverInput :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff receiverInput).mp hreceiverCheck
  have hordinaryMatch : (CoordinatorUpReception.decoderTransition receiverInput).2 =
      ReferenceActivePhysicalStep.upExpected prepared :=
    hrawAtRow.trans hexpectedAtPrepared.symm
  have hactualOrdinary :
      (ReferenceActivePhysicalStep.receiveUp prepared L).result =
        CoordinatorUpReception.receiveUp receiverInput := by
    simpa [prepared, inputs, receiverInput] using
      ReferenceActivePhysicalStep.receiveUp_eq_ordinary_of_no_mismatch
        prepared L hordinaryMatch
  have hparsedReceiver :
      CoordinatorUpReception.parsedDecoderOutput receiverInput = some M := by
    unfold CoordinatorUpReception.parsedDecoderOutput
    rw [hrawAtRow]
    exact hparsedWord
  have hacceptReceiver :
      CoordinatorCollectionLedger.acceptUpCheck receiverInput.ledger
        receiverInput.selectedFollower M = true := by
    change CoordinatorCollectionLedger.acceptUpCheck L
      (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true
    exact haccept
  rcases CoordinatorUpReception.receptionInputDomain_parts receiverInput hdomain with
    ⟨hledgerValid, _, hphase, hcutoff, hcutoffCursor, hcursorT, _, _⟩
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck receiverInput.ledger = true ∧
        receiverInput.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ receiverInput.ledger.cutoff ∧
        receiverInput.ledger.cutoff ≤ receiverInput.ledger.cursor ∧
        receiverInput.ledger.cursor ≤ p.T :=
    ⟨hledgerValid, hphase, hcutoff, hcutoffCursor, hcursorT⟩
  have hdecodeNotRejected : ∀ out,
      CoordinatorCollectionLedger.decodeUp receiverInput.ledger
        receiverInput.selectedFollower (some M) ≠ .rejected out := by
    intro out hdecode
    unfold CoordinatorCollectionLedger.decodeUp at hdecode
    rw [dite_eq_left hdecodeInput] at hdecode
    dsimp only at hdecode
    rw [ite_eq_left hacceptReceiver] at hdecode
    repeat' (first | split at hdecode)
    all_goals
      have hdifferent := congrArg
        (fun result : CoordinatorCollectionLedger.Checked
            (ReferenceActivePhysicalStep.Ledger rate) =>
          match result with
          | .success _ => 0
          | .rejected _ => 1
          | .invalid => 2) hdecode
      norm_num at hdifferent
  have hreceiveDecode : CoordinatorUpReception.receiveUp receiverInput =
      CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp receiverInput.ledger
          receiverInput.selectedFollower
          (CoordinatorUpReception.parsedDecoderOutput receiverInput))
        (CoordinatorUpReception.decoderBankAfter receiverInput) := by
    rw [CoordinatorUpReception.receiveUp_eq_existing_decodeUp receiverInput hreceiverCheck]
    rfl
  have hsuccess : ∃ decoded bank,
      (ReferenceActivePhysicalStep.receiveUp prepared L).result = .success (decoded, bank) := by
    cases hdecode : CoordinatorCollectionLedger.decodeUp receiverInput.ledger
        receiverInput.selectedFollower (some M) with
    | success decoded =>
        refine ⟨decoded, CoordinatorUpReception.decoderBankAfter receiverInput, ?_⟩
        have hordinarySuccess : CoordinatorUpReception.receiveUp receiverInput =
            .success (decoded, CoordinatorUpReception.decoderBankAfter receiverInput) := by
          rw [hreceiveDecode, hparsedReceiver, hdecode]
          rfl
        calc
          (ReferenceActivePhysicalStep.receiveUp prepared L).result =
              CoordinatorUpReception.receiveUp receiverInput := hactualOrdinary
          _ = .success (decoded, CoordinatorUpReception.decoderBankAfter receiverInput) :=
                hordinarySuccess
    | rejected out => exact (hdecodeNotRejected out hdecode).elim
    | invalid =>
        have hactualInvalid : (ReferenceActivePhysicalStep.receiveUp prepared L).result = .invalid := by
          have hordinaryInvalid : CoordinatorUpReception.receiveUp receiverInput = .invalid := by
            rw [hreceiveDecode, hparsedReceiver, hdecode]
            rfl
          exact hactualOrdinary.trans hordinaryInvalid
        exact (hnotInvalid hactualInvalid).elim
  rcases hsuccess with ⟨decoded, bank, hsuccess⟩
  have haccepted : ReferenceCollectionPhaseHistory.AcceptedUp r.input
      (ReferenceActivePhysicalStep.upSenderIndex r.input) M := by
    refine ⟨tail, recording, L, decoded, bank, htail, hrecording, hstart,
      hsuccess, hfilteredParsed, rfl⟩
  exact ⟨hfilteredParsed, hparsedResult, hlocalResult, hrawMatchesResult,
    hwrongResult, ⟨decoded, bank, hsuccess, haccepted⟩⟩

end Bandits.Support.ReferenceCollectionUpReceiverLocal

end
