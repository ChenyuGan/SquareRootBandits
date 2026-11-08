/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionUpReceiverLocal

/-!
# Actual cutoff-round UP receiver

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:36-53`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`.

This module follows the live dispatcher's selected cutoff branch into its
literal collection tail and UP receiver. It keeps the first reset ledger
separate from the ledger after the same-round receiver, which may erase a
pending label before FinishRound.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCutoffUpReceiverLocal

private theorem cutoff_tail
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    ∃ tail : ReferenceCollectionPhaseHistory.Tail r.input,
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) =
        ReferenceCoordinatorUpPhysicalCall.tailLedger?
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
          tail.started tail.weights ∧
      tail.ledger.pending = Finset.univ ∧
      tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      tail.ledger.cutoff = r.input.time.val + 1 ∧
      tail.ledger.cursor = r.input.time.val + 1 ∧
      tail.ledger.phase = .ready ∧
      tail.started.pending = Finset.univ := by
  classical
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hcoord : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched startEq ledger initializationEq ledgerEq valid
          cutoffClock cutoffPending noAssignment selected =>
          have hselected :
              (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection ≠ none := by
            rw [hcoord]
            change ReferenceActivePhysicalStep.selectionAt r.input registers.payload
              dispatched.startResult r.input.time
              (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights
              selected ≠ none
            simp [ReferenceActivePhysicalStep.selectionAt]
          have hbranchSelected :
              (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                (.cutoffChosen dispatched startEq ledger initializationEq ledgerEq valid
                  cutoffClock cutoffPending noAssignment selected)).selection ≠ none := by
            change ReferenceActivePhysicalStep.selectionAt r.input registers.payload
              dispatched.startResult r.input.time
              (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights
              selected ≠ none
            simp [ReferenceActivePhysicalStep.selectionAt]
          let tail : ReferenceCollectionPhaseHistory.Tail r.input :=
            ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
              dispatched.startResult,
              (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights⟩
          have htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail := by
            simp [ReferenceCollectionPhaseHistory.executedTail, hcoord, hbranchSelected, tail]
          have hobserve0 := ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare r.input) registers owned base
            (.cutoffChosen dispatched startEq ledger initializationEq ledgerEq valid
              cutoffClock cutoffPending noAssignment selected) hcoord
          have hobserve :
              (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator =
                ReferenceActivePhysicalStep.collectionPostChoice
                  (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
                  tail.started tail.weights := by
            simpa [hbranchSelected, tail] using hobserve0
          have houtput : r.output.coordinator =
              (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator := by
            rw [r.output_eq]
            rfl
          have hstartFields :=
            CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
              registers owned base r.input.time
          rcases hstartFields with
            ⟨_, hnewSigma, hnewCutoff, _, _, hnewPending, _, _, _, _, _, _, _,
              hnewCursor, hnewPhase⟩
          have hsharedFields := ReferenceActivePhysicalStep.sharedLedger_fields ledger
          rcases hsharedFields with
            ⟨_, hsharedSigma, hsharedCutoff, _, _, hsharedPending, _, _, _, _, _, _,
              hsharedCursor, hsharedPhase⟩
          have htailPending : tail.ledger.pending = Finset.univ := by
            dsimp [tail]
            rw [hsharedPending, ledgerEq]
            exact hnewPending
          have htailSigma : tail.ledger.sigma = tail.payload.sigma.val + 1 := by
            dsimp [tail]
            rw [hsharedSigma, ledgerEq]
            exact hnewSigma
          have htailCutoff : tail.ledger.cutoff = r.input.time.val + 1 := by
            dsimp [tail]
            rw [hsharedCutoff, ledgerEq]
            exact hnewCutoff
          have htailCursor : tail.ledger.cursor = r.input.time.val + 1 := by
            dsimp [tail]
            rw [hsharedCursor, ledgerEq]
            exact hnewCursor
          have htailPhase : tail.ledger.phase = .ready := by
            dsimp [tail]
            rw [hsharedPhase, ledgerEq]
            exact hnewPhase
          have hsite :
              ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) =
                ReferenceCoordinatorUpPhysicalCall.tailLedger?
                  (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
                  tail.started tail.weights := by
            simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?, hcoord, hbranchSelected, tail]
          exact ⟨tail, htail, houtput.trans hobserve, hsite, htailPending, htailSigma,
            htailCutoff, htailCursor, htailPhase, cutoffPending⟩
      | _ => simp [hcoord] at hcut
  | _ => simp [hcoord] at hcut

/-- The actual live cutoff branch creates an executed collection tail with
its first reset fields, selects the same post-choice collection operation,
and identifies the call-site ledger with that tail's actual start result. -/
theorem actual_cutoff_up_receiver
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    ∃ tail : ReferenceCollectionPhaseHistory.Tail r.input,
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) =
        ReferenceCoordinatorUpPhysicalCall.tailLedger?
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
          tail.started tail.weights ∧
      tail.ledger.pending = Finset.univ ∧
      tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      tail.ledger.cutoff = r.input.time.val + 1 ∧
      tail.ledger.cursor = r.input.time.val + 1 ∧
      tail.ledger.phase = .ready ∧
      tail.started.pending = Finset.univ := by
  exact cutoff_tail r hcut

private theorem successful_cutoff_start_fields
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (tail : ReferenceCollectionPhaseHistory.Tail x)
    (recording : CoordinatorRecordingOperation.Output p)
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (hstart : CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success L)
    (htailPending : tail.ledger.pending = Finset.univ)
    (htailSigma : tail.ledger.sigma = tail.payload.sigma.val + 1)
    (htailCutoff : tail.ledger.cutoff = x.time.val + 1) :
    L.pending = Finset.univ ∧
      L.sigma = tail.payload.sigma.val + 1 ∧
      L.cutoff = x.time.val + 1 ∧
      L.cursor = x.time.val + 1 := by
  have hcand := ReferenceActivePhysicalStep.collection_started_candidate
    tail.ledger L x.time
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hpending : L.pending = tail.ledger.pending := by
    rw [hcand]
    simp [CoordinatorCollectionLedger.startRoundCandidate]
  have hsigma : L.sigma = tail.ledger.sigma := by
    rw [hcand]
    simp [CoordinatorCollectionLedger.startRoundCandidate]
  have hcutoff : L.cutoff = tail.ledger.cutoff := by
    rw [hcand]
    simp [CoordinatorCollectionLedger.startRoundCandidate]
  have hcursor : L.cursor = x.time.val + 1 := by
    rw [hcand]
    simp [CoordinatorCollectionLedger.startRoundCandidate,
      CoordinatorCollectionLedger.sourceRound]
  exact ⟨hpending.trans htailPending, hsigma.trans htailSigma,
    hcutoff.trans htailCutoff, hcursor⟩

private theorem cutoff_receiveUp_invalid_of_failed_check
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput x L) = false) :
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) L).result = .invalid ∧
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) L).diagnostic = none := by
  classical
  let prepared := ReferenceActivePhysicalStep.prepare x
  let inputs := ReferenceActivePhysicalStep.upInputs prepared L
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  let sender := prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x)
  have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
    simpa [input, inputs, prepared, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hcheck
  have hfiltered := ReferenceUpReception.receiveUpFilteredAtRow_input_invalid
    rate x.row inputs x.time sender
    (prepared.follower_alignment _).1
    (prepared.follower_alignment _).2.1
    (prepared.follower_alignment _).2.2.1 rfl hfalse
  have hresult : (ReferenceActivePhysicalStep.receiveUp prepared L).result = .invalid := by
    change ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time sender
      (prepared.follower_alignment _).1
      (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 rfl = .invalid
    exact hfiltered.1
  have hdiagnostic : (ReferenceActivePhysicalStep.receiveUp prepared L).diagnostic = none := by
    simp [ReferenceActivePhysicalStep.receiveUp, prepared, inputs, input, hfalse]
  exact ⟨hresult, hdiagnostic⟩

private theorem record_next_dagger
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hconfiguration : r.output.coordinator.configuration = .dagger) :
    r.output.next.coordinator = .dagger := by
  have hconfigurationStep :
      (ReferenceActivePhysicalStep.step r.input).coordinator.configuration = .dagger := by
    simpa [r.output_eq] using hconfiguration
  calc
    r.output.next.coordinator = (ReferenceActivePhysicalStep.step r.input).next.coordinator :=
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput r.input =>
        output.next.coordinator) r.output_eq
    _ = (ReferenceActivePhysicalStep.step r.input).coordinator.configuration := by rfl
    _ = .dagger := hconfigurationStep

/-- Every actual cutoff-tail call retains its recorder, checked start, checked
reception, and finish cases. A successful stage-(1) start has the reset
pending set and the literal cutoff cursor; a checked diagnostic remains in
the coordinator observation through every later reception or finish result.
-/
theorem actual_cutoff_up_receiver_cases
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    ∃ tail : ReferenceCollectionPhaseHistory.Tail r.input,
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) =
        ReferenceCoordinatorUpPhysicalCall.tailLedger?
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
          tail.started tail.weights ∧
      tail.ledger.pending = Finset.univ ∧
      tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      tail.ledger.cutoff = r.input.time.val + 1 ∧
      tail.ledger.cursor = r.input.time.val + 1 ∧
      tail.ledger.phase = .ready ∧
      tail.started.pending = Finset.univ ∧
      (let prepared := ReferenceActivePhysicalStep.prepare r.input;
       let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
         prepared tail.payload tail.started tail.weights;
       let recordingCall := CoordinatorRecorderComplementBridge.run recordingInput;
       (recordingCall = none ∧
          r.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
            r.input.state.upDecoderBank (.collection .recorderDomain) none none ∧
          r.output.coordinator.recording = none ∧
          r.output.coordinator.up = none ∧
          r.output.next.coordinator = .dagger) ∨
       ∃ recording, recordingCall = some recording ∧
         (let startCall := CoordinatorCollectionLedger.startRound tail.ledger
           (r.input.time.val + 1)
           (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
           (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording);
          ((startCall = .invalid ∧
            r.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              r.input.state.upDecoderBank (.collection .ledgerStartDomain)
              (some recording) none ∧
            r.output.coordinator.recording = some recording ∧
            r.output.coordinator.up = none ∧
            r.output.next.coordinator = .dagger) ∨
          (∃ rejectedLedger, startCall = .rejected rejectedLedger ∧
            r.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              r.input.state.upDecoderBank (.collection .ledgerStartDomain)
              (some recording) none ∧
            r.output.coordinator.recording = some recording ∧
            r.output.coordinator.up = none ∧
            r.output.next.coordinator = .dagger) ∨
          (∃ L, startCall = .success L ∧
            ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
            L.pending = Finset.univ ∧
            L.sigma = tail.payload.sigma.val + 1 ∧
            L.cutoff = r.input.time.val + 1 ∧
            L.cursor = r.input.time.val + 1 ∧
            (let check := CoordinatorUpReception.receptionInputCheck
                (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L);
             let receive := ReferenceActivePhysicalStep.receiveUp prepared L;
             (check = false ∧ receive.result = .invalid ∧ receive.diagnostic = none ∧
                r.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                  r.input.state.upDecoderBank (.collection .upReceptionDomain)
                  (some recording) none ∧
                r.output.coordinator.up = none ∧
                r.output.next.coordinator = .dagger) ∨
             (∃ d, check = true ∧ receive.diagnostic = some d ∧
               r.output.coordinator = ReferenceActivePhysicalStep.collectionFinish
                 (x := r.input) tail.payload tail.started recording receive ∧
               r.output.coordinator.up = some d ∧
               d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
               d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
               d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
               d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
               d.expected = ReferenceActivePhysicalStep.upExpected prepared ∧
               d.rawMatches = decide (d.raw = d.expected) ∧
               d.input.upDecoderBank = r.input.state.upDecoderBank ∧
               d.input.time = r.input.time ∧
               d.input.affineSample =
                 ((r.input.rows r.input.selected).2 r.input.time).2
                   (1, CoordinatorUpMeasurability.selectedChannelFollower
                     ((r.input.rows r.input.selected).2 r.input.time)) ∧
               d.input.ownObservation = prepared.feedback.feedback
                 (ActiveRoundActions.coordinator p.two_le_m) ∧
               d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                 rate r.input.row
                 (ReferenceActivePhysicalStep.upInputs prepared L) r.input.time
                 (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex r.input))
                 (prepared.follower_alignment _).1
                 (prepared.follower_alignment _).2.1
                 (prepared.follower_alignment _).2.2.1 rfl)))))) := by
  classical
  obtain ⟨tail, htail, hpost, hsiteTail, htailPending, htailSigma, htailCutoff,
    htailCursor, htailPhase, hstartedPending⟩ := actual_cutoff_up_receiver r hcut
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput
    prepared tail.payload tail.started tail.weights
  let recordingCall := CoordinatorRecorderComplementBridge.run recordingInput
  refine ⟨tail, htail, hpost, hsiteTail, htailPending, htailSigma, htailCutoff,
    htailCursor, htailPhase, hstartedPending, ?_⟩
  cases hrecording : recordingCall with
  | none =>
      have hrecordingRaw : CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) = none := by
        simpa [recordingCall, recordingInput, prepared] using hrecording
      have hfailure : r.output.coordinator =
          ReferenceActivePhysicalStep.coordinatorFailure r.input.state.upDecoderBank
            (.collection .recorderDomain) none none := by
        rw [hpost]
        simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecordingRaw]
      have hconfig : r.output.coordinator.configuration = .dagger := by
        rw [hfailure]
        rfl
      refine Or.inl ⟨hrecording, hfailure, ?_, ?_, record_next_dagger r hconfig⟩
      · exact congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
          observation.recording) hfailure
      · exact congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
          observation.up) hfailure
  | some recording =>
      have hrecordingRaw : CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
            some recording := by
        simpa [recordingCall, recordingInput, prepared] using hrecording
      refine Or.inr ⟨recording, hrecording, ?_⟩
      cases hstart : CoordinatorCollectionLedger.startRound tail.ledger
          (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          have hfailure : r.output.coordinator =
              ReferenceActivePhysicalStep.coordinatorFailure r.input.state.upDecoderBank
                (.collection .ledgerStartDomain) (some recording) none := by
            rw [hpost]
            simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecordingRaw, hstart]
          have hconfig : r.output.coordinator.configuration = .dagger := by
            rw [hfailure]
            rfl
          exact Or.inl ⟨rfl, hfailure,
            congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
              observation.recording) hfailure,
            congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
              observation.up) hfailure, record_next_dagger r hconfig⟩
      | rejected rejectedLedger =>
          have hfailure : r.output.coordinator =
              ReferenceActivePhysicalStep.coordinatorFailure r.input.state.upDecoderBank
                (.collection .ledgerStartDomain) (some recording) none := by
            rw [hpost]
            simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecordingRaw, hstart]
          have hconfig : r.output.coordinator.configuration = .dagger := by
            rw [hfailure]
            rfl
          exact Or.inr <| Or.inl ⟨rejectedLedger, rfl, hfailure,
            congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
              observation.recording) hfailure,
            congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
              observation.up) hfailure, record_next_dagger r hconfig⟩
      | success L =>
          have hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L := by
            rw [hsiteTail]
            simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, hrecordingRaw, hstart]
          have hfields := successful_cutoff_start_fields tail recording L hstart
            htailPending htailSigma htailCutoff
          rcases hfields with ⟨hLpending, hLsigma, hLcutoff, hLcursor⟩
          have hpostFinish := ReferenceActivePhysicalStep.collectionPostChoice_after_start
            prepared tail.payload tail.ledger tail.started tail.weights recording L
            (by simpa [recordingInput] using hrecording) hstart
          refine Or.inr <| Or.inr ⟨L, rfl, hsite, hLpending, hLsigma, hLcutoff,
            hLcursor, ?_⟩
          let check := CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L)
          let receive := ReferenceActivePhysicalStep.receiveUp prepared L
          have hup : r.output.coordinator.up = receive.diagnostic := by
            calc
              r.output.coordinator.up =
                  (ReferenceActivePhysicalStep.collectionPostChoice prepared tail.payload
                    tail.ledger tail.started tail.weights).up :=
                congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                  observation.up) hpost
              _ = (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                    tail.started recording receive).up :=
                congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                  observation.up) (hpostFinish)
              _ = receive.diagnostic :=
                ReferenceActiveAffinePositiveTest.collectionFinish_up r.input tail.payload
                  tail.started recording receive
          by_cases hcheck : check = true
          · let input := ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L
            let d : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
              input := input
              expected := ReferenceActivePhysicalStep.upExpected prepared
              decoderAfter := (CoordinatorUpReception.decoderTransition input).1
              raw := (CoordinatorUpReception.decoderTransition input).2
              parsed := ReferenceUpReception.rawParsedOutput rate input
              locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate input
              rawMatches := decide ((CoordinatorUpReception.decoderTransition input).2 =
                ReferenceActivePhysicalStep.upExpected prepared)
              wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                rate r.input.row (ReferenceActivePhysicalStep.upInputs prepared L) r.input.time
                (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex r.input))
                (prepared.follower_alignment _).1
                (prepared.follower_alignment _).2.1
                (prepared.follower_alignment _).2.2.1 rfl }
            have hcheckControl : CoordinatorUpReception.receptionInputCheck
                (CoordinatorUpMeasurability.receptionInputAtControl
                  (r.input.row.2 r.input.time)
                  (L, r.input.state.upDecoderBank, r.input.time,
                    prepared.coordinatorObservation)) = true := by
              simpa [check, input, prepared, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
                ReferenceActivePhysicalStep.upInputs,
                ReferenceUpReception.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtControl] using hcheck
            have hdiagnostic : receive.diagnostic = some d := by
              simp [d, receive, input, ReferenceActivePhysicalStep.receiveUp,
                prepared, ReferenceActivePhysicalStep.upInputs,
                ReferenceCoordinatorUpPhysicalCall.actualUpInput,
                ReferenceUpReception.receptionInputAtRow,
                CoordinatorUpMeasurability.receptionInputAtRow, hcheckControl]
              rfl
            have houtput : r.output.coordinator.up = some d := by
              exact hup.trans hdiagnostic
            have hcallFields :=
              ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d houtput
            rcases hcallFields with
              ⟨_, _, _, hbank, htime, hobservation, _, hsample, _, _, _, _, _, _⟩
            refine Or.inr ⟨d, hcheck, hdiagnostic, ?_, houtput,
              rfl, rfl, rfl, rfl, rfl, rfl, hbank, htime, hsample, hobservation, rfl⟩
            · exact hpost.trans hpostFinish
          · have hcheckFalse : check = false := by
              cases hvalue : check with
              | false => rfl
              | true => exact (hcheck hvalue).elim
            have hreceive := cutoff_receiveUp_invalid_of_failed_check r.input L
              (by simpa [check] using hcheckFalse)
            have hconfig : r.output.coordinator.configuration = .dagger := by
              calc
                _ = (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                    tail.started recording receive).configuration :=
                  congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                    observation.configuration) (hpost.trans hpostFinish)
                _ = .dagger := by
                  simp [ReferenceActivePhysicalStep.collectionFinish, receive, prepared, hreceive.1,
                    ReferenceActivePhysicalStep.coordinatorFailure]
            have hfailure : r.output.coordinator =
                ReferenceActivePhysicalStep.coordinatorFailure r.input.state.upDecoderBank
                  (.collection .upReceptionDomain) (some recording) none := by
              calc
                _ = ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                    tail.started recording receive := hpost.trans hpostFinish
                _ = ReferenceActivePhysicalStep.coordinatorFailure
                    r.input.state.upDecoderBank (.collection .upReceptionDomain)
                    (some recording) none := by
                  simp [ReferenceActivePhysicalStep.collectionFinish, receive, prepared, hreceive.1,
                    hreceive.2, ReferenceActivePhysicalStep.coordinatorFailure]
            refine Or.inl ⟨hcheckFalse, hreceive.1, hreceive.2, hfailure, ?_,
              record_next_dagger r hconfig⟩
            simpa [ReferenceActivePhysicalStep.coordinatorFailure] using
              congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                observation.up) hfailure

/-- On the nested ordinary endpoint, the same cutoff tail has a successful
recording and checked start, a retained diagnostic at the actual reception
input, and successful receive, ledger-finish, and clock-finish outputs. The
decoder fields and source-row sample remain at that one diagnostic witness.
-/
theorem actual_ordinary_cutoff_up_receiver
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true)
    (hordinary : r.output.next.coordinator ≠ .dagger) :
    ∃ (tail : ReferenceCollectionPhaseHistory.Tail r.input)
      (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (finished : ReferenceActivePhysicalStep.Ledger rate)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
      r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.ledger
        tail.started tail.weights ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      tail.ledger.pending = Finset.univ ∧
      tail.ledger.sigma = tail.payload.sigma.val + 1 ∧
      tail.ledger.cutoff = r.input.time.val + 1 ∧
      tail.ledger.cursor = r.input.time.val + 1 ∧
      tail.ledger.phase = .ready ∧
      tail.started.pending = Finset.univ ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started tail.weights) =
        some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
      L.pending = Finset.univ ∧
      L.sigma = tail.payload.sigma.val + 1 ∧
      L.cutoff = r.input.time.val + 1 ∧
      L.cursor = r.input.time.val + 1 ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      r.output.coordinator.up = some d ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
      ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result =
            .success (receivedLedger, bank) ∨
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result =
            .rejected (receivedLedger, bank)) ∧
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
  classical
  obtain ⟨tail, htail, hpost, hsiteTail, htailPending, htailSigma, htailCutoff,
    htailCursor, htailPhase, hstartedPending, hcases⟩ :=
      actual_cutoff_up_receiver_cases r hcut
  dsimp only at hcases
  rcases hcases with hrecorderFailure | ⟨recording, hrecording, hstartCases⟩
  · rcases hrecorderFailure with ⟨_, _, _, _, hdagger⟩
    exact False.elim (hordinary hdagger)
  · rcases hstartCases with hstartInvalid | hstartRemainder
    · rcases hstartInvalid with ⟨_, _, _, _, hdagger⟩
      exact False.elim (hordinary hdagger)
    · rcases hstartRemainder with hstartRejected | hstartSuccess
      · rcases hstartRejected with ⟨_, _, _, _, _, hdagger⟩
        exact False.elim (hordinary hdagger)
      · rcases hstartSuccess with
          ⟨L, hstart, hsite, hLpending, hLsigma, hLcutoff, hLcursor, hreceiverCases⟩
        rcases hreceiverCases with hcheckFailure | hdiagnosticData
        · rcases hcheckFailure with ⟨_, _, _, _, _, hdagger⟩
          exact False.elim (hordinary hdagger)
        · rcases hdiagnosticData with
            ⟨d, hcheck, hreceiveDiagnostic, hfinishEquation, houtput, hdecoderAfter,
              hraw, hparsed, hlocal, hexpected, hrawMatches, hbankCase, htimeCase,
              hsampleCase, hobservationCase, hwrongUnique⟩
          have hfinishOrdinary :
              (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                tail.started recording
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) L)).configuration ≠ .dagger := by
            intro hdagger
            apply hordinary
            apply record_next_dagger r
            calc
              r.output.coordinator.configuration =
                  (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                    tail.started recording
                    (ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) L)).configuration :=
                congrArg (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
                  observation.configuration) hfinishEquation
              _ = .dagger := hdagger
          have hnotInvalid :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid := by
            intro hinvalid
            apply hfinishOrdinary
            simp [ReferenceActivePhysicalStep.collectionFinish, hinvalid,
              ReferenceActivePhysicalStep.coordinatorFailure]
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result with
          | invalid => exact (hnotInvalid hreceive).elim
          | success pair =>
              rcases pair with ⟨receivedLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound receivedLedger with
              | invalid =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                        tail.started recording
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact False.elim (hfinishOrdinary hdagger)
              | rejected ignored =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                        tail.started recording
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact False.elim (hfinishOrdinary hdagger)
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time
                      tail.started.clock finished.pending r.input.row with
                  | error reason =>
                      have hdagger :
                          (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                            tail.started recording
                            (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                        simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                          hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                      exact False.elim (hfinishOrdinary hdagger)
                  | ok clockFinished =>
                      have hrecordingActual : CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started
                            tail.weights) = some recording := by
                        simpa only [CoordinatorRecorderComplementBridge.run,
                          ReferenceActivePhysicalStep.collectionRecordingInput] using hrecording
                      have htailReception : tail.reception = some (L,
                          ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L) := by
                        simp [ReferenceCollectionPhaseHistory.Tail.reception,
                          hrecordingActual, hstart]
                      have hretention :=
                        (ReferenceCoordinatorUpPhysicalCall.record_up_retention_iff r).mp
                          ⟨d, houtput⟩
                      rcases hretention with ⟨retainedLedger, hretainedSite, hretainedCheck⟩
                      have hretainedLedger : retainedLedger = L := by
                        exact Option.some.inj (hretainedSite.symm.trans hsite)
                      have hcheckActual : CoordinatorUpReception.receptionInputCheck
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true := by
                        simpa [hretainedLedger] using hretainedCheck
                      obtain ⟨fieldLedger, hfieldSite, _, hbank, htime, hobservation, _, hsample,
                        _, _, _, _, _, _⟩ :=
                          ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
                            r d houtput
                      have hfieldLedger : fieldLedger = L := by
                        exact Option.some.inj (hfieldSite.symm.trans hsite)
                      have hinput : d.input =
                          ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L := by
                        obtain ⟨inputLedger, hinputSite, _, hinputEq, _⟩ :=
                          ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d houtput
                        have hinputLedger : inputLedger = L :=
                          Option.some.inj (hinputSite.symm.trans hsite)
                        simpa [hinputLedger] using hinputEq
                      refine ⟨tail, recording, L, d, receivedLedger, bank, finished,
                        clockFinished, htail, hpost, hsite, htailPending, htailSigma,
                        htailCutoff, htailCursor, htailPhase, hstartedPending,
                        hrecordingActual, hstart, hLpending, hLsigma, hLcutoff, hLcursor,
                        hcheckActual, hinput, houtput, htailReception, hnotInvalid, ?_,
                        hfinish, hclock, hdecoderAfter, hraw, hparsed, hlocal, hexpected,
                        hrawMatches, hbank, htime, hsample, hobservation, hwrongUnique⟩
                      exact Or.inl hreceive
          | rejected pair =>
              rcases pair with ⟨receivedLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound receivedLedger with
              | invalid =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                        tail.started recording
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact False.elim (hfinishOrdinary hdagger)
              | rejected ignored =>
                  have hdagger :
                      (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                        tail.started recording
                        (ReferenceActivePhysicalStep.receiveUp
                          (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                    simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                      ReferenceActivePhysicalStep.coordinatorFailure]
                  exact False.elim (hfinishOrdinary hdagger)
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time
                      tail.started.clock finished.pending r.input.row with
                  | error reason =>
                      have hdagger :
                          (ReferenceActivePhysicalStep.collectionFinish (x := r.input) tail.payload
                            tail.started recording
                            (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare r.input) L)).configuration = .dagger := by
                        simp [ReferenceActivePhysicalStep.collectionFinish, hreceive, hfinish,
                          hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                      exact False.elim (hfinishOrdinary hdagger)
                  | ok clockFinished =>
                      have hrecordingActual : CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare r.input) tail.payload tail.started
                            tail.weights) = some recording := by
                        simpa only [CoordinatorRecorderComplementBridge.run,
                          ReferenceActivePhysicalStep.collectionRecordingInput] using hrecording
                      have htailReception : tail.reception = some (L,
                          ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L) := by
                        simp [ReferenceCollectionPhaseHistory.Tail.reception,
                          hrecordingActual, hstart]
                      have hretention :=
                        (ReferenceCoordinatorUpPhysicalCall.record_up_retention_iff r).mp
                          ⟨d, houtput⟩
                      rcases hretention with ⟨retainedLedger, hretainedSite, hretainedCheck⟩
                      have hretainedLedger : retainedLedger = L := by
                        exact Option.some.inj (hretainedSite.symm.trans hsite)
                      have hcheckActual : CoordinatorUpReception.receptionInputCheck
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true := by
                        simpa [hretainedLedger] using hretainedCheck
                      obtain ⟨fieldLedger, hfieldSite, _, hbank, htime, hobservation, _, hsample,
                        _, _, _, _, _, _⟩ :=
                          ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
                            r d houtput
                      have hinput : d.input =
                          ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L := by
                        obtain ⟨inputLedger, hinputSite, _, hinputEq, _⟩ :=
                          ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d houtput
                        have hinputLedger : inputLedger = L :=
                          Option.some.inj (hinputSite.symm.trans hsite)
                        simpa [hinputLedger] using hinputEq
                      refine ⟨tail, recording, L, d, receivedLedger, bank, finished,
                        clockFinished, htail, hpost, hsite, htailPending, htailSigma,
                        htailCutoff, htailCursor, htailPhase, hstartedPending,
                        hrecordingActual, hstart, hLpending, hLsigma, hLcutoff, hLcursor,
                        hcheckActual, hinput, houtput, htailReception, hnotInvalid, ?_,
                        hfinish, hclock, hdecoderAfter, hraw, hparsed, hlocal, hexpected,
                        hrawMatches, hbank, htime, hsample, hobservation, hwrongUnique⟩
                      exact Or.inr hreceive

end Bandits.Support.ReferenceCutoffUpReceiverLocal

end
