/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAffineHashHalf
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

/-!
# Executed UP decoder banks on generated active runs

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-150`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This internal producer identifies retained UP diagnostics with their checked
physical inputs and original row coordinates, constructs the generated
initial bank invariant from the corrected launch, and gives decoder chronology
on each actual horizon prefix. Prefix replay is conditional only on that
prefix's ordinary endpoint; no whole-run success law is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.ReferenceUpDecoderBankInvariant
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceGeneratedUpBatchCalendar

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceGeneratedActivePrefixFactor.Remainder p q t

variable {p : Parameters} {rate : RateInput p}

private theorem collectionPostChoice_up_raw
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights).up = some d) :
    ∃ ledgerStarted,
      ReferenceCoordinatorUpPhysicalCall.tailLedger?
        (ReferenceActivePhysicalStep.prepare x) payload ledger started weights =
          some ledgerStarted ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted ∧
      d.expected = ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).2 ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted) ∧
      d.rawMatches = decide ((CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted)).2 =
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)) := by
  classical
  let recordingInput := CoordinatorRecorderComplementBridge.run
    (ReferenceActivePhysicalStep.collectionRecordingInput
      (ReferenceActivePhysicalStep.prepare x) payload started weights)
  cases hrecording : recordingInput with
  | none =>
      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording,
        recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | rejected rejectedLedger =>
          simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecording, hstart,
            recordingInput, ReferenceActivePhysicalStep.coordinatorFailure] at hd
      | success ledgerStarted =>
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, recordingInput,
            hrecording, hstart] at hd
          rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
          let inputs := ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare x) ledgerStarted
          let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
          have hinput : input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledgerStarted := rfl
          have hcheck : CoordinatorUpReception.receptionInputCheck input = true := by
            by_contra hnot
            have hfalse : CoordinatorUpReception.receptionInputCheck input = false := by
              cases hvalue : CoordinatorUpReception.receptionInputCheck input with
              | false => rfl
              | true => exact (hnot hvalue).elim
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hfalse] at hd
          have htail : ReferenceCoordinatorUpPhysicalCall.tailLedger?
              (ReferenceActivePhysicalStep.prepare x) payload ledger started weights =
                some ledgerStarted := by
            simp [ReferenceCoordinatorUpPhysicalCall.tailLedger?, recordingInput,
              hrecording, hstart]
          have hrawMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.raw =
                some (CoordinatorUpReception.decoderTransition input).2 := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hafterMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter =
                some (CoordinatorUpReception.decoderTransition input).1 := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hexpectedMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.expected =
                    some (ReferenceActivePhysicalStep.upExpected
                      (ReferenceActivePhysicalStep.prepare x)) := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hparsedMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.parsed =
                    some (ReferenceUpReception.rawParsedOutput rate input) := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hlocalMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.locallyAccepted =
                    some (ReferenceUpReception.rawParsedLocalAcceptance rate input) := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hmatchMap :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare x) ledgerStarted).diagnostic.map
                  ReferenceActivePhysicalStep.UpDiagnostic.rawMatches =
                    some (decide ((CoordinatorUpReception.decoderTransition input).2 =
                      ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare x))) := by
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck]
          have hrawSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.raw) hd
          rw [hrawMap] at hrawSaved
          have hraw : d.raw = (CoordinatorUpReception.decoderTransition input).2 :=
            (Option.some.inj hrawSaved).symm
          have hexpectedSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.expected) hd
          rw [hexpectedMap] at hexpectedSaved
          have hexpected : d.expected =
              ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) :=
            (Option.some.inj hexpectedSaved).symm
          have hparsedSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.parsed) hd
          rw [hparsedMap] at hparsedSaved
          have hparsed : d.parsed = ReferenceUpReception.rawParsedOutput rate input :=
            (Option.some.inj hparsedSaved).symm
          have hlocalSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.locallyAccepted) hd
          rw [hlocalMap] at hlocalSaved
          have hlocal : d.locallyAccepted =
              ReferenceUpReception.rawParsedLocalAcceptance rate input :=
            (Option.some.inj hlocalSaved).symm
          have hmatchSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.rawMatches) hd
          rw [hmatchMap] at hmatchSaved
          have hmatch : d.rawMatches = decide ((CoordinatorUpReception.decoderTransition input).2 =
              ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)) :=
            (Option.some.inj hmatchSaved).symm
          have hafterSaved := congrArg
            (Option.map ReferenceActivePhysicalStep.UpDiagnostic.decoderAfter) hd
          rw [hafterMap] at hafterSaved
          have hafter : d.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 :=
            (Option.some.inj hafterSaved).symm
          refine ⟨ledgerStarted, htail, ?_, ?_, hexpected, hafter, ?_, ?_, ?_, ?_⟩
          · simpa [hinput] using hcheck
          · have hinputSaved := congrArg
              (Option.map ReferenceActivePhysicalStep.UpDiagnostic.input) hd
            simp [ReferenceActivePhysicalStep.receiveUp, inputs, input, hcheck] at hinputSaved
            exact hinputSaved.symm.trans hinput
          · simpa [hinput] using hraw
          · simpa [hinput] using hparsed
          · simpa [hinput] using hlocal
          · simpa [hinput] using hmatch

private theorem record_up_transition_fields
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some d) :
    ∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare record.input) ∧
      d.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
      d.raw = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).2 ∧
      d.parsed = ReferenceUpReception.rawParsedOutput rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
      d.rawMatches = decide ((CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).2 =
          ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare record.input)) := by
  have hstep : record.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.up := by
    rw [record.output_eq]
    rfl
  rw [hstep] at hdiagnostic
  classical
  let x := record.input
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | recorderBoundaryFailure installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | choiceRejected installation =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | chosen installation selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.first (.chosen installation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation
                (ReferenceActivePhysicalStep.prepare x) (.chosen installation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hdiagnostic
            cases hdiagnostic
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | initializerFailure dispatched _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | localFailure dispatched _ reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
          hnoassignment selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
                  hnoassignment selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hdiagnostic
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hexpected, hafter, hraw, hparsed, hlocal, hmatch⟩ :=
              collectionPostChoice_up_raw x registers.payload
                (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
                d hdiagnostic
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hexpected, hafter, hraw, hparsed, hlocal, hmatch⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, x, hcoord, hsel] using hsite
      | continuingChosen dispatched startRoundEq continuation selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.live registers owned base
                (.continuingChosen dispatched startRoundEq continuation selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_live_equation
                (ReferenceActivePhysicalStep.prepare x) registers owned base
                (.continuingChosen dispatched startRoundEq continuation selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hdiagnostic
            cases hdiagnostic
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | localFailure started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | coreFailure core started _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | continuing core snapshot boundary scores =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel] at hdiagnostic
            let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            obtain ⟨ledgerStarted, hsite, hcheck, hinput, hexpected, hafter, hraw, hparsed, hlocal, hmatch⟩ :=
              collectionPostChoice_up_raw x payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
                d hdiagnostic
            refine ⟨ledgerStarted, ?_, hcheck, hinput, hexpected, hafter, hraw, hparsed, hlocal, hmatch⟩
            simpa [ReferenceCoordinatorUpPhysicalCall.siteLedger?, x, hcoord, hsel, source]
              using hsite
      | laterReconstructionFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | laterPrefixFailure core consistent started _ instruction _ _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | laterOrientationFailure core consistent started _ instruction _ _ =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | laterChoiceFailure core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed reason =>
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            x, hcoord, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
      | laterChosen core consistent started startRoundEq instruction assignmentStartEq
          output localEq clockData installed selected =>
          by_cases hsel : ReferenceActivePhysicalStep.DispatchCut.selection
              (.collection payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected)) = none
          · simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              x, hcoord, hsel, ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
          · have hnone : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up = none := by
              have heq := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
                (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
                (.laterChosen core consistent started startRoundEq instruction assignmentStartEq
                  output localEq clockData installed selected) hcoord
              rw [heq, ite_eq_right hsel]
              dsimp
              unfold ReferenceActivePhysicalStep.livePostChoice
              repeat' (first | split | simp [ReferenceActivePhysicalStep.coordinatorFailure])
            rw [hnone] at hdiagnostic
            cases hdiagnostic
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure] at hdiagnostic
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        x, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] at hdiagnostic


/-- The actual retained UP call, including its decoder transition and raw
output, is tied to the current physical record and its original whole-row
sample. Raw output, parse result, local acceptance, sent word, and current
raw-match test remain distinct actual diagnostic fields. -/
theorem record_up_executed_fields
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic) :
    ∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      diagnostic.decoderAfter =
        (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
      diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
      diagnostic.parsed = ReferenceUpReception.rawParsedOutput rate diagnostic.input ∧
      diagnostic.locallyAccepted =
        ReferenceUpReception.rawParsedLocalAcceptance rate diagnostic.input ∧
      diagnostic.rawMatches = decide ((CoordinatorUpReception.decoderTransition diagnostic.input).2 =
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare record.input)) ∧
      diagnostic.expected = ReferenceGeneratedAffineHashHalf.directionSent 1 record.input ∧
      diagnostic.input.time = record.input.time ∧
      diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
      diagnostic.input.affineSample =
        ((record.input.rows record.input.selected).2 record.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((record.input.rows record.input.selected).2 record.input.time)) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) := by
  obtain ⟨ledger, hsite, hcheck, hinput, hexpected, hafter, hraw, hparsed, hlocal, hmatch⟩ :=
    record_up_transition_fields record diagnostic hdiagnostic
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
    record diagnostic hdiagnostic
  rcases hfields with ⟨ledger', hsite', _, hbank, htime, hobs, hselected, hsample,
    hslot, henabled, hselectedFlag, hroundSample, hroundReward, hfeedback⟩
  have hledger : ledger' = ledger := Option.some.inj (hsite'.symm.trans hsite)
  subst ledger'
  refine ⟨ledger, hsite, hcheck, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htime, hbank, hsample, hobs⟩
  · exact hinput
  · rw [hinput]
    exact hafter
  · rw [hinput]
    exact hraw
  · rw [hinput]
    exact hparsed
  · rw [hinput]
    exact hlocal
  · rw [hinput]
    exact hmatch
  · simpa [ReferenceGeneratedAffineHashHalf.directionSent,
      ReferenceActiveAffinePositiveTest.upSent] using hexpected

theorem retained_launch_start_fields
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0) :
    x.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.1 ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := by
  simpa [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet] using x.property

/-- An actual UP entry is present exactly when the retained call selected
that channel and the executed UP direction was positive. -/
theorem record_up_positive_entries_ne_nil_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (i : Fin (p.m - 1)) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i ≠ [] ↔
      diagnostic.input.selectedFollower = i ∧
        ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true := by
  classical
  have hdirection : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input =
      decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) := by
    calc
      _ = ReferenceActiveAffinePositiveTest.upPositive record.input := by
        simp [ReferenceGeneratedAffineHashHalf.directionPositive]
      _ = ReferenceActiveAffinePositiveTest.upDiagnosticPositive record.output.coordinator.up :=
        ReferenceActiveAffinePositiveTest.record_upPositive record
      _ = decide (AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput diagnostic.input)) := by
        rw [hdiagnostic]
        rfl
  by_cases hselected : diagnostic.input.selectedFollower = i
  · have hpositive :
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries record i ≠ [] ↔
          AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput diagnostic.input) := by
      simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hdiagnostic,
        ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hselected,
        if_pos, ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
        ReferenceCoordinatorUpDecoderReplay.retainedUpTime]
      change (AffineBatchDecoder.positiveAt p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
        diagnostic.input.time ≠ []) ↔ _
      simp only [AffineBatchDecoder.positiveAt]
      rw [show AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input
            diagnostic.input.time) =
            AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput diagnostic.input) from rfl]
      by_cases heligible : AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput diagnostic.input)
      · simp [heligible]
      · simp [heligible]
    rw [hpositive]
    constructor
    · intro heligible
      refine ⟨hselected, ?_⟩
      rw [hdirection]
      simp [heligible]
    · rintro ⟨_, hpositive⟩
      rw [hdirection] at hpositive
      exact of_decide_eq_true hpositive
  · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
      ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hdiagnostic, hselected]

/-- An actual retained call exposes the receiver's invalid versus committed
physical-bank branches. A committed receiver bank remains the successor bank
even when a later finish operation has already made the coordinator dagger. -/
theorem record_up_physical_commit_cases
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state) :
    ∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      diagnostic.decoderAfter =
        (CoordinatorUpReception.decoderTransition
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
      ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid ∧
          record.output.next.upDecoderBank = record.input.state.upDecoderBank ∨
        ∃ out,
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .success out ∨
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .rejected out) ∧
          out.2 = CoordinatorUpReception.decoderBankAfter diagnostic.input ∧
          record.output.next.upDecoderBank = out.2) :=
  ReferenceCoordinatorUpPhysicalCall.record_up_commit_cases
    record diagnostic hdiagnostic hinvariant

/-- At an executed positive quota completion, the saved decoder state is the
exact pending batch appended to the full completed history and its pending
list is empty. The raw field is the decoder result itself, so it may still be
`none` if that batch has no unique decoded word. -/
theorem record_up_quota_completion
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (i : Fin (p.m - 1))
    (hselected : diagnostic.input.selectedFollower = i)
    (hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true)
    (hquota : (record.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p) :
    diagnostic.decoderAfter.pending = [] ∧
      diagnostic.decoderAfter.completed =
        (record.input.state.upDecoderBank i).completed ++
          [(record.input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time]] ∧
      diagnostic.decoderAfter = ⟨[],
        (record.input.state.upDecoderBank i).completed ++
          [(record.input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time]]⟩ ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput
        ((record.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            diagnostic.input.time]) := by
  classical
  have hdirection : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input =
      decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) := by
    calc
      _ = ReferenceActiveAffinePositiveTest.upPositive record.input := by
        simp [ReferenceGeneratedAffineHashHalf.directionPositive]
      _ = ReferenceActiveAffinePositiveTest.upDiagnosticPositive record.output.coordinator.up :=
        ReferenceActiveAffinePositiveTest.record_upPositive record
      _ = decide (AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput diagnostic.input)) := by
        rw [hdiagnostic]
        rfl
  have hdecision : decide
      (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input)) = true := by
    rw [← hdirection]
    exact hpositive
  have heligible : AffineBatchDecoder.eligible
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input
        diagnostic.input.time) := by
    simpa [ReferenceCoordinatorUpDecoderReplay.constantInputTrace] using
      of_decide_eq_true hdecision
  obtain ⟨_, _, _, _, hafter, hraw, _, _, _, _, _, hbank, _, _⟩ :=
    record_up_executed_fields record diagnostic hdiagnostic
  let before := record.input.state.upDecoderBank i
  have hselectedBank : diagnostic.input.upDecoderBank diagnostic.input.selectedFollower = before := by
    calc
      diagnostic.input.upDecoderBank diagnostic.input.selectedFollower =
          diagnostic.input.upDecoderBank i := by rw [hselected]
      _ = record.input.state.upDecoderBank i := congrFun hbank i
      _ = before := rfl
  have hcomplete := AffineBatchDecoder.decodeStep_complete p
    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
    before diagnostic.input.time heligible hquota
  have htrace : CoordinatorUpReception.traceAt diagnostic.input =
      ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input := rfl
  have htransition : CoordinatorUpReception.decoderTransition diagnostic.input =
      (⟨[], before.completed ++
          [before.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time]]⟩,
        AffineBatchDecoder.batchOutput
          (before.pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
              diagnostic.input.time])) := by
    rw [CoordinatorUpReception.decoderTransition, hselectedBank]
    rw [htrace]
    exact hcomplete
  have hstate : diagnostic.decoderAfter = ⟨[],
      before.completed ++
        [before.pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
            diagnostic.input.time]]⟩ := by
    rw [hafter, htransition]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstate]
  · rw [hstate]
  · exact hstate
  · rw [hraw, htransition]

/-- The physical record distinguishes a decoder completion that fails at
reception from one whose decoded channel state is committed. In the latter
case, the exact reset state survives later ledger or clock failures. -/
theorem record_up_quota_physical_commit_cases
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (i : Fin (p.m - 1))
    (hselected : diagnostic.input.selectedFollower = i)
    (hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true)
    (hquota : (record.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p) :
    let batch := (record.input.state.upDecoderBank i).pending ++
      [AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
        diagnostic.input.time]
    diagnostic.decoderAfter.pending = [] ∧
      diagnostic.decoderAfter.completed =
        (record.input.state.upDecoderBank i).completed ++ [batch] ∧
      diagnostic.decoderAfter = ⟨[],
        (record.input.state.upDecoderBank i).completed ++ [batch]⟩ ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput batch ∧
      ((∃ ledger,
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .invalid ∧
          record.output.next.upDecoderBank = record.input.state.upDecoderBank) ∨
        ∃ ledger out,
          ((ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .success out ∨
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare record.input) ledger).result = .rejected out) ∧
          out.2 = CoordinatorUpReception.decoderBankAfter diagnostic.input ∧
          record.output.next.upDecoderBank i = diagnostic.decoderAfter) := by
  classical
  let batch := (record.input.state.upDecoderBank i).pending ++
    [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
      diagnostic.input.time]
  have hcomplete := record_up_quota_completion record diagnostic hdiagnostic i
    hselected hpositive hquota
  rcases record_up_physical_commit_cases record diagnostic hdiagnostic hinvariant with
    ⟨ledger, _, _, _, _, hcases⟩
  obtain ⟨_, _, _, _, hafterTransition, _, _, _, _, _, _, _, _, _⟩ :=
    record_up_executed_fields record diagnostic hdiagnostic
  dsimp only [batch]
  refine ⟨hcomplete.1, hcomplete.2.1, hcomplete.2.2.1, hcomplete.2.2.2, ?_⟩
  rcases hcases with hinvalid | ⟨out, hcommitted, houtbank, hnext⟩
  · exact Or.inl ⟨ledger, hinvalid.1, hinvalid.2⟩
  · have hchannel : record.output.next.upDecoderBank i = diagnostic.decoderAfter := by
      calc
        _ = out.2 i := congrFun hnext i
        _ = (CoordinatorUpReception.decoderBankAfter diagnostic.input) i :=
          congrArg (fun bank => bank i) houtbank
        _ = diagnostic.decoderAfter := by
          simp [CoordinatorUpReception.decoderBankAfter, hselected, hafterTransition]
    exact Or.inr ⟨ledger, out, hcommitted, houtbank, hchannel⟩

/-- The corrected generated launch supplies the first state and initially
empty UP bank for the original retained launch-start fibre. -/
theorem generated_up_initial_bank_invariant
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    ReferenceUpDecoderBankInvariant.upBankInvariant
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
        rate rewards C_star C_h q t control x.1 fields.1 s hs hstart) := by
  dsimp only
  let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  have hcross := (ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).1
  obtain ⟨canonical, hchar, hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hcross
  rcases hchar with ⟨hlaunch, hcoord, hbank, _, _⟩
  have hgenerated : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active := by
    simpa [active, source] using hspec.1
  have hactive : active = canonical := Option.some.inj (hgenerated.symm.trans hlaunch)
  change ReferenceUpDecoderBankInvariant.upBankInvariant active
  rw [hactive]
  change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
    canonical.coordinator canonical.upDecoderBank
  rw [hcoord, hbank]
  exact ReferenceUpDecoderBankInvariant.firstState_upBankInvariant
    canonical.activations canonical.followers

/-- Every physical prefix of the generated run preserves the UP-bank
invariant. At ordinary prefix endpoints the collected list is exactly the
retained positive entries; the complete history and pending suffix remain
available through `collected`. -/
theorem generated_up_prefix_bank_chronology
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (k : ℕ) (hk : k ≤ p.T - s)
    (i : Fin (p.m - 1)) :
    let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let run := ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k (by omega) hmode
    ReferenceUpDecoderBankInvariant.upBankInvariant run.finalState ∧
      (run.finalState.coordinator ≠ .dagger →
        AffineBatchDecoder.collected (run.finalState.upDecoderBank i) =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).length =
          (run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
            (run.finalState.upDecoderBank i).pending.length ∧
        (run.finalState.upDecoderBank i).completed.flatten =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).take
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
        (run.finalState.upDecoderBank i).pending =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).drop
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p)) := by
  dsimp only
  let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  have hspan : s + k ≤ p.T := by omega
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant active := by
    exact generated_up_initial_bank_invariant rate rewards C_star C_h q t s hs control0 x control
  let run := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k hspan hmode
  have hInv := ReferenceUpDecoderBankInvariant.run_upBankInvariant active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k hspan hmode hinitial
  have hcollected : run.finalState.coordinator ≠ .dagger →
      AffineBatchDecoder.collected (run.finalState.upDecoderBank i) =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).length =
        (run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
          (run.finalState.upDecoderBank i).pending.length ∧
      (run.finalState.upDecoderBank i).completed.flatten =
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).take
          ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
      (run.finalState.upDecoderBank i).pending =
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).drop
          ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) := by
    intro hordinary
    have hrun := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
      active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s k hspan hmode hinitial hordinary i
    have hwellFormed : CoordinatorUpReception.decoderStateWellFormed p
        (run.finalState.upDecoderBank i) := by
      change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
        run.finalState.coordinator run.finalState.upDecoderBank at hInv
      exact hInv.1 i
    have hstate : active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
      have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
      have hcross := (ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
        rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).1
      obtain ⟨canonical, ⟨hlaunch, _, hbank, _, _⟩, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
          rate source rewards C_star C_h hcross
      have hgenerated : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h = some active := by
        simpa [active, source] using hspec.1
      have hactive : active = canonical := Option.some.inj (hgenerated.symm.trans hlaunch)
      rw [hactive, hbank]
    have hempty : AffineBatchDecoder.collected (active.upDecoderBank i) = [] := by
      rw [hstate]
      simp [CoordinatorUpReception.initialUpDecoderBank,
        AffineBatchDecoder.initial, AffineBatchDecoder.collected]
    have hcollect : AffineBatchDecoder.collected (run.finalState.upDecoderBank i) =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i := by
      simpa [hempty] using hrun
    have hlength := AffineBatchDecoder.length_collected (run.finalState.upDecoderBank i)
      hwellFormed.2
    have hflatLength :
        (run.finalState.upDecoderBank i).completed.flatten.length =
          (run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p := by
      simp only [AffineBatchDecoder.collected, List.length_append] at hlength
      omega
    have hentryLength :
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).length =
          (run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
            (run.finalState.upDecoderBank i).pending.length := by
      calc
        _ = (AffineBatchDecoder.collected (run.finalState.upDecoderBank i)).length :=
          (congrArg List.length hcollect).symm
        _ = _ := hlength
    have hflat :
        (run.finalState.upDecoderBank i).completed.flatten =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).take
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) := by
      calc
        _ = ((run.finalState.upDecoderBank i).completed.flatten ++
            (run.finalState.upDecoderBank i).pending).take
              (run.finalState.upDecoderBank i).completed.flatten.length :=
          List.take_append_length.symm
        _ = _ := by rw [← hcollect, AffineBatchDecoder.collected, hflatLength]
    have hpending :
        (run.finalState.upDecoderBank i).pending =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).drop
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) := by
      calc
        _ = ((run.finalState.upDecoderBank i).completed.flatten ++
            (run.finalState.upDecoderBank i).pending).drop
              (run.finalState.upDecoderBank i).completed.flatten.length := by
          symm
          rw [List.drop_append_of_le_length (Nat.le_refl _)]
          simp
        _ = _ := by rw [← hcollect, AffineBatchDecoder.collected, hflatLength]
    exact ⟨hcollect, hentryLength, hflat, hpending⟩
  exact ⟨hInv, hcollected⟩

/-- The bank theorem also applies to the original source on the UP branch:
the branch is first transported through A's proved retained-launch map, then
the same generated seed and physical horizon run are used. -/
theorem original_source_up_branch_prefix_bank_chronology
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {source : SourceInput p // source ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t ((1 : Fin 2), i) s})
    (control : TimeControl p) (k : ℕ) (hk : k ≤ p.T - s) :
    let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
      (rate := rate) rewards C_star C_h q t ((1 : Fin 2), i) s hs control0 z
    let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 launch
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s launch.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart).2.1
    let run := ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s k (by omega) hmode
    ReferenceUpDecoderBankInvariant.upBankInvariant run.finalState ∧
      (run.finalState.coordinator ≠ .dagger →
        AffineBatchDecoder.collected (run.finalState.upDecoderBank i) =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).length =
          (run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p +
            (run.finalState.upDecoderBank i).pending.length ∧
        (run.finalState.upDecoderBank i).completed.flatten =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).take
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p) ∧
        (run.finalState.upDecoderBank i).pending =
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i).drop
            ((run.finalState.upDecoderBank i).completed.length * AffineBatchDecoder.quota p)) := by
  exact generated_up_prefix_bank_chronology rate rewards C_star C_h q t s hs
    control0
    (ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
      (rate := rate) rewards C_star C_h q t ((1 : Fin 2), i) s hs control0 z)
    control k hk i

/-- The launch itself is an empty physical UP bank, obtained from the same
corrected-launch crossing characterization used for its invariant. -/
theorem generated_up_initial_bank_empty
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).upDecoderBank =
        CoordinatorUpReception.initialUpDecoderBank p := by
  dsimp only
  let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  have hcross := (ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).1
  obtain ⟨canonical, ⟨hlaunch, _, hbank, _, _⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hcross
  have hgenerated : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active := by
    simpa [active, source] using hspec.1
  have hactive : active = canonical := Option.some.inj (hgenerated.symm.trans hlaunch)
  change active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p
  rw [hactive, hbank]

/-- On a source-local physical interval beginning at a fresh reset, the
pending list is exactly the retained positive entries since that reset while
the completed ordinal remains fixed. The explicit calendar equality pins the
records to the half-open action interval `[alpha, alpha + count)`. -/
theorem connected_up_fresh_interval_pending
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (alpha count : ℕ)
    (hcalendar : records.map (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar alpha count)
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ∀ record, record ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : final.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hreset : (initial.upDecoderBank i).pending = [])
    (hordinal : (final.upDecoderBank i).completed = (initial.upDecoderBank i).completed) :
    (final.upDecoderBank i).pending =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i ∧
      records.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar alpha count := by
  have hcollected := ReferenceCoordinatorUpDecoderReplay.connected_collected_upPositiveEntries
    hconnected hinvariant hordinary i
  change (final.upDecoderBank i).completed.flatten ++
      (final.upDecoderBank i).pending =
    ((initial.upDecoderBank i).completed.flatten ++
      (initial.upDecoderBank i).pending) ++
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i at hcollected
  rw [hordinal, hreset] at hcollected
  simp only [List.append_nil] at hcollected
  have hcancel : ∀ (pre left right : List
      (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))),
      pre ++ left = pre ++ right → left = right := by
    intro pre
    induction pre with
    | nil =>
        intro left right heq
        simpa using heq
    | cons head tail ih =>
        intro left right heq
        injection heq with _ htail
        exact ih left right htail
  exact ⟨hcancel _ _ _ hcollected, hcalendar⟩

/-- The `alpha = s` arm of the fresh-interval identity for the exact
generated run. Its seed is the original corrected launch, its records are the
existing physical run, and its calendar is the full half-open interval from
`s`; completed history is retained unchanged up to the specified endpoint. -/
theorem generated_up_initial_interval_pending
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (count : ℕ) (hspan : s + count ≤ p.T)
    (i : Fin (p.m - 1)) :
    let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
    let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
    let run := ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode
    run.finalState.coordinator ≠ .dagger →
      (run.finalState.upDecoderBank i).completed = (active.upDecoderBank i).completed →
      (run.finalState.upDecoderBank i).pending =
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries run.records i ∧
        run.records.map (fun record => record.input.time.val) =
          ReferenceActivePhysicalHorizon.calendar s count := by
  dsimp only
  let fields := retained_launch_start_fields rate rewards C_star C_h q t s hs control0 x
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 fields.1 s hs hstart).2.1
  let run := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode
  intro hord hordinal
  have hstartBank := generated_up_initial_bank_empty
    rate rewards C_star C_h q t s hs control0 x control
  have hreset : (active.upDecoderBank i).pending = [] := by
    rw [hstartBank]
    simp [CoordinatorUpReception.initialUpDecoderBank, AffineBatchDecoder.initial]
  have hInv := generated_up_initial_bank_invariant
    rate rewards C_star C_h q t s hs control0 x control
  have hrecordsInvariant : ∀ record, record ∈ run.records →
      ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state := by
    intro record hrecord
    exact ReferenceUpDecoderBankInvariant.run_record_input_upBankInvariant
      active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s count hspan hmode hInv record hrecord
  have hcalendar := ReferenceActivePhysicalHorizon.run_time_values
    active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan hmode
  exact connected_up_fresh_interval_pending run.records s count hcalendar run.connected
    hrecordsInvariant hord i hreset hordinal

/-- The committed-completion arm of the reset identity. The caller supplies
the exact physical decoder-bank equality furnished by the success/rejection
arm of `record_up_quota_physical_commit_cases`, whose separate invalid arm
retains the old physical bank. `records` is the actual connected suffix
beginning at the incoming state after action `alpha - 1`. -/
theorem record_up_quota_commit_fresh_interval_pending
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (i : Fin (p.m - 1))
    (hselected : diagnostic.input.selectedFollower = i)
    (hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 record.input = true)
    (hquota : (record.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p)
    (hcommit : record.output.next.upDecoderBank i = diagnostic.decoderAfter)
    (alpha count : ℕ) (hspan : alpha + count ≤ p.T)
    (halpha : record.input.time.val + 1 = alpha)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (final : ReferenceActivePhysicalStep.State p rate)
    (hcalendar : records.map (fun current => current.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar alpha count)
    (hconnected : ReferenceActivePhysicalHorizon.Connected record.output.next records final)
    (hinvariant : ∀ current, current ∈ records →
      ReferenceUpDecoderBankInvariant.upBankInvariant current.input.state)
    (hordinary : final.coordinator ≠ .dagger)
    (hordinal : (final.upDecoderBank i).completed =
      (record.output.next.upDecoderBank i).completed) :
    record.input.time.val + 1 = alpha ∧ alpha + count ≤ p.T ∧
      record.output.next.coordinator ≠ .dagger ∧
      (final.upDecoderBank i).pending =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i ∧
      records.map (fun current => current.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar alpha count := by
  have hcomplete := record_up_quota_completion record diagnostic hdiagnostic i
    hselected hpositive hquota
  have hreset : (record.output.next.upDecoderBank i).pending = [] := by
    rw [hcommit]
    exact hcomplete.1
  have hinterval := connected_up_fresh_interval_pending records alpha count hcalendar
    hconnected hinvariant hordinary i hreset hordinal
  have hincoming : record.output.next.coordinator ≠ .dagger := by
    intro hdagger
    exact hordinary
      (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hconnected hdagger).1
  exact ⟨halpha, hspan, hincoming, hinterval.1, hinterval.2⟩

end Bandits.Support.ReferenceGeneratedUpBatchCalendar

end
